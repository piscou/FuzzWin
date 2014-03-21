#include "fuzzwin_modelview.h"


#include <QStringList>


/*******************/
/****** ITEMS ******/
/*******************/

FuzzwinItem::FuzzwinItem(const QVector<QVariant> &data, FuzzwinItem *parent)
{
    parentItem = parent;
    itemData = data;
}

FuzzwinItem::~FuzzwinItem()
{
    qDeleteAll(childItems);
}

FuzzwinItem *FuzzwinItem::child(int number)
{
    return childItems.value(number);
}

int FuzzwinItem::childCount() const
{
    return childItems.count();
}

int FuzzwinItem::childNumber() const
{
    if (parentItem)   return parentItem->childItems.indexOf(const_cast<FuzzwinItem*>(this));

    return 0;
}

int FuzzwinItem::columnCount() const
{
    return itemData.count();
}

QVariant FuzzwinItem::data(int column) const
{
    return itemData.value(column);
}

bool FuzzwinItem::insertChildren(int position, int count, int columns)
{
    if (position < 0 || position > childItems.size())    return false;

    for (int row = 0; row < count; ++row) {
        QVector<QVariant> data(columns);
        FuzzwinItem *item = new FuzzwinItem(data, this);
        childItems.insert(position, item);
    }

    return true;
}

bool FuzzwinItem::insertColumns(int position, int columns)
{
    if (position < 0 || position > itemData.size())   return false;

    for (int column = 0; column < columns; ++column)  itemData.insert(position, QVariant());

    foreach (FuzzwinItem *child, childItems)  child->insertColumns(position, columns);

    return true;
}

FuzzwinItem *FuzzwinItem::parent()
{
    return parentItem;
}

bool FuzzwinItem::removeChildren(int position, int count)
{
    if (position < 0 || position + count > childItems.size())    return false;

    for (int row = 0; row < count; ++row)  delete childItems.takeAt(position);

    return true;
}

bool FuzzwinItem::removeColumns(int position, int columns)
{
    if (position < 0 || position + columns > itemData.size())    return false;

    for (int column = 0; column < columns; ++column)   itemData.remove(position);

    foreach (FuzzwinItem *child, childItems)   child->removeColumns(position, columns);

    return true;
}

bool FuzzwinItem::setData(int column, const QVariant &value)
{
    if (column < 0 || column >= itemData.size())    return false;

    itemData[column] = value;
    return true;
}

/********************/
/****** MODELE ******/
/********************/

TreeModel::TreeModel(const QStringList &headers, QObject *parent)
    : QAbstractItemModel(parent)
{
    QVector<QVariant> headerData;
    int index = 0;
    foreach (QString header, headers)  headerData << header;

    rootItem = new FuzzwinItem(headerData);
}

TreeModel::~TreeModel()
{
    delete rootItem;
}

int TreeModel::columnCount(const QModelIndex & /* parent */) const
{
    return rootItem->columnCount();
}

QVariant TreeModel::data(const QModelIndex &index, int role) const
{
    if (!index.isValid())    return QVariant();

    if (role != Qt::DisplayRole && role != Qt::EditRole)   return QVariant();

    FuzzwinItem *item = getItem(index);

    return item->data(index.column());
}

Qt::ItemFlags TreeModel::flags(const QModelIndex &index) const
{
    if (!index.isValid())  return 0;

    return Qt::ItemIsEditable | QAbstractItemModel::flags(index);
}

FuzzwinItem *TreeModel::getItem(const QModelIndex &index) const
{
    if (index.isValid()) 
    {
        FuzzwinItem *item = static_cast<FuzzwinItem*>(index.internalPointer());
        if (item)    return item;
    }
    return rootItem;
}

QVariant TreeModel::headerData(int section, Qt::Orientation orientation,
                               int role) const
{
    if (orientation == Qt::Horizontal && role == Qt::DisplayRole)
    {
        return rootItem->data(section);
    }
    else return QVariant();
}

QModelIndex TreeModel::index(int row, int column, const QModelIndex &parent) const
{
    if (parent.isValid() && parent.column() != 0)   return QModelIndex();

    FuzzwinItem *parentItem = getItem(parent);

    FuzzwinItem *childItem = parentItem->child(row);
    if (childItem)  return createIndex(row, column, childItem);
    else            return QModelIndex();
}

bool TreeModel::insertColumns(int position, int columns, const QModelIndex &parent)
{
    bool success;

    beginInsertColumns(parent, position, position + columns - 1);
    success = rootItem->insertColumns(position, columns);
    endInsertColumns();

    return success;
}

bool TreeModel::insertRows(int position, int rows, const QModelIndex &parent)
{
    FuzzwinItem *parentItem = getItem(parent);
    bool success;

    beginInsertRows(parent, position, position + rows - 1);
    success = parentItem->insertChildren(position, rows, rootItem->columnCount());
    endInsertRows();

    return success;
}

QModelIndex TreeModel::parent(const QModelIndex &index) const
{
    if (!index.isValid())    return QModelIndex();

    FuzzwinItem *childItem = getItem(index);
    FuzzwinItem *parentItem = childItem->parent();

    if (parentItem == rootItem)    return QModelIndex();
    else return createIndex(parentItem->childNumber(), 0, parentItem);
}

bool TreeModel::removeColumns(int position, int columns, const QModelIndex &parent)
{
    bool success;

    beginRemoveColumns(parent, position, position + columns - 1);
    success = rootItem->removeColumns(position, columns);
    endRemoveColumns();

    if (rootItem->columnCount() == 0)    removeRows(0, rowCount());

    return success;
}

bool TreeModel::removeRows(int position, int rows, const QModelIndex &parent)
{
    FuzzwinItem *parentItem = getItem(parent);
    bool success = true;

    beginRemoveRows(parent, position, position + rows - 1);
    success = parentItem->removeChildren(position, rows);
    endRemoveRows();

    return success;
}

int TreeModel::rowCount(const QModelIndex &parent) const
{
    FuzzwinItem *parentItem = getItem(parent);

    return parentItem->childCount();
}

bool TreeModel::setData(const QModelIndex &index, const QVariant &value, int role)
{
    if (role != Qt::EditRole)    return false;

    FuzzwinItem *item = getItem(index);
    bool result = item->setData(index.column(), value);

    if (result)   emit dataChanged(index, index);

    return result;
}

bool TreeModel::setHeaderData(int section, Qt::Orientation orientation,
                              const QVariant &value, int role)
{
    if (role != Qt::EditRole || orientation != Qt::Horizontal)   return false;

    bool result = rootItem->setData(section, value);

    if (result)   emit headerDataChanged(orientation, section, section);

    return result;
}

#if 0
void TreeModel::setupModelData(const QStringList &lines, FuzzwinItem *parent)
{
    QList<FuzzwinItem*> parents;
    QList<int> indentations;
    parents << parent;
    indentations << 0;

    int number = 0;

    while (number < lines.count()) 
    {
        int position = 0;
        while (position < lines[number].length()) 
        {
            if (lines[number].mid(position, 1) != " ")    break;
            ++position;
        }

        QString lineData = lines[number].mid(position).trimmed();

        if (!lineData.isEmpty()) 
        {
            // Read the column data from the rest of the line.
            QStringList columnStrings = lineData.split("\t", QString::SkipEmptyParts);
            QVector<QVariant> columnData;
            for (int column = 0; column < columnStrings.count(); ++column)
            {
                columnData << columnStrings[column];
            }

            if (position > indentations.last()) 
            {
                // The last child of the current parent is now the new parent
                // unless the current parent has no children.

                if (parents.last()->childCount() > 0) 
                {
                    parents << parents.last()->child(parents.last()->childCount()-1);
                    indentations << position;
                }
            } 
            else 
            {
                while (position < indentations.last() && parents.count() > 0) 
                {
                    parents.pop_back();
                    indentations.pop_back();
                }
            }

            // Append a new item to the current parent's list of children.
            FuzzwinItem *parent = parents.last();
            parent->insertChildren(parent->childCount(), 1, rootItem->columnCount());
            for (int column = 0; column < columnData.size(); ++column)
            {
                parent->child(parent->childCount() - 1)->setData(column, columnData[column]);
            }

        }

        ++number;
    }
}
#endif
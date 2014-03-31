#include "fuzzwin_widgets.h"

// Bouton de selection personnalisé
FuzzwinButton::FuzzwinButton(QWidget *parent, const QString &text)
    : QPushButton(text, parent),
    _buttonStatus(false)    // non-OK par défaut
{
    // mise au rouge (couleur non-ok à la construction)
    this->setStyleSheet("background-color:rgb(255,50,20)");  
}

FuzzwinButton::~FuzzwinButton() {}

void FuzzwinButton::setButtonOk()
{
    this->setStyleSheet("background-color:rgb(100,255,100)");
    this->_buttonStatus = true;
    emit buttonStatusChanged();
}

void FuzzwinButton::setButtonError()
{
    this->setStyleSheet("background-color:rgb(255,50,20)");
    this->_buttonStatus = false;
    emit buttonStatusChanged();
}

bool FuzzwinButton::getStatus() const
{
    return (this->_buttonStatus);
}

// lignes de textes personnalisées pour accepter le "drag & drop"
// lorsqu'un texte est droppé et conforme, un signal "conforme" est émis (-> bouton au vert)
// sinon un signal "bad" est émis (-> bouton au rouge)

FuzzwinLineEdit::FuzzwinLineEdit(QWidget *parent) : QLineEdit(parent)
{
    // accpeter le drag, le drop, mais lecture seule
    this->setDragEnabled(true);   
    this->setAcceptDrops(true);
    this->setReadOnly(true);
    this->setSizePolicy(QSizePolicy::MinimumExpanding, QSizePolicy::Fixed);
}

void FuzzwinLineEdit::dragEnterEvent(QDragEnterEvent *e)
{
    // n'accepter que les URLS
    if (e->mimeData()->hasUrls()) 
    {
        QUrl url = e->mimeData()->urls().first();
        if ("file" == url.scheme()) e->acceptProposedAction();
    }
}

// initial input
InitialInputLineEdit::InitialInputLineEdit(QWidget *parent) : FuzzwinLineEdit(parent) {}

void InitialInputLineEdit::dropEvent(QDropEvent *e)
{
    // n'accepter que les URLS
    if (e->mimeData()->hasUrls()) 
    {
        QUrl url = e->mimeData()->urls().first();
        if ("file" == url.scheme())
        {           
            QFile path = url.toLocalFile();
            if (path.exists() && !QFileInfo(path).isDir())
            {
                emit conformData(); 
                this->setText(path.fileName());
                this->setCursorPosition(0);
                e->accept();
            }
            else  e->ignore(); 
        }
    }
}

// target path
TargetPathLineEdit::TargetPathLineEdit(QWidget *parent) : FuzzwinLineEdit(parent) {}

void TargetPathLineEdit::dropEvent(QDropEvent *e)
{
    // n'accepter que les URLS
    if (e->mimeData()->hasUrls()) 
    {
        QUrl url = e->mimeData()->urls().first();
        if ("file" == url.scheme())
        {
            emit newTargetDropped(url.toLocalFile());
            e->accept();
        }
    }
}

// resultsDir
ResultsDirLineEdit::ResultsDirLineEdit(QWidget *parent) : FuzzwinLineEdit(parent) {}

void ResultsDirLineEdit::dropEvent(QDropEvent *e)
{
    // n'accepter que les URLS
    if (e->mimeData()->hasUrls()) 
    {
        QUrl url = e->mimeData()->urls().first();
        QString path = url.toLocalFile();
        QFileInfo pathInfo(path);
        // transformation des liens symboliques en liens complets
        if (pathInfo.isSymLink()) pathInfo = QFileInfo(pathInfo.symLinkTarget());

        if ("file" == url.scheme() && pathInfo.isDir())
        {
            e->accept();
            emit newDirDropped(pathInfo.absoluteFilePath());
        }
    }
}


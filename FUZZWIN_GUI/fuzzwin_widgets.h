#pragma once

#include <QtGui/QDragEnterEvent>
#include <QtGui/QDropEvent>

#include <QtCore/QMimeData>
#include <QtCore/QFile>
#include <QtCore/QFileInfo>
#include <QtCore/QDir>

#include <QtWidgets/QMessageBox>
#include <QtWidgets/QPushButton>
#include <QtWidgets/QLineEdit>

#include "globals.h"

// Bouton de selection personnalisé
class FuzzwinButton : public QPushButton
{
    Q_OBJECT
private:
    bool _buttonStatus;     // état du bouton (donnée ok ou non)
public:
    FuzzwinButton(QWidget *parent, const QString &text);
    ~FuzzwinButton();

    bool getStatus() const; // status du bouton

signals:
    void buttonStatusChanged(); // émis lorsqu'un bouton a été modifié (ok ou error)

public slots:
    void setButtonOk();     // mise du bouton à OK     => couleur verte
    void setButtonError();  // mise du bouton à NON_OK => couleur rougeatre 
};

// lignes de textes personnalisées pour accepter le "drag & drop"
// seul le drag est commun, le drop dépend du type de ligne (classes dérivées)
class FuzzwinLineEdit : public QLineEdit
{
public:
    FuzzwinLineEdit(QWidget *parent);
protected:
    void dragEnterEvent(QDragEnterEvent *event);
};

// ligne de texte pour entrée initiale
class InitialInputLineEdit : public FuzzwinLineEdit
{
    Q_OBJECT
public:
    InitialInputLineEdit(QWidget *parent);
signals:
    void conformData();
protected:
    void dropEvent(QDropEvent *event);
};

// ligne de texte pour exécutable cible
class TargetPathLineEdit : public FuzzwinLineEdit
{
    Q_OBJECT
public:
    TargetPathLineEdit(QWidget *parent);
signals:
    void newTargetDropped(QString);
protected:
    void dropEvent(QDropEvent *event);
};

// ligne de texte pour dossier de résultats
class ResultsDirLineEdit : public FuzzwinLineEdit
{
    Q_OBJECT
public:
    ResultsDirLineEdit(QWidget *parent);
signals:
    void newDirDropped(QString);
protected:
    void dropEvent(QDropEvent *event);
};

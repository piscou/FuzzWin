#pragma once

#include <QtGui/QDragEnterEvent>
#include <QtGui/QDropEvent>

#include <QtWidgets/QPushButton>
#include <QtWidgets/QLineEdit>

// Bouton de selection personnalisé
class FuzzwinButton : public QPushButton
{
private:
    bool _buttonStatus;     // état du bouton (donnée ok ou non)
public:
    FuzzwinButton(QWidget *parent, const QString &text);
    ~FuzzwinButton();

    void setButtonOk();     // bouton OK  => couleur verte
    void setButtonError();  // bouton NON => couleur rougeatre
    bool getStatus() const; // status du bouton
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
public:
    InitialInputLineEdit(QWidget *parent);
protected:
    void dropEvent(QDropEvent *event);
};

// ligne de texte pour exécutable cible
class TargetPathLineEdit : public FuzzwinLineEdit
{
public:
    TargetPathLineEdit(QWidget *parent);
    bool check(const QString &path);
protected:
    void dropEvent(QDropEvent *event);
};

// ligne de texte pour dossier de résultats
class ResultsDirLineEdit : public FuzzwinLineEdit
{
public:
    ResultsDirLineEdit(QWidget *parent);
    int check(const QString &dirPath);
protected:
    void dropEvent(QDropEvent *event);
};

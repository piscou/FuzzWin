#include "fuzzwin_gui.h"
#include <qfiledialog>

FUZZWIN_GUI::FUZZWIN_GUI(QWidget *parent)
    : QMainWindow(parent)
{
    ui.setupUi(this);
}

FUZZWIN_GUI::~FUZZWIN_GUI()
{

}

void FUZZWIN_GUI::on_Q_selectPin_clicked()
{
    QString dir = QFileDialog::getExistingDirectory(this, tr("Select PIN directory"),
                                                QDir::currentPath(),
                                                QFileDialog::ShowDirsOnly);
    ui.Q_logWindow->insertPlainText(dir);
}

void FUZZWIN_GUI::on_Q_selectZ3_clicked()
{
    QString dir = QFileDialog::getExistingDirectory(this, tr("Select Z3 directory"),
                                                QDir::currentPath(),
                                                QFileDialog::ShowDirsOnly);
    ui.Q_logWindow->insertPlainText(dir);
}

void FUZZWIN_GUI::on_Q_selectInitialInput_clicked()
{
    QString filename = QFileDialog::getOpenFileName(this, tr("Select Initial Input"),
                                                QDir::currentPath());
    ui.Q_initialInput->setText(filename);
}

void FUZZWIN_GUI::on_Q_selectTarget_clicked()
{
    QString filename = QFileDialog::getOpenFileName(this, tr("Select Target"),
                                                QDir::currentPath(),
                                                ".exe");
    ui.Q_targetPath->setText(filename);
}

void FUZZWIN_GUI::on_Q_selectResultsDir_clicked()
{
    QString dir = QFileDialog::getExistingDirectory(this, tr("Select results directory"),
                                                QDir::currentPath(),
                                                QFileDialog::ShowDirsOnly);
    ui.Q_resultsDir->setText(dir);
}

import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.DesUnOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.SmulMemFiltrationGraded

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

namespace CrystallineSemistableComparison.D

open PAlg

variable (l : ℕ) [Fact l.Prime]

theorem des_Fil_zero (hA : ∀ n k, Des (AcrF l n) (algebraMap (Ainf l) (Acris l) (rtW l k))) (n k : ℕ) :
    Des (FilF l n 0) (algebraMap (Ainf l) (Acris l) (rtW l k)) :=
  (des_semi (RingHom.id (Acris l)) (testι l) (FilF l n 0) (AcrF l n) (fun A => fil0Inclusion A n)
    (fun A a x => filtration_zero_inclusion_smul A n a x) (fun A => filtration_zero_inclusion_bijective A n) (fun f x => fil0Inclusion_map f n x) _).2 (hA n k)

theorem des_Fil_succ (h : RIn l) (n r k : ℕ) (ih : Des (FilF l n r) (algebraMap (Ainf l) (Acris l) (rtW l (k + 2)))) :
    Des (FilF l n (r + 1)) (algebraMap (Ainf l) (Acris l) (rtW l k)) := by
  have hs := (des_ses (algebraMap (Ainf l) (Acris l)) (algebraMap (Ainf l) (Acris l)) (RingHom.id (Ainf l)) (testι l)
    (FilF l n (r + 1)) (FilF l n r) (UnF l n) (fun A => incF A n r) (fun A => grF h.2.2.2.2 A n r)
    (fun A a x => incF_smul A n r a x) (fun A a x => grF_smul h.2.2.2.2 A n r a x)
    (fun f x => incF_nat f n r x) (fun f x => grF_nat h.2.2.2.2 f n r x)
    (fun A => incF_inj A n r) (fun A => grF_exact h.2.2.2.2 A n r) (fun A => grF_surj h.2.2.2.2 A n r) (rtW l (k + 2))).2 ih
    (des_Un l h.1 h.2.2.2.1 n (k + 2))
  exact des_span (testι l) (FilF l n (r + 1)) {algebraMap (Ainf l) (Acris l) (rtW l (k + 2) ^ 3)} (by
    rintro a rfl; exact Or.inl hs) _ (Ideal.mem_span_singleton.2 (map_dvd _ (rtW_dvd l k).1))

theorem des_Fil_of (h : RIn l) (hA : ∀ n k, Des (AcrF l n) (algebraMap (Ainf l) (Acris l) (rtW l k))) (n r k : ℕ) :
    Des (FilF l n r) (algebraMap (Ainf l) (Acris l) (rtW l k)) := by
  induction r generalizing k with
  | zero => exact des_Fil_zero l hA n k
  | succ r ih => exact des_Fil_succ l h n r k (ih (k + 2))

end CrystallineSemistableComparison.D

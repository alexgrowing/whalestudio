import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabAtPair

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv.StabCoord

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF.QuotInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem hAd_add_left (z z' w : Fin n → AE F E) : hAd σ J (z + z') w = hAd σ J z w + hAd σ J z' w := by
  simp only [hAd, add_dotProduct]

theorem hAd_sub_left (z z' w : Fin n → AE F E) : hAd σ J (z - z') w = hAd σ J z w - hAd σ J z' w := by
  simp only [hAd, sub_dotProduct]

theorem hAd_neg_left (z w : Fin n → AE F E) : hAd σ J (-z) w = -hAd σ J z w := by
  simp only [hAd, neg_dotProduct]

theorem hAd_smul_left (s : AE F E) (z w : Fin n → AE F E) : hAd σ J (s • z) w = s * hAd σ J z w := by
  simp only [hAd, smul_dotProduct, smul_eq_mul]

theorem hAd_zero_left (w : Fin n → AE F E) : hAd σ J 0 w = 0 := by
  simp only [hAd, zero_dotProduct]

theorem hAd_add_right (z w w' : Fin n → AE F E) : hAd σ J z (w + w') = hAd σ J z w + hAd σ J z w' := by
  simp only [hAd, Pi.add_apply, map_add]
  rw [show (fun i => cA σ (w i) + cA σ (w' i)) = (fun i => cA σ (w i)) + (fun i => cA σ (w' i)) from rfl,
    Matrix.mulVec_add, dotProduct_add]

theorem hAd_neg_right (z w : Fin n → AE F E) : hAd σ J z (-w) = -hAd σ J z w := by
  simp only [hAd, Pi.neg_apply, map_neg]
  rw [show (fun i => -cA σ (w i)) = -(fun i => cA σ (w i)) from rfl, Matrix.mulVec_neg, dotProduct_neg]

theorem hAd_sub_right (z w w' : Fin n → AE F E) : hAd σ J z (w - w') = hAd σ J z w - hAd σ J z w' := by
  rw [sub_eq_add_neg, hAd_add_right, hAd_neg_right, ← sub_eq_add_neg]

theorem hAd_smul_right (s : AE F E) (z w : Fin n → AE F E) : hAd σ J z (s • w) = cA σ s * hAd σ J z w := by
  simp only [hAd, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => cA σ s * cA σ (w i)) = cA σ s • (fun i => cA σ (w i)) from rfl, Matrix.mulVec_smul,
    dotProduct_smul, smul_eq_mul]

theorem hAd_zero_right (z : Fin n → AE F E) : hAd σ J z 0 = 0 := by
  have h := hAd_smul_right (σ := σ) (J := J) 0 z 0
  rw [zero_smul, map_zero, zero_mul] at h
  exact h

theorem hAd_herm (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (z w : Fin n → AE F E) :
    cA σ (hAd σ J z w) = hAd σ J w z := by
  have hc : ∀ i j, cA σ (incM F J i j) = incM F J j i := fun i j => by
    show cA σ (inclR (F := F) (AF F) (J i j)) = inclR (F := F) (AF F) (J j i)
    rw [← hJ j i]; rfl
  simp only [hAd, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_cA hσ, hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hAd_incV (u u' : Fin n → E) : hAd σ J (incV F u) (incV F u') = inclR (F := F) (AF F) (form σ J u u') := by
  simp only [hAd, form, incV, incM, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul]
  rfl

variable {R : Type} [Zero R] {ev : AF F → R}

theorem at_mulVec {m k : ℕ} (A : Matrix (Fin k) (Fin m) (AE F E)) {w : Fin m → AE F E} (hw : At ev w) :
    At ev (A *ᵥ w) := fun u hu => by
  rw [← Matrix.mulVec_smul, hw u hu, Matrix.mulVec_zero]

theorem at_hAd_left {z : Fin n → AE F E} (hz : At ev z) (w : Fin n → AE F E) : At ev (hAd σ J z w) := fun u hu => by
  rw [hAd, ← smul_dotProduct, hz u hu, zero_dotProduct]

theorem at_hAd_right (z : Fin n → AE F E) {w : Fin n → AE F E} (hw : At ev w) : At ev (hAd σ J z w) := fun u hu => by
  have h0 : (u • fun i => cA σ (w i)) = 0 := funext fun i => by
    show u • cA σ (w i) = 0
    rw [← map_smul, show u • w i = (u • w) i from rfl, hw u hu]
    simp
  rw [hAd, ← dotProduct_smul, ← Matrix.mulVec_smul, h0, Matrix.mulVec_zero, dotProduct_zero]

theorem cA_base (σ : E →ₐ[F] E) (a : AF F) : cA σ (algebraMap (AF F) (AE F E) a) = algebraMap (AF F) (AE F E) a := by
  change a ⊗ₜ[F] σ 1 = a ⊗ₜ[F] (1 : E)
  rw [map_one]

theorem topRing : IsTopologicalRing (AE F E) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  exact IsModuleTopology.isTopologicalRing (AF F) _

theorem cA_cont (σ : E →ₐ[F] E) : Continuous (cA σ) := by
  haveI : IsTopologicalRing (AE F E) := topRing
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) _ ?_
  have : Continuous (algebraMap (AF F) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AE F E))
  exact this.congr fun a => (cA_base σ a).symm

theorem continuous_hAd : Continuous fun p : (Fin n → AE F E) × (Fin n → AE F E) => hAd σ J p.1 p.2 := by
  haveI : IsTopologicalRing (AE F E) := topRing
  have h2 : Continuous fun p : (Fin n → AE F E) × (Fin n → AE F E) => fun i => cA σ (p.2 i) :=
    continuous_pi fun i => (cA_cont σ).comp ((continuous_apply i).comp continuous_snd)
  exact continuous_fst.dotProduct (continuous_const.matrix_mulVec h2)

theorem continuous_mat_pair (X : Spc F E n) (ev : AF F → R) (x y : Fin n → E) :
    Continuous fun l : stabAtPair σ X ev x y => mat l.1.1.1 :=
  Units.continuous_val.comp (continuous_subtype_val.comp (continuous_subtype_val.comp
    (continuous_subtype_val.comp continuous_subtype_val)))

theorem ext_of_frame {m : ℕ} {X Y : Fin n → AE F E} {I : Matrix (Fin n) (Fin m) (AE F E)}
    {P : Matrix (Fin m) (Fin n) (AE F E)} (hP : ∀ z, z = hAd σ J z Y • X + I *ᵥ (P *ᵥ z) + hAd σ J z X • Y)
    {A B : Matrix (Fin n) (Fin n) (AE F E)} (hX : A *ᵥ X = B *ᵥ X) (hY : A *ᵥ Y = B *ᵥ Y) (hI : A * I = B * I) :
    A = B := by
  have h : ∀ z, A *ᵥ z = B *ᵥ z := fun z => by
    rw [hP z]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hX, hY, hI]
  exact Matrix.toLin'.injective (LinearMap.ext h)

end GlobalTheory.ThK.LemF.QuotInv.StabCoord

end

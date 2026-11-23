import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
open scoped TensorProduct

namespace GlobalTheory.AdIsomImage

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.NormSum.AdLattice (lat)

section Ring

variable {A : Type} [CommRing A] {n : ℕ}

theorem inv_mul_mulVec (g β : GL (Fin n) A) (y : Fin n → A) :
    ((g * β)⁻¹).val *ᵥ y = (β⁻¹).val *ᵥ ((g⁻¹).val *ᵥ y) := by
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

theorem gram_mul (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (g β : GL (Fin n) A)
    (h : Formalism.UG.cT σ g.val * J * g.val = J) :
    Formalism.UG.cT σ (g * β).val * J * (g * β).val = Formalism.UG.cT σ β.val * J * β.val := by
  have hc : Formalism.UG.cT σ (g * β).val = Formalism.UG.cT σ β.val * Formalism.UG.cT σ g.val := by
    rw [Units.val_mul]
    exact GlobalTheory.StdFrames.cT_mul' σ _ _
  calc Formalism.UG.cT σ (g * β).val * J * (g * β).val
      = Formalism.UG.cT σ β.val * (Formalism.UG.cT σ g.val * J * g.val) * β.val := by
        rw [hc, Units.val_mul]
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ β.val * J * β.val := by rw [h]

end Ring

variable {D : D7}

theorem fin_cA (z : Formalism.L2.Theta.AE D) :
    ((swapAE D).comp (finPart D)) (cA D z) = cjA D (((swapAE D).comp (finPart D)) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e =>
    simp [cA, cjA, finPart, swapAE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem finE_unitary (V : HSp D) (g : GA D V) :
    Formalism.UG.cT (cjA D) (finE V g).val * V.gram.map (inc D) * (finE V g).val = V.gram.map (inc D) := by
  have hg : Formalism.UG.cT (cA D) (g.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) * V.gram.map (incA D) *
      (g.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = V.gram.map (incA D) := g.2
  have key := congrArg ((swapAE D).comp (finPart D)).mapMatrix hg
  simp only [RingHom.mapMatrix_apply, Matrix.map_mul] at key
  have hcT : ∀ M : Matrix (Fin V.rank) (Fin V.rank) (AE D),
      (Formalism.UG.cT (cA D) M).map ((swapAE D).comp (finPart D)) =
        Formalism.UG.cT (cjA D) (M.map ((swapAE D).comp (finPart D))) := by
    intro M
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply]
    exact fin_cA (M j i)
  have hJ : (V.gram.map (incA D)).map ((swapAE D).comp (finPart D)) = V.gram.map (inc D) := by
    rw [Matrix.map_map]
    congr 1
  have hfin : ((finE V g).val : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) =
      (g.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map ((swapAE D).comp (finPart D)) := rfl
  rw [hcT, hJ] at key
  rw [hfin]
  exact key

theorem carries_iff {n : ℕ} (g : GL (Fin n) (EAf D)) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    Formalism.L2.Herm.Carries g Λ Λ' ↔ ∀ y, y ∈ hat Λ' ↔ (g⁻¹).val *ᵥ y ∈ hat (D := D) Λ := by
  unfold Formalism.L2.Herm.Carries
  exact forall_congr' fun y => Iff.rfl

theorem imageSt (D : D7) : ImageSt D := by
  intro V Λ hΛ d _hd
  obtain ⟨β, rfl, hβ⟩ := exists_orth hΛ
  have hcar : Formalism.L2.Herm.Carries (finE V d) (lat β) (lat (finE V d * β)) := by
    rw [carries_iff]
    intro y
    rw [mem_hat_lat, mem_hat_lat, inv_mul_mulVec]
  have hgram : GlobalTheory.StdFrames.gramOf V (finE V d * β) = 1 :=
    (gram_mul (cjA D) (V.gram.map (inc D)) (finE V d) β (finE_unitary V d)).trans hβ
  refine ⟨⟨lat (finE V d * β), GlobalTheory.NormSum.AdLattice.lat_isLattice _, hcar⟩, fun Λ' hΛ' hc => ?_⟩
  have heq : Λ' = lat (finE V d * β) := by
    ext x
    rw [← inc_mem_hat_iff hΛ' x, ← inc_mem_hat_iff (GlobalTheory.NormSum.AdLattice.lat_isLattice (finE V d * β)) x]
    rw [carries_iff] at hc hcar
    rw [hc, hcar]
  rw [heq]
  exact isSelfDualC_lat (by rw [hgram]; exact unimod_one)

end GlobalTheory.AdIsomImage

end

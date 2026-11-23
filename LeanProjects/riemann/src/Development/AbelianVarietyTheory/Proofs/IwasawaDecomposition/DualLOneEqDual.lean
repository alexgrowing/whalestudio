import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsForgetsFrames
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.Mem.Col2.TC.dualL_one_eq_dual {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (σ : E →+* E)
    (hσ : ∀ x, σ x = star x) (L : Submodule (𝓞 E) (Fin n → E)) :
    dualL σ (1 : Matrix (Fin n) (Fin n) E) L = Formalism.HermitianLatticesTheory.dual (hStd E n) L := by
  have hmem : ∀ y, y ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) L ↔ ∀ x ∈ L, (∑ k, star (x k) * y k) ∈ (algebraMap (𝓞 E) E).range := by
    intro y
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
    rfl
  have hset : dualSet σ (1 : Matrix (Fin n) (Fin n) E) L = (Formalism.HermitianLatticesTheory.dual (hStd E n) L : Set _) := by
    ext y
    rw [SetLike.mem_coe, hmem]
    simp only [dualSet, Set.mem_setOf_eq]
    refine forall₂_congr fun x _ => ?_
    have : hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ k, star (x k) * y k := by
      simp [hform, Matrix.one_apply, hσ]
    rw [this]
  unfold dualL
  rw [hset, Submodule.span_eq]

theorem GlobalTheory.Mem.Col2.TC.ldG_eq_dual_hStd : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∀ (L : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)), LdG (I.rec7 l Z) i hi L = Formalism.HermitianLatticesTheory.dual (hStd B.host.E (B.R.N i)) L := by
  intro B X I hI hP l Z u a i hi L
  have hG : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  unfold LdG
  rw [hG]
  exact GlobalTheory.Mem.Col2.TC.dualL_one_eq_dual _ (fun x => rfl) L

end

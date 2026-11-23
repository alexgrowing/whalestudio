import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel Matrix

namespace GlobalTheory.IwaPlace

variable {D : D7}

def hermAt (S : HSp D) (x y : Fin S.rank → AE D) : AE D := ∑ i, ∑ j, cA D (y i) * gA S i j * x j

def IsSDAt (S : HSp D) (v : Pl D) (Λ : AddSubgroup (Fin S.rank → AE D)) : Prop :=
  (∀ y ∈ Λ, ∀ i, y i ∈ idAt D (· = v)) ∧
    (∃ m : ℕ, 0 < m ∧ ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ intAt D (· = v)) → (m : AE D) • y ∈ Λ) ∧
    ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ x ∈ Λ, hermAt S y x ∈ intAt D (· = v))

theorem mem_congGrp_iff (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, mt V g i j - (1 : Mx D V.rank V.rank) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  have e1 : ((1 : Mx D V.rank V.rank).map (Ideal.Quotient.mk I)) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have e2 : ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp (matHom V) g).1 = (mt V g).map (Ideal.Quotient.mk I) := rfl
  constructor
  · intro h i j
    rw [← Ideal.Quotient.eq]
    have := congrArg (fun u : GL (Fin V.rank) (AE D ⧸ I) => u.1 i j) h
    simp only [e2, Units.val_one] at this
    rw [← e1] at this
    exact this
  · intro h
    ext i j
    rw [e2, Units.val_one, ← e1]
    exact Ideal.Quotient.eq.2 (h i j)

theorem mulVec_mem_idAt {P : Pl D → Prop} {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ idAt D P) (i : Fin m) : (M *ᵥ y) i ∈ idAt D P :=
  by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem wittCoreEmbedding_preserves_supportedUnitarySubgroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {P : Pl D → Prop} {γ : GA D S₀}
    (hγ : γ ∈ grpAt S₀ P) : d.emb0 γ ∈ grpAt S P := by
  have hγ' := (mem_congGrp_iff S₀ (idAt D P) γ).1 hγ
  refine (mem_congGrp_iff S (idAt D P) _).2 fun i j => ?_
  have e : mt S (d.emb0 γ) - 1 = d.j0 ⬝ (mt S₀ γ - 1) ⬝ d.p0 := by
    rw [d.unitaryMatrix_wittCoreEmbedding, ← d.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  rw [← Matrix.sub_apply, e, Matrix.mul_apply]
  refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (by rw [Matrix.sub_apply]; exact hγ' l k)

end GlobalTheory.IwaPlace

end

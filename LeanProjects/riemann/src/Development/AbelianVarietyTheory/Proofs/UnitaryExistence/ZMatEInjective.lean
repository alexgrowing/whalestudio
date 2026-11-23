import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem cc_add' (x y : E) : cc (x + y) = cc x + cc y := by simp [cc]
theorem cc_mul' (x y : E) : cc (x * y) = cc x * cc y := by simp [cc]
theorem cc_neg' (x : E) : cc (-x) = -cc x := by simp [cc]
theorem cc_zero' : cc (0 : E) = 0 := by simp [cc]
theorem cc_cc' (x : E) : cc (cc x) = x := by simp [cc]
theorem cc_sum' {ι : Type} (s : Finset ι) (f : ι → E) : cc (∑ i ∈ s, f i) = ∑ i ∈ s, cc (f i) := by
  simp [cc]

theorem herm_add_l (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp [herm, add_mul, Finset.sum_add_distrib]

theorem herm_add_r (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  simp [herm, cc_add', mul_add, Finset.sum_add_distrib]

theorem herm_comb_l (G : Matrix (Fin r) (Fin r) E) (c : Fin ρ → E) (e : Fin ρ → Fin r → E)
    (y : Fin r → E) : herm G (∑ a, c a • e a) y = ∑ a, c a * herm G (e a) y := by
  simp only [herm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem herm_comb_r (G : Matrix (Fin r) (Fin r) E) (c : Fin ρ → E) (e : Fin ρ → Fin r → E)
    (x : Fin r → E) : herm G x (∑ a, c a • e a) = ∑ a, cc (c a) * herm G x (e a) := by
  simp only [herm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cc_sum', cc_mul', Finset.mul_sum]
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem herm_swap (X : Data E r) (x y : Fin r → E) : herm X.Gm x y = cc (herm X.Gm y x) := by
  simp only [herm, cc_sum', cc_mul', cc_cc', X.Gm_herm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem herm_nondeg (X : Data E r) (w : Fin r → E) (h : ∀ v, herm X.Gm v w = 0) : w = 0 := by
  have h1 : X.Gm *ᵥ (fun b => cc (w b)) = 0 := by
    funext k
    have := h (Pi.single k 1)
    simpa [herm, Pi.single_apply, Matrix.mulVec, dotProduct] using this
  have h2 := Matrix.eq_zero_of_mulVec_eq_zero X.Gm_det h1
  funext b
  have h3 : cc (w b) = 0 := congrFun h2 b
  rw [← cc_cc' (w b), h3, cc_zero']
  rfl

theorem zMatE_mulVec (X : Data E r) (e : Fin ρ → Fin r → E) (β : Matrix (Fin ρ) (Fin ρ) E)
    (v : Fin r → E) :
    FJ.zMatE X e β *ᵥ v = v + ∑ a, (∑ b, β a b * herm X.Gm v (e b)) • e a := by
  funext k
  simp only [FJ.zMatE, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, herm, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun m _ => ?_
  ring

theorem zMatE_zero (X : Data E r) (e : Fin ρ → Fin r → E) : FJ.zMatE X e 0 = 1 := by
  ext k l
  simp [FJ.zMatE, Matrix.one_apply]

theorem zMatE_add (X : Data E r) (cu : FJ.CuspFD X ρ) (β β' : Matrix (Fin ρ) (Fin ρ) E) :
    FJ.zMatE X cu.e (β + β') = FJ.zMatE X cu.e β * FJ.zMatE X cu.e β' := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← Matrix.mulVec_mulVec]
  simp only [zMatE_mulVec, herm_add_l, herm_comb_l, cu.iso, mul_zero, Finset.sum_const_zero,
    add_zero, Matrix.add_apply, add_mul, Finset.sum_add_distrib, add_smul]
  abel

theorem zMatE_unitary (X : Data E r) (cu : FJ.CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E)
    (hβ : FJ.IsSkew β) (u v : Fin r → E) :
    herm X.Gm (FJ.zMatE X cu.e β *ᵥ u) (FJ.zMatE X cu.e β *ᵥ v) = herm X.Gm u v := by
  simp only [zMatE_mulVec, herm_add_l, herm_add_r, herm_comb_l, herm_comb_r, cu.iso, mul_zero,
    Finset.sum_const_zero, add_zero, cc_sum', cc_mul', hβ _ _, ← herm_swap, Finset.sum_mul]
  rw [add_assoc, add_eq_left, Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun b _ => ?_
  ring

theorem zMatE_injective (X : Data E r) (cu : FJ.CuspFD X ρ) :
    Function.Injective (FJ.zMatE X cu.e) := by
  intro β β' h
  have h1 : ∀ v a, ∑ b, β a b * herm X.Gm v (cu.e b) = ∑ b, β' a b * herm X.Gm v (cu.e b) := by
    intro v a
    have h2 := congrArg (· *ᵥ v) h
    simp only [zMatE_mulVec, add_right_inj] at h2
    exact Fintype.linearIndependent_iffₛ.1 cu.ind _ _ h2 a
  ext a b
  have h3 : ∑ b, cc (β a b - β' a b) • cu.e b = 0 := by
    refine herm_nondeg X _ fun v => ?_
    simp only [herm_comb_r, cc_cc', sub_mul, Finset.sum_sub_distrib, h1 v a, sub_self]
  have h4 : cc (β a b - β' a b) = 0 := Fintype.linearIndependent_iff.1 cu.ind _ h3 b
  rw [← sub_eq_zero, ← cc_cc' (β a b - β' a b), h4, cc_zero']

def zGamSub (X : Data E r) (cu : FJ.CuspFD X ρ) : AddSubgroup (Matrix (Fin ρ) (Fin ρ) E) where
  carrier := FJ.zGam X cu
  zero_mem' := ⟨fun a b => by simp [cc_zero'], 1, X.Γ.one_mem, by simp [zMatE_zero]⟩
  add_mem' := by
    rintro β β' ⟨h, γ, hγ, e⟩ ⟨h', γ', hγ', e'⟩
    refine ⟨fun a b => ?_, γ * γ', X.Γ.mul_mem hγ hγ', ?_⟩
    · rw [Matrix.add_apply, Matrix.add_apply, cc_add', h, h']; ring
    · rw [zMatE_add, ← e, ← e', Units.val_mul]
  neg_mem' := by
    rintro β ⟨h, γ, hγ, e⟩
    refine ⟨fun a b => ?_, γ⁻¹, X.Γ.inv_mem hγ, ?_⟩
    · rw [Matrix.neg_apply, Matrix.neg_apply, cc_neg', h]
    · refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [e, ← zMatE_add, add_neg_cancel, zMatE_zero]

end GlobalTheory.CuspCentre

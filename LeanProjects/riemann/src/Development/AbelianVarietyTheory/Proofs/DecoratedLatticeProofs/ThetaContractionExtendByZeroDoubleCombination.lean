import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHZeroRight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ContrComb

variable {D : D7}

theorem heisO_resS_symm_zero {V₀ A L : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (o : OrthDec V₀ A L) (S : HSp D)
    (f : WO V₀ S → ℂ) (a u : WO A S) (x : WO L S) :
    heisO ψ V₀ S ((o.resS S).symm (a, 0)) f ((o.resS S).symm (u, x)) =
      ψ (symplOH A S u a) * f ((o.resS S).symm (u + a, x)) := by
  have h1 : (o.resS S).symm (u, x) + (o.resS S).symm (a, 0) = (o.resS S).symm (u + a, x) := by
    rw [← map_add]; simp
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_right, add_zero, h1]

theorem heisO_resT_symm_zero {T A L : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (o : OrthDec T A L) (S : HSp D)
    (f : WO S T → ℂ) (b v : WO S A) (x : WO S L) :
    heisO ψ S T ((o.resT S).symm (b, 0)) f ((o.resT S).symm (v, x)) =
      ψ (symplOH S A v b) * f ((o.resT S).symm (v + b, x)) := by
  have h1 : (o.resT S).symm (v, x) + (o.resT S).symm (b, 0) = (o.resT S).symm (v + b, x) := by
    rw [← map_add]; simp
  simp only [heisO]
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_right, add_zero, h1]

theorem comb_extS {V₀ A L : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (o : OrthDec V₀ A L) (S : HSp D)
    (c : WO A S →₀ ℂ) (f : WO V₀ S → ℂ) :
    comb ψ V₀ S (extS o S c) f = ∑ a ∈ c.support, c a • heisO ψ V₀ S ((o.resS S).symm (a, 0)) f := by
  have inj : Function.Injective fun a : WO A S => (o.resS S).symm (a, 0) := fun a b h =>
    (Prod.ext_iff.1 ((o.resS S).symm.injective h)).1
  exact Finsupp.sum_mapDomain_index_inj (h := fun u x => x • heisO ψ V₀ S u f) inj

theorem comb_extT {T A L : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (o : OrthDec T A L) (S : HSp D)
    (c : WO S A →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (extT o S c) f = ∑ b ∈ c.support, c b • heisO ψ S T ((o.resT S).symm (b, 0)) f := by
  have inj : Function.Injective fun b : WO S A => (o.resT S).symm (b, 0) := fun a b h =>
    (Prod.ext_iff.1 ((o.resT S).symm.injective h)).1
  exact Finsupp.sum_mapDomain_index_inj (h := fun u x => x • heisO ψ S T u f) inj

theorem contr_comb_ext : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D)
    (vL : VolM D B'.L.rank S.rank) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ),
    (∀ (u : WO B.A S) (v : WO S B'.A), IntegrableOn (fun w => f₂ ((B'.o.resT S).symm (v, w)) *
      f₁ ((B.o.resS S).symm (u, l.κ S w))) vL.𝓕 vL.μ) →
    ∀ (c : WO B.A S →₀ ℂ) (c' : WO S B'.A →₀ ℂ),
      contr l S vL (comb ψ B.V₀ S (extS B.o S c) f₁) (comb ψ S B'.V₀ (extT B'.o S c') f₂) =
        biComb ψ B.A S B'.A c c' (contr l S vL f₁ f₂) := by
  intro D ρ σ B B' l S vL ψ f₁ f₂ hint c c'
  funext u v
  rw [comb_extS, comb_extT]
  simp only [contr, biComb, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO_resS_symm_zero,
    heisO_resT_symm_zero]
  simp only [heisO]
  have hI : ∀ a b, Integrable (fun w => f₂ ((B'.o.resT S).symm (v + b, w)) * f₁ ((B.o.resS S).symm (u + a, l.κ S w)))
      (vL.μ.restrict vL.𝓕) := fun a b => hint (u + a) (v + b)
  calc _ = ∫ w in vL.𝓕, ∑ a ∈ c.support, ∑ b ∈ c'.support, (c a * ψ (symplOH B.A S u a) * (c' b * ψ (symplOH S B'.A v b))) *
          (f₂ ((B'.o.resT S).symm (v + b, w)) * f₁ ((B.o.resS S).symm (u + a, l.κ S w))) ∂vL.μ := by
        congr 1
        funext w
        rw [mul_comm, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ a ∈ c.support, ∑ b ∈ c'.support, (c a * ψ (symplOH B.A S u a) * (c' b * ψ (symplOH S B'.A v b))) *
          contr l S vL f₁ f₂ (u + a) (v + b) := by
        rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => (hI a b).const_mul _]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_finset_sum _ fun b _ => (hI a b).const_mul _]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [integral_const_mul]
        rfl
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring

end GlobalTheory.ContrComb
end

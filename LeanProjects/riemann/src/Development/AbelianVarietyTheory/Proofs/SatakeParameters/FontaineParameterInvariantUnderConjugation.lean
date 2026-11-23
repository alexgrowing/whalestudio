import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WdConjAbove
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PstConj

open TensorProduct Module GlobalTheory.Pst.EnlargeCoeff

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
  {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'}

theorem tensQ_tensQ (f : V →ₗ[ℚ_[l]] V') (g : V' →ₗ[ℚ_[l]] V) (hgf : ∀ v, g (f v) = v)
    (x : V ⊗[ℚ_[l]] Bst P) : tensQ P g (tensQ P f x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [hgf]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def dpstUrCongr (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) :
    DpstUr P ρ ≃ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ' :=
  let f : V →ₗ[ℚ_[l]] V' := (e : V →ₗ[LL] V').restrictScalars ℚ_[l]
  let g : V' →ₗ[ℚ_[l]] V := (e.symm : V' →ₗ[LL] V).restrictScalars ℚ_[l]
  have hf : ∀ s v, f (ρ s v) = ρ' s (f v) := he
  have hg : ∀ s v, g (ρ' s v) = ρ s (g v) := fun s v => by
    apply e.injective
    change e (e.symm (ρ' s v)) = e (ρ s (e.symm v))
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  { toFun := fun x => toUr P ρ' (dQ P hf ((toUr P ρ).symm x))
    invFun := fun x => toUr P ρ (dQ P hg ((toUr P ρ').symm x))
    map_add' := fun x y => by simp only [map_add]
    map_smul' := fun c x => dQ_mulD P hf c _
    left_inv := fun x => Subtype.ext (tensQ_tensQ P f g (fun v => e.symm_apply_apply v) x.1)
    right_inv := fun x => Subtype.ext (tensQ_tensQ P g f (fun v => e.apply_symm_apply v) x.1) }

theorem isPst_congr (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (hV : IsPst P ρ) : IsPst P ρ' := by
  rw [IsPst, ← (dpstUrCongr P e he).rank_eq, hV]
  exact (e.restrictScalars ℚ_[l]).rank_eq

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw) (r r' : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)) (p : GL (Fin a) (Qbar l)), (∀ g, r' g = p * r g * p⁻¹) → IsPstAt P Bw r → IsPstAt P Bw r' ∧ wdAt P ι Bw h hj r' = wdAt P ι Bw h hj r := by
  intro E Ω _ _ _ _ _ l _ ι a P AI _ w A h O _ _ _ Bw hj r r' p hc hr
  have hr' : IsPstAt P Bw r' := by
    obtain ⟨L₁, r₁, h₁, hp⟩ := hr
    obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model p hc h₁
    exact ⟨L₂, r₂, hm, GlobalTheory.PstConj.isPst_congr P e he (GlobalTheory.PstExt.isPst_enlarge P Bw hL r₁ hp)⟩
  exact ⟨hr', GlobalTheory.ConjGal.wdAt_conj P ι Bw h hj r r' p hc hr hr'⟩

end GlobalTheory.PstConj

end

import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CompAtAdd
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchange

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilCH

variable {D : D7} {n : ℕ} {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem tens_cancel (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ)
    {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) {F G : (Fin V.rank → Fin n → ℂ) → ℂ}
    (h : tens θ τ fr F Ψ = tens θ τ fr G Ψ) : F = G := by
  funext u
  obtain ⟨x, hxu, hxo, hxf⟩ := DilBH.pointAt θ hθ τ fr hfr x₀ u
  have hΨx : Ψ x = Ψ x₀ := hΨ.1 x x₀ hxo hxf
  have := congrFun h x
  simp only [tens, hxu, hΨx] at this
  exact mul_right_cancel₀ hx₀ this

variable {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {ι : GR n →* G D n}
  {L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)}

theorem L_sub (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) (y : GR n) {f g : (Fin V.rank → Fin n → ℂ) → ℂ}
    (hf : IsSch f) (hg : IsSch g) : L y (f - g) = L y f - L y g := by
  have h := hL.2 y Ψ hΨ (f - g) (SchwartzDifferenceQuotient.isSch_sub hf hg)
  have e : (⟨tens θ τ fr (f - g) Ψ, hΨ.2 _ (SchwartzDifferenceQuotient.isSch_sub hf hg)⟩ : schwartzA θ V.rank n) =
      ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ - ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ :=
    Subtype.ext (by funext x; simp only [tens, Submodule.coe_sub]; show (f _ - g _) * _ = f _ * _ - g _ * _; ring)
  rw [e, map_sub, Submodule.coe_sub, hL.2 y Ψ hΨ f hf, hL.2 y Ψ hΨ g hg] at h
  refine tens_cancel hθ hfr hΨ hx₀ ?_
  rw [← h]; funext x
  show tens θ τ fr (L y f) Ψ x - tens θ τ fr (L y g) Ψ x = _
  simp only [tens]
  show _ = (L y f _ - L y g _) * _
  ring

theorem L_smul (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) (y : GR n) (a : ℂ) {f : (Fin V.rank → Fin n → ℂ) → ℂ}
    (hf : IsSch f) : L y (fun u => a * f u) = fun u => a * L y f u := by
  have h := hL.2 y Ψ hΨ _ (SchwartzDifferenceQuotient.isSch_smul a hf)
  have e : (⟨tens θ τ fr (fun u => a * f u) Ψ, hΨ.2 _ (SchwartzDifferenceQuotient.isSch_smul a hf)⟩ : schwartzA θ V.rank n) =
      a • ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ :=
    Subtype.ext (by funext x; simp [tens, mul_assoc])
  rw [e, map_smul, Submodule.coe_smul, hL.2 y Ψ hΨ f hf] at h
  refine tens_cancel hθ hfr hΨ hx₀ ?_
  rw [← h]; funext x; simp [tens, mul_assoc]

theorem L_mul (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) (y y' : GR n) {f : (Fin V.rank → Fin n → ℂ) → ℂ}
    (hf : IsSch f) : L (y * y') f = L y (L y' f) := by
  have h := hL.2 (y * y') Ψ hΨ f hf
  have h' : ω (ι y') ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ = ⟨tens θ τ fr (L y' f) Ψ, hΨ.2 _ (hL.1 y' f hf)⟩ :=
    Subtype.ext (hL.2 y' Ψ hΨ f hf)
  rw [map_mul, map_mul, Module.End.mul_apply, h', hL.2 y Ψ hΨ _ (hL.1 y' f hf)] at h
  exact tens_cancel hθ hfr hΨ hx₀ h.symm

theorem diffOn_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (r : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv r f) U := by
  induction r with
  | zero => simpa using hf
  | succ r ih => rw [iteratedDeriv_succ]; exact ih.deriv hU

theorem iteratedDeriv_ofReal {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hR : ∀ s : ℝ, (s : ℂ) ∈ U) (r : ℕ) : iteratedDeriv r (fun t : ℝ => f t) = fun t : ℝ => iteratedDeriv r f t := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd : DifferentiableAt ℂ (iteratedDeriv r f) t :=
      (diffOn_iteratedDeriv hU hf r).differentiableAt (hU.mem_nhds (hR t))
    rw [iteratedDeriv_succ]
    exact (hd.hasDerivAt.comp_ofReal).deriv

end PositivityTheory.Rg.Sw.Glob.DilCH

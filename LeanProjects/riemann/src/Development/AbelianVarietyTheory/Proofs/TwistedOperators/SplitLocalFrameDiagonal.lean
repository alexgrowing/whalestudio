import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIntegralInvNegXi0
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecMulEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFrameLatticeFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunctionalEquationLocalLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

theorem GlobalTheory.FrameFB.frame_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank))
    (ι ι' : Fin (σ + 1) → Fin (G.V (.grid (2 * σ + 2) 0)).rank) (s t : Fin (σ + 1) → k),
  p.v = v ∧ Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
  β.IsLat (G.Λ (.grid (2 * σ + 2) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
  Function.Injective ι ∧ Function.Injective ι' ∧ (∀ a b, ι' b = ι a → a = Fin.last σ ∧ b = Fin.last σ) ∧
  (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xFB F σ h' i q)) = Pi.single (ι q) 1) ∧
  (∀ q, t q • ((fun i => p.pr (cA D (xFB F σ h' i q))) ᵥ*
    ((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (ι' q) 1) ∧
  ∀ a ∈ (pcFB W F σ h h').A₁,
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = s q * (β.b' *ᵥ fun j => p.pr (a j q)) i) ∧
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = t q * ((fun j => p.pr (cA D (a j q))) ᵥ*
      ((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) i) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h' v hv
  obtain ⟨k, _, _, _, _, p, β, j, ϖ, hpv, hid, hlat, hmax, ⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩, hj, hcol, hperp⟩ :=
    GlobalTheory.StairFrameFJ.exists_frame D hq T L μ0 hL sc G W M hM F hF σ h' v hv
  have hϖ : (ϖ : k) ≠ 0 := by
    intro h0
    have h0' : ϖ = 0 := Subtype.ext h0
    have : IsLocalRing.maximalIdeal 𝒪[k] = ⊥ := by rw [hmax, h0', Ideal.span_singleton_eq_bot.2 rfl]
    exact IsDiscreteValuationRing.not_a_field _ this
  obtain ⟨hs, ht⟩ := GlobalTheory.FrameScale.clauses D hq T L μ0 hL sc G W M hM F hF σ h' k p β j (ϖ : k) (G.pl.depth sc v) hϖ hj hcol hperp
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, p, β,
    fun q => j ⟨q.1, by omega⟩, fun q => j ⟨2 * σ - q.1, by omega⟩, _, _, hpv, hid, hlat, ?_, ?_, ?_, hs, ht, ?_⟩
  · intro a b hab
    have := hj hab
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · intro a b hab
    have := congrArg Fin.val (hj hab)
    simp at this
    exact Fin.ext (by omega)
  · intro a b hab
    have := congrArg Fin.val (hj hab)
    simp at this
    constructor <;> exact Fin.ext (by simp; omega)
  · intro a ha
    have hu2 : (p.pr (incA D (star (-D.host.xi0)))) ≠ 0 := right_ne_zero_of_mul_eq_one hu₂
    refine ⟨fun q i => ?_, fun q i => ?_⟩
    · obtain ⟨z, hz, hz'⟩ := GlobalTheory.T.split_frame_lattice_functional D hq T L μ0 hL sc G W M hM F hF σ h h' v hv k p β ϖ hpv hid hlat hmax a ha q i
      exact ⟨z, hz, hz'⟩
    · obtain ⟨z, hz, hz'⟩ := GlobalTheory.ConjClause.functional_equation_local_lattice D hq T L μ0 hL sc G W M hM F hF σ h h' v hv k p β ϖ hpv hid hlat hmax a ha q i
      refine ⟨z * (if q.1 = σ then -1 else 1), Ideal.mul_mem_right _ _ hz, ?_⟩
      clear hperp hcol hs ht hlat
      have hϖn : (ϖ : k) ^ (G.pl.depth sc v * (2 * σ + 1 - q.1)) ≠ 0 := pow_ne_zero _ hϖ
      have hx : (p.pr (incA D (star (-D.host.xi0)))) ^ (q.1 + 1) ≠ 0 := pow_ne_zero _ hu2
      rw [← hz']
      generalize (p.pr (incA D (star (-D.host.xi0)))) ^ (q.1 + 1) = X at hx ⊢
      generalize (ϖ : k) ^ (G.pl.depth sc v * (2 * σ + 1 - q.1)) = Y at hϖn ⊢
      by_cases hqσ : q.1 = σ
      · simp only [hqσ, if_true]
        push_cast
        field_simp
      · simp only [hqσ, if_false]
        push_cast
        field_simp

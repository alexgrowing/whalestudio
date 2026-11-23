import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.ZonalCoeff

open Formalism.UG

theorem apply_heckeVec {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}
    (hK : IsCommensurated K) {h : G → ℂ} (hh : h ∈ Formalism.UG.Hecke ℂ K) (ρ : Representation ℂ G V) (x : V)
    (l : V →ₗ[ℂ] ℂ) : l (GlobalTheory.LFun.heckeVec ρ K h x) = ∑ᶠ c : G ⧸ K, h c.out * l (ρ c.out x) :=
  (l.toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec hK hh ρ x)).trans (finsum_congr fun c => by simp)

theorem eq_zero_of_doset_sum {G : Type} [Group G] {K : Subgroup G} (hK : IsCommensurated K) {w : G → ℂ}
    (hw : IsBiInv K w) (g : G) (e : ∑ᶠ c : G ⧸ K, dosetInd ℂ K g c.out * w c.out = 0) : w g = 0 := by
  classical
  have hfin := Formalism.UG.P.finite_support_cosets hK (Formalism.UG.Final.DosetIndMem G K ℂ g).2
  have hmem : ∀ c ∈ hfin.toFinset, c.out ∈ DoubleCoset.doubleCoset g (K : Set G) K := fun c hc => by
    by_contra hn
    exact (hfin.mem_toFinset.1 hc) (Set.indicator_of_notMem hn _)
  have h1 : ∀ c ∈ hfin.toFinset, dosetInd ℂ K g c.out * w c.out = w g := fun c hc => by
    obtain ⟨a, ha, b, hb, e'⟩ := DoubleCoset.mem_doubleCoset.1 (hmem c hc)
    rw [dosetInd, Set.indicator_of_mem (hmem c hc), Pi.one_apply, one_mul, e']
    exact hw ⟨a, ha⟩ ⟨b, hb⟩ g
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ fun c hc =>
      hfin.mem_toFinset.2 (left_ne_zero_of_mul hc),
    Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul] at e
  refine (mul_eq_zero.1 e).resolve_left (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨(g : G ⧸ K), ?_⟩))
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
  refine hfin.mem_toFinset.2 ?_
  change dosetInd ℂ K g _ ≠ 0
  rw [dosetInd, Set.indicator_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, k, k.2, by rw [hk, one_mul]⟩)]
  exact one_ne_zero

theorem coeff_zero_or_zonal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), IsSatVecU (ϖ : L) q ρ x α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∀ k ∈ KU σ n, ∀ g, ℓ (ρ (k * g) x) = ℓ (ρ g x)) → (ℓ x = 0 → ∀ g, ℓ (ρ g x) = 0) ∧ (ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal (ϖ : L) q α fun g => ℓ (ρ g x) / ℓ x) := by
  intro L _ _ _ ϖ σ q n hU V _ _ ρ x α hx l hl
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n
  have hbi : IsBiInv (KU σ n) fun g => l (ρ g x) := fun a b g => by
    beta_reduce
    rw [map_mul, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ b.2, hl _ a.2]
  refine ⟨fun h0 g => eq_zero_of_doset_sum hK hbi g ?_, fun h0 => ⟨fun a b g => ?_, ?_, fun h hh => ?_⟩⟩
  · have hm := Formalism.UG.Final.DosetIndMem _ (KU σ n) ℂ g
    rw [← apply_heckeVec hK hm, hx.2.2 _ hm, map_smul, h0, smul_zero]
  · exact congrArg (· / l x) (hbi a b g)
  · simpa using div_self h0
  · have e := apply_heckeVec hK hh ρ x ((l x)⁻¹ • l)
    rw [hx.2.2 h hh, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, inv_mul_cancel₀ h0, mul_one] at e
    rw [e]
    exact finsum_congr fun c => by simp [div_eq_inv_mul]

end GlobalTheory.ZonalCoeff

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.TateSpan

theorem exists_eq_p_smul_of_lev_one {p : ℕ} [Fact p.Prime] {M : Type} [CommGroup M]
    (s : GlobalTheory.HTLat.Tate p M) (hs : s.lev 1 = 1) :
    ∃ s' : GlobalTheory.HTLat.Tate p M, s = (p : ℤ_[p]) • s' := by
  have h1 : ∀ k, s.lev (k + 1) ^ p ^ k = 1 := fun k => by
    rw [add_comm, GlobalTheory.HTLat.Tate.lev_add_pow, hs]
  refine ⟨GlobalTheory.HTLat.Tate.mk (fun k => s.lev (k + 1)) fun k => ⟨h1 k, s.lev_succ (k + 1)⟩,
    GlobalTheory.HTLat.Tate.ext fun k => ?_⟩
  rw [GlobalTheory.HTLat.Tate.lev_smul, GlobalTheory.HTLat.Tate.lev_mk, GlobalTheory.PDiv.pow_digit_natCast (h1 k),
    s.lev_succ]

theorem span_range_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (tι : Dw.La →+ P.T),
    (∀ x : (Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A), x ^ p = 1 → ∃ a, (tι a).lev 1 = x) →
    Submodule.span ℤ_[p] (Set.range tι) = ⊤ := by
  intro E _ _ _ H Dw p _ _ P tι h
  set S := Submodule.span ℤ_[p] (Set.range tι)
  have hI : IsLocalRing.maximalIdeal ℤ_[p] ≤ (⊥ : Ideal ℤ_[p]).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hle : (⊤ : Submodule ℤ_[p] P.T) ≤ S ⊔ IsLocalRing.maximalIdeal ℤ_[p] • ⊤ := by
    intro t _
    have hx : t.lev 1 ^ p = 1 := by
      have := GlobalTheory.HTLat.Tate.lev_pow t 1
      rwa [pow_one] at this
    obtain ⟨a, ha⟩ := h _ hx
    have hs : (t - tι a).lev 1 = 1 := by
      have e := congrArg (·.lev 1) (show t = tι a + (t - tι a) by abel)
      simp only [GlobalTheory.HTLat.Tate.lev_add, ha] at e
      exact left_eq_mul.1 e
    obtain ⟨s', hs'⟩ := exists_eq_p_smul_of_lev_one _ hs
    have e : t = tι a + (p : ℤ_[p]) • s' := by rw [← hs']; abel
    rw [e]
    refine Submodule.add_mem_sup (Submodule.subset_span ⟨a, rfl⟩) (Submodule.smul_mem_smul ?_ trivial)
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  exact top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI hle)

end GlobalTheory.TateSpan

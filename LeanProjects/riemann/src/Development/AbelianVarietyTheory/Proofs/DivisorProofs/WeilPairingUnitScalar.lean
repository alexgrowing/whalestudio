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

namespace GlobalTheory.TateUnitPair

theorem lev_zsmul {p : ℕ} {M : Type} [CommGroup M] (t : Tate p M) (n : ℤ) (k : ℕ) :
    (n • t).lev k = t.lev k ^ n := by
  rfl

theorem lev_nsmul {p : ℕ} {M : Type} [CommGroup M] (t : Tate p M) (n : ℕ) (k : ℕ) :
    (n • t).lev k = t.lev k ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, Tate.lev_add, ih, pow_succ]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (tι : Dw.La →+ P.T) (ζ : ℕ → ℂ_[p]ˣ),
    (∀ k, 0 < k → IsPrimitiveRoot (ζ k) k) → (∀ k m, 0 < k → 0 < m → ζ (k * m) ^ m = ζ k) →
    (∀ (k : ℕ) a b, weil P.A (p ^ k) ((tι a).lev k) ((tι b).lev k) = ζ (p ^ k) ^ Dw.EF a b) →
    ∃ u : ℤ_[p], IsUnit u ∧ ∀ a b, pairT P.A P.eps (tι a) (tι b) = u * (Dw.EF a b : ℤ_[p]) := by
  intro E _ _ _ H Dw p _ _ P tι ζ hprim hcomp hweil
  have hp : p.Prime := Fact.out
  have hpk : ∀ k : ℕ, 0 < p ^ k := fun k => pow_pos hp.pos k
  let z : Tate p ℂ_[p]ˣ := Tate.mk (fun k => ζ (p ^ k)) fun k =>
    ⟨(hprim (p ^ k) (hpk k)).pow_eq_one, by
      rw [pow_succ]; exact hcomp (p ^ k) p (hpk k) hp.pos⟩
  refine ⟨P.eps.equiv.symm z, ?_, fun a b => ?_⟩
  · by_contra hu
    have hlt : ‖P.eps.equiv.symm z‖ < 1 := PadicInt.mem_nonunits.1 hu
    obtain ⟨c, hc⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 hlt
    have h1 : z = P.eps.equiv (P.eps.equiv.symm z) := (P.eps.equiv.apply_symm_apply z).symm
    rw [hc, ← smul_eq_mul, map_smul] at h1
    have h2 : z.lev 1 = 1 := by
      rw [h1]
      change ((p : ℤ_[p]) • P.eps.equiv c).lev 1 = 1
      rw [Nat.cast_smul_eq_nsmul, lev_nsmul]
      simpa using (P.eps.equiv c).lev_pow 1
    have h3 : IsPrimitiveRoot (ζ p) p := by simpa using hprim p hp.pos
    exact h3.ne_one hp.one_lt (by simpa [z] using h2)
  · have hw : weilT P.A p (tι a) (tι b) = (Dw.EF a b : ℤ) • z := Tate.ext fun k => by
      rw [lev_weilT, lev_zsmul, hweil]
      rfl
    change P.eps.equiv.symm (weilT P.A p (tι a) (tι b)) = _
    rw [hw, map_zsmul, zsmul_eq_mul, mul_comm]

end GlobalTheory.TateUnitPair

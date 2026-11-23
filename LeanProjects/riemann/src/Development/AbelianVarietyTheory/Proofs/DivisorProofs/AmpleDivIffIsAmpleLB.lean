import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem presents_lbPow_toLB' {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (k : ℕ) :
    Presents (k • D) (lbPow (toLB D) k) fun j => (j PUnit.unit).1.2 ^ k := by
  refine ⟨isLB_lbPow (isLB_toLB D) k, fun i j h => ?_, fun i x hx => ?_⟩
  · simp only [show (lbPow (toLB D) k).g i j = _ from lbPow_g _ k i j, Units.val_pow_eq_pow_val,
      LB.val_res, map_pow, fnOf_resG, fnOf_toLB_g]
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (Units.ne_zero _))]
  · exact ((i PUnit.unit).2.2 x ((lbPow_U _ k i).le hx)).nsmul k

theorem locus_rat {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (k : ℕ)
    (s : (lbPow (toLB D) k).Sec) :
    locus D k ((presents_lbPow_toLB' D k).rat s) = (nonzeroLocus s : Set X) :=
  Set.ext fun _ => (presents_lbPow_toLB' D k).generatesAt_rat_iff s

theorem rat_mem_sec {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (k : ℕ)
    (s : (lbPow (toLB D) k).Sec) : (presents_lbPow_toLB' D k).rat s ∈ Sec D k :=
  CartierDiv.mem_sections.1 ((presents_lbPow_toLB' D k).rat_mem s)

theorem ampleDiv_iff_isAmpleLB : ∀ (X : Scheme.{0}) [IsIntegral X] [CompactSpace X] (D : CartierDiv X),
    AmpleDiv D ↔ IsAmpleLB (toLB D) := by
  intro X _ hc D
  constructor
  · intro h
    refine ⟨isLB_toLB D, hc, fun x => ?_⟩
    obtain ⟨k, hk, u, hu, U, hUa, hU, hx⟩ := h x
    obtain ⟨s, hs⟩ := (presents_lbPow_toLB' D k).exists_rat_eq (CartierDiv.mem_sections.2 hu)
    have e : nonzeroLocus s = U := SetLike.coe_injective (by rw [hU, ← locus_rat D k s, hs])
    exact ⟨k, hk, s, e ▸ hx, e ▸ hUa⟩
  · intro h x
    obtain ⟨k, hk, s, hx, ha⟩ := h.exists_affine x
    exact ⟨k, hk, _, rat_mem_sec D k s, nonzeroLocus s, ha, (locus_rat D k s).symm, hx⟩

end GlobalTheory.Desc

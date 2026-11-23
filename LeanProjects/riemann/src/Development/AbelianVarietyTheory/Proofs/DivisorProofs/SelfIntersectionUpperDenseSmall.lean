import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolHomog
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBoundStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt

namespace GlobalTheory.DenseHt

theorem nonzeroLocus_nonempty {X : Scheme.{0}} [IsIntegral X] {M : LB X} (s : M.Sec) (hs : s ≠ 0) :
    (Out.nonzeroLocus s : Set X).Nonempty := by
  by_contra hne
  apply hs
  have h0 : ∀ i, s.f i = 0 := fun i => by
    refine (basicOpen_eq_bot_iff (s.f i)).1 ?_
    refine le_bot_iff.1 fun y hy => hne ⟨y, ?_⟩
    exact (le_iSup (fun k => X.basicOpen (s.f k)) i) hy
  obtain ⟨f, hf⟩ := s
  obtain rfl : f = fun _ => 0 := funext h0
  rfl

theorem exists_small_of_pos {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (D : ℕ)
    (h : 0 < arVol L D) : ∃ m : ℕ, 1 ≤ m ∧ ∃ s ∈ (L.pow m).smallSec, s ≠ 0 := by
  by_contra hne
  push Not at hne
  refine absurd h (not_lt.2 ?_)
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have e : (L.pow m).smallSec = {0} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨(L.pow m).zero_mem_smallSec, hne m hm⟩
  rw [e]
  simp

theorem selfInter_le_of_dense : GlobalTheory.Published.VolGe → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (a e : ℝ), L.SemiPos D → NefFib L → L.IsSelfInter a → Dense {x : X | IsAlgPt x ∧ ∃ b, IsPtHt L x b ∧ b ≤ e} → a ≤ ((D : ℝ) + 1) * e * gdeg L D := by
  intro hV hC k _ X _ p D hp L a e hS hN ha hd
  by_contra hlt
  push Not at hlt
  obtain ⟨c, hc, hec⟩ : ∃ c : ℝ, ((D : ℝ) + 1) * c * gdeg L D < a ∧ e < c := by
    have hcont : Continuous fun c : ℝ => ((D : ℝ) + 1) * c * gdeg L D := by fun_prop
    have h1 : ∀ᶠ c in 𝓝[>] e, ((D : ℝ) + 1) * c * gdeg L D < a :=
      nhdsWithin_le_nhds (hcont.continuousAt.eventually_lt continuousAt_const hlt)
    exact (h1.and self_mem_nhdsWithin).exists
  have h1 := hC.arShift k X p D hp L a (-c) ha
  have h2 := hV k X p D hp (L.shift (fun _ => -c) fun _ => rfl) _ hN (hS.shift _ _) h1
  have h3 : 0 < arVol (L.shift (fun _ => -c) fun _ => rfl) D := by
    refine lt_of_lt_of_le ?_ h2
    exact_mod_cast (by linarith : 0 < a + ((D : ℝ) + 1) * (-c) * gdeg L D)
  obtain ⟨m, hm, s, hs, hs0⟩ := exists_small_of_pos _ D h3
  obtain ⟨x, hx, hx1, b, hb, hbe⟩ :=
    hd.inter_open_nonempty _ (Out.nonzeroLocus s).isOpen (nonzeroLocus_nonempty s hs0)
  have := GlobalTheory.T.small_section_height_lower_bound k X p D hp L m c b x s hm hs hx hx1 hb
  linarith

end GlobalTheory.DenseHt

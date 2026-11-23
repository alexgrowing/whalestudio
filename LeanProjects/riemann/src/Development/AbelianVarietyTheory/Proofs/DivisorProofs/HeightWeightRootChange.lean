import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumSubConst

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

section General

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

theorem finite_pts_under (σ : F →+* ℂ) {x : Y.X} (hx : IsClosed ({x} : Set Y.X)) :
    Finite {z : Pts Y σ // under z = x} := by
  obtain ⟨N, hN, hc⟩ := HtTwist.exists_card Y.str x hx
  exact Nat.finite_of_card_ne_zero ((hc ℂ σ).trans_ne hN)

theorem finsum_under_add (σ : F →+* ℂ) {x : Y.X} (hx : IsClosed ({x} : Set Y.X)) (f g : Pts Y σ → ℝ) :
    ∑ᶠ (z : Pts Y σ) (_ : under z = x), (f z + g z) =
      (∑ᶠ (z : Pts Y σ) (_ : under z = x), f z) + ∑ᶠ (z : Pts Y σ) (_ : under z = x), g z := by
  have := finite_pts_under (Y := Y) σ hx
  letI := Fintype.ofFinite {z : Pts Y σ // under z = x}
  rw [← finsum_subtype_eq_finsum_cond, ← finsum_subtype_eq_finsum_cond, ← finsum_subtype_eq_finsum_cond,
    finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_add_distrib]

theorem finsum_under_mul (σ : F →+* ℂ) {x : Y.X} (hx : IsClosed ({x} : Set Y.X)) (a : ℝ) (f : Pts Y σ → ℝ) :
    ∑ᶠ (z : Pts Y σ) (_ : under z = x), a * f z = a * ∑ᶠ (z : Pts Y σ) (_ : under z = x), f z := by
  have := finite_pts_under (Y := Y) σ hx
  letI := Fintype.ofFinite {z : Pts Y σ // under z = x}
  rw [← finsum_subtype_eq_finsum_cond, ← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, Finset.mul_sum]

theorem finsum_under_sum {ι : Type} (s : Finset ι) (σ : F →+* ℂ) {x : Y.X} (hx : IsClosed ({x} : Set Y.X))
    (f : ι → Pts Y σ → ℝ) :
    ∑ᶠ (z : Pts Y σ) (_ : under z = x), ∑ i ∈ s, f i z = ∑ i ∈ s, ∑ᶠ (z : Pts Y σ) (_ : under z = x), f i z := by
  have := finite_pts_under (Y := Y) σ hx
  letI := Fintype.ofFinite {z : Pts Y σ // under z = x}
  simp only [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
  exact Finset.sum_comm

theorem ht_mk_eq (D : Y.Dv) (n : ℕ+) (m m' : ∀ σ, C.Met Y σ D) (ci : InfinitePlace F → ℝ)
    (lg : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) {x : Y.X} (hx : IsClosed ({x} : Set Y.X)) :
    (Adl.mk D n m ci lg).ht x = (Adl.mk D n m' ci lg).ht x -
      (∑ σ : F →+* ℂ, ∑ᶠ (z : Pts Y σ) (_ : under z = x), lnRatio (m σ) (m' σ) z) /
        (((n : ℕ) : ℝ) * (Module.finrank ℚ F : ℝ) * (Nat.card {y : AlgPt Y // below y.1 = x} : ℝ)) := by
  have h (σ : F →+* ℂ) : ∑ᶠ (z : Pts Y σ) (_ : under z = x),
      (Real.log (C.pn Y σ D (m σ) (C.cx Y σ ((eqn D x)⁻¹ : Y.Fnˣ)) z) / 2 - (n : ℕ) * ci (InfinitePlace.mk σ)) =
      (∑ᶠ (z : Pts Y σ) (_ : under z = x),
        (Real.log (C.pn Y σ D (m' σ) (C.cx Y σ ((eqn D x)⁻¹ : Y.Fnˣ)) z) / 2 - (n : ℕ) * ci (InfinitePlace.mk σ))) +
      ∑ᶠ (z : Pts Y σ) (_ : under z = x), lnRatio (m σ) (m' σ) z := by
    rw [← finsum_under_add σ hx]
    refine finsum_congr fun z => finsum_congr fun hz => ?_
    subst hz
    simp only [lnRatio, lnN, genAt]
    ring
  simp only [Adl.ht, h, Finset.sum_add_distrib]
  ring

end General

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) {C : CxSt F}

theorem parOf_rootSym (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : ℕ) : parOf (rootSym Dw a R τ i) = R := by
  classical
  have key (s : Sym E) (n : ℤ) (hn : n ≠ 0) (hs : s.2.1 = R) : parOf (Finsupp.single s n) = R := by
    have hne : (Finsupp.single s n).support.Nonempty := by
      rw [Finsupp.support_single_ne_zero _ hn]
      exact Finset.singleton_nonempty _
    rw [parOf, dif_pos hne]
    have : hne.choose = s := Finset.mem_singleton.1 (Finsupp.support_single_subset hne.choose_spec)
    rw [this, hs]
  rw [rootSym]
  split_ifs
  · exact key _ _ one_ne_zero rfl
  · exact key _ _ (by norm_num) rfl

theorem ht_adlOf_eq (hm : Mets Y C) (h₀ : ∀ (σ : F →+* ℂ) (n : Letter Dw → ℤ), C.Met Y.Y σ (divOf Y n))
    (w : Sym E →₀ ℤ) {R : Option ℝ} (hR : parOf w = R) {n : Letter Dw → ℤ} (hn : expo Dw w = n) {x : Y.Y.X}
    (hx : IsClosed ({x} : Set Y.Y.X)) :
    (adlOf Y hm w).ht x = (adlOf Y (fun _ => h₀) w).ht x -
      (∑ σ : F →+* ℂ, ∑ᶠ (z : Pts Y.Y σ) (_ : under z = x), lnRatio (hm R σ n) (h₀ σ n) z) /
        ((Module.finrank ℚ F : ℝ) * (Nat.card {y : AlgPt Y.Y // below y.1 = x} : ℝ)) := by
  subst hR hn
  have := ht_mk_eq (C := C) (divOf Y (expo Dw w)) 1 (fun σ => hm (parOf w) σ _) (fun σ => h₀ σ _) 0 (lgOf Y w) hx
  simpa [adlOf] using this

end Flag

theorem htWt_rootH_eq : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (u : D.what₂.Tau → Fin O.N → ℝ) (x : (O.var c).X), IsClosed ({x} : Set (O.var c).X) → O.htWt (O.rootH c) u x = O.htWt (O.root0 c ∅) u x + (∑ σ : D.what₂.LL →+* ℂ, ∑ᶠ (w : Pts (O.var c) σ) (_ : under w = x), O.chg c none u σ w) / ((Module.finrank ℚ D.what₂.LL : ℝ) * (Nat.card {y : AlgPt (O.var c) // below y.1 = x} : ℝ)) := by
  intro D O c u x hx
  have key (r : DV.Rt D.what₂.Tau O.N) : (O.rootH c r).ht x = (O.root0 c ∅ r).ht x -
      (∑ σ : D.what₂.LL →+* ℂ, ∑ᶠ (z : Pts (O.var c) σ) (_ : under z = x),
        lnRatio (O.met.hm c none σ (O.ex r)) (O.met.h0 c σ (O.ex r)) z) /
      ((Module.finrank ℚ D.what₂.LL : ℝ) * (Nat.card {y : AlgPt (O.var c) // below y.1 = x} : ℝ)) :=
    ht_adlOf_eq (O.Φ.C c) (O.met.hm c) (O.met.h0 c) _ (parOf_rootSym _ _ _ _) (expo_rootSym _ _ _ _ _) hx
  have hs (σ : D.what₂.LL →+* ℂ) : ∑ᶠ (w : Pts (O.var c) σ) (_ : under w = x), O.chg c none u σ w =
      ∑ r : DV.Rt D.what₂.Tau O.N, u r.1 r.2 * ∑ᶠ (z : Pts (O.var c) σ) (_ : under z = x),
        lnRatio (O.met.hm c none σ (O.ex r)) (O.met.h0 c σ (O.ex r)) z := by
    simp only [Setup.chg]
    rw [finsum_under_sum _ σ hx]
    exact Finset.sum_congr rfl fun r _ => finsum_under_mul σ hx _ _
  simp only [Setup.htWt, key, hs]
  rw [Finset.sum_comm, Finset.sum_div]
  simp only [← Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, mul_div_assoc]
  ring

end GlobalTheory.Mean4O

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleNefHermitianSmallSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionAmpleTwistNonvanishingFiniteSetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteControllingPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonnegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDictStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundleDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensorStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr

theorem exists_bound_nsq {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (M : HermLB p) (u : M.B.Sec) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), (M.φ σ).nsq (CxPts.secVal p σ u) y ≤ C := by
  have := hX.finite_emb
  have hb : ∀ σ : k →+* ℂ, ∃ K : ℝ, ∀ y, (M.φ σ).nsq (CxPts.secVal p σ u) y ≤ K := fun σ => by
    have := hX.compactSpace σ
    obtain ⟨K, hK⟩ := (isCompact_range ((M.cInf σ).continuous_nsq u)).bddAbove
    exact ⟨K, fun y => hK ⟨y, rfl⟩⟩
  choose K hK using hb
  have := Fintype.ofFinite (k →+* ℂ)
  refine ⟨∑ τ, |K τ| + 1, ?_, fun σ y => (hK σ y).trans ?_⟩
  · linarith [Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)]
  · have := Finset.single_le_sum (fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)) (Finset.mem_univ σ)
    linarith [le_abs_self (K σ)]

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

def Pair.shiftA (P : Pair p) (c : ℝ) : Pair p :=
  ⟨P.L, P.A.shift (fun _ => c) (fun _ => rfl), P.r, P.r', P.hr, P.hr'⟩

theorem Pair.nu_shiftA (P : Pair p) (c : ℝ) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    (P.shiftA c).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * c)) := by
  simp only [Pair.shiftA, Pair.nu, Pair.loc, HermLB.shift, Weight.addFn]
  have key : ∀ (n u v w : ℝ), n * Real.exp (-(u + v * (w + 2 * c)) / 2) =
      n * Real.exp (-(u + v * w) / 2) * Real.exp (-(v * c)) := by
    intro n u v w
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  exact key _ _ _ _

theorem Pair.nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f := by
  unfold Pair.nu; positivity

theorem not_unitAt_zero (x : X) : ¬ UnitAt x (0 : X.functionField) := by
  rintro ⟨a, ha, h⟩
  exact (ha.map (algebraMap _ X.functionField)).ne_zero h

end GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem exists_good_pair : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ L : HermLB p, ∃ (P : Pair p) (b : ℕ) (s t : X.functionField), P.L = L ∧ P.Good D b s t := by
  intro hC k _ X _ p D hX L
  obtain ⟨A₀, hAmp, hNef, s₀, hs₀, hs₀ne⟩ := GlobalTheory.T.exists_ample_nef_hermitian_smallSection hC k X p D hX
  obtain ⟨P, rfl, rfl⟩ := exists_pair L A₀
  have hrep := GlobalTheory.T.represents_base_bundles_and_trivial k X p P

  obtain ⟨e, -, he_rng, he_nu, he_loc⟩ := GlobalTheory.T.representedBundle_sections_rationalFunctions_dict k X p P 0 1 P.A hrep.2.1
  have hsH : e s₀ ∈ P.H 0 1 := by
    show e s₀ ∈ (P.H 0 1 : Set X.functionField)
    rw [← he_rng]; exact ⟨s₀, rfl⟩
  have hη : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s₀ := (GlobalTheory.sec_ne_zero_iff s₀).1 hs₀ne
  obtain ⟨i₀, hi₀⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart P.L.isLB (genericPoint X)
  obtain ⟨j₀, hj₀⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart P.A.isLB (genericPoint X)
  have hsne : e s₀ ≠ 0 := by
    intro h0
    have hu := (he_loc s₀ _ i₀ j₀ hi₀ hj₀).1 hη
    rw [h0] at hu
    exact not_unitAt_zero _ (by simpa [Pair.loc] using hu)
  have hs_le : ∀ σ y, P.nu 0 1 σ y (e s₀) ≤ 1 := fun σ y => by
    have h1 := he_nu s₀ σ y
    have h2 := hs₀ σ y
    have h3 := P.nu_nonneg 0 1 σ y (e s₀)
    nlinarith

  obtain ⟨S, hSfin, hS⟩ := GlobalTheory.T.exists_finite_set_controlling_regularity_of_quotient k X p D hX P (e s₀) hsH hsne

  obtain ⟨b, hb, u, hu⟩ := GlobalTheory.T.exists_section_ampleTwist_nonvanishing_finiteSet k X p D hX P.L.dual P.A hAmp (insert (genericPoint X) S) (hSfin.insert _)
  have hR1 : P.Rep (-1) 0 P.L.dual := by simpa using GlobalTheory.T.represents_hermitianLineBundle_dual k X p P 1 0 P.L hrep.1
  have hR2 : P.Rep 0 b (P.A.pow b) := by simpa using GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 0 1 P.A b hrep.2.1
  have hR : P.Rep (-1) b (P.L.dual.tens (P.A.pow b)) := by
    simpa using GlobalTheory.T.hermPairWithSections_represents_tensor k X p P (-1) 0 0 b _ _ hR1 hR2
  obtain ⟨e', -, he'_rng, he'_nu, he'_loc⟩ := GlobalTheory.T.representedBundle_sections_rationalFunctions_dict k X p P (-1) b _ hR
  have htH : e' u ∈ P.H (-1) b := by
    show e' u ∈ (P.H (-1) b : Set X.functionField)
    rw [← he'_rng]; exact ⟨u, rfl⟩
  have htne : e' u ≠ 0 := by
    intro h0
    have hv := (he'_loc u _ i₀ j₀ hi₀ hj₀).1 (hu (Set.mem_insert _ _))
    rw [h0] at hv
    exact not_unitAt_zero _ (by simpa [Pair.loc] using hv)
  obtain ⟨C, hC1, hCb⟩ := exists_bound_nsq hX _ u
  have ht_le : ∀ σ y, P.nu (-1) b σ y (e' u) ≤ C := fun σ y => by
    have h1 := he'_nu u σ y
    have h2 := hCb σ y
    have h3 := P.nu_nonneg (-1) b σ y (e' u)
    nlinarith

  set c := Real.log C with hc
  have hc0 : 0 ≤ c := Real.log_nonneg hC1
  have hCpos : 0 < C := by linarith
  have hexpc : Real.exp (-c) = C⁻¹ := by rw [Real.exp_neg, hc, Real.exp_log hCpos]
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hexpb : Real.exp (-((b : ℤ) * c)) ≤ C⁻¹ := by
    rw [← hexpc]; apply Real.exp_le_exp.2; push_cast; nlinarith
  refine ⟨P.shiftA c, b, e s₀, e' u, rfl, ?_⟩
  have hsub : ∀ (z x : X) (U : X.Opens), z ⤳ x → x ∈ U → z ∈ U := fun z x U h hx => h.mem_open U.isOpen hx
  exact {
    ample := hAmp
    nef := GlobalTheory.T.hermitianLineBundle_isNef_shift_of_nonneg k X p D hX P.A c hc0 hNef
    pos := hb
    s_mem := ⟨hsH, fun σ y => by
      rw [Pair.nu_shiftA]
      have := hs_le σ y
      have h4 : Real.exp (-(((1 : ℤ) : ℝ) * c)) ≤ 1 := by
        apply Real.exp_le_one_iff.2; push_cast; linarith
      have h5 := P.nu_nonneg 0 1 σ y (e s₀)
      nlinarith [Real.exp_pos (-(((1 : ℤ) : ℝ) * c))]⟩
    s_ne := hsne
    t_mem := ⟨htH, fun σ y => by
      rw [Pair.nu_shiftA]
      have := ht_le σ y
      have h5 := P.nu_nonneg (-1) b σ y (e' u)
      calc P.nu (-1) b σ y (e' u) * Real.exp (-((b : ℤ) * c)) ≤ C * C⁻¹ :=
            mul_le_mul this hexpb (Real.exp_pos _).le hCpos.le
        _ = 1 := mul_inv_cancel₀ hCpos.ne'⟩
    t_ne := htne
    reg := fun x i j hi hj g hg h1 => hS x i j hi hj (P.loc (-1) b (e' u) i j) g (htH x i j hi hj)
      (fun z hz hzx => (he'_loc u z i j (hsub z x _ hzx hi) (hsub z x _ hzx hj)).1 (hu (Set.mem_insert_of_mem _ hz)))
      hg h1 }

end GlobalTheory.VolBr

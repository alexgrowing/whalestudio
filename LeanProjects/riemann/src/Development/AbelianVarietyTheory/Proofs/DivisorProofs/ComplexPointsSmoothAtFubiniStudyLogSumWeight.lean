import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionPropertiesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.CanSmooth

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {y : CxPts p σ}

theorem cInfAt_log {f : CxPts p σ → ℝ} (h : CInfAt f y) (hpos : 0 < f y) :
    CInfAt (fun z => Real.log (f z)) y := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have hFy : 0 < F (fun a => ev p σ W (g a) y) := h₅.eq_of_nhds ▸ hpos
  refine ⟨W, ι, inferInstance, g, fun v => Real.log (F v), O ∩ F ⁻¹' Set.Ioi 0, h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_Ioi, ⟨h₃, hFy⟩,
    (h₄.mono Set.inter_subset_left).log fun v hv => (ne_of_gt hv.2), ?_⟩
  filter_upwards [h₅] with z hz
  rw [hz]

theorem cInfAt_sum {ι : Type} [DecidableEq ι] (s : Finset ι) {f : ι → CxPts p σ → ℝ}
    (h : ∀ l ∈ s, CInfAt (f l) y) : CInfAt (fun z => ∑ l ∈ s, f l z) y := by
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const (p := p) (0 : ℝ) y
  | insert a s ha ih =>
    have e : (fun z => ∑ l ∈ insert a s, f l z) = fun z => f a z + ∑ l ∈ s, f l z :=
      funext fun z => Finset.sum_insert ha
    rw [e]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun l hl => h l (Finset.mem_insert_of_mem hl))

theorem cInfAt_normSq_ratVal [IsIntegral X] {g : X.functionField} (hg : RegAt (under y) g) :
    CInfAt (fun z : CxPts p σ => ‖ratVal g z‖ ^ 2) y := by
  obtain ⟨U, hU, a, rfl⟩ := hg.exists_fnOf
  have hyU : y ∈ ptsIn p σ U := mem_ptsIn.2 hU
  have h₁ : CInfAt (fun z => ‖ev p σ U a z‖ ^ 2) y :=
    ⟨U, Unit, inferInstance, fun _ => a, fun v => ‖v ()‖ ^ 2, Set.univ, hyU, isOpen_univ, trivial,
      ((contDiff_apply ℝ ℂ ()).norm_sq ℂ).contDiffOn, EventuallyEq.rfl⟩
  refine h₁.congr ?_
  filter_upwards [(isOpen_ptsIn U).mem_nhds hyU] with z hz
  rw [ratVal_fnOf hz]

end GlobalTheory.HSAmp.CanSmooth

namespace GlobalTheory.HSAmp

open CanSmooth in

theorem cInfAt_canWeight : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p) (D e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ n : ℕ, 1 ≤ n → ∀ (σ : k →+* ℂ) (y : CxPts p σ), CInfAt (fun z : CxPts p σ => ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ z (x l) ^ (2 * n))) y := by
  intro k _ X _ p P D e x hx n _ σ y
  set i := pick (P.L.φ σ).isLB y
  set j := pick (P.A.φ σ).isLB y
  have hi : y ∈ ptsIn p σ (P.L.B.U i) := mem_pick _ y
  have hj : y ∈ ptsIn p σ (P.A.B.U j) := mem_pick _ y
  have hφ : CInfAt ((P.L.φ σ).φ i) y := P.L.cInf σ i y hi
  have hterm : ∀ l, CInfAt (fun z => P.nu e 0 σ z (x l) ^ (2 * n)) y := by
    intro l
    have hreg : RegAt (under y) (P.loc e 0 (x l) i j) := hx.mem l _ i j (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have h₂ := (cInfAt_normSq_ratVal hreg).comp₂ hφ
      (G := fun w => w.1 ^ n * Real.exp (-((e : ℝ) * n) * w.2))
      ((contDiff_fst.pow n).mul ((contDiff_const.mul contDiff_snd).exp))
    refine h₂.congr ?_
    filter_upwards [(isOpen_ptsIn _).mem_nhds hi, (isOpen_ptsIn _).mem_nhds hj] with z hzi hzj
    rw [nu_eq k X p P e 0 (x l) (hx.mem l) σ z i j hzi hzj, mul_pow, pow_mul, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hsum : CInfAt (fun z => ∑ l, P.nu e 0 σ z (x l) ^ (2 * n)) y :=
    cInfAt_sum Finset.univ fun l _ => hterm l
  obtain ⟨l₀, hl₀⟩ := hx.cover (under y)
  have hpos₀ : 0 < P.nu e 0 σ y (x l₀) :=
    mul_pos (norm_pos_iff.2 (ratVal_ne_zero (hl₀ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)))) (Real.exp_pos _)
  have hpos : 0 < ∑ l, P.nu e 0 σ y (x l) ^ (2 * n) :=
    lt_of_lt_of_le (pow_pos hpos₀ _)
      (Finset.single_le_sum (f := fun l => P.nu e 0 σ y (x l) ^ (2 * n))
        (fun l _ => (even_two_mul n).pow_nonneg _) (Finset.mem_univ l₀))
  exact (cInfAt_log hsum hpos).const_mul _

end GlobalTheory.HSAmp

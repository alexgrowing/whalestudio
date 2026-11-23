import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSNef.DenOne

open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.LBGerm

variable {X : Scheme.{0}} [IsIntegral X]

theorem isRatSec_lbPow {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) (τ : ℕ) :
    IsRatSec (lbPow L τ) fun c => r (c PUnit.unit) ^ τ := fun c c' h => by
  have l : (lbPow L τ).U c ⊓ (lbPow L τ).U c' ≤ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit) :=
    fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have e : (lbPow L τ).g c c' = res l (L.g (c PUnit.unit) (c' PUnit.unit)) ^ τ := by
    change ∏ _k : PUnit, _ = _
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rfl
  rw [e, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
    ← mul_pow, hr _ _ (l h)]
  exact congrArg (fun a => (a * _) ^ τ) (fnOf_resG l h _).symm

theorem res_mem_secOn (L : LB X) (V : X.Opens) (a : Γ(X, V)) :
    (fun J : PUnit → L.ι => resG X (inf_le_left : V ⊓ powChart L J ≤ V) a) ∈ secOn (lbPow L 0) V :=
  mem_secOn_of_germ _ fun y i j hV hi hj => by
    rw [gm_lbPow_g 0 (𝟙 X) y i j hi hj, pow_zero, Units.val_one, one_mul]
    exact (gs_res (𝟙 X) y _ (⟨hV, hi⟩ : y ∈ V ⊓ (lbPow L 0).U i) a).trans
      (gs_res (𝟙 X) y _ (⟨hV, hj⟩ : y ∈ V ⊓ (lbPow L 0).U j) a).symm

theorem unitAt_ne_zero {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : UnitAt x f) : f ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  exact (hc.map (algebraMap _ X.functionField)).ne_zero

theorem exists_den_one : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (f : X.functionField),
    ∃ (c : ℕ) (g : X.functionField), 0 < c ∧ g ≠ 0 ∧ g ∈ P.H 0 c ∧ g * f ∈ P.H 0 c := by
  intro k _ X _ p D _ P hA f
  haveI := hA.compactSpace
  haveI := hA.quasiSeparatedSpace
  have hL := hA.isLB
  obtain ⟨n, hn, s, hgs, haff⟩ := hA.exists_affine (genericPoint X)
  haveI : Nonempty (nonzeroLocus s) := ⟨⟨_, hgs⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X (nonzeroLocus s) haff
  obtain ⟨a, b, hb, hf⟩ := IsFractionRing.div_surjective (A := Γ(X, nonzeroLocus s)) f
  change fnOf _ hgs a / fnOf _ hgs b = f at hf
  have hβ : fnOf _ hgs b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  obtain ⟨Na, ha⟩ := exists_sec_eq_pow_mul hL s _ (res_mem_secOn P.A.B (nonzeroLocus s) a)
  obtain ⟨Nb, hb'⟩ := exists_sec_eq_pow_mul hL s _ (res_mem_secOn P.A.B (nonzeroLocus s) b)
  obtain ⟨u, hu⟩ := ha (max Na Nb + 1) (by omega)
  obtain ⟨v, hv⟩ := hb' (max Na Nb + 1) (by omega)
  have hρ := isRatSec_lbPow P.hr' (0 + n * (max Na Nb + 1))
  obtain ⟨e, he⟩ := RepDict.exists_quot (isLB_lbPow hL (0 + n * (max Na Nb + 1))) hρ
  have hmem : ∀ w : (lbPow P.A.B (0 + n * (max Na Nb + 1))).Sec,
      e w ∈ P.H 0 ((0 + n * (max Na Nb + 1) : ℕ) : ℤ) := by
    intro w x i j _ hj
    have hJ : x ∈ (lbPow P.A.B (0 + n * (max Na Nb + 1))).U (fun _ => j) := mem_powChart.2 hj
    have h1 := he w (fun _ => j) (gen_mem hJ)
    simp only [Pair.loc, zpow_zero, mul_one, zpow_natCast]
    rw [← Units.val_pow_eq_pow_val, h1]
    exact regAt_fnOf hJ _ _
  obtain ⟨j₀, hj₀⟩ := exists_chart hL (genericPoint X)
  have hJ₀ : genericPoint X ∈ powChart P.A.B (fun _ => j₀) := mem_powChart.2 hj₀
  have hVJ : genericPoint X ∈ nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) := ⟨hgs, hJ₀⟩
  have key : ∀ (w : (lbPow P.A.B (0 + n * (max Na Nb + 1))).Sec) (a' : Γ(X, nonzeroLocus s)),
      resG X (inf_le_right : nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) ≤ powChart P.A.B (fun _ => j₀))
          (powFn w (fun _ => j₀)) =
        resG X (inf_le_right : nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) ≤ powChart P.A.B (fun _ => j₀))
          (powFn s (fun _ => j₀)) ^ (max Na Nb + 1) *
        resG X (inf_le_left : nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) ≤ nonzeroLocus s) a' →
      e w * (P.r' j₀ : X.functionField) ^ (0 + n * (max Na Nb + 1)) =
        fnOf _ hJ₀ (powFn s (fun _ => j₀)) ^ (max Na Nb + 1) * fnOf _ hgs a' := by
    intro w a' h
    have h' := congrArg (fnOf _ hVJ) h
    rw [map_mul, map_pow, fnOf_resG, fnOf_resG, fnOf_resG] at h'
    rw [← Units.val_pow_eq_pow_val]
    exact (he w _ hJ₀).trans h'
  have eu := key u a (hu _)
  have ev := key v b (hv _)
  have hS : fnOf _ hJ₀ (powFn s (fun _ => j₀)) ≠ 0 := by
    exact unitAt_ne_zero ((unitAt_fnOf_iff hJ₀ hJ₀ _).2 ((mem_nonzeroLocus_iff_basicOpen s hJ₀).1 hgs))
  have hR : (P.r' j₀ : X.functionField) ^ (0 + n * (max Na Nb + 1)) ≠ 0 := pow_ne_zero _ (P.r' j₀).ne_zero
  refine ⟨0 + n * (max Na Nb + 1), e v, by positivity, fun h0 => ?_, hmem v, ?_⟩
  · rw [h0, zero_mul] at ev
    exact mul_ne_zero (pow_ne_zero _ hS) hβ ev.symm
  · have e1 : e u = _ := eq_div_of_mul_eq hR eu
    have e2 : e v = _ := eq_div_of_mul_eq hR ev
    have : e v * f = e u := by
      rw [e1, e2, ← hf]
      field_simp
    rw [this]
    exact hmem u

end GlobalTheory.HSNef.DenOne

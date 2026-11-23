import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesModPGenericOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionUnitsGenericOpen
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option autoImplicit false

noncomputable section

open GlobalTheory.FrameGlue.PowGlue GlobalTheory.FrameGlue.ModPTest GlobalTheory.TrueGeo.SmallSec in

theorem GlobalTheory.LatChain.isEqn_pow_div_of_reads : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (C : CxSt F) (V : Cover Y) (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ) (r : M.B.ι → V.X.functionFieldˣ) (hr : IsRatSec M.B r), NormsX V M lg r hr → ∀ (p m : ℕ), p.Prime → ∀ (A A' : Adl C Y) (c c' : V.X → V.X.functionFieldˣ), A'.D = A.D → Reads V p A c → Reads V p A' c' → (∀ v, resP v = p → ∀ e y, lg v e y = (m : ℝ) * (A.lg v e y - A'.lg v e y)) → ∀ x, Ov p x → (M.div hr).IsEqn x ((c x / c' x) ^ m) := by
  intro F _ _ Y C V M lg r hr hN p m hp A A' c c' hD hA hA' hlg x hx
  obtain ⟨hη, W, U, hW, hU, hu, hn⟩ := hA
  obtain ⟨hη', W', U', hW', hU', hu', hn'⟩ := hA'
  rw [hD] at hu' hn'
  obtain ⟨-, hru, hrn⟩ := hN
  haveI := RootLine.isPreimmersion_j V
  obtain ⟨i, hi⟩ : ∃ i, x ∈ M.B.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (by rw [M.isLB.cover]; trivial)
  have hE : (M.div hr).IsEqn x (r i) := (presents_divOfRatSec M.isLB hr).isEqn i x hi
  refine hE.iff_unitAt.2 ?_
  set t : V.X.functionField := (c x : V.X.functionField) / c' x with ht
  have ht0 : t ≠ 0 := div_ne_zero (c x).ne_zero (c' x).ne_zero
  set f : V.X.functionField := t ^ m / r i with hf
  suffices h : UnitAt x f by simpa [hf, ht] using h
  set O : V.X.Opens := U x ⊓ U' x ⊓ M.B.U i with hO
  have hrat : ∀ g : V.G.functionField, g * jm V hη (c' x) ≠ 0 →
      fnMap V.j hη t = g * jm V hη (c x) / (g * jm V hη (c' x)) := by
    intro g hg
    rw [mul_div_mul_left _ _ (left_ne_zero_of_mul hg), ht, map_div₀]
  have htu : ∀ z : V.G, V.j z ∈ O → UnitAt (V.j z) t := by
    intro z hz
    have h1 := hu x z hz.1.1
    have h2 := hu' x z hz.1.2
    have h3 : UnitAt z (fnMap V.j hη t) := by
      rw [hrat _ h2.ne_zero, div_eq_mul_inv]
      exact h1.mul h2.inv
    exact (unitAt_iff ht0).2 ⟨(regAt_fnMap_iff V.j hη).1 h3.regAt,
      (regAt_fnMap_iff V.j hη).1 (by rw [map_inv₀]; exact h3.inv.regAt)⟩
  have hfu : ∀ z : V.G, V.j z ∈ O → UnitAt (V.j z) f := by
    intro z hz
    rw [hf, div_eq_mul_inv]
    exact (unitAt_pow (htu z hz) m).mul (hru i z hz.2).inv
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : TrueGeo.Ext v) (y : AlgPt Y), below y.1 ∈ W ⊓ W' →
      ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 →
      spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ O →
      V.j (below z) ∈ O ∧ e.w (valAt (z ≫ V.j) f) = 1 := by
    intro v hv e y hy z yt e1 e2 hyt
    have hz : V.j (below z) ∈ O := by
      have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ O := by
        rw [← e2]
        exact hyt (Set.mem_univ _)
      exact h1
    refine ⟨hz, ?_⟩
    have hb : V.π (below z) = below y.1 := by rw [← e1]; rfl
    have h1 := hu x _ hz.1.1
    have h2 := hu' x _ hz.1.2
    rw [hb] at h1 h2
    have l1 := hn v hv e y hy.1 z yt e1 e2 x fun q hq => (hyt hq).1.1
    have l2 := hn' v hv e y hy.2 z yt e1 e2 x fun q hq => (hyt hq).1.2
    have l3 := hrn v e y z yt i e1 e2 fun q hq => (hyt hq).2
    have u3 : UnitAt (below (z ≫ V.j)) (r i : V.X.functionField) := hru i _ hz.2
    have u4 : UnitAt (below (z ≫ V.j)) t := htu _ hz
    have w1 := e.w.pos (valAt_ne_zero h1)
    have w2 := e.w.pos (valAt_ne_zero h2)
    have w3 := e.w.pos (valAt_ne_zero u3)
    have w4 := e.w.pos (valAt_ne_zero u4)
    have hlt : Real.log (e.w (valAt (z ≫ V.j) t)) = A.lg v e y - A'.lg v e y := by
      rw [← valAt_fnMap V.j hη z (htu _ hz).regAt, hrat _ h2.ne_zero, valAt_div h1.regAt h2, map_div₀,
        Real.log_div w1.ne' w2.ne', l1, l2]
    have hlog : Real.log (e.w (valAt (z ≫ V.j) t) ^ m) = Real.log (e.w (valAt (z ≫ V.j) (r i : V.X.functionField))) := by
      rw [Real.log_pow, hlt, ← l3, hlg v hv]
    have heq := Real.log_injOn_pos (pow_pos w4 m) w3 hlog
    rw [hf, valAt_div (regAt_pow u4.regAt m) u3, valAt_pow u4.regAt, map_div₀, map_pow, heq, div_self w3.ne']
  have hWW : genericPoint Y.X ∈ W ⊓ W' := ⟨hW, hW'⟩
  have hxO : x ∈ O := ⟨⟨hU x hx, hU' x hx⟩, hi⟩
  refine (unitAt_iff (div_ne_zero (pow_ne_zero _ ht0) (r i).ne_zero)).2 ⟨?_, ?_⟩
  · exact GlobalTheory.T.good_reduction_extends_regular F Y V p hp _ hWW O f (fun z hz => (hfu z hz).regAt)
      (fun v hv e y hy z yt e1 e2 hyt => (hval v hv e y hy z yt e1 e2 hyt).2.le) x hxO hx
  · refine GlobalTheory.T.good_reduction_extends_regular F Y V p hp _ hWW O f⁻¹ (fun z hz => (hfu z hz).inv.regAt)
      (fun v hv e y hy z yt e1 e2 hyt => ?_) x hxO hx
    obtain ⟨hz, h⟩ := hval v hv e y hy z yt e1 e2 hyt
    have u : UnitAt (below (z ≫ V.j)) f := hfu _ hz
    rw [← one_div, valAt_div (unitAt_one _).regAt u, valAt_one', map_div₀, h, map_one, div_one]

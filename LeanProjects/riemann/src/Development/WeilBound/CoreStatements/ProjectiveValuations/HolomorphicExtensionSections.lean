import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsVanBdOfMemExtVanZ
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OffZero

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS

theorem DifferentiableLines.holomorphic_extension_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (V : Unf Xo c σ r) (T : GlobalTheory.CompHS.TorFlag Xo c) (e : Ix D → ℤ) (k : V.Comp) (P : Frame (V.X k).Ψ r → ℂ) (h : (T.X.LL e).ι → GlobalTheory.CxPts (GlobalTheory.CompHS.flagStr T.X) σ → ℂ), GlobalTheory.CompanionTheory.Ar.HolExt.Reads V T e k P h → ∀ (m : ℕ) (as : Fin m → ℂ) (ss : Fin m → (T.X.LL e).Sec), h = ∑ j, as j • GlobalTheory.CxPts.secVal (GlobalTheory.CompHS.flagStr T.X) σ (ss j) → ∀ x ∈ (V.X k).dom, P x = ∑ j, as j * rdU V (GlobalTheory.CompanionTheory.Ar.OntoDef.ruleTop T.X e (GlobalTheory.Vanishing.H0.ofSec (GlobalTheory.CompHS.flagStr T.X) ⊤ (ss j))) k x := by
  intro E _ _ _ H D l Xo c r σ V T e k P h hR m as ss he x hx
  classical
  haveI : IsLocalRing (CAt σ) := (inferInstance : IsLocalRing ℂ)
  obtain ⟨i, hz⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing T.X.F.cover (T.X.ptY (V.un k ⟨x, hx⟩))
  have hl := T.X.lies_ptY (V.un k ⟨x, hx⟩)
  obtain ⟨Q, hQ⟩ := T.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd (V.un k ⟨x, hx⟩)) hl.1 i hz
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl
  have hO : ⊤ ≤ T.X.ptY (V.un k ⟨x, hx⟩) ⁻¹ᵁ flagOpen T.X := by
    rw [← T.X.pt_inc]
    exact GlobalTheory.FlagMod.le_preimage_map T.X.inc (top_le_inc T.X) le_top
  let y : GlobalTheory.CxPts (flagStr T.X) σ := ⟨(T.X.ptY (S := CAt σ) (V.un k ⟨x, hx⟩) :), ptY_str (S := CAt σ) T.X (V.un k ⟨x, hx⟩)⟩
  have hy : y ∈ GlobalTheory.CxPts.ptsIn (flagStr T.X) σ ((T.X.LL e).U i) := hz
  haveI : _root_.IsReduced (CAt σ) := (inferInstance : _root_.IsReduced ℂ)
  have hs : h i y = ∑ j, as j * GlobalTheory.CxPts.secVal (flagStr T.X) σ (ss j) i y := by
    rw [he]
    exact (congrFun (Finset.sum_apply (show (T.X.LL e).ι from i) _ _) y).trans (Finset.sum_apply y _ _)
  rw [hR x hx i y hz Q t rfl hQ ht, hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have a : rdU V (ruleTop T.X e (GlobalTheory.Vanishing.H0.ofSec (flagStr T.X) ⊤ (ss j))) k x =
      toC (evR Xo c (ruleTop T.X e (GlobalTheory.Vanishing.H0.ofSec (flagStr T.X) ⊤ (ss j))) (V.un k ⟨x, hx⟩)) := dif_pos hx
  have b : GlobalTheory.CxPts.secVal (flagStr T.X) σ (ss j) i y = _ := GlobalTheory.CxPts.ev_eq hy _
  have d := evR_ruleTop (GlobalTheory.Vanishing.H0.ofSec (flagStr T.X) ⊤ (ss j)) hO hQ ht
  have f := GlobalTheory.Vanishing.H0.val_ofSec (p := flagStr T.X) (O := ⊤) (B := T.X.LL e) (T.X.ptY (V.un k ⟨x, hx⟩)) i le_top hz (ss j)
  rw [a, d, f, b, mul_left_comm]
  rfl

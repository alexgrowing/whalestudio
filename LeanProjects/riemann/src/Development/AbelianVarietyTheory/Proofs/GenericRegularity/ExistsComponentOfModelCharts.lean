import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsOpenSameModel
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FlagChartsCoverFramedFieldPoints
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin

open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.Reg
open scoped Matrix

noncomputable section

namespace GlobalTheory.OneComp

open GlobalTheory.CompModel GlobalTheory.SupGeneric

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem wchar_zero {S : Type} [CommRing S] (t : Ix Dw → Sˣ) : wchar (ex Dw 0 0) t = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  have : ex Dw 0 0 i = 0 := by rcases i with _ | ⟨τ, i⟩ <;> simp [ex]
  rw [this, pow_zero]

theorem evR_eq_natCast (hL : EvLaws Xo c) {h : GenFrEx Xo c} {χ : Rul Xo c} (hχ : χ ∈ sec Xo c 0 0) (C : FChart h)
    {L : Type} [Field L] [Algebra c.F L] (ψ : C.R →ₐ[c.F] L) {z w : FrPt Xo c L} {t : Ix Dw → Lˣ}
    (hz : FrMap ψ C.y z) (hb : FrBor t z w) (n : ℕ) (hn : evC h C.Z χ = n) : evR Xo c χ w = n := by
  have h1 : evR Xo c χ C.yg = n := by
    rw [hL.wt 0 0 χ hχ _ C.t _ _ (hL.test _ _) (hL.test _ _) C.bor, wchar_zero]
    unfold evC at hn
    rw [hn]
    simp
  have h2 : evR Xo c χ C.y = n := by
    rw [evR_of_frMap hL hχ C.R.val C.gen] at h1
    exact Subtype.ext (h1.trans (map_natCast C.R.val n).symm)
  have h3 : evR Xo c χ z = n := by rw [evR_of_frMap hL hχ ψ hz, h2, map_natCast]
  rw [hL.wt 0 0 χ hχ _ t _ _ (hL.test _ _) (hL.test _ _) hb, wchar_zero, h3]
  simp

theorem exists_comp_of_charts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → ∀ (h : GenFrEx Xo c) (k : U.Comp), ∃ Z : Comp Xo c, ∀ (x : (U.X k).dom) (C : FChart h) (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap ψ C.y z → FrBor t z (U.un k x) → C.Z = Z := by
  intro E _ _ _ H Dw l Xo c σ r U hU h k
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨x₀, hx₀⟩ := (GlobalTheory.frames_isConnected E r (U.X k)).nonempty
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨C₀, ψ₀, z₀, t₀, hz₀, hb₀⟩ := hA h (CAt σ) (U.un k ⟨x₀, hx₀⟩)
  refine ⟨C₀.Z, fun x C ψ z t hz hb => ?_⟩
  by_contra hne
  obtain ⟨χ, hχ, hi, h1, h0⟩ := exists_idem_section E H Dw l Xo c hL h (hA h) C₀.Z
  have hD : Dom (E := E) 0 0 := ⟨fun τ _ _ _ => le_rfl, Even.zero⟩
  have hs := hU.2.2.2.2.1 0 0 hD χ hχ k
  rw [IdemCusp.laU_zero] at hs
  have hid : IdemCusp.IsIdemFn (U.X k) (Formalism.L2.PjFree.rdU U χ k) := by
    refine IdemCusp.isIdemFn_of_isSec _ hs ?_
    have := congrFun (IdemCusp.rdU_mul U χ χ) k
    rw [hi] at this
    exact this.symm
  have hT : Set.MapsTo (Formalism.L2.PjFree.rdU U χ k) (U.X k).dom ({0, 1} : Set ℂ) := by
    intro s hs
    rcases hid.1 _ hs with h | h <;> simp [h]
  have hc := (GlobalTheory.frames_isConnected E r (U.X k)).isPreconnected.constant_of_mapsTo
    (Set.toFinite ({0, 1} : Set ℂ)).isDiscrete hid.2.1.continuousOn hT x.2 hx₀
  have e0 := evR_eq_natCast hL hχ C ψ hz hb 0 ((h0 _ hne).trans Nat.cast_zero.symm)
  have e1 := evR_eq_natCast hL hχ C₀ ψ₀ hz₀ hb₀ 1 (h1.trans Nat.cast_one.symm)
  rw [rdU_apply, rdU_apply U χ k ⟨x₀, hx₀⟩, e0, e1] at hc
  have hc' : ((0 : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := hc
  simp at hc'

end GlobalTheory.OneComp

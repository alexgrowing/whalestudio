import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PLocPrjGOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocInert

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

def glEquiv {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    (f : R ≃+* S) (hf : Continuous f) (hf' : Continuous f.symm) (n : ℕ) : GL (Fin n) R ≃ₜ* GL (Fin n) S where
  toFun := GeneralLinearGroup.map f.toRingHom
  invFun := GeneralLinearGroup.map f.symm.toRingHom
  left_inv g := by
    ext i j
    simp
  right_inv g := by
    ext i j
    simp
  map_mul' := map_mul _
  continuous_toFun := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_map hf, Units.continuous_coe_inv.matrix_map hf⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_map hf', Units.continuous_coe_inv.matrix_map hf'⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev aw (w : Pl E) : Above (w.under (𝓞 (maximalRealSubfield E))) := ⟨w, rfl⟩

theorem eq_aw {w : Pl E} (hw : ¬ IsSplitAt w) (u : Above (w.under (𝓞 (maximalRealSubfield E)))) : u = aw w := by
  by_contra h
  exact hw ⟨u.1, fun e => h (Subtype.ext e), u.2⟩

def uniq {w : Pl E} (hw : ¬ IsSplitAt w) : Unique (Above (w.under (𝓞 (maximalRealSubfield E)))) :=
  ⟨⟨aw w⟩, eq_aw hw⟩

def evR {w : Pl E} (hw : ¬ IsSplitAt w) : Av (w.under (𝓞 (maximalRealSubfield E))) ≃+* w.adicCompletion E :=
  letI := uniq hw
  RingEquiv.piUnique fun u : Above (w.under (𝓞 (maximalRealSubfield E))) => u.1.adicCompletion E

theorem evR_apply {w : Pl E} (hw : ¬ IsSplitAt w) (x : Av (w.under (𝓞 (maximalRealSubfield E)))) :
    evR hw x = x (aw w) := rfl

theorem continuous_evR {w : Pl E} (hw : ¬ IsSplitAt w) : Continuous (evR hw) :=
  continuous_apply (aw w)

theorem continuous_evR_symm {w : Pl E} (hw : ¬ IsSplitAt w) : Continuous (evR hw).symm := by
  letI := uniq hw
  exact (Homeomorph.piUnique fun u : Above (w.under (𝓞 (maximalRealSubfield E))) => u.1.adicCompletion E).symm.continuous

def evY {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) :
    Yv a b (w.under (𝓞 (maximalRealSubfield E))) ≃ₜ* GLw a w × GLw b w where
  toMulEquiv := MulEquiv.prodCongr (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) a).toMulEquiv
    (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) b).toMulEquiv
  continuous_toFun := (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) a).continuous.prodMap
    (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) b).continuous
  continuous_invFun := (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) a).symm.continuous.prodMap
    (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) b).symm.continuous

theorem evY_apply {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    evY hw a b y = evw (aw w) y := rfl

theorem cjv_apply (hC : CjEx) (hU : Unr E) {w : Pl E} (hw : ¬ IsSplitAt w)
    (x : Av (w.under (𝓞 (maximalRealSubfield E)))) : evR hw (cjv _ x) = cj w (evR hw x) := by
  obtain ⟨-, -, -, h4, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  have hc' := (h4 hw).2.2.1
  have h := hC E (w.under (𝓞 (maximalRealSubfield E)))
  set X : Af E := sLoc E w (evR hw x) with hX
  have hp : pLoc E w X = evR hw x := by
    change (Pi.single w (evR hw x) : ∀ u : Pl E, u.adicCompletion E) w = _
    simp
  have hx : projv _ X = x := by
    funext u
    obtain rfl := eq_aw hw u
    exact hp
  have hs : cjv (w.under (𝓞 (maximalRealSubfield E))) = h.choose := by
    rw [cjv, dif_pos h]
  rw [← hx, hs, ← h.choose_spec.2 X]
  rw [evR_apply, evR_apply]
  exact hc' X

theorem evY_thv (hC : CjEx) (hU : Unr E) {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ)
    (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    evY hw a b (thv a b _ y) = ((thL a w).prodMap (thL b w)) (evY hw a b y) := by
  have h : ∀ n (g : GL (Fin n) (Av (w.under (𝓞 (maximalRealSubfield E))))),
      GeneralLinearGroup.map (evR hw).toRingHom (thetaGL n (cjv _) g) =
        thL n w (GeneralLinearGroup.map (evR hw).toRingHom g) := fun n g => by
    rw [thL, if_neg hw]
    exact GlobalTheory.ThetaPull.map_thetaGL _ _ _ (cjv_apply hC hU hw) g
  exact Prod.ext (h a y.1) (h b y.2)

theorem mem_Kv_iff {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    y ∈ Kv a b _ ↔ evY hw a b y ∈ K2 a b w := by
  rw [Kv, Subgroup.mem_iInf]
  constructor
  · intro h
    exact h (aw w)
  · intro h u
    obtain rfl := eq_aw hw u
    exact h

theorem evY_pv {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) :
    evY hw a b (pv a b _ (ratF E a δ₁, ratF E b δ₂)) = (locEl a w δ₁, locEl b w δ₂) := by
  have h : ∀ n (δ : GL (Fin n) E), GeneralLinearGroup.map (evR hw).toRingHom
      (GeneralLinearGroup.map (projv (w.under (𝓞 (maximalRealSubfield E)))) (ratF E n δ)) = locEl n w δ := fun n δ => by
    rw [locEl, if_neg hw]
    ext i j
    rfl
  exact Prod.ext (h a δ₁) (h b δ₂)

theorem fv_eq {w : Pl E} (hw : ¬ IsSplitAt w) {a b : ℕ} {S : Set (Pl E)} (hS : w ∈ S)
    (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    seen φ₁ φ₂ w (evY hw a b y) = fv S φ₁ φ₂ _ y := by
  letI := uniq hw
  rw [fv, finprod_unique]
  change _ = ∏ᶠ (_ : w ∈ S), φ₁ w (evw (aw w) y) * if IsSplitAt w then _ else 1
  rw [finprod_eq_if, if_pos hS, if_neg hw, mul_one, seen, if_neg hw, evY_apply]

theorem locCompareInert : LocCompareInert := by
  intro hC E _ _ _ hU a b S _ φ₁ φ₂ _ _ δ₁ δ₂ _ _ w hS hw
  rw [← evY_pv hw a b δ₁ δ₂]
  exact GlobalTheory.EulerTw.Transport.twOrb_transport _ _ (evY hw a b) _ _ _ _ _ _ _
    (evY_thv hC hU hw a b) (mem_Kv_iff hw a b) (fv_eq hw hS φ₁ φ₂)

end GlobalTheory.CompanionTheory.LocInert

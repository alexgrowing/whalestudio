import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.MoveValues

open GlobalTheory.MoveCalc

noncomputable abbrev cpt : Sp ℂ := IsLocalRing.closedPoint ℂ

noncomputable def ev : (Sp ℂ).presheaf.stalk cpt →+* ℂ := (stalkClosedPointIso (CommRingCat.of ℂ)).hom.hom

theorem mem_iff {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) : f cpt ∈ U ↔ ⊤ ≤ f ⁻¹ᵁ U :=
  ⟨fun h p _ => by
    rw [Subsingleton.elim (α := PrimeSpectrum ℂ) p cpt]
    exact h, fun h => h trivial⟩

theorem ev_gs {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) (h : f cpt ∈ U) (a : Γ(X, U)) :
    ev (gs f cpt U a) = valAt' f U a := by
  have h' := (mem_iff f U).1 h
  rw [gs_eq f cpt U h, valAt', dif_pos h', valAt, ← germ_stalkClosedPointIso_hom (CommRingCat.of ℂ)]
  exact congrArg ev (TopCat.Presheaf.germ_res_apply (Sp ℂ).presheaf (homOfLE h') cpt trivial _).symm

theorem ev_gm {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) (h : f cpt ∈ U) (a : Γ(X, U)ˣ) :
    ev (gm f cpt U a).val = valAt' f U a.val :=
  (congrArg ev (gs_unit f cpt U h a).symm).trans (ev_gs f U h _)

section General

variable {X Y Y' : Scheme.{0}} {L : LB X} {F : X ⟶ X}

theorem mem_div {p : Sp ℂ ⟶ X} {i j : L.ι} :
    ⊤ ≤ p ⁻¹ᵁ (LB.div (L.pull F) L).U ((fun _ => i), j) ↔ F (p cpt) ∈ L.U i ∧ p cpt ∈ L.U j :=
  (mem_iff p _).symm.trans (and_congr_left' (mem_pull (F := F) (J := fun _ => i)))

theorem ev_gw (w : LB.Iso L (L.pull F)) (p : Sp ℂ ⟶ X) {i j : L.ι} (hi : F (p cpt) ∈ L.U i) (hj : p cpt ∈ L.U j) :
    ev (gw w p cpt i j).val =
      valAt' p ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val :=
  ev_gm p _ (show p cpt ∈ (L.pull F).U (fun _ => i) ⊓ L.U j from ⟨mem_pull.2 hi, hj⟩) _

theorem val_ne (w : LB.Iso L (L.pull F)) (p : Sp ℂ ⟶ X) {i j : L.ι} (hi : F (p cpt) ∈ L.U i) (hj : p cpt ∈ L.U j) :
    valAt' p ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val ≠ 0 := by
  rw [← ev_gw w p hi hj]
  exact ((gw w p cpt i j).isUnit.map ev).ne_zero

theorem val_pgen {w : LB.Iso L (L.pull F)} (h : PGen w) (p : Sp ℂ ⟶ X) {i j i' j' : L.ι}
    (hi : F (p cpt) ∈ L.U i) (hj : p cpt ∈ L.U j) (hi' : F (p cpt) ∈ L.U i') (hj' : p cpt ∈ L.U j') :
    valAt' p ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' p (L.U j ⊓ L.U j') (L.g j j').val =
      valAt' (p ≫ F) (L.U i ⊓ L.U i') (L.g i i').val *
        valAt' p ((LB.div (L.pull F) L).U ((fun _ => i'), j')) (w.s ((fun _ => i'), j')).val := by
  have e : gw w p cpt i j * gm p cpt _ (L.g j j') = gm (p ≫ F) cpt _ (L.g i i') * gw w p cpt i' j' := by
    rw [h _ p cpt i i' j j' hi hi' hj hj', mul_right_comm, inv_mul_cancel_right]
  rw [← ev_gw w p hi hj, ← ev_gw w p hi' hj', ← ev_gm p (L.U j ⊓ L.U j') ⟨hj, hj'⟩,
    ← ev_gm (p ≫ F) (L.U i ⊓ L.U i') ⟨hi, hi'⟩, ← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, e]

theorem val_pmaps {w : LB.Iso L (L.pull F)} {e : Y ⟶ X} {t : LB.Gen (L.pull e)} {ρ : Y ⟶ Y} (he : e ≫ F = ρ ≫ e)
    (h : PMaps w (K := PUnit) (fun _ => e) (fun _ => e) (fun _ => 1) t t ρ) (x : Sp ℂ ⟶ Y) {i j : L.ι}
    (hi : F ((x ≫ e) cpt) ∈ L.U i) (hj : (x ≫ e) cpt ∈ L.U j) :
    valAt' (x ≫ ρ) ((L.pull e).U (fun _ => i)) (t.s (fun _ => i)).val =
      valAt' (x ≫ e) ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' x ((L.pull e).U (fun _ => j)) (t.s (fun _ => j)).val := by
  have A := h _ x cpt (fun _ => i) (fun _ => j) (fun _ => hi) (fun _ => hj)
  rw [Fintype.prod_unique, zpow_one] at A
  have m : (x ≫ ρ) cpt ∈ (L.pull e).U (fun _ => i) := mem_pull.2 (by
    have h' : (e ≫ F) (x cpt) ∈ L.U i := hi
    rw [he] at h'
    exact h')
  rw [← ev_gw w (x ≫ e) hi hj, ← ev_gm (x ≫ ρ) _ m, ← ev_gm x ((L.pull e).U (fun _ => j)) (mem_pull.2 hj),
    ← map_mul, ← Units.val_mul]
  exact congrArg (fun u : ((Sp ℂ).presheaf.stalk cpt)ˣ => ev u.val) A

theorem val_carry {w : LB.Iso L (L.pull F)} {q : Y ⟶ X} {q' : Y' ⟶ X} {pm : Y ⟶ Y'} (hpm : pm ≫ q' = q ≫ F)
    {a : Fam L q} {a' : Fam L q'} (h : Carry w pm a a') (pt : Sp ℂ ⟶ Y) {i j : L.ι}
    (hi : F ((pt ≫ q) cpt) ∈ L.U i) (hj : (pt ≫ q) cpt ∈ L.U j) :
    valAt' (pt ≫ pm) _ (a' fun _ => i) =
      valAt' (pt ≫ q) ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' pt _ (a fun _ => j) := by
  have m : (pt ≫ pm) cpt ∈ LB.wchart L (fun _ : Fin 1 => q') (fun _ => i) := mem_chart.2 (by
    have h' : (q ≫ F) (pt cpt) ∈ L.U i := hi
    rw [← hpm] at h'
    exact h')
  rw [← ev_gw w (pt ≫ q) hi hj, ← ev_gs (pt ≫ pm) _ m,
    ← ev_gs pt (LB.wchart L (fun _ : Fin 1 => q) (fun _ => j)) (mem_chart.2 hj), ← map_mul]
  exact congrArg ev (h _ pt cpt i j hi hj)

end General

theorem frMove_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (y y' : FrPt Xo c (CAt σ)), FrMove ρ ν y y' → ∃ (O : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → Xo.univ.t.G.left.Opens) (ω : ∀ i j, Γ(Xo.univ.t.G.left, O i j)), (∀ i j (p : Sp ℂ ⟶ Xo.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j ↔ (⊤ ≤ (p ≫ ν.φ) ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ p ⁻¹ᵁ Xo.univ.t.PP.L.U j)) ∧ (∀ i j (p : Sp ℂ ⟶ Xo.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j → valAt' p (O i j) (ω i j) ≠ 0) ∧ (∀ i j i' j' (p : Sp ℂ ⟶ Xo.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j → ⊤ ≤ p ⁻¹ᵁ O i' j' → valAt' p (O i j) (ω i j) * valAt' p (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val = valAt' (p ≫ ν.φ) (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * valAt' p (O i' j') (ω i' j')) ∧ (∀ i j (x : Sp ℂ ⟶ Xo.X) (p : Sp ℂ ⟶ Xo.univ.t.G.left), p = x ≫ eSec Xo.univ.t.G → ⊤ ≤ p ⁻¹ᵁ O i j → valAt' (x ≫ ρ) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val = valAt' p (O i j) (ω i j) * valAt' x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧ ∀ i j (pt : Sp ℂ ⟶ Gx y.x) (pt' : Sp ℂ ⟶ Gx y'.x) (p : Sp ℂ ⟶ Xo.univ.t.G.left), pt ≫ Formalism.L2.PjFree.gxFst y.x = p → pt ≫ Formalism.L2.PjFree.gxSnd y.x = 𝟙 (Sp ℂ) → pt' ≫ Formalism.L2.PjFree.gxFst y'.x = p ≫ ν.φ → pt' ≫ Formalism.L2.PjFree.gxSnd y'.x = 𝟙 (Sp ℂ) → ⊤ ≤ p ⁻¹ᵁ O i j → valAt' pt' ((PPx y'.x).U (fun _ => i)) (y'.s.f (fun _ => i)) = valAt' p (O i j) (ω i j) * valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) := by
  intro E _ _ _ H Dw l Xo c σ ρ ν y y' h
  obtain ⟨hx, hu, pm, w, hf, hs, hw, hc⟩ := frMove_iff_carry.1 h
  obtain ⟨g, r, -⟩ := (cubIso_iff ν w).1 hw
  refine ⟨fun i j => (LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j),
    fun i j => (w.s ((fun _ => i), j)).val, fun i j p => ?_, fun i j p hp => ?_, fun i j i' j' p hp hp' => ?_,
    fun i j x p e hp => ?_, fun i j pt pt' p e₁ e₂ e₃ e₄ hp => ?_⟩
  · exact mem_div.trans (and_congr (mem_iff (p ≫ ν.cm.F) _) (mem_iff p _))
  · exact val_ne w p (mem_div.1 hp).1 (mem_div.1 hp).2
  · exact val_pgen g p (mem_div.1 hp).1 (mem_div.1 hp).2 (mem_div.1 hp').1 (mem_div.1 hp').2
  · subst e
    have A := val_pmaps ν.cm.e_comm r x (mem_div.1 hp).1 (mem_div.1 hp).2
    rw [ν.base] at A
    exact A
  · subst e₁
    obtain rfl : pt' = pt ≫ pm := by
      apply Limits.pullback.hom_ext
      · exact e₄.trans (e₂.symm.trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hf)).symm)
      · exact e₃.trans ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hs)).symm)
    exact val_carry hs hc pt (mem_div.1 hp).1 (mem_div.1 hp).2

end GlobalTheory.MoveValues

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CabsGenEqOneOfNormPin
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover

noncomputable section

namespace GlobalTheory.CoverFrameMod

section Exp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UnifPoint GlobalTheory.LevStab
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

theorem exists_isometry_of_hol' {S : Scheme.{0}} {t : SAB H S} {y : Sp ℂ ⟶ S} {D D' : Datum H}
    {ty ty' : Fin g → (E →+* ℂ)}
    {P : D.La →+ (Fin g → ℂ)} {P' : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty' P')
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (ha : ∀ z w, e (z + w) = e z * e w) (hs : Function.Surjective e)
    (hhol : IsHolTo Set.univ (fun z => (e z).left)) (he' : IsExp e')
    (hr : ReadsPeriods t unitOn D ty P e) (hr' : ReadsPeriods t unitOn D' ty' P' e') :
    ∃ (gam : D.La ≃ₗ[𝓞 E] D'.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) ∧
      (∀ a, P' (gam a) = h (P a)) ∧ ∀ z, e' (h z) = e z := by
  obtain ⟨h, hh⟩ := exists_linearEquiv_of_period hP' he' hr'.1 ha hs hhol
    ((countable_periods hP).mono fun z hz => (hr.1 z).1 hz)
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty' k (a : E) * h z k := fun a z => by
    have := hP'.2.2.1
    have k := realLinear_eq_of_sub_mem_discrete (Γ := P'.range) DiscreteTopology.isDiscrete
      (L := (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty k (a : E)))
      (L' := LinearMap.mulLeft ℝ (fun k => ty' k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ)) fun x =>
        (hr'.1 _).1 ((eq_iff_sub_of_add he'.1 _ _).1
          (((hh _).trans (hr.2.1 a x)).trans (by rw [← hh]; exact (hr'.2.1 a (h x)).symm)))
    exact DFunLike.congr_fun k z
  have hmem : ∀ a, ∃ b, P' b = h (P a) := fun a => (hr'.1 _).1 ((hh _).trans ((hr.1 _).2 ⟨a, rfl⟩))
  choose r₀ hr₀ using hmem
  let r₁ : D.La →ₗ[𝓞 E] D'.La :=
    { toFun := r₀
      map_add' := fun a b => hP'.2.1 (by rw [map_add, hr₀, hr₀, hr₀, map_add, map_add])
      map_smul' := fun c a => hP'.2.1 (by
        rw [hr₀, show P (c • a) = fun k => ty k (c : E) * P a k from funext (hP.1 c a), hcomm, ← hr₀]
        exact (funext (hP'.1 c (r₀ a))).symm) }
  have hb : Function.Bijective r₁ := by
    refine ⟨fun a b hab => hP.2.1 (h.injective (((hr₀ a).symm.trans (congrArg P' hab)).trans (hr₀ b))), fun b => ?_⟩
    obtain ⟨a, ha⟩ := (hr.1 (h.symm (P' b))).1 (by rw [← hh, h.apply_symm_apply]; exact (hr'.1 _).2 ⟨b, rfl⟩)
    exact ⟨a, hP'.2.1 ((hr₀ a).trans (by rw [ha, h.apply_symm_apply]))⟩
  refine ⟨LinearEquiv.ofBijective r₁ hb, h, fun a b => int_eq_of_exp_eq fun k hk => ?_, hr₀, hh⟩
  have w := hr.2.2 k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  have w' := hr'.2.2 k (r₀ a) (r₀ b) (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  rw [hr₀, hr₀, ← map_smul h, ← map_smul h, hh, hh] at w'
  exact congrArg Units.val (weilIs_unique_fieldPoint _ _ _ t.PP.isLB ℂ y k _ _ _ _ w' w)

variable {D : Datum H} {l l₂ : Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂} {σ : KA l →+* ℂ} {σ₂ : KA l₂ →+* ℂ}
  {ty ty₂ : Fin g → (E →+* ℂ)}

theorem exists_isometry_of_cover (F₂ : FamilyUnif Xo₂ σ₂ ty₂) (F : FamilyUnif Xo σ ty) {ρ : Xo₂.X ⟶ Xo.X}
    (ν : SABMap Xo₂.univ.t Xo.univ.t ρ) {i : Fin F₂.n} {j : Fin F.n} {P : (F₂.Di i).La →+ (Fin g → ℂ)}
    {P' : (F.Di j).La →+ (Fin g → ℂ)} (hP : IsPeriod (F₂.Di i) ty₂ P) (hP' : IsPeriod (F.Di j) ty P')
    (hu : F₂.u i P ≫ ρ = F.u j P') :
    ∃ (gam : (F₂.Di i).La ≃ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di j).EF (gam a) (gam b) = (F₂.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
      ∀ z, (F.ex j P' (h z)).left = (F₂.ex i P z).left ≫ ν.φ := by
  obtain ⟨β, hβ⟩ := GlobalTheory.CMSpreadCompare.exists_pointEquiv ν.cart (Over.mk (F₂.u i P)) (s := F.u j P') hu.symm
  have hr : ReadsPeriods Xo.univ.t unitOn (F₂.Di i) ty₂ P (fun z => β (F₂.ex i P z)) := by
    refine ⟨fun z => by rw [β.map_eq_one_iff, F₂.ex_ker i P hP], fun a z => ?_, fun k a b c hk hc => ?_⟩
    · apply Over.OverMorphism.ext
      rw [hβ, F₂.ex_lin i P hP, Over.comp_left, Over.comp_left, hβ, Category.assoc, Category.assoc]
      exact congrArg _ (ν.act a)
    · obtain ⟨w, hw, -⟩ := ν.lin
      have h₁ := (weilIs_grpPullback_of_comm _ _ Xo.univ.t.G Xo₂.univ.t.G ρ ν.φ _ _ Xo.univ.t.PP.isLB
        Xo₂.univ.t.PP.isLB ν.cart ⟨w, hw⟩ _ k _ _ (pushPt ν.cart.1.w _) (pushPt ν.cart.1.w _) _ rfl rfl).1
        (F₂.ex_weil i P hP k a b c hk hc)
      exact weilIs_congr hu (hβ _).symm (hβ _).symm h₁
  obtain ⟨gam, h, hEF, hh, hx⟩ := exists_isometry_of_hol' hP hP' (e := fun z => β (F₂.ex i P z)) (e' := F.ex j P')
    (fun z w => by rw [F₂.ex_add i P hP, map_mul]) (β.surjective.comp (F₂.ex_onto i P hP))
    (by
      simp only [hβ]
      exact GlobalTheory.CMSpreadCompare.isHolTo_postcomp (GlobalTheory.ClassUniq.isHolTo_ex F₂ i P hP) _)
    ⟨F.ex_add j P' hP', F.ex_onto j P' hP', GlobalTheory.ClassUniq.isHolTo_ex F j P' hP', (F.ex_diff j P' hP').1,
      (F.ex_diff j P' hP').2⟩ hr ⟨F.ex_ker j P' hP', F.ex_lin j P' hP', F.ex_weil j P' hP'⟩
  exact ⟨gam, h, hEF, hh, fun z => by rw [hx, hβ]⟩

end Exp

section Values

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.MoveValues (cpt ev mem_iff ev_gs ev_gm)

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem mem_div {p : Sp ℂ ⟶ X'} {i : L.ι} {j : L'.ι} :
    ⊤ ≤ p ⁻¹ᵁ (LB.div (L.pull F) L').U ((fun _ => i), j) ↔ F (p cpt) ∈ L.U i ∧ p cpt ∈ L'.U j :=
  (mem_iff p _).symm.trans (and_congr_left' (mem_pull (F := F) (J := fun _ => i)))

theorem ev_gw (w : LB.Iso L' (L.pull F)) (p : Sp ℂ ⟶ X') {i : L.ι} {j : L'.ι} (hi : F (p cpt) ∈ L.U i)
    (hj : p cpt ∈ L'.U j) :
    ev (gw w p cpt i j).val =
      valAt' p ((LB.div (L.pull F) L').U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val :=
  ev_gm p _ (show p cpt ∈ (L.pull F).U (fun _ => i) ⊓ L'.U j from ⟨mem_pull.2 hi, hj⟩) _

theorem val_ne (w : LB.Iso L' (L.pull F)) (p : Sp ℂ ⟶ X') {i : L.ι} {j : L'.ι} (hi : F (p cpt) ∈ L.U i)
    (hj : p cpt ∈ L'.U j) :
    valAt' p ((LB.div (L.pull F) L').U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val ≠ 0 := by
  rw [← ev_gw w p hi hj]
  exact ((gw w p cpt i j).isUnit.map ev).ne_zero

theorem val_pgen {w : LB.Iso L' (L.pull F)} (h : PGen w) (p : Sp ℂ ⟶ X') {i i' : L.ι} {j j' : L'.ι}
    (hi : F (p cpt) ∈ L.U i) (hj : p cpt ∈ L'.U j) (hi' : F (p cpt) ∈ L.U i') (hj' : p cpt ∈ L'.U j') :
    valAt' p ((LB.div (L.pull F) L').U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' p (L'.U j ⊓ L'.U j') (L'.g j j').val =
      valAt' (p ≫ F) (L.U i ⊓ L.U i') (L.g i i').val *
        valAt' p ((LB.div (L.pull F) L').U ((fun _ => i'), j')) (w.s ((fun _ => i'), j')).val := by
  have e : gw w p cpt i j * gm p cpt _ (L'.g j j') = gm (p ≫ F) cpt _ (L.g i i') * gw w p cpt i' j' := by
    rw [h _ p cpt i i' j j' hi hi' hj hj', mul_right_comm, inv_mul_cancel_right]
  rw [← ev_gw w p hi hj, ← ev_gw w p hi' hj', ← ev_gm p (L'.U j ⊓ L'.U j') ⟨hj, hj'⟩,
    ← ev_gm (p ≫ F) (L.U i ⊓ L.U i') ⟨hi, hi'⟩, ← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, e]

theorem val_pmaps {w : LB.Iso L' (L.pull F)} {e : Y ⟶ X} {e' : Y' ⟶ X'} {t : LB.Gen (L.pull e)}
    {t' : LB.Gen (L'.pull e')} {ρ : Y' ⟶ Y} (he : e' ≫ F = ρ ≫ e)
    (h : PMaps w (K := PUnit) (fun _ => e') (fun _ => e) (fun _ => 1) t' t ρ) (x : Sp ℂ ⟶ Y') {i : L.ι} {j : L'.ι}
    (hi : F ((x ≫ e') cpt) ∈ L.U i) (hj : (x ≫ e') cpt ∈ L'.U j) :
    valAt' (x ≫ ρ) ((L.pull e).U (fun _ => i)) (t.s (fun _ => i)).val =
      valAt' (x ≫ e') ((LB.div (L.pull F) L').U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' x ((L'.pull e').U (fun _ => j)) (t'.s (fun _ => j)).val := by
  have A := h _ x cpt (fun _ => i) (fun _ => j) (fun _ => hi) (fun _ => hj)
  rw [Fintype.prod_unique, zpow_one] at A
  have m : (x ≫ ρ) cpt ∈ (L.pull e).U (fun _ => i) := mem_pull.2 (by
    have h' : (e' ≫ F) (x cpt) ∈ L.U i := hi
    rw [he] at h'
    exact h')
  rw [← ev_gw w (x ≫ e') hi hj, ← ev_gm (x ≫ ρ) _ m, ← ev_gm x ((L'.pull e').U (fun _ => j)) (mem_pull.2 hj),
    ← map_mul, ← Units.val_mul]
  exact congrArg (fun u : ((Sp ℂ).presheaf.stalk cpt)ˣ => ev u.val) A

theorem val_rel {w : LB.Iso L' (L.pull F)} {q' : Y' ⟶ X'} {q : Y ⟶ X} {pm : Y' ⟶ Y} (hpm : pm ≫ q = q' ≫ F)
    {s' : LB.Sec (FrameLift.LOne L' q')} {s : LB.Sec (FrameLift.LOne L q)} (h : FrameLift.Rel w pm s' s)
    (pt : Sp ℂ ⟶ Y') {i : L.ι} {j : L'.ι} (hi : F ((pt ≫ q') cpt) ∈ L.U i) (hj : (pt ≫ q') cpt ∈ L'.U j) :
    valAt' (pt ≫ pm) (FrameLift.ch L q i) (s.f fun _ => i) =
      valAt' (pt ≫ q') ((LB.div (L.pull F) L').U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' pt (FrameLift.ch L' q' j) (s'.f fun _ => j) := by
  have m : (pt ≫ pm) cpt ∈ FrameLift.ch L q i := FrameLift.mem_ch.2 (by
    have h' : (q' ≫ F) (pt cpt) ∈ L.U i := hi
    rw [← hpm] at h'
    exact h')
  rw [← ev_gw w (pt ≫ q') hi hj, ← ev_gs (pt ≫ pm) _ m, ← ev_gs pt (FrameLift.ch L' q' j) (FrameLift.mem_ch.2 hj),
    ← map_mul]
  exact congrArg ev (h _ pt cpt i j hi hj)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem frOver_values (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ] (y : FrPt d.Xo₂ d.c₂ ℂ)
    (y' : FrPt Xo c ℂ) (h : FrOver d y y') :
    ∃ (O : Xo.univ.t.PP.L.ι → d.Xo₂.univ.t.PP.L.ι → d.Xo₂.univ.t.G.left.Opens)
      (ω : ∀ i j, Γ(d.Xo₂.univ.t.G.left, O i j)),
      (∀ i j (p : Sp ℂ ⟶ d.Xo₂.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j ↔
        (⊤ ≤ (p ≫ d.m.φ) ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ p ⁻¹ᵁ d.Xo₂.univ.t.PP.L.U j)) ∧
      (∀ i j (p : Sp ℂ ⟶ d.Xo₂.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j → valAt' p (O i j) (ω i j) ≠ 0) ∧
      (∀ i j i' j' (p : Sp ℂ ⟶ d.Xo₂.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j → ⊤ ≤ p ⁻¹ᵁ O i' j' →
        valAt' p (O i j) (ω i j) *
            valAt' p (d.Xo₂.univ.t.PP.L.U j ⊓ d.Xo₂.univ.t.PP.L.U j') (d.Xo₂.univ.t.PP.L.g j j').val =
          valAt' (p ≫ d.m.φ) (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val *
            valAt' p (O i' j') (ω i' j')) ∧
      (∀ i j (x : Sp ℂ ⟶ d.Xo₂.X) (p : Sp ℂ ⟶ d.Xo₂.univ.t.G.left), p = x ≫ eSec d.Xo₂.univ.t.G →
        ⊤ ≤ p ⁻¹ᵁ O i j →
        valAt' (x ≫ d.r) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i))
            (Xo.univ.t.PP.rig.s (fun _ => i)).val =
          valAt' p (O i j) (ω i j) *
            valAt' x ((d.Xo₂.univ.t.PP.L.pull (eSec d.Xo₂.univ.t.G)).U (fun _ => j))
              (d.Xo₂.univ.t.PP.rig.s (fun _ => j)).val) ∧
      ∀ i j (pt : Sp ℂ ⟶ Gx y.x) (pt' : Sp ℂ ⟶ Gx y'.x) (p : Sp ℂ ⟶ d.Xo₂.univ.t.G.left),
        pt ≫ Formalism.L2.PjFree.gxFst y.x = p → pt ≫ Formalism.L2.PjFree.gxSnd y.x = 𝟙 (Sp ℂ) →
        pt' ≫ Formalism.L2.PjFree.gxFst y'.x = p ≫ d.m.φ → pt' ≫ Formalism.L2.PjFree.gxSnd y'.x = 𝟙 (Sp ℂ) →
        ⊤ ≤ p ⁻¹ᵁ O i j →
        valAt' pt' ((PPx y'.x).U (fun _ => i)) (y'.s.f (fun _ => i)) =
          valAt' p (O i j) (ω i j) * valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) := by
  obtain ⟨-, -, w, pm, ⟨hg, hw⟩, hs, hf, hc⟩ := (FrameLift.frOver_iff d y y').1 h
  have g := (isGen_iff w).1 hg
  have r := (maps_iff w _ (fun _ => eSec Xo.univ.t.G) _ d.Xo₂.univ.t.PP.rig Xo.univ.t.PP.rig d.m.cm.e _
    (rigPull_le d.m.cm.F d.m.cm.e d.m.cm.e_comm Xo.univ.t.PP.L) (fun _ => rfl)).1 hw
  refine ⟨fun i j => (LB.div (Xo.univ.t.PP.L.pull d.m.φ) d.Xo₂.univ.t.PP.L).U ((fun _ => i), j),
    fun i j => (w.s ((fun _ => i), j)).val, fun i j p => ?_, fun i j p hp => ?_, fun i j i' j' p hp hp' => ?_,
    fun i j x p e hp => ?_, fun i j pt pt' p e₁ e₂ e₃ e₄ hp => ?_⟩
  · exact mem_div.trans (and_congr (mem_iff (p ≫ d.m.φ) _) (mem_iff p _))
  · exact val_ne w p (mem_div.1 hp).1 (mem_div.1 hp).2
  · exact val_pgen g p (mem_div.1 hp).1 (mem_div.1 hp).2 (mem_div.1 hp').1 (mem_div.1 hp').2
  · subst e
    have A := val_pmaps d.m.cm.e_comm r x (mem_div.1 hp).1 (mem_div.1 hp).2
    rw [d.m.base] at A
    exact A
  · subst e₁
    obtain rfl : pt' = pt ≫ pm := by
      apply Limits.pullback.hom_ext
      · exact e₄.trans (e₂.symm.trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hf)).symm)
      · exact e₃.trans ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hs)).symm)
    exact val_rel hs hc pt (mem_div.1 hp).1 (mem_div.1 hp).2

end Values

section Norm

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open scoped Matrix
open GlobalTheory.UnitFrameGen MeasureTheory

set_option maxHeartbeats 1600000 in

theorem norm_gen_eq_one_of_frOver {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) {σ : c.F →+* ℂ} {σ₂ : d.c₂.F →+* ℂ} {σ' : KA l →+* ℂ}
    {σ₂' : KA d.l₂ →+* ℂ} {g : ℕ} {ty ty₂ : Fin g → (E →+* ℂ)} (F₂ : FamilyUnif d.Xo₂ σ₂' ty₂)
    (F : FamilyUnif Xo σ' ty) (i : Fin F₂.n) (i' : Fin F.n) (P : (F₂.Di i).La →+ (Fin g → ℂ))
    (P' : (F.Di i').La →+ (Fin g → ℂ)) (y₀ : FrPt d.Xo₂ d.c₂ (CAt σ₂)) (z₀ y' : FrPt Xo c (CAt σ))
    (t : Ix Dw → (CAt σ)ˣ) (hp : IsPeriod (F₂.Di i) ty₂ P) (hp' : IsPeriod (F.Di i') ty P')
    (hu : y₀.x = F₂.u i P) (hu' : z₀.x = F.u i' P') (hx : NormPin F₂ i P y₀) (hx' : NormPin F i' P' z₀)
    (hmv : @FrOver E _ _ _ H Dw l Xo c n d (CAt σ) _ _ (RingHom.toAlgebra (R := d.c₂.F) (S := CAt σ) σ₂) y₀ y')
    (hb : FrBor t z₀ y') : ‖toC (t none : CAt σ)‖ = 1 := by
  obtain ⟨Hm, χ, fr, θ, Fd, hH, -, him, hd, hn, hc, h0, ha, hv, hF, hI⟩ := hx
  obtain ⟨Hm', χ', fr', θ', Fd', hH', -, him', hd', hn', hc', h0', ha', hv', hF', hI'⟩ := hx'
  obtain ⟨O, ω, o1, o2, o3, o4, o5⟩ := @frOver_values E _ _ _ H Dw l Xo c n d σ.toAlgebra σ₂.toAlgebra y₀ y' hmv
  have hxρ : (z₀.x : Sp ℂ ⟶ Xo.X) = (y₀.x : Sp ℂ ⟶ d.Xo₂.X) ≫ d.r := hb.1.symm.trans hmv.1.symm
  obtain ⟨hxx, -, hbc⟩ := hb
  clear hmv
  obtain ⟨gam, hl, hg1, hg4, hex0⟩ := exists_isometry_of_cover F₂ F d.m hp hp'
    ((congrArg (· ≫ d.r) hu).symm.trans (hxρ.symm.trans hu'))
  obtain ⟨h, hdet, hh⟩ : ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h.det ∧ ∀ z, h *ᵥ z = hl z :=
    ⟨LinearMap.toMatrix' hl.toLinearMap, by
      rw [LinearMap.det_toMatrix']; exact LinearEquiv.isUnit_det' hl,
      fun a => by rw [LinearMap.toMatrix'_mulVec]; rfl⟩
  have hg : ∀ a, P' (gam a) = h *ᵥ P a := fun a => by rw [hh, hg4]
  have hex : ∀ z, (F.ex i' P' (h *ᵥ z)).left = (F₂.ex i P z).left ≫ d.m.φ := fun z => by rw [hh, hex0]
  have hspan : Submodule.span ℝ (P.range : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hp.2.2.2.1
  have hHH : ∀ z w, hermForm Hm' (h *ᵥ z) (h *ᵥ w) = hermForm Hm z w :=
    hermForm_eq_of_im _ hspan Hm Hm' h (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← hg, ← hg, him, him', hg1])
  have hexp : ∀ a ∈ P.range, ∀ z, F₂.ex i P (z + a) = F₂.ex i P z := fun a ha z => by
    rw [F₂.ex_add i P hp, (F₂.ex_ker i P hp a).2 ha]
    exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hcov : ∀ z, ∃ j, ⊤ ≤ (F₂.ex i P z).left ⁻¹ᵁ d.Xo₂.univ.t.PP.L.U j := fun z =>
    GlobalTheory.ThetaPtChg.exists_chart_point d.Xo₂.univ.t.PP.isLB _
  have hcov2 : ∀ z, ∃ q : Xo.univ.t.PP.L.ι × d.Xo₂.univ.t.PP.L.ι, ⊤ ≤ (F₂.ex i P z).left ⁻¹ᵁ O q.1 q.2 := fun z => by
    obtain ⟨j, hj⟩ := hcov z
    obtain ⟨j', hj'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB ((F₂.ex i P z).left ≫ d.m.φ)
    exact ⟨(j', j), (o1 _ _ _).2 ⟨hj', hj⟩⟩
  have tr : ∀ j j' z, ⊤ ≤ (F₂.ex i P z).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex i' P' (h *ᵥ z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j j' z hz => by
    rw [hex]; exact ((o1 _ _ _).1 hz).1
  have tr2 : ∀ j j' z, ⊤ ≤ (F₂.ex i P z).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F₂.ex i P z).left ⁻¹ᵁ d.Xo₂.univ.t.PP.L.U j' := fun j j' z hz => ((o1 _ _ _).1 hz).2
  have hm : ∀ j, ∀ a ∈ P.range, ∀ z, ⊤ ≤ (F₂.ex i P z).left ⁻¹ᵁ d.Xo₂.univ.t.PP.L.U j → ‖fr j z‖ =
      Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re) * ‖fr j (z + a)‖ := by
    rintro j _ ⟨a, rfl⟩ z hz
    exact norm_factor Hm _ _ _ _ _ (ha a j z).1 ((ha a j z).2 hz)
  have dl : Differentiable ℂ (fun z' : Fin g → ℂ => h *ᵥ z') :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h)).differentiable
  have hw0 : ∀ z, (F₂.ex i P z).left ≫ d.Xo₂.univ.t.G.hom = (y₀.x : Sp ℂ ⟶ d.Xo₂.X) := fun z =>
    (Over.w (F₂.ex i P z)).trans hu.symm
  have hw0' : ∀ z, (F.ex i' P' z).left ≫ Xo.univ.t.G.hom = (z₀.x : Sp ℂ ⟶ Xo.X) := fun z =>
    (Over.w (F.ex i' P' z)).trans hu'.symm
  have hz0 : (F₂.ex i P 0).left = (y₀.x : Sp ℂ ⟶ d.Xo₂.X) ≫ eSec d.Xo₂.univ.t.G := by
    rw [(F₂.ex_ker i P hp 0).2 (zero_mem _), hu]
    rfl
  have hfr : ∀ q : Xo.univ.t.PP.L.ι × d.Xo₂.univ.t.PP.L.ι, ∀ z, ⊤ ≤ (F₂.ex i P z).left ⁻¹ᵁ O q.1 q.2 →
      fr' q.1 (h *ᵥ z) = valAt' (F₂.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * fr q.2 z :=
    frames_eq P.range hspan
      (fun q : Xo.univ.t.PP.L.ι × d.Xo₂.univ.t.PP.L.ι => {z | ⊤ ≤ (F₂.ex i P z).left ⁻¹ᵁ O q.1 q.2})
      (fun j => GlobalTheory.FamilyUnif_isOpen_ex F₂ i P hp _) hcov2
      (fun j a ha z hz => by rw [Set.mem_setOf_eq, hexp a ha]; exact hz)
      (fun q z => valAt' (F₂.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * fr q.2 z) (fun q z => fr' q.1 (h *ᵥ z))
      (fun q q' z => valAt' ((F₂.ex i P z).left ≫ d.m.φ) (Xo.univ.t.PP.L.U q.1 ⊓ Xo.univ.t.PP.L.U q'.1)
        (Xo.univ.t.PP.L.g q.1 q'.1).val)
      (fun a z => Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re))
      (fun q => (((GlobalTheory.ClassUniq.isHolTo_ex F₂ i P hp) (O q.1 q.2) (ω q.1 q.2)).2.mono
        fun z hz => ⟨Set.mem_univ _, hz⟩).mul ((hd q.2).mono fun z hz => tr2 _ _ z hz))
      (fun q => (hd' q.1).comp dl.differentiableOn fun z hz => tr _ _ z hz)
      (fun q z hz => mul_ne_zero (o2 _ _ _ hz) (hn _ z (tr2 _ _ z hz)))
      (fun q q' z h1 h2 => by
        rw [hc q.2 q'.2 z ((top_le_preimage_inf _ _ _).2 ⟨tr2 _ _ z h1, tr2 _ _ z h2⟩), ← mul_assoc,
          o3 _ _ _ _ _ h1 h2, mul_assoc])
      (fun q q' z h1 h2 => by
        have e2 := hc' q.1 q'.1 (h *ᵥ z) ((top_le_preimage_inf _ _ _).2 ⟨tr _ _ _ h1, tr _ _ _ h2⟩)
        rw [hex] at e2
        exact e2)
      (fun q hz => by
        have t0 := tr _ _ 0 hz
        simp only [Matrix.mulVec_zero] at t0 ⊢
        rw [h0 _ (tr2 _ _ 0 hz), h0' _ t0]
        exact (congrArg (fun x : Sp ℂ ⟶ Xo.X => valAt' x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => q.1))
          (Xo.univ.t.PP.rig.s (fun _ => q.1)).val) hxρ).trans (o4 _ _ _ _ hz0 hz))
      (fun q a haa z hz => by
        rw [hexp a haa, norm_mul, norm_mul, hm _ a haa z (tr2 _ _ z hz)]
        ring)
      (by
        rintro q _ ⟨a, rfl⟩ z hz
        have := norm_factor Hm' _ _ _ _ _ (ha' (gam a) q.1 (h *ᵥ z)).1
          ((ha' (gam a) q.1 (h *ᵥ z)).2 (tr _ _ z hz))
        rw [hg, hHH, hHH, ← Matrix.mulVec_add] at this
        exact this)
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by simp [spMap]
  have hbc' : GlobalTheory.Frames.SecBC (RingHom.id ℂ) (toC (t none : CAt σ)) z₀.x y'.x z₀.s y'.s := by
    obtain ⟨pm, p1, p2, p3⟩ := hbc
    exact ⟨pm, p1, by rw [hid]; exact p2.trans (Category.comp_id _).symm, p3⟩
  have hθ : ∀ z, θ z = toC (t none : CAt σ) * θ' (h *ᵥ z) := fun z => by
    obtain ⟨q, hq⟩ := hcov2 z
    let p : Over.mk (y₀.x : Sp ℂ ⟶ d.Xo₂.X) ⟶ d.Xo₂.univ.t.G := Over.homMk (F₂.ex i P z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv q.2 z _ e1 e2 (tr2 _ _ z hq)
    have hval := GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hxx _ _ _ hbc'
      (Over.homMk (F.ex i' P' (h *ᵥ z)).left (hw0' _)) q.1 _ _
      (fun pt h1 h2 => hv' q.1 (h *ᵥ z) pt h1 h2 (tr _ _ z hq))
      (fun pt h1 h2 => o5 q.1 q.2 _ pt _ e1 e2 (h1.trans (hex z)) h2 hq)
    have hval2 : valAt' (F₂.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * (θ z * fr q.2 z) =
        toC (t none : CAt σ) * (θ' (h *ᵥ z) * fr' q.1 (h *ᵥ z)) :=
      (congrArg (valAt' (F₂.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * ·) v1).symm.trans hval
    rw [hfr q z hq] at hval2
    apply mul_right_cancel₀ (mul_ne_zero (o2 _ _ _ hq) (hn _ z (tr2 _ _ z hq)))
    linear_combination hval2
  have ht0 : toC (t none : CAt σ) ≠ 0 := Units.ne_zero (M₀ := ℂ) (t none)
  have hθp : ∀ a ∈ P.range, ∀ z, ‖θ (z + a)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm (z + a) (z + a)).re) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) := fun a ha z => by
    obtain ⟨j, hj⟩ := hcov z
    have hj' : ⊤ ≤ (F₂.ex i P (z + a)).left ⁻¹ᵁ d.Xo₂.univ.t.PP.L.U j := by rw [hexp a ha]; exact hj
    let p : Over.mk (y₀.x : Sp ℂ ⟶ d.Xo₂.X) ⟶ d.Xo₂.univ.t.G := Over.homMk (F₂.ex i P z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv j z _ e1 e2 hj
    have v2 := hv j (z + a) _ (by rw [hexp a ha]; exact e1) e2 hj'
    exact normSq_periodic hH _ _ _ _ z a (hn j _ hj') (v2.symm.trans v1) (hm j a ha z hj)
  haveI : Countable P.range := by
    haveI := hp.2.2.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hinj : Function.Injective (fun z : Fin g → ℂ => h *ᵥ z) :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hdet)
  have hn0 : ‖toC (t none : CAt σ)‖ ≠ 0 := norm_ne_zero_iff.2 ht0
  have key : ∀ z, ‖θ' (h *ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' (h *ᵥ z) (h *ᵥ z)).re) =
      (‖toC (t none : CAt σ)‖ ^ 2)⁻¹ * (‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) :=
    fun z => by rw [hθ, hHH, norm_mul, mul_pow]; field_simp
  have hmean := mean_comp_eq P.range P'.range h hdet (fun z => ⟨?_, ?_⟩) Fd Fd' hF hF'
    (fun z => ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re))
    (fun a ha z => by simp only [key, hθp a ha z])
  · simp only [key] at hmean
    rw [hI', integral_const_mul, mul_div_assoc, hI, mul_one, inv_eq_one] at hmean
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hmean
  · rintro ⟨a, ha⟩
    refine ⟨gam.symm a, hinj ?_⟩
    simp only
    rw [← hg, gam.apply_symm_apply, ha]
  · rintro ⟨a, rfl⟩
    exact ⟨gam a, hg a⟩

end Norm

end GlobalTheory.CoverFrameMod

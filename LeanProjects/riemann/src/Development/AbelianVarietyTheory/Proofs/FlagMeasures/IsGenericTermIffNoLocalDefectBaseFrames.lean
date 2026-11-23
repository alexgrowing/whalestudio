import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitriangularFrameChangeLocalScalings
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnsignedLocalTermRowLatticeIsTerm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDatumOfTwoCongruentFramesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermDefectEqOfLatticeEqStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAtBasePointOfFramesStatement

noncomputable section

namespace GlobalTheory.Unfold.GenLoc

section Loc

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

lemma mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ img g Λ ↔ ∃ y ∈ Λ, g y = x := Submodule.mem_map

lemma img_selfDual (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} (hΛ : H.IsSelfDual Λ) : H.IsSelfDual (img g Λ) := by
  obtain ⟨hfg, hsp, hmem⟩ := hΛ
  refine ⟨hfg.map _, ?_, ?_⟩
  · have hc : ((img g Λ : Submodule M.L.O V) : Set V) = (g : V → V) '' (Λ : Set V) := Submodule.map_coe _ _
    have hsi := Submodule.span_image (R := E) (s := (Λ : Set V)) (g : V →ₗ[E] V)
    simp only [LinearEquiv.coe_coe] at hsi
    rw [hc, hsi, hsp, Submodule.map_top]
    exact LinearMap.range_eq_top.2 g.surjective
  · intro x
    have key : ∀ z, z ∈ img g Λ ↔ g.symm z ∈ Λ := fun z => by
      rw [mem_img]
      constructor
      · rintro ⟨y, hy, rfl⟩; simpa using hy
      · intro h; exact ⟨_, h, by simp⟩
    rw [key, hmem]
    constructor
    · intro h y hy
      obtain ⟨y0, hy0, rfl⟩ := (mem_img g Λ y).1 hy
      have := h y0 hy0
      rwa [← hg (g.symm x) y0, LinearEquiv.apply_symm_apply] at this
    · intro h y hy
      have := h (g y) ((mem_img g Λ _).2 ⟨y, hy, rfl⟩)
      rwa [← hg (g.symm x) y, LinearEquiv.apply_symm_apply]

lemma img_frame (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} {r : ℕ} {f : Fin (r + 1) → V} {T : F} (hf : H.IsFrame Λ r f T) :
    H.IsFrame (img g Λ) r (fun b => g (f b)) T := by
  obtain ⟨⟨hin, hli, hsp⟩, hiso, hzz, hT, hT0⟩ := hf
  refine ⟨⟨fun a => (mem_img g Λ _).2 ⟨f a, hin a, rfl⟩, hli.map' (g : V →ₗ[E] V) g.ker, ?_⟩,
    fun a b hab => by rw [hg]; exact hiso a b hab, by rw [hg]; exact hzz, hT, hT0⟩
  intro x hx hxs
  obtain ⟨y, hy, rfl⟩ := (mem_img g Λ x).1 hx
  have hr : Set.range (fun b => g (f b)) = (g : V → V) '' Set.range f := (Set.range_comp _ _).symm ▸ rfl
  rw [hr] at hxs ⊢
  have hys : y ∈ Submodule.span E (Set.range f) := by
    have := Submodule.apply_mem_span_image_of_mem_span (g.symm : V →ₗ[E] V) hxs
    simpa [Set.image_image] using this
  have := Submodule.apply_mem_span_image_of_mem_span ((g : V →ₗ[E] V).restrictScalars M.L.O) (hsp y hy hys)
  simpa using this

lemma isTerm_move (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {r : ℕ} {t : Term V M r}
    (ht : H.IsTerm t) : H.IsTerm (move g t) := by
  have hg' : ∀ x y, H.h (g x) (g y) = H.h x y := hg
  have hZ : H.Zhat (move g t).f (move g t).f' = H.Zhat t.f t.f' := by
    ext a b; simp [HermSp.Zhat, move, hg']
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
  refine ⟨img_selfDual H hg h1, img_frame H hg h2, img_frame H hg h3, ?_, ?_, ?_⟩
  · simpa [HermSp.Dl, hZ] using h4
  · show H.Gdet (move g t).f (move g t).f' t.T t.T' ≠ 0
    simpa [HermSp.Gdet, HermSp.Dl, hZ] using h5
  · intro g0 hs
    obtain ⟨hu, hc, hadm⟩ := h6 g0 hs
    refine ⟨hu, hc, fun b => ?_⟩
    have hb := hadm b
    show g (t.f' b) - g (t.f b) ∈ H.smulLat _ (img g t.abelian₂)
    rw [← map_sub]
    have := Submodule.apply_mem_span_image_of_mem_span ((g : V →ₗ[E] V).restrictScalars M.L.O) hb
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨g y, (mem_img g t.abelian₂ _).2 ⟨y, hy, rfl⟩, by simp⟩

lemma mmfam_move (H : HermSp M V) (g : V ≃ₗ[E] V) {r : ℕ} (t : Term V M r) (i : Fin (r + 1) ⊕ Fin (r + 1)) :
    H.MMfam (move g t) i = g (H.MMfam t i) := by
  unfold HermSp.MMfam
  rcases M.split with _ | g0 <;> rcases i with a | a <;> simp [move, map_sub, map_smul]

lemma bbne_move (H : HermSp M V) (g : V ≃ₗ[E] V) {r : ℕ} (t : Term V M r) :
    BBne (H := H) (move g t) ↔ BBne (H := H) t := by
  have hr : Set.range (H.MMfam (move g t)) = (g : V → V) '' Set.range (H.MMfam t) := by
    rw [← Set.range_comp]; congr 1; funext i; exact mmfam_move H g t i
  have kE : ∀ x, g x ∈ Submodule.span E ((g : V → V) '' Set.range (H.MMfam t)) ↔
      x ∈ Submodule.span E (Set.range (H.MMfam t)) := fun x => by
    constructor
    · intro h
      simpa [Set.image_image] using Submodule.apply_mem_span_image_of_mem_span (g.symm : V →ₗ[E] V) h
    · intro h
      simpa using Submodule.apply_mem_span_image_of_mem_span (g : V →ₗ[E] V) h
  have kO : ∀ x, g x ∈ Submodule.span M.L.O ((g : V → V) '' Set.range (H.MMfam t)) ↔
      x ∈ Submodule.span M.L.O (Set.range (H.MMfam t)) := fun x => by
    constructor
    · intro h
      simpa [Set.image_image] using
        Submodule.apply_mem_span_image_of_mem_span ((g.symm : V →ₗ[E] V).restrictScalars M.L.O) h
    · intro h
      simpa using Submodule.apply_mem_span_image_of_mem_span ((g : V →ₗ[E] V).restrictScalars M.L.O) h
  unfold BBne
  rw [hr]
  constructor
  · rintro ⟨v, hv, h1, h2⟩
    obtain ⟨y, hy, rfl⟩ := (mem_img g t.abelian₂ v).1 hv
    exact ⟨y, hy, (kE y).1 h1, fun h => h2 ((kO y).2 h)⟩
  · rintro ⟨y, hy, h1, h2⟩
    exact ⟨g y, (mem_img g t.abelian₂ _).2 ⟨y, hy, rfl⟩, (kE y).2 h1, fun h => h2 ((kO y).1 h)⟩

lemma span_sign {R W ι : Type} [CommRing R] [AddCommGroup W] [Module R W] (s : ι → R) (hs : ∀ i, s i * s i = 1)
    (v w : ι → W) (h : ∀ i, w i = s i • v i) :
    Submodule.span R (Set.range w) = Submodule.span R (Set.range v) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [h i]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : v i = s i • w i := by rw [h i, smul_smul, hs i, one_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

lemma bbne_sign (H : HermSp M V) {r : ℕ} (t t' : Term V M r) (s s' : Fin (r + 1) → M.L.O)
    (hs : ∀ a, s a * s a = 1) (hs' : ∀ a, s' a * s' a = 1) (hL : t'.abelian₂ = t.abelian₂)
    (hf : ∀ a, t'.f a = (s a : E) • t.f a) (hf' : ∀ a, t'.f' a = (s' a : E) • t.f' a)
    (hss : ∀ g, M.split = some g → s' = s) :
    BBne (H := H) t' ↔ BBne (H := H) t := by
  have hσ2 : ∀ i, Sum.elim s s' i * Sum.elim s s' i = 1 := by
    rintro (a | a)
    · exact hs a
    · exact hs' a
  have hfam : ∀ i, H.MMfam t' i = ((Sum.elim s s' i : M.L.O) : E) • H.MMfam t i := by
    unfold HermSp.MMfam
    rcases hsp : M.split with _ | g0
    · rintro (a | a)
      · simp [hf]
      · simp [hf']
    · have e := hss g0 hsp
      rintro (a | a)
      · simp [hf]
      · simp only [Sum.elim_inr, hf', hf, e]
        rw [← smul_sub, smul_comm]
  have hE := span_sign (R := E) (fun i => ((Sum.elim s s' i : M.L.O) : E))
    (fun i => by have := congrArg Subtype.val (hσ2 i); simpa using this) (H.MMfam t) (H.MMfam t') hfam
  have hO := span_sign (R := M.L.O) (Sum.elim s s') hσ2 (H.MMfam t) (H.MMfam t') hfam
  unfold BBne
  rw [hE, hO, hL]

lemma uni_mul {K : Type} [CommRing K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : Uni A) (hB : Uni B) :
    Uni (A * B) := by
  obtain ⟨hA0, hA1⟩ := hA
  obtain ⟨hB0, hB1⟩ := hB
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with hca | hac
    · rw [hA0 a c hca, zero_mul]
    · rw [hB0 c b (lt_of_lt_of_le hba hac), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a, hA1, hB1, one_mul]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [hA0 a c h, zero_mul]
      · rw [hB0 c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

lemma tri_trans {K W : Type} [CommRing K] [AddCommGroup W] [Module K W] {n : ℕ} {f g h : Fin n → W}
    (h1 : Tri K f g) (h2 : Tri K g h) : Tri K f h := by
  obtain ⟨A, hA, hfg⟩ := h1
  obtain ⟨B, hB, hgh⟩ := h2
  refine ⟨A * B, uni_mul hA hB, fun c => ?_⟩
  have e1 : ∀ b, g b = ∑ a, A a b • f a := hfg
  have e2 : h c = ∑ b, B b c • g b := hgh c
  rw [e2]
  simp_rw [e1, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun b _ => by rw [mul_comm]

lemma tri_map {K W : Type} [CommRing K] [AddCommGroup W] [Module K W] {n : ℕ} {f h : Fin n → W}
    (g : W ≃ₗ[K] W) (h1 : Tri K f h) : Tri K (fun a => g (f a)) (fun a => g (h a)) := by
  obtain ⟨A, hA, hfh⟩ := h1
  refine ⟨A, hA, fun b => ?_⟩
  have e : h b = ∑ a, A a b • f a := hfh b
  show g (h b) = ∑ a, A a b • g (f a)
  rw [e, map_sum]
  simp_rw [map_smul]

end Loc

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem frame_castSucc {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (i : Fin D.R.rS) :
    frame F i.castSucc = F.fl.e i := by
  show F.fl.fvec i.castSucc = F.fl.e i
  simp only [FlagG.fvec, Fin.snoc_castSucc]

theorem tri_of_adapt {T : D.host.E} (g : GV D) (F G : LFlag (VS D) D.R.rS T) (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (h : ∀ a : Fin (D.R.rS + 1), g (frame F a) - frame G a ∈ Xflag G a.val) :
    GlobalTheory.LocOver.Tri D.host.E (frame G) (frame (Formalism.L2.SG.Saturated.mapL g hg F)) := by
  have hcs : ∀ i : Fin D.R.rS, frame G i.castSucc = G.fl.e i := fun i => frame_castSucc G i
  have h0 : ∀ a : Fin (D.R.rS + 1), ∃ l ∈ Finsupp.supported D.host.E D.host.E {i : Fin D.R.rS | i.val < a.val},
      ∑ i, l i • G.fl.e i = g (frame F a) - frame G a := by
    intro a
    have ha := h a
    simp only [Xflag, FlagG.Xa] at ha
    obtain ⟨l, hl, hsum⟩ := (Finsupp.mem_span_image_iff_linearCombination (R := D.host.E)).1 ha
    refine ⟨l, hl, ?_⟩
    rw [← hsum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp
  choose l hl hsum using h0
  refine ⟨fun a b => (if a = b then 1 else 0) + Fin.lastCases 0 (fun i => l b i) a, ⟨?_, ?_⟩, ?_⟩
  · intro a b hba
    have hne : a ≠ b := fun e => lt_irrefl _ (e ▸ hba)
    beta_reduce
    rw [if_neg hne, zero_add]
    rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl
    · rw [Fin.lastCases_castSucc]
      exact (Finsupp.mem_supported' _ _).1 (hl b) i
        (by simp only [Set.mem_ofPred_eq, not_lt]; exact le_of_lt (by simpa [Fin.lt_def] using hba))
    · rw [Fin.lastCases_last]
  · intro a
    beta_reduce
    rw [if_pos rfl]
    rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl
    · rw [Fin.lastCases_castSucc, (Finsupp.mem_supported' _ _).1 (hl i.castSucc) i (by simp), add_zero]
    · rw [Fin.lastCases_last, add_zero]
  · intro b
    rw [Formalism.L2.SG.Saturated.frame_mapL]
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, zero_smul, add_zero, hcs]
    rw [hsum b]
    abel

theorem tri_loc (Z : LocDat D) (p : PlF D) {T : D.host.E} (g : GV D) (F G : LFlag (VS D) D.R.rS T)
    (h : Adapt g F G) (g' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hg' : GlobalTheory.LocOver.Ext p g g') :
    GlobalTheory.LocOver.Tri (D.s.atP p).Ep (GlobalTheory.LocOver.scaled Z p (frame G))
      (fun a => g' (GlobalTheory.LocOver.scaled Z p (frame F) a)) := by
  obtain ⟨hg, hadp⟩ := h
  obtain ⟨A, hA, hC⟩ := tri_of_adapt g F G hg hadp
  obtain ⟨Ap, hAp, -⟩ := GlobalTheory.LocOver.tri_scaled D Z (frame G) (frame (Formalism.L2.SG.Saturated.mapL g hg F)) A hA hC
  obtain ⟨hU, hC'⟩ := hAp p
  have hx : ∀ x, g' (baseChange₂ D p x) = baseChange₂ D p (g x) := hg'
  have e : GlobalTheory.LocOver.scaled Z p (frame (Formalism.L2.SG.Saturated.mapL g hg F)) =
      fun a => g' (GlobalTheory.LocOver.scaled Z p (frame F) a) := by
    funext a
    simp only [GlobalTheory.LocOver.scaled, Formalism.L2.SG.Saturated.frame_mapL, map_smul, hx]
  exact ⟨Ap p, hU, e ▸ hC'⟩

theorem locBBne_iff (Z : LocDat D) (p : PlF D) (Λ : LV D) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) :
    LocNG.BBne (H := locH Z p) (GlobalTheory.LocOver.locU Z p Λ F F' Tn T'n) ↔ locBBne Z p Λ F F' Tn T'n := by
  have hmem : ∀ x : (D.s.atP p).Ep, x * x = 1 → x ∈ (Z.M p).L.O := fun x hx => by
    rw [(Z.M p).L.O_def]
    exact IsIntegral.of_pow two_pos (by rw [sq, hx]; exact isIntegral_one)
  have hsplit : ∀ g, (Z.M p).split = some g → ∀ b, sgnP' D p b = sgnP D p b := by
    intro g hg b
    have ag := Z.agree p
    unfold Agree at ag
    obtain ⟨-, -, -, -, -, hm⟩ := ag
    rw [hg] at hm
    unfold sgnP'
    rcases hs : (D.s.atP p).split with _ | sg
    · rw [hs] at hm; exact (hm : False).elim
    · rfl
  let s : Fin (D.R.rS + 1) → (Z.M p).L.O := fun a => ⟨sgnP D p a, hmem _ (localSign_sq p a)⟩
  let s' : Fin (D.R.rS + 1) → (Z.M p).L.O := fun a => ⟨sgnP' D p a, hmem _ (sgnP'_sq p a)⟩
  unfold locBBne
  exact bbne_sign (locH Z p) (locTerm Z p Λ F F' Tn T'n) (GlobalTheory.LocOver.locU Z p Λ F F' Tn T'n) s s'
    (fun a => Subtype.ext (localSign_sq p a)) (fun a => Subtype.ext (sgnP'_sq p a)) rfl
    (fun a => congrFun (GlobalTheory.LocOver.locU_f_eq Z p Λ F F' Tn T'n) a)
    (fun a => congrFun (GlobalTheory.LocOver.locU_f'_eq Z p Λ F F' Tn T'n) a)
    (fun g hg => funext fun b => Subtype.ext (hsplit g hg b))

theorem generic_iff_frame {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (Z : LocDat D) (t : TauC Y u u') :
    t.generic ↔ ∀ p, ¬ locBBne Z p t.lam (lf D (X.Fu u)) t.frame (Tu D u) (Tu D u') := by
  have hG := genIffLocBB_of Z (Formalism.L2.SG.Pf.bbTie_holds D Z) u u' (Formalism.L2.SG.Pf.big_block_function_holds D u u')
    (fun F0 Λ F' => Formalism.L2.SG.Pf.m_plus_independent _ _ _ _)
  have hR : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 _ t.mem
  have hf : ∀ p (x y : Formalism.L2.SG.TermDef.Carrier (Formalism.L2.SG.TermDef.PD D t.lam (lf D (X.Fu u)) u')),
      Formalism.L2.SG.TermDef.Rel t.lam (lf D (X.Fu u)) (Formalism.L2.SG.TermDef.PD D t.lam (lf D (X.Fu u)) u') x y →
      locBBne Z p t.lam (lf D (X.Fu u)) x.1 (Tu D u) (Tu D u') =
        locBBne Z p t.lam (lf D (X.Fu u)) y.1 (Tu D u) (Tu D u') := by
    intro p x y hxy
    apply propext
    have e1 := Formalism.L2.SG.Pf.bbTie_holds D Z u u' (X.Fu u) t.lam x.1 hR x.2
      (Formalism.L2.SG.Pf.m_plus_independent _ _ _ _) p
    have e2 := Formalism.L2.SG.Pf.bbTie_holds D Z u u' (X.Fu u) t.lam y.1 hR y.2
      (Formalism.L2.SG.Pf.m_plus_independent _ _ _ _) p
    refine e1.symm.trans (Iff.trans ?_ e2)
    unfold Formalism.L2.SG.Saturated.BBneF
    exact exists_congr fun P => and_congr_right fun _ =>
      Formalism.L2.SG.Pf.big_block_function_holds D u u' (X.Fu u) t.lam hR P x y hxy
  unfold GTerm.generic GTerm.frame
  rw [hG (X.Fu u) (Y.what₂ u) (Y.rowsOK u) (GTerm.toTerm t)]
  unfold GTerm.toTerm
  refine forall_congr' fun p => not_congr ?_
  unfold locBBneT
  exact (Formalism.L2.SG.TermDef.const_of_mk
    (fun x : Formalism.L2.SG.TermDef.Carrier (Formalism.L2.SG.TermDef.PD D t.lam (lf D (X.Fu u)) u') =>
      locBBne Z p t.lam (lf D (X.Fu u)) x.1 (Tu D u) (Tu D u')) (hf p) (Quot.out_eq _)).to_iff

theorem rank_loc (p : PlF D) : Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := Ranks.r_eq (R := D.R)
  have h2 := Ranks.rS_two (R := D.R)
  omega

theorem generic_iff_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → (t.generic ↔ ∀ p d τ, LocNG.IsTermOver (FP p) d τ → τ.abelian₂ = lattice₂ D Z.M p Λ → ¬ LocNG.BBne (H := locH Z p) τ) := by
  intro D X Y u u' F F' w hZw hGv Z FP hB hRel t Λ hTG
  have hC := GlobalTheory.T.term_at_base_point_of_frames D X Y u u' F F' w hZw hGv t Λ hTG
  have hPD : Formalism.L2.SG.TermDef.PD D t.lam (lf D (X.Fu u)) u' (GTerm.frame t) := (Quot.out t.cls).2.2.2.2
  have hR : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 _ t.mem
  have hgf := (Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam hR).1
  have hG0 : Gval (lf D (X.Fu u)) (GTerm.frame t) ≠ 0 := by
    have e := Formalism.L2.SG.TermDef.Gt_mk hgf ⟨GTerm.frame t, hPD⟩
    intro h0
    exact hC.1 (e.trans h0)
  obtain ⟨g, hA1, hA2, hΛ⟩ := hTG
  rw [generic_iff_frame Z t]
  refine forall_congr' fun p => ?_
  obtain ⟨gp, hext, hunit, -, himg, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p g hA1.1
  obtain ⟨hU, htriU⟩ := GlobalTheory.LocOver.locU_isTerm D Z u u' (X.Fu u) t.lam hR (GTerm.frame t) hPD hG0 p
  have hOK : (Z.M p).OK := (Z.agree p).1
  obtain ⟨hfA, hfB, hTA, hTB⟩ := hB p
  set τ0 := GlobalTheory.LocOver.move gp
    (GlobalTheory.LocOver.locU Z p t.lam (lf D (X.Fu u)) (GTerm.frame t) (Tu D u) (Tu D u'))
  have hτ0T : (locH Z p).IsTerm τ0 := isTerm_move (locH Z p) hunit hU
  have htA : GlobalTheory.LocOver.Tri (D.s.atP p).Ep (FP p).A.f τ0.f := by
    rw [hfA]
    exact tri_loc Z p g (lf D (X.Fu u)) F hA1 gp hext
  have htB : GlobalTheory.LocOver.Tri (D.s.atP p).Ep (FP p).B.f τ0.f' := by
    rw [hfB]
    exact tri_trans (tri_loc Z p g (GTerm.frame t) F' hA2 gp hext) (tri_map gp htriU)
  obtain ⟨d0, hd0⟩ := GlobalTheory.T.exists_datum_of_two_congruent_frames (Z.M p) hOK (locH Z p) D.R.rS (FP p) τ0 hτ0T hTA.symm hTB.symm htA htB
  have hLam : τ0.abelian₂ = lattice₂ D Z.M p Λ := by
    rw [hΛ]
    exact himg t.lam
  rw [← locBBne_iff, ← bbne_move (locH Z p) gp
    (GlobalTheory.LocOver.locU Z p t.lam (lf D (X.Fu u)) (GTerm.frame t) (Tu D u) (Tu D u'))]
  constructor
  · intro hn d τ hτ hτL h
    exact hn ((GlobalTheory.T.localTerm_defect_eq_of_lattice_eq (Z.M p) hOK (locH Z p) D.R.rS D.R.k (FP p) (rank_loc p) (hRel p) d d0 τ τ0 hτ hd0
      (hτL.trans hLam.symm)).1 h)
  · intro h
    exact h d0 τ0 hd0 hLam

end GlobalTheory.Unfold.GenLoc

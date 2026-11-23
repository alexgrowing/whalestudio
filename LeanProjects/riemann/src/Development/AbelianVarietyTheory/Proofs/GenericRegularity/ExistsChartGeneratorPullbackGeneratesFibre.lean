import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionNowhereZeroOfPullbackTriple
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSecPullNonzeroOnFibres

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.ChartGenerator

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.SectionBaseChange GlobalTheory.SecTransport GlobalTheory.Frames

section Stalk

variable {X Z : Scheme.{0}}

theorem flat_fromSpecStalk (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx, IsAffineOpen.fromSpecStalk]
  have : Flat (Spec.map (X.presheaf.germ U x hx)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
    have := hU.isLocalization_stalk ⟨x, hx⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  infer_instance

theorem stalkMap_injective (r : Z ⟶ X) [Flat r] (z : Z) : Function.Injective (r.stalkMap z).hom := by
  refine (injective_iff_map_eq_zero _).2 fun b hb => zero_dvd_iff.1 (dvd_descend r z ?_)
  rw [hb]; exact dvd_zero _

theorem fromSpecStalk_mem (x : X) {U : X.Opens} (hx : x ∈ U) (y : Spec (X.presheaf.stalk x)) :
    X.fromSpecStalk x y ∈ U := by
  have : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y, rfl⟩
  rw [Scheme.range_fromSpecStalk] at this
  exact Specializes.mem_open this U.isOpen hx

theorem gs_fromSpecStalk (x : X) {U : X.Opens} (hx : x ∈ U) (r : Z ⟶ Sp (X.presheaf.stalk x)) (z : Z)
    (a : Γ(X, U)) : gs (r ≫ X.fromSpecStalk x) z U a = cst r z (gs (𝟙 X) x U a) := by
  have hm := fromSpecStalk_mem x hx (r z)
  rw [← gs_pull r _ z U hm, Scheme.fromSpecStalk_app hx, cst, gs_eq (𝟙 X) x U hx]
  exact gs_res r z le_top hm _

theorem gs_eq_near {U : X.Opens} {x : X} (hx : x ∈ U) {a b : Γ(X, U)} (h : gs (𝟙 X) x U a = gs (𝟙 X) x U b) :
    ∃ W : X.Opens, x ∈ W ∧ W ≤ U ∧ ∀ y ∈ W, gs (𝟙 X) y U a = gs (𝟙 X) y U b := by
  rw [gs_eq _ x _ hx, gs_eq _ x _ hx] at h
  obtain ⟨W, hW, i₁, i₂, e⟩ := X.presheaf.germ_eq x hx hx _ _ h
  refine ⟨W, hW, i₁.le, fun y hy => ?_⟩
  exact (gs_res (𝟙 X) y i₁.le hy a).symm.trans ((congrArg (gs (𝟙 X) y W) e).trans (gs_res (𝟙 X) y i₂.le hy b))

end Stalk

theorem generates_of_isLocalRing (hT : SecTwistSt) {S : Scheme.{0}} (P : PolAV S) (C : Type) [CommRing C] [IsLocalRing C]
    (t : Sp C ⟶ S) (θ : (twistLB P.A P.L 1 (1 : Over.mk t ⟶ P.A)).Sec)
    (hθ : ∃ y, (fst (Over.mk t) P.A).left y = IsLocalRing.closedPoint C ∧ y ∈ nonzeroLocus θ)
    (s : (twistLB P.A P.L 1 (1 : Over.mk t ⟶ P.A)).Sec) :
    ∃! a : C, ∀ j, ∀ y ∈ (twistLB P.A P.L 1 (1 : Over.mk t ⟶ P.A)).U j,
      gs (𝟙 _) y _ (s.f j) = cst (fst (Over.mk t) P.A).left y a * gs (𝟙 _) y _ (θ.f j) := by
  obtain ⟨⟨b, hb⟩, -⟩ := hT S P 1 le_rfl C t 1
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv
  have basis : ∀ σ : (twistLB P.A P.L 1 (1 : Over.mk t ⟶ P.A)).Sec, ∃! a : C,
      ∀ j, ∀ y ∈ (twistLB P.A P.L 1 (1 : Over.mk t ⟶ P.A)).U j,
      gs (𝟙 _) y _ (σ.f j) = cst (fst (Over.mk t) P.A).left y a * gs (𝟙 _) y _ ((b hq.default).f j) := fun σ => by
    obtain ⟨r, hr, hu⟩ := hb σ
    obtain ⟨a, ha⟩ := bij.2 (r hq.default)
    refine ⟨a, (sec_eq_iff (fst (Over.mk t) P.A).left σ _ a).1 fun j => ?_, fun a' ha' => bij.1 ?_⟩
    · rw [hr j, Fintype.sum_unique, ← ha]; rfl
    · have e := (sec_eq_iff (fst (Over.mk t) P.A).left σ _ a').2 ha'
      have := hu (fun _ => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom a') fun j => by
        rw [e j, Fintype.sum_unique]; rfl
      exact (congrFun this hq.default).trans ha.symm
  obtain ⟨u, hu, -⟩ := basis θ
  have un : IsUnit u := by
    by_contra hn
    obtain ⟨y, hy, hy'⟩ := hθ
    obtain ⟨j, hj, h⟩ := (SectionBaseChange.mem_nonzeroLocus θ y).1 hy'
    rw [hu j y hj] at h
    exact cst_not_isUnit _ y hy hn (isUnit_of_mul_isUnit_left h)
  obtain ⟨u, rfl⟩ := un
  obtain ⟨r, hr, hru⟩ := basis s
  refine ⟨r * (u⁻¹).val, fun j y hy => ?_, fun a ha => ?_⟩
  · rw [hr j y hy, hu j y hy, ← _root_.mul_assoc, ← cst_mul, Units.inv_mul_cancel_right]
  · refine (Units.eq_mul_inv_iff_mul_eq u).2 (hru _ fun j y hy => ?_)
    rw [ha j y hy, hu j y hy, ← _root_.mul_assoc, ← cst_mul]

theorem generates_stalk (hT : SecTwistSt) {S : Scheme.{0}} (P : PolAV S) {B : Scheme.{0}}
    {t : B ⟶ S} {X' : Scheme.{0}} {q : X' ⟶ B} {φ : X' ⟶ P.A.left} (hφ : IsPullback φ q P.A.hom t) {L' : LB X'}
    (hL' : L'.IsLB) (hw : LBIso L' (P.L.pull φ)) (θ : L'.Sec) (hθ : ∀ y : B, ∃ x : X', q x = y ∧ x ∈ nonzeroLocus θ)
    (s : L'.Sec) (p : B) :
    (∃ (U : B.Opens) (a : Γ(B, U)), p ∈ U ∧ ∀ k, ∀ x ∈ L'.U k, q x = p →
      gs (𝟙 X') x _ (s.f k) = gs q x U a * gs (𝟙 X') x _ (θ.f k)) ∧
    ∀ (U : B.Opens) (a a' : Γ(B, U)), p ∈ U →
      (∀ k, ∀ x ∈ L'.U k, q x ∈ U → gs (𝟙 X') x _ (s.f k) = gs q x U a * gs (𝟙 X') x _ (θ.f k)) →
      (∀ k, ∀ x ∈ L'.U k, q x ∈ U → gs (𝟙 X') x _ (s.f k) = gs q x U a' * gs (𝟙 X') x _ (θ.f k)) →
      gs (𝟙 B) p U a = gs (𝟙 B) p U a' := by
  let u : Sp (B.presheaf.stalk p) ⟶ B := B.fromSpecStalk p
  have hι : Flat u := flat_fromSpecStalk p
  let T : Over S := Over.mk (u ≫ t)
  have big : IsPullback (snd T P.A).left (fst T P.A).left P.A.hom (u ≫ t) := (IsPullback.of_hasPullback _ _).flip
  let ρ : (T ⊗ P.A).left ⟶ X' := hφ.lift (snd T P.A).left ((fst T P.A).left ≫ u) (by rw [Category.assoc]; exact big.w)
  have ρ₁ : ρ ≫ φ = (snd T P.A).left := hφ.lift_fst _ _ _
  have ρ₂ : ρ ≫ q = (fst T P.A).left ≫ u := hφ.lift_snd _ _ _
  have sq : IsPullback ρ (fst T P.A).left q u := IsPullback.of_right (by rw [ρ₁]; exact big) ρ₂ hφ
  have hρ : Flat ρ := MorphismProperty.of_isPullback (P := @Flat) sq.flip hι
  have := P.isAb.comm
  have e : translPt P.A (1 : T ⟶ P.A) = snd T P.A := by
    show (fst T P.A ≫ 1) * snd T P.A = _
    rw [MonObj.comp_one, _root_.one_mul]
  have h₁ : LBIso (twistLB P.A P.L 1 (1 : T ⟶ P.A)) (P.L.pull (snd T P.A).left) :=
    exists_iso_linComb (F := (snd T P.A).left) P.isLB (K := Fin 2)
      ![(snd T P.A).left, (translPt P.A (1 : T ⟶ P.A)).left] ![((1 : ℕ) : ℤ) - 1, 1] (fun U _ k => by
        rw [e]; simp [Fin.prod_univ_succ])
  have hM : (twistLB P.A P.L 1 (1 : T ⟶ P.A)).IsLB := DVR.linComb_isLB P.L P.isLB _ _
  have m : ∀ (j : PUnit → P.L.ι) (y : (T ⊗ P.A).left), y ∈ (P.L.pull (snd T P.A).left).U j →
      ρ y ∈ (P.L.pull φ).U j := fun j y h =>
    mem_pull.2 ((congrArg (fun e => e y ∈ P.L.U (j PUnit.unit)) ρ₁).mpr (mem_pull.1 h))
  let cp : ChartPull (P.L.pull (snd T P.A).left) (P.L.pull φ) ρ :=
    { idx := fun j => j
      le := m
      g := fun y i j hi hj => (gm_pull_g P.L _ (𝟙 _) y i j hi hj).trans
        (Eq.trans (by rw [ρ₁, Category.id_comp]) (gm_pull_g P.L φ ρ y _ _ (m i y hi) (m j y hj)).symm) }
  obtain ⟨w, hw'⟩ := LBIso.trans hM (DVR.linComb_isLB P.L P.isLB _ _) (DVR.linComb_isLB L' hL' _ _) h₁
    (LBIso.chartPull cp (chartPullPull L' ρ ρ rfl) hw.symm)
  have down := sec_pull_down ((isGen_iff w).1 hw') hL' hM
  obtain ⟨θU, hθU⟩ := down θ
  obtain ⟨sU, hsU⟩ := down s
  have G := generates_of_isLocalRing hT P _ (u ≫ t) θU (fibre_nonzero_of_pull hM hθU sq hθ _) sU
  have key : ∀ (U : B.Opens) (a : Γ(B, U)) (y : (T ⊗ P.A).left) k j, p ∈ U → ρ y ∈ L'.U k →
      y ∈ (twistLB P.A P.L 1 (1 : T ⟶ P.A)).U j →
      (gs (𝟙 _) y _ (sU.f j) = cst (fst T P.A).left y (gs (𝟙 B) p U a) * gs (𝟙 _) y _ (θU.f j) ↔
      gs (𝟙 X') (ρ y) _ (s.f k) = gs q (ρ y) U a * gs (𝟙 X') (ρ y) _ (θ.f k)) := fun U a y k j hp hk hj => by
    have hq : q (ρ y) ∈ U := (congrArg (fun e => e y ∈ U) ρ₂).mpr (fromSpecStalk_mem p hp _)
    have inj := stalkMap_injective ρ y
    have c : (ρ.stalkMap y).hom (gs q (ρ y) U a) = cst (fst T P.A).left y (gs (𝟙 B) p U a) := by
      rw [gs_comp_stalkMap ρ q y U hq, ρ₂]
      exact gs_fromSpecStalk p hp _ y a
    have e₁ := hsU _ (𝟙 _) y k j hk hj
    have e₂ := hθU _ (𝟙 _) y k j hk hj
    rw [Category.id_comp] at e₁ e₂
    rw [← inj.eq_iff, map_mul, c, ← gs_stalkMap ρ y _ hk, ← gs_stalkMap ρ y _ hk, e₁, e₂, mul_left_comm,
      Units.mul_right_inj]
  refine ⟨?_, fun U a a' hp h h' => G.unique (fun j y hj => ?_) (fun j y hj => ?_)⟩
  · obtain ⟨a₀, ha₀, -⟩ := G
    obtain ⟨U, hU, a, rfl⟩ := B.presheaf.exists_germ_eq a₀
    refine ⟨U, a, hU, fun k x hk hx => ?_⟩
    obtain ⟨y, h₁, -⟩ := Scheme.exists_preimage_of_isPullback sq x (IsLocalRing.closedPoint _)
      (hx.trans Scheme.fromSpecStalk_closedPoint.symm)
    obtain rfl : ρ y = x := h₁
    obtain ⟨j, hj⟩ := exists_chart hM y
    refine (key U a y k j hU hk hj).1 ?_
    rw [gs_eq (𝟙 B) p U hU]
    exact ha₀ j y hj
  · obtain ⟨k, hk⟩ := exists_chart hL' (ρ y)
    exact (key U a y k j hp hk hj).2 (h k _ hk ((congrArg (fun e => e y ∈ U) ρ₂).mpr (fromSpecStalk_mem p hp _)))
  · obtain ⟨k, hk⟩ := exists_chart hL' (ρ y)
    exact (key U a' y k j hp hk hj).2 (h' k _ hk ((congrArg (fun e => e y ∈ U) ρ₂).mpr (fromSpecStalk_mem p hp _)))

theorem generates (hT : SecTwistSt) {S : Scheme.{0}} (P : PolAV S) {R' : Type} [CommRing R']
    {t : Sp R' ⟶ S} {X' : Scheme.{0}} {q : X' ⟶ Sp R'} {φ : X' ⟶ P.A.left} (hφ : IsPullback φ q P.A.hom t) {L' : LB X'}
    (hL' : L'.IsLB) (hw : LBIso L' (P.L.pull φ)) (θ : L'.Sec) (hθ : ∀ y : Sp R', ∃ x : X', q x = y ∧ x ∈ nonzeroLocus θ)
    (s : L'.Sec) : ∃! a : R', ∀ i, s.f i = constFn q _ a * θ.f i := by
  have H := generates_stalk hT P hφ hL' hw θ hθ s
  have hpr : IsProper q := MorphismProperty.of_isPullback (P := @IsProper) hφ P.isAb.proper
  let Rel : ∀ U : (Sp R').Opens, Γ(Sp R', U) → Prop := fun U a => ∀ k, ∀ x ∈ L'.U k, q x ∈ U →
    gs (𝟙 X') x _ (s.f k) = gs q x U a * gs (𝟙 X') x _ (θ.f k)
  have hres : ∀ (U W : (Sp R').Opens) (h : U ≤ W) (a : Γ(Sp R', W)), Rel W a → Rel U (resG _ h a) :=
    fun U W h a ha k x hk hx => (ha k x hk (h hx)).trans (congrArg₂ (· * ·) (gs_res q x h hx a).symm rfl)
  have main : ∃! a, Rel ⊤ a := by
    refine existsUnique_of_local Rel (fun U => ∃ a, Rel U a) (fun p W hp => ?_) hres (fun a h k x hk _ => ?_) ?_
    · obtain ⟨U, a, hU, ha⟩ := (H p).1
      have near : ∀ x : X', q x = p → ∃ V : X'.Opens, x ∈ V ∧ ∀ y ∈ V, ∀ k, y ∈ L'.U k →
          gs (𝟙 X') y _ (s.f k) = gs q y U a * gs (𝟙 X') y _ (θ.f k) := fun x hx => by
        obtain ⟨k, hk⟩ := exists_chart hL' x
        have v : ∀ y ∈ L'.U k ⊓ q ⁻¹ᵁ U, gs (𝟙 X') y (L'.U k ⊓ q ⁻¹ᵁ U) (q.appLE U _ inf_le_right a *
            resG X' inf_le_left (θ.f k)) = gs q y U a * gs (𝟙 X') y _ (θ.f k) := fun y hy =>
          (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_appLE q U _ inf_le_right (𝟙 _) y hy a).trans
            (by rw [Category.id_comp])) (gs_res _ y inf_le_left hy _))
        have hm : x ∈ L'.U k ⊓ q ⁻¹ᵁ U := ⟨hk, show q x ∈ U from hx ▸ hU⟩
        obtain ⟨V, hV, le, hV'⟩ := gs_eq_near hm (a := resG X' inf_le_left (s.f k))
          (((gs_res _ x inf_le_left hm _).trans (ha k x hk hx)).trans (v x hm).symm)
        refine ⟨V, hV, fun y hy k' hk' => ?_⟩
        have e := ((gs_res (𝟙 X') y inf_le_left (le hy) _).symm.trans (hV' y hy)).trans (v y (le hy))
        rw [gs_compat s (𝟙 X') y hk' (le hy).1, gs_compat θ (𝟙 X') y hk' (le hy).1, e, mul_left_comm]
      choose V hV hV' using near
      let O : X'.Opens := ⨆ x : {x : X' // q x = p}, V x.1 x.2
      have cl : IsClosed (q '' (O : Set X')ᶜ) := q.isClosedMap _ O.isOpen.isClosed_compl
      let W' : (Sp R').Opens := ⟨(q '' (O : Set X')ᶜ)ᶜ, cl.isOpen_compl⟩
      have hp' : p ∈ W' := by
        rintro ⟨x, hx, e⟩
        exact hx (Opens.mem_iSup.2 ⟨⟨x, e⟩, hV x e⟩)
      refine ⟨W ⊓ (W' ⊓ U), inf_le_left, ⟨hp, hp', hU⟩, resG _ (inf_le_right.trans inf_le_right) a, fun k x hk hx => ?_⟩
      have hO : x ∈ O := by
        by_contra hn
        exact hx.2.1 ⟨x, hn, rfl⟩
      obtain ⟨z, hz⟩ := Opens.mem_iSup.1 hO
      exact (hV' z.1 z.2 x hz k hk).trans (congrArg₂ (· * ·) (gs_res q x _ hx a).symm rfl)
    · obtain ⟨U, hU, h'⟩ := h (q x)
      exact (h' k x hk hU).trans (congrArg₂ (· * ·) (gs_res q x le_top hU a) rfl)
    · rintro U ⟨a, ha⟩
      exact ⟨a, ha, fun a' ha' => fn_ext fun p hp => (H p).2 U a' a hp ha' ha⟩
  have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R')).inv
  obtain ⟨r, hr, hu⟩ := main
  obtain ⟨a, rfl⟩ := bij.2 r
  exact ⟨a, (sec_eq_iff _ _ _ _).2 fun k x hk => hr k x hk trivial,
    fun a' ha' => bij.1 (hu _ fun k x hk _ => (sec_eq_iff _ _ _ _).1 ha' k x hk)⟩

theorem secGen_of_secNZ (hT : SecTwistSt) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {T : Type} [CommRing T] (x : Sp T ⟶ Xo.X) (θ : LB.Sec (PPx x)) (h : SecNZ x θ) :
    SecGen x θ := by
  intro s
  have hw : LBIso (PPx x) (Xo.univ.t.PP.L.pull (snd (Over.mk x) Xo.univ.t.G).left) :=
    exists_iso_linComb Xo.univ.t.PP.isLB _ _ fun _ _ _ => by simp
  refine generates hT (Obj.toPolAV Xo.univ) (IsPullback.of_hasPullback _ _).flip
    (DVR.linComb_isLB _ Xo.univ.t.PP.isLB _ _) hw θ (fun y => ?_) s
  obtain ⟨q, i, hq, hi⟩ := h y
  exact ⟨q, hq, Opens.mem_iSup.2 ⟨i, hi⟩⟩

set_option maxHeartbeats 400000 in

theorem exists_thTie_generator : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∃ s : LB.Sec (PPx x), Λ.ThTie s ∧ ∀ s' : LB.Sec (PPx x), ∃! a : R, ∀ i, s'.f i = scal x a i * s.f i := by
  intro hT E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ
  obtain ⟨w2, σ', r2, hcl, hnz⟩ := exists_sec_pull_nonzero_on_fibres E H _ _ Y.t Λ.t' _ Λ.m2 M.U
    (fun y _ => M.hU.range_fromSpec.le ⟨spMap f y, rfl⟩) M.θ M.θ_mem M.θ_ne
  obtain ⟨w1, g1, r1, -⟩ := Λ.m1.lin
  have hw1 := (isGen_iff w1).1 g1
  have hL := Xo.univ.t.PP.isLB
  have hL' := Λ.t'.PP.isLB
  obtain ⟨s1, hs1⟩ := exists_sec_along_iso hw1 hL hL' σ'
  let A := Xo.univ.t.G
  have cond : (snd (Over.mk x) A).left ≫ A.hom = (fst (Over.mk x) A).left ≫ x :=
    (Over.w (snd (Over.mk x) A)).trans (Over.w (fst (Over.mk x) A)).symm
  let h : Gx x ⟶ Λ.t'.G.left := Λ.m1.cart.1.lift _ _ cond
  have hφ : h ≫ Λ.m1.φ = (snd (Over.mk x) A).left := Λ.m1.cart.1.lift_fst _ _ cond
  have hh : h ≫ Λ.t'.G.hom = (fst (Over.mk x) A).left := Λ.m1.cart.1.lift_snd _ _ cond
  let a0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk Λ.t'.G.hom rfl
  let b0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ A := Over.homMk Λ.m1.φ Λ.m1.cart.1.w
  let g0 : Λ.t'.G.left ⟶ Gx x := (lift a0 b0).left
  have g0f : g0 ≫ (fst (Over.mk x) A).left = Λ.t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
  have g0s : g0 ≫ (snd (Over.mk x) A).left = Λ.m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
  have uniq : ∀ g : Λ.t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) A).left = Λ.m1.φ →
      g ≫ (fst (Over.mk x) A).left = Λ.t'.G.hom → g ≫ h = 𝟙 _ := fun g e₁ e₂ =>
    Λ.m1.cart.1.hom_ext (by rw [Category.assoc, hφ, e₁, Category.id_comp])
      (by rw [Category.assoc, hh, e₂, Category.id_comp])
  have hg0 : g0 ≫ h = 𝟙 _ := uniq g0 g0s g0f
  let s : LB.Sec (PPx x) := secPullOne Xo.univ.t.PP.L h hφ s1
  have hI1 : IsoMaps w1 σ' s1 := fun (i : PUnit → Xo.univ.t.PP.L.ι) k => fn_ext fun y hy => by
    exact (gs_res _ y _ hy _).trans ((hs1 _ (𝟙 _) y i k hy.1 hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _)))))
  refine ⟨s, ⟨w1, w2, σ', s1, ⟨g1, r1⟩, r2, hI1, hcl, fun g e₁ e₂ j hj => fn_ext fun y hy =>
    Eq.symm ((gs_appLE g _ _ hj (𝟙 _) y hy _).trans
      ((gs_appLE h _ _ (chart_le_preimage _ h hφ _) (𝟙 _ ≫ g) y (hj hy) _).trans
        (congrArg (fun q => gs q y _ (s1.f j)) (by rw [Category.id_comp, uniq g e₁ e₂]))))⟩,
    secGen_of_secNZ hT x s fun p => ?_⟩
  obtain ⟨q, k, hq, hk⟩ := hnz p
  have hkU : q ∈ Λ.t'.PP.L.U k := Λ.t'.G.left.basicOpen_le _ hk
  obtain ⟨j, hj⟩ := exists_chart hL (Λ.m1.φ q)
  have mg : g0 q ∈ (PPx x).U (fun _ => j) :=
    Set.mem_iInter.2 fun _ => (congrArg (fun r => r q ∈ Xo.univ.t.PP.L.U j) g0s).mpr hj
  refine ⟨g0 q, fun _ => j, (congrArg (fun r => r q) g0f).trans hq, ?_⟩
  refine (isUnit_gs_iff g0 q _ mg _).1 ?_
  have e : gs g0 q _ (s.f (fun _ => j)) = (gw w1 (𝟙 _) q j k).val * gs (𝟙 _) q _ (σ'.f k) := by
    refine (gs_appLE h _ _ (chart_le_preimage _ h hφ _) g0 q mg _).trans ?_
    rw [hg0]
    exact hs1 _ (𝟙 _) q (fun _ => j) k (mem_pull.2 hj) hkU
  rw [e]
  exact (Units.isUnit _).mul ((isUnit_gs_iff (𝟙 _) q _ hkU _).2 hk)

end GlobalTheory.Reg.ChartGenerator

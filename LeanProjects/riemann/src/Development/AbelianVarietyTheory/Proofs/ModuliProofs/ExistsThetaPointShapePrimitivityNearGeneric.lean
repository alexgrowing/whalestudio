import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapeOfGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoGenericSpreadsOutStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescentStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBaseStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnitStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.GenericSpread

theorem lbIso_pull_of_comp {X Y Z : Scheme.{0}} {M N : LB X} {a : Y ⟶ X} {c : Z ⟶ X} (h : Z ⟶ Y) (e : c = h ≫ a)
    (H : LBIso (M.pull a) (N.pull a)) : LBIso (M.pull c) (N.pull c) :=
  LBIso.chartPull (chartPullSame M _ _ _ h fun _ => e) (chartPullSame N _ _ _ h fun _ => e) H

section Grp

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

def sqMap (h : IsGrpPullback G' G f φ) : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G ⊗ G :=
  lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))

theorem isPullback_sqMap (h : IsGrpPullback G' G f φ) :
    IsPullback (sqMap h).left (G' ⊗ G').hom (G ⊗ G).hom f := by
  have e₁ : (sqMap h).left ≫ (fst G G).left = (fst G' G').left ≫ φ :=
    congrArg (fun z => z.left) (lift_fst (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')))
  have e₂ : (sqMap h).left ≫ (snd G G).left = (snd G' G').left ≫ φ :=
    congrArg (fun z => z.left) (lift_snd (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')))
  have a' : IsPullback (fst G' G').left (snd G' G').left G'.hom G'.hom := IsPullback.of_hasPullback _ _
  have a : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  have b := a'.paste_horiz h.1
  rw [← e₁, ← h.1.w] at b
  have c := (IsPullback.of_right b e₂ a).paste_vert h.1
  rw [Over.w, Over.w] at c
  exact c

theorem pushPt_comp (h : IsGrpPullback G' G f φ) {w' : G' ⟶ G'} {w : G ⟶ G} (hw : w'.left ≫ φ = φ ≫ w.left)
    {T : Over S'} (x : T ⟶ G') : pushPt h.1.w (x ≫ w') = pushPt h.1.w x ≫ w :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, hw, Category.assoc])

theorem mul_left_comp (h : IsGrpPullback G' G f φ) {w' v' : G' ⟶ G'} {w v : G ⟶ G} (hw : w'.left ≫ φ = φ ≫ w.left)
    (hv : v'.left ≫ φ = φ ≫ v.left) : (w' * v').left ≫ φ = φ ≫ (w * v).left := by
  have b : pushPt h.1.w (w' * v') = pushPt h.1.w w' * pushPt h.1.w v' := map_mul (pushHom h G') _ _
  have c := pushPt_comp h hw (𝟙 G')
  have d := pushPt_comp h hv (𝟙 G')
  rw [Category.id_comp] at c d
  rw [c, d, ← MonObj.comp_mul] at b
  have e := congrArg (fun z => z.left) b
  refine e.trans ?_
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

variable [IsCommMonObj G] [IsCommMonObj G'] {L : LB G.left} {L' : LB G'.left}

theorem lbIso_cube_pull (h : IsGrpPullback G' G f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hb : LBIso L' (L.pull φ))
    {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G))
    (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) :
    LBIso (cubeLB G' x' L') ((cubeLB G x L).pull (Y := T'.left) U.left) :=
  LBIso.trans (DVR.linComb_isLB L' hL' _ _) (DVR.linComb_isLB _ (pull_isLB hL φ) _ _)
    (pull_isLB (DVR.linComb_isLB L hL _ _) _) (GlobalTheory.PowPrimitive.lbIso_linComb hb _ _)
    (LBIso.chartPull (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U hx I.down)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (PolBaseChange.lbIso_refl (DVR.linComb_isLB L hL _ _)))

theorem adj_iff (h : IsGrpPullback G' G f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hb : LBIso L' (L.pull φ))
    {w' v' : G' ⟶ G'} {w v : G ⟶ G} (hw : w'.left ≫ φ = φ ≫ w.left) (hv : v'.left ≫ φ = φ ≫ v.left) :
    LBIso (cubeLB G' ![fst G' G' ≫ w', snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ v'] L') ↔
      LBIso ((cubeLB G ![fst G G ≫ w, snd G G] L).pull (Y := (G' ⊗ G').left) (sqMap h).left)
        ((cubeLB G ![fst G G, snd G G ≫ v] L).pull (Y := (G' ⊗ G').left) (sqMap h).left) := by
  have a := lbIso_cube_pull h hL hL' hb ![fst G' G' ≫ w', snd G' G'] ![fst G G ≫ w, snd G G] (sqMap h) fun i => by
    fin_cases i
    · exact (pushPt_comp h hw _).trans (by simp [sqMap])
    · simp [sqMap]
  have b := lbIso_cube_pull h hL hL' hb ![fst G' G', snd G' G' ≫ v'] ![fst G G, snd G G ≫ v] (sqMap h) fun i => by
    fin_cases i
    · simp [sqMap]
    · exact (pushPt_comp h hv _).trans (by simp [sqMap])
  have i' : ∀ x : Fin 2 → (G' ⊗ G' ⟶ G'), (cubeLB G' x L').IsLB := fun x => DVR.linComb_isLB L' hL' _ _
  have i : ∀ x : Fin 2 → (G ⊗ G ⟶ G), ((cubeLB G x L).pull (Y := (G' ⊗ G').left) (sqMap h).left).IsLB :=
    fun x => pull_isLB (DVR.linComb_isLB L hL _ _) _
  exact ⟨fun H => LBIso.trans (i _) (i' _) (i _) a.symm (LBIso.trans (i' _) (i' _) (i _) H b),
    fun H => LBIso.trans (i' _) (i _) (i' _) a (LBIso.trans (i _) (i _) (i' _) H b.symm)⟩

theorem prim_iff (h : IsGrpPullback G' G f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hb : LBIso L' (L.pull φ))
    {w' : G' ⟶ G'} {w : G ⟶ G} (hw : w'.left ≫ φ = φ ≫ w.left) :
    LBIso L' (cubeLB G' ![𝟙 G', w'] L') ↔ LBIso (L.pull φ) ((cubeLB G ![𝟙 G, w] L).pull φ) := by
  have a := lbIso_cube_pull h hL hL' hb ![𝟙 G', w'] ![𝟙 G, w] (pushPt h.1.w (𝟙 G')) fun i => by
    fin_cases i
    · simp
    · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pushPt_comp h hw _)
  have e : (pushPt h.1.w (𝟙 G')).left = φ := Category.id_comp _
  rw [e] at a
  have i' : (cubeLB G' ![𝟙 G', w'] L').IsLB := DVR.linComb_isLB L' hL' _ _
  have i : ((cubeLB G ![𝟙 G, w] L).pull φ).IsLB := pull_isLB (DVR.linComb_isLB L hL _ _) _
  have j := pull_isLB hL φ
  exact ⟨fun H => LBIso.trans j hL' i hb.symm (LBIso.trans hL' i' i H a),
    fun H => LBIso.trans hL' j i' hb (LBIso.trans j i i' H a.symm)⟩

end Grp

theorem spread_lbIso (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {B BK : Scheme.{0}} (pB : B ⟶ Sp R) [QuasiCompact pB] [QuasiSeparated pB] {M N : LB B}
    (hM : M.IsLB) (hN : N.IsLB) {U : BK ⟶ B} {p : BK ⟶ Sp K} (h : IsPullback U p pB (spMap (algebraMap R K)))
    (H : LBIso (M.pull U) (N.pull U)) :
    ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → ∀ {B' : Scheme.{0}} {U' : B' ⟶ B}
      {p' : B' ⟶ Sp R'}, U' ≫ pB = p' ≫ spMap φ → LBIso (M.pull U') (N.pull U') := by
  obtain ⟨f, hf, Hf⟩ := GlobalTheory.T.lbIso_generic_spreads_out_alt R K B pB M N inferInstance inferInstance hM hN
    (lbIso_pull_of_comp h.isoPullback.inv h.isoPullback_inv_fst.symm H)
  exact ⟨f, hf, fun R' _ φ hu B' U' p' e =>
    lbIso_pull_of_comp (pullback.lift U' p' e) (pullback.lift_fst _ _ _).symm (Hf R' φ hu)⟩

theorem spread_prim {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {w w' : J} (R K : Type) [CommRing R]
    [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] {s : Sp R ⟶ Sp o}
    {s' : Sp K ⟶ Sp o} (t' : TObj g k J b s) (t : TObj g k J b s') (hm : TMap t t' (spMap (algebraMap R K)))
    (hp : t.Prim w w') :
    ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (s'' : Sp R' ⟶ Sp o) (t'' : TObj g k J b s''),
      IsUnit (φ f) → TMap t'' t' (spMap φ) → t''.Prim w w' := by
  obtain ⟨ψ, h, hb, -, ha⟩ := hm
  obtain ⟨h₁, h₂, h₃⟩ := hp
  letI := t.ab.comm
  letI := t'.ab.comm
  haveI : IsProper t'.A.hom := t'.ab.proper
  haveI : Smooth t'.A.hom := t'.ab.smooth
  haveI : IsProper (t'.A ⊗ t'.A).hom := by
    rw [← Over.w (fst t'.A t'.A)]
    haveI : IsProper (fst t'.A t'.A).left := inferInstanceAs (IsProper (pullback.fst t'.A.hom t'.A.hom))
    infer_instance
  obtain ⟨q₁, q₂⟩ := GlobalTheory.ExtUnique.spec_fractionRing R K
  have e₁ : t'.act w * t'.act w' = 𝟙 t'.A := by
    refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback h.1 ?_
    rw [← mul_left_comp h (ha w) (ha w'), h₁]
    simp
  obtain ⟨f₂, hf₂, H₂⟩ := spread_lbIso R K (t'.A ⊗ t'.A).hom (DVR.linComb_isLB _ t'.isLB _ _)
    (DVR.linComb_isLB _ t'.isLB _ _) (isPullback_sqMap h) ((adj_iff h t'.isLB t.isLB hb (ha w) (ha w')).1 h₂)
  obtain ⟨f₃, hf₃, H₃⟩ := spread_lbIso R K t'.A.hom t'.isLB
    (DVR.linComb_isLB _ t'.isLB _ _) h.1 ((prim_iff h t'.isLB t.isLB hb (ha w)).1 h₃)
  refine ⟨f₂ * f₃, mul_ne_zero hf₂ hf₃, fun R' _ φ s'' t'' hu ⟨ψ', h', hb', _, ha'⟩ => ?_⟩
  rw [map_mul] at hu
  letI := t''.ab.comm
  refine ⟨?_, (adj_iff h' t'.isLB t''.isLB hb' (ha' w) (ha' w')).2
    (H₂ R' φ (isUnit_of_mul_isUnit_left hu) (isPullback_sqMap h').w),
    (prim_iff h' t'.isLB t''.isLB hb' (ha' w)).2 (H₃ R' φ (isUnit_of_mul_isUnit_right hu) h'.1.w)⟩
  apply Over.OverMorphism.ext
  apply h'.1.hom_ext
  · rw [mul_left_comp h' (ha' w) (ha' w'), e₁]
    simp
  · rw [Over.w, Over.w]

theorem hasTh_unit_mul {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {S : Scheme.{0}}
    {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {R : Type} [CommRing R] {x : Sp R ⟶ S} {v v' : Ix g (N' ^ 2) → R}
    (c : R) (hc : IsUnit c) (e : ∀ a, v' a = c * v a) (H : t.HasTh x v) : t.HasTh x v' := by
  obtain ⟨h₁, h₂, h₃⟩ := H
  refine ⟨h₁, h₂, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h₃ p
  obtain ⟨u', hu⟩ : ∃ u' : Γ((Out.overRes V).left, ⊤)ˣ, u'.val =
      V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) :=
    (hc.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).map V.ι.appTop.hom
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, u' * u, a₁, a₂, a₃, a₄, a₅, a₆, a₇, fun i => ?_⟩
  rw [Units.val_mul, _root_.mul_assoc, ← a₈ i, hu]
  beta_reduce
  rw [e, map_mul]
  exact map_mul V.ι.appTop.hom _ _

theorem exists_eq_mul_of_field (hL : Out.Laws) (hL2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} {S : Scheme.{0}} {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {K : Type} [Field K]
    {x : Sp K ⟶ S} {v v' : Ix g (N' ^ 2) → K} (H : t.HasTh x v) (H' : t.HasTh x v') :
    ∃ c : K, c ≠ 0 ∧ ∀ a, v' a = c * v a := by
  have key : ∀ z : Ix g (N' ^ 2) → K, Ideal.span (Set.range z) = ⊤ ∨ ∀ a, z a = 0 := fun z =>
    (Ideal.eq_bot_or_top (Ideal.span (Set.range z))).symm.imp id fun h a =>
      Ideal.span_eq_bot.1 h _ (Set.mem_range_self a)
  rcases key v with h | h
  · obtain ⟨u, hu⟩ := GlobalTheory.T.thetaConstants_unique_up_to_unit hL hL2 o g N' J b S s t K x v v' H H' h
    exact ⟨(u : K), u.ne_zero, hu⟩
  rcases key v' with h' | h'
  · obtain ⟨u, hu⟩ := GlobalTheory.T.thetaConstants_unique_up_to_unit hL hL2 o g N' J b S s t K x v' v H' H h'
    exact ⟨(u⁻¹ : Kˣ), (u⁻¹).ne_zero, fun a => by rw [hu, Units.inv_mul_cancel_left]⟩
  · exact ⟨1, one_ne_zero, fun a => by rw [h, h', mul_zero]⟩

theorem exists_hasTh_away (hL : Out.Laws) (hL2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} {R : Type} [CommRing R] [IsDomain R] {s : Sp R ⟶ Sp o} (t : TObj g (N' ^ 2) J b s)
    (hN : Odd N') : ∃ f : R, f ≠ 0 ∧ ∃ w : Ix g (N' ^ 2) → Localization.Away f,
      t.HasTh (spMap (algebraMap R (Localization.Away f))) w := by
  let p : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  obtain ⟨R₁, _, x, w, hx, hp, H⟩ := GlobalTheory.T.exists_thetaConstants_locally_on_base hL hL2 o g N' J b _ s t hN p
  obtain ⟨_, ⟨f, rfl⟩, hf, hsub⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
    hp x.isOpenEmbedding.isOpen_range
  have hr : Set.range (spMap (algebraMap R (Localization.Away f))) ⊆ Set.range x := by
    refine subset_trans (le_of_eq ?_) hsub
    exact PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  let y := IsOpenImmersion.lift x (spMap (algebraMap R (Localization.Away f))) hr
  have hy : spMap (Spec.preimage y).hom ≫ x = spMap (algebraMap R (Localization.Away f)) := by
    rw [← IsOpenImmersion.lift_fac x (spMap (algebraMap R (Localization.Away f))) hr]
    congr 1
    exact Spec.map_preimage y
  refine ⟨f, fun h => hf (by subst h; exact Ideal.zero_mem _), fun a => (Spec.preimage y).hom (w a), ?_⟩
  rw [← hy]
  exact GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ s t R₁ _ _ x w H

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spread_hasTh (hL : Out.Laws) (hL2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {s : Sp R ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) (v : Ix g (N' ^ 2) → R)
    (H : t.HasTh (spMap (algebraMap R K)) (fun a => algebraMap R K (v a))) :
    ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      t.HasTh (spMap φ) (fun a => φ (v a)) := by
  obtain ⟨f, hf, w, Hw⟩ := exists_hasTh_away hL hL2 t H.1
  have pull : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (hu : IsUnit (φ f)),
      t.HasTh (spMap φ) (fun a => IsLocalization.Away.lift f hu (w a)) := fun R' _ φ hu => by
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ s t _ R' (IsLocalization.Away.lift f hu) _ w Hw
    rwa [spMap_comp, IsLocalization.Away.lift_comp] at this
  have inj := IsFractionRing.injective R K
  have hK : IsUnit (algebraMap R K f) := ((map_ne_zero_iff _ inj).2 hf).isUnit
  obtain ⟨c, hc, e⟩ := exists_eq_mul_of_field hL hL2 (pull K _ hK) H
  obtain ⟨a, a', ha', rfl⟩ := IsFractionRing.div_surjective (A := R) c
  have ha0' : a' ≠ 0 := nonZeroDivisors.ne_zero ha'
  have ha0 : a ≠ 0 := fun h => hc (by rw [h, map_zero, zero_div])
  have linj : Function.Injective (IsLocalization.Away.lift (S := Localization.Away f) f hK) := by
    unfold IsLocalization.Away.lift
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      rw [IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hf) h]
    · intro h
      rw [inj h]
  have e' : ∀ i, algebraMap R (Localization.Away f) (a' * v i) = algebraMap R _ a * w i := fun i => by
    apply linj
    have := e i
    beta_reduce at this
    rw [IsLocalization.Away.lift_eq, map_mul (IsLocalization.Away.lift f hK), IsLocalization.Away.lift_eq, map_mul, this, ← _root_.mul_assoc,
      mul_div_cancel₀ _ ((map_ne_zero_iff _ inj).2 ha0')]
  refine ⟨f * (a * a'), mul_ne_zero hf (mul_ne_zero ha0 ha0'), fun R' _ φ hu => ?_⟩
  rw [map_mul, map_mul] at hu
  have u₁ := isUnit_of_mul_isUnit_left hu
  have u₂ := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right hu)
  obtain ⟨u₃, hu₃⟩ := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hu)
  refine hasTh_unit_mul ((u₃⁻¹ : R'ˣ) * φ a) ((u₃⁻¹).isUnit.mul u₂) (fun i => ?_) (pull R' φ u₁)
  have := congrArg (IsLocalization.Away.lift f u₁) (e' i)
  rw [map_mul (IsLocalization.Away.lift f u₁), IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq, map_mul,
    ← hu₃] at this
  beta_reduce
  rw [_root_.mul_assoc, ← this, Units.inv_mul_cancel_left]

theorem range_spMap_fractionRing (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :
    Set.range (spMap (algebraMap R K)) = {genericPoint (Sp R)} := by
  have e : ∀ q : Sp K, spMap (algebraMap R K) q = genericPoint (Sp R) := fun q => by
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap R K) q.asIdeal = ⊥
    rw [(Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨(default : PrimeSpectrum K), e _⟩, ?_⟩
  rintro _ ⟨q, rfl⟩
  exact e q

theorem exists_ne_zero_hasTh_shape_prim : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) Mat κ (w w' : J) (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (s : Sp R ⟶ Sp o) (s' : Sp K ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s) (t : TObj g (N' ^ 2) J b s') (v : Ix g (N' ^ 2) → R), TMap t t' (spMap (algebraMap R K)) → t.HasTh (𝟙 _) (fun a => algebraMap R K (v a)) → t.Shape Mat κ → t.Prim w w' → ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (s'' : Sp R' ⟶ Sp o) (t'' : TObj g (N' ^ 2) J b s''), IsUnit (φ f) → TMap t'' t' (spMap φ) → t''.HasTh (𝟙 _) (fun a => φ (v a)) ∧ t''.Shape Mat κ ∧ t''.Prim w w' := by
  intro hL hL2 o _ g N' J b Mat κ w w' R K _ _ _ _ _ _ s s' t' t v hm hT hS hP
  have hS' : t'.Shape Mat κ :=
    GlobalTheory.T.thetaLevelShape_of_generic_point hL hL2 o g _ J b Mat κ _ s t' K _ s' t (range_spMap_fractionRing R K) hm hS
  have hT' := (GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ s t' _ s' t _ K _ _ hm).1 hT
  rw [Category.id_comp] at hT'
  obtain ⟨f₁, hf₁, H₁⟩ := spread_hasTh hL hL2 R K t' v hT'
  obtain ⟨f₂, hf₂, H₂⟩ := spread_prim R K t' t hm hP
  refine ⟨f₁ * f₂, mul_ne_zero hf₁ hf₂, fun R' _ φ s'' t'' hu hm' => ?_⟩
  rw [map_mul] at hu
  refine ⟨(GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ s t' _ s'' t'' _ R' _ _ hm').2 ?_,
    (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w w' _ _ s s'' _ t' t'' hm').1 hS',
    H₂ R' φ s'' t'' (isUnit_of_mul_isUnit_right hu) hm'⟩
  rw [Category.id_comp]
  exact H₁ R' φ (isUnit_of_mul_isUnit_left hu)

end GlobalTheory.GenericSpread

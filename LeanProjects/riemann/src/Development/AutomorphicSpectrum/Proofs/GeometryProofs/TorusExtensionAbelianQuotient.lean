import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KTrivOfLamEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGroupQuotientPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsStalkHom
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PicardClassTrivialBySeesaw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CechPic
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.AbB

open GlobalTheory GlobalTheory.UU GlobalTheory.UU.PackageDescent GlobalTheory.BiextTriv GlobalTheory.GeneratorLaw GlobalTheory.TorusUnit GlobalTheory.CompanionTheory.TorusPic

attribute [local instance] Over.cartesianMonoidalCategory

theorem pic_inj_field : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (T : TorusExtension G) (Y : Over (Sp k)), Smooth Y.hom → GeometricallyConnected Y.hom → ∀ (y₀ : 𝟙_ (Over (Sp k)) ⟶ Y) (c : Pic (T.B ⊗ Y).left), pull (lift (fst G Y ≫ T.q) (snd G Y)).left c = 0 → pull (lift (𝟙 T.B) (toUnit T.B ≫ y₀)).left c = 0 → c = 0 := by
  intro k _ G _ _ hG T Y hYs hYc y₀ c h₁ h₂
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  letI := T.addCommGroup
  letI := T.grpB
  have := T.free
  have := T.q_hom
  have := T.i_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have := hG.smooth
  have := hG.geomConnected
  have hsm : Smooth (G ⊗ Y).hom := by
    rw [Over.tensorObj_hom, pullback.condition]
    infer_instance
  have hgc : GeometricallyConnected (G ⊗ Y).hom := by
    rw [Over.tensorObj_hom, pullback.condition]
    exact GeometricallyConnected.comp _ _
  have : ConnectedSpace (G ⊗ Y).left :=
    GeometricallyConnected.connectedSpace (G ⊗ Y).hom (G ⊗ Y).hom.isOpenMap
  have : IsReduced (G ⊗ Y).left := isReduced_of_smooth (G ⊗ Y).hom
  have eπ : proj T.q Y = T.q ⊗ₘ 𝟙 Y := by ext <;> simp
  have hid₁ : Flat (𝟙 Y : Y ⟶ Y).left := by rw [Over.id_left]; infer_instance
  have hid₂ : Surjective (𝟙 Y : Y ⟶ Y).left := by rw [Over.id_left]; infer_instance
  have hid₃ : QuasiCompact (𝟙 Y : Y ⟶ Y).left := by rw [Over.id_left]; infer_instance
  have : Flat (proj T.q Y).left := eπ ▸ CosetQuotient.flat_tensorHom T.q (𝟙 Y)
  have : Surjective (proj T.q Y).left := eπ ▸ CosetQuotient.surjective_tensorHom T.q (𝟙 Y)
  have : QuasiCompact (proj T.q Y).left := eπ ▸ CosetQuotient.quasiCompact_tensorHom T.q (𝟙 Y)
  have hiq : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) T.X) (g : Z ⟶ G), ((t ≫ T.i) * g) ≫ T.q = g ≫ T.q := by
    intro Z t g
    rw [MonObj.mul_comp, Category.assoc, T.isKernel.w, ← Category.assoc,
      toUnit_unique (t ≫ toUnit _) (toUnit Z), ← Hom.one_def, _root_.one_mul]
  have ker : ∀ {Z : Over (Sp k)} (g g' : Z ⟶ G), g ≫ T.q = g' ≫ T.q →
      ∃ t : Z ⟶ splitTorus (Sp k) T.X, g = (t ≫ T.i) * g' := by
    intro Z g g' e
    have h : (g * g'⁻¹) ≫ T.q = toUnit Z ≫ η[T.B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]
      rfl
    exact ⟨T.isKernel.lift _ _ h, by rw [T.isKernel.lift_fst, inv_mul_cancel_right]⟩
  obtain ⟨u, hu⟩ := (cls_eq_zero_iff (pull_isLB hN ((proj T.q Y).left ≫ 𝟙 _))).1 (by
    rw [cls_pull hN, Category.comp_id]; exact h₁)
  obtain ⟨s, hs⟩ := (cls_eq_zero_iff (pull_isLB hN (lift (𝟙 T.B) (toUnit T.B ≫ y₀)).left)).1 (by
    rw [cls_pull hN]; exact h₂)
  obtain ⟨χ, hw⟩ := exists_weight T.i ((proj T.q Y).left ≫ 𝟙 _) (by
    rw [Category.comp_id, ← Over.comp_left, ← Over.comp_left]
    congr 1
    have e₁ : snd (splitTorus (Sp k) T.X) (G ⊗ Y) ≫ proj T.q Y =
        lift ((snd _ _ ≫ fst G Y) ≫ T.q) (snd _ _ ≫ snd G Y) := by
      rw [proj, comp_lift, Category.assoc]
    rw [act, lift_proj, e₁, hiq]) hN u hu
  obtain ⟨f, hf⟩ := exists_unit_weight T.i T.q hiq ((proj T.q Y).left ≫ 𝟙 _)
    (lift (𝟙 T.B) (toUnit T.B ≫ y₀)).left y₀ (by
      rw [Category.comp_id, ← Over.comp_left, ← Over.comp_left, TorusPic.sec, lift_proj]
      simp [comp_lift, toUnit_unique (T.q ≫ toUnit T.B) (toUnit G)]) hN u hu s hs χ hw
  obtain ⟨t, ht⟩ := exists_gen_of_weight T.i T.q ker hN u hu χ hw f hf
  have h := (cls_eq_zero_iff (pull_isLB hN (𝟙 _))).2 ⟨t, ht⟩
  rwa [cls_pull hN, pull_id] at h

theorem exists_desc {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] (T : TorusExtension G)
    {Y : Over (Sp k)} [GrpObj Y] (f : G ⟶ Y) [IsMonHom f] (hf : T.i ≫ f = 1) :
    ∃ f' : T.B ⟶ Y, T.q ≫ f' = f := by
  letI := T.grpB
  have := T.q_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have : EffectiveEpi T.q := GlobalTheory.CosetQuotient.effectiveEpi_of_left T.q
  refine ⟨EffectiveEpi.desc T.q f fun {Z} g₁ g₂ e => ?_, EffectiveEpi.fac _ _ _⟩
  have h : (g₁ * g₂⁻¹) ≫ T.q = toUnit Z ≫ η[T.B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]
    rfl
  have h₁ : T.isKernel.lift _ _ h ≫ T.i = g₁ * g₂⁻¹ := T.isKernel.lift_fst _ _ h
  have h₂ : g₁ = (T.isKernel.lift _ _ h ≫ T.i) * g₂ := by rw [h₁, inv_mul_cancel_right]
  rw [h₂, MonObj.mul_comp, Category.assoc, hf, MonObj.comp_one, _root_.one_mul]

theorem i_comp_eq_one {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] (T : TorusExtension G)
    {B : Over (Sp k)} [GrpObj B] (hB : IsAbelianScheme B) (f : G ⟶ B) [IsMonHom f] : T.i ≫ f = 1 := by
  letI := T.addCommGroup
  have := T.free
  have := T.finite
  have := T.i_hom
  have := hB.proper
  have hb := GlobalTheory.TorusConst.eq_const T.X (T.i ≫ f)
  have e : (η[splitTorus (Sp k) T.X]) ≫ T.i ≫ f = η[B] := IsMonHom.one_hom _
  rw [e] at hb
  rw [hb]
  rfl

theorem exists_act {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] {O : Type} [CommRing O]
    (a : OAct O G) (T : TorusExtension G) :
    letI := T.grpB
    ∃ b : OAct O T.B, ∀ r, a.act r ≫ T.q = T.q ≫ b.act r := by
  letI := T.grpB
  have hB := T.isAbelian
  have := T.q_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have : EffectiveEpi T.q := GlobalTheory.CosetQuotient.effectiveEpi_of_left T.q
  have canc : ∀ {Y : Over (Sp k)} (f f' : T.B ⟶ Y), T.q ≫ f = T.q ≫ f' → f = f' := fun f f' h =>
    (cancel_epi T.q).1 h
  have hact : ∀ r, ∃ f' : T.B ⟶ T.B, T.q ≫ f' = a.act r ≫ T.q := fun r => by
    have := a.hom r
    exact exists_desc T _ (i_comp_eq_one T hB _)
  choose α hα using hact
  refine ⟨{ act := α, hom := fun r => GlobalTheory.abelianSchemeLaws_all.1.rigidity _ T.B T.B hB hB _ ?_,
            one := canc _ _ (by rw [hα, a.one, Category.id_comp, Category.comp_id]),
            mul := fun r s => canc _ _ (by
              rw [hα, a.mul, ← Category.assoc T.q, hα, Category.assoc, Category.assoc, hα]),
            add := fun r s => canc _ _ (by rw [hα, a.add, MonObj.mul_comp, MonObj.comp_mul, hα, hα]) },
    fun r => (hα r).symm⟩
  have := a.hom r
  rw [← IsMonHom.one_hom T.q, Category.assoc, hα, ← Category.assoc, IsMonHom.one_hom]

section Maps

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

theorem lift_p {A G Z : C} [MonObj A] (t t' : Z ⟶ A) (x : Z ⟶ G) :
    lift t (lift t' x) ≫ lift (fst A (A ⊗ G) * (snd A (A ⊗ G) ≫ fst A G)) (snd A (A ⊗ G) ≫ snd A G) =
      lift (t * t') x := by
  rw [comp_lift, MonObj.comp_mul]
  simp

theorem lift_r {A G Z : C} [MonObj G] (i : A ⟶ G) (t t' : Z ⟶ A) (x : Z ⟶ G) :
    lift t (lift t' x) ≫ lift (fst A (A ⊗ G)) ((snd A (A ⊗ G) ≫ fst A G ≫ i) * (snd A (A ⊗ G) ≫ snd A G)) =
      lift t ((t' ≫ i) * x) := by
  rw [comp_lift, MonObj.comp_mul]
  simp

theorem lift_act_mul {A G Z : C} [MonObj A] [MonObj G] (i : A ⟶ G) [IsMonHom i] (t t' : Z ⟶ A) (x : Z ⟶ G) :
    lift (t * t') x ≫ ((fst A G ≫ i) * snd A G) = lift t ((t' ≫ i) * x) ≫ ((fst A G ≫ i) * snd A G) := by
  simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd, MonObj.mul_comp, _root_.mul_assoc]

theorem lift_act {A G Z : C} [MonObj G] (i : A ⟶ G) (t : Z ⟶ A) (x : Z ⟶ G) :
    lift t x ≫ ((fst A G ≫ i) * snd A G) = (t ≫ i) * x := by
  simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd]

end Maps

section Coc

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Free ℤ X] {G : Over S} [GrpObj G]

theorem coc_of_normalised (i : splitTorus S X ⟶ G) [IsMonHom i] [IsIntegral (splitTorus S X ⊗ G).left]
    {N : LB G.left} (hN : N.IsLB)
    (a : LB.Gen (LB.LinComb N (K := Fin 2)
      ![((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left, (snd (splitTorus S X) G).left] ![1, -1]))
    (ha : a.IsGen)
    (hn : ∀ (Z : Over S) (y : Z ⟶ G) (z : Z.left) (J), Good N z J →
      val a (lift (1 : Z ⟶ splitTorus S X) y).left z J = 1) :
    ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (x : Z ⟶ G) (z : Z.left) (J), Good N z J →
      val a (lift (t * t') x).left z J =
        val a (lift t ((t' ≫ i) * x)).left z J * val a (lift t' x).left z J := by
  let A : Over S := splitTorus S X
  let act : A ⊗ G ⟶ G := (fst A G ≫ i) * snd A G
  let t₀ : A ⊗ (A ⊗ G) ⟶ A := fst A (A ⊗ G)
  let t₁ : A ⊗ (A ⊗ G) ⟶ A := snd A (A ⊗ G) ≫ fst A G
  let x₀ : A ⊗ (A ⊗ G) ⟶ G := snd A (A ⊗ G) ≫ snd A G
  let p : A ⊗ (A ⊗ G) ⟶ A ⊗ G := lift (t₀ * t₁) x₀
  let r : A ⊗ (A ⊗ G) ⟶ A ⊗ G := lift t₀ ((t₁ ≫ i) * x₀)
  let s : A ⊗ (A ⊗ G) ⟶ A ⊗ G := snd A (A ⊗ G)
  have ep : ∀ {Z : Over S} (t t' : Z ⟶ A) (x : Z ⟶ G), (lift t (lift t' x)).left ≫ p.left = (lift (t * t') x).left :=
    fun t t' x => by
      rw [← Over.comp_left]
      exact congrArg (·.left) (lift_p t t' x)
  have er : ∀ {Z : Over S} (t t' : Z ⟶ A) (x : Z ⟶ G),
      (lift t (lift t' x)).left ≫ r.left = (lift t ((t' ≫ i) * x)).left := fun t t' x => by
    rw [← Over.comp_left]
    exact congrArg (·.left) (lift_r i t t' x)
  have es : ∀ {Z : Over S} (t t' : Z ⟶ A) (x : Z ⟶ G), (lift t (lift t' x)).left ≫ s.left = (lift t' x).left :=
    fun t t' x => by
      rw [← Over.comp_left]
      exact congrArg (·.left) (lift_snd t (lift t' x))
  have eact₁ : p ≫ act = r ≫ act := lift_act_mul i t₀ t₁ x₀
  have eact₂ : r ≫ snd A G = s ≫ act := by
    have e : s = lift t₁ x₀ := by simp [s, t₁, x₀]
    rw [e, lift_snd]
    exact (lift_act i t₁ x₀).symm
  have eact₃ : p ≫ snd A G = s ≫ snd A G := lift_snd _ _
  have R := ((rep_val ha).pull p.left).mul (((rep_val ha).pull r.left).mul ((rep_val ha).pull s.left)).inv
  have R' := R.congr (σ' := fun _ _ _ => 1) fun V _ h => by
    simp only [Fin.prod_univ_two]
    show (h (p.left ≫ act.left) ^ (1 : ℤ) * h (p.left ≫ (snd A G).left) ^ (-1 : ℤ)) *
      (h (r.left ≫ act.left) ^ (1 : ℤ) * h (r.left ≫ (snd A G).left) ^ (-1 : ℤ) *
        (h (s.left ≫ act.left) ^ (1 : ℤ) * h (s.left ≫ (snd A G).left) ^ (-1 : ℤ)))⁻¹ = 1
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left,
      eact₁, eact₂, eact₃]
    simp
  have hsplit : ∀ {Z : Over S} (y : Z ⟶ A ⊗ G), ∃ (t' : Z ⟶ A) (x : Z ⟶ G), y = lift t' x :=
    fun y => ⟨y ≫ fst _ _, y ≫ snd _ _, by simp⟩
  obtain ⟨χ, hχ⟩ := exists_char_of_rep (S := S) (X := X) (Y := A ⊗ G) hN R' fun Z y z J hJ => by
    obtain ⟨t', x, rfl⟩ := hsplit y
    show val a ((lift 1 (lift t' x)).left ≫ p.left) z J *
      (val a ((lift 1 (lift t' x)).left ≫ r.left) z J * val a ((lift 1 (lift t' x)).left ≫ s.left) z J)⁻¹ = 1
    rw [ep, er, es, _root_.one_mul, hn _ _ z J hJ, _root_.one_mul, mul_inv_cancel]
  intro Z t t' x z J hJ
  have h₁ : val a ((lift t (lift t' x)).left ≫ p.left) z J *
      (val a ((lift t (lift t' x)).left ≫ r.left) z J * val a ((lift t (lift t' x)).left ≫ s.left) z J)⁻¹ = _ :=
    hχ Z t (lift t' x) z J hJ
  have h₂ : val a ((lift t (lift 1 x)).left ≫ p.left) z J *
      (val a ((lift t (lift 1 x)).left ≫ r.left) z J * val a ((lift t (lift 1 x)).left ≫ s.left) z J)⁻¹ = _ :=
    hχ Z t (lift 1 x) z J hJ
  rw [ep, er, es] at h₁ h₂
  rw [_root_.mul_one, MonObj.one_comp, _root_.one_mul, hn _ _ z J hJ, _root_.mul_one, mul_inv_cancel] at h₂
  rw [← h₂] at h₁
  exact mul_inv_eq_one.1 h₁

end Coc

theorem exists_bundle {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (T : TorusExtension G) (N : LB G.left) (hN : N.IsLB) :
    ∃ M : LB T.B.left, M.IsLB ∧ LBIso N (M.pull T.q.left) := by
  letI := T.addCommGroup
  letI := T.grpB
  have := T.free
  have := T.finite
  have := T.q_hom
  have := T.i_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have hB := T.isAbelian
  haveI := hB.comm
  have := hG.smooth
  have := hG.geomConnected
  have hk := T.isKernel
  have haff : IsAffineHom T.q.left := ToSplit.isAffineHom_left hk
  let Q : TQ G T.X :=
    { B := T.B, isAb := hB, q := T.q, i := T.i, q_hom := T.q_hom, i_hom := T.i_hom, q_flat := T.q_flat,
      q_surj := T.q_surjective, q_affine := haff, isKernel := hk,
      loc := fun b χ => by
        obtain ⟨V, hV, u, hu⟩ := GlobalTheory.exists_local_unit_of_weight _ T.X G T.B T.q T.i T.q_hom T.i_hom T.q_flat
          T.q_surjective T.q_quasiCompact hk haff χ b
        exact ⟨V, hV, u, hu⟩ }
  let A := splitTorus (Sp k) T.X
  obtain ⟨c₁, c₂⟩ := GroupConn.connectedSpace_group _ G
  obtain ⟨c₃, -⟩ := c₂ T.X G c₁
  have : IsIntegral G.left := isIntegral_of_smooth_field_of_connectedSpace G.hom
  have : Smooth (A ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst A.hom G.hom ≫ _))
  have : IsIntegral (A ⊗ G).left := isIntegral_of_smooth_field_of_connectedSpace (A ⊗ G).hom
  let act : A ⊗ G ⟶ G := (fst A G ≫ T.i) * snd A G
  have e₁ : unitSec T.X G ≫ act.left = 𝟙 G.left := by
    rw [unitSec, ← Over.comp_left]
    have : lift (1 : G ⟶ A) (𝟙 G) ≫ act = 𝟙 G := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, MonObj.one_comp, _root_.one_mul]
    rw [this]; rfl
  have e₂ : unitSec T.X G ≫ (snd A G).left = 𝟙 G.left := by
    rw [unitSec, ← Over.comp_left, lift_snd]; rfl
  obtain ⟨a, ha, hn⟩ := exists_normalised_gen (S := Sp k) (X := T.X) (Y := G) (L := N)
    (φ := ![act.left, (snd A G).left]) (ε := ![1, -1]) (fun U hU => by
      have : IsAffine U.1.toScheme := U.2
      have : IsIntegral U.1.toScheme := isIntegral_of_isOpenImmersion U.1.ι
      have h := (HasRingHomProperty.appTop (P := @Smooth) (U.1.ι ≫ G.hom) inferInstance)
      algebraize [(U.1.ι ≫ G.hom).appTop.hom]
      have : IsIntegrallyClosed Γ(Spec (CommRingCat.of k), ⊤) :=
        IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
      exact isIntegrallyClosed_of_smooth Γ(Spec (CommRingCat.of k), ⊤) _) hN fun V _ h => by
    rw [Fin.prod_univ_two]
    show h (unitSec T.X G ≫ act.left) ^ (1 : ℤ) * h (unitSec T.X G ≫ (snd A G).left) ^ (-1 : ℤ) = 1
    rw [e₁, e₂]
    simp
  obtain ⟨M, w, hM, hw, -⟩ := GlobalTheory.EquivDesc.main (Sp k) T.X G Q N hN a ha
    (coc_of_normalised T.i hN a ha hn)
  exact ⟨M, hM, w, hw⟩

section Vanish

variable {k : Type} [Field k]

theorem smooth_tensor {A C : Over (Sp k)} (hA : Smooth A.hom) (hC : Smooth C.hom) : Smooth (A ⊗ C).hom := by
  rw [Over.tensorObj_hom, pullback.condition]
  infer_instance

theorem geomConnected_tensor {A C : Over (Sp k)} (hA : GeometricallyConnected A.hom)
    (hC : GeometricallyConnected C.hom) : GeometricallyConnected (A ⊗ C).hom := by
  rw [Over.tensorObj_hom, pullback.condition]
  exact GeometricallyConnected.comp _ _

theorem vanish {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (T : TorusExtension G)
    (Y : Over (Sp k)) (hs : Smooth Y.hom) (hc : GeometricallyConnected Y.hom) (y₀ : 𝟙_ (Over (Sp k)) ⟶ Y)
    (F : ∀ {Z : Over (Sp k)}, (Z ⟶ T.B) → (Z ⟶ Y) → Pic Z.left)
    (nat : ∀ {Z Z' : Over (Sp k)} (h : Z' ⟶ Z) (x : Z ⟶ T.B) (y : Z ⟶ Y), pull h.left (F x y) = F (h ≫ x) (h ≫ y))
    (hq : ∀ {Z : Over (Sp k)} (u : Z ⟶ G) (y : Z ⟶ Y), F (u ≫ T.q) y = 0)
    (h1 : ∀ {Z : Over (Sp k)} (x : Z ⟶ T.B), F x (toUnit Z ≫ y₀) = 0)
    {Z : Over (Sp k)} (x : Z ⟶ T.B) (y : Z ⟶ Y) : F x y = 0 := by
  have c : F (fst T.B Y) (snd T.B Y) = 0 := by
    refine pic_inj_field k G hG T Y hs hc y₀ _ ?_ ?_
    · rw [nat, lift_fst, lift_snd]
      exact hq _ _
    · rw [nat, lift_fst, lift_snd]
      exact h1 _
  have h := congrArg (pull (lift x y).left) c
  rwa [nat, map_zero, lift_fst, lift_snd] at h

end Vanish

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

set_option maxHeartbeats 600000 in

theorem theta_quot {k : Type} [Field k] {H : Host E} (tK : SAB H (Sp k)) (T : TorusExtension tK.G)
    (M : LB T.B.left) (hM : M.IsLB) (hbun : LBIso tK.PP.L (M.pull T.q.left)) :
    letI := T.grpB
    ∃ t : LB.Gen (Theta T.B M), t.IsGen := by
  letI := T.grpB
  have hB := T.isAbelian
  haveI := hB.comm
  have := T.q_hom
  have hL := tK.PP.isLB
  have hGs := tK.semi
  set l := cls tK.PP.L hL with hl
  set m := cls M hM with hm
  have hqm : pull T.q.left m = l := ((cls_eq_iff hL (pull_isLB hM _)).2 hbun).symm
  have lamq : ∀ {Z : Over (Sp k)} (u v : Z ⟶ tK.G), lam m (u ≫ T.q) (v ≫ T.q) = lam l u v := fun u v => by
    rw [← lam_pull, hqm]
  have h0 : lam l (fst tK.G _ * (snd tK.G _ ≫ fst tK.G tK.G)) (snd tK.G (tK.G ⊗ tK.G) ≫ snd tK.G tK.G) -
      lam l (fst tK.G _) (snd tK.G (tK.G ⊗ tK.G) ≫ snd tK.G tK.G) -
      lam l (snd tK.G (tK.G ⊗ tK.G) ≫ fst tK.G tK.G) (snd tK.G (tK.G ⊗ tK.G) ≫ snd tK.G tK.G) = 0 :=
    (cls_cube_three hL _ _ _ (LB.isLB_linComb hL _ _)).symm.trans
      ((cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨tK.cub.t, tK.cub.isGen⟩)
  have cubG : ∀ {Z : Over (Sp k)} (u v w : Z ⟶ tK.G), lam l (u * v) w - lam l u w - lam l v w = 0 := by
    intro Z u v w
    have h := congrArg (pull (lift u (lift v w)).left) h0
    simpa only [map_sub, map_zero, pull_lam, MonObj.comp_mul, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h
  let D : ∀ {Z : Over (Sp k)}, (Z ⟶ T.B) → (Z ⟶ T.B) → (Z ⟶ T.B) → Pic Z.left := fun x y z =>
    lam m (x * y) z - lam m x z - lam m y z
  have Dpull : ∀ {Z Z' : Over (Sp k)} (h : Z' ⟶ Z) (x y z : Z ⟶ T.B),
      pull h.left (D x y z) = D (h ≫ x) (h ≫ y) (h ≫ z) := by
    intro Z Z' h x y z
    simp only [D, map_sub, pull_lam, MonObj.comp_mul]
  have Dq : ∀ {Z : Over (Sp k)} (u v w : Z ⟶ tK.G), D (u ≫ T.q) (v ≫ T.q) (w ≫ T.q) = 0 := by
    intro Z u v w
    simp only [D]
    rw [← MonObj.mul_comp, lamq, lamq, lamq]
    exact cubG u v w
  have D1l : ∀ {Z : Over (Sp k)} (y z : Z ⟶ T.B), D 1 y z = 0 := by
    intro Z y z
    simp only [D]
    rw [_root_.one_mul, lam_one_left]
    abel
  have D1m : ∀ {Z : Over (Sp k)} (x z : Z ⟶ T.B), D x 1 z = 0 := by
    intro Z x z
    simp only [D]
    rw [_root_.mul_one, lam_one_left]
    abel
  have D1r : ∀ {Z : Over (Sp k)} (x y : Z ⟶ T.B), D x y 1 = 0 := by
    intro Z x y
    simp only [D]
    rw [lam_one_right, lam_one_right, lam_one_right]
    abel
  have sG := hGs.smooth
  have gG := hGs.geomConnected
  have sB := hB.smooth
  have gB := hB.geomConnected
  have one_q : ∀ {Z : Over (Sp k)}, (1 : Z ⟶ tK.G) ≫ T.q = 1 := fun {Z} => MonObj.one_comp _

  have s₁ : ∀ {Z : Over (Sp k)} (x : Z ⟶ T.B) (v w : Z ⟶ tK.G), D x (v ≫ T.q) (w ≫ T.q) = 0 := by
    intro Z x v w
    have := vanish hGs T (tK.G ⊗ tK.G) (smooth_tensor sG sG) (geomConnected_tensor gG gG) (lift η[tK.G] η[tK.G])
      (fun {Z} x y => D x (y ≫ fst _ _ ≫ T.q) (y ≫ snd _ _ ≫ T.q))
      (fun h x y => by
        rw [Dpull]
        simp only [Category.assoc])
      (fun u y => by
        simpa only [Category.assoc] using Dq u (y ≫ fst _ _) (y ≫ snd _ _))
      (fun {Z} x => by
        have e₁ : (toUnit Z ≫ lift η[tK.G] η[tK.G]) ≫ fst tK.G tK.G ≫ T.q = 1 := by
          simp only [Category.assoc, lift_fst_assoc]
          rw [IsMonHom.one_hom]
          rfl
        have e₂ : (toUnit Z ≫ lift η[tK.G] η[tK.G]) ≫ snd tK.G tK.G ≫ T.q = 1 := by
          simp only [Category.assoc, lift_snd_assoc]
          rw [IsMonHom.one_hom]
          rfl
        show D x _ _ = 0
        rw [e₂]
        exact D1r _ _) x (lift v w)
    simpa only [lift_fst_assoc, lift_snd_assoc] using this

  have s₂ : ∀ {Z : Over (Sp k)} (x y : Z ⟶ T.B) (w : Z ⟶ tK.G), D y x (w ≫ T.q) = 0 := by
    intro Z x y w
    have := vanish hGs T (T.B ⊗ tK.G) (smooth_tensor sB sG) (geomConnected_tensor gB gG) (lift η[T.B] η[tK.G])
      (fun {Z} x y => D (y ≫ fst _ _) x (y ≫ snd _ _ ≫ T.q))
      (fun h x y => by
        rw [Dpull]
        simp only [Category.assoc])
      (fun u y => by
        have h := s₁ (y ≫ fst T.B tK.G) u (y ≫ snd T.B tK.G)
        rwa [Category.assoc] at h)
      (fun {Z} x => by
        have e₁ : (toUnit Z ≫ lift η[T.B] η[tK.G]) ≫ snd T.B tK.G ≫ T.q = 1 := by
          simp only [Category.assoc, lift_snd_assoc]
          rw [IsMonHom.one_hom]
          rfl
        show D _ x _ = 0
        rw [e₁]
        exact D1r _ _) x (lift y w)
    simpa only [lift_fst, lift_snd_assoc] using this

  have s₃ : ∀ {Z : Over (Sp k)} (x y z : Z ⟶ T.B), D x y z = 0 := by
    intro Z x y z
    have := vanish hGs T (T.B ⊗ T.B) (smooth_tensor sB sB) (geomConnected_tensor gB gB) (lift η[T.B] η[T.B])
      (fun {Z} z y => D (y ≫ fst _ _) (y ≫ snd _ _) z)
      (fun h x y => by
        rw [Dpull]
        simp only [Category.assoc])
      (fun u y => s₂ (y ≫ snd T.B T.B) (y ≫ fst T.B T.B) u)
      (fun {Z} x => by
        have e₁ : (toUnit Z ≫ lift η[T.B] η[T.B]) ≫ fst T.B T.B = 1 := by
          simp only [Category.assoc, lift_fst]
          rfl
        show D _ _ x = 0
        rw [e₁]
        exact D1l _ _) z (lift x y)
    simpa only [lift_fst, lift_snd] using this
  have hT : (Theta T.B M).IsLB := LB.isLB_linComb hM _ _
  exact (cls_eq_zero_iff hT).1 ((cls_cube_three hM _ _ _ hT).trans (s₃ _ _ _))

theorem adj_quot {k : Type} [Field k] {H : Host E} (tK : SAB H (Sp k)) (T : TorusExtension tK.G)
    (M : LB T.B.left) (hM : M.IsLB) (hbun : LBIso tK.PP.L (M.pull T.q.left)) :
    letI := T.grpB
    ∀ (act : OAct (𝓞 E) T.B), (∀ r, tK.act.act r ≫ T.q = T.q ≫ act.act r) → ∀ a,
      LBIso (cubeLB T.B ![fst T.B T.B ≫ act.act a, snd T.B T.B] M)
        (cubeLB T.B ![fst T.B T.B, snd T.B T.B ≫ act.act (H.bar a)] M) := by
  letI := T.grpB
  have hB := T.isAbelian
  haveI := hB.comm
  have := T.q_hom
  intro act hact a
  have := act.hom a
  have := act.hom (H.bar a)
  have hL := tK.PP.isLB
  set l := cls tK.PP.L hL with hl
  set m := cls M hM with hm
  have hqm : pull T.q.left m = l := ((cls_eq_iff hL (pull_isLB hM _)).2 hbun).symm
  have lamq : ∀ {Z : Over (Sp k)} (u v : Z ⟶ tK.G), lam m (u ≫ T.q) (v ≫ T.q) = lam l u v := fun u v => by
    rw [← lam_pull, hqm]
  have adjG : ∀ {Z : Over (Sp k)} (u v : Z ⟶ tK.G),
      lam l (u ≫ tK.act.act a) v = lam l u (v ≫ tK.act.act (H.bar a)) := by
    intro Z u v
    have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (tK.adj a)
    have h' := congrArg (pull (lift u v).left)
      ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
  let D : ∀ {Z : Over (Sp k)}, (Z ⟶ T.B) → (Z ⟶ T.B) → Pic Z.left := fun x y =>
    lam m (x ≫ act.act a) y - lam m x (y ≫ act.act (H.bar a))
  have Dpull : ∀ {Z Z' : Over (Sp k)} (h : Z' ⟶ Z) (x y : Z ⟶ T.B), pull h.left (D x y) = D (h ≫ x) (h ≫ y) := by
    intro Z Z' h x y
    simp only [D, map_sub, pull_lam, Category.assoc]
  have Dq : ∀ {Z : Over (Sp k)} (u v : Z ⟶ tK.G), D (u ≫ T.q) (v ≫ T.q) = 0 := by
    intro Z u v
    have e₁ : (u ≫ T.q) ≫ act.act a = (u ≫ tK.act.act a) ≫ T.q := by
      rw [Category.assoc, Category.assoc, hact]
    have e₂ : (v ≫ T.q) ≫ act.act (H.bar a) = (v ≫ tK.act.act (H.bar a)) ≫ T.q := by
      rw [Category.assoc, Category.assoc, hact]
    simp only [D]
    rw [e₁, e₂, lamq, lamq, adjG, sub_self]
  have D1l : ∀ {Z : Over (Sp k)} (y : Z ⟶ T.B), D 1 y = 0 := by
    intro Z y
    simp only [D]
    rw [MonObj.one_comp, lam_one_left, lam_one_left, sub_self]
  have D1r : ∀ {Z : Over (Sp k)} (x : Z ⟶ T.B), D x 1 = 0 := by
    intro Z x
    simp only [D]
    rw [MonObj.one_comp, lam_one_right, lam_one_right, sub_self]
  have hGs := tK.semi
  have one_q : ∀ {Z : Over (Sp k)}, (1 : Z ⟶ tK.G) ≫ T.q = 1 := fun {Z} => MonObj.one_comp _
  have c₁ : D (fst T.B tK.G) (snd T.B tK.G ≫ T.q) = 0 := by
    refine pic_inj_field k tK.G hGs T tK.G hGs.smooth hGs.geomConnected η[tK.G] _ ?_ ?_
    · have e₁ : lift (fst tK.G tK.G ≫ T.q) (snd tK.G tK.G) ≫ fst T.B tK.G = fst tK.G tK.G ≫ T.q := lift_fst _ _
      have e₂ : lift (fst tK.G tK.G ≫ T.q) (snd tK.G tK.G) ≫ snd T.B tK.G ≫ T.q = snd tK.G tK.G ≫ T.q := by
        rw [← Category.assoc, lift_snd]
      rw [Dpull, e₁, e₂]
      exact Dq _ _
    · have e₁ : lift (𝟙 T.B) (toUnit T.B ≫ η[tK.G]) ≫ fst T.B tK.G = 𝟙 T.B := lift_fst _ _
      have e₂ : lift (𝟙 T.B) (toUnit T.B ≫ η[tK.G]) ≫ snd T.B tK.G ≫ T.q = 1 := by
        rw [← Category.assoc, lift_snd]
        exact one_q
      rw [Dpull, e₁, e₂]
      exact D1r _
  have Dr : ∀ {Z : Over (Sp k)} (x : Z ⟶ T.B) (v : Z ⟶ tK.G), D x (v ≫ T.q) = 0 := by
    intro Z x v
    have h := congrArg (pull (lift x v).left) c₁
    have e₂ : lift x v ≫ snd T.B tK.G ≫ T.q = v ≫ T.q := by rw [← Category.assoc, lift_snd]
    rw [Dpull, map_zero, lift_fst, e₂] at h
    exact h
  have c₂ : D (snd T.B T.B) (fst T.B T.B) = 0 := by
    refine pic_inj_field k tK.G hGs T T.B hB.smooth hB.geomConnected η[T.B] _ ?_ ?_
    · have e₁ : lift (fst tK.G T.B ≫ T.q) (snd tK.G T.B) ≫ fst T.B T.B = fst tK.G T.B ≫ T.q := lift_fst _ _
      have e₂ : lift (fst tK.G T.B ≫ T.q) (snd tK.G T.B) ≫ snd T.B T.B = snd tK.G T.B := lift_snd _ _
      rw [Dpull, e₁, e₂]
      exact Dr _ _
    · have e₁ : lift (𝟙 T.B) (toUnit T.B ≫ η[T.B]) ≫ fst T.B T.B = 𝟙 T.B := lift_fst _ _
      have e₂ : lift (𝟙 T.B) (toUnit T.B ≫ η[T.B]) ≫ snd T.B T.B = 1 := lift_snd _ _
      rw [Dpull, e₁, e₂]
      exact D1l _
  have c₃ : D (fst T.B T.B) (snd T.B T.B) = 0 := by
    have h := congrArg (pull (lift (snd T.B T.B) (fst T.B T.B)).left) c₂
    rw [Dpull, map_zero, lift_fst, lift_snd] at h
    exact h
  have h₁ : (cubeLB T.B ![fst T.B T.B ≫ act.act a, snd T.B T.B] M).IsLB := LB.isLB_linComb hM _ _
  have h₂ : (cubeLB T.B ![fst T.B T.B, snd T.B T.B ≫ act.act (H.bar a)] M).IsLB := LB.isLB_linComb hM _ _
  refine (cls_eq_iff h₁ h₂).1 ?_
  rw [cls_cube_two hM, cls_cube_two hM]
  exact sub_eq_zero.1 c₃

theorem exists_triple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [CharZero L] (tK : SAB H (Sp L)) (τ : TorusExtension tK.G), ∃ (tB : SAB H (Sp L)) (e : τ.B ≅ tB.G), (letI := τ.grpB; IsMonHom e.hom) ∧ (∀ a, tK.act.act a ≫ τ.q ≫ e.hom = τ.q ≫ e.hom ≫ tB.act.act a) ∧ LBIso tK.PP.L (tB.PP.L.pull (τ.q ≫ e.hom).left) := by
  intro E _ _ _ H L _ _ tK T
  letI := T.grpB
  have hB := T.isAbelian
  haveI := hB.comm
  have hq := T.q_hom
  have hL : tK.PP.L.IsLB := tK.PP.isLB
  obtain ⟨M, hM, hbun⟩ := exists_bundle tK.semi T tK.PP.L hL
  have hqL := pull_isLB hM T.q.left
  obtain ⟨act, hact⟩ := exists_act tK.act T
  have hadj := adj_quot tK T M hM hbun act hact
  obtain ⟨PP, cub, hsym, hPP, -, hprim, hadjP⟩ := GlobalTheory.PrimNorm.exists_primitive_normalisation GlobalTheory.globalFns_holds
    E H _ T.B act M hB hM (theta_quot tK T M hM hbun) hadj
  have hP' := PP.isLB
  have hqm : pull T.q.left (cls M hM) = cls tK.PP.L hL := ((cls_eq_iff hL hqL).2 hbun).symm
  have hpull : pull T.q.left (cls PP.L hP') = cls tK.PP.L hL := by
    have h := (cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 tK.prim
    have h' := (cls_eq_iff hP' (LB.isLB_linComb hM _ _)).2 hPP
    have e : cls tK.PP.L hL = lam (cls tK.PP.L hL) (𝟙 _) (tK.act.act H.w0) := h.trans (cls_cube_two hL _ _ _)
    have e' : cls PP.L hP' = lam (cls M hM) (𝟙 _) (act.act H.w0) := h'.trans (cls_cube_two hM _ _ _)
    rw [e', pull_lam, ← hact, Category.comp_id, ← Category.id_comp T.q, ← Category.assoc, Category.comp_id,
      ← lam_pull, hqm, ← e]
  have hfin : LBIso tK.PP.L (PP.L.pull T.q.left) := by
    rw [← cls_eq_iff hL (pull_isLB hP' _), cls_pull hP', hpull]
  refine ⟨⟨T.B, GlobalTheory.isSemiAbelian_of_isAbelianScheme T.B hB, act, PP, cub, hsym, hadjP, hprim⟩, Iso.refl _,
    ?_, fun a => ?_, ?_⟩
  · exact inferInstanceAs (IsMonHom (𝟙 T.B))
  · simpa using hact a
  · simpa using hfin

end GlobalTheory.CompanionTheory.Ar.AbB

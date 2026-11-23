import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TranslationBySection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsPullbackOfFpqcLeft
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolAVIsoExtendsOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.ArcDataDescent

theorem exists_desc_of_points {K L : Type} [Field K] [CharZero K] [Field L] (gam : K →+* L) {X X' Z S : Scheme.{0}}
    {p : X ⟶ Sp K} {p' : X' ⟶ Sp L} {π : X' ⟶ X} (h : IsPullback π p' p (spMap gam)) [IsReduced X'] (z : Z ⟶ S)
    [IsSeparated z] (φ : X' ⟶ Z) (s : X ⟶ S) (hs : φ ≫ z = π ≫ s)
    (H : ∀ (F : Type) [Field F] [IsAlgClosed F] (x₁ x₂ : Sp F ⟶ X'), x₁ ≫ π = x₂ ≫ π → x₁ ≫ φ = x₂ ≫ φ) :
    ∃ ψ : X ⟶ Z, π ≫ ψ = φ := by
  letI := gam.toAlgebra
  have f₁ : Flat (spMap gam) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField K) gam
  have f₂ : Surjective (spMap gam) := ⟨fun y => ⟨(default : PrimeSpectrum L), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have : Flat π := MorphismProperty.of_isPullback h.flip f₁
  have : Surjective π := MorphismProperty.of_isPullback h.flip f₂
  have : QuasiCompact π := MorphismProperty.of_isPullback h.flip inferInstance
  have gr : GeometricallyReduced (π ≫ p) := ReducedSubgroup.geometricallyReduced_of_perfectField _
  have hp : IsPullback (pullback.fst π π) (pullback.snd π π ≫ p') (π ≫ p) (spMap gam) :=
    (IsPullback.of_hasPullback π π).paste_vert h
  have : IsReduced (pullback π π) := GeometricallyReduced.geometrically_isReduced _ _ _ hp
  have e : pullback.fst π π ≫ φ = pullback.snd π π ≫ φ := by
    refine ext_of_fromSpecResidueField_eq _ _ z Set.univ dense_univ (fun x _ => ?_) ?_
    · let k := (pullback π π).residueField x
      let F := AlgebraicClosure k
      have : Epi (spMap (algebraMap k F)) := by
        have f₁ : Flat (spMap (algebraMap k F)) := by
          rw [HasRingHomProperty.Spec_iff (P := @Flat)]
          exact RingHom.Flat.of_isField (Field.toIsField k) _
        have f₂ : Surjective (spMap (algebraMap k F)) :=
          ⟨fun y => ⟨(default : PrimeSpectrum F), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
        exact Flat.epi_of_flat_of_surjective _
      let j : Sp k ⟶ pullback π π := (pullback π π).fromSpecResidueField x
      show j ≫ _ = j ≫ _
      rw [← cancel_epi (spMap (algebraMap k F))]
      simpa only [Category.assoc] using H F (spMap (algebraMap k F) ≫ j ≫ pullback.fst π π)
        (spMap (algebraMap k F) ≫ j ≫ pullback.snd π π) (by simp only [Category.assoc, pullback.condition])
    · rw [Category.assoc, Category.assoc, hs, pullback.condition_assoc]
  exact ⟨EffectiveEpi.desc π φ (fun g₁ g₂ hg => by
    rw [← pullback.lift_fst g₁ g₂ hg, Category.assoc, e, ← Category.assoc, pullback.lift_snd]), EffectiveEpi.fac _ _ _⟩

theorem ext_of_injective {R V : Type} [CommRing R] [IsDomain R] [CommRing V] {g : R →+* V} (hg : Function.Injective g)
    {X X' Z S : Scheme.{0}} {p : X ⟶ Sp R} {p' : X' ⟶ Sp V} {π : X' ⟶ X} (h : IsPullback π p' p (spMap g)) [Flat p]
    (z : Z ⟶ S) [IsSeparated z] {a b : X ⟶ Z} (hz : a ≫ z = b ≫ z) (H : π ≫ a = π ≫ b) : a = b := by
  have := SS.SectionTranslation.schDom_spec_map g hg
  have : IsSchemeTheoreticallyDominant π := IsSchemeTheoreticallyDominant.of_isPullback h.flip
  exact SS.SectionTranslation.ext_of_schDom z hz π H

def chartQuot {X Y : Scheme.{0}} (A B : LB X) (h : Y ⟶ X) :
    ChartPull ((LB.div B A).pull h) (LB.div (B.pull h) (A.pull h)) (𝟙 Y) where
  idx J := (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
  le J y hy := ⟨mem_pull.2 (mem_pull.1 hy).1, mem_pull.2 (mem_pull.1 hy).2⟩
  g y J J' hj hj' := by
    have a := mem_pull.1 hj
    have b := mem_pull.1 hj'
    refine (gm_pull_g _ h (𝟙 Y) y J J' hj hj').trans ((gm_div A B (𝟙 Y ≫ h) y _ _ ⟨a, b⟩).trans (Eq.symm ?_))
    refine (gm_div (A.pull h) (B.pull h) (𝟙 Y) y (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2)
      ⟨⟨mem_pull.2 a.1, mem_pull.2 a.2⟩, ⟨mem_pull.2 b.1, mem_pull.2 b.2⟩⟩).trans ?_
    exact congrArg₂ (fun u v => u * v⁻¹) (gm_pull_g B h (𝟙 Y) y _ _ (mem_pull.2 a.1) (mem_pull.2 b.1))
      (gm_pull_g A h (𝟙 Y) y _ _ (mem_pull.2 a.2) (mem_pull.2 b.2))

theorem lbIso_pull {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {φ : Y ⟶ X} (h : LBIso M (L.pull φ)) (r : Z ⟶ Y)
    {ψ : Z ⟶ X} (e : ψ = r ≫ φ) : LBIso (M.pull r) (L.pull ψ) :=
  h.chartPull (Geo.Tor.chartPullPull M r r rfl) (chartPullSame L (fun _ => ψ) (fun _ => φ) _ r fun _ => e)

theorem lbIso_pull_pull {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (φ : Y ⟶ X) (r : Z ⟶ Y)
    {ψ : Z ⟶ X} (e : ψ = r ≫ φ) : LBIso ((L.pull φ).pull r) (L.pull ψ) := by
  have h : LBIso (L.pull φ) (L.pull φ) := by
    obtain ⟨i, hi⟩ : LBIso L L := by
      refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
      refine (gm_res (𝟙 X) y _ hy _).trans (Eq.symm ?_)
      refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div L L (𝟙 X) y p q hy) (gm_res (𝟙 X) y _ hy _))).trans ?_
      have e := (gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2).trans (gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2).symm
      exact (mul_right_comm _ _ _).trans (mul_inv_eq_of_eq_mul e)
    exact LBIso.chartPull (Geo.Tor.chartPullPull L φ φ rfl) (Geo.Tor.chartPullPull L φ φ rfl) ⟨i, hi⟩
  exact lbIso_pull h r e

theorem exists_polPull (hP : PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (P : PolAV S) :
    ∃ (P' : PolAV S') (g : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f g ∧ LBIso P'.L (P.L.pull g) := by
  obtain ⟨A', gA, pA, -, mA, tA⟩ := hP _ _ f P
  exact ⟨A', gA, ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩, LBIso.symm tA⟩

set_option maxHeartbeats 1600000 in

theorem exists_desc_pol (hL : Laws) (h2 : Laws2) (hH : HomExtSt) {O' R V : Type} [CommRing O'] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] [CharZero R] [CommRing V] [IsDomain V] (f : O' →+* R)
    {g : R →+* V} (hg : Function.Injective g) (P₀ : PolAV (Sp O')) (P : PolAV (Sp R)) (P' : PolAV (Sp V))
    {Φ : P'.A.left ⟶ P.A.left} {φ' : P'.A.left ⟶ P₀.A.left} (gp : IsGrpPullback P'.A P.A (spMap g) Φ)
    (gp' : IsGrpPullback P'.A P₀.A (spMap (g.comp f)) φ') (w : LBIso P'.L (P.L.pull Φ)) (w' : LBIso P'.L (P₀.L.pull φ'))
    (H : ∀ (F : Type) [Field F] [IsAlgClosed F] (i₁ i₂ : V →+* F), Function.Injective i₁ → Function.Injective i₂ →
      ∀ x₁ x₂ : Sp F ⟶ P'.A.left, x₁ ≫ P'.A.hom = spMap i₁ → x₂ ≫ P'.A.hom = spMap i₂ → x₁ ≫ Φ = x₂ ≫ Φ →
      x₁ ≫ φ' = x₂ ≫ φ') :
    ∃ φ : P.A.left ⟶ P₀.A.left, IsGrpPullback P.A P₀.A (spMap f) φ ∧ Φ ≫ φ = φ' ∧ LBIso P.L (P₀.L.pull φ) := by
  let gam : FractionRing R →+* FractionRing V :=
    IsFractionRing.lift (g := (algebraMap V (FractionRing V)).comp g) ((IsFractionRing.injective V _).comp hg)
  have hgam : ∀ r, gam (algebraMap R _ r) = algebraMap V _ (g r) := fun r => IsFractionRing.lift_algebraMap _ r
  have sq : spMap gam ≫ jK R = jK V ≫ spMap g :=
    (spMap_comp _ gam).symm.trans ((congrArg spMap (RingHom.ext hgam)).trans (spMap_comp g _))
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P'.isAb.smooth
  have := P₀.isAb.proper
  let AK := (Over.pullback (jK R)).obj P.A
  let AL := (Over.pullback (jK V)).obj P'.A
  have gK : IsGrpPullback AK P.A (jK R) (pullback.fst P.A.hom (jK R)) := isGrpPullback_pullback P.A (jK R)
  have gL : IsGrpPullback AL P'.A (jK V) (pullback.fst P'.A.hom (jK V)) := isGrpPullback_pullback P'.A (jK V)
  have gL' : IsGrpPullback AL P.A (spMap gam ≫ jK R) (pullback.fst P'.A.hom (jK V) ≫ Φ) := (gL.comp gp).congr sq.symm rfl
  obtain ⟨π, hπ₁, hπ₂⟩ : ∃ π : AL.left ⟶ AK.left, π ≫ pullback.fst P.A.hom (jK R) = pullback.fst P'.A.hom (jK V) ≫ Φ ∧
      π ≫ AK.hom = AL.hom ≫ spMap gam :=
    ⟨gK.1.lift _ (AL.hom ≫ spMap gam) (gL'.1.w.trans (Category.assoc _ _ _).symm), gK.1.lift_fst _ _ _, gK.1.lift_snd _ _ _⟩
  have gπ : IsGrpPullback AL AK (spMap gam) π := gK.cancel (gL'.congr rfl hπ₁.symm) hπ₂
  have sL : Smooth AL.hom := MorphismProperty.of_isPullback gL.1 inferInstance
  have : GeometricallyReduced AL.hom := geometricallyReduced_of_smooth _
  have : IsReduced AL.left := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian AL.hom
  have bs : (pullback.fst P'.A.hom (jK V) ≫ φ') ≫ P₀.A.hom = π ≫ AK.hom ≫ jK R ≫ spMap f := by
    rw [Category.assoc, gp'.1.w, ← Category.assoc, gL.1.w, reassoc_of% hπ₂, reassoc_of% sq, spMap_comp, Category.assoc]
  obtain ⟨ψ, hψ⟩ := exists_desc_of_points gam gπ.1 P₀.A.hom (pullback.fst P'.A.hom (jK V) ≫ φ') _ bs
    (fun F _ _ x₁ x₂ hx => by
      obtain ⟨j₁, e₁⟩ := Spec.map_surjective (x₁ ≫ AL.hom)
      obtain ⟨j₂, e₂⟩ := Spec.map_surjective (x₂ ≫ AL.hom)
      have k : ∀ (x : Sp F ⟶ AL.left) (j : CommRingCat.of (FractionRing V) ⟶ CommRingCat.of F), Spec.map j = x ≫ AL.hom →
          (x ≫ pullback.fst P'.A.hom (jK V)) ≫ P'.A.hom = spMap (j.hom.comp (algebraMap V (FractionRing V))) :=
        fun x j e => by
          rw [Category.assoc, gL.1.w, ← Category.assoc, ← e, spMap_comp]; rfl
      simpa only [Category.assoc] using H F _ _ (j₁.hom.injective.comp (IsFractionRing.injective V _))
        (j₂.hom.injective.comp (IsFractionRing.injective V _)) _ _ (k x₁ j₁ e₁) (k x₂ j₂ e₂)
        (by rw [Category.assoc, Category.assoc, ← hπ₁, reassoc_of% hx]))
  have f₁ : Flat (spMap gam) := inferInstance
  have f₂ : Surjective (spMap gam) := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  have : Flat π := MorphismProperty.of_isPullback gπ.1.flip f₁
  have : Surjective π := MorphismProperty.of_isPullback gπ.1.flip f₂
  have : Epi π := Flat.epi_of_flat_of_surjective _
  have gψ : IsGrpPullback AK P₀.A (jK R ≫ spMap f) ψ :=
    isGrpPullback_of_fpqc _ _ _ _ (spMap gam) P₀.A AK AL π ψ f₁ f₂ inferInstance gπ
      ((gL.comp gp').congr (by rw [reassoc_of% sq, spMap_comp]) hψ.symm)
      (by rw [← cancel_epi π, ← Category.assoc, hψ, bs])
  have ab : IsAbelianScheme AK := ⟨by have := P.isAb.comm; infer_instance, MorphismProperty.of_isPullback gK.1 inferInstance,
    MorphismProperty.of_isPullback gK.1 inferInstance, MorphismProperty.of_isPullback gK.1 P.isAb.geomConnected⟩
  have lK := pull_isLB P.isLB (pullback.fst P.A.hom (jK R))
  have l₀ := pull_isLB P₀.isLB ψ
  have wK : LBIso (P.L.pull (pullback.fst P.A.hom (jK R))) (P₀.L.pull ψ) := by
    refine FieldTriv.exists_gen_of_field_extension _ _ gam AK ab _ π AL.hom gπ.1 _ (LB.isLB_div l₀ lK) ?_
    have u : LBIso ((P.L.pull (pullback.fst P.A.hom (jK R))).pull π) ((P₀.L.pull ψ).pull π) :=
      LBIso.trans (pull_isLB lK _) (pull_isLB P.isLB _) (pull_isLB l₀ _) (lbIso_pull_pull P.isLB _ π rfl)
        (LBIso.trans (pull_isLB P.isLB _) (pull_isLB P'.isLB _) (pull_isLB l₀ _)
          (LBIso.symm (lbIso_pull w (pullback.fst P'.A.hom (jK V)) hπ₁))
          (LBIso.trans (pull_isLB P'.isLB _) (pull_isLB P₀.isLB _) (pull_isLB l₀ _)
            (lbIso_pull w' (pullback.fst P'.A.hom (jK V)) hψ) (LBIso.symm (lbIso_pull_pull P₀.isLB ψ π rfl))))
    obtain ⟨t, ht⟩ := u
    exact gen_chartPull (chartQuot _ _ π) t ht
  obtain ⟨P₁, g₁, gp₁, w₁⟩ := exists_polPull hL.polBaseChange (spMap f) P₀
  obtain ⟨e, me, he⟩ := grpPullback_iso gψ ((isGrpPullback_pullback P₁.A (jK R)).comp gp₁)
  obtain ⟨Ψ, mΨ, hΨ, wΨ⟩ := polAV_iso_extends_of_isIntegrallyClosed hL h2 R P₁ P e me
    (LBIso.trans lK l₀ (pull_isLB P₁.isLB _) wK
      (LBIso.symm (lbIso_pull w₁ _ (he.symm.trans (Category.assoc _ _ _).symm)))) hH
  have hΨ' : pullback.fst P.A.hom (jK R) ≫ Ψ.hom.left = e.hom.left ≫ pullback.fst P₁.A.hom (jK R) := by
    rw [← hΨ]; exact (pullback.lift_fst _ _ _).symm
  have gφ : IsGrpPullback P.A P₀.A (spMap f) (Ψ.hom.left ≫ g₁) :=
    ((isGrpPullback_of_iso Ψ).comp gp₁).congr (Category.id_comp _) rfl
  refine ⟨Ψ.hom.left ≫ g₁, gφ, ?_,
    LBIso.trans P.isLB (pull_isLB P₁.isLB _) (pull_isLB P₀.isLB _) wΨ (lbIso_pull w₁ _ rfl)⟩
  refine ext_of_injective (IsFractionRing.injective V (FractionRing V)) gL.1 P₀.A.hom ?_ ?_
  · rw [Category.assoc, gφ.1.w, ← Category.assoc, gp.1.w, gp'.1.w, spMap_comp, Category.assoc]
  · rw [← hψ, ← he, ← reassoc_of% hπ₁, reassoc_of% hΨ']

section Values

variable {F F' : Type} [Field F] [Field F'] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {K : Type} [Fintype K] {ε : K → ℤ}

theorem valF_pullGen (σ : F →+* F') {pt : K → (Sp F ⟶ B)} (t : LB.Gen (LB.LinComb M pt ε)) (j : K → M.ι) (z : Sp F')
    (h : ∀ k, pt k (spMap σ z) ∈ M.U (j k)) :
    valF (𝟙 (Sp F')) _ ((LB.pullGen M pt ε t (spMap σ)).s j).val = σ (valF (𝟙 (Sp F)) _ (t.s j).val) := by
  have m : spMap σ z ∈ LB.wchart M pt j := Set.mem_iInter.2 h
  have m' : z ∈ LB.wchart M (fun k => spMap σ ≫ pt k) j := Set.mem_iInter.2 h
  refine Eq.trans ((toStk z).injective ?_)
    (ArcExt.valF_ext σ (𝟙 _) (LB.wchart M pt j) ((top_le_iff_mem (𝟙 _) _ (spMap σ z)).2 m) (t.s j).val)
  refine (toStk_valF (𝟙 _) (LB.wchart M (fun k => spMap σ ≫ pt k) j) z m' _).trans (Eq.trans ?_
    (toStk_valF (spMap σ ≫ 𝟙 _) (LB.wchart M pt j) z m _).symm)
  rw [gm_pullGen M pt ε t (spMap σ) (𝟙 _) z j m', Category.id_comp, Category.comp_id]

theorem genRel_pull_iff (σ : F →+* F') {φ : B ⟶ B₀} (w : LB.Iso M (M₀.pull φ)) {pt : K → (Sp F ⟶ B)}
    {pt₀ : K → (Sp F ⟶ B₀)} (t : LB.Gen (LB.LinComb M pt ε)) (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) (x : F) :
    GenRel w (LB.pullGen M pt ε t (spMap σ)) (LB.pullGen M₀ pt₀ ε t₀ (spMap σ)) (σ x) ↔ GenRel w t t₀ x := by
  have := ArcExt.epi_spMap σ
  have z : Sp F' := (default : PrimeSpectrum F')
  have e₁ : (∀ k, (spMap σ ≫ pt k) ≫ φ = spMap σ ≫ pt₀ k) ↔ ∀ k, pt k ≫ φ = pt₀ k :=
    forall_congr' fun k => by rw [Category.assoc, cancel_epi]
  refine (and_congr_left fun _ => e₁).trans (and_congr_right fun hp => forall_congr' fun j => forall_congr' fun j₀ => ?_)
  have e₂ : ∀ k, ⊤ ≤ (spMap σ ≫ pt k) ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => j₀ k, j k) ↔
      ⊤ ≤ pt k ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => j₀ k, j k) := fun k =>
    (top_le_iff_mem _ _ z).trans (top_le_iff_mem (pt k) _ (spMap σ z)).symm
  refine (imp_congr_left (forall_congr' e₂)).trans (imp_congr_right fun h => ?_)
  have h' := fun k => (top_le_iff_mem (pt k) _ (spMap σ z)).1 (h k)
  rw [valF_pullGen σ t j z fun k => (h' k).2, valF_pullGen σ t₀ j₀ z fun k => by
    rw [← hp k]; exact mem_pull.1 (h' k).1, ← σ.injective.eq_iff, map_mul, map_mul, map_prod]
  refine Eq.congr rfl (congrArg₂ (· * ·) (congrArg _ (Finset.prod_congr rfl fun k _ => ?_)) rfl)
  rw [map_zpow₀, ArcExt.valF_ext σ (pt k) _ (h k)]

theorem genRel_congr (hM : M.IsLB) (hM₀ : M₀.IsLB) {φ : B ⟶ B₀} (w : LB.Iso M (M₀.pull φ)) {pt pt' : K → (Sp F ⟶ B)}
    {pt₀ pt₀' : K → (Sp F ⟶ B₀)} (hp : pt = pt') (hp₀ : pt₀ = pt₀') {t : LB.Gen (LB.LinComb M pt ε)}
    {t' : LB.Gen (LB.LinComb M pt' ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {t₀' : LB.Gen (LB.LinComb M₀ pt₀' ε)}
    (g : t.IsGen) (g' : t'.IsGen) (g₀ : t₀.IsGen) (g₀' : t₀'.IsGen)
    (h : ∀ y J, Good M y J → val t (𝟙 _) y J = val t' (𝟙 _) y J)
    (h₀ : ∀ y J, Good M₀ y J → val t₀ (𝟙 _) y J = val t₀' (𝟙 _) y J) (x : F) :
    GenRel w t t₀ x ↔ GenRel w t' t₀' x := by
  subst hp hp₀
  rw [TorusExt.gen_ext_val hM g g' h, TorusExt.gen_ext_val hM₀ g₀ g₀' h₀]

end Values

theorem exists_common_field {K F L : Type} [Field K] [Field F] [Field L] (i : K →+* F) (j : K →+* L) :
    ∃ (F' : Type) (_ : Field F') (_ : IsAlgClosed F') (σ : F →+* F') (τ : L →+* F'), σ.comp i = τ.comp j := by
  letI := i.toAlgebra
  letI := j.toAlgebra
  have : Nontrivial (TensorProduct K F L) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct K F L)
  letI := Ideal.Quotient.field m
  let q : TensorProduct K F L →+* AlgebraicClosure (TensorProduct K F L ⧸ m) :=
    (algebraMap (TensorProduct K F L ⧸ m) _).comp (Ideal.Quotient.mk m)
  refine ⟨AlgebraicClosure (TensorProduct K F L ⧸ m), inferInstance, inferInstance,
    q.comp Algebra.TensorProduct.includeLeftRingHom, q.comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  rw [RingHom.comp_assoc, RingHom.comp_assoc]
  exact congrArg q.comp Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F F' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F']

theorem gtφ_ext {σ : F →+* F'} (hσ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') {k : ℕ}
    {p : QkPt D F k} {p' : QkPt D F' k} (h : QkExt σ p p') (χ : D.X) :
    DegPre.gtφ D F' p'.g.b χ = fun i => spMap σ ≫ DegPre.gtφ D F p.g.b χ i := by
  have hj : spMap σ ≫ jFK (R := R) F = jFK (R := R) F' := (spMap_comp _ _).symm.trans (congrArg spMap hσ)
  let r : TF (R := R) F' ⟶ TF (R := R) F := Over.homMk (spMap σ) (by
    show spMap σ ≫ jFK (R := R) F ≫ jK R = jFK (R := R) F' ≫ jK R
    rw [← Category.assoc, hj])
  have hb : p'.g.b = r ≫ p.g.b := Over.OverMorphism.ext h.2.1
  have hc : ∀ x : 𝟙_ (Over (Sp R)) ⟶ D.P.A, toUnit (TF (R := R) F') ≫ x = r ≫ toUnit _ ≫ x := fun x => by
    rw [← Category.assoc, toUnit_unique (r ≫ toUnit _) (toUnit _)]
  funext i
  fin_cases i
  · show (toUnit _ ≫ D.c χ * p'.g.b).left = (r ≫ (toUnit _ ≫ D.c χ * p.g.b)).left
    rw [MonObj.comp_mul, hb, hc]
  · exact congrArg (fun q => q.left) (hc _)
  · exact h.2.1
  · exact congrArg (fun q => q.left) (hc _)

end GlobalTheory.ArcDataDescent
end

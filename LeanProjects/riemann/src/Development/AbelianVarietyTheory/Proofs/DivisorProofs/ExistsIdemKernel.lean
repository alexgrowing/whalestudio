import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFlatTorsionHarrisTaylorAbelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFiniteFlat
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatAbelianSchemeHomOfQuasiInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointTrivialOfGeometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantOpenNatCastIsUnitNonZeroDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiniteFlatTorsionSubschemeEqCardPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiberEqCardSectionsMulLengthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupSchemeStalkLengthConstantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UPel.HT.ES.OrdCount

open GlobalTheory.IwLevel GlobalTheory.IwLevel.KerGrp in

theorem exists_idem_kernel : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') (f : A ⟶ A), IsMonHom ψ → IsMonHom f → IsFinite ψ.left → Flat ψ.left → (∀ (T : Over S) (z : T ⟶ A), z ≫ ψ = 1 → (z ≫ f) ≫ ψ = 1 ∧ (z ≫ f) ≫ f = z ≫ f) → ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ A), IsMonHom i ∧ Mono i ∧ IsFinite K.hom ∧ Flat K.hom ∧ ∀ (T : Over S) (z : T ⟶ A), GlobalTheory.IwLevel.InSub i z ↔ (z ≫ ψ = 1 ∧ z ≫ f = 1) := by
  intro S A A' _ _ _ _ ψ fx _ _ hfin hfl hyp
  letI gH : GrpObj (IwLevel.ker ψ) := grp ψ
  haveI : IsMonHom (pullback.fst ψ η[A']) := isMonHom_fst ψ
  have hPB := (IsPullback.of_hasPullback ψ η[A']).map (Over.forget S)
  have hHfin : IsFinite (IwLevel.ker ψ).hom := by
    rw [← Over.w (pullback.snd ψ η[A'])]
    haveI : IsFinite (pullback.snd ψ η[A']).left := MorphismProperty.of_isPullback (P := @IsFinite) hPB hfin
    exact inferInstanceAs (IsFinite (_ ≫ 𝟙 S))
  have hHflat : Flat (IwLevel.ker ψ).hom := by
    rw [← Over.w (pullback.snd ψ η[A'])]
    haveI : Flat (pullback.snd ψ η[A']).left := MorphismProperty.of_isPullback (P := @Flat) hPB hfl
    exact inferInstanceAs (Flat (_ ≫ 𝟙 S))
  set jH := pullback.fst ψ η[A'] with hjH
  have hj : jH ≫ ψ = 1 := fst_comp ψ
  let g : IwLevel.ker ψ ⟶ IwLevel.ker ψ := KerGrp.lift ψ (jH ≫ fx) (hyp _ jH hj).1
  have hg : g ≫ jH = jH ≫ fx := KerGrp.lift_fst _ _ _
  have hxx' : jH ≫ fx ≫ fx = jH ≫ fx := by rw [← Category.assoc]; exact (hyp _ jH hj).2
  letI gK : GrpObj (IwLevel.ker (jH ≫ fx)) := grp (jH ≫ fx)
  haveI : IsMonHom (pullback.fst (jH ≫ fx) η[A]) := isMonHom_fst (jH ≫ fx)
  set iK := pullback.fst (jH ≫ fx) η[A] with hiK
  have hk : iK ≫ jH ≫ fx = 1 := fst_comp (jH ≫ fx)
  have hrk : (𝟙 (IwLevel.ker ψ) / g) ≫ jH ≫ fx = 1 := by
    rw [← Category.assoc, GrpObj.div_comp, Category.id_comp, hg, GrpObj.div_comp, Category.assoc, hxx',
      div_self']
  let r : IwLevel.ker ψ ⟶ IwLevel.ker (jH ≫ fx) := KerGrp.lift (jH ≫ fx) (𝟙 (IwLevel.ker ψ) / g) hrk
  have hr : r ≫ iK = 𝟙 (IwLevel.ker ψ) / g := KerGrp.lift_fst _ _ _
  have hiKg : iK ≫ g = 1 := KerGrp.hom_ext ψ (by
    rw [Category.assoc, hg, hk, MonObj.one_comp])
  have hir : iK ≫ r = 𝟙 _ := KerGrp.hom_ext (jH ≫ fx) (by
    rw [Category.assoc, hr, GrpObj.comp_div, Category.comp_id, hiKg, div_one, Category.id_comp])
  have hirl : iK.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, hir, Over.id_left]
  have hKfin : IsFinite (IwLevel.ker (jH ≫ fx)).hom := by
    haveI : IsFinite (r.left ≫ (IwLevel.ker (jH ≫ fx)).hom) := by rw [Over.w r]; exact hHfin
    haveI : IsSeparated (r.left ≫ (IwLevel.ker (jH ≫ fx)).hom) := by rw [Over.w r]; infer_instance
    haveI : IsSeparated r.left := IsSeparated.of_comp _ (IwLevel.ker (jH ≫ fx)).hom
    haveI : IsFinite (iK.left ≫ r.left) := by rw [hirl]; infer_instance
    haveI : IsFinite iK.left := IsFinite.of_comp _ r.left
    rw [← Over.w iK]; infer_instance
  have hKflat : Flat (IwLevel.ker (jH ≫ fx)).hom := by
    haveI : Flat (r.left ≫ (IwLevel.ker (jH ≫ fx)).hom) := by rw [Over.w r]; exact hHflat
    exact HTTorsionFF.flat_of_retract _ iK.left r.left hirl
  refine ⟨IwLevel.ker (jH ≫ fx), gK, iK ≫ jH, inferInstance, inferInstance, hKfin, hKflat, fun T z => ?_⟩
  refine ⟨?_, fun ⟨h1, h2⟩ => ?_⟩
  · rintro ⟨y, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, Category.assoc, hj, MonObj.comp_one, MonObj.comp_one]
    · rw [Category.assoc, Category.assoc, hk, MonObj.comp_one]
  · refine ⟨KerGrp.lift (jH ≫ fx) (KerGrp.lift ψ z h1) (by rw [← Category.assoc, KerGrp.lift_fst, h2]), ?_⟩
    rw [← Category.assoc, KerGrp.lift_fst, KerGrp.lift_fst]

def subEquiv {S : Scheme.{0}} {A K T : Over S} (i : K ⟶ A) [Mono i] (P : (T ⟶ A) → Prop)
    (h : ∀ x, GlobalTheory.IwLevel.InSub i x ↔ P x) : (T ⟶ K) ≃ {x : T ⟶ A // P x} :=
  Equiv.ofBijective (fun g => ⟨g ≫ i, (h _).1 ⟨g, rfl⟩⟩)
    ⟨fun g g' hgg => (cancel_mono i).1 (congrArg Subtype.val hgg),
     fun x => let ⟨g, hg⟩ := (h x.1).2 x.2; ⟨g, Subtype.ext hg⟩⟩

def fibreEquiv {S T : Scheme.{0}} (K : Over S) (y : T ⟶ S) :
    (Over.mk y ⟶ K) ≃ {s : T ⟶ pullback K.hom y // s ≫ pullback.snd K.hom y = 𝟙 _} where
  toFun g := ⟨pullback.lift g.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w g), pullback.lift_snd _ _ _⟩
  invFun s := Over.homMk (s.1 ≫ pullback.fst K.hom y) (by
    change (s.1 ≫ pullback.fst K.hom y) ≫ K.hom = y
    rw [Category.assoc, pullback.condition, ← Category.assoc, s.2, Category.id_comp])
  left_inv g := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  right_inv s := Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans s.2.symm))

theorem eq_one_of_reg {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    {T : Over S} (x : T ⟶ A) (c : ℕ)
    (hc : ∀ (U : T.left.Opens) (f : Γ(T.left, U)), (c : Γ(T.left, U)) * f = 0 → f = 0) (hx : x ^ c = 1)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (z : Sp k ⟶ S) (g : Over.mk z ⟶ T), g ≫ x = 1) :
    x = 1 := by
  obtain ⟨U, j, hj, hu⟩ := GlobalTheory.T.exists_dominant_natCast_isUnit_of_nonZeroDivisor T.left c hc
  let j' : Over.mk (j ≫ T.hom) ⟶ T := Over.homMk j
  have h1 : j' ≫ x = 1 := GlobalTheory.T.abelianScheme_torsionPoint_trivial_of_geometric S A hA _ (j' ≫ x) c hu (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
    (fun k _ _ hk z g => by rw [← Category.assoc]; exact h k hk z _)
  have h2 : j' ≫ x = j' ≫ 1 := by rw [h1, MonObj.comp_one]
  have := hA.proper
  exact Over.OverMorphism.ext (GlobalTheory.hom_ext_of_isSchemeTheoreticallyDominant j A.hom
    (congrArg CommaMorphism.left h2) (by rw [Over.w, Over.w]))

end GlobalTheory.UPel.HT.ES.OrdCount

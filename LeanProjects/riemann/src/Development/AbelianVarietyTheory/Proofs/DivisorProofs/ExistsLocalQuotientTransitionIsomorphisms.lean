import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace QuotTransition

section

variable {S U V : Scheme.{0}} (fU : U ⟶ S) (fV : V ⟶ S) (A : Over S)
  (BU : Over U) (BV : Over V) (qU : (Over.pullback fU).obj A ⟶ BU) (qV : (Over.pullback fV).obj A ⟶ BV)

lemma w_left : qU.left ≫ BU.hom = pullback.snd A.hom fU := Over.w qU

noncomputable abbrev src : Scheme.{0} := pullback qU.left (pullback.fst (BU.hom ≫ fU) fV)

noncomputable def toV : src fU fV A BU qU ⟶ pullback A.hom fV :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst A.hom fU) (pullback.snd _ _ ≫ pullback.snd _ _) (by
    have h1 := pullback.condition (f := A.hom) (g := fU)
    have h2 := pullback.condition (f := qU.left) (g := pullback.fst (BU.hom ≫ fU) fV)
    have h3 := pullback.condition (f := BU.hom ≫ fU) (g := fV)
    have h4 := w_left fU A BU qU
    simp only [Category.assoc] at h1 h2 h3 ⊢
    rw [h1, ← h4, Category.assoc, reassoc_of% h2, h3])

@[reassoc (attr := simp)]
lemma toV_fst : toV fU fV A BU qU ≫ pullback.fst A.hom fV =
    pullback.fst _ _ ≫ pullback.fst A.hom fU := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma toV_snd : toV fU fV A BU qU ≫ pullback.snd A.hom fV =
    pullback.snd _ _ ≫ pullback.snd _ _ := pullback.lift_snd _ _ _

variable (H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)

lemma map_left_fst {T : Scheme.{0}} (f : T ⟶ S) {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
  pullback.lift_fst _ _ _

lemma toV_comp_eq [Flat qU.left] [Surjective qU.left] [QuasiCompact qU.left]
    (hU : IsPullback ((fst ((Over.pullback fU).obj H) ((Over.pullback fU).obj A) ≫ (Over.pullback fU).map i) *
      snd ((Over.pullback fU).obj H) ((Over.pullback fU).obj A))
      (snd ((Over.pullback fU).obj H) ((Over.pullback fU).obj A)) qU qU)
    (hV : IsPullback ((fst ((Over.pullback fV).obj H) ((Over.pullback fV).obj A) ≫ (Over.pullback fV).map i) *
      snd ((Over.pullback fV).obj H) ((Over.pullback fV).obj A))
      (snd ((Over.pullback fV).obj H) ((Over.pullback fV).obj A)) qV qV)
    {T : Scheme.{0}} (u v : T ⟶ src fU fV A BU qU)
    (huv : u ≫ pullback.snd _ _ = v ≫ pullback.snd _ _) :
    u ≫ toV fU fV A BU qU ≫ qV.left = v ≫ toV fU fV A BU qU ≫ qV.left := by
  obtain ⟨yu, hyu_def⟩ : ∃ y, y = u ≫ pullback.fst qU.left (pullback.fst (BU.hom ≫ fU) fV) := ⟨_, rfl⟩
  obtain ⟨yv, hyv_def⟩ : ∃ y, y = v ≫ pullback.fst qU.left (pullback.fst (BU.hom ≫ fU) fV) := ⟨_, rfl⟩
  have hq : yu ≫ qU.left = yv ≫ qU.left := by
    simp only [hyu_def, hyv_def, Category.assoc, pullback.condition, reassoc_of% huv]
  have hs : yu ≫ pullback.snd A.hom fU = yv ≫ pullback.snd A.hom fU := by
    rw [← w_left fU A BU qU, reassoc_of% hq]
  let Tj : Over U := Over.mk (yv ≫ pullback.snd A.hom fU)
  let yu' : Tj ⟶ (Over.pullback fU).obj A := Over.homMk yu hs
  let yv' : Tj ⟶ (Over.pullback fU).obj A := Over.homMk yv rfl
  have hq' : yu' ≫ qU = yv' ≫ qU := Over.OverMorphism.ext hq
  let s := hU.lift yu' yv' hq' ≫ fst _ _
  have hyu : yu' = (s ≫ (Over.pullback fU).map i) * yv' := by
    have h1 := hU.lift_fst yu' yv' hq'
    rw [comp_mul, hU.lift_snd] at h1
    rw [Category.assoc, h1]
  have e1 : yv ≫ pullback.snd A.hom fU ≫ fU =
      u ≫ pullback.snd _ _ ≫ pullback.snd (BU.hom ≫ fU) fV ≫ fV := by
    rw [← w_left fU A BU qU, hyv_def]
    simp only [Category.assoc]
    rw [reassoc_of% (pullback.condition (f := qU.left) (g := pullback.fst (BU.hom ≫ fU) fV)),
      pullback.condition, reassoc_of% huv]
  have hsw : s.left ≫ pullback.snd H.hom fU = yv ≫ pullback.snd A.hom fU := Over.w s
  have hc1 : (s.left ≫ pullback.fst H.hom fU) ≫ H.hom =
      (u ≫ pullback.snd _ _ ≫ pullback.snd (BU.hom ≫ fU) fV) ≫ fV := by
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% hsw, e1]
  let Tk : Over V := Over.mk (u ≫ pullback.snd _ _ ≫ pullback.snd (BU.hom ≫ fU) fV)
  let s' : Tk ⟶ (Over.pullback fV).obj H :=
    Over.homMk (pullback.lift (s.left ≫ pullback.fst H.hom fU) (u ≫ pullback.snd _ _ ≫ pullback.snd _ _) hc1)
      (pullback.lift_snd _ _ _)
  let zu : Tk ⟶ (Over.pullback fV).obj A :=
    Over.homMk (u ≫ toV fU fV A BU qU) (by simp [Tk])
  let zv : Tk ⟶ (Over.pullback fV).obj A :=
    Over.homMk (v ≫ toV fU fV A BU qU) (by simp [Tk, reassoc_of% huv])
  have hc0 : (s.left ≫ pullback.fst H.hom fU ≫ i.left) ≫ A.hom = yv ≫ pullback.fst A.hom fU ≫ A.hom := by
    rw [Category.assoc, Category.assoc, Over.w i, pullback.condition, reassoc_of% hsw, pullback.condition]
  let x0 : Over.mk (yv ≫ pullback.fst A.hom fU ≫ A.hom) ⟶ A :=
    Over.homMk (s.left ≫ pullback.fst H.hom fU ≫ i.left) hc0
  let y0 : Over.mk (yv ≫ pullback.fst A.hom fU ≫ A.hom) ⟶ A :=
    Over.homMk (yv ≫ pullback.fst A.hom fU) (Category.assoc _ _ _)
  have mU := GlobalTheory.TorusToProper.mul_left_fst fU A (s ≫ (Over.pullback fU).map i) yv' x0 y0
    (by rw [Over.comp_left, Category.assoc, map_left_fst]; rfl) rfl
  have mV := GlobalTheory.TorusToProper.mul_left_fst fV A (s' ≫ (Over.pullback fV).map i) zv x0 y0
    (by rw [Over.comp_left, Category.assoc, map_left_fst]; simp only [x0, s', Over.homMk_left]; rw [pullback.lift_fst_assoc, Category.assoc]) (by simp [y0, zv, hyv_def])
  have key : zu = (s' ≫ (Over.pullback fV).map i) * zv := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [mV, ← mU, ← hyu]
      simp [zu, yu', hyu_def]
    · exact (Over.w zu).trans (Over.w ((s' ≫ (Over.pullback fV).map i) * zv)).symm
  have hk : zu ≫ qV = zv ≫ qV := by
    rw [key]
    have := lift s' zv ≫= hV.w
    simpa [comp_mul, ← Category.assoc] using this
  have := congrArg CommaMorphism.left hk
  simpa [zu, zv] using this

theorem exists_trans [Flat qU.left] [Surjective qU.left] [QuasiCompact qU.left]
    (hU : IsPullback ((fst ((Over.pullback fU).obj H) ((Over.pullback fU).obj A) ≫ (Over.pullback fU).map i) *
      snd ((Over.pullback fU).obj H) ((Over.pullback fU).obj A))
      (snd ((Over.pullback fU).obj H) ((Over.pullback fU).obj A)) qU qU)
    (hV : IsPullback ((fst ((Over.pullback fV).obj H) ((Over.pullback fV).obj A) ≫ (Over.pullback fV).map i) *
      snd ((Over.pullback fV).obj H) ((Over.pullback fV).obj A))
      (snd ((Over.pullback fV).obj H) ((Over.pullback fV).obj A)) qV qV) :
    ∃ b : pullback (BU.hom ≫ fU) fV ⟶ BV.left, b ≫ BV.hom = pullback.snd _ _ ∧
      ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom fU) (z : T ⟶ pullback A.hom fV)
        (w : T ⟶ pullback (BU.hom ≫ fU) fV), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ qU.left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b = z ≫ qV.left := by
  have hc : ∀ {T : Scheme.{0}} (u v : T ⟶ src fU fV A BU qU),
      u ≫ pullback.snd _ _ = v ≫ pullback.snd _ _ →
      u ≫ (toV fU fV A BU qU ≫ qV.left) = v ≫ (toV fU fV A BU qU ≫ qV.left) :=
    fun u v huv => toV_comp_eq fU fV A BU BV qU qV H i hU hV u v huv
  have fac := EffectiveEpi.fac (pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV))
    (toV fU fV A BU qU ≫ qV.left) hc
  refine ⟨EffectiveEpi.desc (pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV))
    (toV fU fV A BU qU ≫ qV.left) hc, ?_, ?_⟩
  · rw [← cancel_epi (pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV)), reassoc_of% fac,
      w_left fV A BV qV, toV_snd]
  · intro T y z w h1 h2 h3
    have hw : w = pullback.lift y w h2.symm ≫ pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV) :=
      (pullback.lift_snd _ _ _).symm
    have hz : pullback.lift y w h2.symm ≫ toV fU fV A BU qU = z := by
      apply pullback.hom_ext
      · rw [Category.assoc, toV_fst, pullback.lift_fst_assoc, h1]
      · rw [Category.assoc, toV_snd, pullback.lift_snd_assoc, h3]
    rw [hw, Category.assoc, fac, ← Category.assoc, hz]

end

lemma lift_comp_lift {S U V : Scheme.{0}} (fU : U ⟶ S) (fV : V ⟶ S) (A : Over S)
    (BU : Over U) (BV : Over V) (qU : (Over.pullback fU).obj A ⟶ BU) (qV : (Over.pullback fV).obj A ⟶ BV)
    [Flat qU.left] [Surjective qU.left] [QuasiCompact qU.left]
    (b : pullback (BU.hom ≫ fU) fV ⟶ BV.left) (b' : pullback (BV.hom ≫ fV) fU ⟶ BU.left)
    (hb : b ≫ BV.hom = pullback.snd _ _)
    (cb : ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom fU) (z : T ⟶ pullback A.hom fV)
        (w : T ⟶ pullback (BU.hom ≫ fU) fV), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ qU.left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b = z ≫ qV.left)
    (cb' : ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom fV) (z : T ⟶ pullback A.hom fU)
        (w : T ⟶ pullback (BV.hom ≫ fV) fU), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ qV.left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b' = z ≫ qU.left)
    (h₁ : b ≫ BV.hom ≫ fV = (pullback.fst _ _ ≫ BU.hom) ≫ fU)
    (h₂ : b' ≫ BU.hom ≫ fU = (pullback.fst _ _ ≫ BV.hom) ≫ fV) :
    pullback.lift b (pullback.fst _ _ ≫ BU.hom) h₁ ≫ pullback.lift b' (pullback.fst _ _ ≫ BV.hom) h₂ =
      𝟙 _ := by
  rw [← cancel_epi (pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV)), Category.comp_id]
  have k1 : pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV) ≫ b = toV fU fV A BU qU ≫ qV.left :=
    cb _ (pullback.fst _ _) (toV fU fV A BU qU) _ (toV_fst fU fV A BU qU).symm pullback.condition.symm
      (toV_snd fU fV A BU qU).symm
  have k2 := cb' _ (toV fU fV A BU qU) (pullback.fst _ _)
    (pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV) ≫ pullback.lift b (pullback.fst _ _ ≫ BU.hom) h₁)
    (toV_fst fU fV A BU qU) (by rw [Category.assoc, pullback.lift_fst, k1])
    (by rw [Category.assoc, pullback.lift_snd, ← Category.assoc, ← pullback.condition, Category.assoc,
      w_left fU A BU qU])
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst, ← Category.assoc, k2, pullback.condition]
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, ← Category.assoc (pullback.lift b _ _),
      pullback.lift_fst, hb]

theorem isPullback_trans {S U V : Scheme.{0}} (fU : U ⟶ S) (fV : V ⟶ S) (A : Over S)
    (BU : Over U) (BV : Over V) (qU : (Over.pullback fU).obj A ⟶ BU) (qV : (Over.pullback fV).obj A ⟶ BV)
    [Flat qU.left] [Surjective qU.left] [QuasiCompact qU.left]
    [Flat qV.left] [Surjective qV.left] [QuasiCompact qV.left]
    (b : pullback (BU.hom ≫ fU) fV ⟶ BV.left) (b' : pullback (BV.hom ≫ fV) fU ⟶ BU.left)
    (hb : b ≫ BV.hom = pullback.snd _ _) (hb' : b' ≫ BU.hom = pullback.snd _ _)
    (cb : ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom fU) (z : T ⟶ pullback A.hom fV)
        (w : T ⟶ pullback (BU.hom ≫ fU) fV), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ qU.left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b = z ≫ qV.left)
    (cb' : ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom fV) (z : T ⟶ pullback A.hom fU)
        (w : T ⟶ pullback (BV.hom ≫ fV) fU), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ qV.left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b' = z ≫ qU.left) :
    IsPullback b (pullback.fst _ _ ≫ BU.hom) (BV.hom ≫ fV) fU := by
  have h₁ : b ≫ BV.hom ≫ fV = (pullback.fst _ _ ≫ BU.hom) ≫ fU := by
    rw [reassoc_of% hb, Category.assoc]; exact pullback.condition.symm
  have h₂ : b' ≫ BU.hom ≫ fU = (pullback.fst _ _ ≫ BV.hom) ≫ fV := by
    rw [reassoc_of% hb', Category.assoc]; exact pullback.condition.symm
  let e : pullback (BU.hom ≫ fU) fV ≅ pullback (BV.hom ≫ fV) fU :=
    { hom := pullback.lift b (pullback.fst _ _ ≫ BU.hom) h₁
      inv := pullback.lift b' (pullback.fst _ _ ≫ BV.hom) h₂
      hom_inv_id := lift_comp_lift fU fV A BU BV qU qV b b' hb cb cb' h₁ h₂
      inv_hom_id := lift_comp_lift fV fU A BV BU qV qU b' b hb' cb' cb h₂ h₁ }
  exact IsPullback.of_iso_pullback ⟨h₁⟩ e (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem exists_transition : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j),
    (∀ j, Flat (q j).left) → (∀ j, Surjective (q j).left) → (∀ j, QuasiCompact (q j).left) → (∀ j, IsPullback ((fst ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A) ≫ (Over.pullback (𝒰.f j)).map i) * snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (q j) (q j)) →
    ∃ b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left,
      (∀ j k, b j k ≫ (B k).hom = pullback.snd _ _) ∧
      (∀ j k, IsPullback (b j k) (pullback.fst _ _ ≫ (B j).hom) ((B k).hom ≫ 𝒰.f k) (𝒰.f j)) ∧
      ∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left := by
  intro S 𝒰 A H _ _ i B q hf hs hqc hpb
  have key : ∀ j k, ∃ b : pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left,
      b ≫ (B k).hom = pullback.snd _ _ ∧
      ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b = z ≫ (q k).left := fun j k => by
    haveI := hf j; haveI := hs j; haveI := hqc j
    exact exists_trans (𝒰.f j) (𝒰.f k) A (B j) (B k) (q j) (q k) H i (hpb j) (hpb k)
  choose b hb1 hb3 using key
  refine ⟨b, hb1, fun j k => ?_, hb3⟩
  haveI := hf j; haveI := hs j; haveI := hqc j
  haveI := hf k; haveI := hs k; haveI := hqc k
  exact isPullback_trans (𝒰.f j) (𝒰.f k) A (B j) (B k) (q j) (q k) (b j k) (b k j) (hb1 j k) (hb1 k j)
    (hb3 j k) (hb3 k j)

end QuotTransition
end GlobalTheory

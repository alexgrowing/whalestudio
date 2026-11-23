import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

namespace PointQuot

theorem exists_grpObj_of_mono {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] {H A : 𝒞}
    [GrpObj A] (i : H ⟶ A) [Mono i] (e : 𝟙_ 𝒞 ⟶ H) (m : H ⊗ H ⟶ H) (n : H ⟶ H)
    (he : e ≫ i = 1) (hm : m ≫ i = (fst H H ≫ i) * (snd H H ≫ i)) (hn : n ≫ i = i⁻¹) :
    ∃ _ : GrpObj H, IsMonHom i := by
  letI : MonObj H :=
    { one := e
      mul := m
      one_mul := by
        rw [← cancel_mono i, Category.assoc, hm]
        simp [MonObj.comp_mul, he, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono i, Category.assoc, hm]
        simp [MonObj.comp_mul, he, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono i]
        simp [MonObj.comp_mul, hm, _root_.mul_assoc] }
  refine ⟨{ inv := n, left_inv := ?_, right_inv := ?_ }, ⟨?_, ?_⟩⟩
  · change lift n (𝟙 H) ≫ m = toUnit H ≫ e
    rw [← cancel_mono i]
    simp [MonObj.comp_mul, hm, hn, he]
  · change lift (𝟙 H) n ≫ m = toUnit H ≫ e
    rw [← cancel_mono i]
    simp [MonObj.comp_mul, hm, hn, he]
  · change e ≫ i = _
    rw [he, Hom.one_def, toUnit_unit, Category.id_comp]
  · change m ≫ i = _
    rw [hm, Hom.mul_def]
    congr 1
    ext <;> simp

variable {S : Scheme.{0}}

def openObj (Z : Over S) (V : Z.left.Opens) : Over S := Over.mk (V.ι ≫ Z.hom)

def openι (Z : Over S) (V : Z.left.Opens) : openObj Z V ⟶ Z := Over.homMk V.ι rfl

def openLE (Z : Over S) {V W : Z.left.Opens} (h : V ≤ W) : openObj Z V ⟶ openObj Z W :=
  Over.homMk (Z.left.homOfLE h) (by
    change Z.left.homOfLE h ≫ W.ι ≫ Z.hom = V.ι ≫ Z.hom
    rw [Scheme.homOfLE_ι_assoc])

lemma openLE_ι (Z : Over S) {V W : Z.left.Opens} (h : V ≤ W) :
    openLE Z h ≫ openι Z W = openι Z V :=
  Over.OverMorphism.ext (Scheme.homOfLE_ι _ h)

lemma const_of_le {Z Y : Over S} {g : Z ⟶ Y} {c : 𝟙_ (Over S) ⟶ Y} {V W : Z.left.Opens}
    (h : V ≤ W) (hW : openι Z W ≫ g = toUnit _ ≫ c) : openι Z V ≫ g = toUnit _ ≫ c := by
  rw [← openLE_ι Z h, Category.assoc, hW, ← Category.assoc]
  congr 1
  exact toUnit_unique _ _

lemma hom_ext_local {Z Y : Over S} (f g : Z ⟶ Y)
    (h : ∀ z : Z.left, ∃ V : Z.left.Opens, z ∈ V ∧ openι Z V ≫ f = openι Z V ≫ g) : f = g := by
  choose V hV hfg using h
  have hc : TopologicalSpace.IsOpenCover V := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    exact fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hV z⟩
  refine Over.OverMorphism.ext ((Z.left.openCoverOfIsOpenCover V hc).hom_ext _ _ fun z => ?_)
  exact congrArg CommaMorphism.left (hfg z)

def constObj (S : Scheme.{0}) (I : Type) : Over S := Over.mk (Sigma.desc fun _ : I => 𝟙 S)

def constPt (S : Scheme.{0}) {I : Type} (c : I) : 𝟙_ (Over S) ⟶ constObj S I :=
  Over.homMk (Sigma.ι (fun _ : I => S) c) (Sigma.ι_desc _ _)

def constDesc {I : Type} {A : Over S} (x : I → (𝟙_ (Over S) ⟶ A)) : constObj S I ⟶ A :=
  Over.homMk (Sigma.desc (f := fun _ : I => S) fun c => (x c).left) (Sigma.hom_ext _ _ fun c => by
    change Sigma.ι (fun _ : I => S) c ≫ Sigma.desc (f := fun _ : I => S) (fun c => (x c).left) ≫ A.hom =
      Sigma.ι (fun _ : I => S) c ≫ Sigma.desc fun _ : I => 𝟙 S
    rw [Sigma.ι_desc_assoc, Sigma.ι_desc]
    exact Over.w (x c))

lemma constPt_desc {I : Type} {A : Over S} (x : I → (𝟙_ (Over S) ⟶ A)) (c : I) :
    constPt S c ≫ constDesc x = x c :=
  Over.OverMorphism.ext (Sigma.ι_desc (f := fun _ : I => S) _ _)

lemma locally_const {I : Type} {Z : Over S} (f : Z ⟶ constObj S I) (z : Z.left) :
    ∃ V : Z.left.Opens, z ∈ V ∧ ∃ c : I, openι Z V ≫ f = toUnit _ ≫ constPt S c := by
  obtain ⟨c, y, hy'⟩ : ∃ (c : I) (y : S), Sigma.ι (fun _ : I => S) c y = f.left z :=
    (sigmaOpenCover fun _ : I ↦ S).exists_eq (f.left z)
  let V : Z.left.Opens := f.left ⁻¹ᵁ (Sigma.ι (fun _ : I => S) c).opensRange
  have hr : Set.range (V.ι ≫ f.left) ⊆ Set.range (Sigma.ι (fun _ : I => S) c) := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact v.2
  have hl := IsOpenImmersion.lift_fac (Sigma.ι (fun _ : I => S) c) (V.ι ≫ f.left) hr
  let l : openObj Z V ⟶ 𝟙_ (Over S) :=
    Over.homMk (IsOpenImmersion.lift (Sigma.ι (fun _ : I => S) c) (V.ι ≫ f.left) hr) (by
      change _ ≫ 𝟙 S = V.ι ≫ Z.hom
      have e₁ : Sigma.ι (fun _ : I => S) c ≫ (constObj S I).hom = 𝟙 S :=
        Sigma.ι_desc (f := fun _ : I => S) (fun _ => 𝟙 S) c
      rw [← Over.w f, ← e₁]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (constObj S I).hom) hl).trans (Category.assoc _ _ _)))
  refine ⟨V, ⟨y, hy'⟩, c, ?_⟩
  rw [toUnit_unique (toUnit _) l]
  exact Over.OverMorphism.ext hl.symm

lemma locally_const_desc {I : Type} {A Z : Over S} (x : I → (𝟙_ (Over S) ⟶ A))
    (f : Z ⟶ constObj S I) (z : Z.left) :
    ∃ V : Z.left.Opens, z ∈ V ∧ ∃ c : I, openι Z V ≫ f ≫ constDesc x = toUnit _ ≫ x c := by
  obtain ⟨V, hV, c, h⟩ := locally_const f z
  exact ⟨V, hV, c, by rw [← Category.assoc, h, Category.assoc, constPt_desc]⟩

lemma exists_lift {I : Type} {A Z : Over S} (x : I → (𝟙_ (Over S) ⟶ A)) [Mono (constDesc x)]
    (g : Z ⟶ A)
    (h : ∀ z : Z.left, ∃ V : Z.left.Opens, z ∈ V ∧ ∃ c : I, openι Z V ≫ g = toUnit _ ≫ x c) :
    ∃ f : Z ⟶ constObj S I, f ≫ constDesc x = g := by
  choose V hV c hc using h
  have hcov : TopologicalSpace.IsOpenCover V := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    exact fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hV z⟩
  have : Mono (constDesc x).left := Over.mono_left_of_mono _
  let 𝒰 := Z.left.openCoverOfIsOpenCover V hcov
  let φ : ∀ z, 𝒰.X z ⟶ (constObj S I).left := fun z =>
    (toUnit (openObj Z (V z)) ≫ constPt S (c z)).left
  have hφ : ∀ z, φ z ≫ (constDesc x).left = 𝒰.f z ≫ g.left := fun (z : Z.left) => by
    have : (toUnit (openObj Z (V z)) ≫ constPt S (c z)) ≫ constDesc x = openι Z (V z) ≫ g := by
      rw [Category.assoc, constPt_desc]
      exact (hc z).symm
    exact congrArg CommaMorphism.left this
  have hcomp : ∀ a b, pullback.fst (𝒰.f a) (𝒰.f b) ≫ φ a = pullback.snd _ _ ≫ φ b := fun a b => by
    rw [← cancel_mono (constDesc x).left, Category.assoc, Category.assoc, hφ, hφ,
      pullback.condition_assoc]
  have key : 𝒰.glueMorphisms φ hcomp ≫ (constDesc x).left = g.left :=
    𝒰.hom_ext _ _ fun z => by rw [𝒰.ι_glueMorphisms_assoc, hφ]
  exact ⟨Over.homMk (𝒰.glueMorphisms φ hcomp) (by
    rw [← Over.w (constDesc x), ← Category.assoc, key, Over.w]), Over.OverMorphism.ext key⟩

lemma epi_toUnit {k : Type} [Field k] (W : Over (Sp k)) [Nonempty W.left] : Epi (toUnit W) := by
  have : Flat W.hom := inferInstance
  have : Surjective W.hom := inferInstance
  have : Epi W.hom := Flat.epi_of_flat_of_surjective _
  have : Epi (toUnit W).left := by
    have h := Over.w (toUnit W)
    have h' : (toUnit W).left = W.hom := (Category.comp_id _).symm.trans h
    rw [h']
    assumption
  exact Over.epi_of_epi_left _

lemma mono_constDesc {k : Type} [Field k] {I : Type} {A : Over (Sp k)}
    (x : I → (𝟙_ (Over (Sp k)) ⟶ A)) (hx : Function.Injective x) : Mono (constDesc x) := by
  refine ⟨fun {Z} f g h => hom_ext_local f g fun z => ?_⟩
  obtain ⟨V, hV, c, hc⟩ := locally_const f z
  obtain ⟨W, hW, d, hd⟩ := locally_const g z
  have hc' := const_of_le (inf_le_left : V ⊓ W ≤ V) hc
  have hd' := const_of_le (inf_le_right : V ⊓ W ≤ W) hd
  have : Nonempty (openObj Z (V ⊓ W)).left := ⟨(⟨z, hV, hW⟩ : (V ⊓ W : Z.left.Opens))⟩
  have := epi_toUnit (openObj Z (V ⊓ W))
  obtain rfl : c = d := by
    apply hx
    rw [← cancel_epi (toUnit (openObj Z (V ⊓ W))), ← constPt_desc x c, ← constPt_desc x d,
      ← reassoc_of% hc', ← reassoc_of% hd', h]
  exact ⟨V ⊓ W, ⟨hV, hW⟩, hc'.trans hd'.symm⟩

lemma exists_grpObj_constObj {I : Type} {A : Over S} [GrpObj A] (x : I → (𝟙_ (Over S) ⟶ A))
    [Mono (constDesc x)] (C : Subgroup (𝟙_ (Over S) ⟶ A)) (hC : Set.range x = C) :
    ∃ _ : GrpObj (constObj S I), IsMonHom (constDesc x) := by
  have mem : ∀ c, x c ∈ C := fun c => hC.le ⟨c, rfl⟩
  obtain ⟨c₀, h₀⟩ := hC.ge C.one_mem
  obtain ⟨m, hm⟩ := exists_lift x
    ((fst _ _ ≫ constDesc x) * (snd _ _ ≫ constDesc x)) fun z => by
      obtain ⟨V, hV, c, hc⟩ := locally_const_desc x (fst _ _) z
      obtain ⟨W, hW, d, hd⟩ := locally_const_desc x (snd _ _) z
      obtain ⟨a, ha⟩ := hC.ge (C.mul_mem (mem c) (mem d))
      refine ⟨V ⊓ W, ⟨hV, hW⟩, a, ?_⟩
      rw [MonObj.comp_mul, const_of_le inf_le_left hc, const_of_le inf_le_right hd, ha,
        MonObj.comp_mul]
  obtain ⟨n, hn⟩ := exists_lift x (constDesc x)⁻¹ fun z => by
      obtain ⟨V, hV, c, hc⟩ := locally_const_desc x (𝟙 _) z
      obtain ⟨a, ha⟩ := hC.ge (C.inv_mem (mem c))
      refine ⟨V, hV, a, ?_⟩
      rw [Category.id_comp] at hc
      rw [GrpObj.comp_inv, hc, ha, GrpObj.comp_inv]
  exact exists_grpObj_of_mono _ (constPt S c₀) m n ((constPt_desc x c₀).trans h₀) hm hn

lemma comp_eq_of_invariant {I : Type} {A B Y : Over S} [GrpObj A] [GrpObj B]
    (x : I → (𝟙_ (Over S) ⟶ A)) (q : A ⟶ B) [IsMonHom q]
    (hker : IsPullback (constDesc x) (toUnit _) q η[B]) (f : A ⟶ Y)
    (hf : ∀ c, ((toUnit A ≫ x c) * 𝟙 A) ≫ f = f) {Z : Over S} (g g' : Z ⟶ A)
    (h : g ≫ q = g' ≫ q) : g ≫ f = g' ≫ f := by
  have h1 : (g / g') ≫ q = toUnit Z ≫ η[B] := by
    rw [GrpObj.div_comp, h, div_self', Hom.one_def]
  refine hom_ext_local _ _ fun z => ?_
  obtain ⟨V, hV, c, hc⟩ := locally_const_desc x (hker.lift (g / g') (toUnit Z) h1) z
  refine ⟨V, hV, ?_⟩
  rw [hker.lift_fst, GrpObj.comp_div, div_eq_iff_eq_mul] at hc
  rw [← Category.assoc, hc]
  conv_rhs => rw [← hf c, ← Category.assoc, ← Category.assoc, MonObj.comp_mul, Category.comp_id,
    ← Category.assoc, toUnit_unique (_ ≫ toUnit A) (toUnit _)]

lemma existsUnique_desc {A B Y : Over S} (q : A ⟶ B) [Flat q.left] [Surjective q.left]
    [QuasiCompact q.left] (f : A ⟶ Y)
    (hf : ∀ {Z : Over S} (g g' : Z ⟶ A), g ≫ q = g' ≫ q → g ≫ f = g' ≫ f) :
    ∃! f' : B ⟶ Y, q ≫ f' = f := by
  have hc : ∀ {Z : Scheme.{0}} (g g' : Z ⟶ A.left), g ≫ q.left = g' ≫ q.left →
      g ≫ f.left = g' ≫ f.left := by
    intro Z g g' h
    have hw : g' ≫ A.hom = g ≫ A.hom := by
      rw [← Over.w q, ← Category.assoc, ← h, Category.assoc]
    have := hf (Z := Over.mk (g ≫ A.hom))
      (Over.homMk g rfl) (Over.homMk g' hw) (Over.OverMorphism.ext h)
    exact congrArg CommaMorphism.left this
  have hfac := EffectiveEpi.fac q.left f.left hc
  let β : B ⟶ Y := Over.homMk (EffectiveEpi.desc q.left f.left hc) (by
    rw [← cancel_epi q.left, ← Category.assoc, hfac, Over.w, Over.w])
  have hβ : q ≫ β = f := Over.OverMorphism.ext hfac
  have : Epi q := Over.epi_of_epi_left q
  exact ⟨β, hβ, fun β' h' => by rw [← cancel_epi q, h', hβ]⟩

end PointQuot

open PointQuot in

theorem exists_quotient_by_finite_group_of_points :
    Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ P.A)), Finite C → ∃ (B : Over (Sp k)) (_ : GrpObj B) (ψ : P.A ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ P.A, x ≫ ψ = 1 ↔ x ∈ C) ∧ ∀ (Y : Over (Sp k)) (f : P.A ⟶ Y), (∀ x ∈ C, ((toUnit P.A ≫ x) * 𝟙 P.A) ≫ f = f) → ∃! f' : B ⟶ Y, ψ ≫ f' = f := by
  intro L k _ _ P C hC
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin C
  let x : Fin n → (𝟙_ (Over (Sp k)) ⟶ P.A) := fun c => (e.symm c).1
  have hx : Function.Injective x := Subtype.val_injective.comp e.symm.injective
  have hr : Set.range x = C := by
    ext y
    exact ⟨by rintro ⟨c, rfl⟩; exact (e.symm c).2, fun hy => ⟨e ⟨y, hy⟩, by simp [x]⟩⟩
  have mem : ∀ c, x c ∈ C := fun c => hr.le ⟨c, rfl⟩
  have hmono := mono_constDesc x hx
  obtain ⟨_, hi⟩ := exists_grpObj_constObj x C hr
  have hs : FinEt.IsSplitOfRank (constObj (Sp k) (Fin n)).hom n :=
    (FinEt.isSplitOfRank_iff_exists_iso _ _).mpr ⟨Iso.refl _, Category.id_comp _⟩
  have het := hs.etale
  obtain ⟨B, _, hB, q, hq, hfin, hflat, hsurj, hker⟩ :=
    L.quotient k P (constObj (Sp k) (Fin n)) (constDesc x) hi hmono hs.isFinite inferInstance
  have hw : constDesc x ≫ q = 1 := hker.w
  refine ⟨B, inferInstance, q, hB, hq, hfin, ?_, hsurj, fun y => ⟨fun hy => ?_, fun hy => ?_⟩,
    fun Y f hf => existsUnique_desc q f
      (comp_eq_of_invariant x q hker f fun c => hf _ (mem c))⟩
  · refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback (constDesc x) q hker).map (Over.forget _)).flip
      ⟨⟨hsurj, hflat⟩, inferInstanceAs (QuasiCompact q.left)⟩ ?_
    exact MorphismProperty.of_isPullback (P := @Etale) (IsPullback.of_hasPullback _ _) het
  · obtain ⟨z⟩ : Nonempty (𝟙_ (Over (Sp k))).left := inferInstanceAs (Nonempty (PrimeSpectrum k))
    obtain ⟨V, hV, c, hc⟩ := locally_const_desc x (hker.lift y (toUnit _) hy) z
    have : Nonempty (openObj _ V).left := ⟨(⟨z, hV⟩ : V)⟩
    have := epi_toUnit (openObj _ V)
    rw [hker.lift_fst, toUnit_unique (openι _ V) (toUnit _), cancel_epi] at hc
    exact hc ▸ mem c
  · obtain ⟨c, rfl⟩ := hr.ge hy
    rw [← constPt_desc x c, Category.assoc, hw, MonObj.comp_one]

end GlobalTheory

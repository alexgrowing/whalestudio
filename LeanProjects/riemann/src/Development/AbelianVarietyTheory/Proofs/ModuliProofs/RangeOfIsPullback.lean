import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkSetPull

theorem range_of_isPullback {P X Y Z : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {c : X ⟶ Z} {d : Y ⟶ Z}
    (h : IsPullback a b c d) : Set.range a = c ⁻¹' Set.range d := by
  rw [← AlgebraicGeometry.Scheme.Pullback.range_fst c d]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨h.isoPullback.hom q, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩
  · rintro ⟨q, rfl⟩
    exact ⟨h.isoPullback.inv q, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]⟩

theorem exists_equiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G), ∀ x, (ρ x).left = x.left ≫ φ := by
  refine ⟨{ toFun := fun x => Over.homMk (x.left ≫ φ) (by rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x]; rfl)
            invFun := fun y => Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _)
            left_inv := fun x => by
              apply Over.OverMorphism.ext
              apply h.1.hom_ext
              · exact h.1.lift_fst _ _ _
              · exact (h.1.lift_snd _ _ _).trans (Over.w x).symm
            right_inv := fun y => by
              apply Over.OverMorphism.ext
              exact h.1.lift_fst _ _ _
            map_mul' := fun x y => by
              apply Over.OverMorphism.ext
              exact (h.2 T x y _ _ rfl rfl).symm }, fun x => rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} {t : SAB H S}
  {t' : SAB H S'} {f : S' ⟶ S}

theorem heckeKer_iff (D : Datum H) (P : Ideal (𝓞 E)) (p i : ℕ) (m : SABMap t' t f) (T : Over S')
    (C' : Subgroup (T ⟶ t'.G)) (C : Subgroup (Over.mk (T.hom ≫ f) ⟶ t.G))
    (h : ∀ (u : T ⟶ t'.G) (v : Over.mk (T.hom ≫ f) ⟶ t.G), v.left = u.left ≫ m.φ → (u ∈ C' ↔ v ∈ C)) :
    t'.HeckeKer T D P p i C' ↔ t.HeckeKer (Over.mk (T.hom ≫ f)) D P p i C := by
  obtain ⟨ρ, hρ⟩ := exists_equiv m.cart T
  have hC : ∀ u, u ∈ C' ↔ ρ u ∈ C := fun u => h u (ρ u) (hρ u)
  have hact : ∀ u a, ρ (u ≫ t'.act.act a) = ρ u ≫ t.act.act a := by
    intro u a
    apply Over.OverMorphism.ext
    rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, Category.assoc]
    exact congrArg (u.left ≫ ·) (m.act a)
  have htors : ∀ I u, u ∈ t'.tors T I ↔ ρ u ∈ t.tors (Over.mk (T.hom ≫ f)) I := by
    intro I u
    simp only [SAB.tors, Set.mem_ofPred_eq]
    refine forall₂_congr fun a _ => ?_
    rw [← hact, map_eq_one_iff ρ ρ.injective]
  have hL : LBIso t'.PP.L (t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hW : ∀ u v, Out.WeilIs t'.G t'.PP.L ((p : ℤ) ^ 2) u v 1 ↔ Out.WeilIs t.G t.PP.L ((p : ℤ) ^ 2) (ρ u) (ρ v) 1 :=
    fun u v => GlobalTheory.weilIs_iff_of_isGrpPullback_comm S S' t.G t'.G f m.φ t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB m.cart hL
      T _ u v (ρ u) (ρ v) 1 (hρ u) (hρ v)
  have cC : Nat.card C' = Nat.card C := Nat.card_congr (ρ.toEquiv.subtypeEquiv hC)
  have cT : ∀ I, Nat.card (t'.tors T I) = Nat.card (t.tors (Over.mk (T.hom ≫ f)) I) :=
    fun I => Nat.card_congr (ρ.toEquiv.subtypeEquiv (htors I))
  have cI : ∀ I, Nat.card ((C' : Set (T ⟶ t'.G)) ∩ t'.tors T I : Set (T ⟶ t'.G)) =
      Nat.card ((C : Set (Over.mk (T.hom ≫ f) ⟶ t.G)) ∩ t.tors (Over.mk (T.hom ≫ f)) I : Set (Over.mk (T.hom ≫ f) ⟶ t.G)) :=
    fun I => Nat.card_congr (ρ.toEquiv.subtypeEquiv fun u => (hC u).and (htors I u))
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx a
      obtain ⟨u, rfl⟩ := ρ.surjective x
      rw [← hact]
      exact (hC _).mp (h1 u ((hC u).mpr hx) a)
    · intro J hJ x hx
      obtain ⟨u, rfl⟩ := ρ.surjective x
      exact (hC u).mp (h2 J hJ ((htors J u).mpr hx))
    · intro x hx
      obtain ⟨u, rfl⟩ := ρ.surjective x
      exact (htors _ u).mp (h3 ((hC u).mpr hx))
    · intro x hx y hy
      obtain ⟨u, rfl⟩ := ρ.surjective x
      obtain ⟨v, rfl⟩ := ρ.surjective y
      exact (hW u v).mp (h4 u ((hC u).mpr hx) v ((hC v).mpr hy))
    · rw [← cC]
      exact h5
    · rw [← cT, ← cI]
      exact h6
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu a
      rw [hC, hact]
      exact h1 _ ((hC u).mp hu) a
    · intro J hJ u hu
      exact (hC u).mpr (h2 J hJ ((htors J u).mp hu))
    · intro u hu
      exact (htors _ u).mpr (h3 ((hC u).mp hu))
    · intro u hu v hv
      exact (hW u v).mpr (h4 _ ((hC u).mp hu) _ ((hC v).mp hv))
    · rw [cC]
      exact h5
    · rw [cT, cI]
      exact h6

theorem heckeSet_pull (D : Datum H) (P : Ideal (𝓞 E)) (p i : ℕ) (m : SABMap t' t f) (K : Set t.G.left)
    (hK : HeckeSet D t P p i K) : HeckeSet D t' P p i (m.φ ⁻¹' K) := by
  intro k _ _ x
  obtain ⟨C, hCK, hC⟩ := hK k (x ≫ f)
  obtain ⟨ρ, hρ⟩ := exists_equiv m.cart (Over.mk x)
  refine ⟨C.comap ρ.toMonoidHom, fun z => ?_, ?_⟩
  · show ρ z ∈ C ↔ _
    rw [hCK, hρ]
    simp only [Set.range_subset_iff, Set.mem_preimage, Scheme.Hom.comp_apply]
    exact Iff.rfl
  · refine (heckeKer_iff D P p i m (Over.mk x) _ C ?_).mpr hC
    intro u v huv
    obtain rfl : v = ρ u := Over.OverMorphism.ext (huv.trans (hρ u).symm)
    exact Iff.rfl

theorem etSet_pull {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom f)
    (K : Set G.left) (hK : EtSet G K) : EtSet G' (φ ⁻¹' K) := by
  obtain ⟨C, j, hfin, het, hcl, hCK⟩ := hK
  have w : (pullback.fst C.hom f ≫ j.left) ≫ G.hom = pullback.snd C.hom f ≫ f := by
    rw [Category.assoc, Over.w j, pullback.condition]
  let j' : Over.mk (pullback.snd C.hom f) ⟶ G' :=
    Over.homMk (h.lift (pullback.fst C.hom f ≫ j.left) (pullback.snd C.hom f) w) (h.lift_snd _ _ _)
  have sq : IsPullback (pullback.fst C.hom f) j'.left j.left φ := by
    refine IsPullback.of_bot (v₂₁ := G'.hom) (v₂₂ := G.hom) (h₃₁ := f) ?_ (h.lift_fst _ _ _).symm h
    have e : j'.left ≫ G'.hom = pullback.snd C.hom f := h.lift_snd _ _ _
    rw [e, Over.w j]
    exact IsPullback.of_hasPullback C.hom f
  refine ⟨Over.mk (pullback.snd C.hom f), j', ?_, ?_, ?_, ?_⟩
  · show IsFinite (pullback.snd C.hom f)
    infer_instance
  · show Etale (pullback.snd C.hom f)
    infer_instance
  · exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq hcl
  · rw [range_of_isPullback sq.flip, hCK]

theorem lists_pull {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (K : Set G.left) (N n : ℕ) (σ : Fin n → (𝟙_ (Over S) ⟶ G)) (hK : Lists N σ K) :
    ∃ σ' : Fin n → (𝟙_ (Over S') ⟶ G'), (∀ j, (σ' j).left ≫ φ = f ≫ (σ j).left) ∧ Lists N σ' (φ ⁻¹' K) := by
  obtain ⟨ρ, hρ⟩ := exists_equiv h (𝟙_ (Over S'))
  let σ' : Fin n → (𝟙_ (Over S') ⟶ G') := fun j => ρ.symm (toUnit _ ≫ σ j)
  have key : ∀ j, (σ' j).left ≫ φ = f ≫ (σ j).left := by
    intro j
    rw [← hρ, MulEquiv.apply_symm_apply, Over.comp_left, Over.toUnit_left]
    simp [Over.tensorUnit_hom]
  have sq : ∀ j, IsPullback (σ' j).left f φ (σ j).left := by
    intro j
    refine (IsPullback.of_bot (v₂₁ := G'.hom) (v₂₂ := G.hom) (h₃₁ := f) ?_ (key j).symm h.1).flip
    rw [Over.w (σ' j), Over.w (σ j)]
    simp only [Over.tensorUnit_hom]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  refine ⟨σ', key, ?_, ?_, ?_⟩
  · intro j
    apply ρ.injective
    rw [map_pow, MulEquiv.apply_symm_apply, ← MonObj.comp_pow, hK.1 j, MonObj.comp_one, map_one]
  · rw [hK.2.1, Set.preimage_iUnion]
    exact Set.iUnion_congr fun j => (range_of_isPullback (sq j)).symm
  · intro k _ _ x i j hij
    apply hK.2.2 k (x ≫ f)
    have e := congrArg (· ≫ φ) hij
    simp only [Category.assoc, key] at e
    simpa only [Category.assoc] using e

end GlobalTheory.HkSetPull

theorem GlobalTheory.heckeSets_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f), IsProper t.G.hom → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S') (C' : Subgroup (Over.mk x ⟶ t'.G)) (C : Subgroup (Over.mk (x ≫ f) ⟶ t.G)), (∀ (u : Over.mk x ⟶ t'.G) (v : Over.mk (x ≫ f) ⟶ t.G), v.left = u.left ≫ m.φ → (u ∈ C' ↔ v ∈ C)) → (t'.HeckeKer (Over.mk x) D 𝔓 p i C' ↔ t.HeckeKer (Over.mk (x ≫ f)) D 𝔓 p i C)) ∧ ∀ K : Set t.G.left, (HeckeSet D t 𝔓 p i K → HeckeSet D t' 𝔓 p i (m.φ ⁻¹' K)) ∧ (EtSet t.G K → EtSet t'.G (m.φ ⁻¹' K)) ∧ ∀ (N n : ℕ) (σ : Fin n → (𝟙_ (Over S) ⟶ t.G)), Lists N σ K → ∃ σ' : Fin n → (𝟙_ (Over S') ⟶ t'.G), (∀ j, (σ' j).left ≫ m.φ = f ≫ (σ j).left) ∧ Lists N σ' (m.φ ⁻¹' K) := by
  intro E _ _ _ H D 𝔓 p i S S' t t' f m _
  exact ⟨fun k _ _ x C' C h => GlobalTheory.HkSetPull.heckeKer_iff D 𝔓 p i m (Over.mk x) C' C h,
    fun K => ⟨fun hK => GlobalTheory.HkSetPull.heckeSet_pull D 𝔓 p i m K hK,
      fun hK => GlobalTheory.HkSetPull.etSet_pull m.cart.1 K hK,
      fun N n σ hK => GlobalTheory.HkSetPull.lists_pull m.cart K N n σ hK⟩⟩

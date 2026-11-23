import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapEqKerIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDataOfCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafGlueOfOpenImmersionsStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

namespace GlobalTheory.HilbGlue

section
variable {S Z : Scheme.{0}} (z : Z ⟶ S)

theorem bc_fst {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    bc z c g k w ≫ pullback.fst z g = pullback.fst z k := by
  simp only [bc, pullback.map, pullback.lift_fst, Category.comp_id]

theorem bc_snd {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    bc z c g k w ≫ pullback.snd z g = pullback.snd z k ≫ c := by
  simp only [bc, pullback.map, pullback.lift_snd]

end

theorem isFinFlatRk_of_cover {V Y : Scheme.{0}} (g : V ⟶ Y) (𝒰 : Y.OpenCover) (r : ℕ)
    (h : ∀ i, ∃ (Q : Scheme.{0}) (p : Q ⟶ V) (q : Q ⟶ 𝒰.X i), IsPullback p q g (𝒰.f i) ∧ IsFinFlatRk q r) :
    IsFinFlatRk g r := by
  choose Q p q hP hq using h
  have i1 : IsZariskiLocalAtTarget @IsFinite.{0} := by
    set_option backward.isDefEq.respectTransparency.types false in exact inferInstance
  have i2 : IsZariskiLocalAtTarget @Flat.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0})
  have hq' : ∀ i, IsFinFlatRk (pullback.snd g (𝒰.f i)) r := fun i => by
    rw [← (hP i).isoPullback_inv_snd]
    exact (hq i).iso_comp _
  have hF : IsFinite g := IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) 𝒰 fun i => (hq' i).1
  have hL : Flat g := IsZariskiLocalAtTarget.of_openCover (P := @Flat) 𝒰 fun i => (hq' i).2.1
  refine ⟨hF, hL, fun y => ?_⟩
  obtain ⟨i, y', rfl⟩ := 𝒰.exists_eq y
  rw [← Scheme.Hom.finrank_of_isPullback (p i) (q i) g (𝒰.f i) (hP i) y', (hq i).2.2]

theorem HPt.exists_glue : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x : ∀ i, GlobalTheory.HilbGlue.HPt z r (𝒰.X i)), (∀ i j (R : Scheme.{0}) (b : R ⟶ 𝒰.X i) (c : R ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → GlobalTheory.HilbGlue.HPt.map b (x i) = GlobalTheory.HilbGlue.HPt.map c (x j)) → ∃ y : GlobalTheory.HilbGlue.HPt z r Y, ∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) y = x i := by
  intro S Z z r Y 𝒰 x hx
  obtain ⟨f, hf⟩ : ∃ f : Y ⟶ S, ∀ i, 𝒰.f i ≫ f = (x i).1 :=
    ⟨𝒰.glueMorphisms (fun i => (x i).1) fun i j =>
      congrArg Sigma.fst (hx i j _ _ _ pullback.condition), fun i => 𝒰.ι_glueMorphisms _ _ i⟩
  let e : ∀ i, pullback z (x i).1 ⟶ pullback z f := fun i => bc z (𝒰.f i) f (x i).1 (hf i)
  have hP : ∀ i, IsPullback (e i) (pullback.snd z (x i).1) (pullback.snd z f) (𝒰.f i) :=
    fun i => isPullback_bc z _ _ _ (hf i)
  have he : ∀ i, IsOpenImmersion (e i) := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hP i).flip inferInstance
  have hcov : ∀ p : ↥(pullback z f), ∃ i, p ∈ Set.range (e i) := by
    intro p
    obtain ⟨i, y', hy'⟩ := 𝒰.exists_eq (pullback.snd z f p)
    obtain ⟨q, hq⟩ : p ∈ Set.range (pullback.fst (pullback.snd z f) (𝒰.f i)) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨y', hy'⟩
    refine ⟨i, (hP i).isoPullback.inv q, ?_⟩
    rw [← hq, ← Scheme.Hom.comp_apply, (hP i).isoPullback_inv_fst]
  have fi : ∀ i, e i ≫ pullback.fst z f = pullback.fst z (x i).1 := fun i => by
    simp only [e, bc, pullback.map, pullback.lift_fst, Category.comp_id]
  have hK : ∀ i j (Q : Scheme.{0}) (a : Q ⟶ pullback z (x i).1) (b : Q ⟶ pullback z (x j).1),
      a ≫ e i = b ≫ e j → (x i).2.1.comap a = (x j).2.1.comap b := by
    intro i j Q a b hab
    have hbc : (a ≫ pullback.snd z (x i).1) ≫ 𝒰.f i = (b ≫ pullback.snd z (x j).1) ≫ 𝒰.f j := by
      rw [Category.assoc, Category.assoc, ← (hP i).w, ← (hP j).w, reassoc_of% hab]
    have H := hx i j Q _ _ hbc
    have w : (a ≫ pullback.snd z (x i).1) ≫ (x i).1 = (b ≫ pullback.snd z (x j).1) ≫ (x j).1 :=
      congrArg Sigma.fst H
    have H' := (HPt.map_eq_mk_iff _ (x i) w ((x j).2.pull _ rfl)).1 H
    have hs : (a ≫ pullback.fst z (x i).1) ≫ z = 𝟙 Q ≫ (b ≫ pullback.snd z (x j).1) ≫ (x j).1 := by
      rw [Category.id_comp, ← w, Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨s, hs1, hs2⟩ : ∃ s : Q ⟶ pullback z ((b ≫ pullback.snd z (x j).1) ≫ (x j).1),
        s ≫ pullback.fst _ _ = a ≫ pullback.fst z (x i).1 ∧ s ≫ pullback.snd _ _ = 𝟙 Q :=
      ⟨pullback.lift _ _ hs, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have hfst : a ≫ pullback.fst z (x i).1 = b ≫ pullback.fst z (x j).1 := by
      rw [← fi i, ← fi j, reassoc_of% hab]
    have ha : a = s ≫ bc z (a ≫ pullback.snd z (x i).1) (x i).1 _ w := by
      apply pullback.hom_ext
      · rw [Category.assoc, bc_fst, hs1]
      · rw [Category.assoc, bc_snd, reassoc_of% hs2]
    have hb : b = s ≫ bc z (b ≫ pullback.snd z (x j).1) (x j).1 _ rfl := by
      apply pullback.hom_ext
      · rw [Category.assoc, bc_fst, hs1, hfst]
      · rw [Category.assoc, bc_snd, reassoc_of% hs2]
    have e1 : (x i).2.1.comap a = ((x i).2.1.comap (bc z (a ≫ pullback.snd z (x i).1) (x i).1 _ w)).comap s := by
      rw [← Scheme.IdealSheafData.comap_comp, ← ha]
    have e2 : (x j).2.1.comap b = ((x j).2.1.comap (bc z (b ≫ pullback.snd z (x j).1) (x j).1 _ rfl)).comap s := by
      rw [← Scheme.IdealSheafData.comap_comp, ← hb]
    rw [e1, e2, H']
    rfl
  obtain ⟨I, hI⟩ := GlobalTheory.T.exists_idealSheafData_glue_of_openImmersions GlobalTheory.T.exists_idealSheafData_of_compatible_ideals (ι := 𝒰.I₀) (fun i : 𝒰.I₀ => pullback z (x i).1) e he hcov (fun i : 𝒰.I₀ => (x i).2.1) hK
  have hfr : IsFinFlatRk (I.subschemeι ≫ pullback.snd z f) r := by
    refine isFinFlatRk_of_cover _ 𝒰 r fun i => ⟨(I.comap (e i)).subscheme, _, _,
      (isPullback_comap I (e i)).flip.paste_vert (hP i), ?_⟩
    have := (x i).2.2
    rw [← hI i] at this
    exact this
  refine ⟨⟨f, I, hfr⟩, fun i => ?_⟩
  exact (HPt.map_eq_mk_iff (𝒰.f i) ⟨f, I, hfr⟩ (hf i) (x i).2).2 (hI i)

end GlobalTheory.HilbGlue

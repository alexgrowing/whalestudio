import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHomExtensionSemiAbelianNormal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

open GlobalTheory

noncomputable section

namespace GlobalTheory.HomExtNormal

open GlobalTheory.HomExt

theorem exists_common_point {A₁ A₂ Y : Scheme.{0}} (c₁ : A₁ ⟶ Y) (c₂ : A₂ ⟶ Y) (x₁ : A₁) (x₂ : A₂)
    (h : c₁ x₁ = c₂ x₂) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (e₁ : Sp Ω ⟶ A₁) (e₂ : Sp Ω ⟶ A₂),
      e₁ ≫ c₁ = e₂ ≫ c₂ ∧ x₁ ∈ Set.range e₁ ∧ x₂ ∈ Set.range e₂ := by
  obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback (f := c₁) (g := c₂) x₁ x₂ h
  let Ω := AlgebraicClosure ((pullback c₁ c₂).residueField z)
  let r : Sp Ω ⟶ Sp ((pullback c₁ c₂).residueField z) :=
    spMap (algebraMap ((pullback c₁ c₂).residueField z) Ω)
  let y : Sp Ω ⟶ pullback c₁ c₂ := r ≫ (pullback c₁ c₂).fromSpecResidueField z
  have hy : y default = z :=
    (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply z _)
  refine ⟨Ω, inferInstance, inferInstance, y ≫ pullback.fst _ _, y ≫ pullback.snd _ _,
    by simp [pullback.condition], ⟨default, ?_⟩, ⟨default, ?_⟩⟩
  · exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ hy)
  · exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ hy)

section Pull

variable {X T T' : Scheme.{0}}

abbrev pullMap (r : T' ⟶ T) (τ : T ⟶ X) (τ' : T' ⟶ X) (h : r ≫ τ = τ') (G : Over X) :
    pullback G.hom τ' ⟶ pullback G.hom τ :=
  pullback.lift (pullback.fst G.hom τ') (pullback.snd G.hom τ' ≫ r)
    (by rw [pullback.condition, Category.assoc, h])

theorem pullMap_fst (r : T' ⟶ T) (τ : T ⟶ X) (τ' : T' ⟶ X) (h : r ≫ τ = τ') (G : Over X) :
    pullMap r τ τ' h G ≫ pullback.fst G.hom τ = pullback.fst G.hom τ' := pullback.lift_fst _ _ _

theorem pullMap_snd (r : T' ⟶ T) (τ : T ⟶ X) (τ' : T' ⟶ X) (h : r ≫ τ = τ') (G : Over X) :
    pullMap r τ τ' h G ≫ pullback.snd G.hom τ = pullback.snd G.hom τ' ≫ r :=
  pullback.lift_snd _ _ _

theorem pull_left_fst (r : T' ⟶ T) (τ : T ⟶ X) (τ' : T' ⟶ X) (h : r ≫ τ = τ') {G G' : Over X}
    (e : (Over.pullback τ').obj G ≅ (Over.pullback r).obj ((Over.pullback τ).obj G))
    (e' : (Over.pullback τ').obj G' ≅ (Over.pullback r).obj ((Over.pullback τ).obj G'))
    (he : e.hom.left ≫ pullback.fst (pullback.snd G.hom τ) r ≫ pullback.fst G.hom τ =
      pullback.fst G.hom τ')
    (he' : e'.hom.left ≫ pullback.fst (pullback.snd G'.hom τ) r ≫ pullback.fst G'.hom τ =
      pullback.fst G'.hom τ')
    (F : (Over.pullback τ).obj G ⟶ (Over.pullback τ).obj G') :
    (e.hom ≫ (Over.pullback r).map F ≫ e'.inv).left ≫ pullback.fst G'.hom τ' =
      pullMap r τ τ' h G ≫ F.left ≫ pullback.fst G'.hom τ := by
  have w : e.hom.left ≫ pullback.snd (pullback.snd G.hom τ) r = pullback.snd G.hom τ' :=
    Over.w e.hom
  have k : e.hom.left ≫ pullback.fst (pullback.snd G.hom τ) r = pullMap r τ τ' h G := by
    apply pullback.hom_ext
    · rw [Category.assoc, he, pullback.lift_fst]
    · rw [Category.assoc, pullback.condition, reassoc_of% w, pullback.lift_snd]
  have n : e'.inv.left ≫ pullback.fst G'.hom τ' =
      pullback.fst (pullback.snd G'.hom τ) r ≫ pullback.fst G'.hom τ := by
    rw [← he', ← Over.comp_left_assoc, e'.inv_hom_id]; simp
  have l : ((Over.pullback r).map F).left ≫ pullback.fst (pullback.snd G'.hom τ) r =
      pullback.fst (pullback.snd G.hom τ) r ≫ F.left := pullback.lift_fst _ _ _
  simp only [Over.comp_left, Category.assoc]
  rw [n, reassoc_of% l, reassoc_of% k]

theorem exists_pull_hom (r : T' ⟶ T) (τ : T ⟶ X) (τ' : T' ⟶ X) (h : r ≫ τ = τ') {G G' : Over X}
    [GrpObj G] [GrpObj G'] (F : (Over.pullback τ).obj G ⟶ (Over.pullback τ).obj G') [IsMonHom F] :
    ∃ F' : (Over.pullback τ').obj G ⟶ (Over.pullback τ').obj G', IsMonHom F' ∧
      F'.left ≫ pullback.fst G'.hom τ' = pullMap r τ τ' h G ≫ F.left ≫ pullback.fst G'.hom τ := by
  obtain ⟨e, m, he⟩ := exists_iso_pullback_pullback r τ τ' h G
  obtain ⟨e', m', he'⟩ := exists_iso_pullback_pullback r τ τ' h G'
  exact ⟨e.hom ≫ (Over.pullback r).map F ≫ e'.inv, inferInstance,
    pull_left_fst r τ τ' h e e' he he' F⟩

theorem exists_hom_along_trait
    (H : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
      [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'],
      IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶
        (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
    {X U : Scheme.{0}} (j : U ⟶ X) {G G' : Over X} [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') [IsMonHom f]
    (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
    [Algebra T K] [IsFractionRing T K] (t : Sp T ⟶ X) (y : Sp K ⟶ U)
    (hy : y ≫ j = spMap (algebraMap T K) ≫ t) :
    ∃ F : (Over.pullback t).obj G ⟶ (Over.pullback t).obj G', IsMonHom F ∧
      pullMap (spMap (algebraMap T K)) t _ rfl G ≫ F.left ≫ pullback.fst G'.hom t =
        pullMap y j _ hy G ≫ f.left ≫ pullback.fst G'.hom j := by
  set i := spMap (algebraMap T K) with hi
  obtain ⟨e₁, m₁, h₁⟩ := exists_iso_pullback_pullback i t _ rfl G
  obtain ⟨e₃, m₃, h₃⟩ := exists_iso_pullback_pullback i t _ rfl G'
  obtain ⟨f', hf', hff⟩ := exists_pull_hom y j (i ≫ t) hy f
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := H T K _ _ (IsSemiAbelian.pullback t G hG)
    (IsSemiAbelian.pullback t G' hG') (e₁.inv ≫ f' ≫ e₃.hom) inferInstance
  refine ⟨F, hF, ?_⟩
  rw [← hff, ← pull_left_fst i t _ rfl e₁ e₃ h₁ h₃ F, hFf]
  simp

end Pull

theorem hom_eq_of_torsion {Ω : Type} [Field Ω] [IsAlgClosed Ω] {A B : Over (Sp Ω)} [GrpObj A]
    [GrpObj B] (hA : IsSemiAbelian A) (hB : IsSemiAbelian B) (F₁ F₂ : A ⟶ B) [IsMonHom F₁]
    [IsMonHom F₂]
    (h : ∀ (y : 𝟙_ (Over (Sp Ω)) ⟶ A) (n : ℕ), 0 < n → y ^ n = 1 → y ≫ F₁ = y ≫ F₂) :
    F₁ = F₂ := by
  have := hB.comm
  obtain ⟨l, hl, hlk⟩ : ∃ l : ℕ, l.Prime ∧ (l : Ω) ≠ 0 := by
    obtain ⟨p, hp⟩ := CharP.exists Ω
    by_cases h2 : p = 2
    · subst h2
      refine ⟨3, Nat.prime_three, fun h3 ↦ ?_⟩
      have := (CharP.cast_eq_zero_iff Ω 2 3).mp (by exact_mod_cast h3)
      omega
    · refine ⟨2, Nat.prime_two, fun h3 ↦ ?_⟩
      have h4 := (CharP.cast_eq_zero_iff Ω p 2).mp (by exact_mod_cast h3)
      rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h5 | h5
      · exact CharP.char_ne_one Ω p h5
      · exact h2 h5
  have hm : IsMonHom (F₁ * F₂⁻¹) :=
    { one_hom := by
        rw [MonObj.comp_mul, GrpObj.comp_inv, IsMonHom.one_hom, IsMonHom.one_hom, mul_inv_cancel,
          one_eq_one]
      mul_hom := by
        have e (z : A ⊗ A ⟶ A) : z ≫ (F₁ * F₂⁻¹) = z ≫ F₁ * (z ≫ F₂)⁻¹ := by
          rw [MonObj.comp_mul, GrpObj.comp_inv]
        rw [mul_eq_mul, e, MonObj.mul_comp, MonObj.mul_comp, mul_eq_mul, MonObj.comp_mul,
          tensorHom_fst, tensorHom_snd, e, e, mul_inv, _root_.mul_mul_mul_comm] }
  have h1 := GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one Ω A B hA hB l hl hlk (F₁ * F₂⁻¹) hm
    (fun _ _ y a hy ↦ by
      rw [MonObj.comp_mul, GrpObj.comp_inv]
      exact mul_inv_eq_one.mpr (h y (l ^ a) (pow_pos hl.pos a) hy))
  exact mul_inv_eq_one.mp h1

theorem quasiFiniteAt_of_torsion {X : Scheme.{0}} {G G' Γ : Over X} [GrpObj G] [GrpObj G']
    (hG' : IsSemiAbelian G') (p : Γ ⟶ G) (q : Γ ⟶ G') [LocallyOfFiniteType p.left]
    (hext : ∀ {T : Scheme.{0}} (a b : T ⟶ Γ.left), a ≫ p.left = b ≫ p.left →
      a ≫ q.left = b ≫ q.left → a = b)
    (key : ∀ (k : Type) [Field k] (c : Sp k ⟶ Γ.left) (n : ℕ),
      c ≫ (p ^ n).left = c ≫ (1 : Γ ⟶ G).left → c ≫ (q ^ n).left = c ≫ (1 : Γ ⟶ G').left)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ X) (x : Over.mk t ⟶ G) {n : ℕ} (hn : 0 < n)
    (hx : x ^ n = 1) (w : Γ.left) (hw : p.left w ∈ Set.range x.left) :
    p.left.QuasiFiniteAt w := by
  have := finite_torsion_points hG' t hn
  let l : {c : Sp Ω ⟶ Γ.left // c ≫ p.left = x.left} → (Over.mk t ⟶ Γ) := fun c ↦
    Over.homMk c.1 (by
      change c.1 ≫ Γ.hom = t
      have := Over.w x
      rw [← Over.w p, ← Category.assoc, c.2]
      exact this)
  have hl (c) : (l c ≫ q) ^ n = 1 := by
    have e : l c ≫ p = x := Over.OverMorphism.ext c.2
    have h₁ : l c ≫ p ^ n = l c ≫ (1 : Γ ⟶ G) := by
      rw [SemiAbTorsion.comp_pow_points, e, hx, MonObj.comp_one]
    have h₂ : l c ≫ q ^ n = l c ≫ (1 : Γ ⟶ G') :=
      Over.OverMorphism.ext (key Ω c.1 n (congrArg CommaMorphism.left h₁))
    rwa [SemiAbTorsion.comp_pow_points, MonObj.comp_one] at h₂
  have hfin : Finite {c : Sp Ω ⟶ Γ.left // c ≫ p.left = x.left} := by
    refine Finite.of_injective (β := {z : Over.mk t ⟶ G' // z ^ n = 1})
      (fun c ↦ ⟨l c ≫ q, hl c⟩) fun a b h ↦ Subtype.ext (hext _ _ (a.2.trans b.2.symm) ?_)
    exact congrArg (fun u ↦ u.1.left) h
  have hf : (p.left ⁻¹' {p.left w}).Finite :=
    (finite_preimage_of_finite_lifts p.left x.left hfin).subset
      (Set.preimage_mono (Set.singleton_subset_iff.mpr hw))
  have : Finite (p.left.fiber (p.left w)) := (p.left.fiberHomeo (p.left w)).finite_iff.mpr hf
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

theorem isOpenImmersion_quasiFiniteLocus_of_isIntegral {W Γ Y : Scheme.{0}} (i : W ⟶ Γ) (p : Γ ⟶ Y)
    [IsSeparated p] [QuasiCompact p] [LocallyOfFiniteType p] [Surjective p]
    [IsIntegral Y] [IsNormalScheme Y] [IsReduced Γ]
    [IsPreimmersion i] [Flat i] [IsDominant i]
    [IsPreimmersion (i ≫ p)] [Flat (i ≫ p)] [IsDominant (i ≫ p)] [QuasiCompact (i ≫ p)] :
    IsOpenImmersion (p.quasiFiniteLocus.ι ≫ p) := by
  obtain ⟨w₀, hw₀⟩ := genericPoints_subset_range_of_isDominant (i ≫ p)
    (show genericPoint Y ∈ genericPoints Y by simp [genericPoints_eq_singleton])
  have hgen : IsGenericPoint (i w₀) (Set.univ : Set Γ) := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← i.denseRange.closure_range]
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨w, rfl⟩
    have h : w₀ ⤳ w := by
      rw [← (i ≫ p).isEmbedding.isInducing.specializes_iff, hw₀]
      exact genericPoint_specializes _
    exact specializes_iff_mem_closure.mp (h.map i.continuous)
  have : IrreducibleSpace Γ := (irreducibleSpace_def Γ).mpr hgen.isIrreducible
  have : IsIntegral Γ := isIntegral_of_irreducibleSpace_of_isReduced Γ
  have he : i w₀ = genericPoint Γ := hgen.eq (genericPoint_spec Γ)
  have : IsIso (p.stalkMap (genericPoint Γ)) := by
    rw [← he]
    have h₁ := isIso_stalkMap_of_flat_of_surjectiveOnStalks (i ≫ p) w₀
    have h₂ := isIso_stalkMap_of_flat_of_surjectiveOnStalks i w₀
    rw [Scheme.Hom.stalkMap_comp] at h₁
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (i.stalkMap w₀) h₂ h₁
  have := isIso_fromNormalization_of_birational p (fun y ↦ inferInstance)
  have e : p.quasiFiniteLocus.ι ≫ p =
      (p.quasiFiniteLocus.ι ≫ p.toNormalization) ≫ p.fromNormalization := by
    rw [Category.assoc, p.toNormalization_fromNormalization]
  rw [e]
  infer_instance

theorem isOpenImmersion_quasiFiniteLocus {W Γ Y : Scheme.{0}} (i : W ⟶ Γ) (p : Γ ⟶ Y)
    [IsSeparated p] [QuasiCompact p] [LocallyOfFiniteType p] [Surjective p]
    [IsLocallyNoetherian Y] [IsNormalScheme Y] [IsReduced Γ]
    [IsPreimmersion i] [Flat i] [IsDominant i]
    [IsPreimmersion (i ≫ p)] [Flat (i ≫ p)] [IsDominant (i ≫ p)] [QuasiCompact (i ≫ p)] :
    IsOpenImmersion (p.quasiFiniteLocus.ι ≫ p) := by
  let V : Y → Y.Opens := fun y ↦ ⟨irreducibleComponent y,
    IsNormalScheme.isOpen_of_mem_irreducibleComponents
      (irreducibleComponent_mem_irreducibleComponents y)⟩
  have hV : iSup V = ⊤ := by
    rw [eq_top_iff]
    exact fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, mem_irreducibleComponent⟩
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsOpenImmersion) V hV).mpr fun y ↦ ?_
  have : IrreducibleSpace (V y).toScheme :=
    Subtype.irreducibleSpace (isIrreducible_irreducibleComponent (x := y))
  have : IsIntegral (V y).toScheme := IsNormalScheme.isIntegral_of_irreducibleSpace _
  have e : (i ≫ p) ∣_ V y = i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y := morphismRestrict_comp _ _ _
  have : IsPreimmersion (i ∣_ (p ⁻¹ᵁ V y)) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : IsDominant (i ∣_ (p ⁻¹ᵁ V y)) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : IsPreimmersion (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) := e ▸ IsZariskiLocalAtTarget.restrict ‹_› _
  have : IsDominant (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) := e ▸ IsZariskiLocalAtTarget.restrict ‹_› _
  have : Flat (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) :=
    e ▸ MorphismProperty.of_isPullback (isPullback_morphismRestrict (i ≫ p) (V y)).flip ‹_›
  have : QuasiCompact (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) :=
    e ▸ MorphismProperty.of_isPullback (isPullback_morphismRestrict (i ≫ p) (V y)).flip ‹_›
  have : Surjective (p ∣_ V y) := IsZariskiLocalAtTarget.restrict ‹_› _
  have hint := isOpenImmersion_quasiFiniteLocus_of_isIntegral (i ∣_ (p ⁻¹ᵁ V y)) (p ∣_ V y)
  rw [morphismRestrict_comp]
  set Q' := (p ∣_ V y).quasiFiniteLocus with hQ'
  set a := p.quasiFiniteLocus.ι ∣_ (p ⁻¹ᵁ V y) with ha
  have hr : Set.range a ⊆ Set.range Q'.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (p ∣_ V y).QuasiFiniteAt (a x)
    rw [← Scheme.Hom.quasiFiniteAt_comp_iff (g := (V y).ι), morphismRestrict_ι,
      Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion]
    have hx : (p ⁻¹ᵁ V y).ι (a x) = p.quasiFiniteLocus.ι ((p.quasiFiniteLocus.ι ⁻¹ᵁ (p ⁻¹ᵁ V y)).ι x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ha, morphismRestrict_ι]
    rw [hx]
    exact (((p.quasiFiniteLocus.ι ⁻¹ᵁ (p ⁻¹ᵁ V y)).ι x)).2
  let b := IsOpenImmersion.lift Q'.ι a hr
  have hb : b ≫ Q'.ι = a := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (b ≫ Q'.ι) := by rw [hb]; infer_instance
  have : IsOpenImmersion b := IsOpenImmersion.of_comp b Q'.ι
  rw [← hb, Category.assoc]
  exact @IsOpenImmersion.comp _ _ _ b (Q'.ι ≫ p ∣_ V y) _ hint

theorem existsUnique_hom_extension_of_dvr
    (H : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
      [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'],
      IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶
        (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f))
    (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X) (hX : Geo.Tor.IsNormalScheme X)
    [IsOpenImmersion j] [IsDominant j] (G G' : Over X) [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') (hf : IsMonHom f) :
    ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f := by
  have := hG.smooth
  have := hG'.smooth
  have := hG.quasiCompact
  have := hG'.quasiCompact
  have := hG'.separated
  have : GlobalTheory.IsNormalScheme X := (GlobalTheory.isNormalScheme_iff X).mpr hX
  have : GlobalTheory.IsNormalScheme G.left := (GlobalTheory.isNormalScheme_iff _).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth G.hom hX)
  have : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  let u : pullback G.hom j ⟶ G.left := pullback.fst G.hom j
  let φ : pullback G.hom j ⟶ G'.left := f.left ≫ pullback.fst G'.hom j
  have hw : f.left ≫ pullback.snd G'.hom j = pullback.snd G.hom j := Over.w f
  have huφ : u ≫ G.hom = φ ≫ G'.hom := by
    rw [Category.assoc, pullback.condition, pullback.condition, reassoc_of% hw]
  have : IsDominant u := isDominant_pullback_fst_of_isOpenMap j G.hom G.hom.isOpenMap
  have : IsPreimmersion u := inferInstanceAs (IsPreimmersion (pullback.fst G.hom j))
  have : Flat u := inferInstanceAs (Flat (pullback.fst G.hom j))
  have : QuasiCompact u := inferInstanceAs (QuasiCompact (pullback.fst G.hom j))
  have hus := isIso_stalkMap_of_flat_of_surjectiveOnStalks u
  have : GlobalTheory.IsNormalScheme (pullback G.hom j) := GlobalTheory.IsNormalScheme.of_isIso_stalkMap u
  let Γ := graphClosure G.hom G'.hom u φ huφ
  let p : Γ ⟶ G.left := graphClosure.fst G.hom G'.hom u φ huφ
  let q : Γ ⟶ G'.left := graphClosure.snd G.hom G'.hom u φ huφ
  let i : pullback G.hom j ⟶ Γ := graphClosure.incl G.hom G'.hom u φ huφ
  have hip : i ≫ p = u := graphClosure.incl_fst ..
  have hiq : i ≫ q = φ := graphClosure.incl_snd ..
  have hpq : p ≫ G.hom = q ≫ G'.hom := graphClosure.condition ..
  have hpb := graphClosure.isPullback_incl G.hom G'.hom u φ huφ
  have : IsPreimmersion i := MorphismProperty.of_isPullback hpb ‹IsPreimmersion u›
  have : Flat i := MorphismProperty.of_isPullback hpb ‹Flat u›
  have : QuasiCompact i := graphClosure.quasiCompact_incl ..
  have : IsSchemeTheoreticallyDominant i := graphClosure.schemeDominant_incl ..
  have : IsDominant i := inferInstance
  have : IsReduced Γ := graphClosure.isReduced ..
  have : LocallyOfFiniteType p := graphClosure.locallyOfFiniteType_fst ..
  have : QuasiCompact p := graphClosure.quasiCompact_fst ..
  have : IsSeparated p := graphClosure.isSeparated_fst ..
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : IsLocallyNoetherian Γ := LocallyOfFiniteType.isLocallyNoetherian p
  have : Surjective p := by
    refine ⟨fun σ ↦ ?_⟩
    rcases mem_range_or_exists_dvr u σ with ⟨w, rfl⟩ | ⟨T, _, _, _, a, c, hc, rfl⟩
    · exact ⟨i w, by rw [← Scheme.Hom.comp_apply, hip]⟩
    obtain ⟨F, s, -, -, hs₂, hs⟩ := exists_hom_along_dvr H j hG hG' f T _ a c hc
    have := schemeTheoreticallyDominant_fractionField T (FractionRing T)
    have hF : F.left ≫ pullback.snd G'.hom (a ≫ G.hom) = pullback.snd G.hom (a ≫ G.hom) := Over.w F
    obtain ⟨l, ⟨hl, -⟩, -⟩ := graphClosure.existsUnique_lift G.hom G'.hom u φ huφ a
      (s ≫ F.left ≫ pullback.fst G'.hom (a ≫ G.hom))
      (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hF, reassoc_of% hs₂])
      (spMap (algebraMap T (FractionRing T))) c hc.symm hs
    exact ⟨l (IsLocalRing.closedPoint T), by rw [← hl]; rfl⟩
  let Γ' : Over X := Over.mk (p ≫ G.hom)
  let p' : Γ' ⟶ G := Over.homMk p rfl
  let q' : Γ' ⟶ G' := Over.homMk q hpq.symm
  have : LocallyOfFiniteType p'.left := ‹LocallyOfFiniteType p›
  have key : ∀ (k : Type) [Field k] (x : Sp k ⟶ Γ'.left) (n : ℕ),
      x ≫ (p' ^ n).left = x ≫ (1 : Γ' ⟶ G).left → x ≫ (q' ^ n).left = x ≫ (1 : Γ' ⟶ G').left := by
    intro k _ x n hx
    rcases mem_range_or_exists_dvr i (x default) with hw | ⟨T, _, _, _, a, c, hc, ha⟩
    · obtain ⟨c, rfl⟩ := exists_lift_of_range_subset i x (by
        rintro _ ⟨t, rfl⟩
        rwa [Subsingleton.elim t default])
      exact comp_pow_eq_one_of_pullback_hom j f p' q' _ c
        (by rw [Category.assoc]; exact congrArg (c ≫ ·) hip.symm)
        (by rw [Category.assoc]; exact congrArg (c ≫ ·) hiq.symm) n hx
    obtain ⟨F, s, _, hs₁, hs₂, hs⟩ := exists_hom_along_dvr H j hG hG' f T _ (a ≫ p) c
      (by rw [← reassoc_of% hc, hip])
    have := schemeTheoreticallyDominant_fractionField T (FractionRing T)
    have hF : F.left ≫ pullback.snd G'.hom ((a ≫ p) ≫ G.hom) =
      pullback.snd G.hom ((a ≫ p) ≫ G.hom) := Over.w F
    have hb : s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom) = a ≫ q := by
      have := over_ext_of_schemeTheoreticallyDominant (Y := Over.mk ((a ≫ p) ≫ G.hom)) (X := G')
        (spMap (algebraMap T (FractionRing T)))
        (a := Over.homMk (s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom)) (by
          change (s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom)) ≫ G'.hom = (a ≫ p) ≫ G.hom
          rw [Category.assoc s, Category.assoc F.left, pullback.condition, reassoc_of% hF,
            reassoc_of% hs₂]))
        (b := Over.homMk (a ≫ q) (by
          change (a ≫ q) ≫ G'.hom = (a ≫ p) ≫ G.hom
          rw [Category.assoc, Category.assoc, hpq]))
        (hs.trans (by
          change _ = spMap (algebraMap T (FractionRing T)) ≫ a ≫ q
          rw [← reassoc_of% hc, hiq]))
      exact congrArg CommaMorphism.left this
    let r : Sp (IsLocalRing.ResidueField T) ⟶ Sp T := spMap (IsLocalRing.residue T)
    have hr : x default ∈ Set.range (r ≫ a) := by
      refine ⟨IsLocalRing.closedPoint _, ?_⟩
      exact (Scheme.Hom.comp_apply r a _).trans
        ((congrArg a (IsLocalRing.comap_closedPoint (IsLocalRing.residue T))).trans ha)
    rw [field_point_comp_eq_iff _ _ x _ ⟨default, rfl⟩,
      ← field_point_comp_eq_iff (Z := Γ'.left) _ _ (r ≫ a) _ hr] at hx ⊢
    exact comp_pow_eq_one_of_pullback_hom _ F p' q' (r ≫ a) (r ≫ s)
      (by rw [Category.assoc, hs₁, Category.assoc]; rfl)
      (by rw [Category.assoc, hb, Category.assoc]; rfl) n hx
  have : IsPreimmersion (i ≫ p) := by rwa [hip]
  have : Flat (i ≫ p) := by rwa [hip]
  have : IsDominant (i ≫ p) := by rwa [hip]
  have : QuasiCompact (i ≫ p) := by rwa [hip]
  have hQ : IsOpenImmersion (p.quasiFiniteLocus.ι ≫ p) := isOpenImmersion_quasiFiniteLocus i p
  have hgraph : ∀ w : Γ, ∃ (T : Scheme.{0}) (τ : T ⟶ X)
      (F : (Over.pullback τ).obj G ⟶ (Over.pullback τ).obj G') (l : pullback G.hom τ ⟶ Γ)
      (x : ↥(pullback G.hom τ)), IsMonHom F ∧ l ≫ p = pullback.fst G.hom τ ∧
        l ≫ q = F.left ≫ pullback.fst G'.hom τ ∧ l x = w := by
    intro w
    rcases mem_range_or_exists_dvr i w with ⟨c, rfl⟩ | ⟨T, _, _, _, a, c, hc, rfl⟩
    · exact ⟨U, j, f, i, c, hf, hip, hiq, rfl⟩
    have := schemeTheoreticallyDominant_fractionField T (FractionRing T)
    set iK := spMap (algebraMap T (FractionRing T)) with hiK
    let t : Sp T ⟶ X := (a ≫ p) ≫ G.hom
    let y : Sp (FractionRing T) ⟶ U := c ≫ pullback.snd G.hom j
    have h0 : c ≫ u = iK ≫ a ≫ p := by rw [← hip, reassoc_of% hc]
    have hy : y ≫ j = iK ≫ t := by
      change (c ≫ pullback.snd G.hom j) ≫ j = iK ≫ (a ≫ p) ≫ G.hom
      rw [Category.assoc, ← pullback.condition]
      simpa [u] using congrArg (· ≫ G.hom) h0
    obtain ⟨F, hF, hFf⟩ := exists_hom_along_trait H j hG hG' f T (FractionRing T) t y hy
    have hFw : F.left ≫ pullback.snd G'.hom t = pullback.snd G.hom t := Over.w F
    let d : pullback (pullback.snd G.hom t) iK ⟶ pullback G.hom t := pullback.fst _ _
    have : IsDominant d := isDominant_pullback_fst_of_isOpenMap iK (pullback.snd G.hom t)
      (pullback.snd G.hom t).isOpenMap
    have : GlobalTheory.IsNormalScheme (pullback G.hom t) := (GlobalTheory.isNormalScheme_iff _).mpr
      (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (pullback.snd G.hom t)
        ((GlobalTheory.isNormalScheme_iff _).mp inferInstance))
    have : IsSchemeTheoreticallyDominant d := IsSchemeTheoreticallyDominant.of_isDominant d
    let v : pullback (pullback.snd G.hom t) iK ⟶ pullback G.hom (iK ≫ t) :=
      pullback.lift (d ≫ pullback.fst G.hom t) (pullback.snd _ iK) (by
        change (pullback.fst _ _ ≫ pullback.fst G.hom t) ≫ G.hom = _
        rw [Category.assoc, pullback.condition, reassoc_of% (pullback.condition (f := pullback.snd G.hom t) (g := iK))])
    have hv₁ : v ≫ pullback.fst G.hom (iK ≫ t) = d ≫ pullback.fst G.hom t :=
      pullback.lift_fst _ _ _
    have hv₂ : v ≫ pullback.snd G.hom (iK ≫ t) = pullback.snd _ iK := pullback.lift_snd _ _ _
    have hv : v ≫ pullMap iK t _ rfl G = d := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullMap_fst, hv₁]
      · rw [Category.assoc, pullMap_snd, reassoc_of% hv₂]
        exact pullback.condition.symm
    let ρ := pullMap y j _ hy G
    have hρ₁ : ρ ≫ pullback.fst G.hom j = pullback.fst G.hom (iK ≫ t) := pullMap_fst ..
    have hρ₂ : ρ ≫ pullback.snd G.hom j = pullback.snd G.hom (iK ≫ t) ≫ y := pullMap_snd ..
    have hw₁ : d ≫ pullback.fst G.hom t = (v ≫ ρ) ≫ u := by
      change _ = (v ≫ ρ) ≫ pullback.fst G.hom j
      rw [Category.assoc, hρ₁, hv₁]
    have hw₂ : d ≫ F.left ≫ pullback.fst G'.hom t = (v ≫ ρ) ≫ φ := by
      rw [← hv, Category.assoc, Category.assoc, hFf]
    have hcond : pullback.fst G.hom t ≫ G.hom = (F.left ≫ pullback.fst G'.hom t) ≫ G'.hom := by
      rw [Category.assoc, pullback.condition, pullback.condition, reassoc_of% hFw]
    obtain ⟨l, ⟨hl₁, hl₂⟩, -⟩ := graphClosure.existsUnique_lift G.hom G'.hom u φ huφ
      (pullback.fst G.hom t) (F.left ≫ pullback.fst G'.hom t) hcond d (v ≫ ρ) hw₁ hw₂
    let s : Sp T ⟶ pullback G.hom t := pullback.lift (a ≫ p) (𝟙 _) (by simp [t])
    have hs₁ : s ≫ pullback.fst G.hom t = a ≫ p := pullback.lift_fst _ _ _
    have hs₂ : s ≫ pullback.snd G.hom t = 𝟙 _ := pullback.lift_snd _ _ _
    have hq : s ≫ F.left ≫ pullback.fst G'.hom t = a ≫ q := by
      let v' : Sp (FractionRing T) ⟶ pullback G.hom (iK ≫ t) :=
        pullback.lift (iK ≫ a ≫ p) (𝟙 _) (by simp [t])
      have hv'₁ : v' ≫ pullback.fst G.hom (iK ≫ t) = iK ≫ a ≫ p := pullback.lift_fst _ _ _
      have hv'₂ : v' ≫ pullback.snd G.hom (iK ≫ t) = 𝟙 _ := pullback.lift_snd _ _ _
      have h₁ : v' ≫ pullMap iK t _ rfl G = iK ≫ s := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullMap_fst, hv'₁, Category.assoc, hs₁]
        · rw [Category.assoc, pullMap_snd, reassoc_of% hv'₂, Category.assoc, hs₂, Category.comp_id]
      have h₂ : v' ≫ ρ = c := by
        apply pullback.hom_ext
        · rw [Category.assoc, hρ₁, hv'₁]
          exact h0.symm
        · rw [Category.assoc, hρ₂, reassoc_of% hv'₂]
      have h₃ : iK ≫ s ≫ F.left ≫ pullback.fst G'.hom t = iK ≫ a ≫ q := by
        rw [← reassoc_of% h₁, hFf, reassoc_of% h₂, ← reassoc_of% hc, hiq]
      have := over_ext_of_schemeTheoreticallyDominant (Y := Over.mk t) (X := G') iK
        (a := Over.homMk (s ≫ F.left ≫ pullback.fst G'.hom t) (by
          change (s ≫ F.left ≫ pullback.fst G'.hom t) ≫ G'.hom = t
          rw [Category.assoc s, Category.assoc F.left, pullback.condition, reassoc_of% hFw,
            reassoc_of% hs₂]))
        (b := Over.homMk (a ≫ q) (by
          change (a ≫ q) ≫ G'.hom = (a ≫ p) ≫ G.hom
          rw [Category.assoc, Category.assoc, hpq]))
        h₃
      exact congrArg CommaMorphism.left this
    have hsl : s ≫ l = a := by
      refine graphClosure.hom_ext G.hom G'.hom u φ huφ ?_ ?_
      · change (s ≫ l) ≫ p = a ≫ p
        rw [Category.assoc, hl₁, hs₁]
      · change (s ≫ l) ≫ q = a ≫ q
        rw [Category.assoc, hl₂, hq]
    exact ⟨Sp T, t, F, l, s (IsLocalRing.closedPoint T), hF, hl₁, hl₂,
      (Scheme.Hom.comp_apply s l _).symm.trans (by rw [hsl])⟩
  have hinj : ∀ w₁ w₂ : Γ, p w₁ = p w₂ → w₁ = w₂ := by
    intro w₁ w₂ hw₁₂
    obtain ⟨T₁, τ₁, F₁, l₁, x₁, m₁, a₁, b₁, rfl⟩ := hgraph w₁
    obtain ⟨T₂, τ₂, F₂, l₂, x₂, m₂, a₂, b₂, rfl⟩ := hgraph w₂
    have hx : pullback.fst G.hom τ₁ x₁ = pullback.fst G.hom τ₂ x₂ := by
      rw [← a₁, ← a₂, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact hw₁₂
    obtain ⟨Ω, _, _, e₁, e₂, he, ⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := exists_common_point _ _ x₁ x₂ hx
    let τ : Sp Ω ⟶ X := e₁ ≫ pullback.fst G.hom τ₁ ≫ G.hom
    have h₁ : (e₁ ≫ pullback.snd G.hom τ₁) ≫ τ₁ = τ := by
      rw [Category.assoc, ← pullback.condition]
    have h₂ : (e₂ ≫ pullback.snd G.hom τ₂) ≫ τ₂ = τ := by
      rw [Category.assoc, ← pullback.condition, ← reassoc_of% he]
    obtain ⟨F₁', m₁', c₁⟩ := exists_pull_hom _ τ₁ τ h₁ F₁
    obtain ⟨F₂', m₂', c₂⟩ := exists_pull_hom _ τ₂ τ h₂ F₂
    let g₁ := pullMap _ τ₁ τ h₁ G ≫ l₁
    let g₂ := pullMap _ τ₂ τ h₂ G ≫ l₂
    have hg₁p : g₁ ≫ p = pullback.fst G.hom τ := by
      change (pullMap _ τ₁ τ h₁ G ≫ l₁) ≫ p = _
      rw [Category.assoc, a₁, pullMap_fst]
    have hg₂p : g₂ ≫ p = pullback.fst G.hom τ := by
      change (pullMap _ τ₂ τ h₂ G ≫ l₂) ≫ p = _
      rw [Category.assoc, a₂, pullMap_fst]
    have hg₁q : g₁ ≫ q = F₁'.left ≫ pullback.fst G'.hom τ := by
      rw [c₁, Category.assoc, b₁]
    have hg₂q : g₂ ≫ q = F₂'.left ≫ pullback.fst G'.hom τ := by
      rw [c₂, Category.assoc, b₂]
    have hF : F₁' = F₂' := by
      refine hom_eq_of_torsion (IsSemiAbelian.pullback τ G hG) (IsSemiAbelian.pullback τ G' hG')
        F₁' F₂' fun y n hn hy ↦ ?_
      let e := TorsionLift.ptsEquiv τ G (𝟙_ (Over (Sp Ω))) τ (Category.id_comp _)
      have hx : (e y) ^ n = 1 := by rw [← map_pow, hy, map_one]
      have hxl : (e y).left = y.left ≫ pullback.fst G.hom τ := TorsionLift.ptsEquiv_left ..
      have hqf : ∀ z : Sp Ω ⟶ Γ, z ≫ p = (e y).left →
          Set.range z ⊆ Set.range p.quasiFiniteLocus.ι := by
        rintro z hz _ ⟨s, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact quasiFiniteAt_of_torsion hG' p' q'
          (fun a b ↦ graphClosure.hom_ext G.hom G'.hom u φ huφ) key τ (e y) hn hx (z s)
          ⟨s, by rw [← hz]; exact (Scheme.Hom.comp_apply _ _ _).symm⟩
      let z₁ : Sp Ω ⟶ Γ := y.left ≫ g₁
      let z₂ : Sp Ω ⟶ Γ := y.left ≫ g₂
      have hz₁ : z₁ ≫ p = (e y).left := by
        change (y.left ≫ g₁) ≫ p = _
        rw [Category.assoc, hg₁p, hxl]
      have hz₂ : z₂ ≫ p = (e y).left := by
        change (y.left ≫ g₂) ≫ p = _
        rw [Category.assoc, hg₂p, hxl]
      let z₁' := IsOpenImmersion.lift p.quasiFiniteLocus.ι z₁ (hqf z₁ hz₁)
      let z₂' := IsOpenImmersion.lift p.quasiFiniteLocus.ι z₂ (hqf z₂ hz₂)
      have hz₁' : z₁' ≫ p.quasiFiniteLocus.ι = z₁ := IsOpenImmersion.lift_fac _ _ _
      have hz₂' : z₂' ≫ p.quasiFiniteLocus.ι = z₂ := IsOpenImmersion.lift_fac _ _ _
      have hz' : z₁' = z₂' := by
        rw [← cancel_mono (p.quasiFiniteLocus.ι ≫ p), reassoc_of% hz₁', reassoc_of% hz₂', hz₁, hz₂]
      have hz : z₁ = z₂ := by rw [← hz₁', ← hz₂', hz']
      apply Over.OverMorphism.ext
      change y.left ≫ F₁'.left = y.left ≫ F₂'.left
      have hw₁ : F₁'.left ≫ pullback.snd G'.hom τ = pullback.snd G.hom τ := Over.w F₁'
      have hw₂ : F₂'.left ≫ pullback.snd G'.hom τ = pullback.snd G.hom τ := Over.w F₂'
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, ← hg₁q, ← hg₂q]
        exact congrArg (· ≫ q) (by simpa [z₁, z₂] using hz)
      · rw [Category.assoc, Category.assoc, hw₁, hw₂]
    have hg : g₁ = g₂ := by
      refine graphClosure.hom_ext G.hom G'.hom u φ huφ ?_ ?_
      · exact hg₁p.trans hg₂p.symm
      · refine hg₁q.trans (hF ▸ hg₂q.symm)
    let b : Sp Ω ⟶ pullback G.hom τ := pullback.lift (e₁ ≫ pullback.fst G.hom τ₁) (𝟙 _) (by simp [τ])
    have hbf : b ≫ pullback.fst G.hom τ = e₁ ≫ pullback.fst G.hom τ₁ := pullback.lift_fst _ _ _
    have hbs : b ≫ pullback.snd G.hom τ = 𝟙 _ := pullback.lift_snd _ _ _
    have hb₁ : b ≫ pullMap _ τ₁ τ h₁ G = e₁ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullMap_fst, hbf]
      · rw [Category.assoc, pullMap_snd, reassoc_of% hbs]
    have hb₂ : b ≫ pullMap _ τ₂ τ h₂ G = e₂ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullMap_fst, hbf, he]
      · rw [Category.assoc, pullMap_snd, reassoc_of% hbs]
    have hl : e₁ ≫ l₁ = e₂ ≫ l₂ := by
      rw [← hb₁, ← hb₂, Category.assoc, Category.assoc]
      exact congrArg (b ≫ ·) hg
    rw [Subsingleton.elim s₂ s₁]
    simp only [← Scheme.Hom.comp_apply]
    rw [hl]
  have : LocallyQuasiFinite p := locallyQuasiFinite_iff_finite_preimage_singleton.mpr fun σ ↦
    Set.Subsingleton.finite fun a ha b hb ↦ hinj a b (ha.trans hb.symm)
  have : IsIso p := isIso_of_densePart i p
  obtain ⟨ψ, hψ, huψ⟩ := graphClosure.exists_extension_of_isIso_fst G.hom G'.hom u φ huφ
  let F : G ⟶ G' := Over.homMk ψ hψ.symm
  have hF : (Over.pullback j).map F = f := by
    ext1
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans huψ
    · exact (Over.w _).trans hw.symm
  refine ⟨F, ⟨?_, hF⟩, fun F' hF' ↦ pullback_map_injective_of_flat j (hF'.2.trans hF.symm)⟩
  have : IsMonHom ((Over.pullback j).map F) := hF ▸ hf
  exact isMonHom_of_pullback_of_flat j F

end GlobalTheory.HomExtNormal

open GlobalTheory.TorRef in

theorem GlobalTheory.homExtNormal : HomExtNormalSt :=
  fun X U _ j hX _ _ G G' _ _ hG hG' f hf ↦
    GlobalTheory.HomExtNormal.existsUnique_hom_extension_of_dvr GlobalTheory.homExtension_semiAbelian_dvr X U j hX
      G G' hG hG' f hf

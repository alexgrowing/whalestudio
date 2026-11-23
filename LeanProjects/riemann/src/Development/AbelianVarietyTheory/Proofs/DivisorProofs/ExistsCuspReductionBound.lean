import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsBasic
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem chains_shortExact_of_free : ∀ (R : Type) [CommRing R] {X₁ X₂ X₃ X₄ : Scheme.{0}} (a : X₁ ⟶ X₂) (b : X₁ ⟶ X₃) (c : X₂ ⟶ X₄) (d : X₃ ⟶ X₄) (w₁ : biprod.lift ((free R).map (yoneda.map a)) (-(free R).map (yoneda.map b)) ≫ biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d)) = 0) (w₂ : biprod.lift ((chains R).map (sch.map a)) (-(chains R).map (sch.map b)) ≫ biprod.desc ((chains R).map (sch.map c)) ((chains R).map (sch.map d)) = 0), (ShortComplex.mk _ _ w₁).ShortExact → (ShortComplex.mk _ _ w₂).ShortExact := by
  intro R _ X₁ X₂ X₃ X₄ a b c d w₁ w₂ h
  obtain ⟨hLE, hnat, -⟩ := chains_basic R
  have hm : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (p : ℕ), ((chains R).map (sch.map f)).f (-(p : ℤ)) ≫ (chainsXIso R (sch.obj Y) p).hom =
      (chainsXIso R (sch.obj X) p).hom ≫ (free R).map (yoneda.map f) := fun f p => hnat (sch.map f) p
  let e : ∀ (X : Scheme.{0}) (p : ℕ), ((chains R).obj (sch.obj X)).X (-(p : ℤ)) ≅ (free R).obj (yoneda.obj X) :=
    fun X p => chainsXIso R (sch.obj X) p
  have he : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (p : ℕ), ((chains R).map (sch.map f)).f (-(p : ℤ)) ≫ (e Y p).hom =
      (e X p).hom ≫ (free R).map (yoneda.map f) := fun f p => hm f p
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  rcases (show (∃ p : ℕ, n = -(p : ℤ)) ∨ 0 < n from by
    by_cases hn : 0 < n
    · exact Or.inr hn
    · exact Or.inl ⟨(-n).toNat, by omega⟩) with ⟨p, rfl⟩ | hn
  · have c1 : (e X₁ p).hom ≫ biprod.lift ((free R).map (yoneda.map a)) (-(free R).map (yoneda.map b)) =
        (biprod.lift ((chains R).map (sch.map a)) (-(chains R).map (sch.map b))).f (-(p : ℤ)) ≫
          ((HomologicalComplex.biprodXIso _ _ _).hom ≫ biprod.map (e X₂ p).hom (e X₃ p).hom) := by
      apply biprod.hom_ext
      · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst, HomologicalComplex.biprodXIso_hom_fst_assoc]
        rw [← HomologicalComplex.comp_f_assoc, biprod.lift_fst, he]
      · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd, HomologicalComplex.biprodXIso_hom_snd_assoc]
        rw [← HomologicalComplex.comp_f_assoc, biprod.lift_snd, HomologicalComplex.neg_f_apply, Preadditive.neg_comp, he,
          Preadditive.comp_neg]
    have c2 : ((HomologicalComplex.biprodXIso _ _ _).hom ≫ biprod.map (e X₂ p).hom (e X₃ p).hom) ≫
        biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d)) =
        (biprod.desc ((chains R).map (sch.map c)) ((chains R).map (sch.map d))).f (-(p : ℤ)) ≫ (e X₄ p).hom := by
      rw [Category.assoc, ← Iso.eq_inv_comp]
      apply biprod.hom_ext'
      · simp only [biprod.inl_map_assoc, biprod.inl_desc, HomologicalComplex.inl_biprodXIso_inv_assoc]
        rw [← HomologicalComplex.comp_f_assoc, biprod.inl_desc, he]
      · simp only [biprod.inr_map_assoc, biprod.inr_desc, HomologicalComplex.inr_biprodXIso_inv_assoc]
        rw [← HomologicalComplex.comp_f_assoc, biprod.inr_desc, he]
    refine ShortComplex.shortExact_of_iso ?_ h
    refine (ShortComplex.isoMk (e X₁ p)
      (HomologicalComplex.biprodXIso _ _ _ ≪≫ biprod.mapIso (e X₂ p) (e X₃ p))
      (e X₄ p) ?_ ?_).symm
    · exact c1
    · exact c2
  · have z : ∀ X : Scheme.{0}, IsZero (((chains R).obj (sch.obj X)).X n) := fun X =>
      have := hLE (sch.obj X); CochainComplex.isZero_of_isStrictlyLE _ 0 n hn
    have z₂ : IsZero ((((chains R).obj (sch.obj X₂)) ⊞ ((chains R).obj (sch.obj X₃))).X n) :=
      IsZero.of_iso ((biprod_isZero_iff _ _).2 ⟨z X₂, z X₃⟩) (HomologicalComplex.biprodXIso _ _ _)
    exact
      { exact := ShortComplex.exact_of_isZero_X₂ _ z₂
        mono_f := ⟨fun _ _ _ => (z X₁).eq_of_tgt _ _⟩
        epi_g := ⟨fun _ _ _ => (z X₄).eq_of_src _ _⟩ }

end GlobalTheory.EtC

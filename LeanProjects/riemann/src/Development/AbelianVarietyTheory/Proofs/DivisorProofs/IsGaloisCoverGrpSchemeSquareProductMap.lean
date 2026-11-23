import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke.ProdGalois
variable {S : Scheme.{0}}

theorem transl_lift_fst {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A) ≫ fst A A = fst A A ≫ transl h₁ := by
  rw [transl, transl, mul_comp, comp_mul, Category.id_comp, Category.comp_id, Category.assoc, lift_fst,
    ← Category.assoc, toUnit_unique (fst A A ≫ toUnit A) (toUnit _)]

theorem transl_lift_snd {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A) ≫ snd A A = snd A A ≫ transl h₂ := by
  rw [transl, transl, mul_comp, comp_mul, Category.id_comp, Category.comp_id, Category.assoc, lift_snd,
    ← Category.assoc, toUnit_unique (snd A A ≫ toUnit A) (toUnit _)]

theorem transl_lift_fst_left {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    (transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A)).left ≫ (fst A A).left = (fst A A).left ≫ (transl h₁).left := by
  rw [← Over.comp_left, transl_lift_fst, Over.comp_left]

theorem transl_lift_snd_left {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    (transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A)).left ≫ (snd A A).left = (snd A A).left ≫ (transl h₂).left := by
  rw [← Over.comp_left, transl_lift_snd, Over.comp_left]

theorem grpScheme_square_hom_ext_fst_snd {A : Over S} {X : Scheme.{0}} {a b : X ⟶ (G2 A).left}
    (h₁ : a ≫ (fst A A).left = b ≫ (fst A A).left) (h₂ : a ≫ (snd A A).left = b ≫ (snd A A).left) : a = b :=
  pullback.hom_ext h₁ h₂

theorem grpSchemeSquareProductMap_comp_fst {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ ≫ (fst A' A').left = (fst A A).left ≫ ψ.left := by
  rw [sq2, ← Over.comp_left, lift_fst, Over.comp_left]

theorem grpSchemeSquareProductMap_comp_snd {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ ≫ (snd A' A').left = (snd A A).left ≫ ψ.left := by
  rw [sq2, ← Over.comp_left, lift_snd, Over.comp_left]

theorem grpSchemeSquareProductMap_eq_pullback_map {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ = pullback.map A.hom A.hom A'.hom A'.hom ψ.left ψ.left (𝟙 S) (by simp) (by simp) := by
  apply grpScheme_square_hom_ext_fst_snd
  · rw [grpSchemeSquareProductMap_comp_fst]; exact (pullback.lift_fst _ _ _).symm
  · rw [grpSchemeSquareProductMap_comp_snd]; exact (pullback.lift_snd _ _ _).symm

end GlobalTheory.UPel.HT.Hecke.ProdGalois

open GlobalTheory.UPel.HT.Hecke.ProdGalois in

theorem GlobalTheory.UPel.HT.Hecke.isGaloisCover_grpSchemeSquareProductMap : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (G : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → GlobalTheory.ZM.IsGaloisCover (G × G) (fun h => (GlobalTheory.UPel.HT.Hecke.transl (lift h.1.1 h.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left) (GlobalTheory.UPel.HT.Hecke.sq2 ψ) := by
  intro S A A' _ _ _ _ G ψ _ hψ
  have := hψ.finite
  have hfin := hψ.fin
  have het := hψ.etale
  have hon := hψ.onto
  refine
    { finite := inferInstance
      one := ?_
      mul := ?_
      inv := ?_
      fin := ?_
      etale := ?_
      onto := ?_
      fibre := ?_ }
  · apply grpScheme_square_hom_ext_fst_snd
    · rw [transl_lift_fst_left, Category.id_comp]
      have e := hψ.one
      rw [show ((1 : G × G).1 : 𝟙_ (Over S) ⟶ A) = ((1 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e, Category.comp_id]
    · rw [transl_lift_snd_left, Category.id_comp]
      have e := hψ.one
      rw [show ((1 : G × G).2 : 𝟙_ (Over S) ⟶ A) = ((1 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e, Category.comp_id]
  · intro a c
    apply grpScheme_square_hom_ext_fst_snd
    · rw [transl_lift_fst_left, Category.assoc, transl_lift_fst_left, reassoc_of% transl_lift_fst_left]
      have e := hψ.mul a.1 c.1
      rw [show ((a * c).1 : 𝟙_ (Over S) ⟶ A) = ((a.1 * c.1 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e]
    · rw [transl_lift_snd_left, Category.assoc, transl_lift_snd_left, reassoc_of% transl_lift_snd_left]
      have e := hψ.mul a.2 c.2
      rw [show ((a * c).2 : 𝟙_ (Over S) ⟶ A) = ((a.2 * c.2 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e]
  · intro a
    apply grpScheme_square_hom_ext_fst_snd
    · rw [Category.assoc, grpSchemeSquareProductMap_comp_fst, reassoc_of% transl_lift_fst_left, hψ.inv a.1]
    · rw [Category.assoc, grpSchemeSquareProductMap_comp_snd, reassoc_of% transl_lift_snd_left, hψ.inv a.2]
  · rw [grpSchemeSquareProductMap_eq_pullback_map]
    exact MorphismProperty.pullback_map (P := @IsFinite) hfin hfin (Over.w ψ).symm (Over.w ψ).symm
  · rw [grpSchemeSquareProductMap_eq_pullback_map]
    haveI : MorphismProperty.IsStableUnderComposition @Etale.{0} := ⟨fun _ _ _ _ ↦ inferInstance⟩
    exact MorphismProperty.pullback_map (P := @Etale) het het (Over.w ψ).symm (Over.w ψ).symm
  · rw [grpSchemeSquareProductMap_eq_pullback_map]
    haveI : MorphismProperty.IsStableUnderComposition @Surjective.{0} := ⟨fun _ _ _ _ ↦ inferInstance⟩
    exact MorphismProperty.pullback_map (P := @Surjective) hon hon (Over.w ψ).symm (Over.w ψ).symm
  · intro K _ _ y y' e
    have e₁ : (y ≫ (fst A A).left) ≫ ψ.left = (y' ≫ (fst A A).left) ≫ ψ.left := by
      rw [Category.assoc, Category.assoc, ← grpSchemeSquareProductMap_comp_fst, reassoc_of% e]
    have e₂ : (y ≫ (snd A A).left) ≫ ψ.left = (y' ≫ (snd A A).left) ≫ ψ.left := by
      rw [Category.assoc, Category.assoc, ← grpSchemeSquareProductMap_comp_snd, reassoc_of% e]
    obtain ⟨a₁, ha₁, hu₁⟩ := hψ.fibre K _ _ e₁
    obtain ⟨a₂, ha₂, hu₂⟩ := hψ.fibre K _ _ e₂
    refine ⟨(a₁, a₂), ?_, ?_⟩
    · apply grpScheme_square_hom_ext_fst_snd
      · rw [Category.assoc, transl_lift_fst_left, ← Category.assoc]; exact ha₁
      · rw [Category.assoc, transl_lift_snd_left, ← Category.assoc]; exact ha₂
    · intro b hb
      refine Prod.ext (hu₁ b.1 ?_) (hu₂ b.2 ?_)
      · show (y ≫ (fst A A).left) ≫ (transl (b.1 : 𝟙_ (Over S) ⟶ A)).left = y' ≫ (fst A A).left
        rw [Category.assoc, ← transl_lift_fst_left _ (b.2 : 𝟙_ (Over S) ⟶ A), ← Category.assoc]
        exact congrArg (· ≫ (fst A A).left) hb
      · show (y ≫ (snd A A).left) ≫ (transl (b.2 : 𝟙_ (Over S) ⟶ A)).left = y' ≫ (snd A A).left
        rw [Category.assoc, ← transl_lift_snd_left (b.1 : 𝟙_ (Over S) ⟶ A), ← Category.assoc]
        exact congrArg (· ≫ (snd A A).left) hb

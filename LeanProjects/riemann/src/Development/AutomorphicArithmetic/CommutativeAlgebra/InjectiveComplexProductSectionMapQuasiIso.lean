import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
import Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveSemiMapOfLocallySurjectiveOnCocycles
import Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveSemiMapOpOfBijectiveCochainPushforward
import Development.AutomorphicArithmetic.CommutativeAlgebra.InjectiveProductPushforwardOfInjective
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsBijectiveCohomologyClassProductAdjunction
import Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonCohomologyClassChainsOfAcyLocallyExa
import Development.AutomorphicArithmetic.CommutativeAlgebra.AcyMappingConeSemiMapOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyMappingConeSecondVariableExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImageCocycleSemilinearSheafComplexMapStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

private theorem rcx_ge (R : Type) [CommRing R] (L : Cx R) [L.IsStrictlyGE 0] :
    ((rcx (Int.castRingHom R)).obj L).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (restr (Int.castRingHom R)).map_isZero (L.isZero_of_isStrictlyGE 0 i hi)

private theorem semi_bij (R : Type) [CommRing R] (L B : Cx R) [L.IsStrictlyGE 0] [B.IsStrictlyGE 0]
    (hL : ∀ s, Injective (L.X s)) (hB : ∀ s, Injective (B.X s)) (ρ : SemiMap L B) (E : Spc)
    (hs : ∀ (T : Scheme.{0}), Nonempty (Sx E 0 T) → ∀ (n : ℤ) (b : Sec (B.X n) T), Sec.map (B.d n (n + 1)) b = 0 →
      Loc T fun V g => ∃ (a : Sec (L.X n) V) (c : Sec (B.X (n - 1)) V), Sec.map (L.d n (n + 1)) a = 0 ∧
        ρ.app V n a = Sec.res g b + Sec.map (B.d (n - 1) n) c)
    (hi : ∀ (T : Scheme.{0}), Nonempty (Sx E 0 T) → ∀ (n : ℤ) (a : Sec (L.X n) T), Sec.map (L.d n (n + 1)) a = 0 →
      (∃ c : Sec (B.X (n - 1)) T, ρ.app T n a = Sec.map (B.d (n - 1) n) c) →
      Loc T fun V g => ∃ a' : Sec (L.X (n - 1)) V, Sec.map (L.d (n - 1) n) a' = Sec.res g a) (n : ℤ) :
    Function.Bijective (ρ.op.app E n) := by
  have gL := rcx_ge R L
  have gB := rcx_ge R B
  apply UpperTheory.bijective_semiMap_op_of_bijective_cochain_pushforward
  haveI hC : (mappingCone ρ.toZ).IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [mappingCone.isZero_X_iff]
    exact ⟨((rcx (Int.castRingHom R)).obj L).isZero_of_isStrictlyGE 0 _ (by omega),
      ((rcx (Int.castRingHom R)).obj B).isZero_of_isStrictlyGE 0 _ (by omega)⟩
  have hQ : ∀ {V U : Scheme.{0}} (a : V ⟶ U), Nonempty (Sx E 0 U) → Nonempty (Sx E 0 V) :=
    fun a ⟨x⟩ => ⟨Sx.res a x⟩
  have hsub : ∀ m, Subsingleton (CohomologyClass ((chains ℤ).obj E) (mappingCone ρ.toZ) m) :=
    UpperTheory.subsingleton_cohomologyClass_chains_of_acy_locally_exact (mappingCone ρ.toZ) (-1) E (UpperTheory.acy_mappingCone_semiMap_of_injective R L B hL hB ρ _)
      (UpperTheory.bijective_semiMap_of_locally_surjective_on_cocycles R L B ρ (fun T => Nonempty (Sx E 0 T)) hQ hs hi)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  constructor
  · have ex := (GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact ℤ ((chains ℤ).obj E) ρ.toZ m).2.2
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (ex x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  · have ex := (GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact ℤ ((chains ℤ).obj E) ρ.toZ (m + 1)).1
    intro x
    exact (ex x).1 (Subsingleton.elim _ _)

theorem UpperTheory.injectiveComplex_productSection_map_quasiIso :
    ∀ (R : Type) [CommRing R] (W : Scheme.{0}) (L I : Cx R) [L.IsStrictlyGE 0] [I.IsStrictlyGE 0],
        (∀ s, Injective (L.X s)) → (∀ s, Injective (I.X s)) →
        ∀ (ψ : ∀ (T : Scheme.{0}) (s : ℤ), Sec (L.X s) T →+ Sec (I.X s) (W ⨯ T)),
        (∀ {T' T : Scheme.{0}} (g : T' ⟶ T) (s : ℤ) (a : Sec (L.X s) T), Sec.res (prod.map (𝟙 W) g) (ψ T s a) = ψ T' s (Sec.res g a)) →
        (∀ (T : Scheme.{0}) (s t : ℤ) (a : Sec (L.X s) T), Sec.map (I.d s t) (ψ T s a) = ψ T t (Sec.map (L.d s t) a)) →
        ∀ Z : Scheme.{0} → Prop, (∀ {T' T : Scheme.{0}}, (T' ⟶ T) → Z T → Z T') →
        (∀ (T : Scheme.{0}), Z T → ∀ (n : ℤ) (b : Sec (I.X n) (W ⨯ T)), Sec.map (I.d n (n + 1)) b = 0 →
          Loc T fun V g => ∃ (a : Sec (L.X n) V) (c : Sec (I.X (n - 1)) (W ⨯ V)), Sec.map (L.d n (n + 1)) a = 0 ∧
            ψ V n a = Sec.res (prod.map (𝟙 W) g) b + Sec.map (I.d (n - 1) n) c) →
        (∀ (T : Scheme.{0}), Z T → ∀ (n : ℤ) (a : Sec (L.X n) T), Sec.map (L.d n (n + 1)) a = 0 →
          (∃ c : Sec (I.X (n - 1)) (W ⨯ T), ψ T n a = Sec.map (I.d (n - 1) n) c) →
          Loc T fun V g => ∃ a' : Sec (L.X (n - 1)) V, Sec.map (L.d (n - 1) n) a' = Sec.res g a) →
        ∀ E : Spc, (∀ T : Scheme.{0}, Nonempty (Sx E 0 T) → Z T) →
        ∃ Φ : ∀ n : ℤ, CohomologyClass ((chains R).obj E) L n →+ CohomologyClass ((chains R).obj (sch.obj W ⨯ E)) I n,
          (∀ n, Function.Bijective (Φ n)) ∧
          ∀ (n : ℤ) (α : Cocycle ((chains R).obj E) L n),
            (∃ β : Cocycle ((chains R).obj (sch.obj W ⨯ E)) I n, Φ n (CohomologyClass.mk α) = CohomologyClass.mk β ∧
              ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (T : Scheme.{0}) (y : Sx (sch.obj W ⨯ E) p T),
                ev β.1 p s h T y = Sec.res (prod.lift (show T ⟶ W from y.map prod.fst) (𝟙 T)) (ψ T s (ev α.1 p s h T (y.map prod.snd)))) := by
  intro R _ W L I _ _ hL hI ψ hψn hψc Z hZ hs hi E hE
  let ρ : SemiMap L (UpperTheory.Bc.Bc W I) :=
    { app := fun T s => ψ T s
      nat := fun g s a => hψn g s a
      comm := fun T s t a => hψc T s t a }
  haveI : (UpperTheory.Bc.Bc W I).IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi'
    exact Functor.map_isZero (UpperTheory.Bc.pw R W) (I.isZero_of_isStrictlyGE 0 i hi')
  have hB : ∀ s, Injective ((UpperTheory.Bc.Bc W I).X s) := fun s => by
    haveI := hI s
    exact UpperTheory.injective_productPushforward_of_injective R W (I.X s)
  have hbij := semi_bij R L (UpperTheory.Bc.Bc W I) hL hB ρ E
    (fun T hT n b hb => hs T (hE T hT) n b hb) (fun T hT n a ha hc => hi T (hE T hT) n a ha hc)
  choose Θ hΘ hΘf using fun n => UpperTheory.exists_bijective_cohomologyClass_product_adjunction R W I E n
  refine ⟨fun n => (Θ n).comp (ρ.op.app E n), fun n => (hΘ n).comp (hbij n), ?_⟩
  intro n α
  obtain ⟨β', hβ'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R R ρ).1 E n α
  have e1 := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R R ρ).2 E n α β' hβ'
  obtain ⟨β, hβ, hβf⟩ := hΘf n β'
  refine ⟨β, ?_, ?_⟩
  · show Θ n (ρ.op.app E n (CohomologyClass.mk α)) = _
    rw [e1, hβ]
  · intro p s h T y
    rw [hβf p s h T y, hβ' p s h T]
    rfl

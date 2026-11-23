import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocallyStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonHypercohomologyFreeOfSuppOfSectionsV
import Development.AutomorphicArithmetic.CommutativeAlgebra.AcyMiddleOfShortExact
import Development.AutomorphicArithmetic.CommutativeAlgebra.AcyRightOfShortExact
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLiftFreeToMiddleOfShortExactAcy
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLiftFreeToKernelOfShortExactVanishingSecti

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

private theorem restriction_trans {F : Shv ℤ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

private theorem res_map_of_sheaf_morphism {F G : Shv ℤ} (φ : F ⟶ G) {V U : Scheme.{0}} (k : V ⟶ U) (b : Sec F U) :
    Sec.res k (Sec.map φ b) = Sec.map φ (Sec.res k b) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private theorem map_map_eq_zero {F G H : Shv ℤ} (φ : F ⟶ G) (ψ : G ⟶ H) (h : φ ≫ ψ = 0) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map ψ (Sec.map φ a) = 0 := by
  have h2 := congrArg (fun t : F ⟶ H => (t.hom.app (op U)).hom a) h
  simpa [Sec.map] using h2

private theorem local_bind {U : Scheme.{0}} {P R : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => R W (k ≫ g)) : Loc U R := by
  obtain ⟨S, hS, hSP⟩ := hP
  choose T hT hTR using fun (V : Scheme.{0}) (g : V ⟶ U) (H : S.arrows g) => h V g (hSP V g H)
  refine ⟨Sieve.bind S.arrows fun Y f H => T Y f H, ?_, ?_⟩
  · exact Scheme.etaleTopology.bind_covering hS fun Y f H => hT Y f H
  · rintro W _ ⟨Y, k, g, H, hk, rfl⟩
    exact hTR Y g H W k hk

theorem UpperTheory.acy_and_lift_of_locally_surjective_exact :
    ∀ (Q : Scheme.{0} → Prop), (∀ {V U : Scheme.{0}}, (V ⟶ U) → Q U → Q V) → ∀ (A C₁ Z : Shv ℤ) (i : A ⟶ C₁) (d : C₁ ⟶ Z) (w : i ≫ d = 0), Mono i → (ShortComplex.mk i d w).Exact → (∀ U : Scheme.{0}, Q U → ∀ b : Sec Z U, Loc U fun V g => ∃ a : Sec C₁ V, Sec.map d a = Sec.res g b) → Acy Q A → Acy Q C₁ → Acy Q Z ∧ ∀ P : PSh, Supp Q P → ∀ f : (free ℤ).obj P ⟶ Z, ∃ h : (free ℤ).obj P ⟶ C₁, h ≫ d = f := by
  intro Q hQ A C₁ Z i d w hi hex hloc hA hC
  have hfac : Abelian.factorThruImage d ≫ Abelian.image.ι d = d := Abelian.image.fac d
  have w1 : i ≫ Abelian.factorThruImage d = 0 := by
    rw [← cancel_mono (Abelian.image.ι d), Category.assoc, hfac, w, zero_comp]
  let S1 := ShortComplex.mk i (Abelian.factorThruImage d) w1
  have hS1ex : S1.Exact := by
    let φ : S1 ⟶ ShortComplex.mk i d w :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := Abelian.image.ι d
        comm₁₂ := by simp [S1]
        comm₂₃ := by simp [S1, hfac] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hex
  have hS1 : S1.ShortExact := { exact := hS1ex, mono_f := hi, epi_g := by dsimp [S1]; infer_instance }
  have w2 : Abelian.image.ι d ≫ cokernel.π d = 0 := by
    rw [← cancel_epi (Abelian.factorThruImage d), ← Category.assoc, hfac, cokernel.condition, comp_zero]
  let S2 := ShortComplex.mk (Abelian.image.ι d) (cokernel.π d) w2
  have hS2 : S2.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
      mono_f := by dsimp [S2]; infer_instance
      epi_g := by dsimp [S2]; infer_instance }
  have hsub : ∀ U : Scheme.{0}, Q U → Subsingleton (Sec (cokernel d) U) := by
    intro U hU
    refine ⟨fun s t => ?_⟩
    have hz : ∀ s : Sec (cokernel d) U, s = 0 := by
      intro s
      have hl := ((GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections ℤ (cokernel.π d)).2.2.1.1 inferInstance) U s
      have hl2 : Loc U fun W k => Sec.res k s = Sec.res k (0 : Sec (cokernel d) U) := by
        refine local_bind hl ?_
        rintro V g ⟨z, hz⟩
        obtain ⟨T, hT, hTz⟩ := hloc V (hQ g hU) z
        refine ⟨T, hT, ?_⟩
        rintro W k hk
        obtain ⟨a, ha⟩ := hTz W k hk
        rw [restriction_trans, ← hz, res_map_of_sheaf_morphism, ← ha, map_map_eq_zero d (cokernel.π d) (cokernel.condition d)]
        simp [Sec.res]
      exact (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ (cokernel d) U).1 s 0 hl2
    rw [hz s, hz t]
  have hI : Acy Q (Abelian.image d) := UpperTheory.acy_right_of_shortExact Q S1 hS1 hA hC
  have hK : Acy Q (cokernel d) := fun P hP n _ => UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish Q _ hsub P hP n
  refine ⟨UpperTheory.acy_middle_of_shortExact Q S2 hS2 hI hK, ?_⟩
  intro P hP f
  obtain ⟨h1, hh1⟩ := UpperTheory.exists_lift_free_to_kernel_of_shortExact_vanishing_sections Q S2 hS2 hsub P hP f
  obtain ⟨h2, hh2⟩ := UpperTheory.exists_lift_free_to_middle_of_shortExact_acy Q S1 hS1 hA P hP h1
  refine ⟨h2, ?_⟩
  dsimp [S1, S2] at hh1 hh2
  rw [← hfac, ← Category.assoc, hh2, hh1]

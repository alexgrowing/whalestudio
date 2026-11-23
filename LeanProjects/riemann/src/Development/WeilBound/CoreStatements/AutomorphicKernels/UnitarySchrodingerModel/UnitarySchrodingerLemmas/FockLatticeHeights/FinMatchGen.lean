import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.MemLatVIff

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SwFinM

section Gen

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] {n : ℕ}

theorem isCO_map (L : AddSubgroup (Fin n → R)) (hL : PositivityTheory.SiegelWeilFormula.Gen.IsCO L) (X Xi : Matrix (Fin n) (Fin n) R)
    (h1 : X * Xi = 1) (h2 : Xi * X = 1) : PositivityTheory.SiegelWeilFormula.Gen.IsCO (L.map (Matrix.mulVecLin X).toAddMonoidHom) := by
  have e : ((L.map (Matrix.mulVecLin X).toAddMonoidHom : AddSubgroup (Fin n → R)) : Set (Fin n → R)) =
      (mulVecHomeo X Xi h1 h2) '' (L : Set (Fin n → R)) := by
    rw [AddSubgroup.coe_map]
    rfl
  unfold PositivityTheory.SiegelWeilFormula.Gen.IsCO
  rw [e]
  exact ⟨(mulVecHomeo X Xi h1 h2).isOpenMap _ hL.1, hL.2.image (mulVecHomeo X Xi h1 h2).continuous⟩

end Gen

section Comp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem matV_mul (v : HeightOneSpectrum (𝓞 F)) (X Y : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    PositivityTheory.SiegelWeilFormula.Gen.matV v (X * Y) = PositivityTheory.SiegelWeilFormula.Gen.matV v X * PositivityTheory.SiegelWeilFormula.Gen.matV v Y := by
  rw [matV_eq, matV_eq, matV_eq, map_mul]

theorem matV_one (v : HeightOneSpectrum (𝓞 F)) :
    PositivityTheory.SiegelWeilFormula.Gen.matV v (1 : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) = 1 := by
  rw [matV_eq, map_one]

theorem finMatchGen {M : ℕ} (a ai a' ai' : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E))
    (ha1 : a * ai = 1) (ha2 : ai * a = 1) (hc1 : a' * ai' = 1) (hc2 : ai' * a' = 1) {d : ℕ}
    (bs : Module.Basis (Fin d) F E) (g : (Fin M → Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
    (gv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ)
    (hP : HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin bs (fun X => g fun i j => X j i) gv)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (L : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (hlam : ∀ v, (lam v).IsAddHaarMeasure) (hL : ∀ v, PositivityTheory.SiegelWeilFormula.Gen.IsCO (L v))
    (hstd : ∀ᶠ v in Filter.cofinite, (L v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO bs v) :
    ∃ (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
      (Φf : (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ),
      (∀ v, PositivityTheory.SiegelWeilFormula.Gen.IsCO (L₁ v) ∧ PositivityTheory.SiegelWeilFormula.Gen.IsCO (L₂ v)) ∧
      (∀ᶠ v in Filter.cofinite,
        (L₁ v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO bs v ∧
        (L₂ v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO bs v) ∧
      HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin bs Φf Φv ∧
      (∀ x : Matrix (Fin M) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E),
        g (fun i j => Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) ((x * a) i j)) =
          Φf (fun c i => Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (x i c))) ∧
      ∀ v (B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)),
        PositivityTheory.SiegelWeilFormula.Gen.nu2 (lam v) (L₁ v) (L₂ v) (PositivityTheory.SiegelWeilFormula.Gen.matV v (a * B * a')) =
          PositivityTheory.SiegelWeilFormula.Gen.nu2 (lam v) (L v) (L v) (PositivityTheory.SiegelWeilFormula.Gen.matV v B) := by
  have hA1 : ∀ v, PositivityTheory.SiegelWeilFormula.Gen.matV v a * PositivityTheory.SiegelWeilFormula.Gen.matV v ai = 1 := fun v => by
    rw [← matV_mul, ha1, matV_one]
  have hA2 : ∀ v, PositivityTheory.SiegelWeilFormula.Gen.matV v ai * PositivityTheory.SiegelWeilFormula.Gen.matV v a = 1 := fun v => by
    rw [← matV_mul, ha2, matV_one]
  have hC1 : ∀ v, PositivityTheory.SiegelWeilFormula.Gen.matV v a' * PositivityTheory.SiegelWeilFormula.Gen.matV v ai' = 1 := fun v => by
    rw [← matV_mul, hc1, matV_one]
  have hC2 : ∀ v, PositivityTheory.SiegelWeilFormula.Gen.matV v ai' * PositivityTheory.SiegelWeilFormula.Gen.matV v a' = 1 := fun v => by
    rw [← matV_mul, hc2, matV_one]
  have hT1 : ∀ v, (PositivityTheory.SiegelWeilFormula.Gen.matV v a)ᵀ * (PositivityTheory.SiegelWeilFormula.Gen.matV v ai)ᵀ = 1 := fun v => by
    rw [← Matrix.transpose_mul, hA2 v, Matrix.transpose_one]
  have hT2 : ∀ v, (PositivityTheory.SiegelWeilFormula.Gen.matV v ai)ᵀ * (PositivityTheory.SiegelWeilFormula.Gen.matV v a)ᵀ = 1 := fun v => by
    rw [← Matrix.transpose_mul, hA1 v, Matrix.transpose_one]
  refine ⟨fun v => (L v).map (Matrix.mulVecLin (PositivityTheory.SiegelWeilFormula.Gen.matV v a)).toAddMonoidHom,
    fun v => (L v).map (Matrix.mulVecLin (PositivityTheory.SiegelWeilFormula.Gen.matV v ai')).toAddMonoidHom,
    fun X => g (fun i j => ∑ c, Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (a c j) * X c i),
    fun v Y => gv v (fun j i => ∑ c, PositivityTheory.SiegelWeilFormula.Gen.matV v a c j * Y c i),
    ?_, ?_, ⟨fun v => ?_, ?_, fun X => ?_⟩, fun x => ?_, fun v B => ?_⟩
  ·
    intro v
    have := GlobalTheory.CompanionTheory.SiegLoc.NuIndex.secondCountable_tens bs v
    exact ⟨isCO_map (L v) (hL v) _ _ (hA1 v) (hA2 v), isCO_map (L v) (hL v) _ _ (hC2 v) (hC1 v)⟩
  ·
    filter_upwards [hstd, intAt_eventually bs, matV_mem_Rv bs a, matV_mem_Rv bs ai,
      matV_mem_Rv bs a', matV_mem_Rv bs ai'] with v hLv hI h1 h2 h3 h4
    constructor
    · refine (AddSubgroup.coe_map _ _).trans ?_
      show (fun y => PositivityTheory.SiegelWeilFormula.Gen.matV v a *ᵥ y) '' (L v : Set _) = _
      rw [hLv]
      exact image_latO hI _ _ h1 h2 (hA1 v)
    · refine (AddSubgroup.coe_map _ _).trans ?_
      show (fun y => PositivityTheory.SiegelWeilFormula.Gen.matV v ai' *ᵥ y) '' (L v : Set _) = _
      rw [hLv]
      exact image_latO hI _ _ h4 h3 (hC2 v)
  ·
    have := GlobalTheory.CompanionTheory.SiegLoc.NuIndex.secondCountable_tens bs v
    let T := lmulHomeo (M := M) (v := v) _ _ (hT1 v) (hT2 v)
    exact ⟨(hP.1 v).1.comp_continuous T.continuous, (hP.1 v).2.comp_homeomorph T⟩
  ·
    filter_upwards [hP.2.1, intAt_eventually bs, matV_mem_Rv bs a, matV_mem_Rv bs ai] with v hg hI h1 h2
    funext Y
    let T := lmulHomeo (M := M) (v := v) _ _ (hT1 v) (hT2 v)
    have hiff : T Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV (M := M) (n := n) bs v ↔ Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV (M := M) (n := n) bs v := by
      constructor
      · intro hy
        have := mul_mem_latV hI (PositivityTheory.SiegelWeilFormula.Gen.matV v ai)ᵀ (fun i j => h2 j i) (T Y) hy
        rwa [show (HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _)
          (PositivityTheory.SiegelWeilFormula.Gen.matV v ai)ᵀ (T Y) : Fin n → Fin M → _) = Y from T.left_inv Y] at this
      · intro hy
        exact mul_mem_latV hI (PositivityTheory.SiegelWeilFormula.Gen.matV v a)ᵀ (fun i j => h1 j i) Y hy
    show gv v (T Y) = _
    rw [hg]
    by_cases hy : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV (M := M) (n := n) bs v
    · rw [Set.indicator_of_mem (hiff.2 hy), Set.indicator_of_mem hy]
      rfl
    · rw [Set.indicator_of_notMem (fun h => hy (hiff.1 h)), Set.indicator_of_notMem hy]
  ·
    refine (hP.2.2 (fun j i => ∑ c, Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (a c j) * X c i)).trans
      (finprod_congr fun v => ?_)
    exact congrArg (gv v) (projV_lmul v a X)
  ·
    exact congrArg g (finPart_mul x a)
  ·
    have := hlam v
    have := GlobalTheory.CompanionTheory.SiegLoc.NuIndex.secondCountable_tens bs v
    rw [matV_mul, matV_mul]
    exact lattice_norm_matrix_conj (lam v) (L v) _ _ _ _ _ (hA1 v) (hA2 v) (hC1 v)

end Comp

end GlobalTheory.CompanionTheory.SwFinM

end

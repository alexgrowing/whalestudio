import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PositionOf

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory
open scoped ContDiff

namespace UpperTheory.ConvolutionTheory.L1

private theorem fin_prod {ι X : Type} [Fintype ι] {Y : ι → Type} (p : ∀ i, X → Y i) (S : ∀ i, Set (Y i → ℂ))
    (hS : ∀ i, FiniteDimensional ℂ (Submodule.span ℂ (S i))) :
    FiniteDimensional ℂ (Submodule.span ℂ
      {f : X → ℂ | ∃ s : ∀ i, Y i → ℂ, (∀ i, s i ∈ S i) ∧ f = fun x => ∏ i, s i (p i x)}) := by
  classical
  let T : MultilinearMap ℂ (fun i => Y i → ℂ) (X → ℂ) :=
    (MultilinearMap.mkPiAlgebra ℂ ι (X → ℂ)).compLinearMap (fun i => LinearMap.funLeft ℂ ℂ (p i))
  have hT : ∀ s x, T s x = ∏ i, s i (p i x) := by
    intro s x
    simp [T, MultilinearMap.compLinearMap_apply, Finset.prod_apply, LinearMap.funLeft_apply]
  let d : ι → ℕ := fun i => Module.finrank ℂ (Submodule.span ℂ (S i))
  let b : ∀ i, Module.Basis (Fin (d i)) ℂ (Submodule.span ℂ (S i)) := fun i => Module.finBasis ℂ _
  let R : Set (X → ℂ) := Set.range fun r : ∀ i, Fin (d i) => T fun i => ((b i (r i) : Submodule.span ℂ (S i)) : Y i → ℂ)
  have hR : R.Finite := Set.finite_range _
  have hle : Submodule.span ℂ {f : X → ℂ | ∃ s : ∀ i, Y i → ℂ, (∀ i, s i ∈ S i) ∧ f = fun x => ∏ i, s i (p i x)} ≤
      Submodule.span ℂ R := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨s, hs, rfl⟩
    have hs' : ∀ i, s i ∈ Submodule.span ℂ (S i) := fun i => Submodule.subset_span (hs i)
    let c : ∀ i, Fin (d i) → ℂ := fun i j => (b i).repr ⟨s i, hs' i⟩ j
    have hsum : ∀ i, s i = ∑ j, c i j • ((b i j : Submodule.span ℂ (S i)) : Y i → ℂ) := by
      intro i
      have h := (b i).sum_repr ⟨s i, hs' i⟩
      calc s i = ((⟨s i, hs' i⟩ : Submodule.span ℂ (S i)) : Y i → ℂ) := rfl
        _ = ((∑ j, c i j • b i j : Submodule.span ℂ (S i)) : Y i → ℂ) := by rw [h]
        _ = _ := by rw [AddSubmonoidClass.coe_finset_sum]; rfl
    have e : (fun x => ∏ i, s i (p i x)) = T s := funext fun x => (hT s x).symm
    have e2 : T s = T fun i => ∑ j, c i j • ((b i j : Submodule.span ℂ (S i)) : Y i → ℂ) :=
      congrArg T (funext hsum)
    show (fun x => ∏ i, s i (p i x)) ∈ (Submodule.span ℂ R : Set (X → ℂ))
    rw [e, e2, MultilinearMap.map_sum]
    refine Submodule.sum_mem _ fun r _ => ?_
    rw [MultilinearMap.map_smul_univ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ R) := FiniteDimensional.span_of_finite ℂ hR
  exact Submodule.finiteDimensional_of_le hle

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E ≃ₐ[F] E} {m : ℕ}

private def cR (D : InfD σ m) (i : Fin (m + 1)) : InfiniteAdeleRing E →+* InfiniteAdeleRing F :=
  (Pi.evalRingHom (fun _ : Fin (m + 1) => InfiniteAdeleRing F) i).comp D.e.toRingHom

private theorem continuous_cR (D : InfD σ m) (i : Fin (m + 1)) : Continuous (cR D i) :=
  (continuous_apply i).comp D.cont

private def thetaR (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : ArchMatrix E n →+* ArchMatrix F n :=
  (archMatrixEquiv F n).toRingHom.comp ((RingHom.mapMatrix (cR D i)).comp (archMatrixEquiv E n).symm.toRingHom)

private theorem continuous_thetaR (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : Continuous (thetaR D n i) := by
  have h1 : Continuous fun M : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E) => M.map (cR D i) :=
    continuous_id.matrix_map (continuous_cR D i)
  exact (continuous_archMatrixEquiv F n).comp (h1.comp (continuous_archMatrixEquiv_symm E n))

private theorem compA_val (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) (g : archGroup E n) :
    (((compA D n i g : archGroup F n) : (ArchMatrix F n)ˣ) : ArchMatrix F n) =
      thetaR D n i ((g : (ArchMatrix E n)ˣ) : ArchMatrix E n) := rfl

private theorem thetaR_exp (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) (X : ArchMatrix E n) :
    thetaR D n i (NormedSpace.exp X) = NormedSpace.exp (thetaR D n i X) := by
  letI : NormedAlgebra ℚ (ArchMatrix E n) := NormedAlgebra.restrictScalars ℚ ℝ _
  letI : NormedAlgebra ℚ (ArchMatrix F n) := NormedAlgebra.restrictScalars ℚ ℝ _
  exact NormedSpace.map_exp (thetaR D n i) (continuous_thetaR D n i) X

private def thetaL (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : archLie E n →L[ℝ] archLie F n where
  toFun Y := ⟨thetaR D n i (Y : ArchMatrix E n), Submodule.mem_top⟩
  map_add' X Y := Subtype.ext (map_add (thetaR D n i) _ _)
  map_smul' c X := Subtype.ext (map_real_smul (thetaR D n i) (continuous_thetaR D n i) c _)
  cont := ((continuous_thetaR D n i).comp continuous_subtype_val).subtype_mk _

private theorem compA_expG (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) (Y : archLie E n) :
    compA D n i ((isExpLieAlgebra E n).expG Y) = (isExpLieAlgebra F n).expG (thetaL D n i Y) := by
  apply Subtype.ext
  apply Units.ext
  rw [compA_val, IsExpLieAlgebra.coe_expG, IsExpLieAlgebra.coe_expG]
  exact thetaR_exp D n i _

private theorem tens_smooth (D : InfD σ m) (n : ℕ) (φ : Fin (m + 1) → TI F n) (β : TI E n) (hβ : IsTens D φ β)
    (hφ : ∀ i, SmoothT (φ i)) : SmoothT β := by
  refine (IsExpLieAlgebra.isSmoothFun_iff (isExpLieAlgebra E n)).2 fun g => ?_
  have e : (fun Y : archLie E n => β (g * (isExpLieAlgebra E n).expG Y)) = fun Y => ∏ i,
      (fun Z : archLie F n => φ i (compA D n i g * (isExpLieAlgebra F n).expG Z)) (thetaL D n i Y) := by
    funext Y
    rw [hβ]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_mul, compA_expG]
  rw [e]
  refine contDiff_prod fun i _ => ?_
  exact ((IsExpLieAlgebra.isSmoothFun_iff (isExpLieAlgebra F n)).1 (hφ i) _).comp (thetaL D n i).contDiff

private theorem tens_fin [IsTotallyComplex F] (D : InfD σ m) (n : ℕ) (φ : Fin (m + 1) → TI F n) (β : TI E n)
    (hβ : IsTens D φ β) (hφ : ∀ i, LeftFin (φ i)) : LeftFin β := by
  haveI := fin_prod (ι := Fin (m + 1)) (X := archGroup E n) (Y := fun _ => archGroup F n) (fun i => compA D n i)
    (fun i => Set.range fun k : archCompact F n => fun g : archGroup F n => φ i ((k : archGroup F n) * g)) hφ
  have hsub : (Set.range fun k : archCompact E n => fun g : archGroup E n => β ((k : archGroup E n) * g)) ⊆
      {f | ∃ s : Fin (m + 1) → archGroup F n → ℂ, (∀ i, s i ∈ Set.range fun k : archCompact F n =>
        fun g : archGroup F n => φ i ((k : archGroup F n) * g)) ∧ f = fun x => ∏ i, s i (compA D n i x)} := by
    rintro f ⟨k, rfl⟩
    have hk := ((positionOf F E σ m D).2 n (k : archGroup E n)).1 k.2
    refine ⟨fun i g => φ i (compA D n i k * g), fun i => ⟨⟨_, hk i⟩, rfl⟩, ?_⟩
    funext x
    show β ((k : archGroup E n) * x) = _
    rw [hβ]
    exact Finset.prod_congr rfl fun i _ => by rw [map_mul]
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.tensSmooth :
    UpperTheory.ConvolutionTheory.L1.TensSmooth := by
  intro F E _ _ _ _ _ _ σ m D n φ β hβ
  exact ⟨UpperTheory.ConvolutionTheory.L1.tens_smooth D n φ β hβ, UpperTheory.ConvolutionTheory.L1.tens_fin D n φ β hβ⟩

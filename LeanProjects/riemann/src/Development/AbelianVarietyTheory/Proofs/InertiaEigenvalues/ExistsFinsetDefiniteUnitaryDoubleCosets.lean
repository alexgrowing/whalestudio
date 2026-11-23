import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatAtConstOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivLocProdTriv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

noncomputable section

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.UnitaryBC.ClassTransport

section General

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_adMap : Continuous (GlobalTheory.AdeleBaseChange.adMap F E) := by
  have hf : Filter.Tendsto (fun P : HeightOneSpectrum (𝓞 E) => P.under (𝓞 F)) Filter.cofinite Filter.cofinite :=
    Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => GlobalTheory.QNorm.finite_places_over F E v
  exact RestrictedProduct.mapAlong_continuous (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun P : HeightOneSpectrum (𝓞 E) => P.adicCompletion E) _ hf
    (fun P => GlobalTheory.AdeleBaseChange.locMap F P)
    (Filter.Eventually.of_forall fun P x hx => GlobalTheory.AdeleBaseChange.locMap_int P x hx)
    (fun P => GlobalTheory.LFun.InertChart.continuous_complMap (rfl : P.under (𝓞 F) = _))

variable {F E} in
theorem finAdEquiv_smul (a : FiniteAdeleRing (𝓞 F) F) (y : FiniteAdeleRing (𝓞 F) F ⊗[F] E) :
    GlobalTheory.LFun.finAdEquiv F E (a • y) = GlobalTheory.AdeleBaseChange.adMap F E a * GlobalTheory.LFun.finAdEquiv F E y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | tmul b x =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    change GlobalTheory.LFun.toFinAd F E ((a * b) ⊗ₜ[F] x) = GlobalTheory.AdeleBaseChange.adMap F E a * GlobalTheory.LFun.toFinAd F E (b ⊗ₜ[F] x)
    rw [GlobalTheory.LFun.toFinAd_tmul, GlobalTheory.LFun.toFinAd_tmul, map_mul, mul_assoc]
  | add y z hy hz => rw [smul_add, map_add, map_add, hy, hz, mul_add]

theorem continuous_finAdEquiv : Continuous (GlobalTheory.LFun.finAdEquiv F E) := by
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := ⟨rfl⟩
  let φ : (FiniteAdeleRing (𝓞 F) F ⊗[F] E) →ₛₗ[GlobalTheory.AdeleBaseChange.adMap F E] FiniteAdeleRing (𝓞 E) E :=
    { toFun := GlobalTheory.LFun.finAdEquiv F E
      map_add' := map_add _
      map_smul' := fun a y => finAdEquiv_smul a y }
  exact IsModuleTopology.continuous_of_linearMapₛₗ (continuous_adMap F E) φ

end General

end GlobalTheory.UnitaryBC.ClassTransport

noncomputable section

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.UnitaryBC.ClassTransport

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

local notation "F₀" => maximalRealSubfield E

theorem conjFin_adMap (a : FiniteAdeleRing (𝓞 F₀) F₀) :
    conjFin (IsCMField.complexConj E).toRingEquiv (GlobalTheory.AdeleBaseChange.adMap F₀ E a) =
      GlobalTheory.AdeleBaseChange.adMap F₀ E a := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  refine congrFun ((GlobalTheory.AdeleCharTwist.denseRange_fin (F := F₀)).equalizer
    ((continuous_conjFin _).comp (continuous_adMap F₀ E)) (continuous_adMap F₀ E) (funext fun k => ?_)) a
  simp only [Function.comp_apply]
  rw [GlobalTheory.AdeleBaseChange.adMap_algebraMap, conjFin_algebraMap]
  congr 1
  exact IsCMField.complexConj_apply_eq_self E k

theorem finAdEquiv_sigR (y : FiniteAdeleRing (𝓞 F₀) F₀ ⊗[F₀] E) :
    GlobalTheory.LFun.finAdEquiv F₀ E (sigR (FiniteAdeleRing (𝓞 F₀) F₀) (IsCMField.complexConj E : E →ₐ[F₀] E) y) =
      conjFin (IsCMField.complexConj E).toRingEquiv (GlobalTheory.LFun.finAdEquiv F₀ E y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a x =>
    change GlobalTheory.LFun.toFinAd F₀ E (a ⊗ₜ[F₀] (IsCMField.complexConj E x)) =
      conjFin (IsCMField.complexConj E).toRingEquiv (GlobalTheory.LFun.toFinAd F₀ E (a ⊗ₜ[F₀] x))
    rw [GlobalTheory.LFun.toFinAd_tmul, GlobalTheory.LFun.toFinAd_tmul, map_mul, conjFin_adMap, conjFin_algebraMap]
    rfl
  | add y z hy hz => rw [map_add, map_add, map_add, hy, hz, map_add]

theorem finGL_mem_UA {n : ℕ} (x : GL (Fin n) (FiniteAdeleRing (𝓞 E) E))
    (hx : Formalism.UG.cT (conjFin (IsCMField.complexConj E).toRingEquiv) x.val * x.val = 1) : finGL E n x ∈ UA E n := by
  change Formalism.UG.cT (conjAd E) (finGL E n x).val * 1 * (finGL E n x).val = 1
  have h1 : (finGL E n x).val.map (pInf E) = 1 := congrArg Units.val (pInf_finGL x)
  have h2 : (finGL E n x).val.map (pFin E) = x.val := congrArg Units.val (pFin_finGL x)
  have h3 : (Formalism.UG.cT (conjAd E) (finGL E n x).val).map (pInf E) = 1 := by
    ext1 i j
    have e := congrFun₂ h1 j i
    change (infEq E).symm (infEq E (starRingEnd (Cinf E) ((infEq E).symm ((finGL E n x).val j i).1))) = _
    rw [RingEquiv.symm_apply_apply]
    change pInf E ((finGL E n x).val j i) = _ at e
    change starRingEnd (Cinf E) (pInf E ((finGL E n x).val j i)) = _
    rw [e]
    simp only [Matrix.one_apply, eq_comm (a := j)]
    split_ifs <;> simp
  have h4 : (Formalism.UG.cT (conjAd E) (finGL E n x).val).map (pFin E) =
      Formalism.UG.cT (conjFin (IsCMField.complexConj E).toRingEquiv) x.val := by
    ext1 i j
    change conjFin _ (pFin E ((finGL E n x).val j i)) = conjFin _ (x.val j i)
    rw [← congrFun₂ h2 j i]
    rfl
  have h5 := congrArg₂ (· * ·) h3 h1
  have h6 := congrArg₂ (· * ·) h4 h2
  simp only [← Matrix.map_mul, hx, mul_one] at h5 h6
  rw [mul_one]
  ext1 i j
  refine ad_ext ((congrFun₂ h5 i j).trans ?_) ((congrFun₂ h6 i j).trans ?_) <;>
  · simp only [Matrix.one_apply]
    split_ifs <;> simp

variable (E) in

def psi (n : ℕ) : HA (FiniteAdeleRing (𝓞 F₀) F₀) (IsCMField.complexConj E : E →ₐ[F₀] E) (1 : Matrix (Fin n) (Fin n) E) →*
    GL (Fin n) (FiniteAdeleRing (𝓞 E) E) :=
  (Matrix.GeneralLinearGroup.map (GlobalTheory.LFun.finAdEquiv F₀ E).toRingHom).comp
    (HR (FiniteAdeleRing (𝓞 F₀) F₀) (IsCMField.complexConj E : E →ₐ[F₀] E) (1 : Matrix (Fin n) (Fin n) E)).subtype

end CM

end GlobalTheory.UnitaryBC.ClassTransport

noncomputable section

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.UnitaryBC.ClassTransport

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

local notation "F₀" => maximalRealSubfield E

theorem psi_mem {n : ℕ}
    (x : HA (FiniteAdeleRing (𝓞 F₀) F₀) (IsCMField.complexConj E : E →ₐ[F₀] E) (1 : Matrix (Fin n) (Fin n) E)) :
    Formalism.UG.cT (conjFin (IsCMField.complexConj E).toRingEquiv) (psi E n x).val * (psi E n x).val = 1 := by
  have hx := (show HR (FiniteAdeleRing (𝓞 F₀) F₀) (IsCMField.complexConj E : E →ₐ[F₀] E)
    (1 : Matrix (Fin n) (Fin n) E) from x).2
  change Formalism.UG.cT (sigR (FiniteAdeleRing (𝓞 F₀) F₀) (IsCMField.complexConj E : E →ₐ[F₀] E))
    (HA.mat _ _ _ x).val * JR (FiniteAdeleRing (𝓞 F₀) F₀) (1 : Matrix (Fin n) (Fin n) E) * (HA.mat _ _ _ x).val =
      JR (FiniteAdeleRing (𝓞 F₀) F₀) (1 : Matrix (Fin n) (Fin n) E) at hx
  rw [JR, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at hx
  have e : (Formalism.UG.cT (sigR (FiniteAdeleRing (𝓞 F₀) F₀) (IsCMField.complexConj E : E →ₐ[F₀] E))
      (HA.mat _ _ _ x).val).map (GlobalTheory.LFun.finAdEquiv F₀ E).toRingHom =
      Formalism.UG.cT (conjFin (IsCMField.complexConj E).toRingEquiv)
        ((HA.mat _ _ _ x).val.map (GlobalTheory.LFun.finAdEquiv F₀ E).toRingHom) := by
    refine Matrix.ext fun i j => ?_
    exact finAdEquiv_sigR (E := E) _
  change Formalism.UG.cT (conjFin (IsCMField.complexConj E).toRingEquiv)
      ((HA.mat _ _ _ x).val.map (GlobalTheory.LFun.finAdEquiv F₀ E).toRingHom) *
      (HA.mat _ _ _ x).val.map (GlobalTheory.LFun.finAdEquiv F₀ E).toRingHom = 1
  rw [← e, ← Matrix.map_mul, hx, Matrix.map_one _ (map_zero _) (map_one _)]

variable (E) in

def jU (n : ℕ) : HA (FiniteAdeleRing (𝓞 F₀) F₀) (IsCMField.complexConj E : E →ₐ[F₀] E) (1 : Matrix (Fin n) (Fin n) E) →*
    UA E n :=
  ((finGL E n).comp (psi E n)).codRestrict (UA E n) fun x => finGL_mem_UA _ (psi_mem x)

variable (E) in

def jF (n : ℕ) : HA (FiniteAdeleRing (𝓞 F₀) F₀) (IsCMField.complexConj E : E →ₐ[F₀] E) (1 : Matrix (Fin n) (Fin n) E) →*
    finU E n :=
  (jU E n).codRestrict (finU E n) fun x => MonoidHom.mem_ker.2 (pInf_finGL (psi E n x))

theorem continuous_finGL (n : ℕ) : Continuous (finGL E n) := by
  have hs : Continuous (sFin E) :=
    (continuous_const.prodMk continuous_id :
      Continuous fun x : FiniteAdeleRing (𝓞 E) E => ((0, x) : InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))
  exact Continuous.units_map _ (continuous_const.add
    (continuous_id.matrix_map hs : Continuous fun x : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) => x.map (sFin E)))

theorem continuous_psi (n : ℕ) : Continuous (psi E n) :=
  (Continuous.units_map _ (continuous_id.matrix_map (continuous_finAdEquiv F₀ E))).comp continuous_subtype_val

theorem continuous_jF (n : ℕ) : Continuous (jF E n) :=
  (((continuous_finGL (E := E) n).comp (continuous_psi (E := E) n)).subtype_mk _).subtype_mk _

end CM

end GlobalTheory.UnitaryBC.ClassTransport

noncomputable section

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.UnitaryBC.ClassTransport

theorem exists_finset_double_cosets : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
    ∀ L : Subgroup (finU E n), IsOpen (L : Set (finU E n)) → ∃ S : Finset (UA E n), ∀ g : UA E n,
      ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ k ∈ L, ∃ y ∈ infU E n, g = γ * s * (k : UA E n) * y := by
  classical
  intro E _ _ _ n L hL
  obtain ⟨S, hS⟩ := GlobalTheory.Mem.ClassFinite.exists_finset_classes (maximalRealSubfield E) E
    (IsCMField.complexConj E : E →ₐ[maximalRealSubfield E] E) (GlobalTheory.AdelicU.isCMExt_of_isCMField E) n 1
    (GlobalTheory.AdelicU.isHermND_one _ n) (L.comap (jF E n)) (hL.preimage (continuous_jF n))
  refine ⟨S.image (jU E n), fun g => ?_⟩
  have hg := g.2
  change Formalism.UG.cT (conjAd E) g.1.val * 1 * g.1.val = 1 at hg
  rw [Matrix.mul_one] at hg
  have hgf : Formalism.UG.cT (conjFin (IsCMField.complexConj E).toRingEquiv)
      (Matrix.GeneralLinearGroup.map (pFin E) g.1).val * (Matrix.GeneralLinearGroup.map (pFin E) g.1).val = 1 := by
    have h := congrArg (fun M => M.map (pFin E)) hg
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hmem : Matrix.GeneralLinearGroup.map (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (pFin E) g.1) ∈
      HR (FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E))
        (IsCMField.complexConj E : E →ₐ[maximalRealSubfield E] E) (1 : Matrix (Fin n) (Fin n) E) := by
    change Formalism.UG.cT (sigR (FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E))
        (IsCMField.complexConj E : E →ₐ[maximalRealSubfield E] E)) _ *
        JR (FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) (1 : Matrix (Fin n) (Fin n) E) * _ =
        JR (FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) (1 : Matrix (Fin n) (Fin n) E)
    rw [JR, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    refine Matrix.map_injective (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).injective ?_
    change Matrix.map _ (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).toRingHom =
      Matrix.map 1 (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).toRingHom
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have hU : Matrix.map ((Matrix.GeneralLinearGroup.map (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).symm.toRingHom)
        (Matrix.GeneralLinearGroup.map (pFin E) g.1)).val (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).toRingHom =
        (Matrix.GeneralLinearGroup.map (pFin E) g.1).val :=
      Matrix.ext fun i j => (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).apply_symm_apply _
    have e : Matrix.map (Formalism.UG.cT (sigR (FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E))
        (IsCMField.complexConj E : E →ₐ[maximalRealSubfield E] E))
        ((Matrix.GeneralLinearGroup.map (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).symm.toRingHom)
          (Matrix.GeneralLinearGroup.map (pFin E) g.1)).val) (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).toRingHom =
        Formalism.UG.cT (conjFin (IsCMField.complexConj E).toRingEquiv)
          (Matrix.map ((Matrix.GeneralLinearGroup.map (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).symm.toRingHom)
            (Matrix.GeneralLinearGroup.map (pFin E) g.1)).val (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).toRingHom) :=
      Matrix.ext fun i j => finAdEquiv_sigR (E := E) _
    rw [e, hU]
    exact hgf
  let u : HA (FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E))
      (IsCMField.complexConj E : E →ₐ[maximalRealSubfield E] E) (1 : Matrix (Fin n) (Fin n) E) := ⟨_, hmem⟩
  have hu : psi E n u = Matrix.GeneralLinearGroup.map (pFin E) g.1 :=
    Units.ext (Matrix.ext fun i j => (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).apply_symm_apply _)
  obtain ⟨γ, s, hs, k, hk, e⟩ := hS u
  obtain ⟨γ0, hγ0, eγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  change Formalism.UG.cT ((IsCMField.complexConj E : E →ₐ[maximalRealSubfield E] E) : E →+* E) γ0.val * 1 * γ0.val = 1 at hγ0
  rw [Matrix.mul_one] at hγ0
  have hγU : ratGL E n γ0 ∈ UA E n := by
    change Formalism.UG.cT (conjAd E) (γ0.val.map (algebraMap E (Ad E))) * 1 * γ0.val.map (algebraMap E (Ad E)) = 1
    have e1 : Formalism.UG.cT (conjAd E) (γ0.val.map (algebraMap E (Ad E))) =
        (Formalism.UG.cT ((IsCMField.complexConj E : E →ₐ[maximalRealSubfield E] E) : E →+* E) γ0.val).map
          (algebraMap E (Ad E)) :=
      Matrix.ext fun i j => conjAd_algebraMap _
    rw [e1, Matrix.mul_one, ← Matrix.map_mul, hγ0, Matrix.map_one _ (map_zero _) (map_one _)]
  let γU : UA E n := ⟨_, hγU⟩
  have hP : ∀ x, Matrix.GeneralLinearGroup.map (pFin E) (jU E n x).1 = psi E n x := fun x => pFin_finGL _
  have hPγ : Matrix.GeneralLinearGroup.map (pFin E) γU.1 = psi E n γ.1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    change pFin E (algebraMap E (Ad E) (γ0 i j)) = GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E (γ.1.1 i j)
    rw [← eγ]
    exact ((GlobalTheory.LFun.toFinAd_tmul 1 (γ0 i j)).trans (by rw [map_one, one_mul]; rfl)).symm
  have hγR : γU ∈ ratU E n := ⟨γ0, rfl⟩
  have hsS : jU E n s ∈ S.image (jU E n) := Finset.mem_image_of_mem _ hs
  have hkL : jF E n k ∈ L := hk
  have hψ : psi E n (γ • (s * k)) = psi E n γ.1 * psi E n s * psi E n k := by
    change psi E n ((show HA (FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E))
      (IsCMField.complexConj E : E →ₐ[maximalRealSubfield E] E) (1 : Matrix (Fin n) (Fin n) E) from γ.1) * (s * k)) = _
    rw [map_mul, map_mul, mul_assoc]
  have hy : (γU * jU E n s * (jF E n k : UA E n))⁻¹ * g ∈ infU E n := by
    refine MonoidHom.mem_ker.2 ?_
    rw [map_mul, map_inv, inv_mul_eq_one]
    change Matrix.GeneralLinearGroup.map (pFin E) (γU * jU E n s * jU E n k).1 =
      Matrix.GeneralLinearGroup.map (pFin E) g.1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, hP, hP, hPγ, ← hψ, ← e, hu]
  exact ⟨γU, hγR, jU E n s, hsS, jF E n k, hkL, _, hy, (mul_inv_cancel_left _ g).symm⟩

end GlobalTheory.UnitaryBC.ClassTransport

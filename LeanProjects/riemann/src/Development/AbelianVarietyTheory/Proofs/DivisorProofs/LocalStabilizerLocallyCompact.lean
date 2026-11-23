import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralCompactInvariant
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodular
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv

noncomputable section

namespace GlobalTheory.LocUnitaryUnimod

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare GlobalTheory.EmbChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem atPlace_mul' (v : Pl F) (a b : Fv F v) : atPlace v (a * b) = atPlace v a * atPlace v b := by
  rw [atPlace_mul_right, evFin_atPlace]

theorem continuous_atPlace' (v : Pl F) : Continuous (atPlace (F := F) v) :=
  continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)

theorem continuous_evFin' (v : Pl F) : Continuous (evFin F v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

theorem at_tensAt' (v : Pl F) (y : Fv F v ⊗[F] E) : At (evFin F v) (tensAt E v y) := by
  intro u hu
  rw [Algebra.smul_def, mul_comm, tensAt_mul_right]
  have : compFin F E v (algebraMap (AF F) (AE F E) u) = 0 := by
    change (evFin F v u) ⊗ₜ[F] (1 : E) = 0
    rw [hu, TensorProduct.zero_tmul]
  rw [this, mul_zero, map_zero]

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F)

theorem extH_mapH {g : HA (AF F) σ J} (hg : At (evFin F v) ((HA.mat (AF F) σ J g : Matrix (Fin n) (Fin n) (AE F E)) - 1)) :
    extH σ J (atPlace v) (atPlace_mul' v) (mapH σ J (evFin F v) g) = g := by
  refine HA_ext σ J fun r s => ?_
  rw [mat_extH, mat_mapH]
  set x := (HA.mat (AF F) σ J g : Matrix (Fin n) (Fin n) (AE F E)) r s with hxdef
  have hx : At (evFin F v) (x - (1 : Matrix (Fin n) (Fin n) (AE F E)) r s) := fun u hu => by
    have := congrFun (congrFun (hg u hu) r) s
    simpa [smul_sub] using this
  have key := GlobalTheory.UnitaryInjAtPlace.eq_tensAt_of_at v _ hx
  change (1 - tensAt E v 1) * (1 : Matrix (Fin n) (Fin n) (AE F E)) r s + tensAt E v (compFin F E v x) = x
  have hc : compFin F E v x = compFin F E v (x - (1 : Matrix (Fin n) (Fin n) (AE F E)) r s) +
      compFin F E v ((1 : Matrix (Fin n) (Fin n) (AE F E)) r s) := by rw [← map_add, sub_add_cancel]
  rw [hc, map_add, ← key]
  by_cases h : r = s
  · subst h
    simp only [Matrix.one_apply_eq, map_one]
    ring
  · simp only [Matrix.one_apply_ne h, map_zero, mul_zero, zero_add, add_zero, sub_zero]

theorem at_extH (h : HA (Fv F v) σ J) :
    At (evFin F v) ((HA.mat (AF F) σ J (extH σ J (atPlace v) (atPlace_mul' v) h) : Matrix (Fin n) (Fin n) (AE F E)) - 1) := by
  intro u hu
  ext r s
  rw [Matrix.smul_apply, Matrix.sub_apply, mat_extH, Matrix.zero_apply]
  change u • ((1 - tensAt E v 1) * (1 : Matrix (Fin n) (Fin n) (AE F E)) r s +
    tensAt E v ((HA.mat (Fv F v) σ J h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) r s) -
      (1 : Matrix (Fin n) (Fin n) (AE F E)) r s) = 0
  by_cases hrs : r = s
  · subst hrs
    simp only [Matrix.one_apply_eq, mul_one]
    rw [show (1 - tensAt E v 1 + tensAt E v ((HA.mat (Fv F v) σ J h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) r r) - 1 : AE F E) =
      tensAt E v ((HA.mat (Fv F v) σ J h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) r r - 1) by rw [map_sub]; ring]
    exact at_tensAt' v _ u hu
  · simp only [Matrix.one_apply_ne hrs, mul_zero, zero_add, sub_zero]
    exact at_tensAt' v _ u hu

def toHAe : UA σ J ≃* HA (AF F) σ Jᵀ := MulEquiv.subgroupCongr (GlobalTheory.ThetaKInv.UG_eq_HR σ J)

theorem continuous_toHAe : Continuous (toHAe σ J) := continuous_subtype_val.subtype_mk _

theorem continuous_toHAe_symm : Continuous (toHAe σ J).symm := continuous_subtype_val.subtype_mk _

theorem mat_toHAe (g : UA σ J) :
    (HA.mat (AF F) σ Jᵀ (toHAe σ J g) : Matrix (Fin n) (Fin n) (AE F E)) = mat g := rfl

theorem mat_toHAe_symm (g : HA (AF F) σ Jᵀ) :
    mat ((toHAe σ J).symm g) = (HA.mat (AF F) σ Jᵀ g : Matrix (Fin n) (Fin n) (AE F E)) := rfl

theorem continuous_locTo {n : ℕ} (X : Spc F E n) :
    Continuous fun g : UAtSub σ X (evFin F v) => mapH σ X.Jᵀ (evFin F v) (toHAe σ X.J g.1) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact (continuous_mapH σ X.Jᵀ (evFin F v) (continuous_evFin' v)).comp
    ((continuous_toHAe σ X.J).comp continuous_subtype_val)

theorem continuous_locFrom {n : ℕ} (X : Spc F E n) :
    Continuous fun h : HA (Fv F v) σ X.Jᵀ => (toHAe σ X.J).symm (extH σ X.Jᵀ (atPlace v) (atPlace_mul' v) h) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact (continuous_toHAe_symm σ X.J).comp
    (continuous_extH σ X.Jᵀ (atPlace v) (atPlace_mul' v) (continuous_atPlace' v))

theorem mem_locFrom {n : ℕ} (X : Spc F E n) (h : HA (Fv F v) σ X.Jᵀ) :
    (toHAe σ X.J).symm (extH σ X.Jᵀ (atPlace v) (atPlace_mul' v) h) ∈ UAtSub σ X (evFin F v) := by
  rw [mem_UAtSub]
  change At (evFin F v) (mat ((toHAe σ X.J).symm (extH σ X.Jᵀ (atPlace v) (atPlace_mul' v) h)) - 1)
  rw [mat_toHAe_symm]
  exact at_extH σ X.Jᵀ v h

theorem locFrom_locTo {n : ℕ} (X : Spc F E n) (g : UAtSub σ X (evFin F v)) :
    (toHAe σ X.J).symm (extH σ X.Jᵀ (atPlace v) (atPlace_mul' v) (mapH σ X.Jᵀ (evFin F v) (toHAe σ X.J g.1))) = g.1 := by
  have hg : At (evFin F v) ((HA.mat (AF F) σ X.Jᵀ (toHAe σ X.J g.1) : Matrix (Fin n) (Fin n) (AE F E)) - 1) := by
    rw [mat_toHAe]
    exact g.2
  rw [extH_mapH σ X.Jᵀ v hg, MulEquiv.symm_apply_apply]

def locEquiv {n : ℕ} (X : Spc F E n) : UAtSub σ X (evFin F v) ≃ₜ* HA (Fv F v) σ X.Jᵀ where
  toFun g := mapH σ X.Jᵀ (evFin F v) (toHAe σ X.J g.1)
  invFun h := ⟨(toHAe σ X.J).symm (extH σ X.Jᵀ (atPlace v) (atPlace_mul' v) h), mem_locFrom σ v X h⟩
  left_inv g := Subtype.ext (locFrom_locTo σ v X g)
  right_inv h := by
    change mapH σ X.Jᵀ (evFin F v) ((toHAe σ X.J) ((toHAe σ X.J).symm _)) = h
    rw [MulEquiv.apply_symm_apply]
    exact mapH_extH_self σ X.Jᵀ (evFin F v) (atPlace v) (atPlace_mul' v) (evFin_atPlace v) h
  map_mul' g g' := by
    change mapH σ X.Jᵀ (evFin F v) (toHAe σ X.J (g.1 * g'.1)) = _
    rw [map_mul, map_mul]
  continuous_toFun := continuous_locTo σ v X
  continuous_invFun := (continuous_locFrom σ v X).subtype_mk _

theorem isUnimodularLC_UAtSub (hcm : IsCMExt F E σ) {n : ℕ} (X : Spc F E n) (herm : ∀ i j, σ (X.J j i) = X.J i j)
    (hdet : X.J.det ≠ 0) : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.IsUnimodularLC (UAtSub σ X (evFin F v)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : SecondCountableTopology (Fv F v) := secondCountable_of_proper
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (UA σ X.J) := inferInstanceAs (IsTopologicalGroup (UG (cA σ) (incM F X.J)))
  have hss := GlobalTheory.HermLineZeros.conj_invol hcm
  obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hcm
  have hJ : IsHermND σ X.Jᵀ := ⟨fun i j => by simp [Matrix.transpose_apply, herm], by rwa [Matrix.det_transpose]⟩
  have hU := GlobalTheory.ArchUnitaryUnimod.isUnimodularLC_of_artinian (Fv F v) hss (sub_ne_zero.2 hd)
    (by rw [map_sub, hss, neg_sub]) hJ
  exact GlobalTheory.ArchUnitaryUnimod.isUnimodularLC_of_equiv hU (locEquiv σ v X).symm

theorem lcsc_unimodular_UAtSub : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F),
    LocallyCompactSpace (UAtSub σ G.V (evFin F v)) ∧ SecondCountableTopology (UAtSub σ G.V (evFin F v)) ∧
      T2Space (UAtSub σ G.V (evFin F v)) ∧
      ∀ μ : Measure (UAtSub σ G.V (evFin F v)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' _ X om om' om₁ om₁' hT _ v
  obtain ⟨-, hT2, hLC, hSC, -, -, hR⟩ := isUnimodularLC_UAtSub σ v hT.base.cm G.V hT.geo.hV.herm
    (GlobalTheory.ThetaKInv.det_ne_zero_of_isHerm hT.geo.hV)
  exact ⟨hLC, hSC, hT2, fun μ hμ => hR μ hμ⟩

end GlobalTheory.LocUnitaryUnimod

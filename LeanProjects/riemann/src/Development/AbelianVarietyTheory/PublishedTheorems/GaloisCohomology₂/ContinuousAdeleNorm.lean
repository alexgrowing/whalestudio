import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryHeckeBaseChange
open scoped TensorProduct Topology HeckeCharacterZeroLocus.ThmBIn

namespace GlobalTheory.GalOfCusp

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem isCMExt_real : HeckeCharacterZeroLocus.ThmBIn.IsCMExt (maximalRealSubfield E) E
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E : E →ₐ[maximalRealSubfield E] E) :=
  (isCMExt_iff _).2 ⟨inferInstance, rfl⟩

def adeleNorm : AdeleRing (𝓞 E) E →* AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) :=
  (Algebra.norm (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E))).comp
    (adeleEquiv (isCMExt_real E)).symm.toRingHom.toMonoidHom

theorem continuous_adeleNorm : Continuous (adeleNorm E) := by
  classical
  refine Continuous.comp (g := Algebra.norm (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E))) ?_
    (continuous_adeleEquiv_symm (isCMExt_real E))
  haveI : IsModuleTopology (HeckeCharacterZeroLocus.ThmBIn.AF (maximalRealSubfield E)) (HeckeCharacterZeroLocus.ThmBIn.AE (maximalRealSubfield E) E) := ⟨rfl⟩
  let b := Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.ThmBIn.AF (maximalRealSubfield E))
    (Module.finBasis (maximalRealSubfield E) E)
  refine (IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap).matrix_det.congr fun x => ?_
  exact (Algebra.norm_eq_matrix_det b x).symm

theorem adeleNorm_algebraMap (x : E) :
    adeleNorm E (algebraMap E _ x) = algebraMap _ _ (Algebra.norm (maximalRealSubfield E) x) := by
  have h : (adeleEquiv (isCMExt_real E)).symm (algebraMap E _ x) = 1 ⊗ₜ x :=
    (adeleEquiv (isCMExt_real E)).symm_apply_eq.2 (toAdele_incA x).symm
  change Algebra.norm _ ((adeleEquiv (isCMExt_real E)).symm (algebraMap E _ x)) = _
  rw [h, Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  ext y
  simp

theorem adeleMap_adeleNorm (x : AdeleRing (𝓞 E) E) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap _ E (adeleNorm E x) = x * adeleConj (maximalRealSubfield E) E x := by
  obtain ⟨z, rfl⟩ := (adeleEquiv (isCMExt_real E)).surjective x
  have h : adeleNorm E (adeleEquiv (isCMExt_real E) z) = Algebra.norm _ z :=
    congrArg (Algebra.norm _) ((adeleEquiv (isCMExt_real E)).symm_apply_apply z)
  rw [h, ← toAdele_algebraMap, GlobalTheory.Doubling.algebraMap_norm_eq (isCMExt_real E), map_mul]
  exact congrArg (_ * ·) (toAdele_cA z)

def ideleNorm : Ideles E →* Ideles (maximalRealSubfield E) := Units.map (adeleNorm E)

theorem ideleMap_ideleNorm (x : Ideles E) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E (ideleNorm E x) =
    x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E x := Units.ext (adeleMap_adeleNorm E x)

def compNorm : HChar (maximalRealSubfield E) →* HChar E where
  toFun χ := ⟨χ.1.comp (ideleNorm E), χ.2.1.comp (Continuous.units_map _ (continuous_adeleNorm E)), fun k => by
    rw [← χ.2.2 (Units.map (Algebra.norm (maximalRealSubfield E)) k)]
    exact congrArg χ.1 (Units.ext (adeleNorm_algebraMap E k))⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem compNorm_apply (χ : HChar (maximalRealSubfield E)) (x : Ideles E) :
    (compNorm E χ).1 x = χ.1 (ideleNorm E x) := rfl

def quadChar : HChar (maximalRealSubfield E) :=
  ⟨(Units.map (Int.castRingHom ℂ).toMonoidHom).comp (GlobalTheory.IdeleNormChar.normSign E),
    continuous_of_continuousAt_one _ ((continuousAt_const (y := (1 : ℂˣ))).congr (by
      filter_upwards [GlobalTheory.IdeleNormChar.eventually_normSign (K := maximalRealSubfield E) E] with a ha
      rw [MonoidHom.comp_apply, ha, map_one])),
    fun k => (congrArg (Units.map (Int.castRingHom ℂ).toMonoidHom) (GlobalTheory.IdeleNormChar.normSign_toUnits E k)).trans
      (map_one _)⟩

theorem compNorm_quadChar : compNorm E (quadChar E) = 1 :=
  Subtype.ext (MonoidHom.ext fun x => (congrArg (Units.map (Int.castRingHom ℂ).toMonoidHom)
    (GlobalTheory.IdeleNormChar.normSign_of_mem E
      ⟨Units.map (adeleEquiv (isCMExt_real E)).symm.toRingHom.toMonoidHom x, rfl⟩)).trans (map_one _))

theorem eta_neg_one (v : InfinitePlace (maximalRealSubfield E)) :
    GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E v.Completion (-1) = -1 := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := GlobalTheory.QuadSymbol.AlmostNorm.exists_basis_sq (maximalRealSubfield E) E
  have hv : v.IsReal := IsTotallyReal.isReal v
  rw [GlobalTheory.QuadSymbol.eta_eq_neg_one_iff, GlobalTheory.QuadSymbol.mem_normGroup_iff_form b h0 h1]
  rintro ⟨x, y, h⟩
  have hc : IsCMField.complexConj E (b 1) = -b 1 := by
    have h2 : IsCMField.complexConj E (b 1) * IsCMField.complexConj E (b 1) = b 1 * b 1 := by
      rw [← map_mul, h1, AlgEquiv.commutes]
    refine (mul_self_eq_mul_self_iff.1 h2).resolve_left fun e => hδ ?_
    exact ⟨⟨b 1, (IsCMField.complexConj_eq_self_iff E _).1 e⟩, Subtype.ext h1.symm⟩
  have h3 := ComplexEmbedding.lift_algebraMap_apply E v.embedding δ
  have h4 := IsCMField.complexEmbedding_complexConj E (ComplexEmbedding.lift E v.embedding) (b 1)
  rw [hc, map_neg] at h4
  rw [← h1, map_mul] at h3
  have h5 : InfinitePlace.embedding_of_isReal hv δ ≤ 0 := by
    have h6 : ((InfinitePlace.embedding_of_isReal hv δ : ℝ) : ℂ) =
        ((-Complex.normSq (ComplexEmbedding.lift E v.embedding (b 1)) : ℝ) : ℂ) := by
      rw [InfinitePlace.embedding_of_isReal_apply, ← h3, Complex.ofReal_neg, ← Complex.mul_conj, ← h4]
      ring
    rw [Complex.ofReal_injective h6]
    exact neg_nonpos.2 (Complex.normSq_nonneg _)
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  have he : e (algebraMap _ v.Completion δ) = InfinitePlace.embedding_of_isReal hv δ :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm δ)
  have h7 := congrArg e h
  simp only [Units.val_neg, Units.val_one, map_neg, map_one, map_sub, map_mul, map_pow, he] at h7
  nlinarith [sq_nonneg (e x), mul_nonneg (neg_nonneg.2 h5) (sq_nonneg (e y))]

theorem quadChar_locInf (v : InfinitePlace (maximalRealSubfield E)) : (quadChar E).locInf v (-1) = -1 := by
  classical
  have h1 : ∀ (A : Type) [CommRing A] [Algebra (maximalRealSubfield E) A],
      GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E A 1 = 1 := fun A _ _ => GlobalTheory.QuadSymbol.eta_eq_one_iff.2 (one_mem _)
  have h : GlobalTheory.IdeleNormChar.normSign E (infIdele _ v (-1)) = -1 := by
    change GlobalTheory.QuadSymbol.etaProd _ E _ _ = _
    unfold GlobalTheory.QuadSymbol.etaProd
    have e1 : GlobalTheory.IdeleNormChar.finComp (infIdele _ v (-1)) = 1 := funext fun _ => Units.ext rfl
    have e2 : ∀ u, u ≠ v → GlobalTheory.IdeleNormChar.infComp (infIdele _ v (-1)) u = 1 := fun u hu =>
      Units.ext (Pi.mulSingle_eq_of_ne (M := fun w : InfinitePlace (maximalRealSubfield E) => w.Completion) hu _)
    have e3 : GlobalTheory.IdeleNormChar.infComp (infIdele _ v (-1)) v = -1 :=
      Units.ext (Pi.mulSingle_eq_same (M := fun w : InfinitePlace (maximalRealSubfield E) => w.Completion) v _)
    rw [e1, Finset.prod_eq_single v (fun u _ hu => by rw [e2 u hu, h1]) (by simp), e3, eta_neg_one]
    simp [h1]
  change Units.map _ (GlobalTheory.IdeleNormChar.normSign E (infIdele _ v (-1))) = _
  rw [h]
  exact Units.ext (by simp)

variable {E} {a : ℕ}

def IsConjDualBy (π : CuspSub E a) (ψ : HChar E) : Prop :=
  ∃ T : π.V ≃ₗ[ℂ] (π.twist ψ⁻¹).V, ∀ o φ, T (π.op (thetaOp o) φ) = (π.twist ψ⁻¹).op o (T φ)

theorem isConjDualBy_one (π : CuspSub E a) : IsConjDualBy π 1 ↔ π.IsCsd := by
  rw [IsConjDualBy, inv_one, CuspSub.twist_one, CuspSub.IsCsd]

theorem isConjDualBy_twist {π : CuspSub E a} (h : π.IsCsd) {ξ ψ : HChar E}
    (hξ : ∀ o : Op E a, opMul ξ (thetaOp o) = opMul (ξ * ψ⁻¹) o ∧ opAdd ξ (thetaOp o) = opAdd (ξ * ψ⁻¹) o) :
    IsConjDualBy (π.twist ξ) ψ := by
  obtain ⟨T, hT⟩ := h
  rw [IsConjDualBy, ← CuspSub.twist_mul]
  refine ⟨((π.toTwist ξ).symm.trans T).trans (π.toTwist _), fun o φ => ?_⟩
  obtain ⟨φ, rfl⟩ := (π.toTwist ξ).surjective φ
  simp only [CuspSub.op_toTwist, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, map_add T, map_smul T, hT,
    (hξ o).1, (hξ o).2]

structure IsPolarized (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) : Prop where
  sign : ∀ v : InfinitePlace (maximalRealSubfield E), χ.locInf v (-1) = (-1) ^ a
  dual : IsConjDualBy π (compNorm E χ)

theorem locInf_pow {K : Type} [Field K] [NumberField K] (χ : HChar K) (k : ℕ) (v : InfinitePlace K)
    (x : (v.Completion)ˣ) : (χ ^ k).locInf v x = χ.locInf v x ^ k := rfl

theorem IsConjDualBy.isPolarized {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)}
    (h : IsConjDualBy π (compNorm E χ)) {m : ℕ} (hχ : ∀ v, χ.locInf v (-1) = (-1) ^ m) :
    IsPolarized π (χ * quadChar E ^ (m + a)) where
  sign v := by
    rw [HChar.locInf_mul, locInf_pow, hχ, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]
    simp
  dual := by rwa [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]

theorem isPolarized_of_isCsd {π : CuspSub E a} (h : π.IsCsd) : IsPolarized π (quadChar E ^ a) := by
  simpa using IsConjDualBy.isPolarized (π := π) (χ := 1) (by rw [map_one]; exact (isConjDualBy_one π).2 h) (m := 0)
    fun _ => rfl

theorem isPolarized_triv : IsPolarized (CuspSub.triv E (le_refl 1)) (quadChar E ^ 1) ∧
    (CG.mk (CuspSub.triv E (le_refl 1))).IsRegAlg := by
  refine ⟨isPolarized_of_isCsd ⟨.refl _ _, fun o φ => Subtype.ext ?_⟩, ?_⟩
  · obtain ⟨c, e⟩ := Submodule.mem_span_singleton.1 φ.2
    change act (thetaOp o) φ.1 = act o φ.1
    rw [← e, map_smul, map_smul, act_oneFn, act_oneFn]
    cases o <;> rfl
  · rw [← CuspSub.twist_one (CuspSub.triv E (le_refl 1))]
    exact (CG.isRegAlg_ofChar 1).2 fun τ => ⟨0, by simp [CG.expo_one]⟩

end GlobalTheory.GalOfCusp

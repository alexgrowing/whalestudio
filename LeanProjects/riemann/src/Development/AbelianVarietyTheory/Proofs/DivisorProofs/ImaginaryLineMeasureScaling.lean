import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemImLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinatesInverse

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipConj.LineModulus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_anti {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  have hne : ∃ e : E, σ e ≠ e := by
    by_contra hc
    push_neg at hc
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := h.2.1
    exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun y =>
        (h.2.2.2 τ y).symm.trans (congrArg τ (hc y)))))
  obtain ⟨e, he⟩ := hne
  refine ⟨e - σ e, sub_ne_zero.2 (Ne.symm he), ?_⟩
  rw [map_sub, GlobalTheory.ThK.UnipDom.Inverse.sigma_sigma h]
  ring

theorem linIndep_one_anti {σ : E →ₐ[F] E} {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ) :
    LinearIndependent F ![1, δ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
  have h2 : σ (algebraMap F E s + algebraMap F E t * δ) = 0 := by rw [hst, map_zero]
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσδ] at h2
  have hs2 : algebraMap F E s * 2 = 0 := by linear_combination hst + h2
  have ht2 : algebraMap F E t * δ * 2 = 0 := by linear_combination hst - h2
  have h2ne : (2 : E) ≠ 0 := two_ne_zero
  refine ⟨?_, ?_⟩
  · have := (mul_eq_zero.1 hs2).resolve_right h2ne
    exact (map_eq_zero_iff _ (algebraMap F E).injective).1 this
  · have := ((mul_eq_zero.1 ht2).resolve_right h2ne)
    have := (mul_eq_zero.1 this).resolve_right hδ
    exact (map_eq_zero_iff _ (algebraMap F E).injective).1 this

theorem cA_eq_sigR (σ : E →ₐ[F] E) (x : AE F E) : cA σ x = sigR (AF F) σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.UnipConj.LineModulus

namespace GlobalTheory.UnipConj.LineModulus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def delta (h : IsCMExt F E σ) : E := (exists_anti h).choose

theorem delta_ne_zero (h : IsCMExt F E σ) : delta h ≠ 0 := (exists_anti h).choose_spec.1

theorem sigma_delta (h : IsCMExt F E σ) : σ (delta h) = -delta h := (exists_anti h).choose_spec.2

def basisE (h : IsCMExt F E σ) : Module.Basis (Fin 2) F E :=
  basisOfLinearIndependentOfCardEqFinrank (linIndep_one_anti (delta_ne_zero h) (sigma_delta h))
    (by rw [Fintype.card_fin, h.2.2.1])

theorem coe_basisE (h : IsCMExt F E σ) : ⇑(basisE h) = ![1, delta h] :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

def basisA (h : IsCMExt F E σ) : Module.Basis (Fin 2) (AF F) (AE F E) :=
  Algebra.TensorProduct.basis (AF F) (basisE h)

theorem basisA_zero (h : IsCMExt F E σ) : basisA h 0 = 1 := by
  rw [basisA, Algebra.TensorProduct.basis_apply, coe_basisE]
  rfl

theorem basisA_one (h : IsCMExt F E σ) : basisA h 1 = (1 : AF F) ⊗ₜ[F] delta h := by
  rw [basisA, Algebra.TensorProduct.basis_apply, coe_basisE]
  rfl

theorem cA_basisA_zero (h : IsCMExt F E σ) : cA σ (basisA h 0) = basisA h 0 := by
  rw [basisA_zero, map_one]

theorem cA_basisA_one (h : IsCMExt F E σ) : cA σ (basisA h 1) = -basisA h 1 := by
  rw [basisA_one]
  simp [cA, sigma_delta h, TensorProduct.tmul_neg]

theorem repr_zero_of_mem (h : IsCMExt F E σ) {t : AE F E} (ht : t ∈ imLine σ) : (basisA h).repr t 0 = 0 := by
  have hsum := (basisA h).sum_repr t
  rw [Fin.sum_univ_two] at hsum
  set c0 := (basisA h).repr t 0
  set c1 := (basisA h).repr t 1
  have key : t + cA σ t = (c0 + c0) • basisA h 0 := by
    conv_lhs => rw [← hsum]
    rw [map_add, map_smul, map_smul, cA_basisA_zero, cA_basisA_one, add_smul, smul_neg]
    abel
  rw [mem_imLine.1 ht] at key
  have h0 := congrArg (fun x => (basisA h).repr x 0) key
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul, mul_one] at h0
  calc c0 = ⅟(2 : AF F) * (2 * c0) := by rw [← mul_assoc, invOf_mul_self, one_mul]
    _ = 0 := by rw [two_mul, ← h0, mul_zero]

theorem smul_basisA_one_mem (h : IsCMExt F E σ) (s : AF F) : s • basisA h 1 ∈ imLine σ := by
  rw [mem_imLine, map_smul, cA_basisA_one, smul_neg, add_neg_cancel]

def lineEquiv (h : IsCMExt F E σ) : AF F ≃ₜ+ imLine σ where
  toFun s := ⟨s • basisA h 1, smul_basisA_one_mem h s⟩
  invFun t := (basisA h).repr t.1 1
  left_inv s := by simp
  right_inv t := by
    apply Subtype.ext
    have hsum := (basisA h).sum_repr t.1
    rw [Fin.sum_univ_two, repr_zero_of_mem h t.2, zero_smul, zero_add] at hsum
    exact hsum
  map_add' a b := by
    apply Subtype.ext
    simp [add_smul]
  continuous_toFun := (continuous_id.smul continuous_const).subtype_mk _
  continuous_invFun := (IsModuleTopology.continuous_of_linearMap ((basisA h).coord 1)).comp continuous_subtype_val

theorem lineEquiv_apply (h : IsCMExt F E σ) (s : AF F) : (lineEquiv h s : AE F E) = s • basisA h 1 := rfl

end GlobalTheory.UnipConj.LineModulus

theorem GlobalTheory.UnipConj.LineModulus.addEquivAddHaarChar_imLine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (l : (AE F E)ˣ) [IsTopologicalAddGroup (GlobalTheory.UnipConj.imLine σ)] [LocallyCompactSpace (GlobalTheory.UnipConj.imLine σ)]
    [MeasurableSpace (GlobalTheory.UnipConj.imLine σ)] [BorelSpace (GlobalTheory.UnipConj.imLine σ)]
    (Bl : GlobalTheory.UnipConj.imLine σ ≃ₜ+ GlobalTheory.UnipConj.imLine σ),
    (∀ t, (Bl t : AE F E) = l.1 * cA σ l.1 * t) → addEquivAddHaarChar Bl = absE F E l := by
  intro F E _ _ _ _ _ σ h l _ _ _ _ Bl hBl
  letI : MeasurableSpace (AF F) := borel _
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  set u : (AF F)ˣ := Units.map (Algebra.norm (AF F) : AE F E →* AF F) l
  have hB : Bl = ((lineEquiv h).symm.trans (GlobalTheory.ModuNorm.mulUnitCE u)).trans (lineEquiv h) := by
    ext t
    obtain ⟨s, rfl⟩ : ∃ s, lineEquiv h s = t := ⟨(lineEquiv h).symm t, (lineEquiv h).apply_symm_apply t⟩
    have e1 : (((lineEquiv h).symm.trans (GlobalTheory.ModuNorm.mulUnitCE u)).trans (lineEquiv h)) (lineEquiv h s) =
        lineEquiv h (u.1 * s) := by
      change lineEquiv h (GlobalTheory.ModuNorm.mulUnitCE u ((lineEquiv h).symm (lineEquiv h s))) = _
      rw [ContinuousAddEquiv.symm_apply_apply]
      rfl
    rw [e1, hBl, lineEquiv_apply, lineEquiv_apply, cA_eq_sigR, ← GlobalTheory.Doubling.algebraMap_norm_eq h,
      ← Algebra.smul_def, smul_smul]
    rfl
  rw [hB, GlobalTheory.ModuLR.addEquivAddHaarChar_transport, ← GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar]
  exact GlobalTheory.ModuAdele.modu_norm_eq_absE F E l

import Mathlib
import Formalism.PeriodIntegrals.SplitIntLoc

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct

noncomputable section

namespace PI.SplitIntLoc.Proof

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

lemma intsV : (Valued.v (R := (v.adicCompletion F))).Integers (v.adicCompletionIntegers F) :=
  Valuation.valuationSubring.integers _

lemma mem_max_iff (z : (v.adicCompletionIntegers F)) : z ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔ Valued.v (z : (v.adicCompletion F)) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, (intsV v).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne ((intsV v).map_le_one z) h, ne_of_lt⟩

lemma exists_unif : ∃ π : 𝓞 F, (algebraMap (𝓞 F) F π) ≠ 0 ∧
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F π)) < 1 := by
  obtain ⟨z, hzI, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨z, ?_, ?_⟩
  · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).2 hz0
  · rw [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
      valuedAdicCompletion_eq_valuation']
    exact (valuation_lt_one_iff_mem v z).2 hzI

variable {v} (spl : E ⊗[F] (v.adicCompletion F) ≃+* (v.adicCompletion F) × (v.adicCompletion F))

def emb (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) : E →+* (v.adicCompletion F) :=
  p.comp ((spl : E ⊗[F] (v.adicCompletion F) →+* (v.adicCompletion F) × (v.adicCompletion F)).comp Algebra.TensorProduct.includeLeftRingHom)

lemma emb_apply (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) (e : E) : emb spl p e = p (spl (e ⊗ₜ[F] 1)) := rfl

lemma spl_tmul_one (e : E) :
    spl (e ⊗ₜ[F] 1) = (emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) e, emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) e) := rfl

lemma emb_algebraMap (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F))
    (hp : ∀ a, p (a, a) = a) (f : F) : emb spl p (algebraMap F E f) = algebraMap F (v.adicCompletion F) f := by
  have h : algebraMap F E f ⊗ₜ[F] (1 : (v.adicCompletion F)) = (1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) f := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [emb_apply, h, hspl, hp]

lemma emb_mem_of_isIntegral (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) (e : E) (he : IsIntegral ℤ e) :
    emb spl p e ∈ (v.adicCompletionIntegers F) := by
  obtain ⟨f, hm, hf⟩ := he
  refine (intsV v).mem_of_integral ⟨f.map (Int.castRingHom _), hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hc : (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)).comp
      (Int.castRingHom (v.adicCompletionIntegers F)) = (emb spl p).comp (algebraMap ℤ E) :=
    RingHom.ext_int _ _
  rw [hc, ← Polynomial.hom_eval₂, hf, map_zero]

def phi (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) : 𝓞 E →+* (v.adicCompletionIntegers F) :=
  ((emb spl p).comp (algebraMap (𝓞 E) E)).codRestrict (v.adicCompletionIntegers F)
    (fun z => emb_mem_of_isIntegral spl p _ (RingOfIntegers.isIntegral_coe z))

lemma coe_phi (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) (z : 𝓞 E) :
    (phi spl p z : (v.adicCompletion F)) = emb spl p (algebraMap (𝓞 E) E z) := rfl

def P (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) : Ideal (𝓞 E) := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)).comap (phi spl p)

instance (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) : (P spl p).IsPrime := Ideal.IsPrime.comap _

lemma mem_P (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) (z : 𝓞 E) :
    z ∈ P spl p ↔ Valued.v (emb spl p (algebraMap (𝓞 E) E z)) < 1 := by
  rw [P, Ideal.mem_comap, mem_max_iff]
  exact Iff.rfl

lemma prime_ne_bot (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F))
    (hp : ∀ a, p (a, a) = a) : P spl p ≠ ⊥ := by
  obtain ⟨π, hπ0, hπ⟩ := exists_unif v
  intro hbot
  have hmem : algebraMap (𝓞 F) (𝓞 E) π ∈ P spl p := by
    rw [mem_P, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E,
      emb_algebraMap spl hspl p hp]
    exact hπ
  rw [hbot, Ideal.mem_bot] at hmem
  apply hπ0
  have := congrArg (algebraMap (𝓞 E) E) hmem
  rw [map_zero, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
  exact (map_eq_zero_iff _ (algebraMap F E).injective).1 this

theorem sub_dir (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (x : E ⊗[F] (v.adicCompletion F))
    (hx : x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) ((v.adicCompletionIntegers F)).toSubring) :
    (spl x).1 ∈ (v.adicCompletionIntegers F) ∧ (spl x).2 ∈ (v.adicCompletionIntegers F) := by
  let S : Subring (E ⊗[F] (v.adicCompletion F)) :=
    (((v.adicCompletionIntegers F)).toSubring.prod ((v.adicCompletionIntegers F)).toSubring).comap (spl : E ⊗[F] (v.adicCompletion F) →+* (v.adicCompletion F) × (v.adicCompletion F))
  have hS : tensInt (F := F) (v.adicCompletion F) (intOE E) ((v.adicCompletionIntegers F)).toSubring ≤ S := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨e, he⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨z, rfl⟩ := RingHom.mem_range.1 he
      have hz : IsIntegral ℤ (algebraMap (𝓞 E) E z) := RingOfIntegers.isIntegral_coe z
      show spl (algebraMap (𝓞 E) E z ⊗ₜ[F] 1) ∈
        ((v.adicCompletionIntegers F)).toSubring.prod ((v.adicCompletionIntegers F)).toSubring
      rw [spl_tmul_one, Subring.mem_prod]
      exact ⟨emb_mem_of_isIntegral spl (RingHom.fst _ _) _ hz,
        emb_mem_of_isIntegral spl (RingHom.snd _ _) _ hz⟩
    · show spl ((1 : E) ⊗ₜ[F] y) ∈
        ((v.adicCompletionIntegers F)).toSubring.prod ((v.adicCompletionIntegers F)).toSubring
      rw [Subring.mem_prod, hspl]
      exact ⟨hy, hy⟩
  exact Subring.mem_prod.1 (hS hx)

end PI.SplitIntLoc.Proof

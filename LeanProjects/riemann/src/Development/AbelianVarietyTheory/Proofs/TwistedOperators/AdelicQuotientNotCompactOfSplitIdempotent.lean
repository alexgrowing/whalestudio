import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele

noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem bddAbove_of_compact_quotient {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G)
    [CompactSpace (G ⧸ H)] (f : G →* ℝ) (hf : Continuous f) (hH : ∀ h ∈ H, f h = 1) :
    ∃ C : ℝ, ∀ g, f g ≤ C := by
  let φ : G ⧸ H → ℝ := Quotient.lift f fun a b hab => by
    have h := hH _ (QuotientGroup.leftRel_apply.1 hab)
    rw [← mul_one (f a), ← h, ← map_mul, mul_inv_cancel_left]
  have hφ : Continuous φ := hf.quotient_lift _
  obtain ⟨C, hC⟩ := (isCompact_range hφ).bddAbove
  exact ⟨C, fun g => hC ⟨(g : G ⧸ H), rfl⟩⟩

theorem exists_one_lt_ideleNorm (F : Type) [Field F] [NumberField F] :
    ∃ t : Idele F, 1 < ideleNorm t := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  let P : HeightOneSpectrum (𝓞 F) :=
    ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformiser P
  have h1 : ‖(ϖ : P.adicCompletion F)‖ = (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by
    rw [FinitePlace.norm_def, hϖ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    have : Multiplicative.toAdd (WithZero.unzero
        (WithZero.exp_ne_zero : WithZero.exp (-1 : ℤ) ≠ 0)) = -1 := rfl
    rw [this]
    simp
  refine ⟨(localIdele P ϖ)⁻¹, ?_⟩
  rw [map_inv, UnitaryHeckeChar.ideleNorm_localIdele, h1, inv_inv]
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P

theorem commute_map_of_mem_centPts {F E : Type} [Field F] [CommRing E] [Algebra F E]
    {n : Type} [Fintype n] [DecidableEq n] {σ : E →ₐ[F] E} {J : Matrix n n E} {γ : GL n E}
    (R : Type) [CommRing R] [Algebra F R] {ε : Matrix n n E} (hε : ε ∈ genAlg (γ : Matrix n n E))
    {g : GL n (E ⊗[F] R)} (hg : g ∈ centPts σ J γ R) :
    (g : Matrix n n (E ⊗[F] R)) * ε.map (inclE (F := F) R) = ε.map (inclE (F := F) R) * g := by
  have h : (g : Matrix n n (E ⊗[F] R)) * (γ : Matrix n n E).map (inclE (F := F) R) =
      (γ : Matrix n n E).map (inclE (F := F) R) * g :=
    congrArg Units.val (Subgroup.mem_centralizer_singleton_iff.1 hg.2)
  refine commute_of_mem_genAlg h ?_
  induction hε using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
  | algebraMap r =>
    have : (algebraMap E (Matrix n n E) r).map (inclE (F := F) R) =
        algebraMap (E ⊗[F] R) _ (inclE (F := F) R r) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
    rw [this]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add _)]; exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [Matrix.map_mul]; exact mul_mem hx hy

theorem notCompactOfIdempotent_of (hD : IdempotentDet) : NotCompactOfIdempotent := by
  intro F E _ _ _ _ n _ _ σ J γ hreg ε hε hε0 hεε ht hc
  haveI := quad_finite hreg.quad
  letI : TopologicalSpace (E ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := E) (AdeleRing (𝓞 F) F)
  obtain ⟨d, χ, hd, hχ, h1, hmul, hrat, hval⟩ := hD F E n ε hε0 hεε (AdeleRing (𝓞 F) F)
  let χ₀ : centPts σ J γ (AdeleRing (𝓞 F) F) →* AdeleRing (𝓞 F) F :=
    { toFun := fun g => χ (g.1 : Matrix n n _)
      map_one' := h1
      map_mul' := fun g h => hmul _ _ (commute_map_of_mem_centPts _ hε h.2) }
  have hχ₀ : Continuous χ₀ := hχ.comp (Units.continuous_val.comp continuous_subtype_val)
  have hχi : Continuous fun g => χ₀ g⁻¹ :=
    hχ.comp (Units.continuous_coe_inv.comp continuous_subtype_val)
  have hχ₁ : Continuous χ₀.toHomUnits := Units.continuous_iff.2 ⟨hχ₀, hχi⟩
  haveI : CompactSpace (centPts σ J γ (AdeleRing (𝓞 F) F) ⧸
    ((centRat σ J γ).map (bc (inclE (F := F) (AdeleRing (𝓞 F) F)))).subgroupOf
      (centPts σ J γ (AdeleRing (𝓞 F) F))) := hc
  obtain ⟨C, hC⟩ := bddAbove_of_compact_quotient
    (((centRat σ J γ).map (bc (inclE (F := F) (AdeleRing (𝓞 F) F)))).subgroupOf
      (centPts σ J γ (AdeleRing (𝓞 F) F))) (ideleNorm.comp χ₀.toHomUnits)
    (continuous_ideleNorm.comp hχ₁) (by
      rintro g ⟨δ, -, hδ⟩
      obtain ⟨c, hc⟩ := hrat δ
      have e : ((χ₀.toHomUnits g : Idele F) : AdeleRing (𝓞 F) F) = algebraMap F _ c := by
        rw [← hc]
        change χ (g.1 : Matrix n n _) = _
        rw [show g.1 = _ from hδ.symm]
        rfl
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [map_zero] at e
        haveI : Nontrivial (AdeleRing (𝓞 F) F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
        exact Units.ne_zero _ e
      have e' : χ₀.toHomUnits g = principalIdele F (Units.mk0 c hc0) := Units.ext e
      rw [MonoidHom.comp_apply, e', ideleNorm_principalIdele])
  obtain ⟨t, ht1⟩ := exists_one_lt_ideleNorm F
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C (one_lt_pow₀ ht1 hd.ne')
  obtain ⟨g, hg, hgt⟩ := ht (t ^ m)
  have e : χ₀.toHomUnits ⟨g, hg⟩ = (t ^ m) ^ d := Units.ext (hval _ _ hgt)
  have := hC ⟨g, hg⟩
  rw [MonoidHom.comp_apply, e, map_pow, map_pow, ← pow_mul, mul_comm, pow_mul] at this
  exact absurd hm (not_lt.2 this)

end GlobalTheory.RegSS

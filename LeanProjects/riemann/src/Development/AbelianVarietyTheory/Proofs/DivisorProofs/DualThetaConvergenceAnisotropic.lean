import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCuspidalNeZero
open scoped TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

open scoped Matrix

namespace GlobalTheory.ThK.AnConv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem form_eq (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (z : Fin n → E) :
    form σ J z z = σ (hE σ (J.map σ) z z) := by
  simp only [form, hE, Formalism.UG.hform, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul, AlgHom.coe_toRingHom,
    RingHom.coe_coe, hσ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem aniso_sig {n s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M 0 s) (y : Fin n → ℂ)
    (hy : y ⬝ᵥ M *ᵥ star y = 0) : y = 0 := by
  obtain ⟨hs, A, hA⟩ := h
  let e : (Fin 0 ⊕ Fin s) ≃ Fin n := (Equiv.emptySum (Fin 0) (Fin s)).trans (finCongr (by omega))
  set D : Matrix (Fin 0 ⊕ Fin s) (Fin 0 ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hD
  have hDD : D * D = 1 := by
    rw [hD, Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]
  have h1 : Aᵀ * (M * A.map star * D) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, hDD]
  have h2 : (M * A.map star * D) * Aᵀ = 1 := (Matrix.mul_eq_one_comm_of_equiv e).mp h1
  have h3 : A * (M * A.map star * D)ᵀ = 1 := by
    have := congrArg Matrix.transpose h2
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  set w := (M * A.map star * D)ᵀ *ᵥ y
  have hyw : y = A *ᵥ w := by rw [Matrix.mulVec_mulVec, h3, Matrix.one_mulVec]
  have hst : star (A *ᵥ w) = A.map star *ᵥ star w := by
    ext i; simp [Matrix.mulVec, dotProduct, star_sum]
  have key : y ⬝ᵥ M *ᵥ star y = w ⬝ᵥ D *ᵥ star w := by
    rw [← hA, hyw, hst, Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.vecMul_transpose,
      Matrix.vecMul_vecMul]
    simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc]
  have h0 : w ⬝ᵥ D *ᵥ star w = 0 := key.symm.trans hy
  have hsum : ∑ i : Fin s, w (Sum.inr i) * star (w (Sum.inr i)) = 0 := by
    simp [hD, dotProduct, Matrix.mulVec, Matrix.fromBlocks, Fintype.sum_sum_type] at h0
    simpa [Matrix.one_apply] using h0
  have hz : ∀ i, w (Sum.inr i) = 0 := by
    have hr : ∑ i : Fin s, Complex.normSq (w (Sum.inr i)) = 0 := by
      have : ((∑ i : Fin s, Complex.normSq (w (Sum.inr i)) : ℝ) : ℂ) = 0 := by
        rw [← hsum]; push_cast; refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.star_def, Complex.mul_conj]
      exact_mod_cast this
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (w (Sum.inr j)))).mp hr i (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.mp this
  have hw : w = 0 := by
    funext i; rcases i with i | i
    · exact i.elim0
    · exact hz i
  rw [hyw, hw, Matrix.mulVec_zero]

theorem aniso_herm {n s : ℕ} (B : Base F E) (hB : B.IsGood σ) (X : Spc F E n) (h : X.IsHerm σ B 0 s) :
    ∀ x, form σ X.J x x = 0 → x = 0 := by
  intro x hx
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  let τ : E →+* ℂ := (B.emb w).1
  have hcm : ∀ z : E, τ (σ z) = star (τ z) := fun z => hB.cm.2.2.2 τ z
  have hy : (fun i => τ (x i)) ⬝ᵥ (X.J.map τ) *ᵥ star (fun i => τ (x i)) = 0 := by
    have := congrArg τ hx
    rw [map_zero] at this
    have hs : (star fun i => τ (x i)) = τ ∘ fun i => σ (x i) := by
      ext i; simp [hcm]
    rw [← this, hs, form, RingHom.map_dotProduct]
    show (τ ∘ x) ⬝ᵥ _ = (τ ∘ x) ⬝ᵥ _
    congr 1
    ext i
    exact (RingHom.map_mulVec τ X.J _ i).symm
  have := aniso_sig (h.sig w) _ hy
  funext i
  exact τ.injective (by simpa using congrFun this i)

theorem conv : GlobalTheory.Published.SiegelSetUnitary → ThetaBasic → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.q = 0 → ∀ Φ' ∈ schA F (Fin a' × Fin (a + a')), G.M'.Conv om' Φ' := by
  intro hP hTB F E _ _ _ _ _ σ B a a' G X om om' hT hq Φ' hΦ' h
  have hcm := hT.base.cm
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm

  have hV' := hT.geo.hV'
  rw [hq] at hV'
  have han := aniso_herm B hT.base G.V' hV'
  have hJ : IsHermND σ (G.V'.J.map σ) := GlobalTheory.UnitaryVol.isHermND_map hσ hT.geo.hV'

  have hW : GlobalTheory.SiegelSet.IsWittFrame σ (G.V'.J.map σ) (0 : Matrix (Fin a') (Fin 0) E) 0 :=
    ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, fun z _ _ hz =>
      han z (by rw [form_eq hσ, hz, map_zero])⟩
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.SiegelSet.Model.compact_quotient hP hcm hJ hW

  have heq : UG (cA σ) (incM F G.V'.J) = HR (AF F) σ (G.V'.J.map σ) := by
    have h := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := G.V'.J) hσ one_ne_zero
    rw [one_smul] at h
    exact h
  let e : UA σ G.V'.J ≃* GAd σ (G.V'.J.map σ) := MulEquiv.subgroupCongr heq
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _

  obtain ⟨hcont, hinv, -⟩ := (hTB F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _
    (Check.isPair_of_isTriple hT).2).1 Φ' hΦ'
  have hf : Continuous fun g => theta om' Φ' g h := hcont.comp (continuous_id.prodMk continuous_const)

  obtain ⟨M, hM⟩ := (hC.image he').exists_bound_of_continuousOn hf.continuousOn
  have hbd : ∀ g, ‖theta om' Φ' g h‖ ≤ M := by
    intro g
    obtain ⟨γ, hγ, s, hs, hgs⟩ := hcov (e g)
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
    have hr : e.symm γ ∈ ratU σ G.V'.J := Subgroup.mem_subgroupOf.2 ⟨u, hu⟩
    have hg : g = e.symm γ * e.symm s := by
      rw [← map_mul, ← hgs, MulEquiv.symm_apply_apply]
    have h1 := hinv (e.symm γ) hr 1 (one_mem _) (e.symm s) h
    rw [one_mul] at h1
    rw [hg, h1]
    exact hM _ ⟨s, hs, rfl⟩
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  have hfin := GlobalTheory.UnitaryVol.measure_dom_lt_top F E σ B a a' G X om om' hP hT
  exact Measure.integrableOn_of_bounded (M := M) hfin.ne hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbd)

end GlobalTheory.ThK.AnConv

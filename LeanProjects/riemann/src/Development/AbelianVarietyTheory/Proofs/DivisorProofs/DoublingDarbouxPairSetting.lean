import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePlaceVacuumAnyDarbouxCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOfIsStabSkew
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer

noncomputable section

namespace GlobalTheory.DblWeilCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem dotProduct_pairVec {A : Type} [CommRing A] {n : ℕ} (x y x' y' : Fin n → A) :
    pairVec finSumFinEquiv x y ⬝ᵥ pairVec finSumFinEquiv x' y' = x ⬝ᵥ x' + y ⬝ᵥ y' := by
  simp only [dotProduct]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [pairVec_inl, pairVec_inr]

theorem form_dblGram {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y₁ y₂ x₁ x₂ : Fin n → E) :
    form σ (dblGram finSumFinEquiv J) (pairVec finSumFinEquiv y₁ y₂) (pairVec finSumFinEquiv x₁ x₂) =
      form σ J y₁ x₁ - form σ J y₂ x₂ := by
  have hs : (fun i => σ (pairVec finSumFinEquiv x₁ x₂ i)) =
      pairVec finSumFinEquiv (fun i => σ (x₁ i)) (fun i => σ (x₂ i)) := by
    funext j; obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective j <;> simp only [pairVec_inl, pairVec_inr]
  simp only [form, hs, dblGram, blkMat_mulVec, dotProduct_pairVec, Matrix.neg_mulVec, dotProduct_neg, sub_eq_add_neg]

theorem hasSig_dbl {d r s : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (h : HasSig M r s) :
    HasSig (blkMat finSumFinEquiv M (-M)) (r + s) (s + r) := by
  obtain ⟨hd, A, hA⟩ := h
  let f : Fin (r + s) ⊕ Fin (s + r) → (Fin r ⊕ Fin s) ⊕ (Fin r ⊕ Fin s) :=
    Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.inr ∘ Sum.inr) ∘ finSumFinEquiv.symm)
      (Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inl) ∘ finSumFinEquiv.symm)
  refine ⟨by omega, (Matrix.fromBlocks A 0 0 A).submatrix finSumFinEquiv.symm f, ?_⟩
  have key : (Matrix.fromBlocks A 0 0 A)ᵀ * Matrix.fromBlocks M 0 0 (-M) * (Matrix.fromBlocks A 0 0 A).map star =
      Matrix.fromBlocks (Aᵀ * M * A.map star) 0 0 (-(Aᵀ * M * A.map star)) := by
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  rw [Matrix.transpose_submatrix, ← Matrix.submatrix_map, blkMat, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, key, hA]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j <;>
    rcases i with i | i <;> rcases j with j | j <;> simp [f, Matrix.one_apply] <;> simp [Fin.ext_iff] <;> omega

theorem form_zero_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E) : form σ J y 0 = 0 := by
  simp [form, Pi.zero_apply, map_zero, ← Pi.zero_def]

theorem exists_isSkew_dbl (B : Base F E) (hcm : IsCMExt F E σ) {n r s : ℕ} (W : Spc F E n) (hW : W.IsSkew σ B r s)
    (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E) (hJ : J₂ = dblGram finSumFinEquiv W.J) :
    ∃ (L : Submodule (𝓞 E) (Fin (n + n) → E)) (θ : InfinitePlace F → Matrix (Fin (n + n)) (Fin (n + n)) ℂ)
      (bas : ∀ v : Pl F, GL (Fin (n + n)) (Fv F v)), (Spc.mk J₂ L θ bas).IsSkew σ B (r + s) (s + r) := by
  classical
  subst hJ
  haveI : Submodule.IsLattice E W.L := hW.lat
  have hex : ∀ v : B.P, ∃ β, IsSplitBasis (B.τ v) (sumLat finSumFinEquiv W.L W.L) β :=
    fun v => exists_isSplitBasis (B.τ v) _ hcm
  refine ⟨sumLat finSumFinEquiv W.L W.L, fun w => blkMat finSumFinEquiv (W.θ w) (-W.θ w),
    fun v => if h : v ∈ B.P then (hex ⟨v, h⟩).choose else 1, ⟨?_, ?_, inferInstance, ?_, ?_, ?_⟩⟩
  · intro i j
    show σ (dblGram finSumFinEquiv W.J j i) = -dblGram finSumFinEquiv W.J i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [dblGram, blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
        Matrix.neg_apply, map_zero, map_neg, neg_zero, hW.skew]
  · intro w
    show HasSig (Complex.I • (dblGram finSumFinEquiv W.J).map (B.emb w).1) (r + s) (s + r)
    rw [dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _), GlobalTheory.DblUnfoldCont.smul_blkMat, smul_neg]
    exact hasSig_dbl _ (hW.sig w)
  · intro y
    show y ∈ sumLat finSumFinEquiv W.L W.L ↔ ∀ x ∈ sumLat finSumFinEquiv W.L W.L, ∀ o : 𝓞 E,
      IsIntegral ℤ (Algebra.trace ℚ E (o * form σ (dblGram finSumFinEquiv W.J) y x))
    refine ⟨fun hy x hx o => ?_, fun H => ?_⟩
    · rw [← pairVec_eta finSumFinEquiv y] at hy ⊢
      rw [← pairVec_eta finSumFinEquiv x] at hx ⊢
      rw [pairVec_mem_sumLat] at hy hx
      rw [form_dblGram, mul_sub, map_sub]
      exact ((hW.dual _).1 hy.1 _ hx.1 o).sub ((hW.dual _).1 hy.2 _ hx.2 o)
    · rw [← pairVec_eta finSumFinEquiv y, pairVec_mem_sumLat]
      constructor
      · refine (hW.dual _).2 fun x hx o => ?_
        have h1 := H (pairVec finSumFinEquiv x 0) ((pairVec_mem_sumLat _).2 ⟨hx, zero_mem _⟩) o
        rw [← pairVec_eta finSumFinEquiv y, form_dblGram, form_zero_right, sub_zero] at h1
        exact h1
      · refine (hW.dual _).2 fun x hx o => ?_
        have h1 := H (pairVec finSumFinEquiv 0 x) ((pairVec_mem_sumLat _).2 ⟨zero_mem _, hx⟩) (-o)
        rw [← pairVec_eta finSumFinEquiv y, form_dblGram, form_zero_right, zero_sub,
          show ((-o : 𝓞 E) : E) = -(o : E) by simp, neg_mul_neg] at h1
        exact h1
  · intro w
    show IsCartan (Complex.I • (dblGram finSumFinEquiv W.J).map (B.emb w).1) (blkMat finSumFinEquiv (W.θ w) (-W.θ w))
    rw [dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _), GlobalTheory.DblUnfoldCont.smul_blkMat, smul_neg]
    exact GlobalTheory.DblUnfoldCont.isCartan_dbl _ _ (hW.cartan w)
  · intro v
    show IsSplitBasis (B.τ v) (sumLat finSumFinEquiv W.L W.L) (if h : (v : Pl F) ∈ B.P then (hex ⟨v, h⟩).choose else 1)
    rw [dif_pos v.2]
    exact (hex v).choose_spec

theorem exists_weil : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E)
    (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ), IsPair B M χX χW om r s' r₁ s₁ →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F Xs.J) (incM F W₂.J)) (Fin n × Fin (d + d)),
      (∀ x : Matrix (Fin n) (Fin (d + d)) E, ∃ y z : Fin n × Fin (d + d) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ om₂ : Rep σ Xs W₂, IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F Xs.J) (incM F W₂.J) co χX 1 om₂ := by
  intro hP F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hpair W₂ hJ co hco
  classical
  have hB := hpair.base
  have hV := hpair.herm
  obtain ⟨L, θ, bas, hS⟩ := exists_isSkew_dbl B hB.cm W hpair.skew W₂.J hJ
  let S : Spc F E (d + d) := ⟨W₂.J, L, θ, bas⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕⟩ := GlobalTheory.ModelEx.exists_haar_fundDom F E σ n Xs.J
  have hI := GlobalTheory.VacIndic.eventually_isVac_indicator B hB Xs S _ _ _ _ hV hS co hco
  let M₀ : Model σ Xs S := ⟨co, fun _ => 0, 0, ∅⟩
  let ind : ∀ v : Pl F, (Fin n × Fin (d + d) → Fv F v) → ℂ := fun v =>
    Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let vac : ∀ v : Pl F, (Fin n × Fin (d + d) → Fv F v) → ℂ := fun v =>
    if M₀.IsVac B.ψ v (ind v) then ind v else (GlobalTheory.T.exists_finitePlace_vacuum_any_darboux_coordinates B hB Xs S _ _ _ _ hV hS co v).choose
  let M₂ : Model σ Xs S := ⟨co, vac, μ, 𝓕⟩
  have hM : M₂.IsGood B.ψ := by
    refine ⟨hco, fun v => ?_, ?_, hμ, h𝓕⟩
    · show M₀.IsVac B.ψ v (vac v)
      by_cases h : M₀.IsVac B.ψ v (ind v)
      · simp only [vac, if_pos h]; exact h
      · simp only [vac, if_neg h]; exact (GlobalTheory.T.exists_finitePlace_vacuum_any_darboux_coordinates B hB Xs S _ _ _ _ hV hS co v).choose_spec
    · filter_upwards [hI] with v hv
      show vac v = ind v
      exact if_pos hv
  have h1 : IsHecke F E (1 : Chr F E) := ⟨continuous_const, fun _ => rfl⟩
  have hr1 : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (1 : Chr F E) (d + d) := by
    intro x
    rw [(show Even (d + d) from ⟨_, rfl⟩).neg_one_pow, ite_self]
    simp
  obtain ⟨om₂, hom₂⟩ := GlobalTheory.WeilExGen.exists_isWeil hP F E σ B hB n _ Xs S _ _ _ _ hV hS M₂ hM χX 1
    hpair.hX h1 hpair.resX hr1
  exact ⟨om₂, hom₂⟩

end GlobalTheory.DblWeilCoord

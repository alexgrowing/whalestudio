import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

namespace GlobalTheory.ThK.PlaneVac

open GlobalTheory.ThK.Adapt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def idx' {n d d₁ : ℕ} (hd : d = d₁ + 2) : Fin n × Fin d ≃ Fin n × Fin 2 ⊕ Fin n × Fin d₁ :=
  (idx hd).trans (Equiv.sumComm _ _)

theorem insert_zero_eq_glue {R : Type} [Zero R] {n d d₁ : ℕ} (hd : d = d₁ + 2) (b : Fin n × Fin d₁ → R) :
    ins0 hd b = glue (idx' hd) 0 b := by
  funext k
  simp only [ins0, glue, idx', Equiv.trans_apply]
  rcases idx hd k with p | p <;> rfl

theorem eq_glue_of {R : Type} [Zero R] {n d d₁ : ℕ} (hd : d = d₁ + 2) (x : Fin n × Fin d → R)
    (hx : ∀ p, x ((idx hd).symm (Sum.inl p)) = 0) : x = glue (idx' hd) (fun k => x ((idx' hd).symm (.inl k))) 0 := by
  funext k
  obtain ⟨k, rfl⟩ := (idx' hd).symm.surjective k
  rcases k with k | k
  · rw [glue_inl]
  · rw [glue_inr]; exact hx k

theorem mul_frame {n d d₁ : ℕ} (H : Plane E d d₁) (w : Matrix (Fin n) (Fin d₁ ⊕ Fin 2) (AE F E)) :
    w * (incM F (frame H))ᵀ = Matrix.vecMulVec (fun i => w i (.inr 0)) (incV F H.x) +
      w.submatrix id .inl * (incM F H.ι)ᵀ + Matrix.vecMulVec (fun i => w i (.inr 1)) (incV F H.y) := by
  ext i j
  simp [Matrix.mul_apply, frame, incM, incV, Matrix.vecMulVec_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem hTens_frame {B : Base F E} {n d d₁ r' s' i₀ i₁ : ℕ} (X : Spc F E n) {W : Spc F E d} {W₁ : Spc F E d₁}
    {H : Plane E d d₁} (hB : B.IsGood σ) (hW : W.IsSkew σ B r' s') (hH : H.IsAdapted σ B W W₁ i₀ i₁)
    (w w' : Matrix (Fin n) (Fin d₁ ⊕ Fin 2) (AE F E)) :
    hTens (cA σ) (incM F X.J) (incM F W.J) (w * (incM F (frame H))ᵀ) (w' * (incM F (frame H))ᵀ) =
      -(∑ i, ∑ k, w i (.inr 1) * incM F X.J i k * cA σ (w' k (.inr 0))) +
        ∑ i, ∑ k, w i (.inr 0) * incM F X.J i k * cA σ (w' k (.inr 1)) +
        hTens (cA σ) (incM F X.J) (incM F W₁.J) (w.submatrix id .inl) (w'.submatrix id .inl) := by
  have hg := frame_gram hB hH (η := -1) (by simp) (fun i j => by rw [hW.skew]; simp)
  have hg' : (incM F (frame H))ᵀ * incM F W.J * (incM F (frame H)).map (cA σ) =
      Matrix.fromBlocks (incM F W₁.J) 0 0 !![0, 1; -1, 0] := by
    have e : (incM F (frame H)).map (cA σ) = incM F ((frame H).map σ) := by
      ext i j
      exact GlobalTheory.VacIndic.cA_inclR _ _
    rw [e, show (incM F (frame H))ᵀ = incM F (frame H)ᵀ from rfl, ← incM_mul, ← incM_mul, hg]
    ext (a | a) (b | b)
    · rfl
    · simp [incM]
    · simp [incM]
    · fin_cases a <;> fin_cases b <;> simp [incM]
  have h := hTens_mul (cA σ) (incM F X.J) (incM F W.J) 1 (incM F (frame H)) w w'
  rw [Matrix.one_mul, Matrix.one_mul, hg', Matrix.transpose_one, Matrix.one_mul,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, hTens_plane_right] at h
  rw [h, neg_one_mul]

theorem exists_vacua (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁)
    (M₁ : Model σ X W₁) (hd : d = d₁ + 2) (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (hM₁ : M₁.IsGood B.ψ)
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
    (hc : (∀ z : Matrix (Fin n) (Fin d₁) (AE F E),
        co.e (z * (incM F H'.ι)ᵀ) = (ins0 hd (M₁.co.e z).1, ins0 hd (M₁.co.e z).2)) ∧
      (∀ a : Fin n → AE F E, (co.e (Matrix.vecMulVec a (incV F H'.x))).1 = 0 ∧
        ∀ p, (co.e (Matrix.vecMulVec a (incV F H'.x))).2 ((idx hd).symm (Sum.inl p)) = 0) ∧
      (∀ b : Fin n → AE F E, (co.e (Matrix.vecMulVec b (incV F H'.y))).2 = 0 ∧
        ∀ p, (co.e (Matrix.vecMulVec b (incV F H'.y))).1 ((idx hd).symm (Sum.inl p)) = 0) ∧
      ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∃ vac : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ,
      (∀ v, (Model.mk co vac 0 ∅ : Model σ X W).IsVac B.ψ v (vac v)) ∧
      (∀ᶠ v in cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      ∀ v, ev hd v (vac v) = M₁.vac v := by
  classical
  obtain ⟨hι, hx, hy, hr⟩ := hc
  obtain ⟨Q, hQ1, hQ2, hQ⟩ := exists_frame_inv hH hW.lat
  let ε : Fin n × Fin d ≃ Fin n × Fin 2 ⊕ Fin n × Fin d₁ := idx' hd
  let Tr := Algebra.trace (AF F) (AE F E)
  let w : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d₁ ⊕ Fin 2) (AE F E) := fun z => z * (incM F Q)ᵀ
  have hw : ∀ z, w z * (incM F (frame H'))ᵀ = z := fun z => by
    show z * _ * _ = z
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← incM_mul, hQ1, incM, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one, Matrix.mul_one]
  let π : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d₁) (AE F E) := fun z => (w z).submatrix id .inl
  let δ : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (AE F E) :=
    fun z => Matrix.vecMulVec (fun i => w z i (.inr 0)) (incV F H'.x)
  let p : Matrix (Fin n) (Fin d) (AE F E) → Fin n × Fin 2 → AF F :=
    fun z k => (co.e (Matrix.vecMulVec (fun i => w z i (.inr 1)) (incV F H'.y))).1 (ε.symm (.inl k))
  let q : Matrix (Fin n) (Fin d) (AE F E) → Fin n × Fin 2 → AF F := fun z k => (co.e (δ z)).2 (ε.symm (.inl k))
  have hδe : ∀ z, co.e (δ z) = (0, glue ε (q z) 0) := fun z => Prod.ext (hx _).1 (eq_glue_of hd _ (hx _).2)
  have hco : ∀ z, co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2) := fun z => by
    have hye : co.e (Matrix.vecMulVec (fun i => w z i (.inr 1)) (incV F H'.y)) = (glue ε (p z) 0, 0) :=
      Prod.ext (eq_glue_of hd _ (hy _).2) (hy _).1
    conv_lhs => rw [← hw z, mul_frame, map_add, map_add, hye, hι, insert_zero_eq_glue, insert_zero_eq_glue]
    rw [show co.e (Matrix.vecMulVec (fun i => w z i (.inr 0)) (incV F H'.x)) = _ from hδe z]
    simp only [Prod.mk_add_mk, zero_add, add_zero]
    rw [glue_add, glue_add]
    simp only [zero_add, add_zero]
    rfl
  let u : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (AE F E) → AE F E :=
    fun z z' => -(∑ i, ∑ k, w z i (.inr 1) * incM F X.J i k * cA σ (w z' k (.inr 0)))
  have hm : ∀ z, w z * (mask (AE F E) d₁ 0 1 0)ᵀ =
      Matrix.of fun i => Sum.elim (fun _ => (0 : AE F E)) ![w z i (.inr 0), 0] := fun z => by
    ext i j
    rw [mask, Matrix.diagonal_transpose, Matrix.mul_diagonal]
    rcases j with j | j
    · simp
    · fin_cases j <;> simp
  have hδm : ∀ z, δ z = w z * (mask (AE F E) d₁ 0 1 0)ᵀ * (incM F (frame H'))ᵀ := fun z => by
    rw [mul_frame, hm]
    ext i j
    simp [δ, Matrix.vecMulVec_apply, Matrix.mul_apply]
  have hu : ∀ z z', hTens (cA σ) (incM F X.J) (incM F W.J) z (δ z') = u z z' := fun z z' => by
    conv_lhs => rw [← hw z, hδm, hTens_frame X hB hW hH, hm]
    simp [u, hTens]
  have hH2 : ∀ z, hTens (cA σ) (incM F X.J) (incM F W.J) z z =
      u z z - cA σ (u z z) + hTens (cA σ) (incM F X.J) (incM F W₁.J) (π z) (π z) := fun z => by
    have hJ : ∀ i j, cA σ (incM F X.J j i) = 1 * incM F X.J i j := fun i j => by
      rw [one_mul]
      exact (GlobalTheory.VacIndic.cA_inclR _ _).trans (congrArg (inclR (F := F) (AF F)) (hX.herm i j))
    conv_lhs => rw [← hw z, hTens_frame X hB hW hH]
    simp only [u]
    rw [map_neg, conj_pair _ (cA_cA hB) hJ, one_mul, sub_neg_eq_add]
  have hpq : ∀ z z', p z ⬝ᵥ q z' = -Tr (u z z') := fun z z' => by
    have h1 := co.form z (δ z')
    rw [hδe, hco z] at h1
    simp only [glue_dot, dotProduct_zero, zero_dotProduct, add_zero, sub_zero] at h1
    rw [← h1, symp, hu, neg_one_mul, map_neg]
  have hTr : ∀ z, Tr (cA σ z) = Tr z := GlobalTheory.VacCocycle.trace_conj (cA σ) (cA_cA hB)
  have h1M : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hlat : ∀ v, ∀ γ ∈ latAtV X W v, π γ ∈ latAtV X W₁ v := fun v γ hγ => by
    have := lat_map (X₁ := X) (W₁ := W₁) (A := 1) (A' := Q.submatrix .inl id) (fun u hu => by rwa [Matrix.one_mulVec])
      (fun u hu => (hQ u hu).1) hγ
    rw [h1M, Matrix.one_mul] at this
    exact this
  have hδl : ∀ v, ∀ γ ∈ latAtV X W v, δ γ ∈ latAtV X W v := fun v γ hγ => by
    have := lat_map (X₁ := X) (W₁ := W) (A := 1) (fun u hu => by rwa [Matrix.one_mulVec]) (mask_mem hH hQ 0 1 0) hγ
    rw [h1M, Matrix.one_mul, incM_mul, incM_mul, incM_mask, Matrix.transpose_mul, Matrix.transpose_mul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc] at this
    rw [hδm]
    exact this
  have hδ : ∀ v, ∀ γ ∈ latAtV X W v, ∀ γ' ∈ latAtV X W v, ∀ θ : 𝓞 E,
      B.ψ (Tr (inclR (F := F) (AF F) (θ : E) * u γ' γ)) = 1 := fun v γ hγ γ' hγ' θ => by
    have := GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W r s r' s' hB hX hW v θ 1 (by rw [map_one]; exact one_mem _) γ' hγ' _
      (hδl v γ hγ)
    rwa [one_mul, symp, hu] at this
  have hv : ∀ v, ∃ φa, Model.IsVac (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W) B.ψ v φa ∧ ∀ c, φa (glue ε 0 c) = M₁.vac v c := by
    intro v
    refine exists_isVac ε hX hW _ M₁ hr p q π hco v (hlat v) (fun γ hγ γ' hγ' => ?_)
      (fun θ hθ γ hγ => ?_) (hM₁.vac v)
    · have := hδ v γ hγ γ' hγ' (-1)
      rw [show ((-1 : 𝓞 E) : E) = -1 by simp, map_neg, map_one, neg_one_mul, map_neg] at this
      rw [hpq, this]
    · rw [← one_mul (B.ψ _ * B.ψ _), ← hδ v γ hγ γ hγ θ]
      simp only [← AddChar.map_add_eq_mul]
      congr 1
      have h1 : inclR (F := F) (AF F) (θ : E) + cA σ (inclR (F := F) (AF F) (θ : E)) = 1 := by
        rw [GlobalTheory.VacIndic.cA_inclR, ← map_add, hθ, map_one]
      have h2 : Tr (inclR (F := F) (AF F) (θ : E) * cA σ (u γ γ)) =
          Tr (u γ γ) - Tr (inclR (F := F) (AF F) (θ : E) * u γ γ) := by
        rw [← hTr, map_mul, cA_cA hB, ← map_sub, eq_sub_of_add_eq' h1, sub_mul, one_mul]
      have h3 : (⅟(2 : AF F)) * 2 = 1 := invOf_mul_self _
      show _ * Tr _ = _ + (_ + _ * Tr _)
      rw [hpq, hH2, mul_add (inclR (F := F) (AF F) (θ : E)), mul_sub, map_add, map_sub, h2]
      generalize (⅟(2 : AF F)) = t at h3 ⊢
      linear_combination (Tr (inclR (F := F) (AF F) (θ : E) * u γ γ)) * h3
  choose φa hφa hφb using hv
  let S : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v => Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let G : Pl F → Prop := fun v => Model.IsVac (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W) B.ψ v (S v) ∧
    M₁.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  refine ⟨fun v => if G v then S v else φa v, fun v => ?_, ?_, fun v => funext fun c => ?_⟩
  · show Model.IsVac _ _ _ (if G v then S v else φa v)
    split_ifs with h
    · exact h.1
    · exact hφa v
  · filter_upwards [GlobalTheory.VacIndic.eventually_isVac_indicator B hB X W r s r' s' hX hW co hr, hM₁.std] with v h1 h2
    exact if_pos ⟨h1, h2⟩
  · rw [ev_apply, insert_zero_eq_glue]
    by_cases h : G v
    · show (if G v then S v else φa v) _ = _
      rw [if_pos h, h.2]
      refine Set.indicator_eq_indicator ⟨fun hx i => ?_, fun hx i => ?_⟩ rfl
      · simpa using hx ((idx' hd).symm (.inr i))
      · obtain ⟨i, rfl⟩ := (idx' hd).symm.surjective i
        rcases i with i | i
        · rw [glue_inl]; exact zero_mem _
        · rw [glue_inr]; exact hx i
    · show (if G v then S v else φa v) _ = _
      rw [if_neg h, hφb]

end GlobalTheory.ThK.PlaneVac

end

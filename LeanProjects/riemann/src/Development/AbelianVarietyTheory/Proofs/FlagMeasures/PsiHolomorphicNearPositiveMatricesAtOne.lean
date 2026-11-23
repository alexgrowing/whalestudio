import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerRepK
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Dec.FormF
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec

variable {n : ℕ}

theorem posDef_mem_Omega {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) : x ∈ Omega n := by
  intro i
  have hsub : (x.submatrix (Fin.castLE i.isLt) (Fin.castLE i.isLt)).PosDef :=
    hx.submatrix (Fin.castLE_injective _)
  exact hsub.det_pos.ne'

theorem posDef_mem_kConjNonzeroMinorsSet (ε : Fin n → Bool) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) : x ∈ U1 ε := by
  intro k hk
  have hu : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk.1
  rw [Matrix.inv_eq_left_inv hu, Matrix.star_eq_conjTranspose]
  apply posDef_mem_Omega
  apply hx.conjTranspose_mul_mul_same
  intro v v' h
  have h2 := congrArg (fun u => (star k).mulVec u) h
  simpa only [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec] using h2

theorem continuous_leadMinor_conj (ε : Fin n → Bool) (l : ℕ) (hl : l ≤ n) :
    Continuous (fun p : KG ε × (Fin n → Fin n → ℂ) =>
      leadMinor ((toMK p.1)⁻¹ * Matrix.of p.2 * toMK p.1) l hl) := by
  have hinv : ∀ k : KG ε, (toMK k)⁻¹ = (toMK k)ᴴ := fun k =>
    Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp ((mem_KG ε _).1 k.2).1)
  simp_rw [hinv]
  unfold leadMinor
  have hc : Continuous (fun k : KG ε => toMK k) := toMK_cont ε
  have hz : Continuous (fun p : KG ε × (Fin n → Fin n → ℂ) => Matrix.of p.2) := continuous_snd
  exact ((((hc.comp continuous_fst).matrix_conjTranspose).matrix_mul hz).matrix_mul
    (hc.comp continuous_fst)).matrix_submatrix _ _ |>.matrix_det

theorem isOpen_kConjNonzeroMinorsSet (ε : Fin n → Bool) : IsOpen {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := by
  have hset : {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} =
      (Prod.snd '' {p : KG ε × (Fin n → Fin n → ℂ) | ∃ i : Fin n,
        leadMinor ((toMK p.1)⁻¹ * Matrix.of p.2 * toMK p.1) (i.val + 1) i.isLt = 0})ᶜ := by
    ext z
    constructor
    · rintro hz ⟨⟨k, z'⟩, ⟨i, hi⟩, rfl⟩
      exact hz (toMK k) ((mem_KG ε _).1 k.2) i hi
    · intro hz g hg i hi
      obtain ⟨k, rfl⟩ : g ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hg
      exact hz ⟨⟨k, z⟩, ⟨i, hi⟩, rfl⟩
  rw [hset, isOpen_compl_iff]
  refine isClosedMap_snd_of_compactSpace _ ?_
  have hu : {p : KG ε × (Fin n → Fin n → ℂ) | ∃ i : Fin n,
      leadMinor ((toMK p.1)⁻¹ * Matrix.of p.2 * toMK p.1) (i.val + 1) i.isLt = 0} =
      ⋃ i : Fin n, {p | leadMinor ((toMK p.1)⁻¹ * Matrix.of p.2 * toMK p.1) (i.val + 1) i.isLt = 0} := by
    ext p; simp
  rw [hu]
  exact isClosed_iUnion_of_finite fun i =>
    isClosed_eq (continuous_leadMinor_conj ε (i.val + 1) i.isLt) continuous_const

theorem differentiable_leadMinor_mul (a b : Matrix (Fin n) (Fin n) ℂ) (l : ℕ) (hl : l ≤ n) :
    Differentiable ℂ (fun z : Fin n → Fin n → ℂ => leadMinor (a * Matrix.of z * b) l hl) := by
  unfold leadMinor
  simp only [Matrix.det_apply', Matrix.submatrix_apply, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem IsTau.isURepOn {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : IsTau ε abelian₂ τ w) :
    IsURepOn (Kset ε) τ := by
  obtain ⟨hfd, ⟨h1, hmul⟩, hdiff, hadj, -⟩ := h
  have hsub : ∀ g ∈ Formalism.REAL.Kset ε, g ∈ KC ε := fun g hg =>
    ⟨⟨⟨g, star g, Matrix.mem_unitaryGroup_iff.mp hg.1, Matrix.mem_unitaryGroup_iff'.mp hg.1⟩, rfl⟩, hg.2⟩
  refine ⟨⟨h1, fun a ha b hb => hmul a (hsub a ha) b (hsub b hb)⟩, ?_, ?_⟩
  · intro g hg v
    have hs : star g ∈ Formalism.REAL.Kset ε := Formalism.REAL.Kset_star ε hg
    have hgg : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hg.1
    have hc : (τ (star g)).comp (τ g) = 1 := by
      rw [← hmul _ (hsub _ hs) _ (hsub _ hg), hgg, h1]
    have hv : τ (star g) (τ g v) = v := by
      rw [← ContinuousLinearMap.comp_apply, hc, ContinuousLinearMap.one_apply]
    have hi : ⟪τ g v, τ g v⟫_ℂ = ⟪v, v⟫_ℂ := by
      rw [hadj g (hsub g hg) v (τ g v), ← Matrix.star_eq_conjTranspose, hv]
    have h2 : ‖τ g v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ) v, hi]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  · intro v
    haveI := hfd
    let bs := stdOrthonormalBasis ℂ W
    have hco : ∀ u : W, ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => ⟪u, τ g v⟫_ℂ)
        (Formalism.REAL.Kset ε) :=
      fun u => (hdiff u v).continuousOn.mono (fun g hg => hsub g hg)
    have heq : (fun g => τ g v) = fun g => ∑ i, ⟪bs i, τ g v⟫_ℂ • bs i := by
      funext g; exact (bs.sum_repr' (τ g v)).symm
    rw [heq]
    exact continuousOn_finset_sum _ fun i _ => (hco (bs i)).smul continuousOn_const

theorem psBasic : PsBasic := by
  intro n ε lam W _ _ τ w _hlam htau
  have hrep : IsURepOn (Formalism.REAL.Kset ε) τ := htau.isURepOn
  obtain ⟨hfd, -, -, -, hirr, hw, -⟩ := htau
  haveI := hfd
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hK : ∀ k : KG ε, toMK k ∈ Formalism.REAL.Kset ε := fun k => (mem_KG ε _).1 k.2
  have hinv : ∀ k : KG ε, (toMK k)⁻¹ = star (toMK k) := fun k =>
    Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp (hK k).1)
  have hτc : Continuous (fun k : KG ε => τ (toMK k) w) :=
    (hrep.2.2 w).comp_continuous (toMK_cont ε) hK
  have hPc : Continuous (fun k : KG ε => (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) := by
    have := (ContinuousLinearMap.smulRightL ℂ W W).continuous₂.comp₂ ((innerSL ℂ).continuous.comp hτc) hτc
    exact this
  refine ⟨isOpen_kConjNonzeroMinorsSet ε, fun x hx => posDef_mem_kConjNonzeroMinorsSet ε hx, ?_, ?_⟩
  · have hU := isOpen_kConjNonzeroMinorsSet ε
    have hmem : ∀ k : KG ε, ∀ z ∈ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε}, ∀ i : Fin n,
        leadMinor ((toMK k)⁻¹ * Matrix.of z * toMK k) (i.val + 1) i.isLt ≠ 0 :=
      fun k z hz i => hz (toMK k) (hK k) i
    have hcont : ContinuousOn (Function.uncurry fun (k : KG ε) (z : Fin n → Fin n → ℂ) =>
        Phi lam ((toMK k)⁻¹ * Matrix.of z * toMK k) •
          (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w))
        (Set.univ ×ˢ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε}) := by
      show ContinuousOn (fun q : KG ε × (Fin n → Fin n → ℂ) =>
        Phi lam ((toMK q.1)⁻¹ * Matrix.of q.2 * toMK q.1) •
          (innerSL ℂ (τ (toMK q.1) w)).smulRight (τ (toMK q.1) w)) _
      have hA : ContinuousOn (fun q : KG ε × (Fin n → Fin n → ℂ) =>
          Phi lam ((toMK q.1)⁻¹ * Matrix.of q.2 * toMK q.1))
          (Set.univ ×ˢ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε}) := by
        unfold Phi
        exact continuousOn_finset_prod _ fun i _ =>
          (continuous_leadMinor_conj ε (i.val + 1) i.isLt).continuousOn.zpow₀ _
            fun q hq => Or.inl (hmem q.1 q.2 hq.2 i)
      have hB : ContinuousOn (fun q : KG ε × (Fin n → Fin n → ℂ) =>
          (innerSL ℂ (τ (toMK q.1) w)).smulRight (τ (toMK q.1) w))
          (Set.univ ×ˢ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε}) :=
        (hPc.comp continuous_fst).continuousOn
      exact hA.smul hB
    have hdiff : ∀ k : KG ε, DifferentiableOn ℂ (fun z : Fin n → Fin n → ℂ =>
        Phi lam ((toMK k)⁻¹ * Matrix.of z * toMK k) •
          (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w))
        {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := by
      intro k
      apply DifferentiableOn.smul_const
      unfold Phi
      have hg : ∀ i : Fin n, DifferentiableOn ℂ (fun z : Fin n → Fin n → ℂ =>
          leadMinor ((toMK k)⁻¹ * Matrix.of z * toMK k) (i.val + 1) i.isLt ^ (-(sInt lam i)))
          {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := fun i =>
        ((differentiable_leadMinor_mul _ _ (i.val + 1) i.isLt).differentiableOn).zpow
          (Or.inl fun z hz => hmem k z hz i)
      have hprod : ∀ s : Finset (Fin n), DifferentiableOn ℂ (fun z : Fin n → Fin n → ℂ =>
          ∏ i ∈ s, leadMinor ((toMK k)⁻¹ * Matrix.of z * toMK k) (i.val + 1) i.isLt ^ (-(sInt lam i)))
          {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · simp only [Finset.prod_empty]
          exact differentiableOn_const _
        · intro a s ha ih
          simp only [Finset.prod_insert ha]
          exact (hg a).mul ih
      exact hprod Finset.univ
    have hint := (GlobalTheory.differentiableOn_integral_of_holomorphic_of_continuousOn (μ := muK ε) hU hcont hdiff).1
    unfold ps
    exact DifferentiableOn.congr (hint.const_smul (Module.finrank ℂ W : ℂ)) fun z _ => rfl
  · have hI : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : KG ε → E), Continuous f →
        Integrable f (muK ε) := fun f hf =>
      integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)
    have h1 : ∀ k : KG ε, Phi lam ((toMK k)⁻¹ * 1 * toMK k) = 1 := fun k => by
      rw [hinv, Matrix.mul_one, Matrix.mem_unitaryGroup_iff'.mp (hK k).1, Phi_at_one]
    unfold ps
    simp_rw [h1, one_smul]
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    obtain ⟨c, -, hc⟩ := avgSchur n ε W τ w hfd hrep hirr hw0
    have hnorm : ∀ k : KG ε, ‖τ (toMK k) w‖ = 1 := fun k => by rw [hrep.2.1 _ (hK k), hw]
    let b := stdOrthonormalBasis ℂ W
    have hsum : (Module.finrank ℂ W : ℂ) * c = 1 := by
      have e1 : ∀ i, ∫ k : KG ε, ⟪τ (toMK k) w, b i⟫_ℂ * ⟪b i, τ (toMK k) w⟫_ℂ ∂(muK ε) = c := by
        intro i
        have hbi : ⟪b i, b i⟫_ℂ = 1 := by
          rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; simp
        have := hc (b i) (innerSL ℂ (b i))
        simp only [show ∀ a b : W, (innerSL ℂ a) b = ⟪a, b⟫_ℂ from fun _ _ => rfl, hbi, mul_one] at this
        exact this
      have e2 : ∑ i, ∫ k : KG ε, ⟪τ (toMK k) w, b i⟫_ℂ * ⟪b i, τ (toMK k) w⟫_ℂ ∂(muK ε) = 1 := by
        rw [← integral_finset_sum _ fun i _ => hI (fun k : KG ε => ⟪τ (toMK k) w, b i⟫_ℂ * ⟪b i, τ (toMK k) w⟫_ℂ)
          ((hτc.inner continuous_const).mul (continuous_const.inner hτc))]
        simp_rw [b.sum_inner_mul_inner]
        have hone : ∀ k : KG ε, ⟪τ (toMK k) w, τ (toMK k) w⟫_ℂ = 1 := fun k => by
          rw [inner_self_eq_norm_sq_to_K, hnorm]; simp
        simp_rw [hone]
        simp
      simp_rw [e1] at e2
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using e2
    ext u
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.integral_apply (hI _ hPc),
      ContinuousLinearMap.id_apply]
    simp only [ContinuousLinearMap.smulRight_apply, show ∀ a b : W, (innerSL ℂ a) b = ⟪a, b⟫_ℂ from fun _ _ => rfl]
    apply ext_inner_left ℂ
    intro y
    rw [inner_smul_right, ← integral_inner (hI (fun k : KG ε => ⟪τ (toMK k) w, u⟫_ℂ • τ (toMK k) w)
      ((hτc.inner continuous_const).smul hτc))]
    simp_rw [inner_smul_right]
    have := hc u (innerSL ℂ y)
    simp only [show ∀ a b : W, (innerSL ℂ a) b = ⟪a, b⟫_ℂ from fun _ _ => rfl] at this
    rw [this, ← mul_assoc, hsum, one_mul]

end GlobalTheory.Dec

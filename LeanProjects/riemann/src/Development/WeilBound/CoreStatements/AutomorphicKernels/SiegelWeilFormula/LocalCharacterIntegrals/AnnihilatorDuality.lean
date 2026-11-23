import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.MeasurePreservingOfAddEquiv

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin.DualA

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc Filter Topology
open scoped TensorProduct Matrix

open Classical in

theorem setIntegral_char_subgroup {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (ν : Measure G) [ν.IsAddRightInvariant] (Λ : AddSubgroup G) (hΛ : MeasurableSet (Λ : Set G))
    (χ : G → ℂ) (hχ : ∀ x y, χ (x + y) = χ x * χ y) :
    ∫ x in (Λ : Set G), χ x ∂ν = if ∀ x ∈ Λ, χ x = 1 then ((ν.real Λ : ℝ) : ℂ) else 0 := by
  split_ifs with h
  · rw [setIntegral_congr_fun hΛ (fun x hx => h x hx), setIntegral_const]
    simp
  · push Not at h
    obtain ⟨x0, hx0, hne⟩ := h
    have h3 : ∀ x, (Λ : Set G).indicator χ (x + x0) = χ x0 * (Λ : Set G).indicator χ x := by
      intro x
      simp only [Set.indicator]
      by_cases hx : x ∈ Λ
      · have : x + x0 ∈ Λ := Λ.add_mem hx hx0
        simp only [SetLike.mem_coe, hx, this, if_true, hχ, mul_comm]
      · have : x + x0 ∉ Λ := fun h' => hx (by simpa using Λ.sub_mem h' hx0)
        simp only [SetLike.mem_coe, hx, this, if_false, mul_zero]
    have key : ∫ x in (Λ : Set G), χ x ∂ν = χ x0 * ∫ x in (Λ : Set G), χ x ∂ν := by
      calc ∫ x in (Λ : Set G), χ x ∂ν = ∫ x, (Λ : Set G).indicator χ x ∂ν := (integral_indicator hΛ).symm
        _ = ∫ x, (Λ : Set G).indicator χ (x + x0) ∂ν := (integral_add_right_eq_self _ x0).symm
        _ = ∫ x, χ x0 * (Λ : Set G).indicator χ x ∂ν := by simp_rw [h3]
        _ = χ x0 * ∫ x, (Λ : Set G).indicator χ x ∂ν := integral_const_mul _ _
        _ = χ x0 * ∫ x in (Λ : Set G), χ x ∂ν := by rw [integral_indicator hΛ]
    have : (1 - χ x0) * ∫ x in (Λ : Set G), χ x ∂ν = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd (sub_eq_zero.1 h1).symm hne
    · exact h1

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance secondCountable_mat (v : HeightOneSpectrum (𝓞 F)) (p q : ℕ) :
    SecondCountableTopology (Matrix (Fin p) (Fin q) (Fv F v ⊗[F] E)) :=
  inferInstanceAs (SecondCountableTopology (Fin p → Fin q → Fv F v ⊗[F] E))

instance secondCountable_herm (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (n : ℕ) :
    SecondCountableTopology (HermR (Fv F v) σ n) :=
  TopologicalSpace.Subtype.secondCountableTopology (HermR (Fv F v) σ n : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)))

section Pair

variable (R : Type) [CommRing R] [Algebra F R] {n : ℕ}

theorem trPair_comm (S T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : trPair R S T = trPair R T S := by
  unfold trPair
  congr 2
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem trPair_add_right (S T T' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    trPair R S (T + T') = trPair R S T + trPair R S T' := by
  unfold trPair
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]

theorem trPair_neg_right (S T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : trPair R S (-T) = -trPair R S T := by
  unfold trPair
  simp only [Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, map_neg]

theorem trPair_sub_right (S T T' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    trPair R S (T - T') = trPair R S T - trPair R S T' := by
  rw [sub_eq_add_neg, trPair_add_right, trPair_neg_right, ← sub_eq_add_neg]

theorem trPair_add_left (S S' T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    trPair R (S + S') T = trPair R S T + trPair R S' T := by
  rw [trPair_comm, trPair_add_right, trPair_comm R T, trPair_comm R T]

theorem trPair_zero_right (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : trPair R S 0 = 0 := by
  unfold trPair; simp

end Pair

theorem sigma_invol' (σ : E →ₐ[F] E) (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (x : E) :
    σ (σ x) = x := by
  let τ := (Classical.arbitrary (InfinitePlace E)).embedding
  apply τ.injective
  rw [hσ, hσ, star_star]

theorem sigR_invol' (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x)
    (x : R ⊗[F] E) : sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem gramR_mem' (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (X : Fin n → Fin M → R ⊗[F] E) : gramR R σ J X ∈ HermR R σ n := by
  intro a b
  have hJR : ∀ i j, sigR R σ (JR R J i j) = JR R J j i := by
    intro i j; simp [JR, inclR, sigR, hJ]
  simp only [gramR, hR, hform, map_sum, map_mul, sigR_invol' R σ hσ, hJR]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {v : HeightOneSpectrum (𝓞 F)}

theorem exists_entry_ge {p q : ℕ} {x : Fin p → Fin q → Fv F v ⊗[F] E} (h : 0 < nM v x) :
    ∃ i j, nM v x ≤ nA v (x i j) := by
  by_contra hne
  push Not at hne
  have h' : ‖(fun i j => crd v (x i j))‖ < nM v x := by
    rw [pi_norm_lt_iff h]
    intro i
    rw [pi_norm_lt_iff h]
    intro j
    exact hne i j
  exact lt_irrefl _ h'

section Inv

theorem sigR_algebraMap (σ : E →ₐ[F] E) (t : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) t) = algebraMap (Fv F v) (Fv F v ⊗[F] E) t := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp [sigR]

theorem sigR_smul (σ : E →ₐ[F] E) (t : Fv F v) (x : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (t • x) = t • sigR (Fv F v) σ x := by
  rw [Algebra.smul_def, map_mul, sigR_algebraMap, ← Algebra.smul_def]

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR (Fv F v) σ) := by
  let f : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) :=
    { toFun := sigR (Fv F v) σ, map_add' := map_add _, map_smul' := fun t x => sigR_smul σ t x }
  exact IsModuleTopology.continuous_of_linearMap f

theorem isClosed_HermR' (σ : E →ₐ[F] E) (n : ℕ) :
    IsClosed (HermR (Fv F v) σ n : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) := by
  have : (HermR (Fv F v) σ n : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) =
      ⋂ a, ⋂ b, {S | sigR (Fv F v) σ (S b a) = S a b} := by
    ext S; simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]; exact Iff.rfl
  rw [this]
  exact isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_eq ((continuous_sigR σ).comp ((continuous_apply a).comp (continuous_apply b)))
      ((continuous_apply b).comp (continuous_apply a))

theorem trace_sigR (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (x : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (sigR (Fv F v) σ x) = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) x := by
  let f : (Fv F v ⊗[F] E) →ₐ[Fv F v] (Fv F v ⊗[F] E) := Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ
  have hf : ∀ y, f y = sigR (Fv F v) σ y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => rfl
    | add y z hy hz => rw [map_add, map_add, hy, hz]
  have hinv : Function.Involutive f := fun y => by
    rw [hf, hf]; exact sigR_invol' (Fv F v) σ hσ y
  have h := Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective f hinv.bijective) x
  rwa [AlgEquiv.ofBijective_apply, hf] at h

theorem trPair_smul_left {n : ℕ} (t : Fv F v) (S T : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    trPair (Fv F v) (t • S) T = t * trPair (Fv F v) S T := by
  unfold trPair
  simp only [Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul]
  ring

theorem half_mul_two : algebraMap F (Fv F v) (1 / 2) * 2 = 1 := by
  rw [show (2 : Fv F v) = algebraMap F (Fv F v) 2 from (map_ofNat _ 2).symm, ← map_mul]
  norm_num

theorem trPair_herm {n : ℕ} (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (X D : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hD : D ∈ HermR (Fv F v) σ n) :
    trPair (Fv F v) (X + (X.map (sigR (Fv F v) σ))ᵀ) D =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (∑ a, ∑ c, X a c * D c a) := by
  have hD' : ∀ a b, sigR (Fv F v) σ (D b a) = D a b := hD
  have h2 : ∑ a, ∑ c, sigR (Fv F v) σ (X c a) * D c a =
      ∑ a, ∑ c, sigR (Fv F v) σ (X a c) * sigR (Fv F v) σ (D c a) := by
    rw [Finset.sum_comm]; simp_rw [hD']
  have h1 : ∑ a, ∑ c, (X + (X.map (sigR (Fv F v) σ))ᵀ) a c * D c a =
      (∑ a, ∑ c, X a c * D c a) + sigR (Fv F v) σ (∑ a, ∑ c, X a c * D c a) := by
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, add_mul, Finset.sum_add_distrib, map_sum,
      map_mul]
    rw [h2]
  unfold trPair
  rw [h1, map_add, trace_sigR σ hσ, ← two_mul, ← mul_assoc, half_mul_two, one_mul]

end Inv

variable (v)

def ballH (σ : E →ₐ[F] E) (n : ℕ) (R : ℝ) (hR : 0 ≤ R) : AddSubgroup (HermR (Fv F v) σ n) where
  carrier := {b | nM v b.1 ≤ R}
  zero_mem' := by
    show nM v (0 : Fin n → Fin n → Fv F v ⊗[F] E) ≤ R
    rw [nM_zero]; exact hR
  add_mem' := fun {a b} ha hb => (nM_add_le a.1 b.1).trans (max_le ha hb)
  neg_mem' := fun {a} ha => (le_of_eq (nM_neg (v := v) (a.1 : Fin n → Fin n → Fv F v ⊗[F] E))).trans ha

theorem coe_ballH (σ : E →ₐ[F] E) (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (ballH v σ n R hR : Set (HermR (Fv F v) σ n)) = Subtype.val ⁻¹' {x | nM v x ≤ R} := rfl

theorem isCompact_ballH (σ : E →ₐ[F] E) (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    IsCompact (ballH v σ n R hR : Set (HermR (Fv F v) σ n)) := by
  rw [coe_ballH]
  exact (isClosed_HermR' σ n).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_ballM R)

theorem isOpen_ballH (σ : E →ₐ[F] E) (n : ℕ) (R : ℝ) (hR : 0 < R) :
    IsOpen (ballH v σ n R hR.le : Set (HermR (Fv F v) σ n)) := by
  rw [coe_ballH]
  exact IsOpen.preimage (X := HermR (Fv F v) σ n) continuous_subtype_val (isOpen_ballM (v := v) (p := n) (q := n) hR)

theorem perp_bound (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (n : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ R : ℝ, 0 < R → ∀ D : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), D ∈ HermR (Fv F v) σ n →
      (∀ b : HermR (Fv F v) σ n, nM v b.1 ≤ R → psiV F ψ v (trPair (Fv F v) b.1 D) = 1) → nM v D ≤ C₀ / R := by
  obtain ⟨y0, hy0⟩ := exists_psiV_ne_one (v := v) hcm hψ
  obtain ⟨c, hc, htr⟩ := exists_trace_ge (E := E) v
  obtain ⟨Cσ, hCσ0, hCσ⟩ := exists_nA_sig v σ
  have hσ : ∀ x, σ (σ x) = x := sigma_invol' σ hcm.2.2.2
  have hy0n : 0 < ‖y0‖ := by
    rw [norm_pos_iff]; rintro rfl; exact hy0 (psiV_zero ψ)
  set C1 : ℝ := max 1 Cσ with hC1
  have hC1pos : 0 < C1 := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨‖y0‖ * C1 / c, by positivity, ?_⟩
  intro R hR D hD hperp
  by_contra hlt
  push Not at hlt
  have hpos : 0 < nM v D := lt_of_le_of_lt (by positivity) hlt
  have key : ‖y0‖ * C1 < c * nM v D * R := by
    rw [div_lt_iff₀ hR, div_lt_iff₀ hc] at hlt; linarith
  obtain ⟨i, j, hij⟩ := exists_entry_ge hpos
  obtain ⟨a', ha'1, ha'2⟩ := htr (D i j)
  set w := Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a' * D i j) with hw
  have hwpos : c * nM v D ≤ ‖w‖ := le_trans (mul_le_mul_of_nonneg_left hij hc.le) ha'2
  have hcD : 0 < c * nM v D := mul_pos hc hpos
  have hw0 : w ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hwpos; linarith
  let X : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := Matrix.of fun a b => if a = j ∧ b = i then a' else 0
  let M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := X + (X.map (sigR (Fv F v) σ))ᵀ
  let t : Fv F v := y0 / w
  have hX : ∀ a b, nA v (X a b) ≤ 1 := by
    intro a b
    simp only [X, Matrix.of_apply]
    split_ifs
    · exact ha'1
    · rw [nA_zero]; exact zero_le_one
  have hMle : nM v M ≤ C1 := by
    refine (nM_le_iff (v := v) (x := (M : Fin n → Fin n → Fv F v ⊗[F] E)) hC1pos.le).2 ?_
    intro a b
    simp only [M, Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply]
    refine (nA_add_le _ _).trans (max_le ((hX a b).trans (le_max_left _ _)) ?_)
    calc nA v (sigR (Fv F v) σ (X b a)) ≤ Cσ * nA v (X b a) := hCσ _
      _ ≤ Cσ * 1 := mul_le_mul_of_nonneg_left (hX b a) hCσ0
      _ = Cσ := mul_one _
      _ ≤ C1 := le_max_right _ _
  have hM : t • M ∈ HermR (Fv F v) σ n := by
    intro a b
    simp only [M, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, sigR_smul, map_add,
      sigR_invol' (Fv F v) σ hσ]
    rw [add_comm]
  have hnM : nM v (t • M) ≤ R := by
    have e1 : nM v (t • M) = ‖t‖ * nM v M := nM_smul t M
    rw [e1, norm_div]
    calc ‖y0‖ / ‖w‖ * nM v M ≤ ‖y0‖ / ‖w‖ * C1 := by gcongr
      _ ≤ ‖y0‖ / (c * nM v D) * C1 := by gcongr
      _ ≤ R := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hcD]; linarith
  have hsum : ∑ a, ∑ c, X a c * D c a = a' * D i j := by
    simp [X, Matrix.of_apply, ite_and]
  have hval : trPair (Fv F v) (t • M) D = y0 := by
    rw [trPair_smul_left, trPair_herm σ hσ X D hD, hsum, ← hw]
    exact div_mul_cancel₀ y0 hw0
  have h := hperp ⟨t • M, hM⟩ hnM
  rw [hval] at h
  exact hy0 h

section Units

variable {v}

theorem continuous_algNorm : Continuous (fun x : Fv F v ⊗[F] E => Algebra.norm (Fv F v) x) := by
  classical
  let b := bA E v
  have h : (fun x : Fv F v ⊗[F] E => Algebra.norm (Fv F v) x) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h]
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun x : Fv F v ⊗[F] E => Algebra.leftMulMatrix b x i j) =
      fun x => (b.coord i) ((LinearMap.mulRight (Fv F v) (b j)) x) := by
    funext x; rw [Algebra.leftMulMatrix_eq_repr_mul]; rfl
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap ((b.coord i).comp (LinearMap.mulRight (Fv F v) (b j)))

theorem isUnit_iff_algNorm (x : Fv F v ⊗[F] E) : IsUnit x ↔ IsUnit (Algebra.norm (Fv F v) x) := by
  constructor
  · intro h; exact h.map (Algebra.norm (Fv F v))
  · intro h
    have h1 : IsUnit (Algebra.lmul (Fv F v) (Fv F v ⊗[F] E) x) := by
      rw [LinearMap.isUnit_iff_isUnit_det]; exact h
    obtain ⟨u, hu⟩ := h1
    have key := LinearMap.congr_fun u.mul_inv 1
    rw [hu] at key
    exact IsUnit.of_mul_eq_one _ (by simpa using key)

theorem isOpen_unitHerm' (σ : E →ₐ[F] E) (n : ℕ) :
    IsOpen {S : HermR (Fv F v) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} := by
  have hU : IsOpen {x : Fv F v ⊗[F] E | IsUnit x} := by
    have : {x : Fv F v ⊗[F] E | IsUnit x} = (fun x => Algebra.norm (Fv F v) x) ⁻¹' {r | r ≠ 0} := by
      ext x; simp [isUnit_iff_algNorm]
    rw [this]; exact isOpen_ne.preimage continuous_algNorm
  exact (hU.preimage continuous_id.matrix_det).preimage continuous_subtype_val

theorem exists_ballH_sub {σ : E →ₐ[F] E} {n : ℕ} {T : HermR (Fv F v) σ n} {U : Set (HermR (Fv F v) σ n)}
    (hU : U ∈ 𝓝 T) : ∃ r > 0, ∀ S : HermR (Fv F v) σ n, nM v (S.1 - T.1) ≤ r → S ∈ U := by
  rw [mem_nhds_subtype] at hU
  obtain ⟨W, hW, hWU⟩ := hU
  have h0 : {x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | T.1 + x ∈ W} ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) _) := by
    have hc : Continuous fun x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) => T.1 + x := continuous_const.add continuous_id
    have := hc.continuousAt (x := 0) (by simpa using hW)
    exact this
  obtain ⟨r, hr, hsub⟩ := exists_ballM_subset (v := v) (p := n) (q := n) h0
  refine ⟨r, hr, fun S hS => hWU ?_⟩
  have h1 : T.1 + (S.1 - T.1) ∈ W := hsub (show nM v (S.1 - T.1 : Fin n → Fin n → Fv F v ⊗[F] E) ≤ r from hS)
  rwa [add_sub_cancel] at h1

end Units

section Cont

variable {v}

theorem continuous_trace : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) :=
  IsModuleTopology.continuous_of_linearMap (Algebra.trace (Fv F v) (Fv F v ⊗[F] E))

theorem continuous_trPair {n : ℕ} {α : Type*} [TopologicalSpace α] {f g : α → Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => trPair (Fv F v) (f a) (g a) := by
  unfold trPair
  refine continuous_const.mul (continuous_trace.comp ?_)
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply j).comp ((continuous_apply i).comp hf)).mul
    ((continuous_apply i).comp ((continuous_apply j).comp hg))

theorem continuous_gramR' (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous (fun X : Fin n → Fin M → Fv F v ⊗[F] E => gramR (Fv F v) σ J X) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [gramR, hR, hform]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((continuous_sigR σ).comp ((continuous_apply i).comp (continuous_apply a))).mul
    continuous_const).mul ((continuous_apply j).comp (continuous_apply b))

end Cont

end PositivityTheory.SiegelWeilFormula.SwLocFin.DualA

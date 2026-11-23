import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private theorem core {K V : Type} [NormedField K] [IsUltrametricDist K] [SMul K V] {N g : ℕ}
    (P Q : V → Fin N → K) (L : V → Fin g → K) (Λ : V → Prop) (π δ : K) (ε : ℝ)
    (hπ0 : π ≠ 0) (hπ : ‖π‖ < 1) (hε0 : 0 ≤ ε) (hε : ε ≤ ‖π‖ ^ 2 * ‖δ‖)
    (hP : ∀ (c : K) v k, P (c • v) k = c * P v k) (hL : ∀ (c : K) v k, L (c • v) k = c * L v k)
    (hPQ : ∀ v k, ‖P v k - Q v k‖ ≤ ε * ‖L v‖) (hΛ : ∀ v, Λ v ↔ ∀ k, ‖Q v k‖ ≤ ‖δ‖)
    (hb : ∀ v, Λ v → ∀ j, ‖π * L v j‖ ≤ 1) (v : V) : Λ v ↔ ∀ k, ‖P v k‖ ≤ ‖δ‖ := by
  have hπp : 0 < ‖π‖ := norm_pos_iff.2 hπ0
  have key : ∀ v, ‖π‖ ^ 2 * ‖L v‖ ≤ 1 → (Λ v ↔ ∀ k, ‖P v k‖ ≤ ‖δ‖) := by
    intro v hv
    have h1 : ∀ k, ‖P v k - Q v k‖ ≤ ‖δ‖ := fun k => by
      refine (hPQ v k).trans ?_
      calc ε * ‖L v‖ ≤ ‖π‖ ^ 2 * ‖δ‖ * ‖L v‖ := by gcongr
        _ = (‖π‖ ^ 2 * ‖L v‖) * ‖δ‖ := by ring
        _ ≤ 1 * ‖δ‖ := by gcongr
        _ = _ := one_mul _
    rw [hΛ]
    refine forall_congr' fun k => ⟨fun h => ?_, fun h => ?_⟩
    · have : P v k = (P v k - Q v k) + Q v k := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1 k) h)
    · have : Q v k = -(P v k - Q v k) + P v k := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by rw [norm_neg]; exact h1 k) h)
  have hb' : ∀ v, Λ v → ‖π‖ * ‖L v‖ ≤ 1 := by
    intro v hv
    rw [← le_div_iff₀' hπp, pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    rw [le_div_iff₀' hπp, ← norm_mul]
    exact hb v hv j
  by_cases hv : ‖π‖ ^ 2 * ‖L v‖ ≤ 1
  · exact key v hv
  have hv' := not_le.1 hv
  constructor
  · intro h
    have := hb' v h
    exfalso
    have h2 : ‖π‖ ^ 2 * ‖L v‖ = ‖π‖ * (‖π‖ * ‖L v‖) := by ring
    have h3 : ‖π‖ * (‖π‖ * ‖L v‖) ≤ ‖π‖ * 1 := by gcongr
    linarith
  · intro h
    exfalso
    have hne : Nonempty (Fin g) := by
      by_contra hh
      haveI := not_nonempty_iff.1 hh
      rw [Subsingleton.elim (L v) 0] at hv'
      simp at hv'
      linarith
    obtain ⟨j, hj⟩ := Finite.exists_max (fun j => ‖L v j‖)
    have hj' : ‖L v‖ = ‖L v j‖ :=
      le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hj) (norm_le_pi_norm _ _)
    have hc : ‖(π ^ 2 * L v j)⁻¹‖ = (‖π‖ ^ 2 * ‖L v‖)⁻¹ := by
      rw [norm_inv, norm_mul, norm_pow, hj']
    have hc1 : ‖(π ^ 2 * L v j)⁻¹‖ ≤ 1 := by
      rw [hc]; exact inv_le_one_of_one_le₀ hv'.le
    have hn : ‖π‖ ^ 2 * ‖L ((π ^ 2 * L v j)⁻¹ • v)‖ = 1 := by
      have : L ((π ^ 2 * L v j)⁻¹ • v) = (π ^ 2 * L v j)⁻¹ • L v := funext fun k => hL _ _ _
      rw [this, norm_smul, hc, mul_left_comm]
      exact inv_mul_cancel₀ (by linarith)
    have hm := (key _ hn.le).2 (fun k => by
      rw [hP, norm_mul]
      calc _ ≤ 1 * ‖δ‖ := by gcongr; exact h k
        _ = _ := one_mul _)
    have := hb' _ hm
    have h2 : ‖π‖ ^ 2 * ‖L ((π ^ 2 * L v j)⁻¹ • v)‖ = ‖π‖ * (‖π‖ * ‖L ((π ^ 2 * L v j)⁻¹ • v)‖) := by ring
    have h3 : ‖π‖ * (‖π‖ * ‖L ((π ^ 2 * L v j)⁻¹ • v)‖) ≤ ‖π‖ * 1 := by gcongr
    linarith

private theorem pr_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {K : Type} [CommRing K] (c : K) (y : K ⊗[ℤ] Dw.La) (a : Dw.La) :
    pr Dw (c • y) a = c * pr Dw y a := by
  simp [pr]

private theorem pr_sum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {K : Type} [CommRing K] {g : ℕ} (b : (Fin g → K) →ₗ[K] K ⊗[ℤ] Dw.La) (v : Fin g → K) (a : Dw.La) :
    pr Dw (b v) a = ∑ j, pr Dw (b (Pi.single j 1)) a * v j := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [pr, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem eig_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {K : Type} [CommRing K] (σ : 𝓞 E →+* K) (c : K) (y : K ⊗[ℤ] Dw.La) (hy : IsEigL Dw σ y) :
    IsEigL Dw σ (c • y) := fun o => by
  rw [map_smul, hy o, smul_comm]

theorem UpperTheory.cut_lattice_norm_bound :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (n g : ℕ) (h : Dw.La → Fin g → ℂ_[p]) (b : (Fin g → ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p] ⊗[ℤ] Dw.La) (Λ : Set (Fin g → ℂ_[p])), PtData Dw p n h b Λ → ∀ (σ : 𝓞 E →+* ℂ_[p]) (M N r : ℕ) (a : Fin M → Dw.La) (T : Fin N → Fin M → ℂ_[p]) (δ : ℂ_[p]) (A : Fin r → Fin g → ℂ_[p]), CutL Dw σ a T δ → δ ≠ 0 → ‖δ‖ ≤ 1 → (p : ℝ) ^ 2 ≤ (p : ℝ) ^ n * ‖δ‖ → LinearIndependent ℂ_[p] A → (∀ i, IsEigL Dw σ (b (A i))) → (∀ cf, covMat T (fun m => h (a m)) A *ᵥ cf = 0 → cf = 0) ∧ (∀ cf : Fin r → ℂ_[p], ∑ i, cf i • A i ∈ Λ ↔ ∀ k, ‖(covMat T (fun m => h (a m)) A *ᵥ cf) k‖ ≤ ‖δ‖) ∧ ∀ cf : Fin r → ℂ_[p], (∀ k, ‖(covMat T (fun m => h (a m)) A *ᵥ cf) k‖ ≤ 1) → (∀ k, ‖δ * p * (∑ i, cf i • A i) k‖ ≤ 1) ∧ (∀ o, ‖δ * pr Dw (b (∑ i, cf i • A i)) o‖ ≤ 1) ∧ ∀ k, ‖(covMat T (fun m => h (a m)) A *ᵥ cf) k - ∑ m, T k m * pr Dw (b (∑ i, cf i • A i)) (a m)‖ < 1 := by
  intro E _ _ _ H Dw p _ n g h b Λ ⟨h1, h2, h3, _⟩ σ M N r a T δ A ⟨hT, hC⟩ hδ0 hδ1 hn hA hE
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    have := PadicComplex.norm_extends' (p := p) (p : ℚ_[p])
    simpa using this
  have hpz : (p : ℂ_[p]) ≠ 0 := by
    rw [← norm_pos_iff, hpn]; positivity
  have hpl : ‖(p : ℂ_[p])‖ < 1 := by rw [hpn]; exact inv_lt_one_of_one_lt₀ hp1
  have hδp : 0 < ‖δ‖ := norm_pos_iff.2 hδ0
  have hε : (p : ℝ)⁻¹ ^ n ≤ ‖(p : ℂ_[p])‖ ^ 2 * ‖δ‖ := by
    rw [hpn, inv_pow, inv_pow, inv_mul_eq_div, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
    exact hn
  have hL : ∀ (c : ℂ_[p]) (cf : Fin r → ℂ_[p]), ∑ i, (c • cf) i • A i = c • ∑ i, cf i • A i := by
    intro c cf
    simp [Finset.smul_sum, mul_smul]
  have hEv : ∀ cf : Fin r → ℂ_[p], IsEigL Dw σ (b (∑ i, cf i • A i)) := by
    intro cf o
    simp only [map_sum, map_smul, hE _ o, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  have hPv : ∀ (cf : Fin r → ℂ_[p]) k, (covMat T (fun m => h (a m)) A *ᵥ cf) k =
      ∑ m, T k m * ∑ j, h (a m) j * (∑ i, cf i • A i) j := by
    intro cf k
    simp only [covMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hPQ : ∀ (cf : Fin r → ℂ_[p]) k, ‖(covMat T (fun m => h (a m)) A *ᵥ cf) k -
      ∑ m, T k m * pr Dw (b (∑ i, cf i • A i)) (a m)‖ ≤ (p : ℝ)⁻¹ ^ n * ‖∑ i, cf i • A i‖ := by
    intro cf k
    rw [hPv, ← Finset.sum_sub_distrib]
    generalize ∑ i, cf i • A i = v
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun m _ => ?_
    rw [← mul_sub, norm_mul, pr_sum, ← Finset.sum_sub_distrib]
    refine (mul_le_of_le_one_left (norm_nonneg _) (hT k m)).trans ?_
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j _ => ?_
    rw [← sub_mul, norm_mul]
    exact mul_le_mul (h1 _ _) (norm_le_pi_norm _ _) (norm_nonneg _) (by positivity)
  have hΛ : ∀ cf : Fin r → ℂ_[p], ∑ i, cf i • A i ∈ Λ ↔
      ∀ k, ‖∑ m, T k m * pr Dw (b (∑ i, cf i • A i)) (a m)‖ ≤ ‖δ‖ := by
    intro cf
    have := hC _ (eig_smul Dw σ δ⁻¹ _ (hEv cf))
    simp only [pr_smul, mul_inv_cancel_left₀ hδ0] at this
    rw [h2, ← this]
    refine forall_congr' fun k => ?_
    simp only [mul_left_comm _ δ⁻¹, ← Finset.mul_sum, norm_mul, norm_inv]
    rw [inv_mul_le_iff₀ hδp, _root_.mul_one]
  have H2 := core (fun cf : Fin r → ℂ_[p] => covMat T (fun m => h (a m)) A *ᵥ cf)
    (fun cf k => ∑ m, T k m * pr Dw (b (∑ i, cf i • A i)) (a m)) (fun cf => ∑ i, cf i • A i)
    (fun cf => ∑ i, cf i • A i ∈ Λ) p δ _ hpz hpl (by positivity) hε
    (fun c v k => by simp [Matrix.mulVec_smul]) (fun c v k => congrFun (hL c v) k)
    hPQ hΛ (fun v hv => h3 _ hv)
  refine ⟨fun cf hcf => ?_, H2, fun cf hcf => ?_⟩
  · have hv : ∑ i, cf i • A i = 0 := by
      funext j
      by_contra hj
      have hm := (H2 (((p : ℂ_[p]) ^ 2 * (∑ i, cf i • A i) j)⁻¹ • cf)).2 (fun k => by
        simp [Matrix.mulVec_smul, hcf])
      have := h3 _ hm j
      rw [hL, Pi.smul_apply, smul_eq_mul] at this
      have hj' : (∑ i, cf i • A i) j ≠ 0 := hj
      have e : (p : ℂ_[p]) * ((((p : ℂ_[p]) ^ 2 * (∑ i, cf i • A i) j)⁻¹ * (∑ i, cf i • A i) j)) = (p : ℂ_[p])⁻¹ := by
        field_simp
      rw [e, norm_inv, hpn, inv_inv] at this
      linarith
    funext i
    exact Fintype.linearIndependent_iff.1 hA cf hv i
  · have hm := (H2 (δ • cf)).2 (fun k => by
      simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hcf k))
    simp only [hL] at hm
    have hb : ∀ k, ‖δ * p * (∑ i, cf i • A i) k‖ ≤ 1 := fun k => by
      have := h3 _ hm k
      rwa [Pi.smul_apply, smul_eq_mul, ← _root_.mul_assoc, mul_comm _ δ] at this
    refine ⟨hb, fun o => ?_, fun k => ?_⟩
    · have := (h2 _).1 hm o
      rwa [map_smul, pr_smul] at this
    · refine (hPQ cf k).trans_lt ?_
      have hpp : 0 < ‖δ * p‖ := norm_pos_iff.2 (mul_ne_zero hδ0 hpz)
      have hb' : ‖δ * p‖ * ‖∑ i, cf i • A i‖ ≤ 1 := by
        rw [← le_div_iff₀' hpp, pi_norm_le_iff_of_nonneg (by positivity)]
        intro j
        rw [le_div_iff₀' hpp, ← norm_mul]
        exact hb j
      calc _ ≤ ‖(p : ℂ_[p])‖ ^ 2 * ‖δ‖ * ‖∑ i, cf i • A i‖ := by gcongr
        _ = ‖(p : ℂ_[p])‖ * (‖δ * p‖ * ‖∑ i, cf i • A i‖) := by rw [norm_mul]; ring
        _ ≤ ‖(p : ℂ_[p])‖ * 1 := by gcongr
        _ < 1 := by rwa [_root_.mul_one]

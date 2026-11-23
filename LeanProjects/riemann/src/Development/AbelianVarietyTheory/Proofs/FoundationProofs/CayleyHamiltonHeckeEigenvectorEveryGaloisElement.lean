import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommGaloisActionModularTowerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KmapSubMemOfASet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraFrobeniusQuadraticModPrimePowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerBettiModuleFreeFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixingMulFrobAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRelationOfFrobApprox
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalMulApply
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.CayleyHamiltonSmallCoefficients

theorem exists_pow_norm_lt (l : ℕ) [Fact l.Prime] {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, ∀ a ∈ (idl l) ^ k, ‖a‖ < δ := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ (PadicInt.norm_lt_one_iff_dvd (l : ℤ_[l]) |>.2 dvd_rfl)
  refine ⟨k, fun a ha => ?_⟩
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
  obtain ⟨c, rfl⟩ := ha
  rw [norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one c)) hk

theorem small_coeffs (l : ℕ) [Fact l.Prime] {M U n : Type} [AddCommGroup M] [Module ℤ_[l] M] [Fintype n]
    (b : n → U → AdicCompletion (idl l) M) (hb : LinearIndependent ℤ_[l] b) (k : ℕ) :
    ∃ m : ℕ, ∀ a : n → ℤ_[l], (∀ u, (∑ j, a j • b j) u ∈
      (idl l) ^ m • (⊤ : Submodule ℤ_[l] (AdicCompletion (idl l) M))) → ∀ j, a j ∈ (idl l) ^ k := by
  classical
  by_contra hcon
  simp only [not_exists, not_forall] at hcon
  choose a ha j0 hj0 using hcon
  obtain ⟨c, -, φ, hφ, hlim⟩ := (isCompact_univ (X := n → ℤ_[l])).tendsto_subseq (x := a) (fun _ => Set.mem_univ _)
  have hev : ∀ p : ℕ, ∃ i, p ≤ i ∧ ∀ j, a (φ i) j - c j ∈ (idl l) ^ p := by
    intro p
    have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    obtain ⟨i0, hi0⟩ := Metric.tendsto_atTop.1 hlim ((l : ℝ) ^ (-(p : ℤ))) (zpow_pos hl0 _)
    refine ⟨max p i0, le_max_left _ _, fun j => ?_⟩
    rw [Ideal.span_singleton_pow, ← PadicInt.norm_le_pow_iff_mem_span_pow, ← dist_eq_norm]
    exact (dist_le_pi_dist _ _ j).trans (hi0 _ (le_max_right _ _)).le
  have hc0 : ∑ j, c j • b j = 0 := by
    funext u
    refine IsHausdorff.haus (inferInstance : IsHausdorff (idl l) (AdicCompletion (idl l) M)) _ fun p => ?_
    rw [SModEq.zero]
    obtain ⟨i, hi, h⟩ := hev p
    have e : (∑ j, c j • b j) u = (∑ j, a (φ i) j • b j) u - ∑ j, (a (φ i) j - c j) • b j u := by
      simp only [Finset.sum_apply, Pi.smul_apply, sub_smul, Finset.sum_sub_distrib]
      abel
    rw [e]
    refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (h j) Submodule.mem_top)
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (hi.trans (hφ.id_le i))) (ha (φ i) u)
  have hc := Fintype.linearIndependent_iff.1 hb c hc0
  obtain ⟨i, -, h⟩ := hev k
  exact hj0 (φ i) (by simpa [hc] using h (j0 (φ i)))

theorem matrix_relation {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Type} [NormedField E] (l : ℕ) [Fact l.Prime]
    [Algebra ℤ_[l] E] (hE : ∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) {r : ℕ}
    (A : (Ω ≃ₐ[ℚ] Ω) → Matrix (Fin r) (Fin r) ℤ_[l]) (t d : (Ω ≃ₐ[ℚ] Ω) → E) (z : Fin r → E)
    (hA : ∀ s s', A (s * s') = A s * A s')
    (hAc : ∀ k : ℕ, ∃ E0 : Finset Ω, ∀ s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ∀ i j, (A s' - 1) i j ∈ (idl l) ^ k)
    (ht : ∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖t (s * s') - t s‖ < δ)
    (hd : ∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖d (s * s') - d s‖ < δ)
    (hF : ∀ k : ℕ, ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ σ : Ω ≃ₐ[ℚ] Ω, FrobAt q σ →
      ∃ R : Matrix (Fin r) (Fin r) ℤ_[l], (∀ i j, R i j ∈ (idl l) ^ k) ∧
        ((A σ).map (algebraMap ℤ_[l] E) * (A σ).map (algebraMap ℤ_[l] E) - t σ • (A σ).map (algebraMap ℤ_[l] E)
          + d σ • (1 : Matrix (Fin r) (Fin r) E)) *ᵥ z = R.map (algebraMap ℤ_[l] E) *ᵥ z)
    (hC : ∀ (s : Ω ≃ₐ[ℚ] Ω) (E0 : Finset Ω) (S : Finset ℕ),
      ∃ (s' : Ω ≃ₐ[ℚ] Ω) (q : ℕ), (∀ x ∈ E0, s' x = x) ∧ q.Prime ∧ q ∉ S ∧ FrobAt q (s * s'))
    (s : Ω ≃ₐ[ℚ] Ω) :
    ((A s).map (algebraMap ℤ_[l] E) * (A s).map (algebraMap ℤ_[l] E) - t s • (A s).map (algebraMap ℤ_[l] E)
      + d s • (1 : Matrix (Fin r) (Fin r) E)) *ᵥ z = 0 := by
  classical
  have hexp : ∀ (M : Matrix (Fin r) (Fin r) E) (a b : E), (M * M - a • M + b • (1 : Matrix (Fin r) (Fin r) E)) *ᵥ z =
      M *ᵥ (M *ᵥ z) - a • (M *ᵥ z) + b • z := by
    intro M a b
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_mulVec]
  rw [hexp]
  refine GlobalTheory.galois_relation_of_frob_approx r (fun s => (A s).map (algebraMap ℤ_[l] E)) t d z ?_ ?_ hC s
  · intro s δ hδ
    obtain ⟨k, hk⟩ := exists_pow_norm_lt l hδ
    obtain ⟨E1, h1⟩ := hAc k
    obtain ⟨E2, h2⟩ := ht δ hδ
    obtain ⟨E3, h3⟩ := hd δ hδ
    refine ⟨E1 ∪ E2 ∪ E3, fun s' hs' => ⟨fun i j => ?_, h2 s s' fun x hx => hs' x (by simp [hx]),
      h3 s s' fun x hx => hs' x (by simp [hx])⟩⟩
    have h4 := h1 s' fun x hx => hs' x (by simp [hx])
    rw [Matrix.map_apply, Matrix.map_apply, ← map_sub, hE]
    apply hk
    have e : A (s * s') i j - A s i j = (A s * (A s' - 1)) i j := by
      rw [hA, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply]
    rw [e, Matrix.mul_apply]
    exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (h4 m j)
  · intro δ hδ
    have hz : 0 < ∑ j, ‖z j‖ + 1 := by positivity
    obtain ⟨k, hk⟩ := exists_pow_norm_lt l (div_pos hδ hz)
    obtain ⟨S, hS⟩ := hF k
    refine ⟨S, fun q hq hqS σ hσ i => ?_⟩
    obtain ⟨R, hR, hRz⟩ := hS q hq hqS σ hσ
    rw [← hexp, hRz]
    calc ‖(R.map (algebraMap ℤ_[l] E) *ᵥ z) i‖ ≤ ∑ j, ‖algebraMap ℤ_[l] E (R i j) * z j‖ :=
          norm_sum_le Finset.univ fun j => algebraMap ℤ_[l] E (R i j) * z j
      _ ≤ ∑ j, δ / (∑ j, ‖z j‖ + 1) * ‖z j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, hE]
        exact mul_le_mul_of_nonneg_right (hk _ (hR i j)).le (norm_nonneg _)
      _ < δ := by
        rw [← Finset.mul_sum, div_mul_eq_mul_div, div_lt_iff₀ hz]
        exact mul_lt_mul_of_pos_left (lt_add_one _) hδ

theorem repr_baseChange {R E B ι : Type} [CommRing R] [Field E] [Algebra R E] [AddCommGroup B] [Module R B]
    [Fintype ι] [DecidableEq ι] (β : Module.Basis ι R B) (φ : B →ₗ[R] B) (z : E ⊗[R] B) :
    ⇑((Algebra.TensorProduct.basis E β).repr (φ.baseChange E z)) =
      (LinearMap.toMatrix β β φ).map (algebraMap R E) *ᵥ ⇑((Algebra.TensorProduct.basis E β).repr z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e b =>
    funext i
    rw [LinearMap.baseChange_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
    have h := congrFun (LinearMap.toMatrix_mulVec_repr β β φ b) i
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, ← h, Matrix.mulVec, dotProduct,
      Matrix.map_apply, map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  | add a b ha hb => simp [map_add, ha, hb, Matrix.mulVec_add]

end GlobalTheory.CayleyHamiltonSmallCoefficients

namespace GlobalTheory

set_option maxHeartbeats 1000000 in
open GlobalTheory.CayleyHamiltonSmallCoefficients in

theorem cayleyHamilton_galV : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [NormedField E] [IsAlgClosed E] [Algebra ℤ_[l] E], (∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) → ∀ (lam : Letter → E) (t d : (Ω ≃ₐ[ℚ] Ω) → E) (S0 : Finset ℕ), (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖t (s * s') - t (s)‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖d (s * s') - d (s)‖ < δ) → (∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s, FrobAt q s → t s = lam (Letter.T q) ∧ d s = (q : E) ^ (w + 1) * lam (Letter.D q)) → ∀ x ∈ X.VB N l w E, (∀ T : Letter, admitted N l T → X.opV N l E T x = lam T • x) → ∀ s : Ω ≃ₐ[ℚ] Ω, X.galV l E s (X.galV l E s x) - t s • X.galV l E s x + d s • x = 0 := by
  intro Ω _ _ _ ε X hε hj N l w _ hl2 hN hNl hw E _ _ _ hE lam t d S0 ht hd hfr x hx heig s
  have hstabG := fun s b hb => GlobalTheory.KZ.StabGal.galB_mem_B ε X hε hj N l w hl2 hN hNl hw s b hb
  have hstabH := fun T hT b hb => GlobalTheory.KZ.B_stable_op ε X hε hj N l w hl2 hN hNl hw T hT b hb
  have hcomm := GlobalTheory.T.hecke_operator_comm_galois_action_modular_tower ε X hε hj N l w hl2 hN hNl hw
  have hcont := GlobalTheory.KZ.GalCont.galB_cont ε X hε hj N l w hl2 hN hNl hw
  have hes := GlobalTheory.T.eichlerShimura_frobenius_quadratic_mod_prime_pow ε X hε hj N l w hl2 hN hNl hw
  obtain ⟨hfree, hfin⟩ := GlobalTheory.KZ.B_free_finite ε X hε hj N l w hl2 hN hNl hw
  classical
  set B := X.B N l w with hBdef
  let ι := Fin (Module.finrank ℤ_[l] B)
  let β : Module.Basis ι ℤ_[l] B := Module.finBasis ℤ_[l] B
  let βE := Algebra.TensorProduct.basis E β
  let gs : (Ω ≃ₐ[ℚ] Ω) → (B →ₗ[ℤ_[l]] B) := fun s => (X.galB l s).restrict (fun b hb => hstabG s b hb)
  let hT : ∀ T : Letter, admitted N l T → (B →ₗ[ℤ_[l]] B) := fun T h => (X.op N l T).restrict (fun b hb => hstabH T h b hb)
  let jm := LinearMap.baseChange E B.subtype

  have halg : Function.Injective (algebraMap ℤ_[l] E) := by
    intro a b hab
    have : ‖algebraMap ℤ_[l] E (a - b)‖ = 0 := by rw [map_sub, hab, sub_self, norm_zero]
    rw [hE, norm_eq_zero, sub_eq_zero] at this
    exact this
  have hflat : Module.Flat ℤ_[l] E := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro e he
    obtain ⟨⟨a, ha⟩, hae⟩ := (Submodule.mem_torsion_iff e).1 he
    have ha0 : a ≠ 0 := fun h => by simp [h] at ha
    change a • e = 0 at hae
    rw [Algebra.smul_def] at hae
    rcases mul_eq_zero.1 hae with h | h
    · exact absurd ((map_eq_zero_iff _ halg).1 h) ha0
    · simp [h]
  have hjinj : Function.Injective jm := by
    rw [show (jm : E ⊗[ℤ_[l]] B → E ⊗[ℤ_[l]] X.Fn l) = LinearMap.lTensor E B.subtype from
      LinearMap.baseChange_eq_ltensor _]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ B.injective_subtype

  have hjG : ∀ s z, X.galV l E s (jm z) = jm ((gs s).baseChange E z) := by
    intro s z
    show ((X.galB l s).baseChange E ∘ₗ B.subtype.baseChange E) z = (B.subtype.baseChange E ∘ₗ (gs s).baseChange E) z
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    rfl
  have hjH : ∀ T (h : admitted N l T) z, X.opV N l E T (jm z) = jm ((hT T h).baseChange E z) := by
    intro T h z
    show ((X.op N l T).baseChange E ∘ₗ B.subtype.baseChange E) z = (B.subtype.baseChange E ∘ₗ (hT T h).baseChange E) z
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    rfl
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hx
  let zc : ι → E := ⇑(βE.repr z)
  let A : (Ω ≃ₐ[ℚ] Ω) → Matrix ι ι ℤ_[l] := fun s => LinearMap.toMatrix β β (gs s)

  have heigc : ∀ T (h : admitted N l T), (LinearMap.toMatrix β β (hT T h)).map (algebraMap ℤ_[l] E) *ᵥ zc = lam T • zc := by
    intro T h
    have h1 : (hT T h).baseChange E z = lam T • z := by
      refine hjinj ?_
      rw [map_smul, ← hjH T h]
      exact heig T h
    rw [show zc = ⇑(βE.repr z) from rfl, ← repr_baseChange, h1, map_smul]
    rfl

  let bF : ι → X.Fn l := fun i => (β i : X.Fn l)
  have hbF : LinearIndependent ℤ_[l] bF := β.linearIndependent.map' B.subtype (by simp)
  have hsum : ∀ (φ : B →ₗ[ℤ_[l]] B) (j : ι), (∑ i, LinearMap.toMatrix β β φ i j • bF i) = ((φ (β j) : B) : X.Fn l) := by
    intro φ j
    simp only [LinearMap.toMatrix_apply, bF]
    have h := congrArg (fun v : B => (v : X.Fn l)) (β.sum_repr (φ (β j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h
  have hgs_mul : ∀ s s', gs (s * s') = gs s ∘ₗ gs s' := by
    intro s s'
    ext b
    simp [gs, Tower.galB_mul]
  have hA : ∀ s s', A (s * s') = A s * A s' := by
    intro s s'
    simp only [A]
    rw [hgs_mul, LinearMap.toMatrix_comp β β β]
  have hone : ∀ j : ι, (∑ i, (1 : Matrix ι ι ℤ_[l]) i j • bF i) = bF j := by
    intro j
    rw [Finset.sum_eq_single j (fun i _ hi => by rw [Matrix.one_apply_ne hi, zero_smul])
      (fun h => absurd (Finset.mem_univ j) h), Matrix.one_apply_eq, one_smul]
  have hAc : ∀ k : ℕ, ∃ E0 : Finset Ω, ∀ s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) →
      ∀ i j, (A s' - 1) i j ∈ (idl l) ^ k := by
    intro k
    obtain ⟨m, hm⟩ := small_coeffs l bF hbF k
    choose E0 hE0 using fun j : ι => hcont (bF j) (β j).2 m
    refine ⟨Finset.univ.biUnion E0, fun s' hs' i j => ?_⟩
    have hfix : ∀ x ∈ E0 j, s' x = x := fun x hx => hs' x (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hx⟩)
    refine hm (fun i => (A s' - 1) i j) ?_ i
    intro u
    have h2 : (∑ i, (A s' - 1) i j • bF i) = X.galB l s' (bF j) - bF j := by
      simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, hone]
      rw [hsum (gs s') j]
      rfl
    rw [h2]
    exact hE0 j s' hfix u
  have hF : ∀ k : ℕ, ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ σ : Ω ≃ₐ[ℚ] Ω, FrobAt q σ →
      ∃ R : Matrix ι ι ℤ_[l], (∀ i j, R i j ∈ (idl l) ^ k) ∧
        ((A σ).map (algebraMap ℤ_[l] E) * (A σ).map (algebraMap ℤ_[l] E) - t σ • (A σ).map (algebraMap ℤ_[l] E)
          + d σ • (1 : Matrix ι ι E)) *ᵥ zc = R.map (algebraMap ℤ_[l] E) *ᵥ zc := by
    intro k
    obtain ⟨m, hm⟩ := small_coeffs l bF hbF k
    obtain ⟨S1, hS1⟩ := hes m
    refine ⟨S1 ∪ S0 ∪ (N * l).primeFactors, fun q hq hqS σ hσ => ?_⟩
    simp only [Finset.mem_union, not_or, Nat.mem_primeFactors] at hqS
    obtain ⟨⟨hq1, hq0⟩, hq2⟩ := hqS
    have hNl0 : N * l ≠ 0 := Nat.mul_ne_zero (by omega) (Fact.out : l.Prime).ne_zero
    have hndvd : ¬ q ∣ N * l := fun h => hq2 ⟨hq, h, hNl0⟩
    have hadmT : admitted N l (Letter.T q) := ⟨hq, hndvd⟩
    have hadmD : admitted N l (Letter.D q) :=
      (Nat.Prime.coprime_iff_not_dvd hq).2 (fun h => hndvd (Dvd.dvd.mul_right h l))
    obtain ⟨htq, hdq⟩ := hfr q hq hq0 σ hσ
    let Rφ : B →ₗ[ℤ_[l]] B := gs σ ∘ₗ gs σ - hT _ hadmT ∘ₗ gs σ + ((q : ℤ_[l]) ^ (w + 1)) • hT _ hadmD
    refine ⟨LinearMap.toMatrix β β Rφ, fun i j => ?_, ?_⟩
    · refine hm (fun i => LinearMap.toMatrix β β Rφ i j) ?_ i
      intro u
      rw [hsum Rφ j]
      exact hS1 q hq hq1 σ hσ (bF j) (β j).2 u
    · have hc : hT _ hadmT ∘ₗ gs σ = gs σ ∘ₗ hT _ hadmT := by
        exact LinearMap.ext fun b => Subtype.ext (hcomm _ hadmT σ b b.2)
      have hcm : LinearMap.toMatrix β β (hT _ hadmT) * A σ = A σ * LinearMap.toMatrix β β (hT _ hadmT) := by
        simp only [A]
        rw [← LinearMap.toMatrix_comp β β β, ← LinearMap.toMatrix_comp β β β, hc]
      have hR : LinearMap.toMatrix β β Rφ = A σ * A σ - LinearMap.toMatrix β β (hT _ hadmT) * A σ
          + ((q : ℤ_[l]) ^ (w + 1)) • LinearMap.toMatrix β β (hT _ hadmD) := by
        simp only [Rφ, map_add, map_sub, map_smul, LinearMap.toMatrix_comp β β β]
        rfl
      have hmap : (LinearMap.toMatrix β β Rφ).map (algebraMap ℤ_[l] E) =
          (A σ).map (algebraMap ℤ_[l] E) * (A σ).map (algebraMap ℤ_[l] E)
          - (LinearMap.toMatrix β β (hT _ hadmT)).map (algebraMap ℤ_[l] E) * (A σ).map (algebraMap ℤ_[l] E)
          + (algebraMap ℤ_[l] E ((q : ℤ_[l]) ^ (w + 1))) •
            (LinearMap.toMatrix β β (hT _ hadmD)).map (algebraMap ℤ_[l] E) := by
        rw [hR]
        ext i j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
          smul_eq_mul, map_add, map_sub, map_mul, map_sum]
      have hHa : (LinearMap.toMatrix β β (hT _ hadmT)).map (algebraMap ℤ_[l] E) * (A σ).map (algebraMap ℤ_[l] E) =
          (A σ).map (algebraMap ℤ_[l] E) * (LinearMap.toMatrix β β (hT _ hadmT)).map (algebraMap ℤ_[l] E) := by
        rw [← Matrix.map_mul, hcm, Matrix.map_mul]
      rw [hmap, hHa]
      simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.one_mulVec]
      rw [heigc _ hadmT, heigc _ hadmD, Matrix.mulVec_smul, htq, hdq, smul_smul]
      simp [map_pow, map_natCast]
  have hY := matrix_relation l hE A t d zc hA hAc ht hd hF (fun s E0 S => exists_fixing_mul_frobAt s E0 S) s
  have hW : (gs s).baseChange E ((gs s).baseChange E z) - t s • (gs s).baseChange E z + d s • z = 0 := by
    apply βE.repr.injective
    rw [map_zero]
    apply DFunLike.coe_injective
    rw [Finsupp.coe_zero]
    refine Eq.trans ?_ hY
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec]
    rw [map_add, map_sub, map_smul, map_smul, Finsupp.coe_add,
      Finsupp.coe_sub, Finsupp.coe_smul, Finsupp.coe_smul, repr_baseChange, repr_baseChange]
  show X.galV l E s (X.galV l E s (jm z)) - t s • X.galV l E s (jm z) + d s • jm z = 0
  calc _ = jm ((gs s).baseChange E ((gs s).baseChange E z) - t s • (gs s).baseChange E z + d s • z) := by
        rw [map_add, map_sub, map_smul, map_smul, hjG, hjG]
    _ = 0 := by rw [hW, map_zero]

end GlobalTheory

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiCapelliStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CapPhi
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ProdOfFnSmul
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasPsA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandPsB

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

namespace CapPs

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

local notation "𝕄" => Matrix (Fin n) (Fin n) ℂ
local notation "𝕋" => Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ

section Chains

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def opL (c : ℂ) (X : 𝕄) (F : 𝕄 → E) : 𝕄 → E := fun z => c • F z + Lhol X F z

def chainL {m : ℕ} (s : Fin m → ℂ × 𝕄) (F : 𝕄 → E) : 𝕄 → E :=
  (List.ofFn fun i => opL (s i).1 (s i).2).foldr (fun t h => t h) F

lemma chainL_succ {m : ℕ} (s : Fin (m + 1) → ℂ × 𝕄) (F : 𝕄 → E) :
    chainL s F = opL (s 0).1 (s 0).2 (chainL (fun i => s i.succ) F) := by
  simp only [chainL, List.ofFn_succ, List.foldr_cons]

lemma top_opL (x : ℂ) (a b : Fin n) (F : 𝕄 → E) :
    Formalism.QuantumDeterminants.Top negL x a b F = opL (if a = b then x else 0) (-(Matrix.single a b 1)) F := by
  funext z
  unfold Formalism.QuantumDeterminants.Top opL negL Lhol
  rw [Matrix.neg_mul, map_neg]
  split_ifs <;> simp

def sσ (u : ℂ) (σ : Equiv.Perm (Fin n)) : Fin n → ℂ × 𝕄 :=
  fun i => (if σ i = i then u - ((i : ℕ) : ℂ) else 0, -(Matrix.single (σ i) i 1))

lemma qdet_chain (u : ℂ) (F : 𝕄 → E) (z : 𝕄) :
    Formalism.QuantumDeterminants.qdetOp negL u F z = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • chainL (sσ u σ) F z := by
  unfold Formalism.QuantumDeterminants.qdetOp Formalism.QuantumDeterminants.qminorOp
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Pi.smul_apply]
  congr 1
  show _ = (List.ofFn fun i => opL (sσ u σ i).1 (sσ u σ i).2).foldr (fun t h => t h) F z
  have hl : (List.ofFn fun k : Fin n => Formalism.QuantumDeterminants.Top (E := E) negL (u - ((k : ℕ) : ℂ)) (id (σ k)) (id k)) =
      List.ofFn fun i => opL (E := E) (sσ u σ i).1 (sσ u σ i).2 := by
    congr 1
    funext k G
    exact top_opL _ _ _ G
  rw [hl]

end Chains

def opH (c : ℂ) (X : 𝕄) (g : 𝕋 → ℂ) : 𝕋 → ℂ := fun p => c • g p + GPs.DH X g p

def chainH {m : ℕ} (s : Fin m → ℂ × 𝕄) (g : 𝕋 → ℂ) : 𝕋 → ℂ :=
  (List.ofFn fun i => opH (s i).1 (s i).2).foldr (fun t h => t h) g

lemma chainH_succ {m : ℕ} (s : Fin (m + 1) → ℂ × 𝕄) (g : 𝕋 → ℂ) :
    chainH s g = opH (s 0).1 (s 0).2 (chainH (fun i => s i.succ) g) := by
  simp only [chainH, List.ofFn_succ, List.foldr_cons]

lemma sm_chainH : ∀ {m : ℕ} (s : Fin m → ℂ × 𝕄) {g : 𝕋 → ℂ}, ContDiffOn ℂ ∞ g (GPs.Wset n) →
    ContDiffOn ℂ ∞ (chainH s g) (GPs.Wset n)
  | 0, s, g, hg => by simpa [chainH] using hg
  | m + 1, s, g, hg => by
    rw [chainH_succ]
    show ContDiffOn ℂ ∞ (fun p => (s 0).1 • chainH _ g p + GPs.DH (s 0).2 (chainH _ g) p) _
    exact ((sm_chainH _ hg).const_smul _).add (GPs.sm_DH _ (sm_chainH _ hg))

lemma chainH_slice : ∀ {m : ℕ} (s : Fin m → ℂ × 𝕄) {g : 𝕋 → ℂ}, ContDiffOn ℂ ∞ g (GPs.Wset n) →
    ∀ p ∈ GPs.Wset n, chainH s g p = chainL s (fun y => g (y, p.2)) p.1
  | 0, s, g, _, p, _ => by simp [chainH, chainL]
  | m + 1, s, g, hg, p, hp => by
    rw [chainH_succ, chainL_succ]
    show (s 0).1 • chainH _ g p + GPs.DH (s 0).2 (chainH _ g) p =
      (s 0).1 • chainL _ (fun y => g (y, p.2)) p.1 + Lhol (s 0).2 (chainL _ (fun y => g (y, p.2))) p.1
    have hS : IsOpen {y : 𝕄 | (y, p.2) ∈ GPs.Wset n} :=
      GPs.isOpen_kappaOpenNeighbourhood.preimage (continuous_id.prodMk continuous_const)
    rw [chainH_slice _ hg p hp, GPs.DH_slice _ (GPs.dAtW (sm_chainH _ hg) hp)]
    congr 1
    exact GPs.lhol_congr hS (fun y hy => chainH_slice _ hg (y, p.2) hy) _ (show (p.1, p.2) ∈ GPs.Wset n from hp)

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ} [CompactSpace (KG ε)]

lemma Fint_opH (T : KType ε Λ) {g₁ g₂ : 𝕋 → ℂ} (h₁ : ContDiffOn ℂ ∞ g₁ (GPs.Wset n))
    (h₂ : ContDiffOn ℂ ∞ g₂ (GPs.Wset n)) (c : ℂ) {x : 𝕄} (hx : x ∈ Ps1.Uset ε) :
    GPs.Fint T (fun p => c • g₁ p + g₂ p) x = c • GPs.Fint T g₁ x + GPs.Fint T g₂ x := by
  unfold GPs.Fint
  have : ∫ k, (c • g₁ (GPs.emb x k) + g₂ (GPs.emb x k)) • GPs.Pk T k ∂(muK ε) =
      c • ∫ k, g₁ (GPs.emb x k) • GPs.Pk T k ∂(muK ε) + ∫ k, g₂ (GPs.emb x k) • GPs.Pk T k ∂(muK ε) := by
    simp only [add_smul, smul_eq_mul, mul_smul]
    have e := integral_add ((GPs.int_int T h₁ hx).smul c) (GPs.int_int T h₂ hx)
    simp only [Pi.smul_apply] at e
    rw [e, integral_smul]
  rw [this, smul_add, smul_comm (GPs.cK T) c]

lemma chain_Fint (T : KType ε Λ) : ∀ {m : ℕ} (s : Fin m → ℂ × 𝕄) {g : 𝕋 → ℂ},
    ContDiffOn ℂ ∞ g (GPs.Wset n) → ∀ z ∈ Ps1.Uset ε,
      chainL s (GPs.Fint T g) z = GPs.Fint T (chainH s g) z
  | 0, s, g, _, z, _ => by simp [chainL, chainH]
  | m + 1, s, g, hg, z, hz => by
    rw [chainL_succ, chainH_succ]
    show (s 0).1 • chainL _ (GPs.Fint T g) z + Lhol (s 0).2 (chainL _ (GPs.Fint T g)) z =
      GPs.Fint T (fun p => (s 0).1 • chainH _ g p + GPs.DH (s 0).2 (chainH _ g) p) z
    rw [Fint_opH T (sm_chainH _ hg) (GPs.sm_DH _ (sm_chainH _ hg)) _ hz, chain_Fint T _ hg z hz,
      GPs.lhol_congr Ps1.isOpen_Uset (fun y hy => chain_Fint T _ hg y hy) _ hz,
      GPs.lhol_Fint T (sm_chainH _ hg) _ hz]

lemma fold_conj (c : 𝕄 → 𝕄) : ∀ {p : ℕ} (T T' : Fin p → (𝕄 → ℂ) → (𝕄 → ℂ)),
    (∀ i F, T i (fun y => F (c y)) = fun y => T' i F (c y)) → ∀ F : 𝕄 → ℂ,
    (List.ofFn T).foldr (fun t h => t h) (fun y => F (c y)) =
      fun y => (List.ofFn T').foldr (fun t h => t h) F (c y)
  | 0, _, _, _, F => by simp
  | p + 1, T, T', h, F => by
    simp only [List.ofFn_succ, List.foldr_cons]
    rw [fold_conj c (fun i => T i.succ) (fun i => T' i.succ) (fun i => h i.succ) F, h 0]

lemma qdet_conj (A B : 𝕄) (hAB : A * B = 1) (hBA : B * A = 1) (u : ℂ) (F : 𝕄 → ℂ) (z : 𝕄) :
    Formalism.QuantumDeterminants.qdetOp negL u (fun y => F (A * y * B)) z =
      Formalism.QuantumDeterminants.qdetOp (fun a b (G : 𝕄 → ℂ) => fun w => -Lhol (A * Matrix.single a b 1 * B) G w) u F
        (A * z * B) := by
  unfold Formalism.QuantumDeterminants.qdetOp Formalism.QuantumDeterminants.qminorOp
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Pi.smul_apply, Pi.smul_apply]
  congr 1
  rw [fold_conj (fun y => A * y * B) _ _ (fun i G => ?_) F]
  funext y
  unfold Formalism.QuantumDeterminants.Top negL
  rw [GPs.lhol_conj A B hAB hBA]

lemma qdet_eq_gen (Eop : Fin n → Fin n → (𝕄 → ℂ) → (𝕄 → ℂ)) (A : Fin n → Fin n → Module.End ℂ (smoothS n))
    (hA : ∀ a b (F : 𝕄 → ℂ) (G : smoothS n), Set.EqOn F G (OmegaSet n) →
      Set.EqOn (Eop a b F) ((A a b G : smoothS n) : 𝕄 → ℂ) (OmegaSet n))
    (u : ℂ) (F : 𝕄 → ℂ) (G : smoothS n) (h : Set.EqOn F G (OmegaSet n)) {z : 𝕄} (hz : z ∈ OmegaSet n) :
    Formalism.QuantumDeterminants.qdetOp Eop u F z = ((capelliC A u G : smoothS n) : 𝕄 → ℂ) z := by
  have htop : ∀ (x : ℂ) (a b : Fin n) (F : 𝕄 → ℂ) (G : smoothS n), Set.EqOn F G (OmegaSet n) →
      Set.EqOn (Formalism.QuantumDeterminants.Top Eop x a b F) ((capEntry A x a b G : smoothS n) : 𝕄 → ℂ) (OmegaSet n) := by
    intro x a b F G h z hz
    rw [capEntry_apply_end]
    show (if a = b then x • F z else 0) + Eop a b F z =
      ((A a b G : smoothS n) : 𝕄 → ℂ) z + ((if a = b then x • G else 0 : smoothS n) : 𝕄 → ℂ) z
    rw [hA a b F G h hz, h hz]
    split_ifs <;> simp [add_comm]
  unfold Formalism.QuantumDeterminants.qdetOp Formalism.QuantumDeterminants.qminorOp capelliC cminor
  rw [Finset.sum_apply, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Pi.smul_apply, LinearMap.smul_apply, Submodule.coe_smul_of_tower, Pi.smul_apply, zsmul_eq_mul, smul_eq_mul]
  congr 1
  exact CapPhi.fold_eqOn n (fun k => Formalism.QuantumDeterminants.Top Eop (u - ((k : ℕ) : ℂ)) (id (σ k)) (id k))
    (fun j => capEntry A (u - ((j : ℕ) : ℂ)) (id (σ j)) (id j))
    (fun i F' G' h' => htop _ _ _ F' G' h') F G h hz

lemma cap_conj_phi (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) (Y : ℂ) (A B : 𝕄) (hAB : A * B = 1)
    (hBA : B * A = 1) {z : 𝕄} (hz : A * z * B ∈ OmegaSet n) :
    Formalism.QuantumDeterminants.qdetOp negL (Y + ((n : ℂ) - 1) / 2) (fun y => PhiM μ (A * y * B)) z =
      Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y * PhiM μ (A * z * B) := by
  have hA : ∀ a b (F : 𝕄 → ℂ) (G : smoothS n), Set.EqOn F G (OmegaSet n) →
      Set.EqOn ((fun a b (G : 𝕄 → ℂ) => fun w => -Lhol (A * Matrix.single a b 1 * B) G w) a b F)
        (((∑ c, ∑ d, (A c a * B b d) • CapPhi.negE c d : Module.End ℂ (smoothS n)) G : smoothS n) : 𝕄 → ℂ)
        (OmegaSet n) := by
    intro a b F G h w hw
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
      Finset.sum_apply, Pi.smul_apply, CapPhi.negE_apply _ _ _ hw]
    rw [lhol_congr h hw, CasPsA.conj_single_eq, GPs.lhol_sumX]
    simp only [GPs.lhol_sumX, GPs.lhol_smulX, Finset.sum_neg_distrib, smul_neg]
  rw [qdet_conj A B hAB hBA, qdet_eq_gen _ _ hA _ _ _ (CapPhi.phiS_eqOn μ) hz,
    CapAd.capelliC_ad _ ((isGlRep_iff_glRelR _).mp CapPhi.isGlRep_negE) A B hBA hAB,
    ← CapPhi.qdet_eq _ _ _ (CapPhi.phiS_eqOn μ) hz, cap_phiM μ lam hμ Y hz]

end CapPs

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

open CapPs in
theorem cap_psM (T : KType ε Λ) (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ posSet n ⊆ U ∧ DifferentiableOn ℂ (psM T μ) U ∧
      ∀ (Y : ℂ), ∀ z ∈ U,
        Formalism.QuantumDeterminants.qdetOp negL (Y + ((n : ℂ) - 1) / 2) (psM T μ) z =
          Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • psM T μ z := by
  have := compactSpace_KG ε
  have hK : ∀ k : KG ε, toMK k⁻¹ * toMK k = 1 ∧ toMK k * toMK k⁻¹ = 1 := fun k => by
    rw [Ps1.toMK_inv_eq, ← Matrix.star_eq_conjTranspose]
    exact ⟨Unitary.star_mul_self_of_mem k.2.1, Unitary.mul_star_self_of_mem k.2.1⟩
  refine ⟨Ps1.Uset ε, Ps1.isOpen_Uset, Ps1.posSet_subset_Uset, fun z hz => ?_, fun Y z hz => ?_⟩
  · exact (GPs.hasFDerivAt_Fint T (GPs.smooth_g0_on_Wset μ) hz).differentiableAt.differentiableWithinAt
  set u : ℂ := Y + ((n : ℂ) - 1) / 2 with hu
  set C : ℂ := Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y with hC
  have hint : ∀ k : KG ε, ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      chainH (sσ u σ) (GPs.g0 μ) (GPs.emb z k) = C * GPs.g0 μ (GPs.emb z k) := by
    intro k
    rw [Finset.sum_congr rfl fun σ _ => by rw [chainH_slice _ (GPs.smooth_g0_on_Wset μ) _ (GPs.emb_mem hz k)], ← qdet_chain]
    exact cap_conj_phi μ lam hμ Y (toMK k⁻¹) (toMK k) (hK k).1 (hK k).2 (GPs.emb_mem hz k)
  have hI : ∀ σ : Equiv.Perm (Fin n),
      Integrable (fun k => chainH (sσ u σ) (GPs.g0 μ) (GPs.emb z k) • GPs.Pk T k) (muK ε) :=
    fun σ => GPs.int_int T (sm_chainH _ (GPs.smooth_g0_on_Wset μ)) hz
  rw [GPs.psM_eq, qdet_chain, Finset.sum_congr rfl fun σ _ => by rw [chain_Fint T _ (GPs.smooth_g0_on_Wset μ) z hz]]
  calc ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • GPs.Fint T (chainH (sσ u σ) (GPs.g0 μ)) z
      = GPs.cK T • ∫ k, ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
          (chainH (sσ u σ) (GPs.g0 μ) (GPs.emb z k) • GPs.Pk T k) ∂(muK ε) := by
        have e := integral_finsetSum (μ := muK ε) Finset.univ
          (fun σ _ => (hI σ).smul (((Equiv.Perm.sign σ : ℤ) : ℂ)))
        simp only [Pi.smul_apply] at e
        rw [e, Finset.smul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [integral_smul, GPs.Fint, smul_comm]
    _ = GPs.cK T • ∫ k, C • (GPs.g0 μ (GPs.emb z k) • GPs.Pk T k) ∂(muK ε) := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only [← smul_assoc, ← Finset.sum_smul]
        rw [hint k, smul_eq_mul]
    _ = C • GPs.Fint T (GPs.g0 μ) z := by
        rw [integral_smul, GPs.Fint, smul_comm]

end ReciprocityTheory.ChartRestriction.DS.S7

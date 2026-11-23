import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import GroundTheory.PAdicHodge.AxLemma
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaKillsFplusDiscreteFormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFunctionalOddWeightOddPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombination
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueGalBEquivariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerBettiModuleFreeFiniteStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsThBSuccCoeffCongStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLinearLimitOfCompatibleFamilyStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSpanEigenOfBaseChangeEigenStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineFunctionalEqPeriodMulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringNonunitsPowModEqZero
import Development.AbelianVarietyTheory.Definitions.Foundations.ThNSpec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalValueModPrimePowUniqueOddWeightStatement

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois
open scoped TensorProduct Matrix

namespace GlobalTheory.LamPr

variable {l : ℕ} [Fact l.Prime]

theorem norm_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem l_ne_zero : ((l : ℕ) : Qbar l) ≠ 0 := by
  exact_mod_cast (Fact.out : l.Prime).ne_zero

theorem eq_zero_of_le {z : ℂ_[l]} {C : ℝ} {c : ℕ} (h : ∀ n, c ≤ n → ‖z‖ ≤ C * ‖((l : ℕ) : Qbar l) ^ n‖) : z = 0 := by
  have h1 : Filter.Tendsto (fun n : ℕ => C * ‖((l : ℕ) : Qbar l) ^ n‖) Filter.atTop (nhds 0) := by
    simp_rw [norm_pow]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one (l := l))).const_mul C
  exact norm_le_zero_iff.1 (ge_of_tendsto h1 (Filter.eventually_atTop.2 ⟨c, h⟩))

theorem lam_le {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l} {C : ℝ} (hC : ∀ f : ℕ → Qbar l, (∀ s, ‖f s‖ ≤ 1) → ‖lam f‖ ≤ C)
    {a : Qbar l} (ha : a ≠ 0) (f : ℕ → Qbar l) (hf : ∀ s, ‖f s‖ ≤ ‖a‖) : ‖lam f‖ ≤ C * ‖a‖ := by
  have hp : 0 < ‖a‖ := norm_pos_iff.2 ha
  have h := hC (a⁻¹ • f) (fun s => by
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ hp, mul_one]; exact hf s)
  rw [map_smul, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ hp] at h
  linarith

theorem lam_gal {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l} (h : FinSupp lam) : ∃ F : Finset (Qbar l),
    ∀ τ : Qbar l →+* Qbar l, (∀ a ∈ F, τ a = a) → ∀ f : ℕ → Qbar l, lam (fun s => τ (f s)) = τ (lam f) := by
  classical
  obtain ⟨S, hS⟩ := h
  have key : ∀ f : ℕ → Qbar l, lam f = ∑ s ∈ S, f s * lam (Pi.single s 1) := by
    intro f
    have h0 := hS (f - ∑ s ∈ S, f s • (Pi.single s 1 : ℕ → Qbar l)) (fun s hs => by
      simp [Finset.sum_apply, Pi.single_apply, hs])
    rw [map_sub, sub_eq_zero, map_sum] at h0
    simpa using h0
  refine ⟨S.image fun s => lam (Pi.single s 1), fun τ hτ f => ?_⟩
  rw [key f, key, map_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [map_mul, hτ _ (Finset.mem_image_of_mem _ hs)]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem exists_restrict [IsAlgClosure ℚ Ω] (j : Ω →+* Qbar l) (τ : Qbar l ≃+* Qbar l) :
    ∃ s : Ω ≃ₐ[ℚ] Ω, ∀ x, j (s x) = τ (j x) := by
  letI : Algebra Ω (Qbar l) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (Qbar l) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let τ' : Qbar l ≃ₐ[ℚ] Qbar l := AlgEquiv.ofRingEquiv (f := τ) (fun x => by simp)
  exact ⟨τ'.restrictNormal Ω, fun x => τ'.restrictNormal_commutes Ω x⟩

theorem norm_le_of_cgA {A : ValuationSubring Ω} {j : Ω →+* Qbar l} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) {n : ℕ} {x y : Ω}
    (h : CgA A l n x y) : ‖j x - j y‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
  obtain ⟨z, hz, h⟩ := h
  rw [← map_sub, h, map_mul, map_pow, map_natCast, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) ((hj z).1 hz)

theorem val_l_lt_one {A : ValuationSubring Ω} {j : Ω →+* Qbar l} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) :
    A.valuation (l : Ω) < 1 := by
  have h0 : (l : Ω) ≠ 0 := fun h => l_ne_zero (l := l) (by rw [← map_natCast j, h, map_zero])
  by_contra hc
  have h1 : A.valuation (l : Ω)⁻¹ ≤ 1 := by
    rw [map_inv₀]; exact inv_le_one_of_one_le₀ (not_lt.1 hc)
  have h2 := (hj _).1 ((A.valuation_le_one_iff _).1 h1)
  rw [map_inv₀, map_natCast, norm_inv, inv_le_one₀ (norm_pos_iff.2 l_ne_zero)] at h2
  exact absurd norm_l_lt_one (not_lt.2 h2)

theorem mem_iff_of_le [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω} {j : Ω →+* Qbar l} (hl : (l : Ω) ∈ A.nonunits)
    (hj : ∀ x ∈ A, ‖j x‖ ≤ 1) (x : Ω) : x ∈ A ↔ ‖j x‖ ≤ 1 := by
  refine ⟨hj x, fun h => ?_⟩
  by_contra hx
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ A.zero_mem)
  have hv : x⁻¹ ∈ A.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff, map_inv₀]
    exact inv_lt_one_of_one_lt₀ (not_le.1 fun h1 => hx ((A.valuation_le_one_iff x).1 h1))
  obtain ⟨k, z, hz, hk⟩ := GlobalTheory.cgA_pow_of_mem_nonunits l A hl _ hv
  have h1 := congrArg (fun y => ‖j y‖) hk
  simp only [sub_zero, pow_one, map_mul, map_pow, map_inv₀, map_natCast, norm_mul, norm_pow, norm_inv] at h1
  have hp : 0 < ‖j x‖ := norm_pos_iff.2 ((map_ne_zero j).2 hx0)
  have h2 : 1 ≤ ‖j x‖⁻¹ ^ k := one_le_pow₀ ((one_le_inv₀ hp).2 h)
  have h3 := mul_le_of_le_one_right (norm_nonneg ((l : ℕ) : Qbar l)) (hj z hz)
  linarith [norm_l_lt_one (l := l)]

theorem exists_limit [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (A : ValuationSubring Ω) (j : Ω →+* Qbar l)
    (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
    (hhol : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) (N w D : ℕ) (hl2 : l ≠ 2) (hN : 5 ≤ N)
    (hNl : Nat.Coprime N l) (hw : Odd w) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (hfin : FinSupp lam) (C : ℝ)
    (hC : ∀ f : ℕ → Qbar l, (∀ s, ‖f s‖ ≤ 1) → ‖lam f‖ ≤ C) :
    ∃ (L : Qbar l ⊗[ℤ_[l]] X.Fn l →ₗ[Qbar l] ℂ_[l]) (F : Finset (Qbar l)),
      (∀ n, ∀ b ∈ X.B N l w, ∀ φ, IsThB X A N l n b φ →
        ‖(lam (seqN D j φ) : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] b)‖ ≤ C * ‖((l : ℕ) : Qbar l) ^ n‖) ∧
      (∀ b ∈ X.B N l w, ‖L (1 ⊗ₜ[ℤ_[l]] b)‖ ≤ C) ∧
      ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ a ∈ F, a ∈ K) → ∀ (τ : Qbar l ≃ₐ[K] Qbar l) (s : Ω ≃ₐ[ℚ] Ω),
        (∀ x, j (s x) = τ (j x)) → ∀ b ∈ X.B N l w, L (1 ⊗ₜ[ℤ_[l]] X.galB l s b) = τ • L (1 ⊗ₜ[ℤ_[l]] b) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hlN : ¬ l ∣ N := (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hNl.symm
  have hlA : (l : Ω) ∈ A.nonunits := (ValuationSubring.mem_nonunits_iff A).2 (val_l_lt_one hj)
  have hhol' : ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs := hhol.imp fun _ h => h.symm
  have hex : ∀ n, ∀ b ∈ X.B N l w, ∃ φ, IsThB X A N l n b φ := fun n b hb =>
    (GlobalTheory.T.exists_cuspFunctional_oddWeight_oddPrime Ω ε X A N l inferInstance hhol' hl2 hlN (by omega) hlA n w hw b hb).imp fun _ h => h.1
  obtain ⟨L, hL⟩ := GlobalTheory.T.exists_linearMap_limit_of_compatible_approximations l (X.Fn l) (X.B N l w)
    (fun n b x => ∃ φ, IsThB X A N l n b φ ∧ x = lam (seqN D j φ)) C
    (fun n b hb => (hex n b hb).elim fun φ h => ⟨_, φ, h, rfl⟩)
    (by
      rintro n b hb _ _ ⟨φ, h, rfl⟩ ⟨φ', h', rfl⟩
      rw [← map_sub]
      exact lam_le hC (pow_ne_zero _ l_ne_zero) _ fun s =>
        norm_le_of_cgA hj (GlobalTheory.T.cgA_coeff_of_isThB_succ Ω ε X A N l hl2 hlN (by omega) hlA n b φ φ' h h' _))
    (by
      rintro n b hb b' hb' a a' _ _ ⟨φ, h, rfl⟩ ⟨φ', h', rfl⟩
      refine ⟨_, GlobalTheory.ThAdd.isThB_add Ω ε X A N l n w b b' hlA hb hb' a a' φ φ' h h', ?_⟩
      rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add]
      congr 1
      funext s
      simp [seqN])
  have hL' : ∀ n, ∀ b ∈ X.B N l w, ∀ φ, IsThB X A N l n b φ →
      ‖(lam (seqN D j φ) : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] b)‖ ≤ C * ‖((l : ℕ) : Qbar l) ^ n‖ :=
    fun n b hb φ h => hL n b hb _ ⟨φ, h, rfl⟩
  obtain ⟨F, hF⟩ := lam_gal hfin
  refine ⟨L, F, hL', fun b hb => ?_, fun K hK τ s hs b hb => ?_⟩
  · obtain ⟨φ, h⟩ := hex 0 b hb
    have h1 := hL' 0 b hb φ h
    rw [pow_zero, norm_one, mul_one] at h1
    have h2 : ‖(lam (seqN D j φ) : ℂ_[l])‖ ≤ C := by
      rw [PadicComplex.norm_extends]
      obtain ⟨f, -, -, -, hint, -⟩ := h
      exact hC _ fun s => (hj _).1 (hint _)
    have e : L (1 ⊗ₜ[ℤ_[l]] b) = (lam (seqN D j φ) : ℂ_[l]) + -((lam (seqN D j φ) : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] b)) := by
      ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 (by rwa [norm_neg]))
  · have hsA : ∀ x, x ∈ A ↔ s x ∈ A := fun x => by rw [hj, hj, hs, GroundTheory.PAdicHodge.norm_gal_apply]
    have hgb := GlobalTheory.KZ.StabGal.galB_mem_B ε X ε.injective hhol N l w hl2 hN hNl hw s b hb
    rw [← sub_eq_zero]
    refine eq_zero_of_le (C := C) (c := 0) fun n _ => ?_
    obtain ⟨φ, h⟩ := hex n b hb
    have h1 := hL' n _ hgb _ (GlobalTheory.isThB_galB Ω ε X A N l n w s hlA hsA b hb φ h)
    have h2 := hL' n b hb φ h
    have e1 : seqN D j (HahnSeries.map φ (s : Ω →+* Ω)) = fun t => (τ : Qbar l →+* Qbar l) (seqN D j φ t) := by
      funext t
      simp [seqN, hs]
    rw [e1, hF _ (fun a ha => τ.commutes ⟨a, hK a ha⟩)] at h1
    rw [← GroundTheory.PAdicHodge.norm_smul_gal τ, smul_sub, GroundTheory.PAdicHodge.gal_smul_coe] at h2
    have e : L (1 ⊗ₜ[ℤ_[l]] X.galB l s b) - τ • L (1 ⊗ₜ[ℤ_[l]] b) =
        (((τ (lam (seqN D j φ)) : Qbar l) : ℂ_[l]) - τ • L (1 ⊗ₜ[ℤ_[l]] b)) +
          -(((τ (lam (seqN D j φ)) : Qbar l) : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] X.galB l s b)) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 (by rw [norm_neg]; exact h1))

theorem exists_period [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (A : ValuationSubring Ω) (j : Ω →+* Qbar l)
    (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
    (hhol : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) (N w D : ℕ) (hl2 : l ≠ 2) (hN : 5 ≤ N)
    (hNl : Nat.Coprime N l) (hw : Odd w) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (hfin : FinSupp lam) (C : ℝ)
    (hC : ∀ f : ℕ → Qbar l, (∀ s, ‖f s‖ ≤ 1) → ‖lam f‖ ≤ C) (ρ : R2 Ω l)
    (hρ : ∃ F : Finset Ω, ∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
      mat ρ s 1 0 = 0 ∧ mat ρ s 0 0 = algebraMap ℤ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]) ^ (w + 1)))
    (m : ℕ) (σ : Fin m → (Fin 2 → Qbar l) →ₗ[Qbar l] (Qbar l ⊗[ℤ_[l]] X.Fn l))
    (hσ : ∀ i v, σ i v ∈ X.VB N l w (Qbar l))
    (hσg : ∀ i s v, X.galV l (Qbar l) s (σ i v) = σ i (mat ρ s *ᵥ v)) :
    ∃ (L : Qbar l ⊗[ℤ_[l]] X.Fn l →ₗ[Qbar l] ℂ_[l]) (κ : Fin m → Qbar l) (per : ℂ_[l]),
      (∀ n, ∀ b ∈ X.B N l w, ∀ φ, IsThB X A N l n b φ →
        ‖(lam (seqN D j φ) : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] b)‖ ≤ C * ‖((l : ℕ) : Qbar l) ^ n‖) ∧
      (∀ b ∈ X.B N l w, ‖L (1 ⊗ₜ[ℤ_[l]] b)‖ ≤ C) ∧ ‖per‖ = 1 ∧
      ∀ i v, L (σ i v) = per * ((κ i * v 1 : Qbar l) : ℂ_[l]) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hlN : ¬ l ∣ N := (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hNl.symm
  have hlA : (l : Ω) ∈ A.nonunits := (ValuationSubring.mem_nonunits_iff A).2 (val_l_lt_one hj)
  have hhol' : ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs := hhol.imp fun _ h => h.symm
  obtain ⟨L, F, hL, hb, hg⟩ := exists_limit X A j hj hhol N w D hl2 hN hNl hw lam hfin C hC
  obtain ⟨F₀, hF₀⟩ := hρ
  obtain ⟨c, hc⟩ := GlobalTheory.T.theta_kills_Fplus_discrete_form l Ω ε X A hhol' (val_l_lt_one hj) N w F₀ hl2 hlN (by omega) hw
  have := (GlobalTheory.T.kummerBettiModule_free_finite ε X ε.injective hhol N l w hl2 hN hNl hw).1
  have hkill : ∀ i, L (σ i ![1, 0]) = 0 := by
    intro i
    have hsp := GlobalTheory.T.mem_span_eigen_of_baseChange_eigen' l (X.Fn l) {s : Ω ≃ₐ[ℚ] Ω // s ∈ Ine (F := ℚ) A ∧ ∀ y ∈ F₀, s y = y} (X.B N l w)
      (fun s => X.galB l s.1) (fun s => (cycZ ℚ Ω l s.1 : ℤ_[l]) ^ (w + 1))
      (fun s => GlobalTheory.KZ.StabGal.galB_mem_B ε X ε.injective hhol N l w hl2 hN hNl hw s.1) (σ i ![1, 0]) (hσ i _) (fun s => by
        obtain ⟨h1, h2⟩ := hF₀ s.1 s.2.1 s.2.2
        have h := hσg i s.1 ![1, 0]
        rw [← h2, ← map_smul]
        refine h.trans (congrArg _ ?_)
        funext k
        fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h1])
    refine (Submodule.span_le (p := LinearMap.ker L)).2 ?_ hsp
    rintro _ ⟨b, hbB, hbe, rfl⟩
    refine eq_zero_of_le (C := C * ‖((l : ℕ) : Qbar l) ^ c‖⁻¹) (c := 0) fun n _ => ?_
    obtain ⟨φ, hφ, -⟩ := GlobalTheory.T.exists_cuspFunctional_oddWeight_oddPrime Ω ε X A N l inferInstance hhol' hl2 hlN (by omega) hlA n w hw b hbB
    have hlc : ((l : ℕ) : Qbar l) ^ c ≠ 0 := pow_ne_zero _ l_ne_zero
    have hp : 0 < ‖((l : ℕ) : Qbar l) ^ c‖ := norm_pos_iff.2 hlc
    have hc1 : 1 ≤ ‖((l : ℕ) : Qbar l) ^ c‖⁻¹ := by
      rw [one_le_inv₀ hp, norm_pow]; exact pow_le_one₀ (norm_nonneg _) norm_l_lt_one.le
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hb 0 (Submodule.zero_mem _))
    have h1 := hL n b hbB φ hφ
    have h2 : ‖(lam (seqN D j φ) : ℂ_[l])‖ ≤ C * ‖((l : ℕ) : Qbar l) ^ c‖⁻¹ * ‖((l : ℕ) : Qbar l) ^ n‖ := by
      rw [PadicComplex.norm_extends, mul_assoc, ← norm_inv, ← norm_mul]
      refine lam_le hC (mul_ne_zero (inv_ne_zero hlc) (pow_ne_zero _ l_ne_zero)) _ fun t => ?_
      have h3 := norm_le_of_cgA hj (hc b hbB (fun s hs hs' => hbe ⟨s, hs, hs'⟩) n φ hφ ((t : ℚ) / D))
      rw [map_zero, sub_zero, map_mul, map_pow, map_natCast, norm_mul] at h3
      rw [norm_mul, norm_inv, le_inv_mul_iff₀ hp]
      exact h3
    have e : L (1 ⊗ₜ[ℤ_[l]] b) = (lam (seqN D j φ) : ℂ_[l]) + -((lam (seqN D j φ) : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] b)) := by
      ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 ?_)
    rw [norm_neg]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC0 hc1) (norm_nonneg _))
  obtain ⟨κ, per, h1, h2⟩ := GlobalTheory.T.line_functional_eq_period_mul_alt l (X.Fn l) (Ω ≃ₐ[ℚ] Ω) (X.B N l w) (X.galB l) (fun s => mat ρ s) L F
    (fun K hK τ => (exists_restrict j τ.toRingEquiv).imp fun s hs => hg K hK τ s hs) m σ hσ hσg hkill
  exact ⟨L, κ, per, hL, hb, h1, h2⟩

theorem exists_bound {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l} (h : FinSupp lam) : ∃ C : ℝ,
    (∀ f : ℕ → Qbar l, (∀ s, ‖f s‖ ≤ 1) → ‖lam f‖ ≤ C) ∧ ((∀ f : ℕ → Qbar l, (∀ s, ‖f s‖ ≤ 1) → ‖lam f‖ ≤ 1) → C ≤ 1) := by
  by_cases hi : ∀ f : ℕ → Qbar l, (∀ s, ‖f s‖ ≤ 1) → ‖lam f‖ ≤ 1
  · exact ⟨1, hi, fun _ => le_rfl⟩
  · obtain ⟨S, hS⟩ := h.exists_sum
    refine ⟨∑ s ∈ S, ‖lam (Pi.single s 1)‖, fun f hf => ?_, fun h => absurd h hi⟩
    rw [hS f]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hf s)

theorem act_sgD_one (X : Tower Ω ε) {N w : ℕ} (hN : N ≠ 0) {b : X.Fn l} (hb : b ∈ X.B N l w) :
    X.act l (sgD N l 1 : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  obtain ⟨⟨h0, h1⟩, h2⟩ := Betti.isDiam_sgD (d := 1) hN (Fact.out : l.Prime).ne_zero (Nat.coprime_one_left N)
  have h3 : (⟨sgD N l 1, h0⟩ : CongruenceSubgroup.Gamma0 N) ∈ CongruenceSubgroup.Gamma1' N := by
    rw [CongruenceSubgroup.Gamma1_mem']
    simpa [en, CongruenceSubgroup.Gamma0Map] using h2
  have h4 : sgD N l 1 ∈ Gam N l :=
    ⟨(CongruenceSubgroup.Gamma1_mem N _).2 ((CongruenceSubgroup.Gamma1_to_Gamma0_mem _).1 h3), h1⟩
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 _ h4
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

end GlobalTheory.LamPr

end

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois
open scoped TensorProduct MatrixGroups Matrix

namespace GlobalTheory.LamPr

end GlobalTheory.LamPr

end

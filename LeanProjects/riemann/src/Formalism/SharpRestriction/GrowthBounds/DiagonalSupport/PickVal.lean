import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PickLem

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

theorem support_diagK_subset {σ Kf : Type} [Field Kf] (g : (σ →₀ ℕ) → Kf) (F : MvPolynomial σ Kf) :
    (diagK g F).support ⊆ F.support := by
  intro mo hmo
  rw [mem_support_iff] at hmo ⊢
  rw [coeff_diagK] at hmo
  exact right_ne_zero_of_mul hmo

section Id

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem value_exact (d : Fin n' → ℕ) (hDig : DigFacts Fr p O hk nL d) (G : MvPolynomial (TV n' (m + 1)) (KK O))
    (hG : HasMultideg G d) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (hrho : ∀ x c, rho (x, c) < lowP Fr p x)
    (hgn : ∀ bn, ((gamNo Fr p nL rho bn : ℚ) : KK O) ≠ 0)
    (e : Module.End (KK O) (MvPolynomial (TL J nL r × Fin K) (KK O)))
    (hsa : ∀ F G, fock (e F) G = fock F (e G)) (nu : TL J nL r × Fin K →₀ ℕ) (cY : KK O)
    (hpol : e (monomial nu 1) ∈ Pol (KK O) K dNo)
    (A : MvPolynomial (TL J nL r × Fin r) (KK O)) (hA : A ∈ Pol (KK O) r dPl) :
    fock G (asm Fr p O hk nL rho A
        (diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)⁻¹) (cY • e (monomial nu 1)))) =
      ((cstOf Fr p nL rho dPl dNo : ℕ) : KK O) * cY * ((expFact nu : ℕ) : KK O) *
        fock (planeCoeff nu (oneT e (levImg Fr p hk nL rho dPl dNo G)))
          (diagK (fun bp => ((gamPl Fr p nL rho bp : ℚ) : KK O)) A) := by
  have hNpol0 : diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)⁻¹) (cY • e (monomial nu 1)) ∈ Pol (KK O) K dNo :=
    diagK_mem_pol _ _ (Submodule.smul_mem _ _ hpol)
  obtain ⟨Nex, hNex⟩ : ∃ Nex, Nex = diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)⁻¹) (cY • e (monomial nu 1)) :=
    ⟨_, rfl⟩
  rw [← hNex]
  have hNpol : Nex ∈ Pol (KK O) K dNo := by rw [hNex]; exact hNpol0
  rw [(hDig G hG).1 rho dPl dNo hrho A hA Nex hNpol]
  have hback : diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)) Nex = cY • e (monomial nu 1) := by
    ext bn
    rw [coeff_diagK, hNex, coeff_diagK, ← mul_assoc, mul_inv_cancel₀ (hgn bn), one_mul]
  have hin : ∀ bp : TL J nL r × Fin r →₀ ℕ,
      ∑ bn ∈ Nex.support, ((levImg Fr p hk nL rho dPl dNo G).coeff bp).coeff bn *
            (((gamPl Fr p nL rho bp : ℚ) : KK O) * A.coeff bp * ((expFact bp : ℕ) : KK O)) *
            (((gamNo Fr p nL rho bn : ℚ) : KK O) * Nex.coeff bn * ((expFact bn : ℕ) : KK O)) =
        (((gamPl Fr p nL rho bp : ℚ) : KK O) * A.coeff bp * ((expFact bp : ℕ) : KK O)) *
          (cY * ((e ((levImg Fr p hk nL rho dPl dNo G).coeff bp)).coeff nu * ((expFact nu : ℕ) : KK O))) := by
    intro bp
    have h1 : fock ((levImg Fr p hk nL rho dPl dNo G).coeff bp)
        (diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)) Nex) =
        cY * ((e ((levImg Fr p hk nL rho dPl dNo G).coeff bp)).coeff nu * ((expFact nu : ℕ) : KK O)) := by
      rw [hback, fock_smul_right, ← hsa, fock_monomial_right]
    rw [← h1, fock_eq_sum _ _ Nex.support (support_diagK_subset _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun bn _ => ?_
    rw [coeff_diagK]; ring
  rw [Finset.sum_congr rfl fun bp _ => hin bp]
  rw [fock_eq_sum _ _ A.support (support_diagK_subset _ _), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun bp _ => ?_
  rw [coeff_planeCoeff, coeff_oneT, coeff_diagK]; ring

theorem asm_add_right (rho : TL J nL r × Fin (r + K) → ℕ) (A : MvPolynomial (TL J nL r × Fin r) (KK O))
    (N N' : MvPolynomial (TL J nL r × Fin K) (KK O)) :
    asm Fr p O hk nL rho A (N + N') = asm Fr p O hk nL rho A N + asm Fr p O hk nL rho A N' := by
  unfold asm
  rw [map_add]; ring

end Id

theorem asm_coefGe' {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)
    (rho : TL J nL r × Fin (r + K) → ℕ) {A : MvPolynomial (TL J nL r × Fin r) (KK O)}
    {N : MvPolynomial (TL J nL r × Fin K) (KK O)} {t : ℝ} (hA : CoefGe p A 0) (hN : CoefGe p N t) :
    CoefGe p (asm Fr p O hk nL rho A N) t := by
  unfold asm
  have h1 : CoefGe p (monomial (labMon Fr hk nL rho) (1 : KK O)) 0 := CoefGe.monomial _ geQ_one
  have h2 : CoefGe p (upPl Fr p O hk nL A) 0 := CoefGe.aeval _ (fun v => CoefGe.X_pow _ _) hA
  have h3 : CoefGe p (upNo Fr p O hk nL N) t := CoefGe.aeval _ (fun v => CoefGe.X_pow _ _) hN
  have h4 := CoefGe.mul (CoefGe.mul h1 h2) h3
  simpa using h4

theorem padicVal_expFact_le (p : ℕ) [hp : Fact p.Prime] {n' k : ℕ} (d : Fin n' → ℕ) (α : Fin n' × Fin k →₀ ℕ)
    (hα : ∀ s, multideg α s = d s) : padicValNat p (expFact α) ≤ padicValNat p (∏ s, (d s).factorial) := by
  have h1 : ∀ s, (d s).factorial = Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) *
      ∏ c : Fin k, (α (s, c)).factorial := by
    intro s
    rw [mul_comm, Nat.multinomial_spec, ← hα s]
    rfl
  have h2 : expFact α = ∏ s : Fin n', ∏ c : Fin k, (α (s, c)).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Fintype.prod_prod_type]
  have h3 : (∏ s, (d s).factorial) = (∏ s : Fin n', Nat.multinomial Finset.univ (fun c : Fin k => α (s, c))) * expFact α := by
    rw [h2, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => h1 s
  have hMn0 : (∏ s : Fin n', Nat.multinomial Finset.univ (fun c : Fin k => α (s, c))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun s _ => (Nat.multinomial_pos _ _).ne'
  have hE0 : expFact α ≠ 0 := by
    rw [h2]
    exact Finset.prod_ne_zero_iff.2 fun s _ => Finset.prod_ne_zero_iff.2 fun c _ => Nat.factorial_ne_zero _
  rw [h3, padicValNat.mul hMn0 hE0]
  omega

end Formalism.MainNotions.Proposition5Numerics

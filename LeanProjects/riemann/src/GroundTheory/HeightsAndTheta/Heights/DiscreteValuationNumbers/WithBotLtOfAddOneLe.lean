import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

namespace AdditivityInDivisor

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem cycEval_add_cycle {n Z₁ Z₂ : Ideal (MRing ι R) → ℤ} (h₁ : (Function.support Z₁).Finite)
    (h₂ : (Function.support Z₂).Finite) : cycEval n (Z₁ + Z₂) = cycEval n Z₁ + cycEval n Z₂ := by
  unfold cycEval
  rw [← finsum_add_distrib (h₁.subset (Function.support_mul_subset_left _ _))
    (h₂.subset (Function.support_mul_subset_left _ _))]
  exact finsum_congr fun W => by simp [add_mul]

theorem cycEval_add_fn {n n₁ n₂ Z : Ideal (MRing ι R) → ℤ} (hZ : (Function.support Z).Finite)
    (h : ∀ W, Z W ≠ 0 → n W = n₁ W + n₂ W) : cycEval n Z = cycEval n₁ Z + cycEval n₂ Z := by
  unfold cycEval
  rw [← finsum_add_distrib (hZ.subset (Function.support_mul_subset_left _ _))
    (hZ.subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun W => ?_
  by_cases hW : Z W = 0
  · simp [hW]
  · rw [h W hW, mul_add]

theorem ratDiv_support_finite {P : Ideal (MRing ι R)} {f g : MRing ι R}
    (hf : (Function.support (divCycle P f)).Finite) (hg : (Function.support (divCycle P g)).Finite) :
    (Function.support (ratDiv P f g)).Finite := by
  refine (hf.union hg).subset fun W hW => ?_
  by_contra h
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
  exact hW (by simp [ratDiv, h.1, h.2])

theorem withBot_lt_of_add_one_le {x : WithBot ℕ∞} {n : ℕ} (hx : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have e : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [e] at hx
      exact absurd (WithBot.coe_le_coe.mp hx) (by simp)
    | coe m =>
      have h1 : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ((n : ℕ) : WithBot ℕ∞) := by simpa using hx
      have h2 : m + 1 ≤ n := by exact_mod_cast h1
      have h3 : ((m : ℕ) : WithBot ℕ∞) < ((n : ℕ) : WithBot ℕ∞) := by exact_mod_cast (show m < n by omega)
      simpa using h3

theorem ratDiv_mul_mul (hmul : DivCycleMul.Statement.{u}) {O : Type u} [CommRing O] [IsNoetherianRing O]
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (hP : P.IsPrime)
    {f₁ g₁ f₂ g₂ : MRing ι O} (hf₁ : f₁ ∉ P) (hf₂ : f₂ ∉ P) (hg₁ : g₁ ∉ P) (hg₂ : g₂ ∉ P) :
    ratDiv P (f₁ * f₂) (g₁ * g₂) = ratDiv P f₁ g₁ + ratDiv P f₂ g₂ := by
  funext W
  simp only [ratDiv, Pi.add_apply, hmul O K ι P f₁ f₂ hP hf₁ hf₂, hmul O K ι P g₁ g₂ hP hg₁ hg₂]
  ring

end AdditivityInDivisor

theorem AdditivityInDivisor.proof (hmul : DivCycleMul.Statement.{u}) (hfin : DivCycleFiniteSupport.Statement.{u})
    (hadd : IntNumAddFirst.Statement.{u}) (hsup : SupSpanMultiHomog.Statement.{u})
    (hmin : MinimalPrimeMultiHomog.Statement.{u}) (hspm : SpecialIdealMultiHomog.Statement.{u})
    (hcor : SpecialIdealCorresp.Statement.{u}) (hqd : SpecialQuotDim.Statement.{u})
    (hdrop : DimStrictDrop.Statement.{u}) : AdditivityInDivisor.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b₁ b₂ f₁ g₁ f₂ g₂ hD₁ hD₂ c s hs hsP hsH L
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have rfin : ∀ (Q : Ideal (MRing ι O)) (x y : MRing ι O), (Function.support (ratDiv Q x y)).Finite :=
    fun Q x y => ratDiv_support_finite (hfin O K ι Q x) (hfin O K ι Q y)
  refine ⟨?_, ?_⟩
  · unfold cutIdentityLeftSide
    rw [ratDiv_mul_mul hmul hPp hD₁.num_not_mem hD₂.num_not_mem hD₁.den_not_mem hD₂.den_not_mem]
    exact cycEval_add_cycle (rfin _ _ _) (rfin _ _ _)
  · unfold cutIdentityRightSide
    refine cycEval_add_fn (hfin O K ι P s) fun W hW => ?_
    obtain ⟨hWp, hPW, -⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
    split_ifs with hϖW
    ·
      have hWmin : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
        unfold divCycle at hW
        split_ifs at hW with h
        · exact h.1
        · exact absurd rfl hW
      have hWh : IsMultiHomogIdeal W :=
        hmin O K ι _ W (hsup O K ι P s c hP.multiProj.multiHomog hs) hWmin
      have hsW : s ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
      have hlt : P < W := lt_of_le_of_ne hPW fun h => hsP (h ▸ hsW)
      have hdim := hdrop (MRing ι O) P W hlt
      rw [hP.dim, ← hqd O ϖ hϖ K ι W hϖW,
        show d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K by ring] at hdim
      exact hadd _ K ι d (specialIdeal W) (hcor O ϖ hϖ K ι P W hWp hϖW).1 (hspm O K ι W hWh)
        (withBot_lt_of_add_one_le hdim) b₁ b₂ L
    ·
      obtain ⟨hV₁, hV₂⟩ := hsH W hW hϖW
      rw [ratDiv_mul_mul hmul hWp hV₁.num_not_mem hV₂.num_not_mem hV₁.den_not_mem hV₂.den_not_mem]
      exact cycEval_add_cycle (rfin _ _ _) (rfin _ _ _)

end GroundTheory.Heights₂.Heights.NumbersDVR

import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SatBorel

theorem heckeVec_satU_borel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ), ∀ h ∈ Hecke ℂ (KU σ n), ∃ (ι : Type) (_ : Fintype ι) (b : ι → GU σ n), (∀ i, IsBorelU (b i)) ∧ (∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (GU σ n) M) (s : M), (∀ k ∈ KU σ n, π k s = s) → heckeVec π (KU σ n) h s = ∑ i, h (b i) • π (b i) s) ∧ ∀ α : Fin (n / 2) → ℂˣ, SatU ϖ q h (fun i => (α i : ℂ)) = ∑ i, h (b i) * ∏ k : Fin (n / 2), ((α k : ℂ) * (q : ℂ) ^ (-((n : ℤ) - 1 - 2 * (k.1 : ℤ)))) ^ ordL ((b i).1.1 (lo n k) (lo n k)) := by
  intro L _ _ _ ϖ σ q hU n h hh
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have hfin := P.finite_support_cosets hK hh.2
  have hI : ∀ c : GU σ n ⧸ KU σ n, ∃ b : GU σ n, IsBorelU b ∧ (b : GU σ n ⧸ KU σ n) = c := by
    intro c
    obtain ⟨b, k, hb, hk, e⟩ := P.fIwasawa_iwasawa σ hU.1 hU.2.1 c.out
    refine ⟨b, hb, ?_⟩
    conv_rhs => rw [← QuotientGroup.out_eq' c, e]
    exact QuotientGroup.eq.2 (by simpa using hk)
  choose s hsB hs using hI
  have hhs : ∀ c, h (s c) = h c.out := by
    intro c
    have hk : (c.out)⁻¹ * s c ∈ KU σ n := QuotientGroup.eq.1 (c.out_eq'.trans (hs c).symm)
    have e : s c = 1 * c.out * ((c.out)⁻¹ * s c) := by group
    rw [e]
    exact hh.1 1 ⟨_, hk⟩ c.out
  have c1 : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (GU σ n) M) (x : M),
      (∀ k ∈ KU σ n, π k x = x) →
      heckeVec π (KU σ n) h x = ∑ i : hfin.toFinset, h (s i.1) • π (s i.1) x := by
    intro M _ _ π x hx
    rw [GlobalTheory.LFun.heckeVec_eq_of_section hh.1 (GlobalTheory.LGrp.mem_fixed.2 hx) s hs,
      finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_, ← Finset.sum_coe_sort]
    intro c hc
    rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq, ← hhs]
    intro h0
    exact hc (by simp [h0])
  refine ⟨hfin.toFinset, inferInstance, fun i => s i.1, fun i => hsB _, c1, fun α => ?_⟩
  obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega)
    (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  have e := congrFun (Final.SatakeInert L ϖ σ q n (n / 2) hU (by omega) (by omega) _
    (fun i => (α i).ne_zero) h hh φ hφ) 1
  have hfix : ∀ k ∈ KU σ n, GlobalTheory.PRep.rightReg ℂ (GU σ n) ℂ k φ = φ := by
    intro k hk
    funext g
    change φ (g * k) = φ g
    simpa [GlobalTheory.LFun.chiDeltaU_one] using hφ 1 g k GlobalTheory.LFun.isBorelU_one hk
  rw [← GlobalTheory.LFun.heckeVec_rightReg hK hh, c1 _ _ φ hfix] at e
  have hχ : ∀ i : hfin.toFinset, φ (s i.1) = ∏ k : Fin (n / 2),
      ((α k : ℂ) * (q : ℂ) ^ (-((n : ℤ) - 1 - 2 * (k.1 : ℤ)))) ^ ordL ((s i.1).1.1 (lo n k) (lo n k)) := by
    intro i
    have := hφ (s i.1) 1 1 (hsB _) (one_mem _)
    simp only [mul_one, h1] at this
    rw [this]
    unfold chiDeltaU
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [dif_pos (by omega), mul_zpow, ← _root_.zpow_mul]
    have hl : lo n k = ⟨k.1, by omega⟩ := rfl
    rw [hl]
    congr 2
    ring
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h1, mul_one] at e
  rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hχ i]
  exact congrArg (h (s i.1) * ·) (congrArg φ (one_mul _))

end GlobalTheory.SatBorel

import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system.PartialZeroIdentity

private theorem lft_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    lft (uni I J) = I := by
  ext i
  simp [lft, uni]

private theorem rgt_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    rgt (uni I J) = J := by
  ext i
  simp [rgt, uni]

private theorem cech_zero {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    {G : Finset ι → Submodule ℂ E} {n : ℤ} {y : Finset ι → E} (hy : y ∈ (cech G).Z n)
    (s : Finset ι) (h : (s.card : ℤ) ≠ n + 1) : y s = 0 := by
  have h1 : y s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then G s else ⊥) := hy.1 s (Set.mem_univ s)
  rw [if_neg (fun h' => h h'.2)] at h1
  simpa using h1

private theorem res_mu {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
    [IsScalarTower ℂ F K] (τ : DR ℂ K →ₗ[K] K) (ρ : F →ₗ[ℂ] ℂ) (e f w : DR ℂ K) :
    resP (DR ℂ K) ρ (muP F K τ (e ⊗ₜ f) w) = trF ℂ τ ρ (e * w) • f := by
  simp [muP, resP, trF]

end UpperTheory.Gal.productCup_of_system.PartialZeroIdentity

open UpperTheory.Gal.productCup_of_system.PartialZeroIdentity in
theorem UpperTheory.Gal.productCup_of_system.zId_of :
    ZAct → RCupTop → KunDec → SysBasic → GoodZ → ZId := by
  intro hZA hRC hKD hSB hGZ F K _ _ _ _ _ _ d x hFC τ hT ρ hR a ha c hc hD
  have htop : top c ∈ (sysZ K x a).mix.Z (d + 2) :=
    (hSB d _ _ (sysZ K x a) (Mi d) n11 (sysZ K x a).mu (d + 2)).2.2.1 c hc
  obtain ⟨m, p, e, f, hk, hB⟩ := hKD (Fin (d + 1)) (DR ℂ K) (DR ℂ K)
    (fun s => omB ℂ K (rB ℂ K (xv x) s) (d - a)) (fun s => omB ℂ K (rB ℂ K (xv x) s) a) d
    (hGZ F K d x hFC (d - a)).2.2 (hGZ F K d x hFC a).2.2 (top c) htop
  refine ⟨m, p, e, f, hk, hB, ?_⟩
  intro q α hα
  have h1 := hZA F K d x hFC τ hT ρ hR a q ha c hc hD α hα
  have h2 := hRC F K d x hFC τ hT ρ hR a q ha _ hB α hα
  have hzero : ∀ k, p k ≠ q → pr K τ ρ (e k) α = 0 := by
    intro k hkq
    simp only [pr, cupPair, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
      LinearMap.proj_apply, LinearMap.mul_apply']
    refine Finset.sum_eq_zero fun j _ => ?_
    have hc1 : ((Finset.univ.filter (· ≤ j)).card : ℤ) = (j : ℤ) + 1 := by
      rw [Finset.filter_ge_eq_Iic, Fin.card_Iic]; push_cast; ring
    have hc2 : ((Finset.univ.filter (j ≤ ·)).card : ℤ) = (d : ℤ) + 1 - j := by
      rw [Finset.filter_le_eq_Ici, Fin.card_Ici]; have := j.2; omega
    by_cases hA : ((Finset.univ.filter (· ≤ j)).card : ℤ) = ((d : ℤ) - p k) + 1
    · have : α (Finset.univ.filter (j ≤ ·)) = 0 := by
        refine cech_zero hα _ ?_
        rw [hc2]; rw [hc1] at hA
        intro h; apply hkq; omega
      simp [this]
    · have : e k (Finset.univ.filter (· ≤ j)) = 0 := cech_zero (hk k).2.1 _ hA
      simp [this]
  have key : ∀ J, resP (DR ℂ K) ρ (∑ i, muP F K τ
      ((∑ k, join (TensorProduct.mk ℂ (DR ℂ K) (DR ℂ K)) (e k) (f k))
        (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·)))) =
      ∑ k ∈ Finset.univ.filter (fun k => p k = q), pr K τ ρ (e k) α • f k J := by
    intro J
    rw [Finset.sum_filter_of_ne (fun k _ hne => ?_)]
    · simp only [Finset.sum_apply, join, lft_uni', rgt_uni', TensorProduct.mk_apply, map_sum,
        LinearMap.sum_apply, res_mu]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [pr, cupPair, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
        LinearMap.proj_apply, LinearMap.mul_apply', Finset.sum_smul]
    · by_contra hpq
      exact hne (by rw [hzero k hpq, zero_smul])
  have hfin := add_mem h1 h2
  convert hfin using 1
  funext J
  simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
  rw [← key J]
  simp only [Finset.sum_apply, map_sub, LinearMap.sub_apply, Finset.sum_sub_distrib, map_sum, LinearMap.sum_apply]
  abel

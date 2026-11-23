import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualWeylHighestWeightSpaceLineField
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory.CoefWtLine

open Formalism.GradedWeylDivisibility

open Classical in

def blkW (ι : Type) (n : ℕ) : ι × Fin n × Fin n → ι → Fin n → ℕ :=
  fun v => Pi.single v.1 (Pi.single v.2.1 1)

theorem weight_blkW {ι : Type} [Fintype ι] {n : ℕ} (m : ι × Fin n × Fin n →₀ ℕ) (τ : ι) (a : Fin n) :
    Finsupp.weight (blkW ι n) m τ a = ∑ s : Fin n, m (τ, a, s) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Finset.sum_apply,
    Fintype.sum_prod_type, Finset.sum_eq_single τ, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [blkW]
  · intro b _ hb
    simp [blkW, hb]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [blkW, hb]
  · simp

open Classical in
theorem blockEmb_hom {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (τ : ι)
    (f : MvPolynomial (Fin n × Fin n) K) (μ : Fin n → ℕ) (hf : IsWeightedHomogeneous (rowW n n) f μ) :
    IsWeightedHomogeneous (blkW ι n) (blockEmb K τ f) (Pi.single τ μ) := by
  intro d hd
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ _ _ hd
  have e := hf hu
  funext τ' a
  rw [weight_blkW]
  by_cases h : τ' = τ
  · subst h
    rw [Pi.single_eq_same, ← e, GlobalTheory.LvT.KerLat.weight_rowW, rowDeg]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact Finsupp.mapDomain_apply (fun x y hxy => (Prod.mk.inj hxy).2) u (a, s)
  · rw [Pi.single_eq_of_ne h]
    refine Finset.sum_eq_zero fun s _ => ?_
    apply Finsupp.mapDomain_notin_range
    rintro ⟨x, hx⟩
    exact h (Prod.mk.inj hx).1.symm

theorem ten_hom {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}
    (f : ι → MvPolynomial (Fin n × Fin n) K) (μ : ι → Fin n → ℕ)
    (hf : ∀ τ, IsWeightedHomogeneous (rowW n n) (f τ) (μ τ)) :
    IsWeightedHomogeneous (blkW ι n) (ten f) μ := by
  classical
  have h := IsWeightedHomogeneous.prod Finset.univ (fun τ => blockEmb K τ (f τ)) _
    (fun τ _ => blockEmb_hom τ (f τ) (μ τ) (hf τ))
  have e : μ = ∑ τ, Pi.single τ (μ τ) := (Finset.univ_sum_single μ).symm
  rw [e]
  exact h

theorem natW_antitone' {n : ℕ} (l : DomWeight n) : Antitone l.natW := fun _ _ h =>
  Int.toNat_le_toNat (sub_le_sub_right (l.anti h) _)

theorem extremal_hom (K : Type) [Field K] {n : ℕ} (l : DomWeight n) :
    IsWeightedHomogeneous (rowW n n) (extremal K n l) l.natW := by
  have h := hwRowWeight K n n le_rfl l.natW (natW_antitone' l)
  have e : (rowNu l.natW : Fin n → ℕ) = l.natW := by
    funext a
    simp [rowNu]
  rwa [e] at h

theorem weight_line : ∀ (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n), (∀ m ∈ (ten fun τ => extremal K n (lam τ) : Pol K ι n).support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) ∧ ∀ G ∈ VV K lam, (∀ m ∈ G.support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) → ∃ c : K, G = c • ten fun τ => extremal K n (lam τ) := by
  intro K _ ι _ n lam
  classical
  refine ⟨fun m hm τ a => ?_, fun G hG hw => ?_⟩
  · have h := ten_hom _ (fun τ => (lam τ).natW) (fun τ => extremal_hom K (lam τ)) (mem_support_iff.1 hm)
    rw [← weight_blkW, h]
  · have hGh : IsWeightedHomogeneous (blkW ι n) G (fun τ => (lam τ).natW) := by
      intro d hd
      funext τ a
      rw [weight_blkW]
      exact hw d (mem_support_iff.2 hd) τ a
    have key : VV K lam ≤ (Submodule.span K {(ten fun τ => extremal K n (lam τ) : Pol K ι n)}).comap
        (weightedHomogeneousComponent (blkW ι n) (fun τ => (lam τ).natW)) := by
      rw [← (bVVfun_spec K lam).2, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have sp := fun τ => (sSBasis K n n (lam τ).natW).choose_spec.1
      have hb : ∀ τ, IsWeightedHomogeneous (rowW n n) (ssB K (lam τ).natW (i τ)) (rowWt (i τ).1) :=
        fun τ => (sp τ).2.2 (i τ)
      have hi : IsWeightedHomogeneous (blkW ι n) (bVVfun K lam i) (fun τ => rowWt (i τ).1) := ten_hom _ _ hb
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      by_cases he : (fun τ => (lam τ).natW) = fun τ => rowWt (i τ).1
      · rw [← he] at hi
        rw [hi.weightedHomogeneousComponent_same]
        have hc : ∀ τ, ∃ c : K, ssB K (lam τ).natW (i τ) = c • extremal K n (lam τ) := fun τ => by
          refine GlobalTheory.Alc.hw_line_field K n _ (natW_antitone' _) _ ?_ ?_
          · rw [← (sp τ).2.1]
            exact Submodule.subset_span ⟨i τ, rfl⟩
          · have := hb τ
            rwa [← congrFun he τ] at this
        choose c hc using hc
        refine Submodule.mem_span_singleton.2 ⟨∏ τ, c τ, ?_⟩
        simp only [bVVfun, ten, hc, map_smul]
        exact (Finset.prod_smul _ _ _).symm
      · rw [hi.weightedHomogeneousComponent_ne _ he]
        exact zero_mem _
    have h := key hG
    rw [Submodule.mem_comap, hGh.weightedHomogeneousComponent_same] at h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
    exact ⟨c, hc.symm⟩

end GlobalTheory.CoefWtLine

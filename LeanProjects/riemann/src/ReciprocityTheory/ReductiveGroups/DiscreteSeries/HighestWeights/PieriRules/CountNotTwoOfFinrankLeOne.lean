import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Finrank
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.TensRepB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.TensHW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.WeylPos

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem count_mem_kSpan_self {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) : x ∈ Formalism.REAL.kSpan ε F x :=
  Submodule.mem_sInf.mpr fun _ hS => hS.1

theorem count_mem_khwSub_iff {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ W) (ν : Fin n → ℝ) (v : W) :
    v ∈ khwSub ε E ν ↔ Formalism.REAL.KHighest ε E ν v := by
  simp only [khwSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero, Formalism.REAL.KHighest,
    Formalism.REAL.IsWeight]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => by simpa using h1 a, fun a b hab he => h2 a b ⟨hab, he⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => by simpa using h1 a, fun a b h => h2 a b h.1 h.2⟩

theorem count_eq_zero_of_orth {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {m : ℕ}
    (A : Fin m → Submodule ℂ V) (htop : (⨆ k, A k) = ⊤) (x : V)
    (h : ∀ k, ∀ z ∈ A k, ⟪x, z⟫_ℂ = 0) : x = 0 := by
  have hle : (⨆ k, A k) ≤ (ℂ ∙ x)ᗮ :=
    iSup_le fun k z hz => (Submodule.mem_orthogonal_singleton_iff_inner_right).mpr (h k z hz)
  rw [htop] at hle
  have hx : x ∈ (ℂ ∙ x)ᗮ := hle Submodule.mem_top
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hx
  exact inner_self_eq_zero.mp hx

theorem count_not_two_of_finrank_le_one {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (S : Submodule ℂ V) [FiniteDimensional ℂ S] (hS : Module.finrank ℂ S ≤ 1) {y z : V} (hy : y ∈ S)
    (hz : z ∈ S) (hy0 : y ≠ 0) (hz0 : z ≠ 0) (hyz : ⟪y, z⟫_ℂ = 0) : False := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hS
  obtain ⟨c, hc⟩ := hv ⟨y, hy⟩
  obtain ⟨d, hd⟩ := hv ⟨z, hz⟩
  have hc' : c • (v : V) = y := by rw [← Submodule.coe_smul, hc]
  have hd' : d • (v : V) = z := by rw [← Submodule.coe_smul, hd]
  have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hc'; exact hy0 hc'.symm
  have hzy : z = (d / c) • y := by
    rw [← hc', ← hd', smul_smul, div_mul_cancel₀ d hc0]
  have hd0 : d / c ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hzy; exact hz0 hzy
  rw [hzy, inner_smul_right] at hyz
  rcases mul_eq_zero.mp hyz with h | h
  · exact hd0 h
  · exact hy0 (inner_self_eq_zero.mp h)

theorem count_finrank_piLp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ι : Type*) [Fintype ι] :
    Module.finrank ℂ (PiLp 2 (fun _ : ι => V)) = Fintype.card ι * Module.finrank ℂ V := by
  rw [(WithLp.linearEquiv 2 ℂ (ι → V)).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, smul_eq_mul]

theorem count_weylK_eq {n : ℕ} {ε : Fin n → Bool} {μ : Fin n → ℝ} (T : KType ε μ) :
    (Module.finrank ℂ T.V : ℝ) = weylK ε μ :=
  kType_finrank T

theorem count_weylK_pos {n : ℕ} {ε : Fin n → Bool} {μ : Fin n → ℝ} (T : KType ε μ) :
    0 < weylK ε μ := by
  rw [← count_weylK_eq T]
  have : Nontrivial T.V := ⟨⟨T.w, 0, KType.w_ne_zero T⟩⟩
  exact_mod_cast Module.finrank_pos

theorem pieriCount_of_st (hc : CompRedStatement) (hr : KRepRelStatement) (ht : TensRepStatement)
    (hh : TensHWStatement) (hw : WeylPosStatement) : PieriCountStatement := by
  intro n ε Λ T ι _ _ ρ dρ γ hρc hdρ hrelM hdiag hinj hsum hvan
  obtain ⟨τ, D, hτc, hD, hunits⟩ := ht n ε Λ T ι ρ dρ hρc hdρ
  let R : KRep ε :=
    { V := PiLp 2 (fun _ : ι => T.V), τ := τ, cont := hτc, dτ := D, hasDeriv := hD }
  have hRu : R.units = tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) := by
    funext a b
    exact hunits a b
  obtain ⟨hrelR, hunitR⟩ := hr n ε R
  obtain ⟨m, x, μ, hx, horth, htop, hfin, -, hT⟩ := hc n ε R
  rw [hRu] at hrelR hunitR hx horth htop hfin
  have hTH := hh T.V n ε (kunits T) Λ T.w ι (fun a b => dρ (Matrix.single a b 1)) γ
    (KType.kRel T) (KType.kUnit T) (KType.kHighest_w T) (KType.kSpan_eq_top T) hrelM hdiag

  have hdimk : ∀ k, (Module.finrank ℂ (Formalism.REAL.kSpan ε
      (tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1))) (x k)) : ℝ) = weylK ε (μ k) := by
    intro k
    obtain ⟨Tk, -, hfr, -⟩ := hT k
    rw [hRu] at hfr
    rw [← hfr]
    exact count_weylK_eq Tk
  have hpos : ∀ k, 0 < weylK ε (μ k) := fun k => by
    obtain ⟨Tk, -⟩ := hT k
    exact count_weylK_pos Tk

  choose idx hidx using fun k => hTH.1 (μ k) (x k) (hx k).1 (hx k).2
  have hcard1 : ∀ i, Nat.card {j : ι // Λ + γ i = Λ + γ j} = 1 := by
    intro i
    rw [Nat.card_eq_one_iff_exists]
    exact ⟨⟨i, rfl⟩, fun j => Subtype.ext (hinj (add_left_cancel j.2)).symm⟩

  have hidx_inj : Function.Injective idx := by
    intro k k' hkk'
    by_contra hne
    obtain ⟨hfd, hle⟩ := hTH.2 (Λ + γ (idx k))
    rw [hcard1] at hle
    have hk : x k ∈ khwSub ε (tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)))
        (Λ + γ (idx k)) := by
      rw [count_mem_khwSub_iff, ← hidx k]
      exact (hx k).2
    have hk' : x k' ∈ khwSub ε (tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)))
        (Λ + γ (idx k)) := by
      rw [count_mem_khwSub_iff, hkk', ← hidx k']
      exact (hx k').2
    exact count_not_two_of_finrank_le_one _ hle hk hk' (hx k).1 (hx k').1
      (horth k k' hne _ (count_mem_kSpan_self _ _ _) _ (count_mem_kSpan_self _ _ _))

  have hpiece : ∀ (ν : Fin n → ℝ) (y : PiLp 2 (fun _ : ι => T.V)), y ≠ 0 →
      Formalism.REAL.KHighest ε (tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1))) ν y →
      ∃ k, μ k = ν := by
    intro ν y hy0 hy
    by_contra hno
    push Not at hno
    apply hy0
    refine count_eq_zero_of_orth _ htop y fun k z hz => ?_
    exact Formalism.REAL.kOrth _ n ε _ ν (μ k) y (x k) hrelR hunitR hy (hx k).2 (hno k).symm y
      (count_mem_kSpan_self _ _ _) z hz
  have hnn : ∀ i, 0 ≤ weylK ε (Λ + γ i) := by
    intro i
    by_cases hd : KDom ε (Λ + γ i)
    · exact (hw n ε _ hd).le
    · rw [hvan i hd]
  refine ⟨?_, ?_⟩
  · intro i0 hd0
    by_contra hno
    push Not at hno
    have hne : ∀ k, idx k ≠ i0 := fun k h =>
      hno (x k) (hx k).1 (by rw [← h, ← hidx k]; exact (hx k).2)
    have hdimR : (Module.finrank ℂ (PiLp 2 (fun _ : ι => T.V)) : ℝ) =
        (Fintype.card ι : ℝ) * weylK ε Λ := by
      rw [count_finrank_piLp, Nat.cast_mul, count_weylK_eq T]
    have hdimR' : (Module.finrank ℂ (PiLp 2 (fun _ : ι => T.V)) : ℝ) =
        ∑ k, weylK ε (Λ + γ (idx k)) := by
      have hfin' : Module.finrank ℂ (PiLp 2 (fun _ : ι => T.V)) = ∑ k, Module.finrank ℂ
          (Formalism.REAL.kSpan ε (tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1))) (x k)) := hfin
      rw [hfin', Nat.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hdimk, hidx]
    have hsub : univ.image idx ⊆ univ.erase i0 := by
      intro i hi
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_erase.mpr ⟨hne k, Finset.mem_univ _⟩
    have h1 : ∑ k, weylK ε (Λ + γ (idx k)) = ∑ i ∈ univ.image idx, weylK ε (Λ + γ i) :=
      by rw [Finset.sum_image fun a _ b _ h => hidx_inj h]
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnn i)
    have h3 := Finset.sum_erase_add univ (fun i => weylK ε (Λ + γ i)) (Finset.mem_univ i0)
    have h4 := hw n ε _ hd0
    linarith
  · intro ν y hy0 hy
    obtain ⟨i, hi⟩ := hTH.1 ν y hy0 hy
    obtain ⟨k, hk⟩ := hpiece ν y hy0 hy
    refine ⟨i, hi, ?_⟩
    by_contra hnd
    have hp := hpos k
    rw [hk, hi, hvan i hnd] at hp
    exact lt_irrefl (0 : ℝ) hp

theorem pieriCount_of (hc : CompRedStatement) (hr : KRepRelStatement) : PieriCountStatement :=
  pieriCount_of_st hc hr tensRep tensHW weylPos

end ReciprocityTheory.ChartRestriction.DS.HW

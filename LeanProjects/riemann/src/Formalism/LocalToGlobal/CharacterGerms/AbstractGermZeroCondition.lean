import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
import Formalism.LocalToGlobal.CharacterGerms.WipDworkInvG
import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.EqSingleOfDegreeEqOne

noncomputable section
open Classical

namespace Formalism.L2.FormalSeriesBounds
namespace AbstractGermZero

open Formalism.IncomingBounds

variable {C : Type} [Field C] (V : VF C)

def eG' {I : Fin 2 → Type} (g : Fin 2) : I g ↪ WV I := ⟨fun x => ⟨g, x⟩, sigma_mk_injective⟩

def AbstractGermZeroCondition : Prop :=
  ∀ (I : Fin 2 → Type) [∀ g, Fintype (I g)] (t t₂ φ φ₂ : ∀ g, I g → MvPowerSeries (I g) C),
    (∀ g c, MvPowerSeries.constantCoeff (t g c) = 0) → (∀ g c, MvPowerSeries.constantCoeff (t₂ g c) = 0) →
    (∀ g k, MvPowerSeries.constantCoeff (φ g k) = 0) → (∀ g k, IntS V (φ g k)) →
    (∀ g, V.v (Matrix.of fun k c : I g => MvPowerSeries.coeff (Finsupp.single c 1) (φ g k)).det = 0) →
    (∀ g k, MvPowerSeries.constantCoeff (φ₂ g k) = 0) → (∀ g k, IntS V (φ₂ g k)) →
    (∀ g, V.v (Matrix.of fun k c : I g => MvPowerSeries.coeff (Finsupp.single c 1) (φ₂ g k)).det = 0) →
    (∀ g k, MvPowerSeries.subst (t g) (φ g k) = MvPowerSeries.subst (t₂ g) (φ₂ g k)) →
    IntGerm V t = IntGerm V t₂

theorem intS_iff_alt {σ : Type} (F : MvPowerSeries σ C) : IntS V F ↔ AltInv.IntS V.v F := by
  simp only [IntS, AltInv.IntS, AltInv.IntC]
  exact Iff.rfl

theorem one_group {σ : Type} [Fintype σ] (t t₂ φ φ₂ : σ → MvPowerSeries σ C)
    (ht0₂ : ∀ c, MvPowerSeries.constantCoeff (t₂ c) = 0) (ht0 : ∀ c, MvPowerSeries.constantCoeff (t c) = 0)
    (hφ0 : ∀ k, MvPowerSeries.constantCoeff (φ k) = 0) (hφ : ∀ k, IntS V (φ k))
    (hL : V.v (Matrix.of fun k c : σ => MvPowerSeries.coeff (Finsupp.single c 1) (φ k)).det = 0)
    (hφ0₂ : ∀ k, MvPowerSeries.constantCoeff (φ₂ k) = 0) (hφ₂ : ∀ k, IntS V (φ₂ k))
    (heq : ∀ k, MvPowerSeries.subst t (φ k) = MvPowerSeries.subst t₂ (φ₂ k)) :
    ∃ h : σ → MvPowerSeries σ C, (∀ c, MvPowerSeries.constantCoeff (h c) = 0) ∧ (∀ c, IntS V (h c)) ∧
      ∀ c, t c = MvPowerSeries.subst t₂ (h c) := by
  classical

  set L : Matrix σ σ C := Matrix.of fun k c : σ => MvPowerSeries.coeff (Finsupp.single c 1) (φ k)
    with hLdef
  have hdet : IsUnit L.det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0] at hL
    simp at hL
  set N : Matrix σ σ C := L⁻¹ with hNdef
  have hLN : L * N = 1 := Matrix.mul_nonsing_inv L hdet
  have hNL : N * L = 1 := Matrix.nonsing_inv_mul L hdet

  have comb : ∀ {M : Type} [AddCommGroup M] [Module C M] (A B : Matrix σ σ C), A * B = 1 →
      ∀ (X : σ → M) (i : σ), ∑ j, A i j • ∑ k, B j k • X k = X i := by
    intro M _ _ A B hAB X i
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have hrow : ∀ k, ∑ j, A i j * B j k = (1 : Matrix σ σ C) i k := fun k => by
      rw [← hAB, Matrix.mul_apply]
    simp only [hrow, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hcoeff : ∀ (ψ : σ → MvPowerSeries σ C) j μ,
      MvPowerSeries.coeff μ (∑ k, N j k • ψ k) = ∑ k, N j k * MvPowerSeries.coeff μ (ψ k) := by
    intro ψ j μ
    simp only [map_sum, MvPowerSeries.coeff_smul]
  have hcc : ∀ (ψ : σ → MvPowerSeries σ C), (∀ k, MvPowerSeries.constantCoeff (ψ k) = 0) →
      ∀ j, MvPowerSeries.constantCoeff (∑ k, N j k • ψ k) = 0 := by
    intro ψ hψ j
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hcoeff]
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hψ]

  have hid : Formalism.FG.IsIdMod2 (fun j => ∑ k, N j k • φ k) := by
    refine ⟨hcc φ hφ0, fun j i => ?_⟩
    show MvPowerSeries.coeff (Finsupp.single i 1) (∑ k, N j k • φ k) = _
    rw [hcoeff]
    have hNLji : ∑ k, N j k * MvPowerSeries.coeff (Finsupp.single i 1) (φ k) = (N * L) j i := by
      rw [Matrix.mul_apply]
      rfl
    rw [hNLji, hNL, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [if_neg (Ne.symm hij), if_neg hij]
  obtain ⟨h, hh0, hhs⟩ := Formalism.FG.solve_exists_vector C σ σ (fun j => ∑ k, N j k • φ k)
    (fun j => ∑ k, N j k • φ₂ k) hid (hcc φ₂ hφ0₂)
  have hsub_h : MvPowerSeries.HasSubst h := MvPowerSeries.hasSubst_of_constantCoeff_zero hh0
  have hlin : ∀ (a : σ → MvPowerSeries σ C), MvPowerSeries.HasSubst a → ∀ j,
      MvPowerSeries.subst a (∑ k, N j k • φ k) = ∑ k, N j k • MvPowerSeries.subst a (φ k) := by
    intro a ha j
    rw [← MvPowerSeries.coe_substAlgHom ha, map_sum, MvPowerSeries.coe_substAlgHom ha]
    exact Finset.sum_congr rfl fun k _ => MvPowerSeries.subst_smul ha _ _

  have hφh : ∀ k, MvPowerSeries.subst h (φ k) = φ₂ k := by
    have h1 : ∀ j, ∑ k, N j k • MvPowerSeries.subst h (φ k) = ∑ k, N j k • φ₂ k := by
      intro j
      rw [← hlin h hsub_h]
      exact hhs j
    intro i
    have e1 := comb L N hLN (fun k => MvPowerSeries.subst h (φ k)) i
    have e2 := comb L N hLN φ₂ i
    simp only [h1] at e1
    exact e1.symm.trans e2
  have hhI : ∀ c, IntS V (h c) := by
    have hint := AltInv.intS_invG φ h φ₂ hφ0 (fun k => (intS_iff_alt V _).mp (hφ k)) hL hh0
      (fun k => (intS_iff_alt V _).mp (hφ₂ k)) hφh
    exact fun c => (intS_iff_alt V _).mpr (hint c)

  have hsub_t : MvPowerSeries.HasSubst t := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  have hsub_t₂ : MvPowerSeries.HasSubst t₂ := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0₂
  set t' : σ → MvPowerSeries σ C := fun c => MvPowerSeries.subst t₂ (h c) with ht'
  have hL1t : ∀ i, Formalism.FG.SolveVAux.Low 1 (t i) :=
    fun i => (Formalism.FG.SolveVAux.low_one_iff _).mpr (ht0 i)
  have hL1t' : ∀ i, Formalism.FG.SolveVAux.Low 1 (t' i) := fun i =>
    Formalism.FG.SolveVAux.low_subst (fun j => (Formalism.FG.SolveVAux.low_one_iff _).mpr (ht0₂ j))
      ((Formalism.FG.SolveVAux.low_one_iff _).mpr (hh0 i))
  have hsub_t' : MvPowerSeries.HasSubst t' :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => (Formalism.FG.SolveVAux.low_one_iff _).mp (hL1t' i)
  have hφt : ∀ k, MvPowerSeries.subst t (φ k) = MvPowerSeries.subst t' (φ k) := by
    intro k
    rw [heq k, ← hφh k]
    exact MvPowerSeries.subst_comp_subst_apply hsub_h hsub_t₂ (φ k)
  have hg2 : ∀ j, Formalism.FG.SolveVAux.Low 2 ((∑ k, N j k • φ k) - MvPowerSeries.X j) := by
    intro j
    unfold Formalism.FG.SolveVAux.Low
    intro d hd
    rw [map_sub]
    rcases (by omega : d.degree = 0 ∨ d.degree = 1) with hd0 | hd1
    · have hd00 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hd0
      subst hd00
      simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ0]
    · obtain ⟨i, rfl⟩ := Formalism.FG.SolveVAux.degree_eq_one d hd1
      rw [show MvPowerSeries.coeff (Finsupp.single i 1) (∑ k, N j k • φ k) =
        if i = j then 1 else 0 from hid.2 j i, MvPowerSeries.coeff_X]
      by_cases hij : i = j
      · subst hij
        simp
      · rw [if_neg hij, if_neg]
        · simp
        · intro h'
          exact hij (Finsupp.single_left_injective one_ne_zero h')
  have hlow : ∀ (M : ℕ) (i : σ), Formalism.FG.SolveVAux.Low M (t i - t' i) := by
    intro M
    induction M with
    | zero => exact fun i => Formalism.FG.SolveVAux.low_zero _
    | succ M ih =>
      intro i
      have hsplit : ∀ a : σ → MvPowerSeries σ C, MvPowerSeries.HasSubst a →
          MvPowerSeries.subst a (∑ k, N i k • φ k) =
            a i + MvPowerSeries.subst a ((∑ k, N i k • φ k) - MvPowerSeries.X i) := by
        intro a ha
        rw [MvPowerSeries.subst_sub ha, MvPowerSeries.subst_X ha]
        abel
      have hfeq : MvPowerSeries.subst t (∑ k, N i k • φ k) =
          MvPowerSeries.subst t' (∑ k, N i k • φ k) := by
        rw [hlin t hsub_t, hlin t' hsub_t']
        simp only [hφt]
      have h1 := hsplit t hsub_t
      have h2 := hsplit t' hsub_t'
      rw [hfeq] at h1
      have hdiff : t i - t' i =
          -(MvPowerSeries.subst t ((∑ k, N i k • φ k) - MvPowerSeries.X i) -
            MvPowerSeries.subst t' ((∑ k, N i k • φ k) - MvPowerSeries.X i)) := by
        linear_combination h2 - h1
      rw [hdiff]
      exact Formalism.FG.SolveVAux.low_neg (Formalism.FG.SolveVAux.low_subst_sub hL1t hL1t' ih (hg2 i))
  have htt : t = t' := by
    funext i
    ext d
    have hd := hlow (d.degree + 1) i d (Nat.lt_succ_self _)
    rw [map_sub] at hd
    exact sub_eq_zero.mp hd
  exact ⟨h, hh0, hhI, fun c => congrFun htt c⟩

private theorem cc_subst_lemma {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]

theorem upG_subst {I : Fin 2 → Type} [∀ g, Fintype (I g)] (t : ∀ g, I g → MvPowerSeries (I g) C)
    (ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0) (g : Fin 2) (γ : MvPowerSeries (I g) C) :
    MvPowerSeries.subst (fun w : WV I => upG w.1 (t w.1 w.2)) (upG g γ) = upG g (MvPowerSeries.subst (t g) γ) := by
  have hX : MvPowerSeries.HasSubst
      (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp)
  have hT : MvPowerSeries.HasSubst (fun w : WV I => upG w.1 (t w.1 w.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by
      unfold upG
      rw [cc_subst_lemma _ (fun x => by simp)]
      exact ht0 w.1 w.2)
  have ht : MvPowerSeries.HasSubst (t g) := MvPowerSeries.hasSubst_of_constantCoeff_zero (ht0 g)
  have e1 : upG g γ = MvPowerSeries.subst
      (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) γ := rfl
  have e2 : upG g (MvPowerSeries.subst (t g) γ) = MvPowerSeries.subst
      (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) (MvPowerSeries.subst (t g) γ) := rfl
  rw [e1, e2, MvPowerSeries.subst_comp_subst_apply hX hT, MvPowerSeries.subst_comp_subst_apply ht hX]
  congr 1
  funext x
  rw [MvPowerSeries.subst_X hT]
  try rfl

theorem germ_sub {I : Fin 2 → Type} [∀ g, Fintype (I g)] (t t₂ h : ∀ g, I g → MvPowerSeries (I g) C)
    (ht0₂ : ∀ g c, MvPowerSeries.constantCoeff (t₂ g c) = 0)
    (hh0 : ∀ g c, MvPowerSeries.constantCoeff (h g c) = 0) (hhI : ∀ g c, IntS V (h g c))
    (hth : ∀ g c, t g c = MvPowerSeries.subst (t₂ g) (h g c)) :
    IntGerm V t ⊆ IntGerm V t₂ := by
  rintro F ⟨γ, hγ, rfl⟩
  have hX : ∀ (g : Fin 2) (x : I g),
      AltInv.IntS V.v (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C) := fun g x => by
    intro μ
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact AltInv.intC_one (v := V.v)
    · exact AltInv.intC_zero (v := V.v)
  have hH0 : ∀ w : WV I, MvPowerSeries.constantCoeff (upG w.1 (h w.1 w.2)) = 0 := fun w => by
    unfold upG
    rw [cc_subst_lemma _ (fun x => by simp)]
    exact hh0 w.1 w.2
  have hHI : ∀ w : WV I, IntS V (upG w.1 (h w.1 w.2)) := fun w => by
    rw [intS_iff_alt]
    exact AltInv.intS_subst (v := V.v) (fun x => by simp) (fun x => hX w.1 x)
      ((intS_iff_alt V _).mp (hhI w.1 w.2))
  have hH : MvPowerSeries.HasSubst (fun w : WV I => upG w.1 (h w.1 w.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hH0
  have hT₂ : MvPowerSeries.HasSubst (fun w : WV I => upG w.1 (t₂ w.1 w.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by
      unfold upG
      rw [cc_subst_lemma _ (fun x => by simp)]
      exact ht0₂ w.1 w.2)
  refine ⟨MvPowerSeries.subst (fun w : WV I => upG w.1 (h w.1 w.2)) γ, ?_, ?_⟩
  · exact AltInv.intS_subst (v := V.v) hH0 (fun w => (intS_iff_alt V _).mp (hHI w)) ((intS_iff_alt V γ).mp hγ)
  · rw [MvPowerSeries.subst_comp_subst_apply hH hT₂]
    congr 1
    funext w
    rw [upG_subst t₂ ht0₂, ← hth]

theorem abstract_germ_zero : AbstractGermZeroCondition V := by
  intro I _ t t₂ φ φ₂ ht0 ht0₂ hφ0 hφ hL hφ0₂ hφ₂ hL₂ heq
  choose h hh0 hhI hth using fun g => one_group V (t g) (t₂ g) (φ g) (φ₂ g) (ht0₂ g) (ht0 g) (hφ0 g) (hφ g)
    (hL g) (hφ0₂ g) (hφ₂ g) (heq g)
  choose h' hh0' hhI' hth' using fun g => one_group V (t₂ g) (t g) (φ₂ g) (φ g) (ht0 g) (ht0₂ g) (hφ0₂ g)
    (hφ₂ g) (hL₂ g) (hφ0 g) (hφ g) (fun k => (heq g k).symm)
  exact Set.Subset.antisymm (germ_sub V t t₂ h ht0₂ hh0 hhI hth) (germ_sub V t₂ t h' ht0 hh0' hhI' hth')

end AbstractGermZero
end Formalism.L2.FormalSeriesBounds

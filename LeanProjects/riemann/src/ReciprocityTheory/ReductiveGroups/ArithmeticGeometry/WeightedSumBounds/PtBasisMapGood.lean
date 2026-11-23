import Mathlib
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtRescaleGood

namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

open Classical

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def ptOn (a : Fin d) (ga : Fin d → PowerSeries C) : Fin d → MvPowerSeries (Fin d) C :=
  fun b => PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (ga b)

def ptBasisMap (G : LogFGL v d) (γ : Fin d → Fin d → PowerSeries C) :
    Fin d → MvPowerSeries (Fin d) C :=
  ptSumL G (List.ofFn fun a => ptOn a (γ a))

theorem ptOn_hs (a : Fin d) : HasSubst (fun _ : Unit => (X a : MvPowerSeries (Fin d) C)) := MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X a

theorem ptOn_good (a : Fin d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga) :
    PTGood v (ptOn a ga) := by
  intro b
  refine ⟨PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X a) _ (h b).1, ?_⟩
  show ∀ α, coeff α (ptOn a ga b) ∈ ptIntSub v
  intro e
  rw [ptOn, PowerSeries.coeff_subst_single]
  split_ifs
  · exact (ptIsIntV_iff _).mp ((h b).2 _)
  · exact (ptIntSub v).zero_mem

theorem ptOn_lin (a : Fin d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga) (b s : Fin d) :
    coeff (Finsupp.single s 1) (ptOn a ga b) = if s = a then tangent ga b else 0 := by
  rw [ptOn, PowerSeries.coeff_subst_single]
  by_cases hs : s = a
  · subst hs
    simp [tangent]
  · simp [Finsupp.single_apply, hs, Ne.symm hs]

theorem ptOn_lg (G : LogFGL v d) (a : Fin d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga)
    (b : Fin d) :
    subst (ptOn a ga) (G.lg b) = PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve ga b) := by
  have hga : HasSubst ga := MvPowerSeries.hasSubst_of_constantCoeff_zero fun c => (h c).1
  show subst (ptOn a ga) (G.lg b) = PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (subst ga (G.lg b))
  rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hga (ptOn_hs a)]
  rfl

theorem ptBasisMap_good (G : LogFGL v d) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) : PTGood v (ptBasisMap G γ) := by
  unfold ptBasisMap
  refine ptSumL_good G _ fun x hx => ?_
  obtain ⟨a, rfl⟩ : ∃ a, ptOn a (γ a) = x := by simpa [List.mem_ofFn] using hx
  exact ptOn_good a (hγ a)

theorem ptBasisMap_lin (G : LogFGL v d) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (b s : Fin d) :
    coeff (Finsupp.single s 1) (ptBasisMap G γ b) = tangent (γ s) b := by
  have hc : ∀ x ∈ List.ofFn (fun a => ptOn a (γ a)), ∀ c, constantCoeff (x c) = 0 := by
    intro x hx c
    obtain ⟨a, rfl⟩ : ∃ a, ptOn a (γ a) = x := by simpa [List.mem_ofFn] using hx
    exact (ptOn_good a (hγ a) c).1
  rw [ptBasisMap, ptSumL_lin G _ hc b s, List.map_ofFn, List.sum_ofFn]
  simp [Function.comp_def, ptOn_lin _ (hγ _)]

theorem ptBasisMap_lg (G : LogFGL v d) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (b : Fin d) :
    subst (ptBasisMap G γ) (G.lg b) =
      ∑ a, PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve (γ a) b) := by
  have hc : ∀ x ∈ List.ofFn (fun a => ptOn a (γ a)), ∀ c, constantCoeff (x c) = 0 := by
    intro x hx c
    obtain ⟨a, rfl⟩ : ∃ a, ptOn a (γ a) = x := by simpa [List.mem_ofFn] using hx
    exact (ptOn_good a (hγ a) c).1
  rw [ptBasisMap, ptSumL_lg G _ hc b, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl fun a _ => ptOn_lg G a (hγ a) b

theorem pt_inv_int {M : Matrix (Fin d) (Fin d) C} (hM : ∀ i j, M i j ∈ ptIntSub v)
    (hdet : v M.det = 0) : IsUnit M.det ∧ ∀ i j, M⁻¹ i j ∈ ptIntSub v := by
  have hdet0 : M.det ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hdet
    exact WithTop.top_ne_coe hdet
  refine ⟨isUnit_iff_ne_zero.mpr hdet0, fun i j => ?_⟩
  obtain ⟨M', rfl⟩ : ∃ M' : Matrix (Fin d) (Fin d) (ptIntSub v), M = M'.map (ptIntSub v).subtype :=
    ⟨fun i j => ⟨M i j, hM i j⟩, by ext i j; rfl⟩
  have hadj : (M'.map (ptIntSub v).subtype).adjugate i j = (ptIntSub v).subtype (M'.adjugate i j) :=
    (congrArg (fun N : Matrix (Fin d) (Fin d) C => N i j) (RingHom.map_adjugate (ptIntSub v).subtype M')).symm
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, hadj, Ring.inverse_eq_inv']
  refine (ptIntSub v).mul_mem ?_ (M'.adjugate i j).2
  show 0 ≤ v (M'.map (ptIntSub v).subtype).det⁻¹
  rw [AddValuation.map_inv, hdet, neg_zero]

theorem ptBasisMap_inv (G : LogFGL v d) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (hdet : v (Matrix.det (Matrix.of fun a b => tangent (γ a) b)) = 0) :
    ∃ Ψ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (Ψ a)) ∧
      (∀ a, constantCoeff (Ψ a) = 0) ∧
      (∀ a, subst Ψ (ptBasisMap G γ a) = X a) ∧ (∀ a, subst (ptBasisMap G γ) (Ψ a) = X a) := by
  have hΦ : PTGood v (ptBasisMap G γ) := ptBasisMap_good G hγ
  have hΦs : HasSubst (ptBasisMap G γ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => (hΦ s).1
  let M : Matrix (Fin d) (Fin d) C := Matrix.of fun a b => tangent (γ a) b
  have hMint : ∀ i j, M i j ∈ ptIntSub v := fun i j => (ptIsIntV_iff _).mp (((hγ i) j).2 1)
  obtain ⟨hdu, hNint⟩ := pt_inv_int hMint hdet
  have hNM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdu
  have hMN : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdu
  let K : Fin d → MvPowerSeries (Fin d) C := fun b => ptBasisMap G γ b - ∑ a, M a b • X a
  have hlin : ∀ b s, coeff (Finsupp.single s 1) (ptBasisMap G γ b) = M s b :=
    fun b s => ptBasisMap_lin G hγ b s
  have hlow : ∀ b (α : Fin d →₀ ℕ), α.degree ≤ 1 → coeff α (K b) = 0 :=
    fun b => pt_low_of_lin (hΦ b).1 (fun a => M a b) (hlin b)
  have hK : ∀ b (α : Fin d →₀ ℕ), coeff α (K b) ≠ 0 → 2 ≤ α.degree ∨
      ∀ x y : Fin d → MvPowerSeries (Fin d) C, PTGood v x → PTGood v y → ∀ s ∈ α.support, x s = y s := by
    intro b α h
    left
    by_contra h'
    push_neg at h'
    exact h (hlow b α (by omega))
  have hKi : ∀ b, K b ∈ ptIntSer v (Fin d) := fun b =>
    Subring.sub_mem _ (hΦ b).2 (Subring.sum_mem _ fun a _ => ptIntSer_smul (hMint a b) (ptIntSer_X a))
  have hK0 : ∀ b, constantCoeff (K b) = 0 := fun b => by simp [K, (hΦ b).1]
  have hA0 : ∀ x : Fin d → MvPowerSeries (Fin d) C, PTGood v x → ∀ s, constantCoeff (x s) = 0 :=
    fun x hx s => (hx s).1
  have hAi : ∀ x : Fin d → MvPowerSeries (Fin d) C, PTGood v x → ∀ s, x s ∈ ptIntSer v (Fin d) :=
    fun x hx s => (hx s).2
  have hAag : ∀ k (x y : Fin d → MvPowerSeries (Fin d) C), PTGood v x → PTGood v y → PTAgree k x y →
      ∀ s (e : Fin d →₀ ℕ), e.degree < k → coeff e (x s) = coeff e (y s) :=
    fun k x y _ _ hxy s e he => hxy s e he
  have hfX : PTGood v (fun b => (X b : MvPowerSeries (Fin d) C)) := fun b => ⟨by simp, ptIntSer_X b⟩
  have hsub : ∀ x : Fin d → MvPowerSeries (Fin d) C, PTGood v x → ∀ b,
      subst x (ptBasisMap G γ b) = ∑ a, M a b • x a + subst x (K b) := fun x hx b =>
    pt_subst_lin_split (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => (hx s).1) _ (fun a => M a b)
  obtain ⟨Ψ, ⟨hΨg, hΨeq⟩, -⟩ := pt_solve (M := M) (N := M⁻¹) (A := fun x => x) (K := K)
    (f := fun b => (X b : MvPowerSeries (Fin d) C)) hNM hMN hNint hfX hA0 hAi hAag hK hKi hK0
  have hΨs : HasSubst Ψ := MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => (hΨg s).1
  have hright : ∀ b, subst Ψ (ptBasisMap G γ b) = X b := fun b => (hsub Ψ hΨg b).trans (hΨeq b)
  obtain ⟨y0, -, huniq⟩ := pt_solve (M := M) (N := M⁻¹) (A := fun x => x) (K := K)
    (f := ptBasisMap G γ) hNM hMN hNint hΦ hA0 hAi hAag hK hKi hK0
  let y : Fin d → MvPowerSeries (Fin d) C := fun a => subst (ptBasisMap G γ) (Ψ a)
  have hyg : PTGood v y := fun a =>
    ⟨MvPowerSeries.constantCoeff_subst_eq_zero hΦs (fun s => (hΦ s).1) (hΨg a).1,
      ptIntSer_subst hΦs (fun s => (hΦ s).2) (hΨg a).2⟩
  have hy : y = y0 := huniq y ⟨hyg, fun b => by
    rw [← hsub y hyg b]
    show subst (fun a => subst (ptBasisMap G γ) (Ψ a)) (ptBasisMap G γ b) = ptBasisMap G γ b
    rw [← MvPowerSeries.subst_comp_subst_apply hΨs hΦs, hright b, MvPowerSeries.subst_X hΦs]⟩
  have hX : (fun b => (X b : MvPowerSeries (Fin d) C)) = y0 := huniq _ ⟨hfX, fun b => by
    rw [← hsub _ hfX b, MvPowerSeries.subst_self]
    rfl⟩
  refine ⟨Ψ, fun a => (ptMvIsInt_iff _).mpr (hΨg a).2, fun a => (hΨg a).1, hright, fun a => ?_⟩
  exact congrFun (hy.trans hX.symm) a

end

end ReciprocityTheory.ChartRestriction.G.Sh

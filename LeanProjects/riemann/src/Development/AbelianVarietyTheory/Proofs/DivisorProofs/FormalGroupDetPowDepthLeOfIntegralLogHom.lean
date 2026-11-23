import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsExpEqOfSubstLg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst

set_option autoImplicit false

noncomputable section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory.DepthMono

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

def linSub {d d' : ℕ} (M : Matrix (Fin d') (Fin d) C) : Fin d' → MvPowerSeries (Fin d) C :=
  fun b => ∑ a, M b a • (X a : MvPowerSeries (Fin d) C)

theorem constantCoeff_linSub {d d' : ℕ} (M : Matrix (Fin d') (Fin d) C) (b : Fin d') :
    constantCoeff (linSub M b) = 0 := by
  simp [linSub]

theorem subst_expOf_hom {d d' : ℕ} {G : LogFGL v d} {G' : LogFGL v d'}
    {φ : Fin d' → MvPowerSeries (Fin d) C} {M : Matrix (Fin d') (Fin d) C} (hφ : IsIntHom G G' φ M)
    (c : Fin d') : subst (expOf G) (φ c) = subst (linSub M) (expOf G' c) := by
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero (isExp_expOf G).1
  have hE' : HasSubst (expOf G') := hasSubst_of_constantCoeff_zero (isExp_expOf G').1
  have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ.1
  have hL : HasSubst (linSub M) := hasSubst_of_constantCoeff_zero (constantCoeff_linSub M)
  have hlg' : HasSubst G'.lg := hasSubst_of_constantCoeff_zero G'.lg_const
  set ψ : Fin d' → MvPowerSeries (Fin d) C := fun c => subst (expOf G) (φ c) with hψ
  set ρ : Fin d' → MvPowerSeries (Fin d) C := fun c => subst (linSub M) (expOf G' c) with hρ
  have hψ0 : ∀ c, constantCoeff (ψ c) = 0 := fun c =>
    constantCoeff_subst_eq_zero hE (isExp_expOf G).1 (hφ.1 c)
  have hρ0 : ∀ c, constantCoeff (ρ c) = 0 := fun c =>
    constantCoeff_subst_eq_zero hL (constantCoeff_linSub M) ((isExp_expOf G').1 c)
  have hψs : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  have hρs : HasSubst ρ := hasSubst_of_constantCoeff_zero hρ0
  have key : ∀ b, subst ψ (G'.lg b) = subst ρ (G'.lg b) := by
    intro b
    have h1 : subst ψ (G'.lg b) = subst (expOf G) (subst φ (G'.lg b)) :=
      (subst_comp_subst_apply hφs hE (G'.lg b)).symm
    have h2 : subst ρ (G'.lg b) = subst (linSub M) (subst (expOf G') (G'.lg b)) :=
      (subst_comp_subst_apply hE' hL (G'.lg b)).symm
    rw [h1, h2, hφ.2.2, (isExp_expOf G').2, subst_sum_smul hE, subst_X hL]
    simp only [(isExp_expOf G).2, linSub]
  have inj : ∀ c, ψ c = subst (fun b => subst ψ (G'.lg b)) (expOf G' c) ∧
      ρ c = subst (fun b => subst ρ (G'.lg b)) (expOf G' c) := by
    intro c
    constructor
    · rw [← subst_comp_subst_apply hlg' hψs, subst_lg_expOf, subst_X hψs]
    · rw [← subst_comp_subst_apply hlg' hρs, subst_lg_expOf, subst_X hρs]
  show ψ c = ρ c
  rw [(inj c).1, (inj c).2, funext key]

theorem subst_exp_hom {τ : Type} {d d' : ℕ} {G : LogFGL v d} {G' : LogFGL v d'}
    {φ : Fin d' → MvPowerSeries (Fin d) C} {M : Matrix (Fin d') (Fin d) C} (hφ : IsIntHom G G' φ M)
    {L : Fin d → MvPowerSeries τ C} (hL0 : ∀ e, constantCoeff (L e) = 0) (c : Fin d') :
    subst (fun e => (subst L (expOf G e) : MvPowerSeries τ C)) (φ c) =
      (subst (fun b => ∑ a, M b a • L a) (expOf G' c) : MvPowerSeries τ C) := by
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero (isExp_expOf G).1
  have hM : HasSubst (linSub M) := hasSubst_of_constantCoeff_zero (constantCoeff_linSub M)
  have hL : HasSubst L := hasSubst_of_constantCoeff_zero hL0
  rw [← subst_comp_subst_apply hE hL, subst_expOf_hom hφ, subst_comp_subst_apply hM hL]
  congr 1
  funext b
  rw [linSub, subst_sum_smul hL]
  simp only [subst_X hL]

theorem detDepth_le_of_isIntHom : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)),
    ∀ (i d d' k : ℕ) (G : LogFGL v d) (G' : LogFGL v d') (φ : Fin d' → MvPowerSeries (Fin d) C)
      (M : Matrix (Fin d') (Fin d) C), IsIntHom G G' φ M → ∀ u : Fin i → Fin d → C,
      detDepth G u k ≤ detDepth G' (fun a => M.mulVec (u a)) k := by
  intro C _ _ v i d d' k G G' φ M hφ u
  have hX : ∀ b : Fin i, HasSubst
      (fun e : Fin d => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) := fun b =>
    hasSubst_of_constantCoeff_zero fun e => by simp
  let Φ : (Σ _ : Fin i, Fin d') → MvPowerSeries (Σ _ : Fin i, Fin d) C := fun x =>
    subst (fun e : Fin d => (X ⟨x.1, e⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (φ x.2)
  have hΦ : HasSubst Φ := hasSubst_of_constantCoeff_zero fun x =>
    constantCoeff_subst_eq_zero (hX x.1) (fun e => by simp) (hφ.1 x.2)
  have hΦi : ∀ x, MvIsInt v (Φ x) := fun x =>
    ptIntSer_subst (v := v) (hX x.1) (fun e => ptIntSer_X _) (hφ.2.1 x.2)
  have hL0 : ∀ (b : Fin i) (e : Fin d), constantCoeff
      (∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) = 0 := fun b e => by simp
  have hA : HasSubst (expAlong (fun _ : Fin i => G) (fun _ => u)) :=
    hasSubst_of_constantCoeff_zero fun x =>
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (hL0 x.1)) (hL0 x.1)
        ((isExp_expOf G).1 x.2)
  have hcol : (fun x => subst (expAlong (fun _ : Fin i => G) (fun _ => u)) (Φ x)) =
      expAlong (fun _ : Fin i => G') (fun _ a => M.mulVec (u a)) := by
    funext x
    simp only [Φ]
    rw [subst_comp_subst_apply (hX x.1) hA]
    simp only [subst_X hA, expAlong]
    rw [subst_exp_hom hφ (hL0 x.1)]
    congr 1
    funext b
    simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  refine le_iInf fun f => iInf_le_of_le ⟨subst Φ f.1, ptIntSer_subst (v := v) hΦ hΦi f.2⟩ (le_of_eq ?_)
  simp only
  rw [subst_comp_subst_apply hΦ hA, hcol]

end GlobalTheory.DepthMono

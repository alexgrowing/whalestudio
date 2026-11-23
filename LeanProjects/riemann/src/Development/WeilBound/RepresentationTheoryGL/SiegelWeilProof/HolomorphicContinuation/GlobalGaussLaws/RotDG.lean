import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IsSchwartzSmul

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.VacF

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC
  PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacE

variable {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
  {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
  {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}

theorem cpos {l : D.what₂.Tau → ℝ} {τ : D.what₂.Tau} (hl0 : l τ ≠ 0) : 0 < cLoc l τ := by
  unfold cLoc; have := abs_pos.2 hl0; positivity

theorem tabs {l : D.what₂.Tau → ℝ} {τ : D.what₂.Tau} : |tLoc l τ| = cLoc l τ := by
  unfold tLoc cLoc; rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

theorem rot_DG (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) (hl0 : l τ ≠ 0) (hN : LawN) (hNb : LawNbar) (hLM : LocMul)
    (hGZ : GZSch) (L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ))
    (hL : IsLocFact ω τ fr ι L) (e : ℤ)
    (hlev : ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∀ f, IsSch f → L y f = levF e a f)
    (φ : Fin n → ℝ) (hφ : ∀ j, 0 < Real.cos (φ j)) (K : ℂ) :
    L (mkG (kth φ) (inK_kth φ).1) (DG K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (K * ∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ)))
        (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
  have hc : 0 < cLoc l τ := cpos hl0
  have hta : |tLoc l τ| = cLoc l τ := tabs
  have ht2 : (tLoc l τ) ^ 2 = (cLoc l τ) ^ 2 := by rw [← hta, sq_abs]
  have hσ : ∀ a, (VacC.sigR ε a) ^ 2 = 1 := by intro a; unfold VacC.sigR; split_ifs <;> norm_num
  have hX1 : (dR fun j => Real.tan (φ j))ᴴ = dR fun j => Real.tan (φ j) := dR_conjTranspose _
  have hX2 : (dR fun j => -(Real.sin (φ j) * Real.cos (φ j)))ᴴ = dR fun j => -(Real.sin (φ j) * Real.cos (φ j)) :=
    dR_conjTranspose _
  have hDd : IsUnit (dR fun j => (Real.cos (φ j))⁻¹).det := by
    rw [isUnit_iff_ne_zero, dR, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun j _ => by
      have := (hφ j).ne'; exact_mod_cast inv_ne_zero this
  set g1 := mkG (nU (dR fun j => Real.tan (φ j))) (inG_nU _ hX1) with hg1
  set g2 := mkG (nbar (dR fun j => -(Real.sin (φ j) * Real.cos (φ j)))) (inG_nbar _ hX2) with hg2
  set g3 := mkG (mM (dR fun j => (Real.cos (φ j))⁻¹)) (inG_mM _ hDd) with hg3
  have hk : mkG (kth φ) (inK_kth φ).1 = g1 * g2 * g3 := by
    apply Subtype.ext; apply Units.ext
    exact kth_decomp φ (fun j => (hφ j).ne')
  have hf0 : IsSch (DG (n := n) K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) := isSch_DG hGZ ε (tLoc l τ) (cLoc l τ) hc hta K
  rw [hk, hLM D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL (g1 * g2) g3 _ hf0,
    hLM D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL g1 g2 _ (hL.1 g3 _ hf0)]
  have h3 : L g3 (DG (n := n) K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (n := n) (K * (∏ j, (((Real.cos (φ j))⁻¹ : ℝ) : ℂ)) ^ V.rank)
        (fun _ j => ((cLoc l τ : ℝ) : ℂ) * ((((Real.cos (φ j))⁻¹ : ℝ) : ℂ) ^ 2)) := by
    rw [hlev g3 _ hDd rfl _ hf0]
    exact levF_diag e (fun j => (Real.cos (φ j))⁻¹) (fun j => inv_pos.2 (hφ j)) K _
  have hf3 := hL.1 g3 _ hf0
  rw [h3] at hf3 ⊢
  set K1 : ℂ := K * (∏ j, (((Real.cos (φ j))⁻¹ : ℝ) : ℂ)) ^ V.rank with hK1
  set γ1 : Fin V.rank → Fin n → ℂ := fun _ j => ((cLoc l τ : ℝ) : ℂ) * ((((Real.cos (φ j))⁻¹ : ℝ) : ℂ) ^ 2) with hγ1
  have hre1 : ∀ a j, 0 < (γ1 a j).re := by
    intro a j
    rw [hγ1]; simp only
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    have := inv_pos.2 (hφ j); positivity
  set γ2 : Fin V.rank → Fin n → ℂ := fun a j => ((-tLoc l τ : ℝ) : ℂ) ^ 2 * (((VacC.sigR ε a : ℝ) : ℂ) ^ 2) / γ1 a j -
    Complex.I * (tLoc l τ : ℂ) * ((VacC.sigR ε a : ℝ) : ℂ) * ((Real.sin (φ j) * Real.cos (φ j) : ℝ) : ℂ) with hγ2
  have hX2' : -(dR fun j => -(Real.sin (φ j) * Real.cos (φ j))) = dR fun j => Real.sin (φ j) * Real.cos (φ j) := by
    rw [dR_neg]; congr 1; funext j; ring
  have hin : (fun v => chN ε (tLoc l τ) (-(dR fun j => -(Real.sin (φ j) * Real.cos (φ j)))) v *
      ftLoc ε (-tLoc l τ) (DG K1 γ1) v) = DG (K1 * ∏ a, ∏ j, ((Real.pi : ℂ) / γ1 a j)) γ2 := by
    funext v
    rw [ftLoc_eq, ftG_DG _ _ _ _ hre1, hX2']
    exact chN_DG ε (tLoc l τ) (fun j => Real.sin (φ j) * Real.cos (φ j)) _ _ v
  have hre2 : ∀ a j, 0 < (γ2 a j).re := by
    intro a j
    have e : γ2 a j = ((((-tLoc l τ) ^ 2 * (VacC.sigR ε a) ^ 2 / (cLoc l τ * ((Real.cos (φ j))⁻¹) ^ 2)) : ℝ) : ℂ) -
        Complex.I * (((tLoc l τ * VacC.sigR ε a * (Real.sin (φ j) * Real.cos (φ j))) : ℝ) : ℂ) := by
      rw [hγ2, hγ1]; push_cast; ring
    rw [e, Complex.sub_re, Complex.ofReal_re, Complex.re_mul_ofReal, Complex.I_re, zero_mul, sub_zero, hσ a, mul_one, neg_sq]
    have htne : tLoc l τ ≠ 0 := by intro h0; rw [h0, abs_zero] at hta; linarith
    have := inv_pos.2 (hφ j)
    positivity
  set K2 : ℂ := K1 * ∏ a, ∏ j, ((Real.pi : ℂ) / γ1 a j) with hK2
  set γ3 : Fin V.rank → Fin n → ℂ := fun a j => ((tLoc l τ : ℝ) : ℂ) ^ 2 * (((VacC.sigR ε a : ℝ) : ℂ) ^ 2) / γ2 a j with hγ3
  set C0 : ℂ := ((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ (2 * V.rank * n) with hC0
  have h2 : (fun u => C0 * ftLoc ε (tLoc l τ) (DG K2 γ2) u) = DG (C0 * (K2 * ∏ a, ∏ j, ((Real.pi : ℂ) / γ2 a j))) γ3 := by
    funext u
    rw [ftLoc_eq, ftG_DG _ _ _ _ hre2]
    unfold DG
    ring
  have hf2 := hL.1 g2 _ hf3
  rw [hNb D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL g2 _ hX2 rfl _ hf3, hin, h2] at hf2
  rw [hNb D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL g2 _ hX2 rfl _ hf3, hin, h2]
  rw [hN D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL g1 _ hX1 rfl _ hf2]
  funext u
  refine (chN_DG ε (tLoc l τ) (fun j => Real.tan (φ j)) _ _ u).trans ?_
  have hγ4 : (fun a j => γ3 a j - Complex.I * (tLoc l τ : ℂ) * ((VacC.sigR ε a : ℝ) : ℂ) * ((Real.tan (φ j) : ℝ) : ℂ)) =
      fun _ _ => ((cLoc l τ : ℝ) : ℂ) := by
    funext a j
    rw [hγ3, hγ2, hγ1]
    simp only
    rw [Real.tan_eq_sin_div_cos]
    exact coord_gamma (cLoc l τ) (tLoc l τ) (VacC.sigR ε a) (Real.cos (φ j)) (Real.sin (φ j)) hc ht2 (hσ a) (hφ j)
      (Real.sin_sq_add_cos_sq _)
  have hK : C0 * (K2 * ∏ a, ∏ j, ((Real.pi : ℂ) / γ2 a j)) =
      K * ∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ)) := by
    have p1 : (∏ j, (((Real.cos (φ j))⁻¹ : ℝ) : ℂ)) ^ V.rank = ∏ _a : Fin V.rank, ∏ j, (((Real.cos (φ j))⁻¹ : ℝ) : ℂ) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have p2 : ((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ (2 * V.rank * n) =
        ∏ _a : Fin V.rank, ∏ _j : Fin n, (((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ 2) := by
      rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.card_univ, Fintype.card_fin,
        ← pow_mul, ← pow_mul]
      ring_nf
    have hc1 : ∀ a j, (((Real.cos (φ j))⁻¹ : ℝ) : ℂ) * ((Real.pi : ℂ) / γ1 a j) * ((Real.pi : ℂ) / γ2 a j) *
        (((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ 2) =
        (Real.cos (φ j) : ℂ) + Complex.I * (rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ) := by
      intro a j
      rw [hγ2, hγ1]
      simp only
      rw [coord_const (cLoc l τ) (tLoc l τ) (VacC.sigR ε a) (Real.cos (φ j)) (Real.sin (φ j)) hc ht2 (hσ a) (hφ j)
        (Real.sin_sq_add_cos_sq _), rhoT_eq (tLoc l τ) (cLoc l τ) hta hc ε a]
      push_cast
      ring
    rw [hC0, hK2, hK1, p1, p2, ← Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun j _ => hc1 a j))]
    simp only [Finset.prod_mul_distrib]
    ring
  rw [hγ4, hK]

end PositivityTheory.Rg.Sw.Glob.VacF

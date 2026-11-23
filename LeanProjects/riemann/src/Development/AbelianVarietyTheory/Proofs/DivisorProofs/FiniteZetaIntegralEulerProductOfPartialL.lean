import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAdjointScalarParts

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow.ZetaProd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem prod_fin_getD_list (f : ℂˣ → ℂ) : ∀ l : List ℂˣ, ∏ a : Fin l.length, f (l.getD a 1) = (l.map f).prod
  | [] => by simp
  | b :: l => by
    rw [List.length_cons, Fin.prod_univ_succ]
    simp [prod_fin_getD_list f l]

theorem prod_fin_getD (m : Multiset ℂˣ) {n : ℕ} (hn : m.card = n) (f : ℂˣ → ℂ) :
    ∏ a : Fin n, f (m.toList.getD a 1) = (m.map f).prod := by
  have hl : m.toList.length = n := (Multiset.length_toList m).trans hn
  subst hl
  rw [prod_fin_getD_list]
  conv_rhs => rw [← Multiset.coe_toList m]
  rw [Multiset.map_coe, Multiset.prod_coe]

variable {D : D7}

open Classical in

def zetaParams (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (B : GlobalTheory.LFun.Fam D.host.E) (cμ : (AE D)ˣ →* Circle) :
    HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ := fun w a =>
  if OffS D S w then
    (((B w).toList.getD a 1 : ℂˣ) : ℂ) * ((((GlobalTheory.LFun.val cμ)⁻¹ w : ℂˣ)) : ℂ) * GlobalTheory.LFun.npow w (-((1 + (D.R.t : ℂ)) / 2))
  else 0

theorem re_neg_half : (-((1 + (D.R.t : ℂ)) / 2)).re = -((1 + (D.R.t : ℝ)) / 2) := by
  rw [show -((1 + (D.R.t : ℂ)) / 2) = ((-((1 + (D.R.t : ℝ)) / 2) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

theorem norm_zetaParams_le {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {B : GlobalTheory.LFun.Fam D.host.E} (cμ : (AE D)ˣ →* Circle)
    (hcard : ∀ w, OffS D S w → (B w).card = D.R.r)
    (hb : ∀ w, OffS D S w → ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (a : Fin D.R.r) :
    ‖zetaParams S B cμ w a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2 - (1 + (D.R.t : ℝ)) / 2) := by
  unfold zetaParams
  split_ifs with hw
  · have ha : (a : ℕ) < (B w).toList.length := by rw [Multiset.length_toList, hcard w hw]; exact a.2
    have hβ : (B w).toList.getD a 1 ∈ B w := by
      rw [List.getD_eq_getElem _ _ ha]
      exact Multiset.mem_toList.1 (List.getElem_mem ha)
    have hN : (0 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by
      have := two_le_absNorm w
      linarith
    rw [norm_mul, norm_mul, Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv, GlobalTheory.LFun.norm_val, inv_one, mul_one,
      GlobalTheory.LFun.norm_npow, re_neg_half, sub_eq_add_neg, Real.rpow_add hN]
    exact mul_le_mul_of_nonneg_right (hb w hw _ hβ) (Real.rpow_nonneg hN.le _)
  · rw [norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem eulerOff_zetaParams {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {B : GlobalTheory.LFun.Fam D.host.E} (cμ : (AE D)ˣ →* Circle)
    (hcard : ∀ w, OffS D S w → (B w).card = D.R.r)
    (hb : ∀ w, OffS D S w → ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)) :
    eulerOff D S (zetaParams S B cμ) = GlobalTheory.LFun.LSD D S B cμ ((1 + (D.R.t : ℂ)) / 2) := by
  set x := zetaParams S B cμ with hxdef
  have hx := norm_zetaParams_le cμ hcard hb
  obtain ⟨h1, h2, -⟩ := sum_bound (OffS D S) (κ := Fin D.R.r) (fun a => ‖x a.1.1 a.2‖) (fun _ => norm_nonneg _) fun a => by
    refine (hx _ _).trans ?_
    have ht : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast D.R.rank_add_five_le
    have := two_le_absNorm a.1.1
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
  have hm : Multipliable fun p : {w // OffS D S w} × Fin D.R.r => (1 - x p.1.1 p.2)⁻¹ := by
    have := multipliable_one_add_of_summable (f := fun p : {w // OffS D S w} × Fin D.R.r => (1 - x p.1.1 p.2)⁻¹ - 1)
      (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) (h2.mul_left 2))
    · simpa using this
    · have hx2 : ‖x p.1.1 p.2‖ ≤ 1 / 2 := h1 p
      have h3 : 1 / 2 ≤ ‖1 - x p.1.1 p.2‖ := by
        have := norm_sub_norm_le (1 : ℂ) (x p.1.1 p.2)
        rw [norm_one] at this
        linarith
      have hne : 1 - x p.1.1 p.2 ≠ 0 := fun h => by rw [h, norm_zero] at h3; linarith
      have e : (1 - x p.1.1 p.2)⁻¹ - 1 = x p.1.1 p.2 * (1 - x p.1.1 p.2)⁻¹ := by
        field_simp
        ring
      have h4 : ‖1 - x p.1.1 p.2‖⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) two_pos]
        linarith
      rw [e, norm_mul, norm_inv]
      nlinarith [norm_nonneg (x p.1.1 p.2)]
  have hp := hm.hasProd.prod_fiberwise fun b => hasProd_fintype _
  rw [eulerOff, ← hp.tprod_eq]
  show _ = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F))))
    (GlobalTheory.LFun.twist B (GlobalTheory.LFun.val cμ)⁻¹) ((1 + (D.R.t : ℂ)) / 2)
  rw [GlobalTheory.LFun.eulerProd]
  let e : {w // OffS D S w} ≃ {w // w ∉ GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F)))} :=
    Equiv.subtypeEquivRight fun w => (GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents.offS_iff S w).trans (by simp [GlobalTheory.LFun.above])
  rw [← e.tprod_eq]
  refine tprod_congr fun w => ?_
  show _ = GlobalTheory.LFun.locL _ w.1 _
  rw [GlobalTheory.LFun.locL_twist, ← prod_fin_getD (B w.1) (hcard w.1 w.2)]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [hxdef, zetaParams, if_pos w.2]

end GlobalTheory.LowRow.ZetaProd

namespace GlobalTheory.LowRow

theorem finiteZetaC_of_finiteZetaL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    FiniteZetaL R F → FiniteZetaC R F := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hZ i t σ s P cμ cη m ω BW f₀ f c io hd μ 𝓧 hμ ev hne
  obtain ⟨B, hsys, hb, -, hsum⟩ := hZ i t σ s P cμ cη m ω BW f₀ f c io hd μ 𝓧 hμ ev hne
  have hcard : ∀ w, OffS D (finS R t) w → (B w).card = D.R.r := fun w hw => by
    have hv : w.under (𝓞 D.host.F) ∉ ((finS R t : Finset _) : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
      simpa using (GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents.offS_iff _ w).1 hw
    rcases hsys _ hv w rfl with ⟨-, h, -⟩ | ⟨-, τ, ϖ, α, -, -, h, -⟩
    · exact h
    · rw [h]
      exact GlobalTheory.LGrp.card_bcParam _ α
  refine ⟨ZetaProd.zetaParams (finS R t) B cμ, ZetaProd.norm_zetaParams_le cμ hcard hb, fun U₁ h₁ U₂ h₂ v₁ v₂ => ?_⟩
  rw [ZetaProd.eulerOff_zetaParams cμ hcard hb]
  exact hsum U₁ h₁ U₂ h₂ v₁ v₂

end GlobalTheory.LowRow

end

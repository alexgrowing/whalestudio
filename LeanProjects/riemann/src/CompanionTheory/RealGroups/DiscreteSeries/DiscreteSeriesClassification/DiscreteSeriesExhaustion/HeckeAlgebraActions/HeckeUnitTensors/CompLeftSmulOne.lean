import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeUnitTensors.ContOfFnProd

noncomputable section

open Finset

namespace CompanionTheory.RgExh.Hk.UnitPf

open Formalism.REAL (qdet qminor Tm GlRel)
open Formalism.QuantumDeterminants (capP)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor)
open CompanionTheory.RgExh

variable {m : ℕ} (X : GMod (m + 1)) (χ : Fin (m + 1) → ℂ) (s : Fin (m + 1))

def omg : ℂ := cn (m + 1) - χ s

def kap : ℂ := ∏ t ∈ univ.erase s, (χ t - χ s)

def Pr : Module.End ℂ (Fin (m + 1) → X.V) := (kap χ s)⁻¹ • qdet (tensE X) (omg χ s)

variable {X χ s}

theorem qdet_scal (hS : ScalChar X χ) (u : ℂ) :
    qdet X.E u = capP χ (u - cn (m + 1)) • (1 : Module.End ℂ X.V) := by
  have := hS (u - cn (m + 1))
  have e : u - cn (m + 1) + ((↑(m + 1) : ℂ) - 1) / 2 = u := by rw [cn]; ring
  rwa [e] at this

theorem capelliPoly_root : capP χ (-(χ s)) = 0 :=
  Finset.prod_eq_zero (mem_univ s) (by ring)

theorem capelliPoly_eq_mul_prod_erase (u : ℂ) :
    capP χ u = (u + χ s) * ∏ t ∈ univ.erase s, (u + χ t) :=
  (Finset.mul_prod_erase univ (fun t => u + χ t) (mem_univ s)).symm

theorem qdet_omg (hS : ScalChar X χ) : qdet X.E (omg χ s) = 0 := by
  rw [qdet_scal hS, omg, show cn (m + 1) - χ s - cn (m + 1) = -χ s by ring, capelliPoly_root, zero_smul]

theorem compLeft_zero' : (0 : Module.End ℂ X.V).compLeft (Fin (m + 1)) = 0 := by
  ext f d; simp

theorem ct_omg (hS : ScalChar X χ) : qdet (tensE X) (omg χ s) = minorOp X (omg χ s - 1) := by
  rw [GlobalTheory.T.HeckeRankOne m X, qdet_omg hS, compLeft_zero', zero_add]

theorem om_ct (hS : ScalChar X χ) (f : Fin (m + 1) → X.V) :
    om X (qdet (tensE X) (omg χ s) f) = (χ s - cn (m + 1)) • qdet (tensE X) (omg χ s) f := by
  have h := LinearMap.congr_fun (GlobalTheory.T.OmegaMinor m X (omg χ s)) f
  rw [qdet_omg hS, compLeft_zero'] at h
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.zero_apply] at h
  rw [ct_omg hS]
  have h2 : om X (minorOp X (omg χ s - 1) f) = -(omg χ s • minorOp X (omg χ s - 1) f) := eq_neg_of_add_eq_zero_right h
  rw [h2, omg, ← neg_smul]
  congr 1; ring

theorem compLeft_smul_one (c : ℂ) (g : Fin (m + 1) → X.V) :
    (c • (1 : Module.End ℂ X.V)).compLeft (Fin (m + 1)) g = c • g := by
  funext d; simp

theorem ct_on_step (hS : ScalChar X χ) (f : Fin (m + 1) → X.V) (hf : om X f = (χ s - cn (m + 1)) • f) :
    qdet (tensE X) (omg χ s) f = kap χ s • f := by
  set a : ℂ := χ s - cn (m + 1) with ha
  set q : ℂ → ℂ := fun u => ∏ t ∈ univ.erase s, (u - cn (m + 1) + χ t) with hq
  have key : ∀ u : ℂ, u ≠ -a → qdet (tensE X) u f = ((u + 1 + a) * q u) • f := by
    intro u hu
    have h := LinearMap.congr_fun (GlobalTheory.CompanionTheory.RgExh.qdetTens (m + 1) X u) f
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, hf] at h
    rw [← add_smul, map_smul, qdet_scal hS, ← add_smul, LinearMap.map_smul, compLeft_smul_one,
      capelliPoly_eq_mul_prod_erase (s := s)] at h
    have hua : u + a ≠ 0 := fun h0 => hu (eq_neg_of_add_eq_zero_left h0)
    have e : u - cn (m + 1) + χ s = u + a := by rw [ha]; ring
    rw [e, smul_smul] at h
    have h3 : (u + a) • qdet (tensE X) u f = (u + a) • (((u + 1 + a) * q u) • f) := by
      rw [h, smul_smul]; congr 1; simp only [hq]; ring
    exact smul_right_injective _ hua h3
  have hcont : ∀ ℓ : Module.Dual ℂ (Fin (m + 1) → X.V),
      ℓ (qdet (tensE X) (omg χ s) f) = kap χ s * ℓ f := by
    intro ℓ
    have hg : Continuous (fun u : ℂ => ℓ (qdet (tensE X) u f) - (u + 1 + a) * q u * ℓ f) := by
      refine (cont_qdet (tensE X) ℓ f).sub (Continuous.mul (Continuous.mul (by fun_prop) ?_) continuous_const)
      exact continuous_finset_prod _ fun t _ => by fun_prop
    have h0 := eq_zero_of_off hg (-a) fun u hu => by rw [key u hu, map_smul, smul_eq_mul]; ring
    have e1 : omg χ s = -a := by rw [omg, ha]; ring
    have e2 : q (-a) = kap χ s := by
      simp only [hq, kap]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [ha]; ring
    rw [e1]
    have : -a + 1 + a = 1 := by ring
    rw [this, one_mul, e2] at h0
    exact sub_eq_zero.1 h0
  have : qdet (tensE X) (omg χ s) f - kap χ s • f = 0 := by
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
    rw [map_sub, map_smul, hcont ℓ, smul_eq_mul, sub_self]
  exact sub_eq_zero.1 this

theorem kap_ne (hsimp : ∀ r, r ≠ s → χ r ≠ χ s) : kap χ s ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun t ht => sub_ne_zero.2 (hsimp t (Finset.ne_of_mem_erase ht))

theorem Pr_step (hS : ScalChar X χ) (hsimp : ∀ r, r ≠ s → χ r ≠ χ s) (f : Fin (m + 1) → X.V)
    (hf : om X f = (χ s - cn (m + 1)) • f) : Pr X χ s f = f := by
  rw [Pr, LinearMap.smul_apply, ct_on_step hS f hf, smul_smul, inv_mul_cancel₀ (kap_ne hsimp), one_smul]

theorem om_Pr (hS : ScalChar X χ) (f : Fin (m + 1) → X.V) :
    om X (Pr X χ s f) = (χ s - cn (m + 1)) • Pr X χ s f := by
  rw [Pr, LinearMap.smul_apply, map_smul, om_ct hS, smul_comm]

theorem Pr_om (f : Fin (m + 1) → X.V) : Pr X χ s (om X f) = om X (Pr X χ s f) := by
  have hc := GlobalTheory.CompanionTheory.RgExh.commute_qdet_of (tensE X) (om X) (fun a b => commute_om X a b) (omg χ s)
  simp only [Pr, LinearMap.smul_apply, map_smul]
  congr 1
  exact LinearMap.congr_fun hc.eq f

theorem Pr_tensE (a b : Fin (m + 1)) (f : Fin (m + 1) → X.V) :
    Pr X χ s (tensE X a b f) = tensE X a b (Pr X χ s f) := by
  have hc := Formalism.REAL.qDetCentral (Module.End ℂ (Fin (m + 1) → X.V)) (m + 1) (tensE X) (glRel_tensE X) (omg χ s) a b
  simp only [Pr, LinearMap.smul_apply, map_smul]
  congr 1
  exact LinearMap.congr_fun hc f

theorem ptr_Pr (hS : ScalChar X χ) (v : X.V) :
    ∑ c : Fin (m + 1), Pr X χ s (Pi.single c v) c = ((kap χ s)⁻¹ * -capP χ (-χ s - 1)) • v := by
  have e : ∀ c : Fin (m + 1), Pr X χ s (Pi.single c v) c =
      (kap χ s)⁻¹ • cminor X.E c.succAbove c.succAbove (omg χ s - 1) v := by
    intro c
    rw [Pr, LinearMap.smul_apply, ct_omg hS, Pi.smul_apply]
    congr 1
    show ∑ b : Fin (m + 1), ((-1 : ℂ) ^ ((c : ℕ) + (b : ℕ))) • cminor X.E c.succAbove b.succAbove (omg χ s - 1)
      ((Pi.single c v : Fin (m + 1) → X.V) b) = _
    rw [Finset.sum_eq_single c]
    · rw [Pi.single_eq_same, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero, smul_zero]
    · intro h; exact absurd (mem_univ c) h
  simp only [e, ← Finset.smul_sum]
  have hp := GlobalTheory.T.PrincipalSum m X.V X.E X.gl (omg χ s)
  rw [← LinearMap.sum_apply, hp, LinearMap.sub_apply, qdet_omg hS, LinearMap.zero_apply, zero_sub,
    qdet_scal hS, show omg χ s - 1 - cn (m + 1) = -χ s - 1 by rw [omg]; ring, LinearMap.smul_apply,
    Module.End.one_apply, smul_neg, smul_smul, ← neg_smul]
  congr 1; ring

theorem capelliPoly_ne (hfree : ∀ r, χ r ≠ χ s + 1) : capP χ (-χ s - 1) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun t _ => ?_
  intro h; exact hfree t (by linear_combination h)

end CompanionTheory.RgExh.Hk.UnitPf

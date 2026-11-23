import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspValueLePhiComplementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameStalkCompatibilityStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp

theorem vV_algebraMap_unit (T : CDVR) (u : T.Vˣ) : vV T.V (algebraMap T.V T.Fr (u : T.V)) = 0 := by
  have h1 : valV T.V (algebraMap T.V T.Fr (u : T.V)) = 1 := by
    unfold valV
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    refine (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).2 ?_
    show (u : T.V) ∉ IsLocalRing.maximalIdeal T.V
    exact fun h => h u.isUnit
  simp [vV, h1]

theorem log_ofAdd_neg (m : ℤ) :
    WithZero.log ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = -m := by
  first | rfl | simp [WithZero.log] | exact WithZero.log_coe _

theorem isLocalHom_of_centred {Y : Scheme.{0}} {y : Y} {ν : Valuation (Y.presheaf.stalk y) (WithZero (Multiplicative ℤ))}
    (hν : Centred y ν) (T : CDVR) (g : Y.presheaf.stalk y →+* T.V) (ρ : ℝ) (hρ : 0 < ρ)
    (hval : ∀ a, ν a ≠ 0 → -((WithZero.log (ν a) : ℤ) : ℝ) = ρ * (vV T.V (algebraMap T.V T.Fr (g a)) : ℝ)) :
    IsLocalHom g := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hm : a ∈ IsLocalRing.maximalIdeal _ := hna
  have h0 : ν a ≠ 0 := by
    intro h
    rw [hν.2.2 a h, map_zero] at ha
    exact not_isUnit_zero ha
  have hlt := hν.2.1 a hm
  have hlog : WithZero.log (ν a) < 0 := by
    have := (WithZero.log_lt_log h0 one_ne_zero).2 hlt
    simpa using this
  have hv := hval a h0
  obtain ⟨u, hu⟩ := ha
  rw [← hu, vV_algebraMap_unit] at hv
  have : (0 : ℝ) < -((WithZero.log (ν a) : ℤ) : ℝ) := by
    have : ((WithZero.log (ν a) : ℤ) : ℝ) < 0 := by exact_mod_cast hlog
    linarith
  rw [hv] at this
  simp at this

set_option maxHeartbeats 2000000 in

theorem exists_space_order_le_phi : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∃ w ∈ space TF.X Z Y.U la, ∀ (j' : (L₀ TF.X Z la).ι) (hj' : y ∈ (L₀ TF.X Z la).U j'), ν (H0.germ j' y (memTop y) hj' w) ≠ 0 ∧ ∀ m : ℤ, ν (H0.germ j' y (memTop y) hj' w) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (m : ℝ) ≤ φ / 2500 := by
  intro h1 h2 h3 h4
  refine ((GlobalTheory.T.cusp_value_le_phi_complement h1 h2 h3 h4).and (GlobalTheory.T.integral_frame_stalk_compatibility h1 h2 h3 h4)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C, hC, x0, hx⟩, ⟨C', hC', x1, hx1⟩⟩ := h
  refine ⟨C, hC, max x0 x1, fun x hx' hle ι p hp i hi Y hY Z TF la hla y hy ν hν φ hφ => ?_⟩
  obtain ⟨T, io, y', g, ρ, φT, hρ, hφT, rfl, hpt, hval⟩ := hφ
  haveI hg : IsLocalHom g := isLocalHom_of_centred hν T g ρ hρ hval
  obtain ⟨w, hw0, hwb⟩ := hx x hx' ((le_max_left _ _).trans hle) ι p hp i hi Y hY Z TF la hla y hy T io y' g φT hg hφT hpt
  refine ⟨w.1, w.2, fun j' hj' => ?_⟩
  obtain ⟨u, hu⟩ := hx1 x hx' ((le_max_right _ _).trans hle) ι p hp i hi Y hY Z TF la w y T io y' g hg hpt j' hj'
  have hu0 : algebraMap T.V T.Fr (u : T.V) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 u.ne_zero
  have hg0 : algebraMap T.V T.Fr (g (H0.germ j' y (memTop y) hj' w.1)) ≠ 0 := by
    rw [hu]; exact mul_ne_zero hu0 hw0
  have hgerm : H0.germ j' y (memTop y) hj' w.1 ≠ 0 := by
    intro h; rw [h, map_zero, map_zero] at hg0; exact hg0 rfl
  have hne : ν (H0.germ j' y (memTop y) hj' w.1) ≠ 0 := fun h => hgerm (hν.2.2 _ h)
  refine ⟨hne, fun m hm => ?_⟩
  have hv := hval _ hne
  rw [hm, log_ofAdd_neg, hu, vV_mul hu0 hw0, vV_algebraMap_unit, zero_add] at hv
  have e : (m : ℝ) = ρ * (vV T.V (evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂)) : ℝ) := by
    rw [← hv]; push_cast; ring
  rw [e, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hwb hρ.le

end GlobalTheory.HSApp

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DatExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatDatumXiOffCommonStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IdemEqAddTwistStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatDatumAddTwistPlacesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiEqXiOffMulJoinStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam
theorem QuadraticExtensionData.dat_exists : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∃ C : ℕ → ℂ, (∀ j, j < B.R.m → C j ≠ 0) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∃ s ζ ρ, J.Dat C s ζ ρ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr hoT
  obtain ⟨C, hC0, hC⟩ := _root_.GlobalTheory.T.true_geometry_row_pair_relation_alt_alt W hW u a ha hTr hoT
  refine ⟨C, hC0, fun t J hR => ?_⟩
  obtain ⟨e₀, he₀, hAe⟩ := _root_.GlobalTheory.T.true_geometry_twist_quadratic_level_alt W hW u a ha hTr t J hR
  obtain ⟨p, q, hA, hB, ⟨c0, hc0, h0⟩, hstep, hD⟩ := _root_.GlobalTheory.T.true_geometry_row_pair_property_alt W hW u a ha hTr hoT t J hR
  set Af : ∀ j, J.Ch j → ℂ := fun j α => p j α * (J.A.chr (j + 1) (J.A.xr j (J.ι j α)) : ℂ) with hAf
  set Bf : ∀ j, J.Ch (j + 1) → ℂ := fun j γ => q j γ * ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ))⁻¹ with hBf
  let k : ℕ → ℂ := fun j => if h : j + 1 < B.R.m then (hstep j h).choose else 1
  have hk : ∀ j, ∃ n : ℕ, 0 < n ∧ k j ^ n = 1 := fun j => by
    by_cases h : j + 1 < B.R.m
    · simp only [k, dif_pos h]; exact (hstep j h).choose_spec.1
    · simp only [k, dif_neg h]; exact ⟨1, one_pos, by simp⟩
  let cc : ℕ → ℂ := fun j => c0 * ∏ i ∈ Finset.range j, k i
  have hcc : ∀ j, ∃ n : ℕ, 0 < n ∧ cc j ^ n = 1 := fun j =>
    datRoot_mul hc0 (datRoot_prod _ _ fun i _ => hk i)
  let s : ∀ j, J.Ch j → ℂ := chartRescale B.R.m cc Bf
  have hs0 : ∀ α, s 0 α = 1 := fun _ => rfl
  have hsS : ∀ j γ, j < B.R.m → s (j + 1) γ = cc j * Bf j γ := fun j γ h => by
    show (if j < B.R.m then cc j * Bf j γ else 1) = _
    rw [if_pos h]
  have hsA : ∀ j, j < B.R.m → ∀ α, s j α * Af j α = cc j := by
    intro j
    induction j with
    | zero => intro _ α; rw [hs0, one_mul]; simp [cc, Af, h0 α]
    | succ j ih =>
      intro hj γ
      rw [hsS j γ (by omega)]
      have hk' : k j = (hstep j hj).choose := by simp only [k, dif_pos hj]
      have := (hstep j hj).choose_spec.2 γ
      calc cc j * Bf j γ * Af (j + 1) γ = cc j * (Bf j γ * Af (j + 1) γ) := by ring
        _ = cc j * k j := by rw [hk', ← this]
        _ = cc (j + 1) := by simp only [cc, Finset.prod_range_succ]; ring
  have hsroot : ∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1 := by
    intro j
    cases j with
    | zero => intro α; exact ⟨1, one_pos, by rw [hs0, one_pow]⟩
    | succ j =>
      intro γ
      by_cases h : j < B.R.m
      · rw [hsS j γ h]; exact datRoot_mul (hcc j) (hB j h γ)
      · refine ⟨1, one_pos, ?_⟩
        show (if j < B.R.m then cc j * Bf j γ else 1) ^ 1 = 1
        rw [if_neg h, one_pow]
  refine ⟨s, fun j α γ => s j α * (s (j + 1) γ)⁻¹ * (p j α * q j γ), fun _ => 1, hsroot, hs0,
    fun _ => ⟨1, one_pos, one_pow 1⟩, fun j hj α γ => ⟨?_, ?_⟩⟩
  · have h1 := hD e₀ he₀ j hj α γ _ _ (hC t J hR e₀ he₀ j hj α γ)
    have h2 := isRatDatum_const_mul h1 (s j α * (s (j + 1) γ)⁻¹ * J.wt j α)
    rw [← hAe] at h2
    have hdQ : J.dQ s j α γ = (s j α * (s (j + 1) γ)⁻¹ * J.wt j α) • aconv (List.ofFn fun i => (J.E i).dL j (α i) (γ i)) := by
      simp only [_root_.GlobalTheory.Fam.QuadraticExtensionData.dQ, smul_smul]
    rw [hdQ, comb_smul_coef]
    convert h2 using 2
    rename_i z
    beta_reduce
    rw [_root_.GlobalTheory.T.true_geometry_twist_quadratic_value_alt W hW u a ha hTr t J hR j hj α γ z]
    ring
  · have hjm : j < B.R.m := by omega
    have hSA := hsA j hjm α
    have hBn : Bf j γ ≠ 0 := datRoot_ne_zero (hB j hjm γ)
    have hcn : cc j ≠ 0 := datRoot_ne_zero (hcc j)
    beta_reduce
    rw [hsS j γ hjm]
    have hx : ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ)) ≠ 0 := by
      exact Circle.coe_ne_zero _
    calc s j α * (cc j * Bf j γ)⁻¹ * (p j α * q j γ) * (J.A.chr (j + 1) (J.A.xr j (J.ι j α)) : ℂ) *
          ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ))⁻¹
        = (s j α * Af j α) * Bf j γ * (cc j * Bf j γ)⁻¹ := by simp only [hAf, hBf]; ring
      _ = 1 := by rw [hSA]; exact mul_inv_cancel₀ (mul_ne_zero hcn hBn)
end GlobalTheory.Fam
end
end

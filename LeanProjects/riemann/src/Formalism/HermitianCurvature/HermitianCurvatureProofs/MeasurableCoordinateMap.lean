import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurePreservingProdRearrange
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasMUpper
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbJConvCpt

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.OG

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD Formalism.FourierDecayAlt.P.StabilizerDisintegration.MM
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

section meas

variable (S : B.RealPlaceData k r Wp Wq) (w : Equiv.Perm (Fin (r + 1)))
  (e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT (r + 1) → ℂ))

theorem meas_Xi : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w => Xi S w e p.1 p.2 := by
  have he : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w => e (p.1, p.2.1.2.1) :=
    e.measurable.comp (measurable_fst.prodMk measurable_snd.fst.snd.fst)
  have h1 : MeasM fun p : (C2.Lstidx w → ℂ) × RR k r w =>
      C2.tauM k r S.z (G.upper (e (p.1, p.2.1.2.1))) * Matrix.of p.2.1.2.2 :=
    measM_mul (measM_tau _ (OF.measM_upper he)) measurable_snd.fst.snd.snd
  have h2 : MeasM fun p : (C2.Lstidx w → ℂ) × RR k r w =>
      C2.tauM k r S.z' (G.upper p.2.2.2.1) * Matrix.of p.2.2.2.2 :=
    measM_mul (measM_tau _ (OF.measM_upper measurable_snd.snd.snd.fst)) measurable_snd.snd.snd.snd
  exact (measurable_snd.fst.fst.prodMk h1).prodMk (measurable_snd.snd.fst.prodMk h2)

theorem measurable_coordinate_map : Measurable fun q : RR k r w => Xi0 S w q := by
  have h1 : MeasM fun q : RR k r w => C2.tauM k r S.z (lowP w q.1.2.1)ᴴ * Matrix.of q.1.2.2 :=
    measM_mul (measM_tau _ (measM_star (OF.measM_lowP w measurable_fst.snd.fst))) measurable_fst.snd.snd
  have h2 : MeasM fun q : RR k r w => C2.tauM k r S.z' (G.upper q.2.2.1) * Matrix.of q.2.2.2 :=
    measM_mul (measM_tau _ (OF.measM_upper measurable_snd.snd.fst)) measurable_snd.snd.snd
  exact (measurable_fst.fst.prodMk h1).prodMk (measurable_snd.fst.prodMk h2)

variable {μ0 μ0' : Measure (Mt k r)} (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0)
  (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0')

include hμ0 hμ0' in
theorem ae_good : ∀ᵐ q ∂(nuR S w μ0 μ0'), Matrix.of q.1.1 ∈ UWset k r S.z ∧ Matrix.of q.1.2.2 ∈ C2.N0set k r S.z ∧
    Matrix.of q.2.1 ∈ UWset k r S.z' ∧ Matrix.of q.2.2.2 ∈ C2.N0set k r S.z' := by
  haveI : IsFiniteMeasureOnCompacts S.μW := ⟨fun K hK => S.haarW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts S.μW' := ⟨fun K hK => S.haarW'.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μ0 := ⟨fun K hK => hμ0.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μ0' := ⟨fun K hK => hμ0'.finite_compact K hK⟩
  haveI t1 : SFinite S.μW := inferInstance
  haveI t2 : SFinite μ0 := inferInstance
  haveI t5 : SFinite S.μW' := inferInstance
  haveI t6 : SFinite μ0' := inferInstance
  have hW : ∀ᵐ a ∂S.μW, Matrix.of a ∈ UWset k r S.z :=
    ae_iff.2 S.haarW.conc
  have hW' : ∀ᵐ a ∂S.μW', Matrix.of a ∈ UWset k r S.z' :=
    ae_iff.2 S.haarW'.conc
  have hN : ∀ᵐ a ∂μ0, Matrix.of a ∈ C2.N0set k r S.z :=
    ae_iff.2 hμ0.conc
  have hN' : ∀ᵐ a ∂μ0', Matrix.of a ∈ C2.N0set k r S.z' :=
    ae_iff.2 hμ0'.conc
  have a1 : ∀ᵐ q ∂(nuR S w μ0 μ0'), Matrix.of q.1.1 ∈ UWset k r S.z := by
    have b1 : ∀ᵐ p ∂(S.μW.prod ((volume : Measure (C2.LPidx w → ℂ)).prod μ0)), Matrix.of p.1 ∈ UWset k r S.z :=
      Measure.quasiMeasurePreserving_fst.ae (p := fun a : Mt k r => Matrix.of a ∈ UWset k r S.z) hW
    exact Measure.quasiMeasurePreserving_fst.ae (p := fun p : Mt k r × ((C2.LPidx w → ℂ) × Mt k r) =>
      Matrix.of p.1 ∈ UWset k r S.z) b1
  have a2 : ∀ᵐ q ∂(nuR S w μ0 μ0'), Matrix.of q.1.2.2 ∈ C2.N0set k r S.z := by
    have b1 : ∀ᵐ p ∂((volume : Measure (C2.LPidx w → ℂ)).prod μ0), Matrix.of p.2 ∈ C2.N0set k r S.z :=
      Measure.quasiMeasurePreserving_snd.ae (p := fun a : Mt k r => Matrix.of a ∈ C2.N0set k r S.z) hN
    have b2 : ∀ᵐ p ∂(S.μW.prod ((volume : Measure (C2.LPidx w → ℂ)).prod μ0)),
        Matrix.of p.2.2 ∈ C2.N0set k r S.z :=
      Measure.quasiMeasurePreserving_snd.ae (p := fun p : (C2.LPidx w → ℂ) × Mt k r =>
        Matrix.of p.2 ∈ C2.N0set k r S.z) b1
    exact Measure.quasiMeasurePreserving_fst.ae (p := fun p : Mt k r × ((C2.LPidx w → ℂ) × Mt k r) =>
      Matrix.of p.2.2 ∈ C2.N0set k r S.z) b2
  have a3 : ∀ᵐ q ∂(nuR S w μ0 μ0'), Matrix.of q.2.1 ∈ UWset k r S.z' := by
    have b1 : ∀ᵐ p ∂(S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0')),
        Matrix.of p.1 ∈ UWset k r S.z' :=
      Measure.quasiMeasurePreserving_fst.ae (p := fun a : Mt k r => Matrix.of a ∈ UWset k r S.z') hW'
    exact Measure.quasiMeasurePreserving_snd.ae (p := fun p : Mt k r × ((G.UT (r + 1) → ℂ) × Mt k r) =>
      Matrix.of p.1 ∈ UWset k r S.z') b1
  have a4 : ∀ᵐ q ∂(nuR S w μ0 μ0'), Matrix.of q.2.2.2 ∈ C2.N0set k r S.z' := by
    have b1 : ∀ᵐ p ∂((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0'), Matrix.of p.2 ∈ C2.N0set k r S.z' :=
      Measure.quasiMeasurePreserving_snd.ae (p := fun a : Mt k r => Matrix.of a ∈ C2.N0set k r S.z') hN'
    have b2 : ∀ᵐ p ∂(S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0')),
        Matrix.of p.2.2 ∈ C2.N0set k r S.z' :=
      Measure.quasiMeasurePreserving_snd.ae (p := fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
        Matrix.of p.2 ∈ C2.N0set k r S.z') b1
    exact Measure.quasiMeasurePreserving_snd.ae (p := fun p : Mt k r × ((G.UT (r + 1) → ℂ) × Mt k r) =>
      Matrix.of p.2.2 ∈ C2.N0set k r S.z') b2
  filter_upwards [a1, a2, a3, a4] with q h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end meas

theorem nn_smul {α : Type*} [MeasurableSpace α] (c : NNReal) (μ : Measure α) : c • μ = ((c : ENNReal) • μ) := by
  ext s _
  rw [Measure.smul_apply, Measure.smul_apply]
  rfl

theorem meas_actR (γ : B.Mat k r) (p : B.SS k r) :
    Measurable fun y : Mt k r => C6.actR γ (Matrix.of y) p := by
  have hy : MeasM fun y : Mt k r => Matrix.of y := measurable_id
  unfold C6.actR
  exact (measurable_const.prodMk (measM_mul hy (measM_const _))).prodMk
    (measurable_const.prodMk (measM_mul (measM_mul (measM_mul (measM_const _) hy) (measM_const _)) (measM_const _)))

def Hf (S : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1))) (θ : B.SS k r → ℝ)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (p : (C2.Lstidx w → ℂ) × RR k r w) : Wq →L[ℂ] Wp :=
  θ (C6.actR γ (rhoX S γ w p.1) (Xi0 S w p.2)) • D.orbIntegrand S γ F (Xi0 S w p.2)

section main

variable (S : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) {w : Equiv.Perm (Fin (r + 1))}
  {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0) (hZw : Zhat k r S.z S.z' γ = C2.monoP w d)
  (hpos : 0 < Gf k r S.z S.z' γ) (hrel : C6.IsRelevant S γ)
  (e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT (r + 1) → ℂ)) (hemp : MeasurePreserving e volume volume)
  (he : ∀ p, G.upper (e p) = (lowS w p.1)ᴴ * (lowP w p.2)ᴴ)
  {μ0 μ0' : Measure (Mt k r)} (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0)
  (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0')

include hγ hd hZw hpos hrel he in
theorem comp_eq (θ : B.SS k r → ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (x : C2.Lstidx w → ℂ) (q : RR k r w)
    (hq1 : Matrix.of q.1.2.2 ∈ Nset k r) (hq2 : Matrix.of q.2.2.2 ∈ Nset k r) :
    θ (Xi S w e x q) • D.orbIntegrand S γ F (Xi S w e x q) = Hf S γ w θ F (Tt S γ w e (x, q)) := by
  have key : ∀ {ρ : B.Mat k r}, ρ ∈ C6.Rset γ → ∀ (p : B.SS k r), WeylGroupFacts.col k r (Matrix.of p.1.2) →
      WeylGroupFacts.col k r (Matrix.of p.2.2) → D.orbIntegrand S γ F (C6.actR γ ρ p) = D.orbIntegrand S γ F p := by
    intro ρ hρ p h1 h2
    have hψ := hrel.2 ρ hρ
    obtain ⟨hρN, hρ'N⟩ := hρ
    have cρ := ((WeylGroupFacts.nset_iff _).1 hρN).2
    have cρ' := ((WeylGroupFacts.nset_iff _).1 hρ'N).2
    have iρ : ρ⁻¹ * ρ = 1 := PI.PolynomialProperness.GN.inv_mul ((WeylGroupFacts.nset_iff _).1 hρN).1
    have iγ : γ * γ⁻¹ = 1 := Matrix.mul_nonsing_inv γ (Matrix.isUnit_det_of_left_inverse (PI.PolynomialProperness.GN.inv_mul hγ))
    have e1 := WeylGroupFacts.ell_mul S.z S.z_mem cρ h1
    have e2 := WeylGroupFacts.ell_mul S.z' S.z'_mem cρ' h2
    have hs : (Matrix.of p.1.1)⁻¹ * (ρ * Matrix.of p.1.2)⁻¹ * γ * (γ⁻¹ * ρ * γ * Matrix.of p.2.2) * Matrix.of p.2.1 =
        (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1 := by
      rw [Matrix.mul_inv_rev]
      calc _ = (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (ρ⁻¹ * (γ * γ⁻¹) * ρ) * γ * Matrix.of p.2.2 *
            Matrix.of p.2.1 := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [iγ, Matrix.mul_one, iρ, Matrix.mul_one]
    have hxi : B.xiTau S (1, 1) (C6.actR γ ρ p) = B.xiTau S (1, 1) p := by
      unfold B.xiTau C6.actR
      simp only [Equiv.apply_symm_apply]
      unfold B.lam
      rw [e1, e2]
      unfold psi at hψ
      set a := (cStd * ell k r S.z ρ).re
      set b := (cStd * ell k r S.z' (γ⁻¹ * ρ * γ)).re
      have hx : ((1 : ℝ) * (cStd * (ell k r S.z ρ + ell k r S.z (Matrix.of p.1.2))).re -
          (1 : ℝ) * (cStd * (ell k r S.z' (γ⁻¹ * ρ * γ) + ell k r S.z' (Matrix.of p.2.2))).re : ℝ) =
          (a - b) + ((1 : ℝ) * (cStd * ell k r S.z (Matrix.of p.1.2)).re -
            (1 : ℝ) * (cStd * ell k r S.z' (Matrix.of p.2.2)).re) := by
        simp only [a, b, mul_add, Complex.add_re]
        ring
      rw [hx, Complex.ofReal_add, mul_add, Complex.exp_add, Complex.ofReal_sub, mul_sub, Complex.exp_sub, hψ,
        div_self (Complex.exp_ne_zero _), one_mul]
    have hrh : B.rho S (C6.actR γ ρ p) F γ = B.rho S p F γ := by
      unfold B.rho B.sgs C6.actR
      simp only [Equiv.apply_symm_apply, hs]
    unfold D.orbIntegrand
    rw [hxi, hrh]
  have hX : Xi S w e x q = C6.actR γ (rhoX S γ w x) (Xi0 S w (Tx S γ w e x q)) := by
    apply Xi_eq <;> assumption
  obtain ⟨hρR, -⟩ : rhoX S γ w x ∈ C6.Rset γ ∧ C2.uMap k r S.z (rhoX S γ w x) = (lowS w x)ᴴ := by
    apply rhoX_spec <;> assumption
  have hρN := hρR.1
  have hρ'N := hρR.2
  have iρ : (rhoX S γ w x)⁻¹ * rhoX S γ w x = 1 := PI.PolynomialProperness.GN.inv_mul ((WeylGroupFacts.nset_iff _).1 hρN).1
  have iρ' : (γ⁻¹ * rhoX S γ w x * γ)⁻¹ * (γ⁻¹ * rhoX S γ w x * γ) = 1 :=
    PI.PolynomialProperness.GN.inv_mul ((WeylGroupFacts.nset_iff _).1 hρ'N).1
  have cρi := WeylGroupFacts.col_of_left_inv ((WeylGroupFacts.nset_iff _).1 hρN).2 iρ
  have cρi' := WeylGroupFacts.col_of_left_inv ((WeylGroupFacts.nset_iff _).1 hρ'N).2 iρ'
  have hz : C2.StdZ k r S.z := ⟨S.z_mem, S.T_pos⟩
  have hz' : C2.StdZ k r S.z' := ⟨S.z'_mem, S.T'_pos⟩
  set P := Xi0 S w (Tx S γ w e x q) with hP
  have E1 : rhoX S γ w x * Matrix.of P.1.2 =
      C2.tauM k r S.z (G.upper (e (x, q.1.2.1))) * Matrix.of q.1.2.2 := by
    have := congrArg (fun s : B.SS k r => Matrix.of s.1.2) hX
    simpa [Xi, C6.actR] using this.symm
  have E2 : (γ⁻¹ * rhoX S γ w x * γ) * Matrix.of P.2.2 =
      C2.tauM k r S.z' (G.upper q.2.2.1) * Matrix.of q.2.2.2 := by
    have := congrArg (fun s : B.SS k r => Matrix.of s.2.2) hX
    simpa [Xi, C6.actR] using this.symm
  have c1 : WeylGroupFacts.col k r (Matrix.of P.1.2) := by
    have h : Matrix.of P.1.2 = (rhoX S γ w x)⁻¹ * (rhoX S γ w x * Matrix.of P.1.2) := by
      rw [← Matrix.mul_assoc, iρ, Matrix.one_mul]
    rw [h, E1]
    exact WeylGroupFacts.col_mul cρi (WeylGroupFacts.col_mul ((WeylGroupFacts.nset_iff _).1 (A.tau_N hz (HC.upper_mem _))).2
      ((WeylGroupFacts.nset_iff _).1 hq1).2)
  have c2 : WeylGroupFacts.col k r (Matrix.of P.2.2) := by
    have h : Matrix.of P.2.2 = (γ⁻¹ * rhoX S γ w x * γ)⁻¹ * ((γ⁻¹ * rhoX S γ w x * γ) * Matrix.of P.2.2) := by
      rw [← Matrix.mul_assoc, iρ', Matrix.one_mul]
    rw [h, E2]
    exact WeylGroupFacts.col_mul cρi' (WeylGroupFacts.col_mul ((WeylGroupFacts.nset_iff _).1 (A.tau_N hz' (HC.upper_mem _))).2
      ((WeylGroupFacts.nset_iff _).1 hq2).2)
  rw [hX]
  show θ (C6.actR γ (rhoX S γ w x) P) • D.orbIntegrand S γ F (C6.actR γ (rhoX S γ w x) P) =
    θ (C6.actR γ (rhoX S γ w x) P) • D.orbIntegrand S γ F P
  rw [key hρR P c1 c2]

include hγ hd hZw hpos hrel hemp he hμ0 hμ0' in
theorem orb_int [CompleteSpace Wp] {c1 c2 : NNReal} (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hN1 : S.μN = c1 • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0).map
      (fun p => Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)))
    (hN2 : S.μN = c2 • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0').map
      (fun p => Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2)))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (θ : B.SS k r → ℝ) (hθ : D.IsNormCut S γ (D.muR S γ w) θ)
    (hint : Integrable (fun p => θ p • D.orbIntegrand S γ F p) S.μSS) :
    Integrable (fun q => D.orbIntegrand S γ F (Xi0 S w q)) (nuR S w μ0 μ0') ∧
      ∫ p, θ p • D.orbIntegrand S γ F p ∂S.μSS =
        ((c1 * c2 : NNReal) : ℝ) • ∫ q, D.orbIntegrand S γ F (Xi0 S w q) ∂(nuR S w μ0 μ0') := by
  haveI : IsFiniteMeasureOnCompacts S.μW := ⟨fun K hK => S.haarW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts S.μW' := ⟨fun K hK => S.haarW'.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μ0 := ⟨fun K hK => hμ0.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μ0' := ⟨fun K hK => hμ0'.finite_compact K hK⟩
  haveI t1 : SFinite S.μW := inferInstance
  haveI t2 : SFinite μ0 := inferInstance
  haveI t5 : SFinite S.μW' := inferInstance
  haveI t6 : SFinite μ0' := inferInstance
  haveI t7 : SFinite (nuR S w μ0 μ0') := by unfold nuR; infer_instance
  have hz : C2.StdZ k r S.z := ⟨S.z_mem, S.T_pos⟩
  have hz' : C2.StdZ k r S.z' := ⟨S.z'_mem, S.T'_pos⟩

  have nmul : ∀ a b : B.Mat k r, a ∈ Nset k r → b ∈ Nset k r → a * b ∈ Nset k r := by
    intro a b ha hb
    rw [WeylGroupFacts.nset_iff] at ha hb ⊢
    refine ⟨?_, WeylGroupFacts.col_mul ha.2 hb.2⟩
    have h1 : aᴴ * Hpk k r * a = Hpk k r := ha.1
    have h2 : bᴴ * Hpk k r * b = Hpk k r := hb.1
    show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [h1, h2]
  have hrho : ∀ x : C2.Lstidx w → ℂ,
      D.rhoOfU S γ (Matrix.conjTranspose (C2.lowOf (fun q => q.1) x)) = rhoX S γ w x := fun x => rfl

  have hSS := ME.muSS_eq S w e hemp μ0 μ0' hμ0 hμ0' c1 c2 hN1 hN2
  have hc : ((c1 * c2 : NNReal) : ENNReal) ≠ 0 := by
    rw [ENNReal.coe_ne_zero]
    exact mul_ne_zero hc1.ne' hc2.ne'
  rw [hSS, nn_smul] at hint
  rw [hSS, nn_smul]
  have hint1 := (integrable_smul_measure hc ENNReal.coe_ne_top).1 hint
  have hXm : AEMeasurable (fun p : (C2.Lstidx w → ℂ) × RR k r w => Xi S w e p.1 p.2)
      ((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0')) := (meas_Xi S w e).aemeasurable
  have hint2 := (integrable_map_measure hint1.aestronglyMeasurable hXm).1 hint1
  have hgood : ∀ᵐ p ∂((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0')),
      θ (Xi S w e p.1 p.2) • D.orbIntegrand S γ F (Xi S w e p.1 p.2) = Hf S γ w θ F (Tt S γ w e p) := by
    have h := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (C2.Lstidx w → ℂ)))
      (ν := nuR S w μ0 μ0')).ae
      (p := fun q : RR k r w => Matrix.of q.1.1 ∈ UWset k r S.z ∧ Matrix.of q.1.2.2 ∈ C2.N0set k r S.z ∧
        Matrix.of q.2.1 ∈ UWset k r S.z' ∧ Matrix.of q.2.2.2 ∈ C2.N0set k r S.z') (ae_good S w hμ0 hμ0')
    filter_upwards [h] with p hp
    exact comp_eq S hγ hd hZw hpos hrel e he θ F p.1 p.2 hp.2.1.1 hp.2.2.2.1
  have hint3 : Integrable (fun p => Hf S γ w θ F (Tt S γ w e p))
      ((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0')) := hint2.congr hgood
  have hmp : MeasurePreserving (Tt S γ w e) ((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0'))
      ((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0')) := by
    apply OF.mp_Tt <;> assumption
  have hemb : MeasurableEmbedding (Tt S γ w e) := by
    apply OF.emb_Tt <;> assumption
  have hint4 : Integrable (Hf S γ w θ F) ((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0')) :=
    (hmp.integrable_comp_emb hemb).1 hint3
  have hI1 : ∫ p, θ (Xi S w e p.1 p.2) • D.orbIntegrand S γ F (Xi S w e p.1 p.2)
        ∂((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0')) =
      ∫ p, Hf S γ w θ F p ∂((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0')) := by
    rw [integral_congr_ae hgood]
    exact hmp.integral_comp hemb _

  have hcut : ∀ P : B.SS k r, S.inSS P →
      ∫ x, θ (C6.actR γ (rhoX S γ w x) P) ∂(volume : Measure (C2.Lstidx w → ℂ)) = 1 := by
    intro P hP
    have h1 := hθ.2.2 P hP
    have hφ : Measurable fun x : C2.Lstidx w → ℂ =>
        (Matrix.of.symm (D.rhoOfU S γ (Matrix.conjTranspose (C2.lowOf (fun q => q.1) x))) : Mt k r) := by
      simp only [hrho]
      have hm : MeasM fun t : C2.Lstidx w → ℂ => rhoX S γ w (id t) := by
        apply OF.measM_rhoX <;> first | exact measurable_id | assumption
      exact hm
    unfold D.muR at h1
    rw [integral_map (f := fun y : Mt k r => θ (C6.actR γ (Matrix.of y) P)) hφ.aemeasurable
      (hθ.1.comp (meas_actR γ P)).aestronglyMeasurable] at h1
    simpa only [hrho, Equiv.apply_symm_apply] using h1
  have hSSae : ∀ᵐ q ∂(nuR S w μ0 μ0'), S.inSS (Xi0 S w q) := by
    filter_upwards [ae_good S w hμ0 hμ0'] with q hq
    refine ⟨hq.1, ?_, hq.2.2.1, ?_⟩
    · exact nmul _ _ (A.tau_N hz (lowPH_UT _)) hq.2.1.1
    · exact nmul _ _ (A.tau_N hz' (HC.upper_mem _)) hq.2.2.2.1
  have hfib : ∀ᵐ q ∂(nuR S w μ0 μ0'),
      ∫ x, Hf S γ w θ F (x, q) ∂(volume : Measure (C2.Lstidx w → ℂ)) = D.orbIntegrand S γ F (Xi0 S w q) := by
    filter_upwards [hSSae] with q hq
    show ∫ x, θ (C6.actR γ (rhoX S γ w x) (Xi0 S w q)) • D.orbIntegrand S γ F (Xi0 S w q)
      ∂(volume : Measure (C2.Lstidx w → ℂ)) = D.orbIntegrand S γ F (Xi0 S w q)
    rw [integral_smul_const, hcut _ hq, one_smul]
  refine ⟨?_, ?_⟩
  · exact hint4.integral_prod_right.congr hfib
  · rw [integral_smul_measure, integral_map hXm hint1.aestronglyMeasurable, hI1, integral_prod_symm _ hint4,
      integral_congr_ae hfib, ENNReal.coe_toReal]

end main

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.OG

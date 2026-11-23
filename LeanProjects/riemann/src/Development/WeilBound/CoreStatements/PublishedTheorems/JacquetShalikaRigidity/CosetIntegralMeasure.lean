import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace CosetIntegralMeasure

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem meas_mul (g : GA E k) : Measurable (fun h : GA E k => g * h) := by
  exact measurable_const_mul g

theorem lint_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) (F : GA E k → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ h, F h ∂nuG Γ d = ∑' γ : Γ, ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k d := by
  rw [nuG, lintegral_sum_measure]
  refine tsum_congr fun γ => ?_
  exact lintegral_map hF (meas_mul _)

end CosetIntegralMeasure

open CosetIntegralMeasure in
theorem coset_integration_of : N0 → N1 → N3 → CosetIntegralParabolic := by
  intro h0 _ _ E _ _ _ k j hj1 hjk F hF
  obtain ⟨hgam, huniq, hmul, hinv, -, hmir, -⟩ := h0 E k j hj1 hjk
  have hd : k - (j - 1 + 1) = k - j := by omega
  let f : RowT E k j × ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)) →
      ({γ : GL (Fin k) E | GlobalTheory j γ} : Set (GL (Fin k) E)) := fun x =>
    ⟨(gam x.1)⁻¹ * (x.2 : GL (Fin k) E), hmul (gam x.1)⁻¹ (x.2 : GL (Fin k) E) (hinv (gam x.1) (hgam x.1).1)
      (hmir (x.2 : GL (Fin k) E) x.2.2).2⟩
  have hinj : Function.Injective f := by
    rintro ⟨ξ, p⟩ ⟨ξ', p'⟩ h
    have hv : (gam ξ)⁻¹ * (p : GL (Fin k) E) = (gam ξ')⁻¹ * (p' : GL (Fin k) E) := congrArg Subtype.val h
    have hB : GlobalTheory j ((gam ξ)⁻¹ * (p : GL (Fin k) E))⁻¹ := hinv ((gam ξ)⁻¹ * (p : GL (Fin k) E)) (f (ξ, p)).2
    obtain ⟨q, -, huq⟩ := huniq _ hB
    have e1 : (ξ, (p : GL (Fin k) E)⁻¹) = q :=
      huq (ξ, (p : GL (Fin k) E)⁻¹) ⟨(hmir (p : GL (Fin k) E) p.2).1, by simp only [_root_.mul_inv_rev, inv_inv]⟩
    have e2 : (ξ', (p' : GL (Fin k) E)⁻¹) = q :=
      huq (ξ', (p' : GL (Fin k) E)⁻¹) ⟨(hmir (p' : GL (Fin k) E) p'.2).1, by simp only [hv, _root_.mul_inv_rev, inv_inv]⟩
    have h3 := Prod.mk.inj (e1.trans e2.symm)
    exact Prod.ext h3.1 (Subtype.ext (inv_injective h3.2))
  have hsurj : Function.Surjective f := by
    rintro ⟨γ, hγ⟩
    obtain ⟨⟨ξ, q⟩, ⟨hq, heq⟩, -⟩ := huniq γ⁻¹ (hinv γ hγ)
    have hq' : IsMir (j - 1) q := hq
    have heq' : γ⁻¹ = q * gam ξ := heq
    refine ⟨(ξ, ⟨q⁻¹, (hmir q hq').1⟩), Subtype.ext ?_⟩
    show (gam ξ)⁻¹ * q⁻¹ = γ
    rw [← _root_.mul_inv_rev, ← heq', inv_inv]
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hR : ∀ ξ : RowT E k j, ∫⁻ h, F ((ratGL E k (gam ξ))⁻¹ * h) ∂nuP E k (j - 1) =
      ∑' p : ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)),
        ∫⁻ h, F (ratGL E k ((gam ξ)⁻¹ * (p : GL (Fin k) E)) * h) ∂nuD E k (k - j) := by
    intro ξ
    have e0 := lint_nuG {γ : GL (Fin k) E | IsMir (j - 1) γ} (k - (j - 1 + 1))
      (fun h => F ((ratGL E k (gam ξ))⁻¹ * h)) (hF.comp (meas_mul _))
    refine e0.trans ?_
    rw [hd]
    refine tsum_congr fun p => ?_
    simp only [map_mul, map_inv, mul_assoc]
  calc ∫⁻ h, F h ∂nuB E k j
      = ∑' γ : ({γ : GL (Fin k) E | GlobalTheory j γ} : Set (GL (Fin k) E)),
          ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k (k - j) := lint_nuG {γ : GL (Fin k) E | GlobalTheory j γ} (k - j) F hF
    _ = ∑' x : RowT E k j × ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)),
          ∫⁻ h, F (ratGL E k ((gam x.1)⁻¹ * (x.2 : GL (Fin k) E)) * h) ∂nuD E k (k - j) :=
        (e.tsum_eq (fun γ : ({γ : GL (Fin k) E | GlobalTheory j γ} : Set (GL (Fin k) E)) =>
          ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k (k - j))).symm
    _ = ∑' ξ : RowT E k j, ∑' p : ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)),
          ∫⁻ h, F (ratGL E k ((gam ξ)⁻¹ * (p : GL (Fin k) E)) * h) ∂nuD E k (k - j) := by
        exact ENNReal.tsum_prod (f := fun (ξ : RowT E k j) (p : ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E))) =>
            ∫⁻ h, F (ratGL E k ((gam ξ)⁻¹ * (p : GL (Fin k) E)) * h) ∂nuD E k (k - j))
    _ = ∑' ξ : RowT E k j, ∫⁻ h, F ((ratGL E k (gam ξ))⁻¹ * h) ∂nuP E k (j - 1) :=
        tsum_congr fun ξ => (hR ξ).symm

end PositivityTheory.AdelicQuotientData

end

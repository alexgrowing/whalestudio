import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodLevelMultipleSameAdelicPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulipointLiftToFinerLevelCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedDataCompleteDVRExtensionStatement

noncomputable section

namespace GlobalTheory.KeyBadPrime

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

theorem key_unit_bad : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (κ : KeyRule), IsKeyRule κ → 1 ≤ Dw.p + Dw.q → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → ¬ l.GoodAt p → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' Xo.univ.t x → SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ u : T.Vˣ, (κ T.Fr k : T.Fr) = algebraMap T.V T.Fr u := by
  intro E _ _ _ H Dw l Xo c κ hκ hpq la p hp hpl hbad T io e ho x hxs G t' m1 m2 n w hw θ hθ k hk
  obtain ⟨l₂, hd, hA, hg₂⟩ := GlobalTheory.T.exists_goodLevel_multiple_same_adelicPart E H l
  obtain ⟨Xo₂⟩ := GlobalTheory.Moduli.moduli_scheme_exists E H Dw l₂ hpq
  obtain ⟨c₂, la₂, T', iT, φ, e', io₂, e₂, x₂, r, m, he', hv, hφ, ho₂, hxs₂, hx₂⟩ :=
    GlobalTheory.T.modulipoint_lift_to_finerLevel_completeDVR E H Dw l l₂ Xo Xo₂ c hpq hd hA la T io e ho x hxs
  obtain ⟨G', t'', mt, m2', n', w', θ', k', hw', hθ', hk', hpb⟩ := GlobalTheory.T.exists_integralFramedData_completeDVR_extension E H T T' iT φ hφ G t' m2 n w hw θ hθ k hk
  obtain ⟨a₁, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m1 mt
  obtain ⟨m1', -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m (PullbackSections.sabMapCast a₁ hx₂.symm)
  obtain ⟨u', hu'⟩ := GlobalTheory.KeyIntegralVal.key_unit hκ hpq hg₂ ho₂ hxs₂ m1' m2' hw' hθ' k' hk'
  have h1 : (κ T'.Fr k' : T'.Fr) = iT (κ T.Fr k : T.Fr) := hκ.2.1 T.Fr T'.Fr iT k k' hpb
  set a : T.Fr := (κ T.Fr k : T.Fr) with ha
  have ha0 : a ≠ 0 := Units.ne_zero _
  have hu0 : ∀ (V : CDVR) (u : V.Vˣ), vV V.V (algebraMap V.V V.Fr u) = 0 := by
    intro V u
    have hne : ∀ u : V.Vˣ, algebraMap V.V V.Fr u ≠ 0 := fun u => (u.isUnit.map _).ne_zero
    have nn : ∀ b : V.V, 0 ≤ vV V.V (algebraMap V.V V.Fr b) := fun b => by
      by_cases h : algebraMap V.V V.Fr b = 0
      · simp [h, vV]
      have := (WithZero.log_le_log (valV_ne_zero (V := V.V) h) one_ne_zero).2
        (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ b)
      rw [WithZero.log_one] at this
      rw [vV]; omega
    have h := vV_mul (V := V.V) (hne u) (hne u⁻¹)
    rw [← map_mul, Units.mul_inv, map_one, show vV V.V (1 : V.Fr) = 0 by simp [vV]] at h
    have := nn u
    have := nn (u⁻¹ : V.Vˣ)
    omega
  have hva : vV T.V a = 0 := by
    have h2 := hv a
    rw [← h1, hu', hu0] at h2
    have : (0 : ℤ) < e' := by exact_mod_cast he'
    nlinarith
  have hvi : vV T.V a⁻¹ = 0 := by
    have h := vV_mul (V := T.V) ha0 (inv_ne_zero ha0)
    rw [mul_inv_cancel₀ ha0, show vV T.V (1 : T.Fr) = 0 by simp [vV], hva] at h
    omega
  obtain ⟨b, hb⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T.V) hva.ge
  obtain ⟨b', hb'⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T.V) hvi.ge
  have hbb : b * b' = 1 := IsFractionRing.injective T.V T.Fr (by rw [map_mul, hb, hb', mul_inv_cancel₀ ha0, map_one])
  exact ⟨⟨b, b', hbb, by rw [mul_comm]; exact hbb⟩, hb.symm⟩

end GlobalTheory.KeyBadPrime

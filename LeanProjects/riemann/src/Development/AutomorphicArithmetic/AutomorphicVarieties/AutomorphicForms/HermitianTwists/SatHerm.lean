import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.RepNewformOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.UOfSat

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.TR UpperTheory.V.Sd UpperTheory.V.Af.Gk GlobalTheory.LFun

theorem UpperTheory.V.Af.Rn.satHerm :
    UpperTheory.V.Af.Rn.SatHerm := by
  intro π H hH w α β hB
  have hB0 : HasSatGL w (π.locRep w) {α, β} := hB
  have hK : ∀ k ∈ KGL w 2, GlobalTheory.CuspRep.invT 2 _ k ∈ KGL w 2 := by
    rintro _ ⟨k, rfl⟩
    exact ⟨GlobalTheory.CuspRep.invT 2 _ k, InvT.map_invT _ k⟩
  have hB' : HasSatGL w ((π.locRep w).comp (GlobalTheory.CuspRep.invT 2 (w.adicCompletion ℚ))) (({α, β} : Multiset ℂˣ).map (·⁻¹)) :=
    InvT.hasSatGL_invT (ρ := π.locRep w) (LinearEquiv.refl ℂ π.V) (fun _ _ => rfl) hB0
  obtain ⟨x, hx'⟩ := hB0.exists_vec
  have hx := hx'.2.1
  have h0 := hx'.1
  have hfix := GlobalTheory.LGrp.mem_fixed.1 hx
  have h2 := hB'.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => hfix _ (hK k hk)) h0
  have hϖ := unif_spec w
  have e := heckeAdj ℚ 2 w π.V (π.locRep w) H (fun g => hH.fin (GlobalTheory.CuspRep.locGL ℚ 2 w g)) x hx _ hϖ 1
  rw [hx'.2.2.2 _ hϖ 1 (by norm_num), h2.2.2.2 _ hϖ 1 (by norm_num), H.map_smulₛₗ, (H x).map_smul, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul] at e
  have e' := mul_right_cancel₀ (fun h => h0 (hH.definite x h)) e
  have hq : 0 < Formalism.UG.qV ℚ w := Nat.pos_of_ne_zero (qV_ne_zero w)
  have hc : ∀ B, satEig (Formalism.UG.qV ℚ w) 2 B 1 =
      ((((Formalism.UG.qV ℚ w : ℝ) ^ (1 / 2 : ℝ) : ℝ)) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm 1 := fun B => by
    rw [Complex.ofReal_cpow (by positivity), satEig]
    norm_num
  have hne : ((((Formalism.UG.qV ℚ w : ℝ) ^ (1 / 2 : ℝ) : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  rw [hc, hc, map_mul, Complex.conj_ofReal] at e'
  have e'' := mul_left_cancel₀ hne e'
  have e3 : (starRingEnd ℂ) ((α : ℂ) + β) = (α : ℂ)⁻¹ + (β : ℂ)⁻¹ := by
    simpa [Multiset.esymm, Multiset.powersetCard_one, add_comm] using e''
  rw [e3, Units.val_mul]
  field_simp
  ring

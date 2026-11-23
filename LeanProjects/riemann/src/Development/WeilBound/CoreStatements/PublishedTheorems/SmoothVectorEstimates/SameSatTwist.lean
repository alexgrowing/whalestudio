import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalEqTwistNormalised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace PSmo

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem val_eq_prod {π : CuspSub E a} {ω : HChar E} (hω : π.HasCentChar ω) {w : HeightOneSpectrum (𝓞 E)}
    {B : Multiset ℂˣ} (hB : HasSatGL w (π.locRep w) B) : ω.val w = B.prod := by
  classical
  obtain ⟨x, hx⟩ := hB.exists_vec
  set u : (w.adicCompletion E)ˣ := atFin w (unif w) with hu_def
  have hu : IsUnifV E w (u : w.adicCompletion E) := unif_spec w
  have h0 : (u : w.adicCompletion E) ≠ 0 := u.ne_zero

  have hTn : Tj ℂ a (Ov E w) (u : w.adicCompletion E) a =
      dosetInd ℂ (KGL w a) (GlobalTheory.WeylGL.tor h0 fun _ => 1) := by
    rw [GlobalTheory.WeylGL.Tj_eq h0]; simp
  have h1 := hx.2.2.2 _ hu a le_rfl
  rw [hTn, heckeVec_dosetInd (R := {GlobalTheory.WeylGL.tor h0 fun _ => 1}) hx.2.1, Finset.sum_singleton] at h1
  rotate_left
  · intro γ hγ
    exact GlobalTheory.WeylGL.mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simpa using hγ⟩
  · intro g hg
    obtain ⟨c, hc, d, hd, rfl⟩ := GlobalTheory.WeylGL.mem_doset.1 hg
    refine ⟨_, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    rw [← GlobalTheory.WeylGL.tor_const_comm, mul_assoc, inv_mul_cancel_left]
    exact mul_mem hc hd
  have ht : GlobalTheory.WeylGL.tor h0 (fun _ : Fin a => (1 : ℤ)) = GeneralLinearGroup.scalar (Fin a) u := by
    ext i j
    simp [GlobalTheory.WeylGL.tor_val, Matrix.diagonal_apply]
  have hz : locGL E a w (GeneralLinearGroup.scalar (Fin a) u) =
      GeneralLinearGroup.scalar (Fin a) (Units.map (corner (sLoc E w)) u) := cornerGL_scalar _ u
  have e1 := finId_det_locGL (E := E) (a := 1) w (GeneralLinearGroup.scalar (Fin 1) u)
  have e2 : GeneralLinearGroup.det (locGL E 1 w (GeneralLinearGroup.scalar (Fin 1) u)) =
      Units.map (corner (sLoc E w)) u := by
    rw [locGL, cornerGL_scalar]; ext; simp
  have e3 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) u) = u := by ext; simp
  rw [e2, e3] at e1
  have hf : ω.1 (finId E (Units.map (corner (sLoc E w)) u)) = ω.val w := by rw [e1]; rfl
  have h2 : π.locRep w (GeneralLinearGroup.scalar (Fin a) u) x = ((ω.val w : ℂˣ) : ℂ) • x := by
    rw [CuspSub.locRep_eq, hz]
    have := hω (Units.map (corner (sLoc E w)) u) x
    change _ = ((ω.1 (finId E (Units.map (corner (sLoc E w)) u)) : ℂˣ) : ℂ) • x at this
    rw [hf] at this
    exact this
  rw [ht, h2] at h1
  have h3 : satEig (qV E w) a B a = ((B.prod : ℂˣ) : ℂ) := by
    have hc : (B.map fun b : ℂˣ => (b : ℂ)).card = a := by rw [Multiset.card_map]; exact hx.2.2.1
    rw [satEig, sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul]
    conv_lhs => rw [← hc]
    rw [Multiset.esymm, Multiset.powersetCard_self, Multiset.map_singleton, Multiset.sum_singleton]
    exact (map_multiset_prod (Units.coeHom ℂ) B).symm
  rw [h3] at h1
  exact Units.ext (smul_left_injective ℂ hx.1 h1)

theorem central_eq (hG : HeckeCharacterRigidity) {π π' : CuspSub E a} (h : SameSat π π') {ω ω' : HChar E} (hω : π.HasCentChar ω)
    (hω' : π'.HasCentChar ω') : ω = ω' :=
  hG E ω ω' (h.mono fun _ ⟨_, h1, h2⟩ => (val_eq_prod hω h1).trans (val_eq_prod hω' h2).symm)

theorem sameSat_twist {π π' : CuspSub E a} (h : SameSat π π') (ν : HChar E) : SameSat (π.twist ν) (π'.twist ν) := by
  filter_upwards [h, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ν)] with w ⟨B, h1, h2⟩ hν
  exact ⟨B.map (· * ν.val w), GlobalTheory.SphGal.hasSatGL_twist E a π ν w B hν h1,
    GlobalTheory.SphGal.hasSatGL_twist E a π' ν w B hν h2⟩

end PSmo

theorem smo_of : SmoNorm → HeckeCharacterRigidity → Smo := by
  intro hS hG E _ _ _ a π π' h
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact hS E 0 π π' (GlobalTheory.CompanionTheory.TwistNorm.isNormalised_rank_zero π) (GlobalTheory.CompanionTheory.TwistNorm.isNormalised_rank_zero π') h
  obtain ⟨ω, hω⟩ := Central.exists_hasCentral E a π
  obtain ⟨ω', hω'⟩ := Central.exists_hasCentral E a π'
  obtain rfl : ω = ω' := PSmo.central_eq hG h (CuspSub.hasCentral_iff.1 hω) (CuspSub.hasCentral_iff.1 hω')
  obtain ⟨ν, hν⟩ := GlobalTheory.SplitCentreChar.exists_hChar_splitCentre E a ha (dchi ω 1)
  have e := hS E a _ _ (GlobalTheory.CompanionTheory.TwistNorm.isNormalised_twist hω hν) (GlobalTheory.CompanionTheory.TwistNorm.isNormalised_twist hω' hν)
    (PSmo.sameSat_twist h ν)
  have e' := congrArg (fun σ : CuspSub E a => σ.twist ν⁻¹) e
  simpa only [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one] using e'

end PositivityTheory.jumpWindows

end

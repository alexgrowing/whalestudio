import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivSplitCentre
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec

namespace PositivityTheory.Rg.Rs.StrStepB

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem absC_unrAt (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) : (GlobalTheory.CuspRep.Model.absC E s).UnrAt w := by
  intro x hx
  apply Units.ext
  change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E w x)) = 1
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local w x 0 (by simpa [IsUnitAt] using hx)]
  simp

theorem absC_val (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) :
    (((GlobalTheory.CuspRep.Model.absC E s).val w : ℂˣ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s) := by
  change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E w (atFin w (unif w)))) = _
  have h0 : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local w _ 1 (unif_spec w), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
    ← Complex.natCast_log]
  congr 1; push_cast; ring

theorem absC_add (s t : ℂ) :
    GlobalTheory.CuspRep.Model.absC E (s + t) = GlobalTheory.CuspRep.Model.absC E s * GlobalTheory.CuspRep.Model.absC E t := by
  refine Subtype.ext (MonoidHom.ext fun x => Units.ext ?_)
  change Complex.exp ((s + t) * _) = Complex.exp (s * _) * Complex.exp (t * _)
  rw [← Complex.exp_add, add_mul]

theorem absC_zero : GlobalTheory.CuspRep.Model.absC E 0 = 1 := by
  refine Subtype.ext (MonoidHom.ext fun x => Units.ext ?_)
  change Complex.exp (0 * _) = 1
  simp

theorem hasSat_twist_absC {a : ℕ} (π : CuspSub E a) {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (h : (CG.mk π).HasSat w B) (x : ℂ) :
    ((CG.mk π).twist (GlobalTheory.CuspRep.Model.absC E x)).HasSat w (B.map (· * (GlobalTheory.CuspRep.Model.absC E x).val w)) :=
  GlobalTheory.SphGal.hasSatGL_twist E a π _ w B (absC_unrAt x w) h

abbrev dC (b : ℕ) : Lie E b := fun i j => if i = j then (1 : Cinf E) else 0

theorem lie_dC_eq_zero {b : ℕ} {ρ : CuspSub E b} (h : IsNormalised ρ) {φ : Sm E b} (hφ : φ ∈ ρ.V) :
    lie E b (dC b) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := GlobalTheory.CuspRep.SplitDeriv.hasDerivAt_splitCentre φ g 0
  have h2 : (fun t : ℝ => φ.1 (g * splitCentre E b t)) = fun _ => φ.1 g := funext fun t => by
    rw [← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm]; exact h φ hφ t g
  rw [h2, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_zero, mul_one] at h1
  rw [h1.unique (hasDerivAt_const 0 _)]
  rfl

theorem opAdd_dC (c : ℂ) (b : ℕ) :
    opAdd (GlobalTheory.CuspRep.Model.absC E c) (.lie (dC b) : Op E b) = c * (2 * b * Fintype.card (InfinitePlace E)) := by
  change dchi (GlobalTheory.CuspRep.Model.absC E c) (Matrix.of (dC (E := E) b)).trace = _
  rw [GlobalTheory.GKCoh.Tests.dchi_absC]
  have e : ∀ w, (Matrix.of (dC (E := E) b)).trace w = b := fun w => by
    simp [Matrix.trace, dC, Finset.sum_apply]
  simp only [e, Complex.natCast_re]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  ring

theorem eq_zero_of_iso_twist {b : ℕ} (hb : 1 ≤ b) {ρ ρ' : CuspSub E b} (h : IsNormalised ρ) (h' : IsNormalised ρ')
    {c : ℂ} (e : ρ.Iso (ρ'.twist (GlobalTheory.CuspRep.Model.absC E c))) : c = 0 := by
  obtain ⟨T, hT⟩ := e
  have := Submodule.nontrivial_iff_ne_bot.2 ρ.ne_bot
  obtain ⟨φ, hφ⟩ := exists_ne (0 : ρ.V)
  obtain ⟨ψ, hψ⟩ := (ρ'.toTwist (GlobalTheory.CuspRep.Model.absC E c)).surjective (T φ)
  have h1 := hT (.lie (dC b)) φ
  have h2 : ρ.op (.lie (dC b)) φ = 0 := Subtype.ext (lie_dC_eq_zero h φ.2)
  have h3 : ρ'.op (.lie (dC b)) ψ = 0 := Subtype.ext (lie_dC_eq_zero h' ψ.2)
  rw [h2, map_zero, ← hψ, CuspSub.op_toTwist, h3, opAdd_dC, smul_zero, zero_add] at h1
  have h4 : (c * (2 * b * Fintype.card (InfinitePlace E)) : ℂ) • ψ = 0 :=
    (ρ'.toTwist _).injective (h1.symm.trans (map_zero _).symm)
  have hψ0 : ψ ≠ 0 := fun e0 => hφ (T.injective (by rw [← hψ, e0, map_zero, map_zero]))
  have hK : (2 * b * Fintype.card (InfinitePlace E) : ℂ) ≠ 0 := by
    have : 0 < Fintype.card (InfinitePlace E) := Fintype.card_pos
    have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
    have hc' : (Fintype.card (InfinitePlace E) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
    exact mul_ne_zero (mul_ne_zero two_ne_zero hb') hc'
  rcases smul_eq_zero.1 h4 with h5 | h5
  · exact (mul_eq_zero.1 h5).resolve_right hK
  · exact absurd h5 hψ0

theorem match_twist {b b' : ℕ} (hb : 1 ≤ b) (ρ : CuspSub E b) (ρ' : CuspSub E b') (h : IsNormalised ρ)
    (h' : IsNormalised ρ') {u u' : ℂ}
    (e : (⟨b, (CG.mk ρ).twist (GlobalTheory.CuspRep.Model.absC E u)⟩ : Σ c, CG E c) =
      ⟨b', (CG.mk ρ').twist (GlobalTheory.CuspRep.Model.absC E u')⟩) :
    u = u' ∧ (⟨b, CG.mk ρ⟩ : Σ c, CG E c) = ⟨b', CG.mk ρ'⟩ := by
  obtain ⟨rfl, e2⟩ := Sigma.mk.inj_iff.1 e
  have e3 : CG.mk ρ = CG.mk (ρ'.twist (GlobalTheory.CuspRep.Model.absC E (u' - u))) := by
    have := congrArg (fun π : CG E b => π.twist (GlobalTheory.CuspRep.Model.absC E (-u))) (eq_of_heq e2)
    simp only [← CG.twist_mul, ← absC_add] at this
    rw [add_neg_cancel, absC_zero, CG.twist_one] at this
    rw [this, CG.twist_mk, sub_eq_add_neg]
  have hI : ρ.Iso (ρ'.twist (GlobalTheory.CuspRep.Model.absC E (u' - u))) := Quotient.exact e3
  have h0 := eq_zero_of_iso_twist hb h h' hI
  obtain rfl : u = u' := by linear_combination -h0
  refine ⟨rfl, ?_⟩
  rw [e3, sub_self, absC_zero, CuspSub.twist_one]

end PositivityTheory.Rg.Rs.StrStepB

end

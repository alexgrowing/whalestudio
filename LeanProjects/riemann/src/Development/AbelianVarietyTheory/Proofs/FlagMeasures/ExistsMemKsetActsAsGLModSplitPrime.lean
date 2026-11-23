import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSpec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtIdMulSupNatCastConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimeIdempotentIntegralAdelesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryStabilizerLiftOfSplitIdempotentStatement

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

theorem sigR_sigR_af (I : AutInst) (x : I.E ⊗[I.F] Af I.F) :
    Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.sigR I.cm.sig (Af I.F) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp [Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem isHerm_af (I : AutInst) :
    Formalism.UG.IsHerm (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) := by
  have hs : ∀ a : I.E, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) a) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by
    intro a
    simp [Formalism.UG.sigR, Formalism.UG.inclE, Formalism.BasicNotions.CMData.sig] <;> rfl
  have hJ := I.J_herm
  unfold Formalism.UG.IsHerm Formalism.UG.cT at hJ ⊢
  ext i j
  have h := congrArg (fun M => M i j) hJ
  simp only [Matrix.transpose_apply, Matrix.map_apply, starRingEnd_apply] at h ⊢
  rw [hs, h]

theorem isUnit_det_af (I : AutInst) : IsUnit (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).det := by
  have h : (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).det = Formalism.UG.inclE (F := I.F) (Af I.F) I.J.det :=
    (RingHom.map_det _ _).symm
  rw [h]
  exact (Ne.isUnit I.J_det).map _

theorem exists_mem_Kset_actsAs_trivial_away : ∀ (I : AutInst) (N p : ℕ) (w : HeightOneSpectrum (𝓞 I.E)) (fr : PlFrame I N p w), I.n = N → p.Prime → Ideal.absNorm w.asIdeal = p → ¬ IsConj I w w → ∀ M : GL (Fin N) (ZMod p), ∃ x ∈ I.Kset, (∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = (M : Matrix (Fin N) (Fin N) (ZMod p)) *ᵥ fr.c y) ∧ ∀ u : HeightOneSpectrum (𝓞 I.E), u ≠ w → ¬ IsConj I w u → ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ extId I u.asIdeal • I.Lf := by
  intro I N p w fr hN hp hw hw' M
  subst hN
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ε, hεε, h1ε, hεu, hεt, hεσ⟩ := GlobalTheory.T.exists_prime_idempotent_integralAdeles I w
  have hA := GlobalTheory.RowLev.intAf_approx_inter_unit_conj I 1 le_rfl
  have hL := GlobalTheory.AdelicLattice.adelicLattice_spec I 1 le_rfl
  have hX := GlobalTheory.RowLev.extId_mul_sup_natCast_conj I
  have hker : ∀ z, fr.r z = 0 ↔ z ∈ extId I w.asIdeal := fun z => by
    rw [← RingHom.mem_ker, fr.ker_r]
  have hrε : fr.r ε = 1 := by
    have h0 : fr.r (1 - ε) = 0 := (hker _).2 h1ε
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact h0.symm
  obtain ⟨x, hxU, hxS, hact, htriv⟩ := GlobalTheory.T.exists_unitary_stabilizer_lift_of_split_idempotent (I.E ⊗[I.F] Af I.F) (Formalism.UG.sigR I.cm.sig (Af I.F))
    (IntAf I.F I.E) I.n (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) I.Lf (ZMod p) fr.r fr.c ε
    (fun a => sigR_sigR_af I a) (fun a ha => hA.2.2.2 a ha) (isHerm_af I) (isUnit_det_af I)
    hL.2.2.2.1 hL.2.2.1 (fun y => GlobalTheory.AdelicLattice.adelicLattice_selfDual I y) hεε (hεσ hw') hrε
    (ZMod.ringHom_surjective fr.r) (fun z hz => hεt z fun h => hz ((hker z).2 h)) fr.c_surj
    (fun y hy => by rw [fr.ker_r]; exact (fr.c_ker y).1 hy) M
  refine ⟨⟨x, hxU⟩, hxS, fun y h => hact y h, ?_⟩
  intro u hu hcu y hy
  obtain ⟨z, hz, e⟩ := htriv y hy
  obtain ⟨u', hu'⟩ := hX.2.2.2.1 u
  have hu'w : u' ≠ w := by
    rintro rfl
    exact hcu (hX.2.2.2.2.1 u u' hu')
  obtain ⟨z', hz', hz'e⟩ := hX.2.2.2.2.2.2 u' u (hX.2.2.2.2.1 u u' hu') ε (hεu u' hu'w)
  have hmem : ε + z' ∈ extId I u.asIdeal := add_mem (hεu u hu) hz'
  have hfin : (I.fmat ⟨x, hxU⟩ - 1) *ᵥ y = (ε + z') • z := by
    change ((x : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) - 1) *ᵥ y = _
    rw [e, ← hz'e]
    rfl
  rw [hfin]
  exact Submodule.smul_mem_smul hmem hz

end GlobalTheory.RowLev

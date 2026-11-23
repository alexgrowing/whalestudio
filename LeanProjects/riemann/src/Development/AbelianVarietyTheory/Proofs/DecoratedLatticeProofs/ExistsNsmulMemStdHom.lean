import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.AdForm

variable {D : D7}

theorem coe_colStdLat (n : ℕ) :
    ((Formalism.L2.Col.stdLat D.host.E n : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = intVec D n := by
  ext x
  simp only [SetLike.mem_coe, Formalism.L2.Col.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact forall_congr' fun k => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun hy => ⟨⟨_, hy⟩, rfl⟩⟩

theorem exists_nsmul_mem_stdHom (S T : HSp D) : ∃ K : ℕ, 0 < K ∧ ∀ t : WO S T, t.map (infPart D) = 0 →
    (∀ i j, toEAf D (t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → K • t ∈ stdHom S T := by
  obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T)
    (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := S.rank)) (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := T.rank))
  refine ⟨K, hK, fun t ht hi => ?_⟩
  have := h t ht hi
  rwa [coe_colStdLat, coe_colStdLat] at this

theorem infPart_liftFin (x : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (GlobalTheory.LatticeStable.liftFin D x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, RingHom.map_zero]
  | tmul a m => exact GlobalTheory.LatVac.infPart_pair a m
  | add x y hx hy => rw [LinearMap.map_add, RingHom.map_add, hx, hy, add_zero]

theorem finPart_liftFin (x : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (GlobalTheory.LatticeStable.liftFin D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, RingHom.map_zero]
  | tmul a m => rfl
  | add x y hx hy => rw [LinearMap.map_add, RingHom.map_add, hx, hy]

theorem toEAf_eq_comm (z : AE D) :
    toEAf D z = Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D z) := rfl

theorem toEAf_liftFin (r : EAf D) :
    toEAf D (GlobalTheory.LatticeStable.liftFin D ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm r)) = r := by
  rw [toEAf_eq_comm, finPart_liftFin, AlgEquiv.apply_symm_apply]

theorem toEAf_approx_eq_zero (t L : AE D) (x : D.host.E) (M : ℕ) (r : EAf D)
    (ht : toEAf D t = eToEAf D x + (M : EAf D) * r) (hL : toEAf D L = -r) :
    toEAf D (incA D x - t - (M : AE D) * L) = 0 := by
  have hi : toEAf D (incA D x) = eToEAf D x := rfl
  rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, map_natCast, hi, ht, hL]
  ring

theorem approx_entry (t : AE D) (M : ℕ) (hM : 0 < M) : ∃ (x : D.host.E) (w : AE D), infPart D w = 0 ∧
    toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ finPart D (incA D x - t - (M : AE D) * w) = 0 := by
  have hM0 : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  obtain ⟨x, r, hr, e⟩ := GlobalTheory.AdeleBaseChange.exists_approx (F := D.host.F) (E := D.host.E)
    (eToEAf D (M : D.host.E)⁻¹ * toEAf D t)
  let c := Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E
  refine ⟨M * x, GlobalTheory.LatticeStable.liftFin D (c.symm (-r)), infPart_liftFin _, ?_, ?_⟩
  · rw [toEAf_liftFin]
    exact neg_mem hr
  · have ht : toEAf D t = eToEAf D (M * x) + (M : EAf D) * r := by
      have e2 := congrArg (eToEAf D (M : D.host.E) * ·) e
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul] at e2
      rw [e2, map_mul, map_natCast, mul_add]
      rfl
    have hz := toEAf_approx_eq_zero t _ (M * x) M r ht (toEAf_liftFin (-r))
    rw [toEAf_eq_comm] at hz
    exact c.injective (hz.trans (map_zero c).symm)

theorem exists_rat_half_approx : ∀ {D : D7} (S T : HSp D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → ∀ (N : ℕ), 0 < N → ∀ y : WO S T, ∃ (γ₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (v : WO S T), v ∈ stdHom S T ∧ IsHalf e v ∧ γ₀.map (fun r => e * incA D r) = e • y + N • v := by
  intro D S T e P he N hN y
  obtain ⟨K, hK, hKm⟩ := exists_nsmul_mem_stdHom S T
  choose x w hw0 hwi hz using fun i j => approx_entry (y i j) (N * K) (Nat.mul_pos hN hK)
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hKw : K • (Matrix.of fun i j => w i j) ∈ stdHom S T := hKm _ (Matrix.ext fun i j => hw0 i j) hwi
  refine ⟨Matrix.of x, e • (K • Matrix.of fun i j => w i j), ?_, ?_, ?_⟩
  · exact GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hee])) _ hKw
  · intro i j
    change e * (e * _) = e * _
    rw [← mul_assoc, hee]
  · ext i j
    have h0 : e * (incA D (x i j) - y i j - ((N * K : ℕ) : AE D) * w i j) = 0 := by
      refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_
      · rw [map_mul, hinf, zero_mul]
      · rw [map_mul, hz i j, mul_zero]
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
    push_cast at h0
    linear_combination h0

end GlobalTheory.AdForm

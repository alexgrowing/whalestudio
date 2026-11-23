import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDualStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateHalfPrescribedAdjointFrameMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeHalfIffFrameMatrixIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToEAfOrientedHermitianFormEqTraceFrames
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ScalarSelfDual

theorem eq_of_parts {D : D7} {x y : AE D} (hx : infPart D x = 0) (hy : infPart D y = 0)
    (h : toEAf D x = toEAf D y) : x = y := by
  rw [← sub_eq_zero]
  refine GlobalTheory.LatVac.eq_zero_of_parts _ (by rw [map_sub, hx, hy, sub_zero]) ?_
  rw [map_sub, sub_eq_zero]
  exact (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h

theorem mul_hO_of_half {D : D7} {S T : HSp D} {e : AE D} {l : WO S T} (hl : IsHalf e l) (u : WO S T) :
    e * hO S T l u = hO S T l u := by
  unfold hO
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  rw [mul_left_comm, hl d a]

set_option maxHeartbeats 800000 in

theorem exists_half_frMapO {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {e : AE D} (hee : e * e = e) (z : Matrix (Fin T.rank) (Fin S.rank) (EAf D))
    (hz : ∀ i j, toEAf D e * z i j = z i j) :
    ∃ y : WO S T, IsHalf e y ∧ frMapO S T βS βT y = z := by
  choose L hL0 hL using fun t : EAf D => GlobalTheory.HalfDuality.exists_lift (D := D) t
  let N : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := HMul.hMul (HMul.hMul βT.val z) (βS⁻¹).val
  refine ⟨Matrix.of fun i j => e * L (N i j), fun i j => ?_, ?_⟩
  · simp only [Matrix.of_apply, ← mul_assoc, hee]
  · have hY : ((Matrix.of fun i j => e * L (N i j) : WO S T).map (toEAf D)) = toEAf D e • N := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply, map_mul, hL, Matrix.smul_apply, smul_eq_mul]
    have h1 : HMul.hMul (βT⁻¹).val βT.val = (1 : Matrix (Fin T.rank) (Fin T.rank) (EAf D)) := Units.inv_mul βT
    have h2 : HMul.hMul (βS⁻¹).val βS.val = (1 : Matrix (Fin S.rank) (Fin S.rank) (EAf D)) := Units.inv_mul βS
    have e1 : HMul.hMul (HMul.hMul (βT⁻¹).val N) βS.val = z := by
      simp only [N, Matrix.mul_assoc]
      rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    unfold frMapO
    rw [hY, Matrix.mul_smul, Matrix.smul_mul, e1]
    exact Matrix.ext fun i j => hz i j

theorem frMapO_half {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {e : AE D} {l : WO S T} (hl : IsHalf e l) (i : Fin T.rank) (j : Fin S.rank) :
    toEAf D e * frMapO S T βS βT l i j = frMapO S T βS βT l i j := by
  have hY : toEAf D e • (l.map (toEAf D)) = l.map (toEAf D) := by
    ext i j
    rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, ← map_mul, hl i j]
  have : toEAf D e • frMapO S T βS βT l = frMapO S T βS βT l := by
    unfold frMapO
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hY]
  exact congrFun (congrFun this i) j

theorem trace_single_mul' {R : Type} [CommRing R] {m n : ℕ} (i : Fin m) (j : Fin n) (a : R)
    (M : Matrix (Fin n) (Fin m) R) : Matrix.trace (Matrix.single i j a * M) = a * M j i := by
  rw [Matrix.trace_single_mul, smul_eq_mul]

set_option maxHeartbeats 1600000 in

theorem int_iff_dual : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → 0 < S.rank → 0 < T.rank → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → (∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ Z : AE D, e * Z = Z → (toEAf D Z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ Z' : AE D, e * Z' = Z' → toEAf D Z' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (Z * Z'))) = 1) := by
  intro D ψ S T ΛS ΛT βS βT hψ hS hT hfS hfT hs ht Q e he hQ Z hZ
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hfin : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  have hsupp : ∀ x : AE D, e * x = x → infPart D x = 0 := fun x hx => by
    rw [← hx, map_mul, hinf, zero_mul]
  let i₀ : Fin S.rank := ⟨0, hs⟩
  let j₀ : Fin T.rank := ⟨0, ht⟩
  have hsingle : ∀ {m n : ℕ} (i : Fin m) (j : Fin n) (x : AE D), e * x = x → ∀ a b,
      toEAf D e * Matrix.single i j (toEAf D x) a b = Matrix.single i j (toEAf D x) a b := by
    intro m n i j x hx a b
    simp only [Matrix.single_apply]
    split_ifs
    · rw [← map_mul, hx]
    · rw [mul_zero]
  have hint : ∀ {m n : ℕ} (i : Fin m) (j : Fin n) (x : EAf D),
      IsIntM (Matrix.single i j x) ↔ x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro m n i j x
    constructor
    · intro h
      have := h i j
      rwa [Matrix.single_apply_same] at this
    · intro h a b
      simp only [Matrix.single_apply]
      split_ifs
      · exact h
      · exact zero_mem _
  obtain ⟨u, hu, -, huZ⟩ := GlobalTheory.T.exists_conjugateHalf_prescribed_adjoint_frameMatrix D S T βS βT e hee (Matrix.single i₀ j₀ (toEAf D Z)) (hsingle i₀ j₀ Z hZ)
  have hval : ∀ (l : WO S T) (Z' : AE D), IsHalf e l → e * Z' = Z' → toEAf D Z' = frMapO S T βS βT l j₀ i₀ →
      symplO S T l u = Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (Z * Z')) := by
    intro l Z' hl hZ' h
    have : hO S T l u = Z * Z' := by
      refine eq_of_parts (hsupp _ (mul_hO_of_half hl u)) (by rw [map_mul, hsupp Z hZ, zero_mul]) ?_
      rw [GlobalTheory.TraceFrames.toEAf_hO_eq_trace_frames S T βS βT u l, huZ, trace_single_mul', map_mul, h]
    unfold symplO
    rw [this]
  have h1 : toEAf D Z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ u ∈ latO S T ΛS ΛT (fun _ => True) := by
    rw [← hint i₀ j₀, ← huZ]
    exact ⟨GlobalTheory.HalfAdjLattice.mem_latO_of_adj_int D S T ΛS ΛT βS βT hS hT hfS hfT Q e he hQ u hu,
      fun h => GlobalTheory.HalfAdjInt.frMapAdj_int_of_half D S T ΛS ΛT βS βT hS hT hfS hfT Q e he hQ u h hu⟩
  rw [h1, GlobalTheory.T.mem_completedLattice_conjugateHalf_iff_dual D ψ S T ΛS ΛT hψ hS hT e hee he.2 hinf hfin u hu]
  constructor
  · intro h Z' hZ' hZi
    obtain ⟨l, hl, hlZ⟩ := exists_half_frMapO S T βS βT hee (Matrix.single j₀ i₀ (toEAf D Z')) (hsingle j₀ i₀ Z' hZ')
    rw [← hval l Z' hl hZ' (by rw [hlZ, Matrix.single_apply_same])]
    refine h l ((GlobalTheory.T.mem_completedLattice_half_iff_frameMatrix_integral D S T ΛS ΛT βS βT hS hT hfS hfT Q e he hQ l hl).2 ?_) hl
    rw [hlZ, hint]
    exact hZi
  · intro h l hlm hl
    have hI := (GlobalTheory.T.mem_completedLattice_half_iff_frameMatrix_integral D S T ΛS ΛT βS βT hS hT hfS hfT Q e he hQ l hl).1 hlm
    obtain ⟨Y, -, hY⟩ := GlobalTheory.HalfDuality.exists_lift (D := D) (frMapO S T βS βT l j₀ i₀)
    have hZ' : e * (e * Y) = e * Y := by rw [← mul_assoc, hee]
    have hE : toEAf D (e * Y) = frMapO S T βS βT l j₀ i₀ := by
      rw [map_mul, hY, frMapO_half βS βT hl]
    rw [hval l (e * Y) hl hZ' hE]
    exact h _ hZ' (by rw [hE]; exact hI j₀ i₀)

end GlobalTheory.ScalarSelfDual

import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.MtHeckeSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStOneOfInt
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.R3.LiftBrg.EtaInvLat

theorem mat_mul_mem {R : Type} [CommRing R] (I : Subring R) {m : Type} [Fintype m]
    {A B : Matrix m m R} (hA : ∀ i j, A i j ∈ I) (hB : ∀ i j, B i j ∈ I) :
    ∀ i j, (A * B) i j ∈ I := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem mulVec_mem {R : Type} [CommRing R] (I : Subring R) {m : Type} [Fintype m]
    {A : Matrix m m R} {y : m → R} (hA : ∀ i j, A i j ∈ I) (hy : ∀ j, y j ∈ I) :
    ∀ i, (A *ᵥ y) i ∈ I := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hy k)

theorem conj_mulVec_mem {R : Type} [CommRing R] (I : Subring R) {m : Type} [Fintype m]
    {C N Ci : Matrix m m R} (hC : ∀ i j, C i j ∈ I) (hCi : ∀ i j, Ci i j ∈ I) (s : R)
    (hN : ∀ i j, s * N i j ∈ I) {y : m → R} (hy : ∀ j, y j ∈ I) (a : m) :
    s * ((C * N * Ci) *ᵥ y) a ∈ I := by
  have h : s * ((C * N * Ci) *ᵥ y) a = ((C * (s • N) * Ci) *ᵥ y) a := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec]
    simp [Pi.smul_apply, smul_eq_mul]
  rw [h]
  refine mulVec_mem I (mat_mul_mem I (mat_mul_mem I hC (fun i j => ?_)) hCi) hy a
  simpa [Matrix.smul_apply, smul_eq_mul] using hN i j

end GlobalTheory.Mem.R3.LiftBrg.EtaInvLat

namespace GlobalTheory.Mem.R3.LiftBrg.EtaInvLat

set_option maxHeartbeats 2000000 in

theorem eta_inv_lat : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → (∀ z : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v z = 0 → swapAE D (finPart D e) * z = 0) → (∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, y ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ j, swapAE D (y j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → C ∈ Formalism.L2.DIV.St 1 → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ →
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, (fun a => finPart D e * (finMat D.sp.cm.sig V.gram α⁻¹).mulVec y a) ∈ Formalism.L2.NTheta.LamHat V) ∧
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z ∈ Formalism.L2.NTheta.LamHat V, (fun a => finPart D e * (finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y a)) =
      fun a => finPart D e * (finMat D.sp.cm.sig V.gram α⁻¹).mulVec z a) := by
  intro D V n _ h v Pb Ut d e C α hI hV hL hC hα hg
  subst h
  rw [GlobalTheory.Mem.R3.LiftBrg.StdFrame.castGL_rfl] at hg
  have hee : e * e = e := hI.1.1
  have hεI : swapAE D (finPart D e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    (GlobalTheory.IdemSupport.mem_intAE_iff _).1 (GlobalTheory.SplitPlace.idem_mem hee)
  have hiA : ∀ x : 𝓞 D.host.E, Formalism.L2.Col.iA D.host.F D.host.E (algebraMap (𝓞 D.host.E) D.host.E x) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := fun x => Formalism.L2.Col.iA_mem x
  have hπ0 : algebraMap (𝓞 D.host.E) D.host.E Ut.π ≠ 0 := by
    rw [← map_zero (algebraMap (𝓞 D.host.E) D.host.E)]
    exact (IsFractionRing.injective (𝓞 D.host.E) D.host.E).ne Ut.hπ0
  have hsπ0 : star (algebraMap (𝓞 D.host.E) D.host.E Ut.π) ≠ 0 := star_ne_zero.mpr hπ0
  have hπinv : swapAE D (finPart D e) * Formalism.L2.Col.iA D.host.F D.host.E (algebraMap (𝓞 D.host.E) D.host.E Ut.π)⁻¹ ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have h1 := not_not.mp ((hI.2 Ut.π Ut.hπ0).not.mp Ut.hπP)
    have h2 := (GlobalTheory.IdemSupport.mem_intAE_iff _).1 h1
    rw [map_mul, map_mul] at h2
    exact h2
  have hstar : star (algebraMap (𝓞 D.host.E) D.host.E Ut.π) =
      algebraMap (𝓞 D.host.E) D.host.E (Formalism.L2.Col.cO D.host.E Ut.π) := rfl
  have hCC := (Formalism.L2.Col.rll_mem_St_iff _ C).1 hC
  obtain ⟨η, hη⟩ : ∃ η : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D),
      η = ((Formalism.L2.Col.mhlEta D.sp.cm V.rank v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm V.rank) : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) :=
    ⟨_, rfl⟩
  rw [← hη] at hg
  have hprη : ∀ i j, Formalism.UG.prV v ((Units.val η) i j) =
      Formalism.UG.prV v (Formalism.L2.Col.iA D.host.F D.host.E (if i = j then Formalism.L2.Col.mhlDiag V.rank Ut.π d i else 0)) := by
    intro i j
    have := congrArg (fun g : GL (Fin V.rank) (D.host.E ⊗[D.host.F] HeightOneSpectrum.adicCompletion D.host.F v) => (Units.val g) i j) (Formalism.L2.Col.rll_put_self (F := D.host.F) (E := D.host.E) V.rank v
      ((Formalism.UG.bc (Formalism.UG.prV v)) ((Formalism.UG.bc (Formalism.L2.Col.iA D.host.F D.host.E)) (Formalism.L2.Col.mhlD V.rank Ut.hπ0 d))))
    rw [hη]
    exact this
  have hV' : ∀ a b : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v a = Formalism.UG.prV v b →
      swapAE D (finPart D e) * a = swapAE D (finPart D e) * b := by
    intro a b hab
    have h0 := hV (a - b) (by
      rw [map_sub, sub_eq_zero]
      exact hab)
    rw [mul_sub] at h0
    exact sub_eq_zero.mp h0
  have hεη : ∀ i j, swapAE D (finPart D e) * (Units.val η) i j =
      swapAE D (finPart D e) * Formalism.L2.Col.iA D.host.F D.host.E (if i = j then Formalism.L2.Col.mhlDiag V.rank Ut.π d i else 0) :=
    fun i j => hV' _ _ (hprη i j)
  have hεηi : ∀ i j, swapAE D (finPart D e) * (Units.val η⁻¹) i j =
      swapAE D (finPart D e) * Formalism.L2.Col.iA D.host.F D.host.E (if i = j then (Formalism.L2.Col.mhlDiag V.rank Ut.π d i)⁻¹ else 0) :=
    fun i j => hV' _ _ (by rw [hη]; exact Formalism.L2.Col.mhl_prV_eta_inv _ _ _ _ _ _)
  have hN1 : ∀ i j, swapAE D (finPart D e) * (Units.val η⁻¹) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j
    rw [hεηi]
    split_ifs with hij
    · simp only [Formalism.L2.Col.mhlDiag]
      split_ifs
      · rw [Formalism.L2.Col.mhlA, _root_.mul_inv_rev, inv_inv, map_mul, mul_left_comm]
        exact Subring.mul_mem _ (hstar ▸ hiA _) hπinv
      · rw [inv_one, map_one, mul_one]
        exact hεI
    · rw [map_zero, mul_zero]
      exact Subring.zero_mem _
  have hN2 : ∀ i j, (swapAE D (finPart D e) * Formalism.L2.Col.iA D.host.F D.host.E (star (algebraMap (𝓞 D.host.E) D.host.E Ut.π))) *
      (Units.val η) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j
    rw [mul_right_comm, hεη]
    split_ifs with hij
    · simp only [Formalism.L2.Col.mhlDiag]
      split_ifs
      · rw [Formalism.L2.Col.mhlA, mul_assoc, ← map_mul, mul_assoc, inv_mul_cancel₀ hsπ0, mul_one]
        exact Subring.mul_mem _ hεI (hiA _)
      · rw [map_one, mul_one]
        exact Subring.mul_mem _ hεI (hstar ▸ hiA _)
    · rw [map_zero, mul_zero, zero_mul]
      exact Subring.zero_mem _
  have hT : ∀ (β : GA D V) (w : Fin V.rank → GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (a : Fin V.rank),
      swapAE D ((finMat D.sp.cm.sig V.gram β *ᵥ w) a) =
        ((Units.val (Formalism.UG.bc (swapAE D) (finHom V β))) *ᵥ (fun b => swapAE D (w b))) a := by
    intro β w a
    rw [RingHom.map_mulVec]
    rfl
  have hgi : Formalism.UG.bc (swapAE D) (finHom V α⁻¹) = C * η⁻¹ * C⁻¹ := by
    rw [map_inv, map_inv, hg]
    group
  have hinv : finMat D.sp.cm.sig V.gram α⁻¹ * finMat D.sp.cm.sig V.gram α = 1 := by
    show Units.val (finHom V α⁻¹) * Units.val (finHom V α) = 1
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [hL] at hy ⊢
    intro a
    show swapAE D (finPart D e * _) ∈ _
    rw [map_mul, hT, hgi, Units.val_mul, Units.val_mul]
    exact conj_mulVec_mem _ hCC.1 hCC.2 _ hN1 hy a
  · refine ⟨fun a => finPart D e * (finMat D.sp.cm.sig V.gram α *ᵥ
      (fun b => finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y b)) a, ?_, ?_⟩
    · rw [hL] at hy ⊢
      intro a
      show swapAE D (finPart D e * _) ∈ _
      rw [map_mul, hT, hg, Units.val_mul, Units.val_mul]
      have hw : (fun b => swapAE D (finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y b)) =
          (Formalism.L2.Col.iA D.host.F D.host.E (star (algebraMap (𝓞 D.host.E) D.host.E Ut.π))) • (fun b => swapAE D (y b)) := by
        funext b
        rw [map_mul]
        rfl
      rw [hw, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc]
      exact conj_mulVec_mem _ hCC.1 hCC.2 _ hN2 hy a
    · have hz : (fun a => finPart D e * (finMat D.sp.cm.sig V.gram α *ᵥ
          (fun b => finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y b)) a) =
          finPart D e • (finMat D.sp.cm.sig V.gram α *ᵥ
          (fun b => finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y b)) := rfl
      rw [hz, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      funext a
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc (finPart D e) (finPart D e), ← map_mul, hee]

end GlobalTheory.Mem.R3.LiftBrg.EtaInvLat

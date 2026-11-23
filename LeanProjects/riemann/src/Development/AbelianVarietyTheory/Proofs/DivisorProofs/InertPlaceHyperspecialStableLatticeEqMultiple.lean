import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicUnitarySupportedAtFinitePlaceEqLocalUnitarStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StabilisesCompletedLatticeIffLocalMatrixIntegralStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplexConjIsometryInertCompletionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTensorInertAdicCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeEqZpowStdInertCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderCompletionSurjectiveFromIntegralAdelesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.InertLatMult

open GlobalTheory.PlaceComp GlobalTheory.SelfDualGenus

variable {D : D7} {n : ℕ}

def coord (v : HeightOneSpectrum (𝓞 D.host.F)) {K : Type} [CommRing K]
    (h : GL (Fin n) (Fv D.host.F v ⊗[D.host.F] D.host.E)) (ψ : (Fv D.host.F v ⊗[D.host.F] D.host.E) →+* K) :
    (Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin n → K) where
  toFun z i := ψ (((h⁻¹).1 *ᵥ fun j => evF D.host.E v (z j)) i)
  map_zero' := by
    funext i
    show ψ (((h⁻¹).1 *ᵥ fun j => evF D.host.E v ((0 : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) j)) i) = 0
    have : (fun j => evF D.host.E v ((0 : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) j)) = 0 :=
      funext fun j => map_zero _
    rw [this, Matrix.mulVec_zero, Pi.zero_apply, map_zero]
  map_add' a b := by
    funext i
    show ψ (((h⁻¹).1 *ᵥ fun j => evF D.host.E v ((a + b) j)) i) =
      ψ (((h⁻¹).1 *ᵥ fun j => evF D.host.E v (a j)) i) + ψ (((h⁻¹).1 *ᵥ fun j => evF D.host.E v (b j)) i)
    have : (fun j => evF D.host.E v ((a + b) j)) = (fun j => evF D.host.E v (a j)) + fun j => evF D.host.E v (b j) :=
      funext fun j => map_add _ _ _
    rw [this, Matrix.mulVec_add, Pi.add_apply, map_add]

section Coord

variable (v : HeightOneSpectrum (𝓞 D.host.F)) {K : Type} [CommRing K]
    (h : GL (Fin n) (Fv D.host.F v ⊗[D.host.F] D.host.E)) (ψ : (Fv D.host.F v ⊗[D.host.F] D.host.E) →+* K)

theorem coord_apply (z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (i : Fin n) :
    coord v h ψ z i = ψ (((h⁻¹).1 *ᵥ fun j => evF D.host.E v (z j)) i) := rfl

theorem coord_mul (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
    (z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    coord v h ψ (fun i => t * z i) = fun i => ψ (evF D.host.E v t) * coord v h ψ z i := by
  funext i
  have e : (fun j => evF D.host.E v (t * z j)) = evF D.host.E v t • fun j => evF D.host.E v (z j) := by
    funext j
    simp [map_mul]
  rw [coord_apply, coord_apply, e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]

theorem coord_mulVec (A : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    coord v h ψ (A *ᵥ z) = ((h⁻¹).1 * A.map (evF D.host.E v) * h.1).map ψ *ᵥ coord v h ψ z := by
  funext i
  have e1 : (fun j => evF D.host.E v ((A *ᵥ z) j)) = A.map (evF D.host.E v) *ᵥ fun j => evF D.host.E v (z j) :=
    funext fun j => RingHom.map_mulVec _ _ _ j
  have e2 : (h⁻¹).1 *ᵥ (A.map (evF D.host.E v) *ᵥ fun j => evF D.host.E v (z j)) =
      ((h⁻¹).1 * A.map (evF D.host.E v) * h.1) *ᵥ ((h⁻¹).1 *ᵥ fun j => evF D.host.E v (z j)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [coord_apply, e1, e2, RingHom.map_mulVec]
  rfl

end Coord

end GlobalTheory.InertLatMult

set_option maxHeartbeats 2000000 in

open GlobalTheory.PlaceComp GlobalTheory.SelfDualGenus GlobalTheory.InertLatMult in

theorem GlobalTheory.InertLatMult.lattice_eq_mult : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : Formalism.L2.Theta.AE D), (∃ v ε, IsPlaceIdem D v ε ∧ e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε) → (∀ x : 𝓞 D.host.E, x ≠ 0 → (x ∈ P.asIdeal ↔ finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D)) → ∀ (M : AddSubgroup (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))), (∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M) → (∀ z ∈ M, finPart D (e) • z = z) → (∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (finPart D (e) • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V) → (∀ g : GA D V, g ∈ KsphC V ∅ → SuppF V (e) g → ∀ z ∈ M, (finMat D.sp.cm.sig V.gram g).mulVec z ∈ M) → ∃ c : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), IsUnit c ∧ ∀ z, z ∈ M ↔ (finPart D (e) • z = z ∧ c • z ∈ Formalism.L2.NTheta.LamHat V) := by
  intro D V P e he hP M hMa hMe hN hG
  obtain ⟨v, ε, ⟨α, rfl, a1, a2⟩, rfl⟩ := he
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hI := GlobalTheory.PlaceComp.isIdemOf_algebraMap (E := D.host.E) a1 a2
  obtain ⟨x0, y, hy, hy1, hy2⟩ := GlobalTheory.SphLabelOps.exists_real_unif D P
  have hin := GlobalTheory.InertDoubleCoset.inert_of_idem (E := D.host.E) hI hP ⟨x0, y, hy, hy1, hy2⟩
  haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  obtain ⟨σ, π, hσE, hσσ, hσv, hσx, hσπ, hπ⟩ := GlobalTheory.T.exists_complexConj_isometry_inert_completion D.host.E v P hin
  obtain ⟨ψ, hψE, hψσ, hψO⟩ := GlobalTheory.T.exists_ringEquiv_tensor_inert_adicCompletion D.host.E v P hin σ hσE hσv
  obtain ⟨h, hfr, hon⟩ := GlobalTheory.PlaceComp.exists_orthonormal D.sp.cm V v
  obtain ⟨s1, -, s3⟩ := GlobalTheory.T.adelicUnitary_supportedAtFinitePlace_eq_localUnitary _ D.host.E D.sp.cm V v _ hI
  set e : Formalism.L2.Theta.AE D := algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (pairA D.host.F 0 α) with he_def
  set fe := finPart D e with hfe_def
  let ψ' : (Fv D.host.F v ⊗[D.host.F] D.host.E) →+* P.adicCompletion D.host.E := ψ
  let X := coord (D := D) (n := V.rank) v h ψ'
  have hfe1 : evF D.host.E v fe = 1 := hI.2.1
  have hfe0 : ∀ w, w ≠ v → evF D.host.E w fe = 0 := hI.2.2
  have hfe : fe * fe = fe := evF_ext fun w => by
    by_cases hw : w = v
    · subst hw; rw [map_mul, hfe1, mul_one]
    · rw [map_mul, hfe0 w hw, mul_zero]

  have supp0 : ∀ z : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ i, fe * z i = z i) → ∀ w, w ≠ v → ∀ i, evF D.host.E w (z i) = 0 := fun z hz w hw i => by
    rw [← hz i, map_mul, hfe0 w hw, zero_mul]
  have hinj : ∀ z z' : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ i, fe * z i = z i) → (∀ i, fe * z' i = z' i) → X z = X z' → z = z' := by
    intro z z' hz hz' e0
    have e1 : ((h⁻¹).1 *ᵥ fun j => evF D.host.E v (z j)) = ((h⁻¹).1 *ᵥ fun j => evF D.host.E v (z' j)) :=
      funext fun i => ψ.injective (congrFun e0 i)
    have e2 : (fun j => evF D.host.E v (z j)) = (fun j => evF D.host.E v (z' j)) := by
      have := congrArg (fun w => h.1 *ᵥ w) e1
      simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] using this
    funext i
    refine evF_ext fun w => ?_
    by_cases hw : w = v
    · subst hw; exact congrFun e2 i
    · rw [supp0 z hz w hw i, supp0 z' hz' w hw i]
  have hsurj : ∀ w : Fin V.rank → P.adicCompletion D.host.E, ∃ z, (∀ i, fe * z i = z i) ∧ X z = w := by
    intro w
    refine ⟨fun j => sgT D.host.E v ((h.1 *ᵥ fun i => ψ.symm (w i)) j), fun i => ?_, ?_⟩
    · refine evF_ext fun u => ?_
      by_cases hu : u = v
      · subst hu; rw [map_mul, hfe1, one_mul]
      · rw [map_mul, hfe0 u hu, zero_mul, evF_sgT_ne hu]
    · funext i
      show ψ (((h⁻¹).1 *ᵥ fun j => evF D.host.E v (sgT D.host.E v ((h.1 *ᵥ fun i => ψ.symm (w i)) j))) i) = w i
      simp only [evF_sgT_self]
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      exact ψ.apply_symm_apply _
  have hmem : ∀ z : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ i, fe * z i = z i) → (z ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ i, Valued.v (X z i) ≤ 1) := by
    intro z hz
    show z ∈ GlobalTheory.PlaceComp.lamHat D.host.F V ↔ _
    rw [mem_lamHat_iff]
    constructor
    · intro hl i
      have := ((hfr _).1 (hl v)) i
      rw [mem_ordAt_iff, hψO] at this
      exact this
    · intro hl w
      by_cases hw : w = v
      · subst hw
        refine (hfr _).2 fun i => ?_
        rw [mem_ordAt_iff, hψO]
        exact hl i
      · have : (fun i => evF D.host.E w (z i)) = 0 := funext fun i => supp0 z hz w hw i
        rw [this]
        exact zero_mem _

  have hback : ∀ x : GL (Fin V.rank) (P.adicCompletion D.host.E),
      Formalism.UG.bc ψ' (Formalism.UG.bc (ψ.symm : P.adicCompletion D.host.E →+* LocAlg v) x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => ψ.apply_symm_apply _)
  have hO : ∀ z, z ∈ ordAt D.host.E v ↔ ψ' z ∈ Formalism.UG.Ov D.host.E P := fun z =>
    (mem_ordAt_iff v z).trans ((hψO z).trans (P.mem_adicCompletionIntegers (K := D.host.E)).symm)
  have hlift : ∀ U : GL (Fin V.rank) (P.adicCompletion D.host.E), U ∈ Formalism.UG.UJ σ 1 →
      (∀ i j, Valued.v (U.1 i j) ≤ 1) → (∀ i j, Valued.v ((U⁻¹).1 i j) ≤ 1) →
      ∃ g : GA D V, g ∈ KsphC V ∅ ∧ SuppF V e g ∧ ∀ z, X (finMat D.sp.cm.sig V.gram g *ᵥ z) = U.1 *ᵥ X z := by
    intro U hU i1 i2
    have h1 := GlobalTheory.InertDoubleCoset.bc_mem_UJ_one (σ' := locConj v) (ψ.symm : P.adicCompletion D.host.E →+* LocAlg v)
      (fun z => ψ.injective (by
        rw [hψσ]
        exact (ψ.apply_symm_apply _).trans (congrArg σ (ψ.apply_symm_apply _).symm))) hU
    obtain ⟨k, hk, ek⟩ := s3 _ (GlobalTheory.InertDoubleCoset.conj_mem_UJ _ (GlobalTheory.InertDoubleCoset.inv_frame _ hon) h1)
    have hk1 := (s1 k).1 hk
    have hconj : h⁻¹ * locMat D.sp.cm V v k * h = Formalism.UG.bc (ψ.symm : P.adicCompletion D.host.E →+* LocAlg v) U := by
      rw [ek]; group
    have hst : Stab D.sp.cm V k := by
      rw [GlobalTheory.T.stabilises_completedLattice_iff_localMatrix_integral _ D.host.E D.sp.cm V v h hfr k hk1.2, hconj,
        GlobalTheory.InertDoubleCoset.bc_mem_range_iff ψ' hO, hback, GlobalTheory.InertDoubleCoset.mem_range_iff]
      refine ⟨fun i j => (P.mem_adicCompletionIntegers (K := D.host.E)).2 (i1 i j),
        fun i j => (P.mem_adicCompletionIntegers (K := D.host.E)).2 (i2 i j)⟩
    refine ⟨k, (GlobalTheory.InertDoubleCoset.mem_KsphC_iff V k).2 ⟨hk1.1, hst⟩, hk, fun z => ?_⟩
    rw [coord_mulVec]
    congr 1
    have : (h⁻¹).1 * (finMat D.sp.cm.sig V.gram k).map (evF D.host.E v) * h.1 =
        (Formalism.UG.bc (ψ.symm : P.adicCompletion D.host.E →+* LocAlg v) U).1 := by
      rw [← hconj, ← locMat_val]; rfl
    rw [this]
    exact congrArg Units.val (hback U)

  have hsupM : ∀ z ∈ M, ∀ i, fe * z i = z i := fun z hz i => congrFun (hMe z hz) i
  have hint : ∀ a : P.adicCompletion D.host.E, Valued.v a ≤ 1 → ∃ t ∈ intAE D, ψ' (evF D.host.E v t) = a := by
    intro a ha
    have h0 : ψ.symm a ∈ ordAt D.host.E v := (mem_ordAt_iff v _).2 ((hψO _).2 (by rwa [ψ.apply_symm_apply]))
    obtain ⟨t, ht, et⟩ := GlobalTheory.T.localOrderCompletion_surjective_from_integralAdeles D.host.F D.host.E v _ h0
    exact ⟨t, ht, by show ψ (evF D.host.E v t) = a; rw [et]; exact ψ.apply_symm_apply a⟩
  have hinc : ∀ x : D.host.E, ψ' (evF D.host.E v (finPart D (incA D x))) = algebraMap D.host.E _ x := fun x => by
    show ψ _ = _
    rw [show finPart D (incA D x) = finP D.host.F D.host.E (inclR (AF D.host.F) x) from rfl, evF_finP_incl]
    exact hψE x
  let L : AddSubgroup (Fin V.rank → P.adicCompletion D.host.E) := M.map X
  have hLmem : ∀ z, (∀ i, fe * z i = z i) → (X z ∈ L ↔ z ∈ M) := fun z hz =>
    ⟨fun ⟨z', hz', e0⟩ => (hinj z' z (hsupM z' hz') hz e0) ▸ hz', fun hzM => ⟨z, hzM, rfl⟩⟩
  have hsmul : ∀ (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (z : Fin V.rank → _),
      (∀ i, fe * z i = z i) → ∀ i, fe * (t * z i) = t * z i := fun t z hz i => by
    rw [mul_left_comm, hz i]
  obtain ⟨N, hNpos, hN1, hN2⟩ := hN
  have hNc : ψ' (evF D.host.E v ((N : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) =
      ((N : ℕ) : P.adicCompletion D.host.E) := by
    rw [map_natCast, map_natCast]
  have hN0 : ((N : ℕ) : P.adicCompletion D.host.E) ≠ 0 := by
    rw [← map_natCast (algebraMap D.host.E (P.adicCompletion D.host.E))]
    exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 hNpos.ne')
  have hyv : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (y : D.host.E)) = WithZero.exp (-1 : ℤ) := by
    rw [GlobalTheory.Idele.valued_algebraMap, ← GlobalTheory.UnramCompletion.intValuation_eq_of_notMem_sq P hy1 hy2]
    exact HeightOneSpectrum.valuation_of_algebraMap P y
  obtain ⟨k, hk⟩ := GlobalTheory.T.stable_lattice_eq_zpow_std_inert_completion D.host.E P σ hσσ hσv hσx _ hyv V.rank L _ hN0
    (by
      rintro a ha _ ⟨z, hz, rfl⟩
      obtain ⟨t, ht, et⟩ := hint a ha
      refine ⟨fun i => t * z i, hMa t ht z hz, ?_⟩
      show X (fun i => t * z i) = a • X z
      rw [coord_mul]
      funext i
      rw [et]; rfl)
    (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := hsurj w
      have h1 := hN1 z ((hmem z hz).2 hw)
      have h2 : (finPart D e • z) = z := funext hz
      rw [h2] at h1
      refine ⟨_, h1, ?_⟩
      show X (fun i => ((N : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) * z i) = _
      rw [coord_mul, hNc]
      rfl)
    (by
      rintro _ ⟨z, hz, rfl⟩ i
      have h1 := (hmem _ (hsmul _ z (hsupM z hz))).1 (hN2 z hz) i
      have h2 : X (fun i => ((N : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) * z i) i =
          ((N : ℕ) : P.adicCompletion D.host.E) * X z i := by
        rw [coord_mul, hNc]
      rw [← h2]
      exact h1)
    (by
      rintro U hU i1 i2 _ ⟨z, hz, rfl⟩
      obtain ⟨g, hgK, hgS, hgX⟩ := hlift U hU i1 i2
      exact ⟨_, hG g hgK hgS z hz, hgX z⟩)
  have hy0 : (y : D.host.E) ≠ 0 := GlobalTheory.SphLabelOps.unif_ne_zero (D := D) hy2
  set a := finPart D (incA D ((y : D.host.E) ^ k)) with ha_def
  set b := finPart D (incA D ((y : D.host.E) ^ (-k))) with hb_def
  have hab : a * b = 1 := by
    rw [ha_def, hb_def, ← map_mul, ← map_mul, ← zpow_add₀ hy0, add_neg_cancel, zpow_zero, map_one, map_one]
  have hc : ∀ z : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, (∀ i, fe * z i = z i) →
      ((a * fe + (1 - fe)) • z) = fun i => a * z i := fun z hz => funext fun i => by
    show (a * fe + (1 - fe)) * z i = a * z i
    calc (a * fe + (1 - fe)) * z i = a * (fe * z i) + (z i - fe * z i) := by ring
      _ = a * z i := by rw [hz i, sub_self, add_zero]
  have hXa : ∀ z : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, ∀ i,
      X (fun i => a * z i) i = algebraMap D.host.E (P.adicCompletion D.host.E) (y : D.host.E) ^ k * X z i :=
    fun z i => by rw [coord_mul, ha_def, hinc, map_zpow₀]
  refine ⟨a * fe + (1 - fe), ⟨⟨a * fe + (1 - fe), b * fe + (1 - fe), ?_, ?_⟩, rfl⟩, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · linear_combination (a * b - a - b + 1) * hfe + fe * hab
  · linear_combination (a * b - a - b + 1) * hfe + fe * hab
  · refine ⟨hMe z hz, ?_⟩
    rw [hc z (hsupM z hz), hmem _ (hsmul _ z (hsupM z hz))]
    intro i
    rw [hXa]
    exact (hk (X z)).1 ⟨z, hz, rfl⟩ i
  · rintro ⟨hz1, hz2⟩
    have hs : ∀ i, fe * z i = z i := fun i => congrFun hz1 i
    rw [hc z hs, hmem _ (hsmul _ z hs)] at hz2
    exact (hLmem z hs).1 ((hk (X z)).2 fun i => by rw [← hXa]; exact hz2 i)

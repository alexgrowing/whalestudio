import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummerDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupNat
import GroundTheory.ProfiniteCohomology.LocalTateDuality.Bockstein
import GroundTheory.ProfiniteCohomology.PoincarePairs.IsDiscreteRepResHomCoindRes
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory IsDedekindDomain NumberField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n]

omit [NeZero n] in

theorem nsmul_galRootsOfUnity_eq_zero' {F L : Type} [Field F] [Field L] [Algebra F L]
    (ζ : galRootsOfUnity.{0} F L n) : n • ζ = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((Additive.toMul ζ : rootsOfUnity n L) : Lˣ) ^ n = 1
  exact (mem_rootsOfUnity n _).1 (Additive.toMul ζ).2

section ActPairings

variable {H : Type} [Group H]

def intActBiadd (A Z' : Rep.{0} (ULift.{0} ℤ) H) (e : Z' →+ ℤ) : A →+ Z' →+ A :=
  AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun z => e z • a) (fun z z' => by rw [map_add, add_smul]))
    (fun a a' => by
      ext z
      change e z • (a + a') = e z • a + e z • a'
      exact smul_add _ _ _)

def intActPairing (A Z' : Rep.{0} (ULift.{0} ℤ) H) (e : Z' →+ ℤ)
    (hZ : ∀ (g : H) (z : Z'), Z'.ρ g z = z) : A ⊗ Z' ⟶ A :=
  pairingHom
    (bilinOfAddHom (intActBiadd A Z' e)
      (fun c a z => by
        obtain ⟨c⟩ := c
        have h : (ULift.up c : ULift.{0} ℤ) = ((c : ℤ) : ULift.{0} ℤ) := by
          ext
          simp
        simp only [intActBiadd, AddMonoidHom.mk'_apply]
        rw [h, Int.cast_smul_eq_zsmul (ULift.{0} ℤ), Int.cast_smul_eq_zsmul (ULift.{0} ℤ), smul_comm])
      (fun c a z => by
        simp only [intActBiadd, AddMonoidHom.mk'_apply]
        obtain ⟨c⟩ := c
        have h : (ULift.up c : ULift.{0} ℤ) = ((c : ℤ) : ULift.{0} ℤ) := by
          ext
          simp
        rw [h, Int.cast_smul_eq_zsmul (ULift.{0} ℤ), Int.cast_smul_eq_zsmul (ULift.{0} ℤ), map_zsmul,
          smul_eq_mul, mul_smul]))
    fun g a z => by
      change e (Z'.ρ g z) • A.ρ g a = A.ρ g (e z • a)
      rw [hZ, map_zsmul]

theorem intActPairing_tmul (A Z' : Rep.{0} (ULift.{0} ℤ) H) (e : Z' →+ ℤ)
    (hZ : ∀ (g : H) (z : Z'), Z'.ρ g z = z)
    (a : A) (z : Z') : (intActPairing A Z' e hZ).hom (a ⊗ₜ[ULift.{0} ℤ] z) = e z • a :=
  pairingHom_tmul _ _ a z

def zmodActBiadd (D Z' : Rep.{0} (ULift.{0} ℤ) H) (hD : ∀ d : D, n • d = 0) (e : Z' →+ ZMod n) : D →+ Z' →+ D :=
  AddMonoidHom.mk' (fun d => AddMonoidHom.mk' (fun z => zmodMulAddHom n hD (e z) d)
      (fun z z' => by
        change zmodMulAddHom n hD (e (z + z')) d = zmodMulAddHom n hD (e z) d + zmodMulAddHom n hD (e z') d
        rw [map_add, map_add, AddMonoidHom.add_apply]))
    (fun d d' => by
      ext z
      change zmodMulAddHom n hD (e z) (d + d') = zmodMulAddHom n hD (e z) d + zmodMulAddHom n hD (e z) d'
      exact map_add _ _ _)

def zmodActPairing (D Z' : Rep.{0} (ULift.{0} ℤ) H) (hD : ∀ d : D, n • d = 0) (e : Z' →+ ZMod n)
    (hZ : ∀ (g : H) (z : Z'), Z'.ρ g z = z) :
    D ⊗ Z' ⟶ D :=
  pairingHom
    (bilinOfAddHom (zmodActBiadd n D Z' hD e)
      (fun c d z => by
        obtain ⟨c⟩ := c
        have h : (ULift.up c : ULift.{0} ℤ) = ((c : ℤ) : ULift.{0} ℤ) := by
          ext
          simp
        simp only [zmodActBiadd, AddMonoidHom.mk'_apply]
        rw [h, Int.cast_smul_eq_zsmul (ULift.{0} ℤ), Int.cast_smul_eq_zsmul (ULift.{0} ℤ), map_zsmul])
      (fun c d z => by
        obtain ⟨c⟩ := c
        have h : (ULift.up c : ULift.{0} ℤ) = ((c : ℤ) : ULift.{0} ℤ) := by
          ext
          simp
        simp only [zmodActBiadd, AddMonoidHom.mk'_apply]
        rw [h, Int.cast_smul_eq_zsmul (ULift.{0} ℤ), Int.cast_smul_eq_zsmul (ULift.{0} ℤ), map_zsmul, map_zsmul,
          AddMonoidHom.zsmul_apply]))
    fun g d z => by
      change zmodMulAddHom n hD (e (Z'.ρ g z)) (D.ρ g d) = D.ρ g (zmodMulAddHom n hD (e z) d)
      rw [hZ, zmodMulAddHom_apply, zmodMulAddHom_apply, map_zsmul]

omit [NeZero n] in
theorem zmodActPairing_tmul (D Z' : Rep.{0} (ULift.{0} ℤ) H) (hD : ∀ d : D, n • d = 0) (e : Z' →+ ZMod n)
    (hZ : ∀ (g : H) (z : Z'), Z'.ρ g z = z)
    (d : D) (z : Z') : (zmodActPairing n D Z' hD e hZ).hom (d ⊗ₜ[ULift.{0} ℤ] z) = (ZMod.cast (e z) : ℤ) • d :=
  pairingHom_tmul _ _ d z

end ActPairings

omit [NeZero n] in

theorem zsmul_eq_cast_zsmul {M : Type*} [AddCommGroup M] [NeZero n] {x : M} (hx : n • x = 0) (z : ℤ) :
    z • x = (ZMod.cast (z : ZMod n) : ℤ) • x := by
  rw [ZMod.coe_intCast]
  conv_lhs => rw [← Int.emod_add_ediv_mul z n]
  rw [add_smul, mul_smul, natCast_zsmul, hx, smul_zero, add_zero]

omit [NeZero n] in
theorem nsmul_zsmul_swap {M : Type*} [AddCommGroup M] (m : ℕ) (z : ℤ) (x : M) : (m • z) • x = z • (m • x) := by
  rw [smul_assoc, smul_comm]

abbrev gsPairingU : galSUnitsMax K.1 ℚ̄ S ⊗ intRepTriv (galUnramifiedOutside K.1 ℚ̄ S) ⟶ galSUnitsMax K.1 ℚ̄ S :=
  intActPairing _ _ (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).toAddMonoidHom (fun _ _ => rfl)

abbrev gsPairingμ : gsRoots S n ⊗ zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n ⟶ galSUnitsMax K.1 ℚ̄ S :=
  zmodActPairing n _ _ (nsmul_gsRoots S n) (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom
      (fun _ _ => rfl) ≫ rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) n

abbrev gsPairingμᵥ (v : S) :
    galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n ⊗
      Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) ⟶
    galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
  zmodActPairing n _ _ (nsmul_galRootsOfUnity_eq_zero' n) (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom
      (fun _ _ => rfl) ≫ rootsOfUnityToUnits _ _ n

omit [NeZero n] in
theorem gsPairingU_tmul (x : galSUnitsMax K.1 ℚ̄ S) (m : intRepTriv (galUnramifiedOutside K.1 ℚ̄ S)) :
    (gsPairingU S).hom (x ⊗ₜ[ULift.{0} ℤ] m) = m.down • x :=
  intActPairing_tmul _ _ _ _ x m

theorem gsPairingU_h₂₃ :
    (𝟙 (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).X₂ ⊗ₘ (bockSeq (galUnramifiedOutside K.1 ℚ̄ S) n).f) ≫
        gsPairingU S =
      ((sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).g ⊗ₘ 𝟙 (bockSeq _ n).X₁) ≫ gsPairingU S := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext'
    fun (x : galSUnitsMax K.1 ℚ̄ S) (m : intRepTriv (galUnramifiedOutside K.1 ℚ̄ S)) => ?_))
  change (gsPairingU S).hom (x ⊗ₜ[ULift.{0} ℤ] (n • m)) = (gsPairingU S).hom ((n • x) ⊗ₜ[ULift.{0} ℤ] m)
  rw [gsPairingU_tmul, gsPairingU_tmul]
  have hm : (n • m).down = (n : ℤ) * m.down := by
    change n • m.down = _
    rw [nsmul_eq_mul]
  rw [hm, mul_comm, mul_smul, natCast_zsmul]

theorem gsPairingμ_tmul (ζ : gsRoots S n) (a : zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) :
    (gsPairingμ S n).hom (ζ ⊗ₜ[ULift.{0} ℤ] a) =
      (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) n).hom ((ZMod.cast a.down : ℤ) • ζ) :=
  congrArg (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) n).hom (zmodActPairing_tmul _ _ _ _ _ _ ζ a)

theorem gsPairingμᵥ_tmul (v : S)
    (ζ : galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n)
    (a : Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)) :
    (gsPairingμᵥ S ιs n v).hom (ζ ⊗ₜ[ULift.{0} ℤ] a) =
      (rootsOfUnityToUnits _ _ n).hom ((ZMod.cast a.down : ℤ) • ζ) :=
  congrArg (rootsOfUnityToUnits _ _ n).hom (zmodActPairing_tmul _ _ _ _ _ _ ζ a)

theorem gsPairingU_h₁₂ :
    ((sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).f ⊗ₘ 𝟙 (bockSeq (galUnramifiedOutside K.1 ℚ̄ S) n).X₂) ≫
        gsPairingU S =
      (𝟙 (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).X₁ ⊗ₘ (bockSeq _ n).g) ≫ gsPairingμ S n := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext'
    fun (ζ : gsRoots S n) (m : intRepTriv (galUnramifiedOutside K.1 ℚ̄ S)) => ?_))
  change (gsPairingU S).hom ((rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) n).hom ζ ⊗ₜ[ULift.{0} ℤ] m) =
    (gsPairingμ S n).hom (ζ ⊗ₜ[ULift.{0} ℤ] (zmodReduction _ n).hom (ULift.up m.down))
  have e2 : (gsPairingμ S n).hom (ζ ⊗ₜ[ULift.{0} ℤ] (zmodReduction _ n).hom (ULift.up m.down)) =
      (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) n).hom
        ((ZMod.cast ((m.down : ℤ) : ZMod n) : ℤ) • ζ) :=
    (congrArg (fun a => (gsPairingμ S n).hom (ζ ⊗ₜ[ULift.{0} ℤ] a)) (zmodReduction_hom_apply _ n m.down)).trans
      (gsPairingμ_tmul S n ζ _)
  refine (gsPairingU_tmul S _ m).trans (Eq.trans ?_ e2.symm)
  exact (zsmul_eq_cast_zsmul n (by rw [← map_nsmul, nsmul_gsRoots, map_zero]) m.down).trans (map_zsmul _ _ _).symm

omit [NeZero n] in
theorem gsPairingU_h₂₃ᵥ (v : S) :
    (𝟙 _ ⊗ₘ (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (bockSeq (galUnramifiedOutside K.1 ℚ̄ S) n).f) ≫
        mulIntRight (gsFinFamily S ιs v).toMonoidHom
          (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
            (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) =
      ((kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
          (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n).g ⊗ₘ 𝟙 _) ≫
        mulIntRight (gsFinFamily S ιs v).toMonoidHom
          (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
            (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext'
    fun (x : galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
      (m : Rep.res (gsFinFamily S ιs v).toMonoidHom (intRepTriv (galUnramifiedOutside K.1 ℚ̄ S))) => ?_))
  change (mulIntRight (gsFinFamily S ιs v).toMonoidHom _).hom
      (x ⊗ₜ[ULift.{0} ℤ] (ULift.up (n • m.down) :
        Rep.res (gsFinFamily S ιs v).toMonoidHom (intRepTriv (galUnramifiedOutside K.1 ℚ̄ S)))) =
    (mulIntRight (gsFinFamily S ιs v).toMonoidHom _).hom ((n • x) ⊗ₜ[ULift.{0} ℤ]
      (ULift.up m.down : Rep.res (gsFinFamily S ιs v).toMonoidHom (intRepTriv (galUnramifiedOutside K.1 ℚ̄ S))))
  refine (mulIntRight_tmul (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) x (n • m.down)).trans
    (Eq.trans ?_ (mulIntRight_tmul (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (n • x) m.down).symm)
  exact nsmul_zsmul_swap n m.down x

set_option maxHeartbeats 1600000 in
theorem gsPairingU_h₁₂ᵥ (v : S) :
    ((kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
          (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n).f ⊗ₘ 𝟙 _) ≫
        mulIntRight (gsFinFamily S ιs v).toMonoidHom
          (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
            (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) =
      (𝟙 _ ⊗ₘ (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (bockSeq (galUnramifiedOutside K.1 ℚ̄ S) n).g) ≫
        gsPairingμᵥ S ιs n v := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext'
    fun (ζ : galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n)
      (m : Rep.res (gsFinFamily S ιs v).toMonoidHom (intRepTriv (galUnramifiedOutside K.1 ℚ̄ S))) => ?_))
  change (mulIntRight (gsFinFamily S ιs v).toMonoidHom _).hom ((rootsOfUnityToUnits _ _ n).hom ζ ⊗ₜ[ULift.{0} ℤ]
      (ULift.up m.down : Rep.res (gsFinFamily S ιs v).toMonoidHom (intRepTriv (galUnramifiedOutside K.1 ℚ̄ S)))) =
    (gsPairingμᵥ S ιs n v).hom (ζ ⊗ₜ[ULift.{0} ℤ]
      ((zmodReduction _ n).hom (ULift.up m.down) : Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} _ n)))
  have e2 : (gsPairingμᵥ S ιs n v).hom (ζ ⊗ₜ[ULift.{0} ℤ]
      ((zmodReduction _ n).hom (ULift.up m.down) : Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} _ n))) =
      (rootsOfUnityToUnits _ _ n).hom ((ZMod.cast ((m.down : ℤ) : ZMod n) : ℤ) • ζ) :=
    (congrArg (fun a : Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} _ n) =>
      (gsPairingμᵥ S ιs n v).hom (ζ ⊗ₜ[ULift.{0} ℤ] a)) (zmodReduction_hom_apply _ n m.down)).trans
      (gsPairingμᵥ_tmul S ιs n v ζ _)
  refine (mulIntRight_tmul (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) _ m.down).trans (Eq.trans ?_ e2.symm)
  have hx : n • (rootsOfUnityToUnits _ _ n).hom ζ = 0 := by
    rw [← map_nsmul, nsmul_galRootsOfUnity_eq_zero', map_zero]
  exact (zsmul_eq_cast_zsmul n hx m.down).trans (map_zsmul (rootsOfUnityToUnits _ _ n).hom _ ζ).symm

set_option maxHeartbeats 1600000 in
theorem gsSUnitsLocalMor_rootsOfUnityToSUnits (v : S) (ζ : gsRoots S n) :
    (gsSUnitsLocalMor S ιs v).hom ((rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) n).hom ζ) =
      (rootsOfUnityToUnits _ _ n).hom ((gsRootsOmegaMor S ιs n v).hom ζ) := by
  apply Additive.toMul.injective
  apply Units.ext
  change (ιs v) ((((Additive.toMul ζ : rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S)) :
      (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) =
    ((restrictRootsOfUnity ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom n
      (Additive.toMul ζ) : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))ˣ) :
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  rw [restrictRootsOfUnity_coe_apply]
  rfl

set_option maxHeartbeats 1600000 in
theorem gsPairingμ_hμ (v : S) :
    (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (gsPairingμ S n) ≫ gsSUnitsLocalMor S ιs v =
      resTensorHom (gsFinFamily S ιs v).toMonoidHom (gsRootsOmegaMor S ιs n v) (𝟙 _) ≫ gsPairingμᵥ S ιs n v := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext'
    fun (ζ : gsRoots S n) (a : zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) => ?_))
  change (gsSUnitsLocalMor S ιs v).hom ((gsPairingμ S n).hom (ζ ⊗ₜ[ULift.{0} ℤ] a)) =
    (gsPairingμᵥ S ιs n v).hom ((gsRootsOmegaMor S ιs n v).hom ζ ⊗ₜ[ULift.{0} ℤ]
      (a : Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} _ n)))
  refine (congrArg (gsSUnitsLocalMor S ιs v).hom (gsPairingμ_tmul S n ζ a)).trans
    (Eq.trans ?_ (gsPairingμᵥ_tmul S ιs n v ((gsRootsOmegaMor S ιs n v).hom ζ) a).symm)
  exact (congrArg (gsSUnitsLocalMor S ιs v).hom
      (map_zsmul (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) n).hom (ZMod.cast a.down : ℤ) ζ)).trans
    ((map_zsmul (gsSUnitsLocalMor S ιs v).hom (ZMod.cast a.down : ℤ) _).trans
      ((congrArg (fun y => (ZMod.cast a.down : ℤ) • y) (gsSUnitsLocalMor_rootsOfUnityToSUnits S ιs n v ζ)).trans
        (map_zsmul (rootsOfUnityToUnits _ _ n).hom (ZMod.cast a.down : ℤ) _).symm))

set_option maxHeartbeats 1600000 in
theorem gsPairingU_hμ (v : S) :
    (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (gsPairingU S) ≫ gsSUnitsLocalMor S ιs v =
      resTensorHom (gsFinFamily S ιs v).toMonoidHom (gsSUnitsLocalMor S ιs v) (𝟙 _) ≫
        mulIntRight (gsFinFamily S ιs v).toMonoidHom
          (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
            (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext'
    fun (x : galSUnitsMax K.1 ℚ̄ S) (m : intRepTriv (galUnramifiedOutside K.1 ℚ̄ S)) => ?_))
  change (gsSUnitsLocalMor S ιs v).hom ((gsPairingU S).hom (x ⊗ₜ[ULift.{0} ℤ]
      (ULift.up m.down : intRepTriv (galUnramifiedOutside K.1 ℚ̄ S)))) =
    (mulIntRight (gsFinFamily S ιs v).toMonoidHom _).hom ((gsSUnitsLocalMor S ιs v).hom x ⊗ₜ[ULift.{0} ℤ]
      (ULift.up m.down : Rep.res (gsFinFamily S ιs v).toMonoidHom (intRepTriv (galUnramifiedOutside K.1 ℚ̄ S))))
  refine (congrArg (gsSUnitsLocalMor S ιs v).hom (gsPairingU_tmul S x _)).trans
    (Eq.trans ?_ (mulIntRight_tmul (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) _ m.down).symm)
  exact map_zsmul _ _ _

omit [NeZero n] in
theorem eq_of_add_neg_one_pow_one_smul_eq_zero {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {a b : M}
    (h : a + (-1 : R) ^ 1 • b = 0) : a = b := by
  rw [pow_one, neg_one_smul, add_neg_eq_zero] at h
  exact h

set_option maxHeartbeats 1600000 in

theorem gsKummerCompactδ_cup (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal) (x : gsUnitsCompact S ιs 1)
    (y : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    compactCup (gsFinFamily S ιs) (gsPairingμ S n) (gsPairingμᵥ S ιs n) (gsPairingμ_hμ S ιs n)
        (show 1 + 1 + 1 = 2 + 1 from rfl) ((gsKummerCompactδ S ιs n hnS 1).hom x) y =
      compactCup (gsFinFamily S ιs) (gsPairingU S)
        (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (gsPairingU_hμ S ιs)
        (show 1 + (1 + 1) = 2 + 1 from rfl) x
        ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom y) := by
  have e := compactCup_compactδ_add_compactCup_δ (gsFinFamily S ιs)
    (SA := sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n)
    (SAᵥ := fun v => kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n)
    (SB := bockSeq (galUnramifiedOutside K.1 ℚ̄ S) n) (C := galSUnitsMax K.1 ℚ̄ S)
    (Cᵥ := fun v => (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (c := gsSUnitsLocalMor S ιs) (gsKummerLocalMap S ιs n)
    (gsPairingμ S n) (gsPairingU S) (gsPairingU S) (gsPairingμᵥ S ιs n)
    (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))))
    (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))))
    (gsPairingμ_hμ S ιs n) (gsPairingU_hμ S ιs) (gsPairingU_hμ S ιs)
    (gsPairingU_h₁₂ S n) (gsPairingU_h₂₃ S n) (gsPairingU_h₁₂ᵥ S ιs n) (gsPairingU_h₂₃ᵥ S ιs n)
    (gsKummer_shortExact S n hnS) (localKummer_shortExact S n)
    (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n))
    (show 1 + 1 + 1 = 2 + 1 from rfl) (show 1 + (1 + 1) = 2 + 1 from rfl) x y
  exact eq_of_add_neg_one_pow_one_smul_eq_zero e

end

end GroundTheory.ProfCoh

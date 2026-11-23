import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SUnits
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IsDedekindDomain NumberField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)

def gsUnitsLocalMor (v : S) :
    Rep.res (gsFinFamily S ιs v).toMonoidHom (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) ⟶
      galUnits ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
  Rep.ofHom ⟨uliftIntLinearMap (MonoidHom.toAdditive (α := (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)
      (β := (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))ˣ)
      (Units.map ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom.toMonoidHom)),
    fun σ => LinearMap.ext fun x => congrArg Additive.ofMul
      (Units.ext (gsFinFamily_apply S ιs v σ ((Additive.toMul x : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
        maxUnramifiedOutside K.1 ℚ̄ S)))⟩

def gsSUnitsLocalMor (v : S) :
    Rep.res (gsFinFamily S ιs v).toMonoidHom (galSUnitsMax K.1 ℚ̄ S) ⟶
      galUnits ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
  (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) ≫
    gsUnitsLocalMor S ιs v

def gsRootsOmegaMor (v : S) :
    Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n) ⟶
      galRootsOfUnity ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n :=
  Rep.ofHom ⟨uliftIntLinearMap (MonoidHom.toAdditive (α := rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))
      (β := rootsOfUnity n (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
      (restrictRootsOfUnity ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom n)),
    fun σ => LinearMap.ext fun ζ => congrArg Additive.ofMul (Subtype.ext (Units.ext
      (gsFinFamily_apply S ιs v σ ((((Additive.toMul ζ : rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S)) :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) : maxUnramifiedOutside K.1 ℚ̄ S))))⟩

theorem comp_nsmul_id_eq {C : Type*} [Category C] [Preadditive C] {X Y : C} (f : X ⟶ Y) (m : ℕ) :
    f ≫ (m • 𝟙 Y) = (m • 𝟙 X) ≫ f := by
  rw [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id, Category.id_comp]

variable [NeZero n]

def gsKummerLocalMap (v : S) :
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).map
        (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom) ⟶
      kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n where
  τ₁ := gsRootsOmegaMor S ιs n v
  τ₂ := gsSUnitsLocalMor S ιs v
  τ₃ := gsSUnitsLocalMor S ιs v
  comm₁₂ := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  comm₂₃ := (comp_nsmul_id_eq (gsSUnitsLocalMor S ιs v) n).trans
    (congrArg (· ≫ gsSUnitsLocalMor S ιs v)
      (Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))))

abbrev gsUnitsCompact (m : ℕ) :=
  compactCohomology (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S)
    (fun v : S => galUnits ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsSUnitsLocalMor S ιs) m

abbrev gsRootsCompact (m : ℕ) :=
  compactCohomology (gsFinFamily S ιs) (gsRoots S n)
    (fun v : S => galRootsOfUnity ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (gsRootsOmegaMor S ιs n) m

def gsRootsComparison (m : ℕ) :
    compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) m ⟶ gsRootsCompact S ιs n m :=
  compactCohomologyMap (gsFinFamily S ιs) (𝟙 (gsRoots S n)) (gsRootsOmegaMor S ιs n)
    (fun _ => Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))) m

theorem gsKummer_shortExact (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal) :
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).ShortExact :=
  sUnitsKummerSequence_shortExact S n hnS

theorem localKummer_shortExact (v : S) :
    (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n).ShortExact :=
  kummerSequence_shortExact n (by exact_mod_cast NeZero.ne n)

def gsKummerCompactδ (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal) (m : ℕ) :
    gsUnitsCompact S ιs m ⟶ gsRootsCompact S ιs n (m + 1) :=
  compactδ (gsFinFamily S ιs) (gsKummerLocalMap S ιs n) (gsKummer_shortExact S n hnS)
    (localKummer_shortExact S n) m

end

end GroundTheory.ProfCoh

import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.GSDefs
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingCriterion
import GroundTheory.ProfiniteCohomology.RestrictedRamification.EqZeroOfPowNsmulCohomologySUnitsOfOdd
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Dimension
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalRestriction
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.HighUnitsLocal
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolBridge
import GroundTheory.ProfiniteCohomology.ClassFormations.HighFormations
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.ProfiniteCohomology.Characters
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.Naturality
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section NSMul

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (A : Rep.{u} k G) [IsDiscreteRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsDiscreteRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v)
  (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsDiscreteRep (Aᵣ w)]
  (ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w)

theorem tateCompactCochainsMap_nsmul_id (m : ℕ)
    (hg : ∀ v, a v ≫ (m • 𝟙 (Aᵥ v)) = (Rep.resFunctor (φ v).toMonoidHom).map (m • 𝟙 A) ≫ a v)
    (hgr : ∀ w, ar w ≫ (m • 𝟙 (Aᵣ w)) = (Rep.resFunctor (ψ w).toMonoidHom).map (m • 𝟙 A) ≫ ar w) :
    tateCompactCochainsMap φ ψ (m • 𝟙 A) (fun v => m • 𝟙 (Aᵥ v)) (fun w => m • 𝟙 (Aᵣ w)) hg hgr =
      m • 𝟙 _ := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun p => ?_)
  obtain ⟨⟨x, e⟩, y⟩ := p
  have h1 : ((cochainsMap (m • 𝟙 A)).f n).hom x = m • x := by
    rw [cochainsMap_nsmul, cochainsMap_id]
    simp
  have h2 : ((degZeroMap (piRepHom fun w => m • 𝟙 (Aᵣ w))).f n).hom e = m • e := by
    cases n with
    | zero =>
      funext w
      exact nsmul_id_hom_apply (Aᵣ w) m _
    | succ n => exact Subsingleton.elim _ _
  have h3 : (shiftNegOneMapF (tateLocalMap (fun v => m • 𝟙 (Aᵥ v)) (fun w => m • 𝟙 (Aᵣ w))) n).hom y =
      m • y := by
    cases n with
    | zero => rfl
    | succ n =>
      obtain ⟨y1, y2⟩ := y
      refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
      · change ((cochainsMap (m • 𝟙 (Aᵥ v))).f n).hom (y1 v) = m • y1 v
        rw [cochainsMap_nsmul, cochainsMap_id]
        simp
      · change ((cochainsMap (m • 𝟙 (Aᵣ w))).f n).hom (y2 w) = m • y2 w
        rw [cochainsMap_nsmul, cochainsMap_id]
        simp
  have hr : ((m • 𝟙 (tateCompactCochains φ ψ A Aᵥ a Aᵣ ar)).f n).hom ((x, e), y) = m • ((x, e), y) := by
    rw [HomologicalComplex.nsmul_f_apply, ModuleCat.hom_nsmul]
    rfl
  rw [hr]
  change ((((cochainsMap (m • 𝟙 A)).f n).hom x,
    ((degZeroMap (piRepHom fun w => m • 𝟙 (Aᵣ w))).f n).hom e),
    (shiftNegOneMapF (tateLocalMap (fun v => m • 𝟙 (Aᵥ v)) (fun w => m • 𝟙 (Aᵣ w))) n).hom y) = _
  rw [h1, h2, h3]
  rfl

theorem tateCompactCohomologyMap_nsmul_id (m n : ℕ)
    (hg : ∀ v, a v ≫ (m • 𝟙 (Aᵥ v)) = (Rep.resFunctor (φ v).toMonoidHom).map (m • 𝟙 A) ≫ a v)
    (hgr : ∀ w, ar w ≫ (m • 𝟙 (Aᵣ w)) = (Rep.resFunctor (ψ w).toMonoidHom).map (m • 𝟙 A) ≫ ar w) :
    tateCompactCohomologyMap φ ψ (m • 𝟙 A) (fun v => m • 𝟙 (Aᵥ v)) (fun w => m • 𝟙 (Aᵣ w)) hg hgr n =
      m • 𝟙 _ := by
  unfold tateCompactCohomologyMap
  rw [tateCompactCochainsMap_nsmul_id]
  have := (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).map_nsmul
    (f := 𝟙 (tateCompactCochains φ ψ A Aᵥ a Aᵣ ar)) (n := m)
  simp only [HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_id] at this
  exact this

end NSMul

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))

section LocalMor

variable {Kv Ωv : Type} [Field Kv] [Field Ωv] [Algebra Kv Ωv]
  (θ : Gal(Ωv/Kv) →* galUnramifiedOutside K.1 ℚ̄ S) (j : maxUnramifiedOutside K.1 ℚ̄ S →+* Ωv)
  (hj : ∀ σ y, j (θ σ y) = σ (j y))

def sUnitsLocalMor : Rep.res θ (galSUnitsMax K.1 ℚ̄ S) ⟶ galUnits.{0} Kv Ωv :=
  Rep.ofHom ⟨uliftIntLinearMap (MonoidHom.toAdditive (α := sUnitsMax K.1 ℚ̄ S) (β := Ωvˣ)
      ((Units.map j.toMonoidHom).comp (sUnitsMax K.1 ℚ̄ S).subtype)),
    fun σ => LinearMap.ext fun x => congrArg Additive.ofMul (Units.ext (hj σ
      (((Additive.toMul x : sUnitsMax K.1 ℚ̄ S) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
        maxUnramifiedOutside K.1 ℚ̄ S)))⟩

theorem sUnitsLocalMor_hom_apply (x : Additive (sUnitsMax K.1 ℚ̄ S)) :
    ((Additive.toMul ((sUnitsLocalMor S θ j hj).hom x) : Ωvˣ) : Ωv) =
      j (((Additive.toMul x : sUnitsMax K.1 ℚ̄ S) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
        maxUnramifiedOutside K.1 ℚ̄ S) :=
  rfl

def rootsLocalMor : Rep.res θ (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) 2) ⟶ galUnits.{0} Kv Ωv :=
  Rep.ofHom ⟨uliftIntLinearMap (MonoidHom.toAdditive (α := rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S))
      (β := Ωvˣ) ((Units.map j.toMonoidHom).comp (rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S)).subtype)),
    fun σ => LinearMap.ext fun x => congrArg Additive.ofMul (Units.ext (hj σ
      (((Additive.toMul x : rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S)) :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S)))⟩

theorem rootsLocalMor_hom_apply (x : Additive (rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S))) :
    ((Additive.toMul ((rootsLocalMor S θ j hj).hom x) : Ωvˣ) : Ωv) =
      j (((Additive.toMul x : rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S)) :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) :=
  rfl

def localKummerSeq : ShortComplex (Rep.{0} (ULift.{0} ℤ) Gal(Ωv/Kv)) :=
  ShortComplex.mk (rootsLocalMor S θ j hj) (2 • 𝟙 (galUnits.{0} Kv Ωv)) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change (2 • 𝟙 (galUnits.{0} Kv Ωv)).hom ((rootsLocalMor S θ j hj).hom x) = 0
    rw [nsmul_id_hom_apply]
    apply Additive.toMul.injective
    apply Units.ext
    have hx2 : ((Additive.toMul (α := rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S)) x :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) ^ 2 = 1 := (mem_rootsOfUnity 2 _).1 (Additive.toMul x).2
    change ((Additive.toMul ((rootsLocalMor S θ j hj).hom x) : Ωvˣ) : Ωv) ^ 2 = 1
    rw [rootsLocalMor_hom_apply, ← map_pow, ← Units.val_pow_eq_pow_val, hx2, Units.val_one, map_one])

theorem localKummerSeq_f : (localKummerSeq S θ j hj).f = rootsLocalMor S θ j hj := rfl

theorem localKummerSeq_g : (localKummerSeq S θ j hj).g = 2 • 𝟙 (galUnits.{0} Kv Ωv) := rfl

theorem localKummerSeq_shortExact [IsAlgClosed Ωv] : (localKummerSeq S θ j hj).ShortExact := by
  have h2' : (2 : maxUnramifiedOutside K.1 ℚ̄ S) ≠ 0 := two_ne_zero
  have h2 : (2 : Ωv) ≠ 0 := by
    have : (2 : Ωv) = j 2 := by rw [map_ofNat]
    rw [this]
    exact (map_ne_zero j).2 h2'
  have hmono : Mono (localKummerSeq S θ j hj).f := by
    refine (Rep.mono_iff_injective _).2 fun x y hxy => ?_
    have h := congrArg (fun t : Additive Ωvˣ => ((Additive.toMul t : Ωvˣ) : Ωv)) hxy
    change j (((Additive.toMul (α := rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S)) x :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) : maxUnramifiedOutside K.1 ℚ̄ S) =
      j (((Additive.toMul (α := rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S)) y :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) : maxUnramifiedOutside K.1 ℚ̄ S) at h
    exact Additive.toMul.injective (Subtype.ext (Units.ext (j.injective h)))
  have hepi : Epi (localKummerSeq S θ j hj).g :=
    (Rep.epi_iff_surjective _).2 (nsmul_id_galUnits_surjective 2 h2)
  refine { exact := ?_ }
  · refine shortComplex_exact_of_forall_exists _ fun x hx => ?_
    let x' : Additive Ωvˣ := x
    have hx' : 2 • x' = 0 :=
      (nsmul_id_hom_apply (galUnits.{0} Kv Ωv) 2 x).symm.trans hx
    have hsq : ((Additive.toMul (α := Ωvˣ) x : Ωvˣ) : Ωv) * ((Additive.toMul (α := Ωvˣ) x : Ωvˣ) : Ωv) = 1 := by
      have e : (2 • x' : Additive Ωvˣ) = x' + x' := two_nsmul x'
      rw [e] at hx'
      have := congrArg (fun t : Additive Ωvˣ => ((Additive.toMul t : Ωvˣ) : Ωv)) hx'
      simp only [toMul_add, toMul_zero, Units.val_mul, Units.val_one] at this
      exact this
    have hneg : (-1 : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) ∈ rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S) := by
      rw [mem_rootsOfUnity]
      exact neg_one_sq
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · refine ⟨0, ?_⟩
      apply Additive.toMul.injective
      apply Units.ext
      change ((Additive.toMul ((rootsLocalMor S θ j hj).hom 0) : Ωvˣ) : Ωv) = _
      rw [map_zero]
      exact h.symm
    · refine ⟨(Additive.ofMul (⟨-1, hneg⟩ : rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S)) :
        Additive (rootsOfUnity 2 (maxUnramifiedOutside K.1 ℚ̄ S))), ?_⟩
      apply Additive.toMul.injective
      apply Units.ext
      change j ((-1 : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) = _
      rw [Units.val_neg, Units.val_one, map_neg, map_one]
      exact h.symm

def kummerLocalMap :
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) 2).map (Rep.resFunctor θ) ⟶
      localKummerSeq S θ j hj where
  τ₁ := 𝟙 _
  τ₂ := sUnitsLocalMor S θ j hj
  τ₃ := sUnitsLocalMor S θ j hj
  comm₁₂ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  comm₂₃ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change (2 • 𝟙 (galUnits.{0} Kv Ωv)).hom ((sUnitsLocalMor S θ j hj).hom x) =
      (sUnitsLocalMor S θ j hj).hom ((2 • 𝟙 (galSUnitsMax K.1 ℚ̄ S)).hom x)
    erw [nsmul_id_hom_apply, nsmul_id_hom_apply, map_nsmul]

end LocalMor

section Compat

variable {Kv Ωv : Type} [Field Kv] [Field Ωv] [Algebra K.1 Kv] [Algebra Kv Ωv] [Algebra K.1 Ωv]
  [IsScalarTower K.1 Kv Ωv] (ι : ℚ̄ →ₐ[K.1] Ωv)

theorem gsRestrict_globalDecomp (σ : Gal(Ωv/Kv)) :
    gsRestrict K S (globalDecomp Kv ι σ) = decompHomS Kv S ι σ := by
  ext y
  apply ι.injective
  change ι ((gsRestrict K S (globalDecomp Kv ι σ) y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) =
    ι ((decompHomS Kv S ι σ y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)
  rw [gsRestrict_apply, globalDecomp_apply]
  exact (decompHom_apply (ι.comp (maxUnramifiedOutside K.1 ℚ̄ S).val) σ y).symm

theorem decompHomS_apply (σ : Gal(Ωv/Kv)) (y : maxUnramifiedOutside K.1 ℚ̄ S) :
    (ι.comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom (decompHomS Kv S ι σ y) =
      σ ((ι.comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom y) :=
  decompHom_apply _ σ y

def sUnitsToUnitsZ : uliftIntToIntRep (galSUnitsMax K.1 ℚ̄ S) ⟶
    uliftIntToIntRep (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (α := sUnitsMax K.1 ℚ̄ S) (β := (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)
    (sUnitsMax K.1 ℚ̄ S).subtype).toIntLinearMap, fun _ => LinearMap.ext fun _ => rfl⟩

def sUnitsLocalMorZ : Rep.res (decompHomS Kv S ι) (uliftIntToIntRep (galSUnitsMax K.1 ℚ̄ S)) ⟶
    galUnitsZ Kv Ωv :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (α := sUnitsMax K.1 ℚ̄ S) (β := Ωvˣ)
    ((Units.map (ι.comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom.toMonoidHom).comp
      (sUnitsMax K.1 ℚ̄ S).subtype)).toIntLinearMap,
    fun σ => LinearMap.ext fun x => congrArg Additive.ofMul (Units.ext (decompHomS_apply S ι σ
      (((Additive.toMul x : sUnitsMax K.1 ℚ̄ S) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
        maxUnramifiedOutside K.1 ℚ̄ S)))⟩

instance isDiscreteRep_uliftIntToIntRep_galSUnitsMax :
    IsDiscreteRep (uliftIntToIntRep (galSUnitsMax K.1 ℚ̄ S)) :=
  isDiscreteRep_uliftIntToIntRep _

variable [Algebra.IsIntegral Kv Ωv]

theorem unitsLocalRes_gsBrauerInfl_sUnitsToUnitsZ (r : ℕ)
    (x : cohomology (uliftIntToIntRep (galSUnitsMax K.1 ℚ̄ S)) r) :
    (unitsLocalRes Kv ι r).hom ((gsBrauerInfl K S r).hom
      ((cohomologyMap (sUnitsToUnitsZ S) r).hom x)) =
      (cohomologyMapAlong (decompHomS Kv S ι) (continuous_decompHomS (Kv := Kv) S ι)
        (sUnitsLocalMorZ S ι) r).hom x := by
  unfold unitsLocalRes gsBrauerInfl
  rw [← cohomologyMapAlong_id_eq_cohomologyMap, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  refine congrArg (fun g => g.hom x) (?_ : _ = cohomologyMapAlong (decompHomS Kv S ι)
    (continuous_decompHomS (Kv := Kv) S ι) (sUnitsLocalMorZ S ι) r)
  apply cohomologyMapAlong_congr
  · ext σ : 1
    exact gsRestrict_globalDecomp S ι σ
  · intro a
    rfl

set_option maxHeartbeats 2000000 in

theorem unitsLocalRes_sUnitsInfl (r : ℕ) (y : cohomology (galSUnitsMax K.1 ℚ̄ S) r) :
    (unitsLocalRes Kv ι r).hom (sUnitsInfl K S r y) =
      cohomologyULiftIntAddEquiv (galUnits.{0} Kv Ωv) r
        ((cohomologyMapAlong (decompHomS Kv S ι) (continuous_decompHomS (Kv := Kv) S ι)
          (sUnitsLocalMor S (decompHomS Kv S ι) (ι.comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom
            (decompHomS_apply S ι)) r).hom y) := by
  have h1 := cohomologyULiftIntAddEquiv_cohomologyMapAlong (galSUnitsMax K.1 ℚ̄ S)
    (decompHomS Kv S ι) (continuous_decompHomS (Kv := Kv) S ι)
    (sUnitsLocalMor S (decompHomS Kv S ι) (ι.comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom
      (decompHomS_apply S ι)) (sUnitsLocalMorZ S ι) (fun _ => rfl) r y
  have h2 := cohomologyULiftIntAddEquiv_cohomologyMapAlong (galSUnitsMax K.1 ℚ̄ S)
    (MonoidHom.id _) continuous_id (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) (sUnitsToUnitsZ S)
    (fun _ => rfl) r y
  rw [cohomologyMapAlong_id_eq_cohomologyMap, cohomologyMapAlong_id_eq_cohomologyMap] at h2
  rw [sUnitsInfl_apply, gsUnitsInfl_apply]
  refine Eq.trans ?_ h1.symm
  rw [h2]
  exact unitsLocalRes_gsBrauerInfl_sUnitsToUnitsZ S ι r _

end Compat

def realLocalEmbeddings (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion) :
    LocalEmbeddings K where
  fin _ := Classical.choice nonempty_algHom_of_isSepClosed
  inf v := by
    classical
    exact if h : v.IsReal then ιr ⟨v, h⟩ else Classical.choice nonempty_algHom_of_isSepClosed

theorem realLocalEmbeddings_inf (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (w : {v : InfinitePlace K.1 // v.IsReal}) : (realLocalEmbeddings ιr).inf w.1 = ιr w := by
  unfold realLocalEmbeddings
  exact dif_pos w.2

end

end GroundTheory.ProfCoh

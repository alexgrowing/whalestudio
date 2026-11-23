import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

open scoped DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) (n : ℕ)

theorem gsRoots_ρ_apply_of_mem (hμ : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ K.1) (g : galUnramifiedOutside K.1 ℚ̄ S)
    (d : gsRoots S n) : (gsRoots S n).ρ g d = d := by
  have key : ∀ ζ : rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S),
      galRootsOfUnityHom K.1 (maxUnramifiedOutside K.1 ℚ̄ S) n g ζ = ζ := by
    intro ζ
    apply Subtype.ext
    apply Units.ext
    show (((restrictRootsOfUnity g n ζ : rootsOfUnity n _) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
        maxUnramifiedOutside K.1 ℚ̄ S) = ((ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S)
    rw [restrictRootsOfUnity_coe_apply]
    have hx : ((ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity n _).1 ζ.2, Units.val_one]
    have hK : (((ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ K.1 :=
      hμ _ (by rw [← IntermediateField.coe_pow, hx]; rfl)
    have hx' : ((ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) =
        algebraMap K.1 (maxUnramifiedOutside K.1 ℚ̄ S) ⟨_, hK⟩ := Subtype.ext rfl
    rw [hx']
    exact g.commutes _
  rw [galRootsOfUnity_ρ_apply, key]
  rfl

theorem nonempty_addEquiv_gsRoots [NeZero n] (hμ : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ K.1) :
    Nonempty (gsRoots S n ≃+ ZMod n) := by
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ n
  have hK : ζ₀ ∈ K.1 := hμ ζ₀ hζ₀.pow_eq_one
  set z : maxUnramifiedOutside K.1 ℚ̄ S := algebraMap K.1 (maxUnramifiedOutside K.1 ℚ̄ S) ⟨ζ₀, hK⟩
  have hz : IsPrimitiveRoot z n :=
    IsPrimitiveRoot.of_map_of_injective (f := (maxUnramifiedOutside K.1 ℚ̄ S).val) (h := hζ₀)
      (maxUnramifiedOutside K.1 ℚ̄ S).val.injective
  have : HasEnoughRootsOfUnity (maxUnramifiedOutside K.1 ℚ̄ S) n := ⟨⟨z, hz⟩, inferInstance⟩
  have hcard : Nat.card (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S)) = Nat.card (Multiplicative (ZMod n)) := by
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  exact ⟨MulEquiv.toAdditive (mulEquivOfCyclicCardEq hcard)⟩

theorem sum_of_apply_of_injective {ι κ : Type*} [Fintype ι] [DecidableEq κ] {M : κ → Type*}
    [∀ k, AddCommGroup (M k)] (e : ι → κ) (he : Function.Injective e) (b : ∀ i, M (e i)) (i₀ : ι) :
    (∑ i, DirectSum.of M (e i) (b i)) (e i₀) = b i₀ := by
  rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single i₀
    (fun i _ hi => DirectSum.of_eq_of_ne (e i) (e i₀) (b i) (fun h => hi (he h.symm)))
    (fun h => absurd (Finset.mem_univ i₀) h), DirectSum.of_eq_same]

theorem sum_of_apply_of_not_mem {ι κ : Type*} [Fintype ι] [DecidableEq κ] {M : κ → Type*}
    [∀ k, AddCommGroup (M k)] (e : ι → κ) (b : ∀ i, M (e i)) (k : κ) (hk : ∀ i, e i ≠ k) :
    (∑ i, DirectSum.of M (e i) (b i)) k = 0 := by
  rw [DFinsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun i _ => DirectSum.of_eq_of_ne (e i) k (b i) (hk i).symm

theorem sum_apply_pi_single {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    {N : Type*} [AddCommGroup N] (f : ∀ i, M i →+ N) (i : ι) (m : M i) :
    ∑ j, f j (Pi.single i m j) = f i m := by
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]

section General

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)] [∀ v, IsTopologicalGroup (H v)]

theorem localToCompact_globalToLocal_apply (φ : ∀ v, H v →ₜ* G) (A : Rep.{u} k G) [IsDiscreteRep A]
    [∀ v, IsDiscreteRep (Rep.res (φ v).toMonoidHom A)] (m : ℕ) (x : cohomology A m) :
    (localToCompact φ A (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _) m).hom
      ((globalToLocal φ A (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _) m).hom x) = 0 := by
  have hz := ConcreteCategory.congr_hom (globalToLocal_localToCompact φ A
    (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _) m) x
  rw [ConcreteCategory.comp_apply] at hz
  exact hz.trans rfl

end General

section Inv

variable (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  [NeZero n] [Fintype S]

set_option maxHeartbeats 1600000 in

theorem surjective_gsCompactInv [Nonempty S] (hodd : Odd n ∨ IsTotallyComplex K.1)
    (h3 : Subsingleton (cohomology (gsRoots S n) 3))
    (ht : ∀ v, Function.Surjective (gsLocalInvRoots S ιs n v)) :
    Function.Surjective (gsCompactInv S ιs n hodd h3) := by
  classical
  intro a
  obtain ⟨v⟩ := ‹Nonempty S›
  obtain ⟨η, hη⟩ := ht v a
  refine ⟨(localToCompact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2).hom (Pi.single v η), ?_⟩
  refine (gsCompactInv_localToCompact S ιs n hodd h3 _).trans ?_
  refine (gsSumInvRoots_apply S ιs n _).trans ?_
  exact (sum_apply_pi_single (fun w => gsLocalInvRoots S ιs n w) v η).trans hη

omit [Fintype S] in

abbrev gsLocalBrauerRoots (v : S) (z : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    localGaloisCohomology K 2 (.inr (v : HeightOneSpectrum (𝓞 K.1))) :=
  (cohomologyMap (rootsLocalMorZ S ιs n v) 2).hom (cohomologyULiftIntAddEquiv _ 2 z)

omit [Fintype S] [NeZero n] in
theorem placeInv_gsLocalBrauerRoots (v : S)
    (z : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    placeInv (.inr (v : HeightOneSpectrum (𝓞 K.1))) (gsLocalBrauerRoots S n ιs v z) =
      gsLocalInvRootsQZ S ιs n v z := by
  refine (placeInv_inr_apply _ _).trans (Eq.symm ?_)
  refine (DFunLike.congr_fun (gsLocalInvRootsQZ_eq S ιs n v) z).trans ?_
  refine (AddMonoidHom.comp_apply _ _ _).trans ?_
  refine congrArg (brauerInvZOfIsSepClosure _ _) ?_
  exact AddMonoidHom.comp_apply _ _ _

omit [Fintype S] [NeZero n] in
theorem nsmul_gsLocalBrauerRoots (v : S)
    (z : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    n • gsLocalBrauerRoots S n ιs v z = 0 := by
  have h : n • z = 0 := nsmul_cohomology_eq_zero (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
    (fun ζ => nsmul_gsRoots S n ζ) 2 z
  exact (map_nsmul _ n _).symm.trans ((congrArg _ ((map_nsmul _ n z).symm.trans
    ((congrArg _ h).trans (map_zero _)))).trans (map_zero _))

open Classical in

noncomputable def gsBrauerFamily
    (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    ⨁ w : Place K.1, localGaloisCohomology K 2 w :=
  ∑ v : S, DirectSum.of (fun w => localGaloisCohomology K 2 w) (Sum.inr (v : HeightOneSpectrum (𝓞 K.1)))
    (gsLocalBrauerRoots S n ιs v (ξ v))

omit [NeZero n] [Fintype S] in
theorem injective_inr_val : Function.Injective fun v : S => (Sum.inr (v : HeightOneSpectrum (𝓞 K.1)) : Place K.1) :=
  fun _ _ h => Subtype.ext (Sum.inr_injective h)

open Classical in
omit [NeZero n] in
theorem gsBrauerFamily_inr (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2)
    (v : S) : gsBrauerFamily S n ιs ξ (.inr (v : HeightOneSpectrum (𝓞 K.1))) = gsLocalBrauerRoots S n ιs v (ξ v) :=
  sum_of_apply_of_injective (fun v : S => (Sum.inr (v : HeightOneSpectrum (𝓞 K.1)) : Place K.1)) (injective_inr_val S)
    (fun v => gsLocalBrauerRoots S n ιs v (ξ v)) v

open Classical in
omit [NeZero n] in
theorem gsBrauerFamily_inr_of_not_mem
    (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2)
    (w : HeightOneSpectrum (𝓞 K.1)) (hw : w ∉ S) : gsBrauerFamily S n ιs ξ (.inr w) = 0 :=
  sum_of_apply_of_not_mem (fun v : S => (Sum.inr (v : HeightOneSpectrum (𝓞 K.1)) : Place K.1))
    (fun v => gsLocalBrauerRoots S n ιs v (ξ v)) _ (fun v h => hw (Sum.inr_injective h ▸ v.2))

omit [NeZero n] in
theorem nsmul_gsBrauerFamily (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    n • gsBrauerFamily S n ιs ξ = 0 := by
  rw [gsBrauerFamily, Finset.smul_sum]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [← map_nsmul, nsmul_gsLocalBrauerRoots, map_zero]

theorem sumPlaceInv_gsBrauerFamily
    (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    sumPlaceInv K (gsBrauerFamily S n ιs ξ) = zmodToQZ n (∑ v, gsLocalInvRoots S ιs n v (ξ v)) := by
  refine (map_sum (sumPlaceInv K) _ _).trans ((Finset.sum_congr rfl fun v _ => ?_).trans
    (map_sum (zmodToQZ n) _ _).symm)
  exact (sumPlaceInv_of _ _).trans
    ((placeInv_gsLocalBrauerRoots S n ιs v (ξ v)).trans (zmodToQZ_gsLocalInvRoots S ιs n v (ξ v)).symm)

omit [NeZero n] [Fintype S] in

theorem placeInv_brauerLocal_sUnitsBrauer (v : S) (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) :
    placeInv (.inr (v : HeightOneSpectrum (𝓞 K.1)))
        (brauerLocal (gsLocalEmbeddings S ιs) (sUnitsBrauer K S y) (.inr (v : HeightOneSpectrum (𝓞 K.1)))) =
      brauerInvZOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) ((gsLocalRes S (ιs v) 2).hom
          (cohomologyULiftIntAddEquiv _ 2
            ((cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom y))) := by
  refine (congrArg (fun z => placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))
    (brauerLocal (gsLocalEmbeddings S ιs) z (.inr (v : HeightOneSpectrum (𝓞 K.1))))) (sUnitsBrauer_apply K S y)).trans ?_
  refine (congrArg (placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1))))
    (brauerLocal_gsBrauerInfl_inr K S _ _ _)).trans ?_
  refine (placeInv_inr_apply _ _).trans ?_
  simp only [gsLocalEmbeddings_fin]

omit [NeZero n] [Fintype S] in

theorem exists_sUnits_of_mem_localPrimaryKernel (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (β : ⨁ w : Place K.1, localGaloisCohomology K 2 w) (hβ : β ∈ localPrimaryKernel K S ℓ) :
    ∃ y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2, (∃ j : ℕ, ℓ ^ j • y = 0) ∧
      brauerLocal (gsLocalEmbeddings S ιs) (sUnitsBrauer K S y) = β :=
  ⟨((sUnitsH2PrimaryEquiv K S ℓ hℓ hS (gsLocalEmbeddings S ιs)).symm ⟨β, hβ⟩).1, ((sUnitsH2PrimaryEquiv K S ℓ hℓ hS (gsLocalEmbeddings S ιs)).symm ⟨β, hβ⟩).2,
    (coe_sUnitsH2PrimaryEquiv_apply K S ℓ hℓ hS (gsLocalEmbeddings S ιs) _).symm.trans
      (congrArg Subtype.val ((sUnitsH2PrimaryEquiv K S ℓ hℓ hS (gsLocalEmbeddings S ιs)).apply_symm_apply ⟨β, hβ⟩))⟩

set_option maxHeartbeats 1600000 in

theorem injective_gsCompactInv (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))
    (ht : ∀ v, Function.Injective (gsLocalInvRoots S ιs n v)) :
    Function.Injective (gsCompactInv S ιs n hodd h3) := by
  rw [injective_iff_map_eq_zero]
  intro z hz0
  refine Exists.elim (localToCompact_two_surjective S ιs n h3 z) (fun ξ hξ => ?_)
  subst hξ
  have hsum : ∑ v, gsLocalInvRoots S ιs n v (ξ v) = 0 :=
    (gsSumInvRoots_apply S ιs n ξ).symm.trans ((gsCompactInv_localToCompact S ιs n hodd h3 ξ).symm.trans hz0)
  have hmem : gsBrauerFamily S n ιs ξ ∈ localPrimaryKernel K S ℓ :=
    ⟨⟨k, hnk ▸ nsmul_gsBrauerFamily S n ιs ξ⟩, gsBrauerFamily_inr_of_not_mem S n ιs ξ,
      (sumPlaceInv_gsBrauerFamily S n ιs ξ).trans (by rw [hsum, map_zero])⟩

  refine Exists.elim (exists_sUnits_of_mem_localPrimaryKernel S ιs ℓ hℓ hS _ hmem) (fun y hy => ?_)
  refine Exists.elim hy.1 (fun j hj => ?_)
  have hyβ' := hy.2
  have hny : n • y = 0 := by
    refine eq_zero_of_sUnitsBrauer_eq_zero K S ℓ hℓ hS (n • y) j (by rw [smul_comm, hj, smul_zero]) ?_
    apply brauerLocal_injective (gsLocalEmbeddings S ιs)
    rw [map_nsmul, map_nsmul, hyβ', nsmul_gsBrauerFamily, map_zero]

  have hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal := fun v hv hn => by
    subst hnk
    rw [Nat.cast_pow] at hn
    exact hv (hS v (v.isPrime.mem_of_pow_mem k hn))
  refine Exists.elim (exists_cohomologyMap_f_eq_of_cohomologyMap_g_eq_zero
    (sUnitsKummerSequence_shortExact (Ω := ℚ̄) S n hnS) 2 y
    ((cohomologyMap_nsmul_id_apply _ n 2 y).trans hny)) (fun x hx => ?_)

  have hres : ∀ v, (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _) (𝟙 _) 2).hom x =
      ξ v := by
    intro v
    apply ht v
    apply zmodToQZ_injective
    refine (zmodToQZ_gsLocalInvRoots S ιs n v _).trans ((gsLocalInvRootsQZ_cohomologyMapAlong S ιs n v x).trans ?_)
    refine Eq.trans ?_ ((placeInv_gsLocalBrauerRoots S n ιs v (ξ v)).trans (zmodToQZ_gsLocalInvRoots S ιs n v (ξ v)).symm)
    refine Eq.trans ?_ (congrArg (placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1))))
      (gsBrauerFamily_inr S n ιs ξ v))
    refine Eq.trans ?_ (congrArg (fun β : ⨁ w : Place K.1, localGaloisCohomology K 2 w =>
      placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1))) (β (.inr (v : HeightOneSpectrum (𝓞 K.1))))) hyβ')
    refine Eq.trans ?_ (placeInv_brauerLocal_sUnitsBrauer S ιs v y).symm
    rw [← hx]
    rfl
  have hg : (globalToLocal (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2).hom x = ξ := funext hres
  exact hg ▸ localToCompact_globalToLocal_apply (gsFinFamily S ιs) (gsRoots S n) 2 x

theorem bijective_gsCompactInv [Nonempty S] (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))
    (ht : ∀ v, Function.Bijective (gsLocalInvRoots S ιs n v)) :
    Function.Bijective (gsCompactInv S ιs n hodd h3) :=
  ⟨injective_gsCompactInv S n ιs ℓ k hℓ hnk hS hodd h3 fun v => (ht v).1,
    surjective_gsCompactInv S n ιs hodd h3 fun v => (ht v).2⟩

theorem bijective_gsCompactInv_of_mem [Nonempty S] (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (hμ : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ K.1) (hodd : Odd n ∨ IsTotallyComplex K.1)
    (h3 : Subsingleton (cohomology (gsRoots S n) 3)) :
    Function.Bijective (gsCompactInv S ιs n hodd h3) :=
  bijective_gsCompactInv S n ιs ℓ k hℓ hnk hS hodd h3 (bijective_gsLocalInvRoots S ιs n hμ)

end Inv

end

end GroundTheory.ProfCoh

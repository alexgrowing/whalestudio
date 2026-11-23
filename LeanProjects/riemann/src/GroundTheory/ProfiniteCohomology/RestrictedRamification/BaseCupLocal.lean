import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummerDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGSLocal
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerLocalVal
import GroundTheory.ProfiniteCohomology.LocalTateDuality.Bockstein
import GroundTheory.ProfiniteCohomology.CyclicCupProf
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory NumberField IsDedekindDomain GroundTheory.Global

open scoped DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

section ULiftCompareAlong

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] (φ : H →* G) (hφ : Continuous φ) {A : Rep.{0} (ULift.{0} ℤ) G} [IsDiscreteRep A]
  {B : Rep.{0} (ULift.{0} ℤ) H} [IsDiscreteRep B] {C : Rep.{0} ℤ H} [IsDiscreteRep C]

theorem cohomologyMap_uliftInt_cohomologyMapAlong_of (f : Rep.res φ A ⟶ B) (g : uliftIntToIntRep B ⟶ C)
    (f₂ : Rep.res φ (uliftIntToIntRep A) ⟶ C) (hf : ∀ a : A, g.hom (f.hom a) = f₂.hom a) (m : ℕ)
    (x : cohomology A m) :
    (cohomologyMap g m).hom (cohomologyULiftIntAddEquiv B m ((cohomologyMapAlong φ hφ f m).hom x)) =
      (cohomologyMapAlong φ hφ f₂ m).hom (cohomologyULiftIntAddEquiv A m x) := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective A m x
  rw [cohomologyMapAlong_cohomologyπ, cohomologyULiftIntAddEquiv_cohomologyπ', cohomologyMap_cohomologyπ,
    cohomologyULiftIntAddEquiv_cohomologyπ', cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cocyclesULiftInt, cochainOf_cocycleι_cocyclesMapAlong,
    cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesULiftInt]
  funext h
  exact hf _

end ULiftCompareAlong

section Bock

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

theorem exists_cocycle_δ_bockSeq (hn : n ≠ 0) (z : cocycles (zmodRep.{0} G n) 1) :
    ∃ x₁ : cocycles (intRepTriv G) 2,
      cohomologyπ _ 2 x₁ = (δ (bockSeq_shortExact G n hn) 1 2 rfl).hom (cohomologyπ _ 1 z) ∧
      ∀ g h : G, (cochainOf _ (cocycleι _ 2 x₁) ![g, h]).down = bockInt (zmodCocycleHom z) g h := by
  have : NeZero n := ⟨hn⟩
  have hS := bockSeq_shortExact G n hn
  have hχ : ∀ g h : G, zmodCocycleHom z (g * h) = zmodCocycleHom z g + zmodCocycleHom z h :=
    zmodCocycleHom_mul z
  have hlc : IsLocallyConstant fun v : Fin 1 → G =>
      (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ) : intRepTriv G) :=
    IsLocallyConstant.comp ((isLocallyConstant_zmodCocycleHom z).comp_continuous (continuous_apply 0))
      (fun c : ZMod n => (ULift.up (c.val : ℤ) : ULift.{0} ℤ))
  let x₂ : (cochainsComplex (bockSeq G n).X₂).X 1 :=
    mkCochain (bockSeq G n).X₂ (fun v : Fin 1 → G =>
      (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ) : intRepTriv G)) hlc
  have hx₂ : (cochainsMap (bockSeq G n).g).f 1 x₂ = cocycleι (bockSeq G n).X₃ 1 z := by
    apply cochainOf_injective
    rw [cochainOf_cochainsMap_f]
    funext v
    have hv : v = ![v 0] := by funext i; fin_cases i; rfl
    change (zmodReduction G n).hom (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ)) =
      cochainOf _ (cocycleι _ 1 z) v
    rw [zmodReduction_hom_apply]
    apply ULift.ext
    change (((zmodCocycleHom z (v 0)).val : ℤ) : ZMod n) = (cochainOf _ (cocycleι _ 1 z) v).down
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    conv_rhs => rw [hv]
    rfl
  obtain ⟨x₁, hx₁⟩ := exists_cocycle_map_f_eq_d hS 2 z x₂ hx₂
  have hδ := δ_cohomologyπ_of_lift hS rfl z x₂ hx₂ x₁ hx₁
  refine ⟨x₁, hδ.symm, fun g h => ?_⟩
  have e : cochainOf (bockSeq G n).X₂ ((cochainsMap (bockSeq G n).f).f 2 (cocycleι _ 2 x₁)) ![g, h] =
      cochainOf (bockSeq G n).X₂ (((cochainsComplex (bockSeq G n).X₂).d 1 2).hom x₂) ![g, h] :=
    congrArg (fun c => cochainOf (bockSeq G n).X₂ c ![g, h]) hx₁
  rw [cochainOf_cochainsMap_f, cochainOf_d_one_apply] at e
  have e2 := congrArg ULift.down e
  change n • (cochainOf _ (cocycleι _ 2 x₁) ![g, h]).down =
    ((zmodCocycleHom z h).val : ℤ) - ((zmodCocycleHom z (g * h)).val : ℤ) +
      ((zmodCocycleHom z g).val : ℤ) at e2
  have e3 := natCast_mul_bockInt (zmodCocycleHom z) hχ g h
  rw [nsmul_eq_mul] at e2
  apply mul_left_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast hn)
  rw [e2, e3]
  ring

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (ψ : H →* G)

def resIntRepTriv : Rep.res ψ (intRepTriv G) ⟶ intRepTriv H :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

def mulIntRight (A : Rep.{0} (ULift.{0} ℤ) H) : A ⊗ Rep.res ψ (intRepTriv G) ⟶ A :=
  (β_ A (Rep.res ψ (intRepTriv G))).hom ≫ (resIntRepTriv ψ ⊗ₘ 𝟙 A) ≫ intMulPairing H A

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H] in
theorem mulIntRight_tmul (A : Rep.{0} (ULift.{0} ℤ) H) (a : A) (m : ℤ) :
    (mulIntRight ψ A).hom (a ⊗ₜ[ULift.{0} ℤ] (ULift.up m : Rep.res ψ (intRepTriv G)) :
      (A ⊗ Rep.res ψ (intRepTriv G) : Rep _ _)) = m • a :=
  intMulPairing_tmul H A m a

end Bock

section Inv

variable (F E : Type) [Field F] [Field E] [Algebra F E]

def galUnitsToZ : uliftIntToIntRep (galUnits.{0} F E) ⟶ galUnitsZ F E :=
  Rep.ofHom ⟨(AddMonoidHom.id (Additive Eˣ)).toIntLinearMap, fun _ => rfl⟩

variable {K : FiniteSubfield}

instance isDiscreteRep_uliftIntToIntRep_galUnits_adic (v : HeightOneSpectrum (𝓞 K.1)) :
    IsDiscreteRep (uliftIntToIntRep (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)))) :=
  ⟨fun a => isOpen_stabilizer (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) a⟩

def localInvU (v : HeightOneSpectrum (𝓞 K.1)) :
    cohomology (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) 2 →+ QZ :=
  (brauerInvZOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))).comp
    ((cohomologyMap (galUnitsToZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) 2).hom.toAddMonoidHom.comp
      (cohomologyULiftIntAddEquiv _ 2).toAddMonoidHom)

theorem localInvU_eq (v : HeightOneSpectrum (𝓞 K.1)) :
    localInvU v = (brauerInvZOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))).comp
      ((cohomologyMap (galUnitsToZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) 2).hom.toAddMonoidHom.comp
        (cohomologyULiftIntAddEquiv _ 2).toAddMonoidHom) :=
  rfl

variable (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

theorem localInvU_cohomologyMapAlong_gsUnitsLocalMor (v : S)
    (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2) :
    localInvU (v : HeightOneSpectrum (𝓞 K.1)) ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
      (continuous_toMonoidHom _) (gsUnitsLocalMor S ιs v) 2).hom x) =
      placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))
        ((gsLocalRes S (ιs v) 2).hom (cohomologyULiftIntAddEquiv _ 2 x)) := by
  refine (DFunLike.congr_fun (localInvU_eq (v : HeightOneSpectrum (𝓞 K.1))) _).trans ?_
  refine (AddMonoidHom.comp_apply _ _ _).trans ?_
  refine Eq.trans ?_ (placeInv_inr_apply _ _).symm
  refine congrArg (brauerInvZOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
    (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) ?_
  refine (AddMonoidHom.comp_apply _ _ _).trans ?_
  exact cohomologyMap_uliftInt_cohomologyMapAlong_of (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
    (gsUnitsLocalMor S ιs v) (galUnitsToZ _ _) (embUnitsMorZ S (ιs v)) (fun _ => rfl) 2 x

theorem localInvU_cohomologyMapAlong_gsSUnitsLocalMor (v : S)
    (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) :
    localInvU (v : HeightOneSpectrum (𝓞 K.1)) ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
      (continuous_toMonoidHom _) (gsSUnitsLocalMor S ιs v) 2).hom y) =
      placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))
        ((gsLocalRes S (ιs v) 2).hom (cohomologyULiftIntAddEquiv _ 2
          ((cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom y))) := by
  exact (congrArg (localInvU (v : HeightOneSpectrum (𝓞 K.1)))
    (cohomologyMapAlong_cohomologyMap_apply (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
      (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) (gsUnitsLocalMor S ιs v) 2 y).symm).trans
    (localInvU_cohomologyMapAlong_gsUnitsLocalMor S ιs v _)

theorem two_nsmul_placeInv_inl (v : InfinitePlace K.1) (y : localGaloisCohomology K 2 (.inl v)) :
    2 • placeInv (.inl v) y = 0 := by
  by_cases hc : v.IsComplex
  · have := subsingleton_cohomology_two_of_isComplex v hc
    rw [show y = 0 from Subsingleton.elim (α := cohomology (galUnitsZ v.Completion
      (AlgebraicClosure v.Completion)) 2) y 0, map_zero, smul_zero]
  · by_cases hy0 : y = 0
    · rw [hy0, map_zero, smul_zero]
    · change 2 • quadraticInvFun v.Completion (AlgebraicClosure v.Completion) y = 0
      rw [quadraticInvFun_of_ne_zero _ _ hy0, two_nsmul, QZ.mk_half_add_mk_half]

variable [Fintype S]

theorem sum_placeInv_inr_eq_zero_of {n : ℕ} (hn : Odd n ∨ IsTotallyComplex K.1) (ι : LocalEmbeddings K)
    (z : cohomology (unitsLimitRep K) 2)
    (hz : ∀ w : HeightOneSpectrum (𝓞 K.1), w ∉ S → placeInv (.inr w) (brauerLocal ι z (.inr w)) = 0)
    (hs : n • ∑ v : S, placeInv (.inr (v : HeightOneSpectrum (𝓞 K.1)))
      (brauerLocal ι z (.inr (v : HeightOneSpectrum (𝓞 K.1)))) = 0) :
    ∑ v : S, placeInv (.inr (v : HeightOneSpectrum (𝓞 K.1)))
      (brauerLocal ι z (.inr (v : HeightOneSpectrum (𝓞 K.1)))) = 0 := by
  classical
  set s := ∑ v : S, placeInv (.inr (v : HeightOneSpectrum (𝓞 K.1)))
      (brauerLocal ι z (.inr (v : HeightOneSpectrum (𝓞 K.1)))) with hsdef
  set i := ∑ w : InfinitePlace K.1, placeInv (.inl w) (brauerLocal ι z (.inl w)) with hidef
  have hT : brauerSumInv ι z = s + i := by
    have hdisj : Disjoint (Finset.univ.image (fun v : S => (Sum.inr (v : HeightOneSpectrum (𝓞 K.1)) : Place K.1)))
        (Finset.univ.image (fun w : InfinitePlace K.1 => (Sum.inl w : Place K.1))) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hw1
      obtain ⟨u, -, hu⟩ := Finset.mem_image.1 hw2
      exact Sum.inl_ne_inr hu
    have hout : ∀ w ∉ Finset.univ.image (fun v : S => (Sum.inr (v : HeightOneSpectrum (𝓞 K.1)) : Place K.1)) ∪
        Finset.univ.image (fun w : InfinitePlace K.1 => (Sum.inl w : Place K.1)),
        placeInv w (brauerLocal ι z w) = 0 := by
      intro w hw
      rcases w with w | w
      · exact absurd (Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, Finset.mem_univ _, rfl⟩)) hw
      · exact hz w fun hwS => hw (Finset.mem_union_left _ (Finset.mem_image.2 ⟨⟨w, hwS⟩, Finset.mem_univ _, rfl⟩))
    refine (AddMonoidHom.comp_apply _ _ _).trans ?_
    rw [sumPlaceInv_eq_sum_of_placeInv _ _ hout, Finset.sum_union hdisj,
      Finset.sum_image (fun v _ w _ h => Subtype.ext (Sum.inr_injective h)),
      Finset.sum_image (fun v _ w _ h => Sum.inl_injective h)]
  have h0 : s + i = 0 := hT.symm.trans (brauerSumInv_eq_zero ι z)
  have hi2 : 2 • i = 0 := by
    rw [hidef, Finset.smul_sum]
    exact Finset.sum_eq_zero fun w _ => two_nsmul_placeInv_inl w _
  rcases hn with ⟨m, hm⟩ | hc
  · have hs2 : 2 • s = 0 := by
      have : s = -i := eq_neg_of_add_eq_zero_left h0
      rw [this, smul_neg, hi2, neg_zero]
    have hs' : n • s = 0 := hs
    rw [hm] at hs'
    have : s = (2 * m + 1) • s - m • (2 • s) := by
      rw [← mul_nsmul', add_nsmul, one_nsmul, mul_comm m 2]
      abel
    rw [this, hs', hs2, smul_zero, sub_zero]
  · have hi : i = 0 := Finset.sum_eq_zero fun w _ => by
      have := subsingleton_cohomology_two_of_isComplex w (hc.isComplex w)
      rw [show brauerLocal ι z (.inl w) = 0 from Subsingleton.elim (α := cohomology (galUnitsZ w.Completion
        (AlgebraicClosure w.Completion)) 2) _ 0, map_zero]
    rw [hi, add_zero] at h0
    exact h0

theorem sum_localInvU_eq_of_sub {n : ℕ} (hn : Odd n ∨ IsTotallyComplex K.1)
    (β β' : ∀ v : S, cohomology (galUnits.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) 2)
    (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2)
    (hy : ∀ v, β v - β' v = (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
      (continuous_toMonoidHom _) (gsSUnitsLocalMor S ιs v) 2).hom y)
    (hβ : n • ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (β v) = 0)
    (hβ' : n • ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (β' v) = 0) :
    ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (β v) =
      ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (β' v) := by
  have hdiff : ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (β v) -
      ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (β' v) =
      ∑ v : S, placeInv (.inr (v : HeightOneSpectrum (𝓞 K.1)))
        (brauerLocal (gsLocalEmbeddings S ιs) (sUnitsBrauer K S y) (.inr (v : HeightOneSpectrum (𝓞 K.1)))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    refine (map_sub _ _ _).symm.trans ?_
    refine (congrArg (localInvU (v : HeightOneSpectrum (𝓞 K.1))) (hy v)).trans ?_
    refine (localInvU_cohomologyMapAlong_gsSUnitsLocalMor S ιs v y).trans ?_
    refine Eq.symm ?_
    refine (congrArg (fun z => placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))
      (brauerLocal (gsLocalEmbeddings S ιs) z (.inr (v : HeightOneSpectrum (𝓞 K.1))))) (sUnitsBrauer_apply K S y)).trans ?_
    refine (congrArg (placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1))))
      (brauerLocal_gsBrauerInfl_inr K S _ _ _)).trans ?_
    simp only [gsLocalEmbeddings_fin]
  have hs : n • (∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (β v) -
      ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (β' v)) = 0 := by
    exact (smul_sub n _ _).trans ((congrArg₂ (· - ·) hβ hβ').trans (sub_zero 0))
  have h0 := sum_placeInv_inr_eq_zero_of S hn (gsLocalEmbeddings S ιs) (sUnitsBrauer K S y)
    (fun w hw => (congrArg (placeInv (.inr w)) (brauerLocal_sUnitsBrauer_inr K S (gsLocalEmbeddings S ιs) y w hw)).trans
      (map_zero _))
    ((congrArg (n • ·) hdiff).symm.trans hs)
  exact sub_eq_zero.1 (hdiff.trans h0)

end Inv

end

end GroundTheory.ProfCoh

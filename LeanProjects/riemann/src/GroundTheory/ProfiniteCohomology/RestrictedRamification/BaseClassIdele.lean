import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseClass
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IsDedekindDomain NumberField GroundTheory.Global IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section General

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {H : ι → Type} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)] [∀ v, IsTopologicalGroup (H v)]
  (φ : ∀ v, H v →ₜ* G) {U X : Rep.{0} k G} [IsDiscreteRep U] (j : U ⟶ X)
  (Ωᵥ : ∀ v, Rep.{0} k (H v)) [∀ v, IsDiscreteRep (Ωᵥ v)] (l : ∀ v, Rep.res (φ v).toMonoidHom X ⟶ Ωᵥ v)

theorem exists_dataCycle_eq
    (c : (compactCochains φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v)).cycles 1) :
    ∃ (x : (cochainsComplex U).X 1) (y : ∀ v, Ωᵥ v) (hx : ((cochainsComplex U).d 1 2).hom x = 0)
      (hy : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U x ![(φ v).toMonoidHom σ])) = (Ωᵥ v).ρ σ (y v) - y v),
      c = dataCycle φ j Ωᵥ l x y hx hy := by
  let q : (cochainsComplex U).X 1 × (piComplex fun v => cochainsComplex (Ωᵥ v)).X 0 :=
    ((compactCochains φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v)).iCycles 1).hom c
  have hd : (mappingCoconeNatD (localRes φ U Ωᵥ fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v) 1).hom
      q = 0 :=
    hom_apply_hom_apply_of_comp_eq
      ((compactCochains φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v)).iCycles_d 1 2) c
  have h2 := (mappingCoconeNatD_apply _ 1 q.1 q.2).symm.trans hd
  let y : ∀ v, Ωᵥ v := fun v => cochainOf (Ωᵥ v) (q.2 v) Fin.elim0
  have hyy : q.2 = piConst Ωᵥ y := funext fun v => cochainOf_injective (funext fun σ => by
    rw [Subsingleton.elim σ Fin.elim0]
    rfl)
  have hx : ((cochainsComplex U).d 1 2).hom q.1 = 0 := congrArg Prod.fst h2
  have hsnd := congrArg Prod.snd h2
  have hy : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U q.1 ![(φ v).toMonoidHom σ])) =
      (Ωᵥ v).ρ σ (y v) - y v := fun v σ => by
    have e := congrArg (fun w => cochainOf (Ωᵥ v) (w v) ![σ]) hsnd
    simp only at e
    rw [shiftNegOneD_succ_apply, shiftNegOneSucc_apply, hyy] at e
    change cochainOf (Ωᵥ v) ((((localRes φ U Ωᵥ fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v).f 1).hom q.1) v
      + -(((piComplex fun v => cochainsComplex (Ωᵥ v)).d 0 1).hom (piConst Ωᵥ y)) v) ![σ] = 0 at e
    rw [cochainOf_add, cochainOf_neg', Pi.add_apply, Pi.neg_apply, piComplex_d_hom_apply, piConst_apply,
      cochainOf_d_constCochain, cochainOf_localRes_f_apply, add_neg_eq_zero] at e
    refine Eq.trans ?_ e
    have hh : (⇑(φ v).toMonoidHom ∘ ![σ]) = ![(φ v).toMonoidHom σ] := by
      funext i
      fin_cases i
      rfl
    rw [hh]
    rfl
  refine ⟨q.1, y, hx, hy, ?_⟩
  apply (ModuleCat.mono_iff_injective ((compactCochains φ U Ωᵥ _).iCycles 1)).1 inferInstance
  rw [iCycles_dataCycle]
  exact Prod.ext rfl hyy

theorem exists_coboundary_of_subsingleton [IsDiscreteRep X] (hX : Subsingleton (cohomology X 1))
    (x : (cochainsComplex U).X 1) (hx : ((cochainsComplex U).d 1 2).hom x = 0) :
    ∃ T : X, ∀ σ : G, j.hom (cochainOf U x ![σ]) = X.ρ σ T - T := by
  have hx' : ((cochainsComplex X).d 1 (1 + 1)).hom (((cochainsMap j).f 1).hom x) = 0 :=
    (hom_apply_hom_apply_eq_of_comp_eq ((cochainsMap j).comm 1 2) x).trans (by rw [hx, map_zero])
  obtain ⟨z, hz⟩ := exists_iCycles_eq_of_d_eq_zero _ 1 _ hx'
  have h0 : ((cochainsComplex X).homologyπ (0 + 1)).hom z = 0 := Subsingleton.elim (α := cohomology X 1) _ _
  obtain ⟨w, hw⟩ := (homologyπ_succ_eq_zero_iff _ 0 z).1 h0
  refine ⟨cochainOf X w Fin.elim0, fun σ => ?_⟩
  have e : cochainOf X (((cochainsComplex X).d 0 (0 + 1)).hom w) ![σ] =
      cochainOf X (((cochainsMap j).f 1).hom x) ![σ] := congrArg (fun c => cochainOf X c ![σ]) (hw.trans hz)
  rw [cochainOf_cochainsMap_f] at e
  refine e.symm.trans ?_
  have hw0 : w = constCochain X (cochainOf X w Fin.elim0) :=
    cochainOf_injective (funext fun τ => by rw [Subsingleton.elim τ Fin.elim0]; rfl)
  rw [hw0, cochainOf_d_constCochain]
  rfl

theorem homologyπ_dataCycle_of_boundary (α : U) (x : (cochainsComplex U).X 1) (y : ∀ v, Ωᵥ v)
    (hx : ((cochainsComplex U).d 1 2).hom x = 0)
    (hy : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U x ![(φ v).toMonoidHom σ])) = (Ωᵥ v).ρ σ (y v) - y v)
    (hxα : ∀ σ : G, cochainOf U x ![σ] = U.ρ σ α - α) (hyα : ∀ v, y v = (l v).hom (j.hom α)) :
    ((compactCochains φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v)).homologyπ 1).hom
      (dataCycle φ j Ωᵥ l x y hx hy) = 0 := by
  refine (homologyπ_succ_eq_zero_iff _ 0 (dataCycle φ j Ωᵥ l x y hx hy)).2
    ⟨((constCochain U α, PUnit.unit) : (cochainsComplex U).X 0 ×
      shiftNegOneX (piComplex fun v => cochainsComplex (Ωᵥ v)) 0), ?_⟩
  rw [iCycles_dataCycle]
  refine (mappingCoconeNatD_apply _ 0 (constCochain U α) PUnit.unit).trans (Prod.ext ?_ ?_)
  · apply cochainOf_injective
    funext σ
    rw [cochainOf_d_constCochain]
    change _ = cochainOf U x σ
    have hσ : σ = ![σ 0] := by
      funext i
      fin_cases i
      rfl
    rw [hσ, hxα]
    rfl
  · change (((localRes φ U Ωᵥ fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v).f 0).hom
      (constCochain U α) : (piComplex fun v => cochainsComplex (Ωᵥ v)).X 0) + 0 = piConst Ωᵥ y
    rw [add_zero]
    funext v
    rw [piConst_apply]
    apply cochainOf_injective
    funext h
    rw [cochainOf_localRes_f_apply, cochainOf_constCochain, cochainOf_constCochain, hyα]
    rfl

theorem dataHom_surjective {D : Type} [AddCommGroup D] (xOf : D →+ (cochainsComplex U).X 1) (yOf : D →+ (∀ v, Ωᵥ v))
    (hx : ∀ d, ((cochainsComplex U).d 1 2).hom (xOf d) = 0)
    (hy : ∀ d v (σ : H v), (l v).hom (j.hom (cochainOf U (xOf d) ![(φ v).toMonoidHom σ])) =
      (Ωᵥ v).ρ σ (yOf d v) - yOf d v)
    (hd : ∀ (x : (cochainsComplex U).X 1) (y : ∀ v, Ωᵥ v), ((cochainsComplex U).d 1 2).hom x = 0 →
      (∀ v (σ : H v), (l v).hom (j.hom (cochainOf U x ![(φ v).toMonoidHom σ])) = (Ωᵥ v).ρ σ (y v) - y v) →
        ∃ d, xOf d = x ∧ yOf d = y) :
    Function.Surjective (dataHom φ j Ωᵥ l xOf yOf hx hy) := by
  intro h
  obtain ⟨c, rfl⟩ := homologyπ_surjective _ 1 h
  obtain ⟨x, y, hx', hy', rfl⟩ := exists_dataCycle_eq φ j Ωᵥ l c
  obtain ⟨d, hxd, hyd⟩ := hd x y hx' hy'
  exact ⟨d, (dataHom_apply φ j Ωᵥ l xOf yOf hx hy d).trans
    (congrArg _ (dataCycle_congr φ j Ωᵥ l hxd hyd _ _ _ _))⟩

theorem dataHom_eq_zero_of_boundary {D : Type} [AddCommGroup D] (xOf : D →+ (cochainsComplex U).X 1)
    (yOf : D →+ (∀ v, Ωᵥ v)) (hx : ∀ d, ((cochainsComplex U).d 1 2).hom (xOf d) = 0)
    (hy : ∀ d v (σ : H v), (l v).hom (j.hom (cochainOf U (xOf d) ![(φ v).toMonoidHom σ])) =
      (Ωᵥ v).ρ σ (yOf d v) - yOf d v) (d : D) (α : U)
    (hxα : ∀ σ : G, cochainOf U (xOf d) ![σ] = U.ρ σ α - α) (hyα : ∀ v, yOf d v = (l v).hom (j.hom α)) :
    dataHom φ j Ωᵥ l xOf yOf hx hy d = 0 :=
  (dataHom_apply φ j Ωᵥ l xOf yOf hx hy d).trans
    (homologyπ_dataCycle_of_boundary φ j Ωᵥ l α _ _ _ _ hxα hyα)

end General

section Concrete

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

theorem ρ_sub_eq_of_sub_eq {F : Type} [Monoid F] (B : Rep.{0} (ULift.{0} ℤ) F) (σ : F) {y m : B}
    (e : B.ρ σ m - m = B.ρ σ y - y) : B.ρ σ (y - m) = y - m := by
  rw [map_sub]
  exact sub_eq_sub_iff_sub_eq_sub.mp e.symm

theorem toMul_mem_sInvariantSubgroup (T : Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)
    (x : (cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).X 1)
    (hT : ∀ σ, (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom (cochainOf _ x ![σ]) =
      (galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ σ T - T) :
    Additive.toMul T ∈ sInvariantSubgroup (F := K.1) ℚ̄ S := fun σ => by
  have h' : galUnitsHom K.1 _ σ (Additive.toMul T) * (Additive.toMul T)⁻¹ =
      ((Additive.toMul (cochainOf _ x ![σ]) : sUnitsOf S (maxUnramifiedOutside K.1 ℚ̄ S)) :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) := (congrArg Additive.toMul (hT σ)).symm
  rw [h']
  exact (Additive.toMul (cochainOf _ x ![σ])).2

theorem sInvCochain_eq_of (t : sInvariantSubgroup (F := K.1) ℚ̄ S) (x : (cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).X 1)
    (hT : ∀ σ, (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom (cochainOf _ x ![σ]) =
      (galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ σ (Additive.ofMul (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) -
        Additive.ofMul (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) :
    sInvCochain S t = x := cochainOf_injective (funext fun σ => by
  have hσ : σ = ![σ 0] := by
    funext i
    fin_cases i
    rfl
  rw [hσ]
  exact sUnitsToUnits_injective S (maxUnramifiedOutside K.1 ℚ̄ S) ((sUnitsToUnits_sInvRatio S t (σ 0)).trans
    (hT (σ 0)).symm))

theorem exists_unitsToInvariants_eq_local (v : HeightOneSpectrum (𝓞 K.1))
    (y : galUnits.{0, 0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)))
    (hy : y ∈ (galUnits.{0, 0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))).ρ.invariants) :
    ∃ a, (unitsToInvariants.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) a).1 = y :=
  (unitsToInvariants_surjective _ _ ⟨y, hy⟩).imp fun _ ha => congrArg Subtype.val ha

theorem localUnitsAlgHom_eq_unitsToInvariants (v : S)
    (a : Additive ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ) :
    localUnitsAlgHom S v a = (unitsToInvariants.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) a).1 :=
  congrArg Additive.ofMul (Units.ext rfl)

theorem exists_localUnitsAlgHom_eq (v : S) (m y : galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
    (h : ∀ σ, (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))).ρ σ m - m =
      (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))).ρ σ y - y) :
    ∃ a : Additive ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ, localUnitsAlgHom S v a = y - m := by
  have hinv : y - m ∈ (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))).ρ.invariants :=
    (Representation.mem_invariants _ _).2 fun σ => ρ_sub_eq_of_sub_eq (galUnits.{0, 0}
      ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) σ (h σ)
  exact (exists_unitsToInvariants_eq_local (K := K) (v : HeightOneSpectrum (𝓞 K.1)) (y - m) hinv).imp
    fun a ha => (localUnitsAlgHom_eq_unitsToInvariants S v a).trans ha

theorem exists_units_coboundary (x : (cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).X 1)
    (hx : ((cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).d 1 2).hom x = 0) :
    ∃ T : galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S), ∀ σ,
      (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom (cochainOf _ x ![σ]) =
        (galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ σ T - T :=
  exists_coboundary_of_subsingleton (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S))
    (subsingleton_cohomology_one_galUnits (K := K.1) (L := maxUnramifiedOutside K.1 ℚ̄ S)) x hx

theorem exists_gsUnitsDatum (x : (cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).X 1)
    (y : ∀ v : S, galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
    (hx : ((cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).d 1 2).hom x = 0)
    (hy : ∀ (v : S) (σ : Gal(AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) /
      (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)),
      (gsUnitsLocalMor.{0} S ιs v).hom ((sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom
        (cochainOf _ x ![(gsFinFamily S ιs v).toMonoidHom σ])) = (galUnits.{0, 0} _ _).ρ σ (y v) - y v) :
    ∃ d : GsUnitsDatum S, (sInvCochainHom S).comp (AddMonoidHom.fst _ _) d = x ∧ dataLocalHom S ιs d = y := by
  refine (exists_units_coboundary S x hx).elim fun T hT => ?_
  let t : sInvariantSubgroup (F := K.1) ℚ̄ S := Subtype.mk (Additive.toMul T) (toMul_mem_sInvariantSubgroup S T x hT)
  have ha : ∀ v : S, ∃ a, localUnitsAlgHom S v a = y v - sInvLocalHom S ιs v (Additive.ofMul t) := fun v =>
    exists_localUnitsAlgHom_eq S v _ (y v) fun σ => (hom_res_sub _ (gsUnitsLocalMor.{0} S ιs v) σ T).symm.trans
      ((congrArg (gsUnitsLocalMor.{0} S ιs v).hom (hT _)).symm.trans (hy v σ))
  exact ⟨(Additive.ofMul t, fun v => Classical.choose (ha v)), sInvCochain_eq_of S t x hT,
    funext fun v => (congrArg (· + sInvLocalHom S ιs v (Additive.ofMul t)) (Classical.choose_spec (ha v))).trans
      (sub_add_cancel _ _)⟩

theorem gsUnitsData_surjective : Function.Surjective (gsUnitsData S ιs) :=
  dataHom_surjective _ _ _ _ _ _ _ _ fun x y hx hy => exists_gsUnitsDatum S ιs x y hx hy

def sInvOfUnit (x : (K.1)ˣ) : sInvariantSubgroup (F := K.1) ℚ̄ S :=
  ⟨_, map_algebraMap_mem_sInvariantSubgroup (Ω := ℚ̄) S x⟩

theorem galUnits_ρ_sInvOfUnit (x : (K.1)ˣ) (σ : galUnramifiedOutside K.1 ℚ̄ S) :
    (galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ σ
        (Additive.ofMul ((sInvOfUnit S x : sInvariantSubgroup (F := K.1) ℚ̄ S) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) =
      Additive.ofMul ((sInvOfUnit S x : sInvariantSubgroup (F := K.1) ℚ̄ S) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :=
  congrArg Additive.ofMul (Units.ext (σ.commutes _))

theorem gsUnitsLocalMor_sInvOfUnit (x : (K.1)ˣ) (v : S) :
    (gsUnitsLocalMor.{0} S ιs v).hom
        (Additive.ofMul ((sInvOfUnit S x : sInvariantSubgroup (F := K.1) ℚ̄ S) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) =
      localUnitsAlgHom S v (Additive.ofMul (finiteProj (v : HeightOneSpectrum (𝓞 K.1)) (diagonal K.1 x))) :=
  congrArg Additive.ofMul (Units.ext (((ιs v).commutes (x : K.1)).trans
    (IsScalarTower.algebraMap_apply K.1 ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (x : K.1))))

theorem hom_sub_comm {F : Type} [Monoid F] {A B : Rep.{0} (ULift.{0} ℤ) F} (f : A ⟶ B) (g : F) (a : A) :
    f.hom (A.ρ g a - a) = B.ρ g (f.hom a) - f.hom a := by
  rw [map_sub]
  congr 1
  exact Rep.hom_comm_apply f g a

section IdeleClass

variable [Finite S]

def gsUnitsPresentationData :
    GsUnitsDatum S →+ Additive ((∀ w : S, ((w : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ) ×
      Multiplicative (sDivisor S)) :=
  AddMonoidHom.mk' (fun d => Additive.ofMul (fun w => Additive.toMul (d.2 w),
      Multiplicative.ofAdd (-divAbove S d.1))) fun d d' =>
    congrArg Additive.ofMul (Prod.ext rfl (congrArg Multiplicative.ofAdd
      ((congrArg Neg.neg (map_add (divAbove S) d.1 d'.1)).trans (neg_add _ _))))

def gsUnitsClass : GsUnitsDatum S →+ Additive (SIdeleClassGroup S) :=
  (MonoidHom.toAdditive (sPresentation S)).comp (gsUnitsPresentationData S)

theorem gsUnitsClass_apply (d : GsUnitsDatum S) :
    gsUnitsClass S d = Additive.ofMul (sPresentation S (fun w => Additive.toMul (d.2 w),
      Multiplicative.ofAdd (-divAbove S d.1))) :=
  rfl

omit [Finite S] in

theorem mul_sInvOfUnit_mem_sUnitsMax (t : Additive (sInvariantSubgroup (F := K.1) ℚ̄ S)) (x : (K.1)ˣ)
    (h : divS S (Additive.ofMul x) = -divAbove S t) :
    ((Additive.toMul (t + Additive.ofMul (sInvOfUnit S x)) : sInvariantSubgroup (F := K.1) ℚ̄ S) :
      (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) ∈ sUnitsMax K.1 ℚ̄ S :=
  mem_sUnitsMax_of_divAbove_eq_zero S (((map_add (divAbove S) _ _).trans
    (congrArg (divAbove S t + ·) ((divAbove_algebraMap S x).trans h))).trans (add_neg_cancel _))

theorem gsUnitsData_eq_zero_of_gsUnitsClass_eq_zero (d : GsUnitsDatum S) (h : gsUnitsClass S d = 0) :
    gsUnitsData S ιs d = 0 := by
  have h2 : ((fun w => Additive.toMul (d.2 w), Multiplicative.ofAdd (-divAbove S d.1)) :
      (∀ w : S, ((w : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ) × Multiplicative (sDivisor S)) ∈
      (principalPresentation S).range := by
    rw [← ker_sPresentation]
    exact congrArg Additive.toMul h
  refine h2.elim fun x hx => ?_
  have hx1 : ∀ w : S, finiteProj (w : HeightOneSpectrum (𝓞 K.1)) (diagonal K.1 x) = Additive.toMul (d.2 w) :=
    fun w => congrFun (congrArg Prod.fst hx) w
  have hx2 : divS S (Additive.ofMul x) = -divAbove S d.1 := congrArg Multiplicative.toAdd (congrArg Prod.snd hx)
  have hu := mul_sInvOfUnit_mem_sUnitsMax S d.1 x hx2
  refine dataHom_eq_zero_of_boundary _ _ _ _ _ _ _ _ d (Additive.ofMul ⟨_, hu⟩) (fun σ => ?_) (fun v => ?_)
  · refine sUnitsToUnits_injective S (maxUnramifiedOutside K.1 ℚ̄ S) ((sUnitsToUnits_sInvRatio S _ σ).trans ?_)
    refine Eq.trans ?_ (hom_sub_comm _ σ _).symm
    exact (ρ_add_sub_of_invariant _ σ (galUnits_ρ_sInvOfUnit S x σ)).symm.trans
      (congrArg (fun z => (galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ σ z - z) (add_comm _ _))
  · refine Eq.trans ?_ (map_add (gsUnitsLocalMor.{0} S ιs v).hom _ _).symm
    exact (congrArg (· + _) ((congrArg (localUnitsAlgHom S v) (congrArg Additive.ofMul (hx1 v))).symm.trans
      (gsUnitsLocalMor_sInvOfUnit S ιs x v).symm)).trans (add_comm _ _)

theorem exists_coprime_gsUnitsClass_eq (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (x : Additive (SIdeleClassGroup S)) :
    ∃ m : ℕ, m.Coprime ℓ ∧ ∃ d : GsUnitsDatum S, gsUnitsClass S d = m • x := by
  refine (sPresentation_surjective S (Additive.toMul x)).elim fun p hp => ?_
  have ho : addOrderOf (sPicMk S (Multiplicative.toAdd p.2)) ≠ 0 :=
    (isOfFinAddOrder_of_finite _).addOrderOf_pos.ne'
  refine (Nat.exists_eq_pow_mul_and_not_dvd ho ℓ hℓ.ne_one).elim fun j hj => hj.elim fun m hm => ?_
  have hc : sPicMk S (ℓ ^ j • (m • Multiplicative.toAdd p.2)) = 0 := by
    rw [map_nsmul, map_nsmul, smul_smul, ← hm.2]
    exact addOrderOf_nsmul_eq_zero _
  refine ((sPicMk_eq_zero_iff S _).1 hc).elim fun a ha => ?_
  have hNS : ∀ v ∉ S, (((ℓ ^ j : ℕ) : ℕ) : 𝓞 K.1) ∉ v.asIdeal := fun v hv hmem => hv (hS v (by
    rw [Nat.cast_pow] at hmem
    exact v.isPrime.mem_of_pow_mem j hmem))
  refine (exists_divAbove_eq (Ω := ℚ̄) S (pow_ne_zero j hℓ.ne_zero) hNS _ a ha).elim fun y hy => ?_
  refine ⟨m, (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hm.1),
    (-Additive.ofMul y, fun w => m • Additive.ofMul (p.1 w)), ?_⟩
  rw [gsUnitsClass_apply]
  have hpair : ((fun w => Additive.toMul (m • Additive.ofMul (p.1 w))),
      Multiplicative.ofAdd (-divAbove S (-Additive.ofMul y))) = p ^ m := by
    refine Prod.ext (funext fun w => ?_) ?_
    · exact toMul_nsmul _ _
    · change Multiplicative.ofAdd (-divAbove S (-Additive.ofMul y)) = p.2 ^ m
      have e : -divAbove S (-Additive.ofMul y) = m • Multiplicative.toAdd p.2 := by
        rw [map_neg (divAbove S), neg_neg, hy]
      rw [e, ofAdd_nsmul]
      rfl
  rw [hpair, map_pow, ofMul_pow, hp]
  rfl

end IdeleClass

end Concrete

end

end GroundTheory.ProfCoh

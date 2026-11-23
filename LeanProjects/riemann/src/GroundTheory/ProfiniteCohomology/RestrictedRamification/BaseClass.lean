import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummerDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SInvariantToInvariantsEqZeroIff
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SPicFinite
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGSPresentation
import GroundTheory.ProfiniteCohomology.CyclicCupProf
import GroundTheory.ProfiniteCohomology.LocalTateDuality.Bockstein
import GroundTheory.ProfiniteCohomology.InflationRestriction.DegreeOne
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.ConePairing
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IsDedekindDomain NumberField GroundTheory.Global IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section General

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {H : ι → Type} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)] [∀ v, IsTopologicalGroup (H v)]
  (φ : ∀ v, H v →ₜ* G)

def constCochain {F : Type} [Group F] [TopologicalSpace F] [IsTopologicalGroup F] (B : Rep.{0} k F)
    [IsDiscreteRep B] (m : B) : (cochainsComplex B).X 0 :=
  mkCochain B (fun _ => m) (IsLocallyConstant.const m)

theorem cochainOf_constCochain {F : Type} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    (B : Rep.{0} k F) [IsDiscreteRep B] (m : B) (σ : Fin 0 → F) :
    cochainOf B (constCochain B m) σ = m :=
  rfl

theorem cochainOf_d_constCochain {F : Type} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    (B : Rep.{0} k F) [IsDiscreteRep B] (m : B) (σ : Fin 1 → F) :
    cochainOf B (((cochainsComplex B).d 0 1).hom (constCochain B m)) σ = B.ρ (σ 0) m - m := by
  rw [cochainOf_d]
  simp [inhomogeneousCochains.d_hom_apply, cochainOf_constCochain, sub_eq_add_neg]

theorem cochainOf_neg' (B : Rep.{0} k G) [IsDiscreteRep B] {n : ℕ} (a : (cochainsComplex B).X n) :
    cochainOf B (-a) = -cochainOf B a :=
  rfl

theorem cochainOf_localRes_f_apply (A : Rep.{0} k G) [IsDiscreteRep A] (Aᵥ : ∀ v, Rep.{0} k (H v))
    [∀ v, IsDiscreteRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v) {n : ℕ}
    (x : (cochainsComplex A).X n) (v : ι) (h : Fin n → H v) :
    cochainOf (Aᵥ v) (((localRes φ A Aᵥ a).f n).hom x v) h = (a v).hom (cochainOf A x (⇑(φ v).toMonoidHom ∘ h)) :=
  rfl

theorem hom_res_sub {F F' : Type} [Monoid F] [Monoid F'] (ψ : F →* F') {X : Rep.{0} k F'} {B : Rep.{0} k F}
    (f : Rep.res ψ X ⟶ B) (g : F) (a : X) : f.hom (X.ρ (ψ g) a - a) = B.ρ g (f.hom a) - f.hom a := by
  rw [map_sub]
  congr 1
  exact Rep.hom_comm_apply f g a

theorem ρ_add_sub_of_invariant {F : Type} [Monoid F] (B : Rep.{0} k F) (g : F) {A M : B} (hA : B.ρ g A = A) :
    B.ρ g (A + M) - (A + M) = B.ρ g M - M := by
  rw [map_add, hA]
  abel

theorem comp_hom_apply' {F : Type} [Monoid F] {A B C : Rep.{0} k F} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    (f ≫ g).hom x = g.hom (f.hom x) :=
  rfl

variable {U X : Rep.{0} k G} [IsDiscreteRep U] (j : U ⟶ X)
  (Ωᵥ : ∀ v, Rep.{0} k (H v)) [∀ v, IsDiscreteRep (Ωᵥ v)] (l : ∀ v, Rep.res (φ v).toMonoidHom X ⟶ Ωᵥ v)

def piConst (y : ∀ v, Ωᵥ v) : (piComplex fun v => cochainsComplex (Ωᵥ v)).X 0 :=
  show ∀ v, (cochainsComplex (Ωᵥ v)).X 0 from fun v => constCochain (Ωᵥ v) (y v)

theorem piConst_apply (y : ∀ v, Ωᵥ v) (v : ι) : piConst Ωᵥ y v = constCochain (Ωᵥ v) (y v) :=
  rfl

def dataCochain (x : (cochainsComplex U).X 1) (y : ∀ v, Ωᵥ v) :
    (compactCochains φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v)).X 1 :=
  ((x, piConst Ωᵥ y) : (cochainsComplex U).X 1 × (piComplex fun v => cochainsComplex (Ωᵥ v)).X 0)

theorem d_dataCochain (x : (cochainsComplex U).X 1) (y : ∀ v, Ωᵥ v)
    (hx : ((cochainsComplex U).d 1 2).hom x = 0)
    (hy : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U x ![(φ v).toMonoidHom σ])) = (Ωᵥ v).ρ σ (y v) - y v) :
    ((compactCochains φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v)).d 1 2).hom
      (dataCochain φ j Ωᵥ l x y) = 0 := by
  refine (mappingCoconeNatD_apply (localRes φ U Ωᵥ fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v) 1 x
    (piConst Ωᵥ y)).trans (Prod.ext hx ?_)
  rw [shiftNegOneD_succ_apply, shiftNegOneSucc_apply]
  funext v
  show (((localRes φ U Ωᵥ fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v).f 1).hom x) v +
    (-(((piComplex fun v => cochainsComplex (Ωᵥ v)).d 0 1).hom (piConst Ωᵥ y))) v = 0
  rw [show (-(((piComplex fun v => cochainsComplex (Ωᵥ v)).d 0 1).hom (piConst Ωᵥ y))) v =
    -((((piComplex fun v => cochainsComplex (Ωᵥ v)).d 0 1).hom (piConst Ωᵥ y)) v) from rfl,
    piComplex_d_hom_apply, piConst_apply]
  apply cochainOf_injective
  funext h
  have hh : (⇑(φ v).toMonoidHom ∘ h) = ![(φ v).toMonoidHom (h 0)] := by
    funext i
    fin_cases i
    rfl
  rw [cochainOf_add, cochainOf_neg', Pi.add_apply, Pi.neg_apply, cochainOf_zero, Pi.zero_apply]
  erw [cochainOf_d_constCochain, cochainOf_localRes_f_apply]
  rw [comp_hom_apply', hh]
  change (l v).hom (j.hom (cochainOf U x ![(φ v).toMonoidHom (h 0)])) + _ = _
  rw [hy v (h 0), add_neg_cancel]

def dataCycle (x : (cochainsComplex U).X 1) (y : ∀ v, Ωᵥ v)
    (hx : ((cochainsComplex U).d 1 2).hom x = 0)
    (hy : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U x ![(φ v).toMonoidHom σ])) = (Ωᵥ v).ρ σ (y v) - y v) :
    (compactCochains φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v)).cycles 1 :=
  (compactCochains φ U Ωᵥ _).cyclesMk (dataCochain φ j Ωᵥ l x y) 2 (by simp) (d_dataCochain φ j Ωᵥ l x y hx hy)

theorem iCycles_dataCycle (x : (cochainsComplex U).X 1) (y : ∀ v, Ωᵥ v)
    (hx : ((cochainsComplex U).d 1 2).hom x = 0)
    (hy : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U x ![(φ v).toMonoidHom σ])) = (Ωᵥ v).ρ σ (y v) - y v) :
    ((compactCochains φ U Ωᵥ _).iCycles 1).hom (dataCycle φ j Ωᵥ l x y hx hy) = dataCochain φ j Ωᵥ l x y :=
  (compactCochains φ U Ωᵥ _).i_cyclesMk _ _ _ _

theorem dataCochain_fst (x : (cochainsComplex U).X 1) (y : ∀ v, Ωᵥ v) :
    (dataCochain φ j Ωᵥ l x y).1 = x :=
  rfl

theorem dataCochain_snd (x : (cochainsComplex U).X 1) (y : ∀ v, Ωᵥ v) :
    (dataCochain φ j Ωᵥ l x y).2 = piConst Ωᵥ y :=
  rfl

theorem dataCochain_add (x x' : (cochainsComplex U).X 1) (y y' : ∀ v, Ωᵥ v) :
    dataCochain φ j Ωᵥ l (x + x') (y + y') = dataCochain φ j Ωᵥ l x y + dataCochain φ j Ωᵥ l x' y' :=
  rfl

theorem dataCochain_zero : dataCochain φ j Ωᵥ l 0 0 = 0 :=
  rfl

theorem dataCycle_congr {x x' : (cochainsComplex U).X 1} {y y' : ∀ v, Ωᵥ v} (ex : x = x') (ey : y = y')
    (hx : ((cochainsComplex U).d 1 2).hom x = 0) (hx' : ((cochainsComplex U).d 1 2).hom x' = 0)
    (hy : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U x ![(φ v).toMonoidHom σ])) = (Ωᵥ v).ρ σ (y v) - y v)
    (hy' : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U x' ![(φ v).toMonoidHom σ])) = (Ωᵥ v).ρ σ (y' v) - y' v) :
    dataCycle φ j Ωᵥ l x y hx hy = dataCycle φ j Ωᵥ l x' y' hx' hy' := by
  subst ex ey
  rfl

theorem d_add_eq_zero {x x' : (cochainsComplex U).X 1} (hx : ((cochainsComplex U).d 1 2).hom x = 0)
    (hx' : ((cochainsComplex U).d 1 2).hom x' = 0) : ((cochainsComplex U).d 1 2).hom (x + x') = 0 := by
  rw [map_add, hx, hx', add_zero]

omit [∀ v, IsTopologicalGroup (H v)] [∀ v, IsDiscreteRep (Ωᵥ v)] in
theorem hy_add {x x' : (cochainsComplex U).X 1} {y y' : ∀ v, Ωᵥ v}
    (hy : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U x ![(φ v).toMonoidHom σ])) = (Ωᵥ v).ρ σ (y v) - y v)
    (hy' : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U x' ![(φ v).toMonoidHom σ])) = (Ωᵥ v).ρ σ (y' v) - y' v) :
    ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U (x + x') ![(φ v).toMonoidHom σ])) =
      (Ωᵥ v).ρ σ ((y + y') v) - (y + y') v := fun v σ => by
  rw [cochainOf_add, Pi.add_apply, map_add, map_add, hy v σ, hy' v σ, Pi.add_apply, map_add]
  abel

theorem dataCycle_add (x x' : (cochainsComplex U).X 1) (y y' : ∀ v, Ωᵥ v)
    (hx : ((cochainsComplex U).d 1 2).hom x = 0) (hx' : ((cochainsComplex U).d 1 2).hom x' = 0)
    (hxx' : ((cochainsComplex U).d 1 2).hom (x + x') = 0)
    (hy : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U x ![(φ v).toMonoidHom σ])) = (Ωᵥ v).ρ σ (y v) - y v)
    (hy' : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U x' ![(φ v).toMonoidHom σ])) = (Ωᵥ v).ρ σ (y' v) - y' v)
    (hyy' : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U (x + x') ![(φ v).toMonoidHom σ])) =
      (Ωᵥ v).ρ σ ((y + y') v) - (y + y') v) :
    dataCycle φ j Ωᵥ l (x + x') (y + y') hxx' hyy' =
      dataCycle φ j Ωᵥ l x y hx hy + dataCycle φ j Ωᵥ l x' y' hx' hy' := by
  apply (ModuleCat.mono_iff_injective ((compactCochains φ U Ωᵥ _).iCycles 1)).1 inferInstance
  rw [map_add, iCycles_dataCycle, iCycles_dataCycle, iCycles_dataCycle, dataCochain_add]

theorem dataCycle_zero (hx : ((cochainsComplex U).d 1 2).hom 0 = 0)
    (hy : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U (0 : (cochainsComplex U).X 1) ![(φ v).toMonoidHom σ])) =
      (Ωᵥ v).ρ σ ((0 : ∀ v, Ωᵥ v) v) - (0 : ∀ v, Ωᵥ v) v) :
    dataCycle φ j Ωᵥ l 0 0 hx hy = 0 := by
  apply (ModuleCat.mono_iff_injective ((compactCochains φ U Ωᵥ _).iCycles 1)).1 inferInstance
  rw [map_zero, iCycles_dataCycle, dataCochain_zero]

def dataHom {D : Type} [AddCommGroup D] (xOf : D →+ (cochainsComplex U).X 1) (yOf : D →+ (∀ v, Ωᵥ v))
    (hx : ∀ d, ((cochainsComplex U).d 1 2).hom (xOf d) = 0)
    (hy : ∀ d v (σ : H v), (l v).hom (j.hom (cochainOf U (xOf d) ![(φ v).toMonoidHom σ])) =
      (Ωᵥ v).ρ σ (yOf d v) - yOf d v) :
    D →+ (compactCochains φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v)).homology 1 where
  toFun d := ((compactCochains φ U Ωᵥ _).homologyπ 1).hom (dataCycle φ j Ωᵥ l (xOf d) (yOf d) (hx d) (hy d))
  map_zero' := by
    rw [dataCycle_congr φ j Ωᵥ l (map_zero xOf) (map_zero yOf) (hx 0) (map_zero _) (hy 0)
      (fun v σ => by rw [cochainOf_zero, Pi.zero_apply, map_zero, map_zero, Pi.zero_apply, map_zero, sub_zero]),
      dataCycle_zero, map_zero]
  map_add' d d' := by
    rw [dataCycle_congr φ j Ωᵥ l (map_add xOf d d') (map_add yOf d d') (hx _)
      (d_add_eq_zero (hx d) (hx d')) (hy _) (hy_add φ j Ωᵥ l (hy d) (hy d')),
      dataCycle_add _ _ _ _ _ _ _ _ (hx d) (hx d'), map_add]

theorem dataHom_apply {D : Type} [AddCommGroup D] (xOf : D →+ (cochainsComplex U).X 1) (yOf : D →+ (∀ v, Ωᵥ v))
    (hx : ∀ d, ((cochainsComplex U).d 1 2).hom (xOf d) = 0)
    (hy : ∀ d v (σ : H v), (l v).hom (j.hom (cochainOf U (xOf d) ![(φ v).toMonoidHom σ])) =
      (Ωᵥ v).ρ σ (yOf d v) - yOf d v) (d : D) :
    dataHom φ j Ωᵥ l xOf yOf hx hy d =
      ((compactCochains φ U Ωᵥ _).homologyπ 1).hom (dataCycle φ j Ωᵥ l (xOf d) (yOf d) (hx d) (hy d)) :=
  rfl

theorem homologyπ_dataCycle_zero_of_invariant (y : ∀ v, Ωᵥ v) (hy0 : ∀ v (σ : H v), (Ωᵥ v).ρ σ (y v) = y v)
    (hx : ((cochainsComplex U).d 1 2).hom 0 = 0)
    (hy : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U (0 : (cochainsComplex U).X 1) ![(φ v).toMonoidHom σ])) =
      (Ωᵥ v).ρ σ (y v) - y v) :
    ((compactCochains φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v)).homologyπ 1).hom
        (dataCycle φ j Ωᵥ l 0 y hx hy) =
      (localToCompact φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v) 0).hom
        (fun v => (H0Iso (Ωᵥ v)).inv.hom ⟨y v, (Representation.mem_invariants _ _).2 (hy0 v)⟩) := by
  have hd : ((piComplex fun v => cochainsComplex (Ωᵥ v)).d 0 1).hom (piConst Ωᵥ y) = 0 := by
    funext v
    rw [piComplex_d_hom_apply, piConst_apply]
    apply cochainOf_injective
    funext h
    rw [cochainOf_d_constCochain, hy0, sub_self]
    rfl
  obtain ⟨c, hc⟩ := exists_iCycles_eq_of_d_eq_zero _ 0 (piConst Ωᵥ y) hd
  have hv : ∀ v, ((piComplex fun v => cochainsComplex (Ωᵥ v)).homologyπ 0 ≫
      HomologicalComplex.homologyMap (piProj (fun v => cochainsComplex (Ωᵥ v)) v) 0).hom c =
      (H0Iso (Ωᵥ v)).inv.hom ⟨y v, (Representation.mem_invariants _ _).2 (hy0 v)⟩ := fun v => by
    obtain ⟨z0, hz0, hz0c⟩ := exists_cocycle_H0Iso_inv (Ωᵥ v) ⟨y v, (Representation.mem_invariants _ _).2 (hy0 v)⟩
    rw [HomologicalComplex.homologyπ_naturality, ModuleCat.hom_comp, LinearMap.comp_apply, ← hz0]
    congr 1
    apply (ModuleCat.mono_iff_injective ((cochainsComplex (Ωᵥ v)).iCycles 0)).1 inferInstance
    refine (hom_apply_hom_apply_eq_of_comp_eq (HomologicalComplex.cyclesMap_i _ _) c).trans ?_
    rw [hc, piProj_f_hom_apply, piConst_apply]
    apply cochainOf_injective
    exact (funext fun _ => rfl : cochainOf (Ωᵥ v) (constCochain (Ωᵥ v) (y v)) = fun _ => y v).trans hz0c.symm
  have h1 : (localCohomologyIso Ωᵥ 0).hom.hom (((piComplex fun v => cochainsComplex (Ωᵥ v)).homologyπ 0).hom c) =
      fun v => (H0Iso (Ωᵥ v)).inv.hom ⟨y v, (Representation.mem_invariants _ _).2 (hy0 v)⟩ :=
    funext fun v => (piHomologyIso_hom_apply _ 0 _ v).trans (hv v)
  obtain ⟨c', hc', hc'i⟩ := mappingCoconeNat.exists_homologyδ_homologyπ
    (localRes φ U Ωᵥ fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v) 0 c
  have h2 : dataCycle φ j Ωᵥ l 0 y hx hy = c' := by
    apply (ModuleCat.mono_iff_injective ((compactCochains φ U Ωᵥ _).iCycles 1)).1 inferInstance
    rw [iCycles_dataCycle]
    refine Eq.trans ?_ hc'i.symm
    rw [hc]
    rfl
  rw [h2]
  refine hc'.symm.trans ?_
  rw [← h1]
  exact congrArg (mappingCoconeNat.homologyδ _ 0).hom (Iso.hom_inv_id_apply (localCohomologyIso Ωᵥ 0) _).symm

theorem dataHom_eq_localToCompact {D : Type} [AddCommGroup D] (xOf : D →+ (cochainsComplex U).X 1)
    (yOf : D →+ (∀ v, Ωᵥ v)) (hx : ∀ d, ((cochainsComplex U).d 1 2).hom (xOf d) = 0)
    (hy : ∀ d v (σ : H v), (l v).hom (j.hom (cochainOf U (xOf d) ![(φ v).toMonoidHom σ])) =
      (Ωᵥ v).ρ σ (yOf d v) - yOf d v) (d : D) (hx0 : xOf d = 0) (y : ∀ v, Ωᵥ v) (hyd : yOf d = y)
    (hy0 : ∀ v (σ : H v), (Ωᵥ v).ρ σ (y v) = y v) :
    dataHom φ j Ωᵥ l xOf yOf hx hy d =
      (localToCompact φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v) 0).hom
        (fun v => (H0Iso (Ωᵥ v)).inv.hom ⟨y v, (Representation.mem_invariants _ _).2 (hy0 v)⟩) := by
  have hy' : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U (0 : (cochainsComplex U).X 1) ![(φ v).toMonoidHom σ])) =
      (Ωᵥ v).ρ σ (y v) - y v := fun v σ => by
    rw [cochainOf_zero, Pi.zero_apply, map_zero, map_zero, hy0, sub_self]
  rw [dataHom_apply, dataCycle_congr φ j Ωᵥ l hx0 hyd (hx d) (map_zero _) (hy d) hy']
  exact homologyπ_dataCycle_zero_of_invariant φ j Ωᵥ l y hy0 _ hy'

end General

section Concrete

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

def sInvRatio (t : sInvariantSubgroup (F := K.1) ℚ̄ S) (σ : galUnramifiedOutside K.1 ℚ̄ S) :
    galSUnitsMax K.1 ℚ̄ S :=
  Additive.ofMul ⟨galUnitsHom K.1 _ σ (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) *
    (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)⁻¹, (mem_sInvariantSubgroup S).1 t.2 σ⟩

theorem sUnitsToUnits_sInvRatio (t : sInvariantSubgroup (F := K.1) ℚ̄ S) (σ : galUnramifiedOutside K.1 ℚ̄ S) :
    (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom (sInvRatio S t σ) =
      (galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ σ
          (Additive.ofMul (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) -
        Additive.ofMul (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :=
  rfl

theorem sInvRatio_mul (t t' : sInvariantSubgroup (F := K.1) ℚ̄ S) (σ : galUnramifiedOutside K.1 ℚ̄ S) :
    sInvRatio S (t * t') σ = sInvRatio S t σ + sInvRatio S t' σ :=
  Additive.toMul.injective (Subtype.ext (galUnitsHom_mul_inv_eq S σ (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) t'))

theorem isLocallyConstant_sInvRatio (t : sInvariantSubgroup (F := K.1) ℚ̄ S) :
    IsLocallyConstant (sInvRatio S t) := by
  refine IsLocallyConstant.desc _ (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom ?_
    (sUnitsToUnits_injective S _)
  have : (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom ∘ sInvRatio S t =
      fun σ => (galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ σ
          (Additive.ofMul (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) -
        Additive.ofMul (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :=
    funext fun σ => sUnitsToUnits_sInvRatio S t σ
  rw [this]
  exact (isLocallyConstant_apply _ _).sub (IsLocallyConstant.const _)

def sInvCochain (t : sInvariantSubgroup (F := K.1) ℚ̄ S) : (cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).X 1 :=
  mkCochain _ (fun σ : Fin 1 → galUnramifiedOutside K.1 ℚ̄ S => sInvRatio S t (σ 0))
    ((isLocallyConstant_sInvRatio S t).comp_continuous (continuous_apply 0))

theorem cochainOf_sInvCochain (t : sInvariantSubgroup (F := K.1) ℚ̄ S) (σ : Fin 1 → galUnramifiedOutside K.1 ℚ̄ S) :
    cochainOf _ (sInvCochain S t) σ = sInvRatio S t (σ 0) :=
  rfl

theorem sInvCochain_mul (t t' : sInvariantSubgroup (F := K.1) ℚ̄ S) :
    sInvCochain S (t * t') = sInvCochain S t + sInvCochain S t' :=
  cochainOf_injective (funext fun σ => sInvRatio_mul S t t' (σ 0))

theorem cochainsMap_sUnitsToUnits_sInvCochain (t : sInvariantSubgroup (F := K.1) ℚ̄ S) :
    ((cochainsMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S))).f 1).hom (sInvCochain S t) =
      ((cochainsComplex (galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S))).d 0 1).hom
        (constCochain _ (Additive.ofMul (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ))) := by
  apply cochainOf_injective
  funext σ
  rw [cochainOf_cochainsMap_f]
  exact (sUnitsToUnits_sInvRatio S t (σ 0)).trans (cochainOf_d_constCochain _ _ σ).symm

theorem d_sInvCochain (t : sInvariantSubgroup (F := K.1) ℚ̄ S) :
    ((cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).d 1 2).hom (sInvCochain S t) = 0 := by
  have hinj : Function.Injective
      ((cochainsMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S))).f 2).hom := fun x y hxy => by
    apply cochainOf_injective
    funext σ
    apply sUnitsToUnits_injective S (maxUnramifiedOutside K.1 ℚ̄ S)
    have := congrFun (congrArg (cochainOf _) hxy) σ
    rwa [cochainOf_cochainsMap_f, cochainOf_cochainsMap_f] at this
  apply hinj
  rw [map_zero]
  have hc := hom_apply_hom_apply_eq_of_comp_eq
    ((cochainsMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S))).comm 1 2) (sInvCochain S t)
  refine hc.symm.trans ?_
  rw [cochainsMap_sUnitsToUnits_sInvCochain]
  exact hom_apply_hom_apply_of_comp_eq ((cochainsComplex _).d_comp_d 0 1 2) _

def localUnitsAlgHom (v : S) :
    Additive ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ →+
      galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
  MonoidHom.toAdditive (α := ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ)
    (β := (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))ˣ)
    (Units.map (algebraMap ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))).toMonoidHom)

def sInvLocalHom (v : S) :
    Additive (sInvariantSubgroup (F := K.1) ℚ̄ S) →+
      galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
  (gsUnitsLocalMor.{0} S ιs v).hom.toAddMonoidHom.comp
    (MonoidHom.toAdditive (α := sInvariantSubgroup (F := K.1) ℚ̄ S) (β := (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)
      (sInvariantSubgroup (F := K.1) ℚ̄ S).subtype)

def dataLocalUnit (t : sInvariantSubgroup (F := K.1) ℚ̄ S) (v : S)
    (a : Additive ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ) :
    galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
  localUnitsAlgHom S v a + sInvLocalHom S ιs v (Additive.ofMul t)

theorem dataLocalUnit_add (t t' : sInvariantSubgroup (F := K.1) ℚ̄ S) (v : S)
    (a a' : Additive ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ) :
    dataLocalUnit S ιs (t * t') v (a + a') = dataLocalUnit S ιs t v a + dataLocalUnit S ιs t' v a' :=
  (congrArg₂ (· + ·) (map_add (localUnitsAlgHom S v) a a') (map_add (sInvLocalHom S ιs v) _ _)).trans
    (add_add_add_comm _ _ _ _)

theorem galUnits_ρ_algebraMap (v : S)
    (σ : Gal(AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) /
      (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
    (a : ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ) :
    (galUnits.{0, 0} _ _).ρ σ (Additive.ofMul (Units.map (algebraMap ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))).toMonoidHom a)) =
      Additive.ofMul (Units.map (algebraMap ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))).toMonoidHom a) :=
  congrArg Additive.ofMul (Units.ext (σ.commutes _))

theorem dataLocalUnit_compat (t : sInvariantSubgroup (F := K.1) ℚ̄ S)
    (a : ∀ v : S, Additive ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ) (v : S)
    (σ : Gal(AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) /
      (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :
    (gsUnitsLocalMor.{0} S ιs v).hom ((sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom
        (cochainOf _ (sInvCochain S t) ![(gsFinFamily S ιs v).toMonoidHom σ])) =
      (galUnits.{0, 0} _ _).ρ σ (dataLocalUnit S ιs t v (a v)) - dataLocalUnit S ιs t v (a v) :=
  ((congrArg (gsUnitsLocalMor.{0} S ιs v).hom (sUnitsToUnits_sInvRatio S t _)).trans
    (hom_res_sub _ (gsUnitsLocalMor.{0} S ιs v) σ _)).trans
    (ρ_add_sub_of_invariant _ σ (M := (gsUnitsLocalMor.{0} S ιs v).hom
      (Additive.ofMul (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ))) (galUnits_ρ_algebraMap S v σ (Additive.toMul (a v)))).symm

abbrev GsUnitsDatum :=
  Additive (sInvariantSubgroup (F := K.1) ℚ̄ S) × (∀ v : S, Additive ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ)

theorem sInvCochain_one : sInvCochain S (1 : sInvariantSubgroup (F := K.1) ℚ̄ S) = 0 :=
  cochainOf_injective (funext fun σ => Additive.toMul.injective (Subtype.ext (by
    change galUnitsHom K.1 _ (σ 0) 1 * (1 : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)⁻¹ = 1
    rw [map_one, inv_one, mul_one])))

def sInvCochainHom : Additive (sInvariantSubgroup (F := K.1) ℚ̄ S) →+ (cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).X 1 where
  toFun t := sInvCochain S (Additive.toMul t)
  map_zero' := sInvCochain_one S
  map_add' _ _ := sInvCochain_mul S _ _

def dataLocalHom :
    GsUnitsDatum S →+ (∀ v : S, galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) :=
  AddMonoidHom.pi fun v => (localUnitsAlgHom S v).comp ((Pi.evalAddMonoidHom _ v).comp (AddMonoidHom.snd _ _)) +
    (sInvLocalHom S ιs v).comp (AddMonoidHom.fst _ _)

theorem dataLocalHom_apply (d : GsUnitsDatum S) (v : S) :
    dataLocalHom S ιs d v = dataLocalUnit S ιs (Additive.toMul d.1) v (d.2 v) :=
  rfl

def gsUnitsData : GsUnitsDatum S →+ gsUnitsCompact S ιs 1 :=
  dataHom (gsFinFamily S ιs) (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S))
    (fun v : S => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsUnitsLocalMor.{0} S ιs)
    ((sInvCochainHom S).comp (AddMonoidHom.fst _ _)) (dataLocalHom S ιs)
    (fun _ => d_sInvCochain S _) (fun d v σ => dataLocalUnit_compat S ιs (Additive.toMul d.1) d.2 v σ)

theorem gsUnitsData_eq (d : GsUnitsDatum S) :
    gsUnitsData S ιs d = ((compactCochains (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S)
      (fun v : S => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
      (fun v => (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) ≫
        gsUnitsLocalMor.{0} S ιs v)).homologyπ 1).hom
      (dataCycle (gsFinFamily S ιs) (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S))
        (fun v : S => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
          (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsUnitsLocalMor.{0} S ιs)
        (sInvCochain S (Additive.toMul d.1)) (fun v => dataLocalUnit S ιs (Additive.toMul d.1) v (d.2 v))
        (d_sInvCochain S _) (fun v σ => dataLocalUnit_compat S ιs (Additive.toMul d.1) d.2 v σ)) :=
  rfl

theorem gsUnitsData_zero_local (a : ∀ v : S, Additive ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ) :
    gsUnitsData S ιs (0, a) =
      (localToCompact (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S)
        (fun v : S => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
          (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsSUnitsLocalMor S ιs) 0).hom
        (fun v => (H0Iso _).inv.hom (unitsToInvariants _ _ (a v))) :=
  dataHom_eq_localToCompact _ _ _ _ _ _ _ _ ((0 : Additive (sInvariantSubgroup (F := K.1) ℚ̄ S)), a)
    (map_zero (sInvCochainHom S))
    (fun v => localUnitsAlgHom S v (a v))
    (funext fun v => (congrArg (localUnitsAlgHom S v (a v) + ·) (map_zero (sInvLocalHom S ιs v))).trans (add_zero _))
    (fun v σ => galUnits_ρ_algebraMap S v σ (Additive.toMul (a v)))

end Concrete

end

end GroundTheory.ProfCoh

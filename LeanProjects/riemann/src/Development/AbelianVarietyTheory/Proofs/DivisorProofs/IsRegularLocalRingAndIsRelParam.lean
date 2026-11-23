import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAndIsDomainOfIsComplAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingOfFlatOfMapComapMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentIndepOfIsComplAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFibreRegularLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNormalFlatOfSmoothOverRegularLocal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSurjectiveOfIsCplAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

set_option backward.isDefEq.respectTransparency false in

theorem Taut.isRegularLocalRing_and_isRelParam : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → ∀ C : Taut (zetaAway n) g n φ, IsRegularLocalRing C.R ∧ CharZero C.R ∧ Function.Injective C.b ∧ C.b.Flat ∧ IsRelParam C.b C.t ∧ IsRegularLocalRing (C.R ⧸ ((maximalIdeal C.R).comap C.b).map C.b) := by
  intro g n φ _ C
  haveI : IsNoetherianRing C.W := C.noeth
  haveI : IsLocalHom C.iw := C.ψ_loc
  set X := (LowChart.powA C.F C.T.r).left with hX
  set π := LowChart.toO C.F C.T.r with hπ
  set y := C.u (closedPoint C.W) with hy
  let φ₀ : X.presheaf.stalk y →+* C.W := (Scheme.stalkClosedPointTo C.u).hom
  let σ := (π.stalkMap y).hom
  let L := Localization.AtPrime (π y).asIdeal
  let e := Spec.stalkIso (CommRingCat.of (cycAway n)) (π y)
  let ρ : cycAway n →+* X.presheaf.stalk y := σ.comp (e.inv.hom.comp (algebraMap (cycAway n) L))
  have h3 : (Sp (cycAway n)).fromSpecStalk (π y) = Spec.map e.inv ≫ spMap (algebraMap (cycAway n) L) := by
    refine (Spec.fromSpecStalk_eq (CommRingCat.of _) (π y)).trans ?_
    rw [spMap, ← Spec.map_comp]
    exact congrArg Spec.map (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of _) (x := π y)).symm
  have hb : C.T.b = φ₀.comp ρ := by
    have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk C.u
    have h2 := Scheme.SpecMap_stalkMap_fromSpecStalk π (x := y)
    have key : spMap C.T.b = spMap (φ₀.comp ρ) := by
      rw [← C.u_base, ← h1, Category.assoc, ← h2, h3]
      simp only [spMap, ρ, φ₀, σ, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  have hq : (π y).asIdeal = (maximalIdeal C.W).comap C.T.b := by
    have : π y = spMap C.T.b (closedPoint C.W) := by
      rw [hy, ← C.u_base, Scheme.Hom.comp_apply]
    rw [this]; rfl
  haveI : IsRegularLocalRing (X.presheaf.stalk y) := LowChart.isRegularLocalRing_stalk C.F y
  have het := C.u_et
  haveI hW : IsRegularLocalRing C.W := by
    letI : Algebra (X.presheaf.stalk y) C.W := φ₀.toAlgebra
    haveI : Module.Flat (X.presheaf.stalk y) C.W := het.1
    exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal _ _ (maximalIdeal _) het.2.1.symm
  obtain ⟨hRreg, hRdom⟩ := isRegularLocalRing_and_isDomain_of_isComplAt C.W (Fin C.m ⊕ Fin C.N) C.R C.ψ C.compl C.ψ_loc
  have hρspec : spMap ρ = X.fromSpecStalk y ≫ π := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk π (x := y), h3]
    simp only [spMap, ρ, σ, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
  have hflatρ : ρ.Flat := by
    haveI := GlobalTheory.SmoothStalkNormal.flat_fromSpecStalk' X y
    have h : Flat (spMap ρ) := by rw [hρspec]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).1 h
  have hiwflat : C.iw.Flat :=
    (show (algebraMap C.W (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W)).Flat from
      RingHom.flat_algebraMap_iff.mpr inferInstance).comp C.compl.2.2.1
  have hbeq : C.b = C.iw.comp (φ₀.comp ρ) := by rw [← hb]; rfl
  have hbflat : C.b.Flat := by rw [hbeq]; exact (hflatρ.comp het.1).comp hiwflat
  have hinj : Function.Injective C.b := GlobalTheory.SmoothStalkNormal.injective_of_flat_of_isDomain C.b hbflat
  have hmW : (maximalIdeal C.R).comap C.iw = maximalIdeal C.W := IsLocalRing.maximalIdeal_comap C.iw
  have h𝔮 : (maximalIdeal C.R).comap C.b = (π y).asIdeal := by
    rw [hq, show C.b = C.iw.comp C.T.b from rfl, ← Ideal.comap_comap, hmW]
  have hle : ((maximalIdeal C.R).comap C.b).map C.b ≤ (maximalIdeal C.W).map (C.ψ.comp MvPolynomial.C) := by
    rw [show C.b = C.iw.comp C.T.b from rfl, ← Ideal.map_map]
    refine Ideal.map_mono (Ideal.map_le_iff_le_comap.2 ?_)
    rw [← Ideal.comap_comap, hmW]
  refine ⟨hRreg, charZero_of_injective_ringHom hinj, hinj, hbflat, ⟨fun k => C.bd k, fun c hc k =>
    cotangent_indep_of_isComplAt C.W _ C.R C.ψ C.compl C.ψ_loc C.m ⟨Sum.inl, Sum.inl_injective⟩ (fun k => C.bd k) c
      (sup_le_sup_left hle (maximalIdeal C.R ^ 2) hc) k⟩, ?_⟩
  have hfib := GlobalTheory.FibreRegular.isRegularLocalRing_stalk_quot_maximalIdeal (Sp (cycAway n)) X π y
  set I := (maximalIdeal ((Sp (cycAway n)).presheaf.stalk (π y))).map σ with hIdef
  have hI : I = (π y).asIdeal.map ρ := by
    have hsurj : Function.Surjective e.inv.hom := e.commRingCatIsoToRingEquiv.symm.surjective
    have hmL : maximalIdeal ((Sp (cycAway n)).presheaf.stalk (π y)) = (maximalIdeal L).map e.inv.hom :=
      (IsLocalRing.map_maximalIdeal_of_surjective _ hsurj).symm
    rw [hIdef, hmL, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map]
    rfl
  set 𝔭 := I.map φ₀ with h𝔭def
  have h𝔭 : 𝔭.map C.iw = ((maximalIdeal C.R).comap C.b).map C.b := by
    rw [h𝔭def, hI, Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, ← hbeq, h𝔮]
  have hIm : I ≤ maximalIdeal (X.presheaf.stalk y) :=
    Ideal.map_le_iff_le_comap.2 (IsLocalRing.maximalIdeal_comap σ).ge
  have h𝔭m : 𝔭 ≤ maximalIdeal C.W := het.2.1 ▸ Ideal.map_mono hIm
  have h𝔭ne : 𝔭 ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top h𝔭m
  haveI : Nontrivial (C.W ⧸ 𝔭) := Ideal.Quotient.nontrivial_iff.2 h𝔭ne
  haveI : IsLocalRing (C.W ⧸ 𝔭) := IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔭) Ideal.Quotient.mk_surjective
  have hreg𝔭 : IsRegularLocalRing (C.W ⧸ 𝔭) := by
    let χ : (X.presheaf.stalk y ⧸ I) →+* (C.W ⧸ 𝔭) := Ideal.quotientMap 𝔭 φ₀ Ideal.le_comap_map
    have hχflat : χ.Flat := GlobalTheory.Pat.flat_quotientMap_map φ₀ het.1 I
    letI : Algebra (X.presheaf.stalk y ⧸ I) (C.W ⧸ 𝔭) := χ.toAlgebra
    haveI : Module.Flat (X.presheaf.stalk y ⧸ I) (C.W ⧸ 𝔭) := hχflat
    have hcomm : (Ideal.Quotient.mk 𝔭).comp φ₀ = χ.comp (Ideal.Quotient.mk I) := by
      ext a; simp [χ]
    have hmax : maximalIdeal (C.W ⧸ 𝔭) = (maximalIdeal (X.presheaf.stalk y ⧸ I)).map (algebraMap _ _) := by
      rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk 𝔭) Ideal.Quotient.mk_surjective, ← het.2.1,
        ← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, Ideal.map_map,
        Ideal.map_map, hcomm]
      rfl
    exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal _ _ _ hmax
  have hfin := isRegularLocalRing_quotient_of_isComplAt C.W _ C.R C.ψ C.compl C.ψ_loc 𝔭 h𝔭ne hreg𝔭
  rwa [show C.ψ.comp MvPolynomial.C = C.iw from rfl, h𝔭] at hfin

end GlobalTheory.TChart

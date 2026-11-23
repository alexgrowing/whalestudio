import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralClosureFiniteLocalCompleteMixedChar
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsNoetherianRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.GtBaseChange

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open IsLocalRing Polynomial
open scoped CategoryTheory.Obj
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.DatAtAll

section Algebra

variable {C : Type} [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [CharZero C]
  {O : Type} [CommRing O] [IsLocalRing O] [Algebra O C] (hO : (NormedField.valuation (K := C)).Integers O)
include hO

theorem exists_complete_domain (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A →+* O)
    [IsLocalHom f] :
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (φ : A →+* S) (g : S →+* O), IsNoetherianRing S ∧
      IsAdicComplete (maximalIdeal S) S ∧ Function.Injective g ∧ IsLocalHom g ∧ g.comp φ = f := by
  obtain ⟨g, hg, -⟩ := NormIntegers.existsUnique_extend_of_fg hO (maximalIdeal A).fg_of_isNoetherianRing f
  have hgl := isLocalHom_of_comp_algebraMap_adicCompletion f g hg
  have hN : IsNoetherianRing (AdicCompletion (maximalIdeal A) A) := by
    refine AdicNoeth.isNoetherianRing_of_isAdicComplete _ (maximalIdeal _) ?_ inferInstance
      (inferInstanceAs (IsNoetherianRing (ResidueField _)))
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact (maximalIdeal A).fg_of_isNoetherianRing.map _
  have : Nontrivial (AdicCompletion (maximalIdeal A) A ⧸ RingHom.ker g) :=
    Ideal.Quotient.nontrivial_iff.2 (RingHom.ker_ne_top g)
  have hl : IsLocalRing (AdicCompletion (maximalIdeal A) A ⧸ RingHom.ker g) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  refine ⟨_, _, hl, (Ideal.Quotient.mk (RingHom.ker g)).comp (algebraMap A _), RingHom.kerLift g, inferInstance,
    CompleteFiniteExtension.isAdicComplete_of_finite_local (AdicCompletion (maximalIdeal A) A) _,
    RingHom.kerLift_injective g, ⟨fun a ha => ?_⟩, ?_⟩
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact (hgl.map_nonunit a ha).map _
  · rw [← hg]
    rfl

theorem exists_complete_normal {p : ℕ} (hp : p.Prime) (hpO : (p : O) ∈ maximalIdeal O) (B : Type) [CommRing B]
    [IsNoetherianRing B] (f : B →+* O) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (_ : CharZero R) (φ : B →+* R) (g : R →+* O),
      IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (maximalIdeal R) R ∧ IsLocalHom g ∧ g.comp φ = f := by
  have := NormIntegers.isDomain hO
  have : CharZero O := RingHom.charZero (algebraMap O C)
  let n : Ideal B := (maximalIdeal O).comap f
  let A := Localization.AtPrime n
  have hu : ∀ y : n.primeCompl, IsUnit (f y) := fun y => by
    by_contra h
    exact y.2 h
  let f₁ : A →+* O := IsLocalization.lift hu
  have hf₁ : f₁.comp (algebraMap B A) = f := IsLocalization.lift_comp hu
  have : IsLocalHom f₁ := by
    refine ((IsLocalRing.local_hom_TFAE f₁).out 0 2).2 ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hf₁]
    exact Ideal.map_comap_le
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing n.primeCompl A inferInstance
  obtain ⟨S, _, _, φ, g, hN, hc, hg, hgl, hgφ⟩ := exists_complete_domain hO A f₁
  have : IsDomain S := hg.isDomain
  have : CharZero S := RingHom.charZero g
  have hpS : (p : S) ∈ maximalIdeal S := fun h => hpO (by simpa using h.map g)
  obtain ⟨hfin, hl, hNR, hcR⟩ := normalisation_finite_local_complete_of_mixedChar S p hp hpS hN hc
  have hinj : Function.Injective ((algebraMap O C).comp g) := hO.hom_inj.comp hg
  let e : FractionRing S →+* C := IsFractionRing.lift hinj
  have he : e.comp (algebraMap S _) = (algebraMap O C).comp g :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a
  have hint : ∀ x : integralClosure S (FractionRing S), ∃ y : O, algebraMap O C y = e x := fun x =>
    hO.exists_of_le_one (hO.mem_of_integral (IsIntegral.map_of_comp_eq g e he.symm x.2))
  let r : integralClosure S (FractionRing S) →+* (algebraMap O C).range :=
    (e.comp (integralClosure S (FractionRing S)).val.toRingHom).codRestrict _ hint
  let q : O ≃+* (algebraMap O C).range := RingEquiv.ofBijective (algebraMap O C).rangeRestrict
    ⟨fun a b h => hO.hom_inj (congrArg Subtype.val h), (algebraMap O C).rangeRestrict_surjective⟩
  let g' : integralClosure S (FractionRing S) →+* O := q.symm.toRingHom.comp r
  have hg' : g'.comp (algebraMap S _) = g := RingHom.ext fun a => by
    apply q.injective
    refine (q.apply_symm_apply _).trans (Subtype.ext ?_)
    exact congrArg (fun w => w a) he
  have hz : CharZero (integralClosure S (FractionRing S)) := RingHom.charZero g'
  have hloc : IsLocalHom g' := by
    refine ((IsLocalRing.local_hom_TFAE g').out 0 4).2 ?_
    have : (((maximalIdeal O).comap g').comap (algebraMap S _)).IsMaximal := by
      rw [Ideal.comap_comap, hg', IsLocalRing.maximalIdeal_comap]
      infer_instance
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := S) _ this)
  refine ⟨integralClosure S (FractionRing S), _, inferInstance, hl, hz,
    (algebraMap S _).comp (φ.comp (algebraMap B A)), g', hNR,
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing S), hcR, hloc, ?_⟩
  rw [← RingHom.comp_assoc, hg', ← RingHom.comp_assoc, hgφ, hf₁]

theorem exists_complete_normal_residue [IsAlgClosed C] {p : ℕ} (hp : p.Prime) (hpO : (p : O) ∈ maximalIdeal O) (A : Type)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A →+* O) [IsLocalHom f] (k : Type) [Field k]
    [Algebra (ResidueField A) k] [FiniteDimensional (ResidueField A) k] [Algebra.IsSeparable (ResidueField A) k] :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (_ : CharZero R) (φ : A →+* R) (g : R →+* O)
      (j : k →+* ResidueField R),
      IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (maximalIdeal R) R ∧ IsLocalHom g ∧ g.comp φ = f ∧
        (j.comp (algebraMap (ResidueField A) k)).comp (residue A) = (residue R).comp φ := by
  let pb := Field.powerBasisOfFiniteOfSeparable (ResidueField A) k
  have hm := minpoly.monic pb.isIntegral_gen
  obtain ⟨Q, hQ, hdeg, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic (f := residue A)
    (Polynomial.mem_lifts_of_surjective residue_surjective _) hm
  have hd : ((Q.map f).map (algebraMap O C)).degree ≠ 0 := by
    rw [(hmon.map f).degree_map, hmon.degree_map, hdeg]
    exact (minpoly.degree_pos pb.isIntegral_gen).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
  have hint : IsIntegral O x := ⟨Q.map f, hmon.map f, by rwa [IsRoot, Polynomial.eval_map] at hx⟩
  obtain ⟨y, rfl⟩ := hO.exists_of_le_one (hO.mem_of_integral hint)
  have hy : Q.eval₂ f y = 0 := by
    apply hO.hom_inj
    rw [IsRoot, Polynomial.eval_map, eval₂_at_apply, Polynomial.eval_map] at hx
    rw [hx, map_zero]
  obtain ⟨R, _, _, _, _, φ, g, hN, hI, hc, hg, hgφ⟩ := exists_complete_normal hO hp hpO A[X] (eval₂RingHom f y)
  have hf : g.comp (φ.comp Polynomial.C) = f := by
    rw [← RingHom.comp_assoc, hgφ]
    ext a
    simp
  have : IsLocalHom (g.comp (φ.comp Polynomial.C)) := hf ▸ ‹IsLocalHom f›
  have : IsLocalHom (φ.comp Polynomial.C) := isLocalHom_of_comp _ g
  letI : Algebra (ResidueField A) (ResidueField R) := (ResidueField.map (φ.comp Polynomial.C)).toAlgebra
  have hres : (algebraMap (ResidueField A) (ResidueField R)).comp (residue A) = (residue R).comp (φ.comp Polynomial.C) :=
    RingHom.ext fun a => ResidueField.map_residue _ a
  have hroot : aeval (residue R (φ X)) (minpoly (ResidueField A) pb.gen) = 0 := by
    have h₁ : Q.eval₂ (φ.comp Polynomial.C) (φ X) = φ Q := by
      rw [← hom_eval₂, eval₂_C_X]
    rw [← hQ, aeval_def, eval₂_map, hres, ← hom_eval₂, h₁, residue_eq_zero_iff]
    intro hu
    have h₂ : g (φ Q) = 0 := (congrArg (fun w => w Q) hgφ).trans hy
    exact (hu.map g).ne_zero h₂
  refine ⟨R, _, inferInstance, inferInstance, inferInstance, φ.comp Polynomial.C, g, (pb.lift _ hroot).toRingHom, hN, hI, hc,
    hg, hf, ?_⟩
  rw [← hres]
  exact congrArg (fun w => RingHom.comp w (residue A)) (pb.lift _ hroot).comp_algebraMap

end Algebra

theorem intO_integers (C : Type) [NormedField C] [IsUltrametricDist C] :
    (NormedField.valuation (K := C)).Integers (intO C) where
  hom_inj := Subtype.val_injective
  map_le_one x := by
    rw [NormedField.valuation_apply, ← NNReal.coe_le_coe]
    exact x.2
  exists_of_le_one r hr := by
    rw [NormedField.valuation_apply, ← NNReal.coe_le_coe] at hr
    exact ⟨⟨r, hr⟩, rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem nonempty_datAt_of_isNoetherianRing [IsNoetherianRing O] (Y : Model Xo c β) (hS : Y.SplitFibres) (hU : Y.N3) {p : ℕ}
    (hp : p.Prime) (C : SCF p) (P : PointsOfFlagModel.PtC Y C) : Nonempty (DatAt Y P) := by
  have hO := intO_integers ↥C.S
  have := NormIntegers.isLocalRing hO
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have hpO : (p : intO ↥C.S) ∈ maximalIdeal (intO ↥C.S) := by
    rw [NormIntegers.mem_maximalIdeal_iff hO, map_natCast, C.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  let x : Y.X := P.yt (closedPoint (intO ↥C.S))
  let f : Y.X.presheaf.stalk x →+* intO ↥C.S := (Scheme.stalkClosedPointTo (R := .of (intO ↥C.S)) P.yt).hom
  have hf : spMap f ≫ Y.X.fromSpecStalk x = P.yt := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of (intO ↥C.S)) P.yt
  have : IsLocalHom f := Scheme.isLocalHom_stalkClosedPointTo' (R := intO ↥C.S) P.yt
  obtain ⟨k, _, ak, hfin, hsep, S', hS'⟩ := hS x
  obtain ⟨R, _, _, _, _, φ, g, j, hN, hI, hc, hg, hgφ, hj⟩ :=
    @exists_complete_normal_residue _ _ _ _ _ _ _ _ _ hO _ p hp hpO (Y.X.presheaf.stalk x) _ _ _ f _ k _ ak hfin hsep
  let ι : Sp R ⟶ Y.X := spMap φ ≫ Y.X.fromSpecStalk x
  have fac : spMap g ≫ ι = P.yt := by
    rw [← hf, ← hgφ, spMap_comp, Category.assoc]
  obtain ⟨t, ⟨m⟩⟩ := exists_sab ι Y.t
  have hne : (ι ⁻¹' abLocus Y.t.G).Nonempty := by
    let q : Sp ↥C.S := (⊥ : PrimeSpectrum ↥C.S)
    have e : (spMap (intO ↥C.S).subtype ≫ spMap g) ≫ ι = (P.y ≫ Y.jQ) ≫ pullback.fst _ _ := by
      rw [Category.assoc, fac, P.ext, Category.assoc]
      rfl
    have h : (P.y ≫ Y.jQ) q ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨P.y q, (Scheme.Hom.comp_apply _ _ _).symm⟩
    refine ⟨(spMap (intO ↥C.S).subtype ≫ spMap g) q, ?_⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
    exact h
  obtain ⟨S₁, -, -, -, -, hS₁⟩ := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.gtBaseChange _ _ (spMap j) S' _ hS'
  have hq : spMap j ≫ (Spec.map (CommRingCat.ofHom (algebraMap (Y.X.residueField x) k)) ≫ Y.X.fromSpecResidueField x) =
      spMap (residue R) ≫ ι := by
    have h₁ : spMap j ≫ spMap (algebraMap (Y.X.residueField x) k) ≫ spMap (residue (Y.X.presheaf.stalk x)) =
        spMap (residue R) ≫ spMap φ := by
      rw [← spMap_comp, ← hj, spMap_comp, spMap_comp, Category.assoc]
      rfl
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ Y.X.fromSpecStalk x) h₁)).trans (Category.assoc _ _ _) |>
      Eq.trans (by rw [Category.assoc]; rfl)
  have gp₁ := ((isGrpPullback_pullback _ (spMap j)).comp (isGrpPullback_pullback Y.t.G _)).congr hq rfl
  have gp₂ := (isGrpPullback_pullback t.G (spMap (residue R))).comp m.cart
  obtain ⟨e, he, -⟩ := grpPullback_iso gp₁ gp₂
  obtain ⟨U, hu, ht⟩ := hU R hN hI hc ι t m hne ⟨S₁, isGt_of_iso e hS₁⟩
  exact ⟨{ R := R
           noeth := hN
           normal := hI
           complete := hc
           «ι» := ι
           f := g
           f_loc := fun a ha => (NormIntegers.mem_maximalIdeal_iff hO).1 (map_nonunit g a ha)
           fac := fac
           t := t
           m := m
           U := U
           unitOn := hu
           tors := ht }⟩

theorem nonempty_datAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), (∀ i, (Y i).SplitFibres ∧ (Y i).N3) → ∀ (i : Idx H p) (C : Formalism.MainNotions.DIV.Cons.SCF p) (P : PointsOfFlagModel.PtC (Y i) C), Nonempty (DatAt (Y i) P) := by
  intro E _ _ _ H Dw Xo p W hp hW Y _ h i C P
  have := i.c.fin
  have : NumberField i.c.F := {}
  have : IsDiscreteValuationRing (i.c.V W) := by
    refine (isDiscreteValuationRing_and_finite_residueField_of_numberField (i.c.V W) hp.ne_zero ?_).1
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    rcases hW with h | h
    · exact absurd (by exact_mod_cast h) hp.ne_zero
    · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')
  exact nonempty_datAt_of_isNoetherianRing (Y i) (h i).1 (h i).2 hp C P

end GlobalTheory.DatAtAll

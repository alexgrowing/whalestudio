import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfIsFiniteOverProjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory GlobalTheory.USep GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.UCovSep.GenModel

theorem exists_genModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (x₀ : Xo.XF c) (n : ℕ), n.Prime → Odd n → ∃ g₀ : ℕ, ∀ e : ℕ, ∃ (o₁ Ω : Type) (_ : CommRing o₁) (_ : Field Ω) (_ : Algebra o₁ Ω) (_ : ArithBase o₁ Ω) (ze : o₁ˣ) (uη : Sp Ω ⟶ Xo.XF c) (A₁ : PolAV (Sp Ω)) (_ : Out.Level A₁ (n ^ e) (unitOn (Units.map (algebraMap o₁ Ω).toMonoidHom ze))) (M : RatModel o₁ Ω) (U : C.Z.Opens) (g : M.Z ⟶ U.toScheme), A₁.g = g₀ ∧ IsUnit (n : o₁) ∧ (∀ w, uη w = x₀) ∧ UOver Xo c A₁ (RingHom.id Ω) uη ∧ M.pt ≫ g ≫ U.ι = uη ≫ C.i ∧ GlobalTheory.IsNormalScheme M.Z ∧ IsProjOver M.s ∧ IsFinite g ∧ Set.range (pullback.fst C.z (spMap C.b)) ⊆ (U : Set C.Z) := by
  intro E _ _ _ H Dw _ l Xo c C x₀ n hn ho
  haveI := c.fin
  haveI : NumberField c.F := {}
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim _
  obtain ⟨A, _, φ, j, P, _, hφ, hjs, hjo, hjx⟩ :=
    GlobalTheory.UPoinc.GSetup.exists_chart (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) x₀
  let ev : A →+* P.ResidueField := algebraMap A P.ResidueField
  let y : Sp P.ResidueField ⟶ Xo.XF c := spMap ev ≫ j
  have hy : ∀ w, y w = x₀ := fun w => by
    have hp : spMap ev w = ⟨P, inferInstance⟩ := by
      refine PrimeSpectrum.ext ?_
      show Ideal.comap ev w.asIdeal = P
      rw [Subsingleton.elim w (⊥ : PrimeSpectrum P.ResidueField)]
      exact Ideal.ker_algebraMap_residueField _
    show j (spMap ev w) = x₀
    rw [hp, hjx]
  haveI : CharZero P.ResidueField := (ev.comp φ).charZero_iff (ev.comp φ).injective |>.1 inferInstance
  obtain ⟨A₀, -, hU₀⟩ := GlobalTheory.UPoinc.GSetup.exists_fibre Xo c y
  refine ⟨A₀.g, fun e => ?_⟩
  have hpos : 1 ≤ n ^ e := Nat.one_le_iff_ne_zero.2 (by have := hn.pos; positivity)
  obtain ⟨Ω, _, f, A₁, ψ, ze, hf, hA₁, hze, ⟨lev⟩⟩ := GlobalTheory.UPoinc.GSetup.exists_level_finite P.ResidueField A₀ _ hpos
  haveI : CharZero Ω := f.charZero_iff f.injective |>.1 inferInstance
  have hU₁ : UOver Xo c A₁ (RingHom.id Ω) (spMap f ≫ y) := by
    refine (uOver_baseChange_iff hA₁.2.1 (LBIso.symm hA₁.2.2) (RingHom.id Ω)).2 ?_
    rw [RingHom.id_comp]
    simpa only [RingHom.comp_id] using hU₀.comp f
  letI : Algebra C.o c.F := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded
  have hnF : C.b (n : C.o) ≠ 0 := by rw [map_natCast]; exact Nat.cast_ne_zero.2 hn.ne_zero
  have hno : (n : C.o) ≠ 0 := fun h => hnF (by rw [h, map_zero])
  have hle : Submonoid.powers (n : C.o) ≤ nonZeroDivisors C.o := powers_le_nonZeroDivisors_of_noZeroDivisors hno
  let o' := Localization.Away (n : C.o)
  haveI : IsDomain o' := IsLocalization.isDomain_localization hle
  haveI : IsDedekindDomain o' := IsLocalization.isDedekindDomain C.o hle o'
  let b' : o' →+* c.F := IsLocalization.Away.lift (n : C.o) (IsUnit.mk0 _ hnF)
  have hb' : b'.comp (algebraMap C.o o') = C.b := IsLocalization.Away.lift_comp _ _
  letI : Algebra o' c.F := b'.toAlgebra
  haveI : IsScalarTower C.o o' c.F := IsScalarTower.of_algebraMap_eq' hb'.symm
  haveI : IsFractionRing o' c.F := IsFractionRing.isFractionRing_of_isLocalization _ o' c.F hle
  let β : c.F →+* Ω := f.comp (ev.comp φ)
  obtain ⟨o₁, _, _, κ, ze₁, hded, hκ, hinj, hcomp, hze₁⟩ :=
    GlobalTheory.UPoinc.GSetup.exists_base_root o' c.F Ω β ze _ hpos hze
  have hft : Algebra.FiniteType ℤ o₁ := by
    have h₁ : (algebraMap ℤ C.o).FiniteType := RingHom.finiteType_algebraMap.2 C.ft
    have h₂ : (algebraMap C.o o').FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
    have h₃ := hκ.finiteType.comp (h₂.comp h₁)
    rw [RingHom.ext_int (κ.comp _) (algebraMap ℤ o₁)] at h₃
    exact RingHom.finiteType_algebraMap.1 h₃
  haveI : ArithBase o₁ Ω := ⟨hded, hft, inferInstance, hinj⟩
  have hun : IsUnit (n : o₁) := by
    simpa using (IsLocalization.Away.algebraMap_isUnit (S := o') (n : C.o)).map κ
  rw [← hze₁] at lev
  haveI : IsProper C.z := ThetaDescent.isProper_of_isProjOver C.proj
  haveI := C.iF_open
  haveI : SurjectiveOnStalks (spMap ev) :=
    (SurjectiveOnStalks.Spec_iff (φ := CommRingCat.ofHom ev)).2 (Ideal.surjectiveOnStalks_residueField P)
  let a : Sp o' ⟶ Sp C.o := spMap (algebraMap C.o o')
  haveI : IsOpenImmersion a := IsOpenImmersion.of_isLocalization (n : C.o)
  have hba : spMap b' ≫ a = spMap C.b := by rw [← hb']; exact (Spec.map_comp _ _).symm
  let inc : pullback C.z a ⟶ C.Z := pullback.fst _ _
  let gf : pullback C.z (spMap C.b) ⟶ pullback C.z a := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap b')
    (by rw [Category.assoc, hba, pullback.condition])
  have hgf : gf ≫ inc = pullback.fst _ _ := pullback.lift_fst _ _ _
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  haveI : IsPreimmersion (gf ≫ inc) := hgf ▸ inferInstance
  haveI : IsPreimmersion gf := IsPreimmersion.of_comp gf inc
  have hpz : (spMap f ≫ spMap ev ≫ j ≫ C.iF ≫ gf) ≫ pullback.snd _ _ = spMap ((algebraMap o₁ Ω).comp κ) := by
    simp only [Category.assoc, gf, pullback.lift_snd]
    rw [← Category.assoc C.iF, C.iF_over, ← Category.assoc j, hjs, hcomp]
    simp only [← Spec.map_comp]
    rfl
  have hst : ((spMap f ≫ spMap ev ≫ j ≫ C.iF ≫ gf).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
    rw [Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp (GlobalTheory.UPoinc.GSetup.finite_stalkMap_field f hf _)
      (RingHom.Finite.of_surjective _ (Scheme.Hom.stalkMap_surjective _ _))
  obtain ⟨M, π, hMn, hπ, hMp⟩ := GlobalTheory.Poinc.exists_ratModel_normalization o' o₁ Ω κ hκ _ (pullback.snd C.z a) inferInstance
    inferInstance inferInstance _ hpz hst
  have hMs : M.s ≫ spMap κ = π ≫ pullback.snd C.z a := by
    refine ext_of_isDominant_of_isSeparated (spMap (algebraMap ℤ o')) (specZIsTerminal.hom_ext _ _) M.pt ?_
    rw [← Category.assoc, M.pt_s, ← Category.assoc, hMp, hpz, ← Spec.map_comp]
    rfl
  have hproj : IsProjOver M.s :=
    GlobalTheory.FiniteOverProj.isProjOver_of_isFinite_over o' o₁ κ M.Z (pullback C.z a) (pullback.snd C.z a) π M.s
      (GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap C.o o') C.proj) hπ inferInstance hMs
  refine ⟨o₁, Ω, inferInstance, inferInstance, inferInstance, inferInstance, ze₁, spMap f ≫ y, A₁, lev, M,
    inc.opensRange, π ≫ inc.isoOpensRange.hom, hA₁.1, hun, fun w => hy _, hU₁, ?_,
    GlobalTheory.IsNormalScheme.of_pred hMn, hproj, inferInstance, ?_⟩
  · rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, ← Category.assoc, hMp]
    simp only [y, Category.assoc, hgf]
  · rintro _ ⟨x, rfl⟩
    exact ⟨gf x, by rw [← Scheme.Hom.comp_apply, hgf]⟩

end GlobalTheory.UCovSep.GenModel

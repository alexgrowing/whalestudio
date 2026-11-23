import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerActionSemiAbelianAlongTraitsOverModuliStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLatticeEquivCompletedLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeIntStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharExistsOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionPullbackUniversalUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.GPeriods

theorem exists_completion_unif {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [hA : ArithBase o' Ω]
    {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE)
    (hO : S.Over₀ M U₀) (x : M.Z) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : M.Z.presheaf.stalk x →+* R)
      (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (gm : G.left ⟶ FinalForm.G.left) (D : DegData R (maximalIdeal R))
      (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ IsSemiAbelian G ∧
      IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm ∧ LBIso U.LG.L (FinalForm.L.L.pull gm) ∧
      ∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G) := by
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI : IsIntegrallyClosed (M.Z.presheaf.stalk x) := (hO.normal x).2
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have fg : (maximalIdeal (M.Z.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  haveI hRn : IsNoetherianRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  set R := AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x) with hR
  set φ := algebraMap (M.Z.presheaf.stalk x) R with hφ
  have hcpl : IsAdicComplete (maximalIdeal R) R := by
    rw [hm]
    exact AdicCompletion.isAdicComplete_self _ fg
  have hinj : Function.Injective φ := AdicCompletion.of_injective _ _
  haveI : CharZero R := (RingHom.charZero_iff hinj).1 inferInstance
  set ξ : Sp R ⟶ M.Z := spMap φ ≫ M.Z.fromSpecStalk x with hξ
  have hne : (ξ ⁻¹' abLocus FinalForm.G).Nonempty := by
    let w : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    let p : Sp (M.Z.presheaf.stalk x) := spMap φ w
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap φ ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot φ).1 hinj
    have hgen : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact genericPoint_specializes x
    obtain ⟨q, hq⟩ := hgen
    have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
      show p.asIdeal ≤ q.asIdeal
      rw [hp]
      exact bot_le)
    have hsp : ξ w ⤳ genericPoint M.Z := by
      have := hpq.map (M.Z.fromSpecStalk x).continuous
      rw [hq] at this
      exact this
    refine ⟨w, ?_⟩
    show ξ w ∈ abLocus FinalForm.G
    rw [FinalForm.ab]
    exact le_bot_iff.1 ((S.TT_anti M hsp).trans (ThetaSys.TT_genericPoint S M).le)
  haveI : IsCommMonObj ((Over.pullback ξ).obj FinalForm.G) := Functor.isCommMonObj_obj
  obtain ⟨D, A, U, hL, hP⟩ := FinalForm.unif R hRn hRi hcpl ξ hne
  exact ⟨R, inferInstance, hRd, hloc, φ, (Over.pullback ξ).obj FinalForm.G, inferInstance, inferInstance,
    pullback.fst _ _, D, A, U, ⟨⟨hRn, hRd, hRi, hcpl⟩, inferInstance⟩, isCpl_self _, IsSemiAbelian.pullback ξ FinalForm.G FinalForm.semi,
    isGrpPullback_pullback _ _, hL, hP⟩

end GlobalTheory.UPoinc.GPeriods

theorem GlobalTheory.UPoinc.GPeriods.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ x : Y.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : Y.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (p : Λ → R), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ ∀ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ → jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ r = T.y ≫ C.i → ∃ e : Λ ≃ₗ[𝓞 E] T.P.D.toPre.X, ∀ y, ∃ k : ℕ, (k : ℤ) = T.be (e y) (e y) ∧ Associated (ψ (p y)) (T.ϖ ^ k) := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out r hO hpt x
  obtain ⟨f, hf, hab, hβ⟩ := GlobalTheory.T.integerAction_semiAbelian_along_traits_over_moduli E H Dw l Xo c C X₁ Y U₀ EE out r hO hpt
  obtain ⟨R, _, _, _, j, G, _, _, gm, D, A, U, hB, hC, hS, hG, hL, hP⟩ :=
    GlobalTheory.UPoinc.GPeriods.exists_completion_unif out hO x
  have hm : ∀ a : 𝓞 E, ∃ m : D.toPre.X →+ D.toPre.X, ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ (f a).left ∧
      EndChar U fR m := by
    intro a
    haveI := hf a
    obtain ⟨fR, hfR, e⟩ := GlobalTheory.PullAction.exists_lift_end hG (f a)
    obtain ⟨m, hm⟩ := GlobalTheory.Poinc.Eq8.endChar_exists_of_isMonHom R hB G hS D A U fR hfR
    exact ⟨m, fR, hfR, e, hm⟩
  choose m hm using hm
  have key := fun (T : UTrait Xo c) (ψ : R →+* T.V) (hψ : IsLocalHom ψ) hc =>
    GlobalTheory.T.exists_traitLattice_equiv_completedLocalRing E H Dw l Xo c C X₁ Y U₀ EE out r hO hpt f hf hab hβ x R j hB hC G gm hS hG D A U hL hP m hm T ψ hψ hc
  haveI : CharZero R := hB.2
  have hco : ∀ y : D.toPre.X, ∃ s, PsiCoord D.toPre y s := fun y =>
    ((GlobalTheory.PsiCoordLocal.main R D hB.1.2.2.1 y).1).imp fun _ h => h.1
  choose s hs using hco
  by_cases hex : ∃ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ ∧
      jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ r = T.y ≫ C.i
  · obtain ⟨T₀, ψ₀, hψ₀, hc₀⟩ := hex
    obtain ⟨ρ₀, -, hρ₀⟩ := key T₀ ψ₀ hψ₀ hc₀
    refine ⟨R, inferInstance, inferInstance, inferInstance, j, T₀.P.D.toPre.X, inferInstance, inferInstance,
      fun y => s (ρ₀.symm y) ^ 2, hB, hC, ?_⟩
    intro T ψ hψ hc
    obtain ⟨ρT, hord, heq⟩ := key T ψ hψ hc
    have hsymm : ∀ (a : 𝓞 E) (v : T₀.P.D.toPre.X), ρ₀.symm (H.bar a • v) = m a (ρ₀.symm v) := fun a v => by
      apply ρ₀.injective
      rw [AddEquiv.apply_symm_apply, hρ₀, AddEquiv.apply_symm_apply]
    let e₀ : T₀.P.D.toPre.X ≃+ T.P.D.toPre.X := ρ₀.symm.trans ρT
    have hlin : ∀ (a : 𝓞 E) (v : T₀.P.D.toPre.X), e₀ (a • v) = a • e₀ v := fun a v => by
      obtain ⟨b, rfl⟩ := H.bar.surjective a
      show ρT (ρ₀.symm (H.bar b • v)) = H.bar b • ρT (ρ₀.symm v)
      rw [hsymm, heq]
    refine ⟨{ e₀ with map_smul' := hlin }, fun y => ?_⟩
    obtain ⟨h0, hA⟩ := hord (ρ₀.symm y) (s (ρ₀.symm y)) (hs _)
    refine ⟨(T.be (ρT (ρ₀.symm y)) (ρT (ρ₀.symm y))).toNat, Int.toNat_of_nonneg h0, ?_⟩
    rw [map_pow]
    exact hA
  · refine ⟨R, inferInstance, inferInstance, inferInstance, j, PUnit, inferInstance, inferInstance, fun _ => 0, hB, hC,
      fun T ψ hψ hc => (hex ⟨T, ψ, hψ, hc⟩).elim⟩

end

import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalksOfRingStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section
namespace GlobalTheory.NormalBaseChange
open scoped TensorProduct
open GlobalTheory.FibreChart

theorem exists_rat_hom (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (W : (gen Y).Opens) :
    Nonempty (ℚ →+* Γ(gen Y, W)) := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  exact ⟨((genStr Y).appLE ⊤ W (fun _ _ => trivial)).hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom.comp (algebraMap ℚ c.F))⟩

theorem stalks_of_ring_statement_charZero : (∀ (A C R : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [CommRing C] [Algebra A C] [Algebra.EssFiniteType A C] [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra A R], (∀ (P : Ideal C) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P) ∧ CharZero (Localization.AtPrime P)) → IsCN R → IsEtaleCompletion (algebraMap A R) → ((residue R).comp (algebraMap A R)).FormallyUnramified → ∀ (Q : Ideal (TensorProduct A C R)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) ∧ IsNoetherianRing (Localization.AtPrime Q)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z), Z.j ≫ π = X.j → π ≫ X.s = Z.s → Y.jQ ≫ e.hom = Z.jQ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → ∀ v : ↥(pullback ξ (e.hom ≫ genι Z ≫ π) : Scheme.{0}), IsDomain ((pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk v) ∧ IsIntegrallyClosed ((pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk v) ∧ IsNoetherianRing ((pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk v) := by
  intro HR E _ _ _ H D l Xo c X Z Y π e _ _ _ R _ _ _ ξ hCN hEt hFU
  generalize e.hom ≫ genι Z ≫ π = g
  intro v
  set x : X.X := ξ (IsLocalRing.closedPoint (CommRingCat.of R)) with hx
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have hpre : ξ ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem ξ hxU
  letI : Algebra Γ(X.X, U) R :=
    (ξ.appLE U ⊤ hpre.ge ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra
  have hξ : ξ = Spec.map (CommRingCat.ofHom (algebraMap Γ(X.X, U) R)) ≫ hU.fromSpec := factor X.X R ξ U hU hxU

  have hwU : g (pullback.snd ξ g v) ∈ U := by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    have : pullback.fst ξ g v ∈ ξ ⁻¹ᵁ U := by rw [hpre]; trivial
    exact this
  obtain ⟨W, hW, hwW, hWU'⟩ := exists_isAffineOpen_mem_and_subset (U := g ⁻¹ᵁ U) hwU
  have hWU : W ≤ g ⁻¹ᵁ U := hWU'
  letI : Algebra Γ(X.X, U) Γ(gen Y, W) := (g.appLE U W hWU).hom.toAlgebra
  have hWg : hW.fromSpec ≫ g = Spec.map (CommRingCat.ofHom (algebraMap Γ(X.X, U) Γ(gen Y, W))) ≫ hU.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec g hU hW hWU).symm
  obtain ⟨ι, hι, hvι⟩ := chart X.X (gen Y) U hU W hW R g hWg ξ hξ v hwW

  set A := X.X.presheaf.stalk x with hA
  letI : Algebra Γ(X.X, U) A := (X.X.presheaf.germ U x hxU).hom.toAlgebra
  letI : Algebra A R := (Scheme.stalkClosedPointTo ξ).hom.toAlgebra
  haveI : IsScalarTower Γ(X.X, U) A R := IsScalarTower.of_algebraMap_eq fun a => by
    have key : X.X.presheaf.germ U x hxU ≫ Scheme.stalkClosedPointTo ξ =
        ξ.appLE U ⊤ hpre.ge ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
      rw [Scheme.germ_stalkClosedPointTo]
      simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
    exact (congrArg (fun q => q.hom a) key).symm
  obtain ⟨-, hAft⟩ := GlobalTheory.GModStalk.charZero_essFiniteType_stalk E H D l Xo c X x
  haveI := hAft
  haveI : Algebra.EssFiniteType ℤ Γ(gen Y, W) := eft E H D l Xo c Y W hW
  haveI : Algebra.EssFiniteType Γ(X.X, U) Γ(gen Y, W) := Algebra.EssFiniteType.of_comp ℤ _ _

  let C := A ⊗[Γ(X.X, U)] Γ(gen Y, W)
  haveI : Algebra.EssFiniteType A C := inferInstance
  have hC : ∀ (P : Ideal C) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P) ∧
      CharZero (Localization.AtPrime P) := by
    intro P _
    haveI : IsLocalization.AtPrime A (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
    letI : Algebra Γ(gen Y, W) C := Algebra.TensorProduct.rightAlgebra
    haveI : IsLocalization (Algebra.algebraMapSubmonoid Γ(gen Y, W) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl) C :=
      inferInstance
    obtain ⟨h1, h2⟩ := locnorm (gen Y) (GlobalTheory.GenFibre.gen_normal_reduced_noetherian E H D l Xo c Y).1 W hW (Algebra.algebraMapSubmonoid Γ(gen Y, W) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl) C P
    obtain ⟨φ⟩ := exists_rat_hom E H D l Xo c Y W
    let ψ : ℚ →+* Localization.AtPrime P :=
      (algebraMap C (Localization.AtPrime P)).comp ((algebraMap Γ(gen Y, W) C).comp φ)
    exact ⟨h1, h2, ψ.charZero_iff ψ.injective |>.1 inferInstance⟩
  have HC := HR A C R hC hCN hEt hFU

  let eR : C ⊗[A] R ≃+* R ⊗[Γ(X.X, U)] Γ(gen Y, W) :=
    ((Algebra.TensorProduct.comm A C R).trans
      (Algebra.TensorProduct.cancelBaseChange Γ(X.X, U) A A R Γ(gen Y, W))).toRingEquiv
  let eI : CommRingCat.of (R ⊗[Γ(X.X, U)] Γ(gen Y, W)) ≅ CommRingCat.of (C ⊗[A] R) :=
    eR.symm.toCommRingCatIso
  haveI := hι
  refine stalk_of_chart (C ⊗[A] R) (Spec.map eI.hom ≫ ι) v ?_ HC
  obtain ⟨t, rfl⟩ := hvι
  refine ⟨Spec.map eI.inv t, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Category.assoc, ← Spec.map_comp, eI.hom_inv_id, Spec.map_id, Category.id_comp]

end GlobalTheory.NormalBaseChange

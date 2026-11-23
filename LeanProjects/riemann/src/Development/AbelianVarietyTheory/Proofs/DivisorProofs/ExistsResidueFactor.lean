import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Formalism.LocalToGlobal.ProjectiveLattices.KapTrdegPf
import Formalism.LocalToGlobal.ProjectiveLattices.ExtPtUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteDvrPointLiftingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteDvrResidueTranscendenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsEigenBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameExtensionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationBoundOverDvrStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

namespace GlobalTheory.GenericCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem exists_residue_factor {X : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ X) (ξ : X) (q : Sp k) (h : x q = ξ) :
    ∃ ι : X.residueField ξ →+* k, spMap ι ≫ X.fromSpecResidueField ξ = x := by
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
  have hp : p = ξ := by
    rw [← h, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  subst hp
  exact ⟨φ.hom, rfl⟩

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

attribute [local instance] Over.cartesianMonoidalCategory in
open MonObj in

theorem isCombAtG_map {X : Scheme.{0}} (t : SAB H X) {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {x : Sp S ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {a : Fin m → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) :
    IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (a i)) (spMap (dualMap φ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_alg])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMap φ) ≫ (u i).left = _
    rw [hu i, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul]
  · have h := map_list_prod (Formalism.L2.Pj.preHom (G := t.G) δ) (List.ofFn u)
    rw [List.map_ofFn] at h
    exact congrArg (fun g => g.left) h.symm

attribute [local instance] Over.cartesianMonoidalCategory in

theorem exists_comb {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x (v j)) (a : Fin m → S) :
    ∃ w, IsCombAtG t x v a w ∧ IsTanAtG t x w :=
  ⟨_, (isCombAtG_iff t x (fun j => ovT (hv j)) a _).2 rfl,
    isTanAtG_of _ (combT_tan _ _ (fun j => smT_zero_ovT (hv j)) a)⟩

attribute [local instance] Over.cartesianMonoidalCategory in

theorem comb_unique {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x (v j)) {a : Fin m → S}
    {w w' : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) (h' : IsCombAtG t x v a w') : w = w' :=
  ((isCombAtG_iff t x (fun j => ovT (hv j)) a _).1 h).symm.trans ((isCombAtG_iff t x (fun j => ovT (hv j)) a _).1 h')

theorem exists_frac_map {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (φ : A →+* B)
    (h : Function.Injective φ) : ∃ φF : FractionRing A →+* FractionRing B,
      φF.comp (algebraMap A (FractionRing A)) = (algebraMap B (FractionRing B)).comp φ := by
  have hi : Function.Injective ((algebraMap B (FractionRing B)).comp φ) := (IsFractionRing.injective B _).comp h
  refine ⟨IsFractionRing.lift (K := FractionRing A) hi, RingHom.ext fun r => ?_⟩
  rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_centre (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c β) (hB : PointsOfFlagModel.BaseAt la β) (Z : Comp Xo c) :
    ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la T.V io e) (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c)
      (ξ : Y.X) (ι : Y.X.residueField ξ →+* ResidueField T.V),
      z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt ∧ z ≫ pullback.snd _ _ = spMap io ∧
      (∀ q, z q ∈ (Z : Set (Xo.XF c))) ∧ spMap ι ≫ Y.X.fromSpecResidueField ξ = spMap (residue T.V) ≫ yt ∧
      TrdegGe (Y.X.residueField ξ) Dw.dim ∧
      ∃ s : ℕ → ResidueField T.V, letI := ι.toAlgebra; AlgebraicIndependent (Y.X.residueField ξ) s := by
  obtain ⟨_, _, hfr, hover⟩ := GlobalTheory.T.ramification_bound_over_dvr c.F la O β hB.1 hB.2
  letI : Algebra O c.F := β.toAlgebra
  have : CharZero O := RingHom.charZero β
  have : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have := Y.jQ_open
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  let g : Sp (kap Z) ⟶ Xo.XF c := genSp Z
  have : IsPreimmersion g := by unfold g genSp; infer_instance
  have hg : g ≫ pullback.snd _ _ = spMap (algebraMap c.F (kap Z)) := (Spec.map_preimage _).symm
  have hjs : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
    show (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
  let a : O →+* kap Z := (algebraMap c.F (kap Z)).comp β
  have htr : letI := a.toAlgebra; ((Dw.dim : ℕ) : Cardinal) ≤ Algebra.trdeg O (kap Z) := by
    letI := a.toAlgebra
    have : IsScalarTower O c.F (kap Z) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    rw [← trdeg_add_eq O c.F (A := kap Z), kapTrdeg_pf Xo c Z]
    exact le_add_self
  have hga : (g ≫ Y.j) ≫ Y.s = spMap a := by
    rw [Category.assoc, hjs, ← Category.assoc, hg, spMap_comp' β]
  obtain ⟨T₀, yt₀, ψ, b, hb, hs, hgen, hd⟩ := GlobalTheory.T.complete_dvr_point_lifting O Y.X Y.s (kap Z) (g ≫ Y.j) a
    ((algebraMap c.F (kap Z)).injective.comp hB.1) hga Dw.dim htr
  obtain ⟨T, φ, hφ, hinj, s, hs'⟩ := GlobalTheory.T.complete_dvr_residue_transcendence T₀
  obtain ⟨φF, hφF⟩ := exists_frac_map φ hinj
  have hba : (algebraMap T₀.V T₀.Fr).comp b = ψ.comp a := by
    apply spMap_inj
    rw [← spMap_comp' b, ← hs, ← Category.assoc, hgen, Category.assoc, hga, spMap_comp' a]
  obtain ⟨e, he⟩ := hover T ((φF.comp ψ).comp (algebraMap c.F (kap Z))) (φ.comp b) inferInstance (by
    rw [← RingHom.comp_assoc, ← hφF, RingHom.comp_assoc, hba]; rfl)
  obtain ⟨ι₀, hι₀⟩ := exists_residue_factor (spMap (residue T₀.V) ≫ yt₀) (yt₀ (closedPoint T₀.V))
    (closedPoint (ResidueField T₀.V))
    ((Scheme.Hom.comp_apply _ _ _).trans (congrArg yt₀ (comap_closedPoint (residue T₀.V))))
  refine ⟨T, _, e, he, spMap φ ≫ yt₀, spMap (φF.comp ψ) ≫ g, _, (ResidueField.map φ).comp ι₀, ?_, ?_, fun q => ?_, ?_,
    hd, s, ?_⟩
  · rw [← spMap_comp', Category.assoc, Category.assoc, ← hgen, ← Category.assoc, ← Category.assoc, spMap_comp',
      spMap_comp', hφF]
  · rw [Category.assoc, hg, spMap_comp']
  · have h1 : (spMap (φF.comp ψ) ≫ g) q = genPt Z :=
      (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
    rw [h1]
    exact ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ Z.2)).mem
  · rw [← spMap_comp', Category.assoc, hι₀, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp',
      ResidueField.map_comp_residue]
  · letI := ι₀.toAlgebra
    letI := (ResidueField.map φ).toAlgebra
    letI := ((ResidueField.map φ).comp ι₀).toAlgebra
    have : IsScalarTower (Y.X.residueField (yt₀ (closedPoint T₀.V))) (ResidueField T₀.V) (ResidueField T.V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact AlgebraicIndependent.restrictScalars ι₀.injective hs'

end GlobalTheory.GenericCentre

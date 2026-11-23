import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOnDualAndBidual
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieVB

open GlobalTheory.CompanionTheory.Ar.LieTangent

variable {X : Scheme.{0}} {G : Over X} [GrpObj G]

def cast {R : Type} [CommRing R] {x y : Sp R ⟶ X} (h : x = y) {F : Type} [AddCommGroup F] [Module R F]
    (M : LieModel G x F) : LieModel G y F := h ▸ M

theorem cast_left {R : Type} [CommRing R] {x y : Sp R ⟶ X} (h : x = y) {F : Type} [AddCommGroup F]
    [Module R F] (M : LieModel G x F) (e : F) : ((cast h M).pt e).left = (M.pt e).left := by
  subst h
  rfl

theorem exists_tr {A B : Type} [CommRing A] [CommRing B] (a : Sp A ⟶ X) (b : Sp B ⟶ X) (c : A →+* B)
    (h : spMap c ≫ a = b) {E E' : Type} [AddCommGroup E] [AddCommGroup E'] [Module A E] [Module B E']
    (M : LieModel G a E) (M' : LieModel G b E') :
    ∃ j : E →ₛₗ[c] E', ∀ e, (M'.pt (j e)).left = spMap (dualMap c) ≫ (M.pt e).left := by
  subst h
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear X G A B c a E E' M M'
  refine ⟨j, fun e => ?_⟩
  have := hj e
  simpa [LieModel.Lifts] using this

theorem spMap_dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (c : A →+* B) (d : B →+* C) :
    spMap (dualMap d) ≫ spMap (dualMap c) = spMap (dualMap (d.comp c)) := by
  have : dualMap (d.comp c) = (dualMap d).comp (dualMap c) := by
    ext a <;> simp [dualMap]
  simp only [this, spMap, ← Spec.map_comp]
  rfl

theorem pt_left_inj {A : Type} [CommRing A] {a : Sp A ⟶ X} {E : Type} [AddCommGroup E] [Module A E]
    (M : LieModel G a E) {u v : E} (h : (M.pt u).left = (M.pt v).left) : u = v :=
  M.inj (Over.OverMorphism.ext h)

theorem exists_lift {R A : Type} [CommRing R] [CommRing A] [IsLocalRing A] (x : Sp R ⟶ X) [IsOpenImmersion x]
    (z : Sp A ⟶ X) (h : z (IsLocalRing.closedPoint A) ∈ x.opensRange) : ∃ a : R →+* A, spMap a ≫ x = z := by
  have hr : Set.range z ⊆ Set.range x := by
    rintro _ ⟨t, rfl⟩
    have := Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of A) z h
    exact (this.ge (Set.mem_univ t) : t ∈ z ⁻¹ᵁ x.opensRange)
  refine ⟨(Spec.preimage (IsOpenImmersion.lift x z hr)).hom, ?_⟩
  change Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x z hr)).hom) ≫ x = z
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

variable [Smooth G.hom]

theorem basis_tr {R A : Type} [CommRing R] [CommRing A] (ψ : R →+* A) (x : Sp R ⟶ X) (y : Sp A ⟶ X)
    (hψ : spMap ψ ≫ x = y) {F Fy : Type} [AddCommGroup F] [Module R F] [AddCommGroup Fy] [Module A Fy]
    (MR : LieModel G x F) (My : LieModel G y Fy) {n : ℕ} (b : Module.Basis (Fin n) R F) :
    ∃ (β : F →ₛₗ[ψ] Fy) (B : Module.Basis (Fin n) A Fy), (∀ k, B k = β (b k)) ∧
      ∀ e, (My.pt (β e)).left = spMap (dualMap ψ) ≫ (MR.pt e).left := by
  obtain ⟨j, hj⟩ := exists_tr x y ψ hψ MR My
  letI : Algebra R A := ψ.toAlgebra
  letI : Module R Fy := Module.compHom Fy ψ
  haveI : IsScalarTower R A Fy :=
    ⟨fun s r e => by
      change (ψ s * r) • e = ψ s • r • e
      rw [mul_smul]⟩
  let j' : F →ₗ[R] Fy :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun r e => j.map_smulₛₗ r e }
  have hbc : IsBaseChange A j' :=
    (GlobalTheory.T.lie_model_finite_base_change X G R x F MR).2.2 A Fy (cast hψ.symm My) j' fun e => by
      rw [cast_left]
      exact hj e
  refine ⟨j, (Algebra.TensorProduct.basis A b).map hbc.equiv, fun k => ?_, hj⟩
  simp only [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, IsBaseChange.equiv_tmul, one_smul]
  rfl

omit [Smooth G.hom] [GrpObj G] in
theorem mem_span_range {A Ω : Type} [CommRing A] [Field Ω] (g : A →+* Ω) {Fq E : Type} [AddCommGroup Fq]
    [Module A Fq] [AddCommGroup E] [Module Ω E] {n : ℕ} (B : Module.Basis (Fin n) A Fq) (j : Fq →ₛₗ[g] E)
    (y : Fq) : j y ∈ Submodule.span g.range (Set.range fun k => j (B k)) := by
  rw [← B.sum_repr y, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [j.map_smulₛₗ]
  exact Submodule.smul_mem _ (⟨g (B.repr y k), _, rfl⟩ : g.range) (Submodule.subset_span ⟨k, rfl⟩)

variable [IsCommMonObj G]

theorem frame_of_basis {R : Type} [CommRing R] (x : Sp R ⟶ X) {F : Type} [AddCommGroup F] [Module R F]
    (MR : LieModel G x F) {n : ℕ} (b : Module.Basis (Fin n) R F) {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X)
    {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (φ : R →+* Ω) (hφ : spMap φ ≫ x = ξ) :
    ∃ c : Fin n → E, LinearIndependent Ω c ∧ Submodule.span Ω (Set.range c) = ⊤ ∧
      ∀ (q : Cpt ξ) (ψ : R →+* X.presheaf.stalk q.1), spMap ψ ≫ x = X.fromSpecStalk q.1 →
        (genMap ξ q).comp ψ = φ → M.lat.IsFrameAt c q := by
  obtain ⟨j, B, hB, hj⟩ := basis_tr φ x ξ hφ MR M b
  have hc : (fun k => j (b k)) = B := funext fun k => (hB k).symm
  refine ⟨fun k => j (b k), ?_, ?_, fun q ψ hψ hg => ?_⟩
  · rw [hc]; exact B.linearIndependent
  · rw [hc]; exact B.span_eq
  refine ⟨by rw [hc]; exact B.linearIndependent, ?_⟩
  obtain ⟨Fq, _, _, ⟨Mq⟩⟩ := lieModel_exists X G (X.presheaf.stalk q.1) (X.fromSpecStalk q.1)
  obtain ⟨β, Bq, hBq, hβ⟩ := basis_tr (A := X.presheaf.stalk q.1) ψ x (X.fromSpecStalk q.1) hψ MR Mq b
  obtain ⟨jq, hjq⟩ := exists_tr (A := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ξ (genMap ξ q)
    (spec_genMap ξ q) Mq M
  have hcomp : ∀ e, jq (β e) = j e := fun e => pt_left_inj M (by
    rw [hjq, hβ, ← Category.assoc, spMap_dual_comp, hg, hj])
  have hcq : (fun k => j (b k)) = fun k => jq (Bq k) := funext fun k => by rw [hBq, hcomp]
  refine le_antisymm (fun e he => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨v, hv⟩ := (M.mem_lat_iff q e).1 he
    obtain ⟨y, rfl⟩ := Mq.onto v hv.1
    have hy : e = jq y := pt_left_inj M (hv.2.trans (hjq y).symm)
    rw [hy, hcq]
    exact mem_span_range (genMap ξ q) Bq jq y
  · rintro _ ⟨k, rfl⟩
    exact (M.mem_lat_iff q _).2 ⟨Mq.pt (β (b k)), Mq.tan _, by
      change (M.pt (j (b k))).left = _
      rw [← hcomp]
      exact hjq _⟩

theorem exists_chart (G : Over X) [GrpObj G] [Smooth G.hom] [IsCommMonObj G] (y : X) :
    ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (F : Type) (_ : AddCommGroup F)
      (_ : Module R F) (_ : LieModel G x F) (n : ℕ) (_ : Module.Basis (Fin n) R F), y ∈ x.opensRange := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  replace hU : IsAffineOpen U := hU
  let R₀ : Type := Γ(X, U)
  let x₀ : Sp R₀ ⟶ X := hU.fromSpec
  have : IsOpenImmersion x₀ := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  obtain ⟨F₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G R₀ x₀
  obtain ⟨hfin, hproj, hbc⟩ := GlobalTheory.T.lie_model_finite_base_change X G R₀ x₀ F₀ M₀
  let P : PrimeSpectrum R₀ := hU.primeIdealOf ⟨y, hy⟩
  have hP : x₀ P = y := hU.fromSpec_primeIdealOf ⟨y, hy⟩
  haveI : Module.FinitePresentation R₀ F₀ := Module.finitePresentation_of_projective R₀ F₀
  haveI : Module.Free (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl F₀) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    P.asIdeal.primeCompl (LocalizedModule.mkLinearMap P.asIdeal.primeCompl F₀) (Localization.AtPrime P.asIdeal)
  let R : Type := Localization.Away f
  let x : Sp R ⟶ X := spMap (algebraMap R₀ R) ≫ x₀
  have hopen : IsOpenImmersion (spMap (algebraMap R₀ R)) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R₀ (Localization.Away f)))))
  have hx : IsOpenImmersion x := inferInstance
  obtain ⟨F, _, _, ⟨MF⟩⟩ := lieModel_exists X G R x
  obtain ⟨β, hβ⟩ := exists_tr x₀ x (algebraMap R₀ R) rfl M₀ MF
  letI : Module R₀ F := Module.compHom F (algebraMap R₀ R)
  haveI : IsScalarTower R₀ R F :=
    ⟨fun s r e => by
      rw [Algebra.smul_def, mul_smul]
      rfl⟩
  let β' : F₀ →ₗ[R₀] F :=
    { toFun := β
      map_add' := β.map_add
      map_smul' := fun r e => β.map_smulₛₗ r e }
  have hb : IsBaseChange R β' := hbc R F MF β' hβ
  haveI : IsLocalizedModule (Submonoid.powers f) β' :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) R β').2 hb
  have e : LocalizedModule (Submonoid.powers f) F₀ ≃ₗ[R] F :=
    (IsLocalizedModule.linearEquiv (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) F₀) β').extendScalarsOfIsLocalization
      (Submonoid.powers f) R
  haveI : Module.Free R F := Module.Free.of_equiv e
  haveI : Module.Finite R F := (GlobalTheory.T.lie_model_finite_base_change X G R x F MF).1
  have hmem : P ∈ Set.range (spMap (algebraMap R₀ R)) := by
    have := PrimeSpectrum.localization_away_comap_range R f
    have h2 : P ∈ PrimeSpectrum.basicOpen f := hf
    rw [← SetLike.mem_coe, ← this] at h2
    exact h2
  obtain ⟨t, ht⟩ := hmem
  haveI : Nontrivial R := PrimeSpectrum.nontrivial t
  refine ⟨R, inferInstance, x, hx, F, inferInstance, inferInstance, MF, _, Module.finBasis R F, ?_⟩
  refine ⟨t, ?_⟩
  change (spMap (algebraMap R₀ R) ≫ x₀) t = y
  rw [Scheme.Hom.comp_apply, ht, hP]

end GlobalTheory.CompanionTheory.Ar.LieVB

namespace GlobalTheory.CompanionTheory.Ar

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB in

theorem lieLat_isVB_of_smooth : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li), IsCptGen ξ → Smooth G.hom → M.lat.IsVB (Module.finrank Ω Li) ⊤ ∧ M.omLat.IsVB (Module.finrank Ω Li) ⊤ := by
  intro X Ω _ ξ G _ _ Li _ _ M _ hs
  haveI := hs
  have hvb : M.lat.IsVB (Module.finrank Ω Li) ⊤ := by
    intro p _
    obtain ⟨R, _, x, hx, F, _, _, MR, n, b, hp⟩ := exists_chart G p.1
    have hgen : genPt ξ ∈ x.opensRange := p.2.mem_open x.opensRange.isOpen hp
    obtain ⟨φ, hφ⟩ := exists_lift x ξ hgen
    obtain ⟨c, hli, hsp, hfr⟩ := frame_of_basis x MR b ξ M φ hφ
    have hn : n = Module.finrank Ω Li := by
      rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp.ge), Fintype.card_fin]
    subst hn
    refine ⟨x.opensRange, hp, c, hsp, fun q _ hq => ?_⟩
    have hq' : (X.fromSpecStalk q.1) (IsLocalRing.closedPoint (X.presheaf.stalk q.1)) ∈ x.opensRange := by
      rw [Scheme.fromSpecStalk_closedPoint]
      exact hq
    obtain ⟨ψ, hψ⟩ := exists_lift (A := X.presheaf.stalk q.1) x (X.fromSpecStalk q.1) hq'
    refine hfr q ψ hψ ?_
    have h1 : spMap ((genMap ξ q).comp ψ) ≫ x = spMap φ ≫ x := by
      have e1 : spMap ((genMap ξ q).comp ψ) = spMap (genMap ξ q) ≫ spMap ψ := by
        simp only [spMap, ← Spec.map_comp]
        rfl
      calc spMap ((genMap ξ q).comp ψ) ≫ x = spMap (genMap ξ q) ≫ spMap ψ ≫ x := by
            rw [e1, Category.assoc]
        _ = spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 := by rw [hψ]
        _ = ξ := spec_genMap ξ q
        _ = spMap φ ≫ x := hφ.symm
    have h2 := Spec.map_injective ((cancel_mono x).1 h1)
    exact congrArg (fun g => g.hom) h2
  exact ⟨hvb, (Lat.isVBOn_dual_and_bidual X Ω ξ Li M.lat Set.univ _ hvb).1⟩

end GlobalTheory.CompanionTheory.Ar

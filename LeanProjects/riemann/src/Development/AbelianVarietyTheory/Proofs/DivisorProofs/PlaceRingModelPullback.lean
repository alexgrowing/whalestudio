import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraBaseChangeIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraFiniteProjectiveRankStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieBasisOfHolUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImaginaryGeneratorCmType
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimultaneousEigenbasisIntegralStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel.EigenForm

theorem exists_eigenForm (R : Subring ℂ) [IsPrincipalIdealRing R] {g : ℕ} {V : Type} [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin g) R V) (ψ : V →ₗ[R] (Fin g → ℂ)) (hψ : LinearIndependent ℂ fun k ↦ ψ (b k))
    {J : Type} (T : J → V →ₗ[R] V) (lam : J → Fin g → ℂ) (hT : ∀ a v j, ψ (T a v) j = lam a j * ψ v j)
    (hsep : ∀ j k, j ≠ k → ∃ a, lam a j ≠ lam a k)
    (hK : ∀ a j, ∃ x ∈ R, ∃ y ∈ R, y ≠ 0 ∧ lam a j * y = x) (i : Fin g) :
    ∃ (e : V →ₗ[R] R) (c : ℂ), c ≠ 0 ∧ (∀ v, ((e v : R) : ℂ) = c * ψ v i) ∧
      ∀ (e' : V →ₗ[R] R) (c' : ℂ), (∀ v, ((e' v : R) : ℂ) = c' * ψ v i) → ∃ t : R, e' = t • e :=
  GlobalTheory.T.simultaneous_eigenbasis_integral R b ψ hψ T lam hT hsep hK i

open ReciprocityTheory.ChartRestriction.G.Chart (isTan_iff) in

theorem exists_diffEquiv {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) {L : LB X.A.left}
    (u : HolUnif X.A L (Module.finrank ℚ F)) :
    ∃ D : X.Lie ≃ₗ[ℂ] (Fin (Module.finrank ℚ F) → ℂ), ∀ (v : X.Lie) W, u.IsDiff W v.hom ↔ W = D v := by
  obtain ⟨h1, h2⟩ := GlobalTheory.TorusTransfer.tangent_bijective u X.dim
  choose Df hDf using fun v : X.Lie ↦ (h1 v.hom v.isTangent).exists
  have huq : ∀ (v : X.Lie) W, u.IsDiff W v.hom ↔ W = Df v := fun v W ↦
    ⟨fun h ↦ (h1 v.hom v.isTangent).unique h (hDf v), fun h ↦ h ▸ hDf v⟩
  let Dl : X.Lie →ₗ[ℂ] (Fin (Module.finrank ℚ F) → ℂ) :=
    { toFun := Df
      map_add' := fun v w ↦ by
        refine ((huq (v + w) _).1 ?_).symm
        rw [Serre.Lie.hom_add]
        exact GlobalTheory.UnifLieBasis.isDiff_add u ((isTan_iff _).2 v.isTangent) ((isTan_iff _).2 w.isTangent) (hDf v) (hDf w)
      map_smul' := fun c v ↦ by
        have hs : u.IsDiff (c • Df v) (c • v).hom := by
          have := GlobalTheory.UnifLieBasis.isDiff_smul u ((isTan_iff _).2 v.isTangent) (hDf v) c
          convert this using 1
          rfl
        rw [RingHom.id_apply]
        exact ((huq (c • v) _).1 hs).symm }
  have hinj : Function.Injective Dl := by
    intro v w hvw
    have e0 : Dl v = Df v := rfl
    have e1 : u.IsDiff (Df v) w.hom := (huq w (Df v)).2 (hvw.symm.trans rfl).symm
    have e2 : v.hom = w.hom := (h2 (Df v)).unique (y₁ := v.hom) (y₂ := w.hom) ⟨v.isTangent, hDf v⟩ ⟨w.isTangent, e1⟩
    exact Serre.Lie.ext e2
  have hsurj : Function.Surjective Dl := by
    intro W
    obtain ⟨v₀, ⟨ht, hd⟩, -⟩ := h2 W
    refine ⟨Serre.Lie.mk X.rm v₀ ht, ?_⟩
    have hd' : u.IsDiff W (Serre.Lie.mk X.rm v₀ ht).hom := hd
    exact ((huq _ W).1 hd').symm
  exact ⟨LinearEquiv.ofBijective Dl ⟨hinj, hsurj⟩, fun v W ↦ huq v W⟩

theorem isDiff_act {E : Type} [Field E] [NumberField E] {I : Type} {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ} {L : Set E}
    {z : I → ℂ} {X : Obj (FR E) 𝔠 (Sp ℂ)} (U : Unif φ L z X) (a : 𝓞 (FR E)) (v : X.Lie)
    (W : Fin (Module.finrank ℚ (FR E)) → ℂ) (h : U.u.IsDiff W v.hom) :
    U.u.IsDiff (fun j ↦ φ (U.e j) ((a : FR E) : E) * W j) (a • v).hom := by
  haveI := X.rm.hom a
  let Fm : (Fin (Module.finrank ℚ (FR E)) → ℂ) →L[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    ContinuousLinearMap.pi fun j ↦ φ (U.e j) ((a : FR E) : E) • ContinuousLinearMap.proj j
  have hF : ∀ w, Fm w = fun j ↦ φ (U.e j) ((a : FR E) : E) * w j := fun w ↦ by
    ext j; simp [Fm]
  have := GlobalTheory.UnifLieBasis.isDiff_comp U.u (X.rm.act a) Fm (fun w ↦ by rw [hF]; exact U.act a w) v.isTangent h
  rw [hF] at this
  exact this

theorem lieCorr_act {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R']
    {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} (σ : R →+* R') {b : Sp R' ⟶ Sp R} {p : X'.A.left ⟶ X.A.left}
    (hp : X'.IsPullBy X b p) (a : 𝓞 F) {v : X.Lie} {v' : X'.Lie} (h : Obj.LieCorr σ p v v') :
    Obj.LieCorr σ p (a • v) (a • v') := by
  unfold Obj.LieCorr at h ⊢
  change (v'.hom ≫ X'.rm.act a).left ≫ p = _ ≫ (v.hom ≫ X.rm.act a).left
  rw [Over.comp_left, Over.comp_left, Category.assoc, hp.act a, ← Category.assoc, h, Category.assoc]

end GlobalTheory.LatModel.EigenForm

namespace GlobalTheory.LatModel.EigenForm

theorem exists_periodGen : GlobalTheory.Published.AbelianDeRham →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ), IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (L : Set E) (U : Unif φ L 0 X) (p : X.A.left ⟶ X₀.A.left),
      X.IsPullBy X₀ (spMap R.subtype) p → ∀ i : I, ∃ (e : X₀.Lie →ₗ[R] R) (a : ℂ), a ≠ 0 ∧ IsPeriodGen X₀ U p i e a ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e := by
  intro _ E _ _ _ I _ φ hφ l _ lam 𝔠 R hR X₀ X L U p hp i
  classical
  obtain ⟨hdvr, -, -, hKR⟩ := hR
  haveI := hdvr
  obtain ⟨eq, hcorr⟩ := GlobalTheory.T.lie_algebra_base_change_iso (R := R) (R' := ℂ) (X := X₀) (X' := X) (φ := p) hp
  obtain ⟨D, hD⟩ := exists_diffEquiv X U.u
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank X₀
  haveI := hfin
  haveI := hproj
  haveI : Module.Free R X₀.Lie := Module.free_of_flat_of_isLocalRing
  have hdim : Module.finrank R X₀.Lie = Module.finrank ℚ (FR E) := by
    have := hrk (IsLocalRing.closedPoint R)
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  let b : Module.Basis (Fin (Module.finrank ℚ (FR E))) R X₀.Lie :=
    (Module.finBasis R X₀.Lie).reindex (finCongr hdim)
  let ψ : X₀.Lie →ₗ[R] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun v ↦ D (eq (1 ⊗ₜ v))
      map_add' := fun v w ↦ by simp [TensorProduct.tmul_add]
      map_smul' := fun r v ↦ by
        have e1 : (1 : ℂ) ⊗ₜ[R] (r • v) = (r : ℂ) • ((1 : ℂ) ⊗ₜ[R] v) := by
          rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
          rfl
        simp only [e1, map_smul, RingHom.id_apply]
        rfl }
  have hψ : ∀ v, ψ v = D (eq (1 ⊗ₜ v)) := fun v ↦ rfl
  let T : 𝓞 (FR E) → X₀.Lie →ₗ[R] X₀.Lie := fun a ↦
    { toFun := fun v ↦ a • v
      map_add' := smul_add a
      map_smul' := fun r v ↦ smul_comm a r v }
  let lamv : 𝓞 (FR E) → Fin (Module.finrank ℚ (FR E)) → ℂ := fun a j ↦ φ (U.e j) ((a : FR E) : E)
  have hT : ∀ a v j, ψ (T a v) j = lamv a j * ψ v j := by
    intro a v j
    have c0 : Obj.LieCorr R.subtype p v (eq (1 ⊗ₜ v)) := (hcorr v _).2 rfl
    have c1 := lieCorr_act R.subtype hp a c0
    have e1 : a • eq (1 ⊗ₜ v) = eq (1 ⊗ₜ (a • v)) := (hcorr _ _).1 c1
    have d0 : U.u.IsDiff (D (eq (1 ⊗ₜ v))) (eq (1 ⊗ₜ v)).hom := (hD _ _).2 rfl
    have d1 := isDiff_act U a _ _ d0
    have e2 := (hD _ _).1 d1
    change D (eq (1 ⊗ₜ (a • v))) j = _
    rw [← e1, ← e2]
    rfl
  have hsep : ∀ j k, j ≠ k → ∃ a, lamv a j ≠ lamv a k := by
    intro j k hjk
    by_contra hc
    push_neg at hc
    exact hjk (U.e.injective (GlobalTheory.SignGen.cm_restrict_inj E I φ hφ (U.e j) (U.e k) fun a ↦ hc a))
  have hK : ∀ a j, ∃ x ∈ R, ∃ y ∈ R, y ≠ 0 ∧ lamv a j * y = x := fun a j ↦ hKR (φ (U.e j)) _
  have hli : LinearIndependent ℂ fun k ↦ ψ (b k) := by
    convert ((b.baseChange ℂ).map (eq.trans D)).linearIndependent using 1
    ext k : 1
    simp [hψ, Module.Basis.baseChange_apply]
  obtain ⟨e, c, hc, he, huniq⟩ := exists_eigenForm R b ψ hli T lamv hT hsep hK (U.e.symm i)
  refine ⟨e, c, hc, ?_, ?_⟩
  · intro v v' W hvv hW
    rw [(hcorr v v').1 hvv] at hW
    rw [(hD _ W).1 hW, he v]
    rfl
  · intro e' c' h'
    exact huniq e' c' fun v ↦ h' v (eq (1 ⊗ₜ v)) (ψ v) ((hcorr _ _).2 rfl) ((hD _ _).2 rfl)

end GlobalTheory.LatModel.EigenForm

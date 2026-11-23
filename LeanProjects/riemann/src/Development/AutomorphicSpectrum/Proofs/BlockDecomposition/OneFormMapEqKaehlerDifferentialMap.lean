import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmetryHypExtendsSemiAbelianDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.FormBC

theorem subsingleton_of_tensor {R : Type} [CommRing R] {Q : Type} [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    {J : Type} (B : J → Type) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (hcov : ∀ p : PrimeSpectrum R, ∃ (i : J) (q : PrimeSpectrum (B i)), PrimeSpectrum.comap (algebraMap R (B i)) q = p)
    (h : ∀ i, Subsingleton (B i ⊗[R] Q)) : Subsingleton Q := by
  by_contra hQ
  rw [not_subsingleton_iff_nontrivial] at hQ
  obtain ⟨p, hp⟩ := Module.nonempty_support_of_nontrivial (R := R) (M := Q)
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  obtain ⟨i, q, hq⟩ := hcov p
  have := h i
  let κ := q.asIdeal.ResidueField
  have h1 : Subsingleton (κ ⊗[R] Q) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (B i) κ κ Q).symm.subsingleton
  have hpq : p.asIdeal = q.asIdeal.comap (algebraMap R (B i)) := by rw [← hq]; rfl
  letI : Algebra p.asIdeal.ResidueField κ :=
    (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R (B i)) hpq).toAlgebra
  haveI : IsScalarTower R p.asIdeal.ResidueField κ := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R (B i) κ]
    exact (Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal (algebraMap R (B i)) hpq r).symm
  have h2 : Nontrivial (κ ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[R] Q)) :=
    Module.FaithfullyFlat.lTensor_nontrivial _ _ _
  exact not_subsingleton _
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField κ κ Q).subsingleton

theorem bijective_of_lTensor {R : Type} [CommRing R] {N M : Type} [AddCommGroup N] [Module R N] [AddCommGroup M]
    [Module R M] [Module.Finite R N] [Module.Finite R M] [Module.Projective R M] (T : N →ₗ[R] M)
    {J : Type} (B : J → Type) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (hcov : ∀ p : PrimeSpectrum R, ∃ (i : J) (q : PrimeSpectrum (B i)), PrimeSpectrum.comap (algebraMap R (B i)) q = p)
    (h : ∀ i, Function.Bijective (T.lTensor (B i))) : Function.Bijective T := by
  have hs : Function.Surjective T := by
    have hQ : Subsingleton (M ⧸ LinearMap.range T) := subsingleton_of_tensor B hcov fun i ↦ by
      refine ⟨fun a b ↦ ?_⟩
      have key : ∀ x : B i ⊗[R] (M ⧸ LinearMap.range T), x = 0 := fun x ↦ by
        obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (B i) (Submodule.mkQ_surjective (LinearMap.range T)) x
        obtain ⟨z, rfl⟩ := (h i).2 y
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, show (LinearMap.range T).mkQ ∘ₗ T = 0 from
          LinearMap.range_mkQ_comp T, LinearMap.lTensor_zero, LinearMap.zero_apply]
      rw [key a, key b]
    exact fun m ↦ LinearMap.mem_range.1 ((Submodule.Quotient.mk_eq_zero (LinearMap.range T)).1 (Subsingleton.elim (Submodule.Quotient.mk m) 0))
  obtain ⟨u, hu⟩ := Module.projective_lifting_property T LinearMap.id hs
  let r : N →ₗ[R] LinearMap.ker T := LinearMap.codRestrict _ (LinearMap.id - u ∘ₗ T) fun x ↦ by
    have := LinearMap.congr_fun hu (T x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp [this]
  have hr : r ∘ₗ (LinearMap.ker T).subtype = LinearMap.id := by
    ext x
    simp [r]
  have hrs : Function.Surjective r := fun x ↦ ⟨x.1, LinearMap.congr_fun hr x⟩
  haveI : Module.Finite R (LinearMap.ker T) := Module.Finite.of_surjective r hrs
  have hK : Subsingleton (LinearMap.ker T) := subsingleton_of_tensor B hcov fun i ↦ by
    have key : ∀ x : B i ⊗[R] LinearMap.ker T, x = 0 := fun x ↦ by
      have e : (LinearMap.ker T).subtype.lTensor (B i) x = 0 := (h i).1 <| by
        rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
          show T ∘ₗ (LinearMap.ker T).subtype = 0 from LinearMap.ext fun x ↦ x.2, LinearMap.lTensor_zero,
          LinearMap.zero_apply]
      have e2 := congrArg (r.lTensor (B i)) e
      rwa [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hr, LinearMap.lTensor_id, LinearMap.id_apply, map_zero] at e2
    exact ⟨fun a b ↦ by rw [key a, key b]⟩
  exact ⟨(injective_iff_map_eq_zero T).2 fun x hx ↦ congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker T) 0), hs⟩

theorem exists_grp {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {X' : Scheme.{0}} (s' : X' ⟶ Sp R')
    (φ : X' ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))) :
    ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') ∧ SmoothOfRelativeDimension g s' := by
  obtain ⟨C, _, ψ, hψ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A (spMap (algebraMap R R'))
  let e : C ≅ Over.mk s' := Over.isoMk (hψ.1.isoIsPullback _ _ h) (by simp)
  let _ : GrpObj (Over.mk s') := GrpObj.ofIso e
  have : IsMonHom e.hom := inferInstance
  have hC := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hψ
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  exact ⟨inferInstance, GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hC (GlobalTheory.SymExtendDvr.isGrpPullback_of_iso e.symm),
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h hg⟩

theorem lTensor_bijective_of_isBaseChange {S B N M P : Type} [CommRing S] [CommRing B] [Algebra S B]
    [AddCommGroup N] [Module S N] [AddCommGroup M] [Module S M] [AddCommGroup P] [Module S P] [Module B P]
    [IsScalarTower S B P] (T : N →ₗ[S] M) (ev : M →ₗ[S] P) (h₁ : IsBaseChange B ev)
    (h₂ : IsBaseChange B (ev ∘ₗ T)) : Function.Bijective (T.lTensor B) := by
  have e : ∀ x, h₁.equiv (T.lTensor B x) = h₂.equiv x := fun x ↦ by
    induction x with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b n => simp [IsBaseChange.equiv_tmul]
  refine (Function.Bijective.of_comp_iff' h₁.equiv.bijective _).1 ?_
  have e' : (h₁.equiv ∘ T.lTensor B) = h₂.equiv := funext e
  rw [e']
  exact h₂.equiv.bijective

theorem oneFormMap_eq_kaehlerDifferential_map {R R' B B' : Type} [CommRing R] [CommRing R'] [CommRing B] [CommRing B'] [Algebra R R'] [Algebra R B]
    [Algebra R' B'] [Algebra B B'] [Algebra R B'] [IsScalarTower R R' B'] [IsScalarTower R B B']
    (hα : SemiHom (algebraMap R R') (algebraMap B B')) (x : Ω[B⁄R]) :
    hα.m1 x = KaehlerDifferential.map R R' B B' x := by
  induction x using ind1 with
  | h b c =>
    rw [SemiHom.oneFormMap_smul_semilinear, SemiHom.m1_D, map_smul, KaehlerDifferential.map_D, algebraMap_smul]
  | h0 => simp
  | ha x y hx hy => rw [map_add, map_add, hx, hy]

theorem isBaseChange_of_isPushout {R R' B B' W : Type} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    [Algebra R R'] [Algebra R B] [Algebra R' B'] [Algebra B B'] [Algebra R B'] [IsScalarTower R R' B']
    [IsScalarTower R B B'] [Algebra.IsPushout R R' B B'] [AddCommGroup W] [Module R W] (ev : W →ₗ[R] Ω[B⁄R])
    (hev : IsBaseChange B ev) (hα : SemiHom (algebraMap R R') (algebraMap B B'))
    (u : R' ⊗[R] W →ₗ[R'] Ω[B'⁄R']) (hu : ∀ c, u (1 ⊗ₜ c) = hα.m1 (ev c)) : IsBaseChange B' u := by
  have h₁ : IsBaseChange B' (KaehlerDifferential.map R R' B B') :=
    IsBaseChange.of_equiv (KaehlerDifferential.tensorKaehlerEquiv R R' B B') fun x ↦ by
      have hx : x ∈ Submodule.span B (Set.range (KaehlerDifferential.D R B)) :=
        (KaehlerDifferential.span_range_derivation R B).ge Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        simp
      | zero => simp
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
      | smul a x _ hx =>
        rw [TensorProduct.tmul_smul, ← algebraMap_smul B', map_smul, hx, map_smul, algebraMap_smul]
  have h₂ := IsBaseChange.comp hev h₁
  refine IsBaseChange.of_comp (TensorProduct.isBaseChange R W R') ?_
  convert h₂ using 1
  refine LinearMap.ext fun c ↦ ?_
  exact (hu c).trans (oneFormMap_eq_kaehlerDifferential_map hα _)

section Main

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'}
  {φ : X' ⟶ X}

def pairOf (h : IsPullback φ s' s (spMap (algebraMap R R'))) (U : X.affineOpens) : Pair φ :=
  ⟨(⟨φ ⁻¹ᵁ U.1, GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback h U.2⟩, U), le_rfl⟩

theorem isBaseChange_at (h : IsPullback φ s' s (spMap (algebraMap R R'))) (hP : Par (OAff s)) (U : X.affineOpens)
    (u : R' ⊗[R] GlobForm s →ₗ[R'] Ω[Sec s' (φ ⁻¹ᵁ U.1)⁄R'])
    (hu : ∀ c : GlobForm s, u (1 ⊗ₜ c) = (semiHom_secPull h.w (pairOf h U)).m1 (c.1 (op U))) :
    IsBaseChange (Sec s' (φ ⁻¹ᵁ U.1)) u := by
  letI : Algebra (Sec s U.1) (Sec s' (φ ⁻¹ᵁ U.1)) := (CechDR.secPull s s' (pairOf h U)).toAlgebra
  letI : Algebra R (Sec s' (φ ⁻¹ᵁ U.1)) :=
    ((algebraMap R' (Sec s' (φ ⁻¹ᵁ U.1))).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' (Sec s' (φ ⁻¹ᵁ U.1)) := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R (Sec s U.1) (Sec s' (φ ⁻¹ᵁ U.1)) :=
    .of_algebraMap_eq fun r ↦ ((semiHom_secPull h.w (pairOf h U)).map_algebraMap r).symm
  haveI : Algebra.IsPushout R R' (Sec s U.1) (Sec s' (φ ⁻¹ᵁ U.1)) :=
    CommRingCat.isPushout_iff_isPushout.mp (GlobalTheory.AbLaw.isPushout_cst h U.2 rfl)
  exact isBaseChange_of_isPushout (B := Sec s U.1) (B' := Sec s' (φ ⁻¹ᵁ U.1)) (evForm (OAff s) (op U)) (hP (op U))
    (semiHom_secPull h.w (pairOf h U)) u hu

theorem exists_prime (h : IsPullback φ s' s (spMap (algebraMap R R'))) (e : Sp R' ⟶ X') (he : e ≫ s' = 𝟙 _)
    (p : PrimeSpectrum R') : ∃ (U : X.affineOpens) (q : PrimeSpectrum (Sec s' (φ ⁻¹ᵁ U.1))),
      PrimeSpectrum.comap (algebraMap R' (Sec s' (φ ⁻¹ᵁ U.1))) q = p := by
  let y : Sp R' := p
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := φ (e y)) trivial
  have hU' := GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback h hV
  refine ⟨⟨V, hV⟩, hU'.primeIdealOf ⟨e y, hx⟩, ?_⟩
  have e₁ := hU'.fromSpec_primeIdealOf ⟨e y, hx⟩
  have e₂ := affPt_w s' ⟨φ ⁻¹ᵁ V, hU'⟩
  have e₃ := congrArg (fun f ↦ f (hU'.primeIdealOf ⟨e y, hx⟩)) e₂
  have e₄ : s' (e y) = y := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have e₅ : s' (hU'.fromSpec (hU'.primeIdealOf ⟨e y, hx⟩)) =
      spMap (algebraMap R' (Sec s' (φ ⁻¹ᵁ V))) (hU'.primeIdealOf ⟨e y, hx⟩) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans e₃
  exact ((congrArg (fun z ↦ s' z) e₁).symm.trans e₅).symm.trans e₄

end Main

theorem formBC : SteinSt → ParSt → FormBCSt := by
  intro _ hPar R _ A _ g hA hg R' _ _ X' s' φ h
  obtain ⟨_, hA', hg'⟩ := exists_grp A g hA hg s' φ h
  obtain ⟨hP, hV⟩ := hPar R A g hA hg
  obtain ⟨hP', hV'⟩ := hPar R' (Over.mk s') g hA' hg'
  replace hP' : Par (OAff s') := hP'
  replace hV' : VB R' (GlobForm s') g := hV'
  obtain ⟨f₁, f₂, -⟩ := hV'
  obtain ⟨f₃, -, -⟩ := hV
  let _ : Module R (GlobForm s') := Module.compHom _ (algebraMap R R')
  have : IsScalarTower R R' (GlobForm s') := .of_algebraMap_smul fun _ _ ↦ rfl
  let T : R' ⊗[R] GlobForm A.hom →ₗ[R'] GlobForm s' := LinearMap.liftBaseChange R'
    { toFun := pullForm h.w
      map_add' := map_add _
      map_smul' := (pullForm h.w).map_smulₛₗ }
  have hT : ∀ c : GlobForm A.hom, T (1 ⊗ₜ c) = pullForm h.w c := fun c ↦ by simp [T]
  let e : Sp R' ⟶ X' := (η[Over.mk s'] : 𝟙_ (Over (Sp R')) ⟶ Over.mk s').left
  have he : e ≫ s' = 𝟙 _ := Over.w (η[Over.mk s'] : 𝟙_ (Over (Sp R')) ⟶ Over.mk s')
  have hb : Function.Bijective T :=
    bijective_of_lTensor T (fun U : A.left.affineOpens ↦ Sec s' (φ ⁻¹ᵁ U.1)) (exists_prime h e he) fun U ↦ ?_
  · exact ⟨LinearEquiv.ofBijective T hb, fun c ↦ by
      have : LinearEquiv.ofBijective T hb (1 ⊗ₜ c) = pullForm h.w c := hT c
      rw [this]
      exact isPullForm_pullForm h.w c⟩
  · refine lTensor_bijective_of_isBaseChange T (evForm (OAff s') (op ⟨φ ⁻¹ᵁ U.1, GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback h U.2⟩)) (hP' _) ?_
    refine isBaseChange_at h hP U _ fun c ↦ ?_
    have k := isPullForm_iff.1 (isPullForm_pullForm h.w c) (pairOf h U)
    exact (congrArg (fun z : GlobForm s' ↦ z.1 (op (pairOf h U).1.1)) (hT c)).trans k.symm

end GlobalTheory.CompanionTheory.Hodge.FormBC

import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Pull1RestrictPairRestriction
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullbackSecondCohomologyOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveTorsorClassAdditiveStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.SmallLift
open GlobalTheory.CompanionTheory.SysBC

section Ring

variable {R : Type} [CommRing R] {B : Type} [AddCommGroup B] [Module R B]

theorem exists_one_tmul (I : Ideal R) (z : (R ⧸ I) ⊗[R] B) : ∃ b : B, (1 : R ⧸ I) ⊗ₜ[R] b = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul q x =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨r • x, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.smul_def, _root_.mul_one]; rfl
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, TensorProduct.tmul_add _ _ _⟩

theorem one_tmul_eq_zero (I : Ideal R) (x : B) : (1 : R ⧸ I) ⊗ₜ[R] x = 0 ↔ x ∈ I • (⊤ : Submodule R B) := by
  rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk I x, LinearEquiv.map_eq_zero_iff,
    Submodule.Quotient.mk_eq_zero]

theorem mem_span_smul_top (t : R) (x : B) : x ∈ Ideal.span {t} • (⊤ : Submodule R B) ↔ ∃ y : B, x = t • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨y, _, h⟩ ↦ ⟨y, h.symm⟩, fun ⟨y, h⟩ ↦ ⟨y, trivial, h.symm⟩⟩

theorem smul_eq_zero_of_mem [IsLocalRing R] {t : R} (ht : ∀ x, ¬ IsUnit x → x * t = 0) {x : B}
    (h : x ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R B)) : t • x = 0 := by
  induction h using Submodule.smul_induction_on' with
  | smul r hr n hn => rw [smul_smul, _root_.mul_comm, ht r hr, zero_smul]
  | add x _ y _ hx hy => rw [smul_add, hx, hy, add_zero]

theorem mem_of_smul_eq_zero [IsLocalRing R] [Module.Flat R B] {t : R} (h0 : t ≠ 0) {x : B} (h : t • x = 0) :
    x ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R B) := by
  have h2 : ∑ i : Unit, (fun _ ↦ t) i • (fun _ ↦ x) i = 0 := by simpa using h
  obtain ⟨κ, a, y, hx, hj⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero h2
  rw [show x = _ from hx ()]
  refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem_smul ?_ trivial
  intro hu
  have h3 : t * a () j = 0 := by simpa using hj j
  exact h0 (hu.mul_left_eq_zero.1 h3)

end Ring

theorem exA_of_bc {R : Type} [CommRing R] (t : R) {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
    {F₀ : C ⥤ CommAlgCat.{0} (R ⧸ Ideal.span {t})} (a : BC F F₀) : ExA a t := by
  have key : ∀ T (x : F.obj T), a.α T x = 0 ↔ ∃ y : F.obj T, x = t • y := by
    intro T x
    obtain ⟨e, he⟩ := a.bij T
    rw [← he, LinearEquiv.map_eq_zero_iff, one_tmul_eq_zero]
    exact mem_span_smul_top t x
  refine ⟨fun T y ↦ ?_, fun T x h ↦ (key T x).1 h, fun T x ↦ (key T _).2 ⟨x, rfl⟩⟩
  obtain ⟨e, he⟩ := a.bij T
  obtain ⟨b, hb⟩ := exists_one_tmul _ (e.symm y)
  exact ⟨b, by rw [← he, hb, e.apply_symm_apply]⟩

theorem exB_of_bc {R : Type} [CommRing R] [IsLocalRing R] {t : R} (ht : ∀ x, ¬ IsUnit x → x * t = 0) (h0 : t ≠ 0)
    {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R} {Fk : C ⥤ CommAlgCat.{0} (IsLocalRing.ResidueField R)}
    (b : BC F Fk) (hf : ∀ T, Module.Flat R (F.obj T)) : ExB b t := by
  have key : ∀ T (x : F.obj T), b.α T x = 0 ↔ x ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R (F.obj T)) := by
    intro T x
    obtain ⟨e, he⟩ := b.bij T
    rw [← he, LinearEquiv.map_eq_zero_iff]
    exact one_tmul_eq_zero (IsLocalRing.maximalIdeal R) x
  refine ⟨fun T y ↦ ?_, fun T x h ↦ ?_, fun T x h ↦ ?_⟩
  · obtain ⟨e, he⟩ := b.bij T
    obtain ⟨c, hc⟩ := exists_one_tmul (IsLocalRing.maximalIdeal R) (e.symm y)
    refine ⟨c, ?_⟩
    rw [← he]
    exact (congrArg e hc).trans (e.apply_symm_apply y)
  · exact smul_eq_zero_of_mem ht ((key T x).1 h)
  · have := hf T
    exact (key T x).2 (mem_of_smul_eq_zero h0 h)

theorem flat_sec {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [Flat s] {U : X.Opens}
    (hU : IsAffineOpen U) : Module.Flat R (Sec s U) := by
  have h := HasRingHomProperty.appLE (P := @Flat) s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h2 : RingHom.Flat (algebraMap R (Sec s U)) := by
    have : algebraMap R (Sec s U) = (s.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := rfl
    rw [this]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)) h
  exact h2

section Group

open GlobalTheory.FieldModel

theorem isSeparated_scheme {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (h : IsSeparated s) :
    X.IsSeparated := by
  have : IsSeparated (s ≫ Limits.terminal.from (Sp R)) := inferInstance
  exact ⟨by rwa [Subsingleton.elim (Limits.terminal.from X) (s ≫ Limits.terminal.from (Sp R))]⟩

theorem exists_grp {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A]
    {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ A.left} (h : IsPullback φ s' A.hom (spMap σ)) :
    ∃ _ : GrpObj (Over.mk s'), IsGrpPullback (Over.mk s') A (spMap σ) φ := by
  have h' : IsPullback (show (Over.mk s').left ⟶ A.left from φ) (Over.mk s').hom A.hom (spMap σ) := h
  letI := GlobalTheory.grpObjOfIsPullback (G' := Over.mk s') (G := A) (f := spMap σ) (φ := φ) h'
  refine ⟨inferInstance, h, fun T x y x₀ y₀ hx hy ↦ ?_⟩
  have e₁ : x₀ = GlobalTheory.pullbackPointEquiv (G' := Over.mk s') (G := A) (f := spMap σ) (φ := φ) h' T x := Over.OverMorphism.ext hx
  have e₂ : y₀ = GlobalTheory.pullbackPointEquiv (G' := Over.mk s') (G := A) (f := spMap σ) (φ := φ) h' T y := Over.OverMorphism.ext hy
  rw [e₁, e₂, ← GlobalTheory.pullbackPointEquiv_mul]
  rfl

variable {S S₀ : Scheme.{0}} {c : S ⟶ S₀} {B : Over S} {B₀ : Over S₀} {φ : B.left ⟶ B₀.left}

theorem sq_mul [GrpObj B] [GrpObj B₀] (H : IsGrpPullback B B₀ c φ) :
    sq H.1.w ≫ (fst B₀ B₀ * snd B₀ B₀).left = (fst B B * snd B B).left ≫ φ := by
  let U : Over.mk ((B ⊗ B).hom ≫ c) ⟶ B₀ ⊗ B₀ := Over.homMk (sq H.1.w) (isPullback_sq H.1).w
  have k := H.2 (B ⊗ B) (fst B B) (snd B B) (U ≫ fst B₀ B₀) (U ≫ snd B₀ B₀) (sq_fst H.1.w) (sq_snd H.1.w)
  rw [← MonObj.comp_mul] at k
  exact k

theorem tensor_prop (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {S : Scheme.{0}} (B : Over S) (h : P B.hom) : P (B ⊗ B).hom := by
  have k : IsPullback (fst B B).left (snd B B).left B.hom B.hom := .of_hasPullback _ _
  rw [← Over.w (snd B B)]
  exact P.comp_mem _ _ (MorphismProperty.of_isPullback k h) h

end Group

theorem flat_osys {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [Flat s] {P : Type} [SemilatticeInf P]
    (S : Sys X P) (T : Pᵒᵖ) : Module.Flat R ((OSys s S).obj T) :=
  flat_sec s (S.u T.unop).2

section Core

open GlobalTheory.FieldModel

variable {R : Type} [CommRing R] [IsLocalRing R] {t : R}

theorem lift_aux (hD : DescentSt) (hL : LowSt) (hAx : AxOSt) (hNP : NoPrimSt)
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    [A.left.IsSeparated] (ht : ∀ x, ¬ IsUnit x → x * t = 0) (h0 : t ≠ 0)
    (A₀ : Over (Sp (R ⧸ Ideal.span {t}))) [GrpObj A₀] (Ak : Over (Sp (IsLocalRing.ResidueField R))) [GrpObj Ak]
    (φ₀ : A₀.left ⟶ A.left) (φk : Ak.left ⟶ A.left)
    (H₀ : IsGrpPullback A₀ A (spMap (algebraMap R (R ⧸ Ideal.span {t}))) φ₀)
    (Hk : IsGrpPullback Ak A (spMap (algebraMap R (IsLocalRing.ResidueField R))) φk)
    (hA₀ : IsAbelianScheme A₀) (hg₀ : SmoothOfRelativeDimension g A₀.hom)
    (hAk : IsAbelianScheme Ak) (hgk : SmoothOfRelativeDimension g Ak.hom) (c' : HO1 A₀.hom) :
    ∃ d, (pullBC H₀.1 (idSys A.left)).coef.pull1 d = (resSys A₀.hom (pullSys H₀.1 (idSys A.left))).pull1 c' := by
  have sepA : IsSeparated A.hom := by have := hA.proper; infer_instance
  have sepA₀ : IsSeparated A₀.hom := by have := hA₀.proper; infer_instance
  have sepAk : IsSeparated Ak.hom := by have := hAk.proper; infer_instance
  have sepY := tensor_prop @IsSeparated A sepA
  have sepY₀ := tensor_prop @IsSeparated A₀ sepA₀
  have sepYk := tensor_prop @IsSeparated Ak sepAk
  haveI : A₀.left.IsSeparated := isSeparated_scheme _ sepA₀
  haveI : Ak.left.IsSeparated := isSeparated_scheme _ sepAk
  haveI : (A ⊗ A).left.IsSeparated := isSeparated_scheme _ sepY
  haveI : (A₀ ⊗ A₀).left.IsSeparated := isSeparated_scheme _ sepY₀
  haveI : (Ak ⊗ Ak).left.IsSeparated := isSeparated_scheme _ sepYk
  haveI smA : Smooth A.hom := hA.smooth
  haveI smY : Smooth (A ⊗ A).hom := tensor_prop @Smooth A smA
  have hY₀ := isPullback_sq H₀.1
  have hYk := isPullback_sq Hk.1

  have haX := exA_of_bc t (pullBC H₀.1 (idSys A.left))
  have hbX := exB_of_bc ht h0 (pullBC Hk.1 (idSys A.left)) (flat_osys A.hom _)
  have haY := exA_of_bc t (pullBC hY₀ (idSys (A ⊗ A).left))
  have hbY := exB_of_bc ht h0 (pullBC hYk (idSys (A ⊗ A).left)) (flat_osys (A ⊗ A).hom _)
  have haP : ∀ f : (A ⊗ A).left ⟶ A.left, ExA (pullBC hY₀ (pairSys f)) t := fun f ↦ exA_of_bc t _
  have hbP : ∀ f : (A ⊗ A).left ⟶ A.left, ExB (pullBC hYk (pairSys f)) t := fun f ↦
    exB_of_bc ht h0 _ (flat_osys (A ⊗ A).hom _)

  obtain ⟨z, Bz⟩ := bd_exists haX hbX ((resSys A₀.hom (pullSys H₀.1 (idSys A.left))).pull1 c')

  have pm := isPullO_pullHO1 (wOver (fst A₀ A₀ * snd A₀ A₀)) c'
  have pp := isPullO_pullHO1 (wOver (fst A₀ A₀)) c'
  have pq := isPullO_pullHO1 (wOver (snd A₀ A₀)) c'
  have prim := GlobalTheory.T.primitive_torsor_class_additive hD hL hAx _ A₀ g hA₀ hg₀ c' _ _ _ pm pp pq
  obtain ⟨yp, Bp⟩ := bd_exists haY hbY ((resSys (A₀ ⊗ A₀).hom (pullSys hY₀ (idSys (A ⊗ A).left))).pull1
    (pullHO1 (wOver (fst A₀ A₀)) c'))
  obtain ⟨yq, Bq⟩ := bd_exists haY hbY ((resSys (A₀ ⊗ A₀).hom (pullSys hY₀ (idSys (A ⊗ A).left))).pull1
    (pullHO1 (wOver (snd A₀ A₀)) c'))
  have Bm : Bd (pullBC hY₀ (idSys (A ⊗ A).left)) (pullBC hYk (idSys (A ⊗ A).left)) t
      ((resSys (A₀ ⊗ A₀).hom (pullSys hY₀ (idSys (A ⊗ A).left))).pull1
        (pullHO1 (wOver (fst A₀ A₀ * snd A₀ A₀)) c')) (yp + yq) := by
    rw [prim, map_add]
    exact Bp.add Bq
  have tp := transfer (wOver (fst A A)) H₀.1 hY₀ (sq_fst H₀.1.w) (wOver (fst A₀ A₀)) Hk.1 hYk (sq_fst Hk.1.w)
    (wOver (fst Ak Ak)) (haP _) (hbP _) pp Bz Bp
  have tq := transfer (wOver (snd A A)) H₀.1 hY₀ (sq_snd H₀.1.w) (wOver (snd A₀ A₀)) Hk.1 hYk (sq_snd Hk.1.w)
    (wOver (snd Ak Ak)) (haP _) (hbP _) pq Bz Bq
  have tm := transfer (wOver (fst A A * snd A A)) H₀.1 hY₀ (sq_mul H₀) (wOver (fst A₀ A₀ * snd A₀ A₀)) Hk.1 hYk
    (sq_mul Hk) (wOver (fst Ak Ak * snd Ak Ak)) (haP _) (hbP _) pm Bz Bm

  obtain ⟨z', hz⟩ := (res_bij hD hL Ak.hom sepAk (pullSys Hk.1 (idSys A.left))).2.2 z
  obtain ⟨yp', hyp⟩ := (res_bij hD hL (Ak ⊗ Ak).hom sepYk (pullSys hYk (idSys (A ⊗ A).left))).2.2 yp
  obtain ⟨yq', hyq⟩ := (res_bij hD hL (Ak ⊗ Ak).hom sepYk (pullSys hYk (idSys (A ⊗ A).left))).2.2 yq
  have Np : IsPullbackH2Structure (wOver (fst Ak Ak)) z' yp' :=
    isPullback_second_cohomology_of_eq hD hL sepYk Hk.1 hYk (sq_fst Hk.1.w) _ (by rw [hz, hyp]; exact tp)
  have Nq : IsPullbackH2Structure (wOver (snd Ak Ak)) z' yq' :=
    isPullback_second_cohomology_of_eq hD hL sepYk Hk.1 hYk (sq_snd Hk.1.w) _ (by rw [hz, hyq]; exact tq)
  have Nm : IsPullbackH2Structure (wOver (fst Ak Ak * snd Ak Ak)) z' (yp' + yq') :=
    isPullback_second_cohomology_of_eq hD hL sepYk Hk.1 hYk (sq_mul Hk) _ (by rw [hz, map_add, hyp, hyq]; exact tm)
  have zero : z' = 0 := hNP _ Ak g hAk hgk (Field.toIsField _) z' _ _ _ Nm Np Nq rfl
  rw [zero, map_zero] at hz
  rw [← hz] at Bz
  exact lift_of_bd haX hbX Bz

theorem lift_core (hD : DescentSt) (hL : LowSt) (hAx : AxOSt) (hNP : NoPrimSt)
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    [A.left.IsSeparated] (ht : ∀ x, ¬ IsUnit x → x * t = 0) (h0 : t ≠ 0)
    {X' : Scheme.{0}} {s' : X' ⟶ Sp (R ⧸ Ideal.span {t})} {φ : X' ⟶ A.left}
    (h : IsPullback φ s' A.hom (spMap (algebraMap R (R ⧸ Ideal.span {t})))) (c' : HO1 s') :
    ∃ d, (pullBC h (idSys A.left)).coef.pull1 d = (resSys s' (pullSys h (idSys A.left))).pull1 c' := by
  have hk : IsPullback (Limits.pullback.fst A.hom (spMap (algebraMap R (IsLocalRing.ResidueField R))))
      (Limits.pullback.snd A.hom (spMap (algebraMap R (IsLocalRing.ResidueField R)))) A.hom
      (spMap (algebraMap R (IsLocalRing.ResidueField R))) := .of_hasPullback _ _
  obtain ⟨gr₀, H₀⟩ := exists_grp _ A h
  obtain ⟨grk, Hk⟩ := exists_grp _ A hk
  obtain ⟨hA₀, hg₀⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ A _ _ g H₀ hA hg
  obtain ⟨hAk, hgk⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ A _ _ g Hk hA hg
  exact lift_aux hD hL hAx hNP A g hA ht h0 (Over.mk s') _ φ _ H₀ Hk hA₀ hg₀ hAk hgk c'

end Core

theorem main : DescentSt → LowSt → SysBCSt → AxOSt → NoPrimSt → SmallLiftSt := by
  intro hD hL _ hAx hNP R _ A _ g hA hg _ t ht X' s' φ h c'
  have hsep : IsSeparated A.hom := by have := hA.proper; infer_instance
  haveI : A.left.IsSeparated := isSeparated_scheme _ hsep
  have hs' : IsSeparated s' := MorphismProperty.of_isPullback (P := @IsSeparated) h hsep
  have key : ∃ d, (pullBC h (idSys A.left)).coef.pull1 d = (resSys s' (pullSys h (idSys A.left))).pull1 c' := by
    by_cases hc : t = 0 ∨ IsUnit t
    · exact lift_of_trivial (exA_of_bc t _) hc _
    · push_neg at hc
      exact lift_core hD hL hAx hNP A g hA hg ht hc.1 h c'
  obtain ⟨d, hd⟩ := key
  obtain ⟨c, rfl⟩ := (res_bij hD hL A.hom hsep (idSys A.left)).1.2 d
  refine ⟨c, ?_⟩
  have inj := (res_bij hD hL s' hs' (pullSys h (idSys A.left))).1.1
  obtain ⟨x, hx⟩ := (pairRes_bijective φ s').1.2 ((pairPull h.w).pull1 c)
  have e' : x = c' := inj (by
    rw [← pull1_restrict_pair_restriction h _ x, hx, pull1_restrict_pair_pullback, hd])
  exact hx.symm.trans (congrArg _ e')

end GlobalTheory.CompanionTheory.SmallLift

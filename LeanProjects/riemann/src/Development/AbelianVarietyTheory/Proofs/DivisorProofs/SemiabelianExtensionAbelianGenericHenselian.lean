import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapDegEqPowMulCard
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueOfIsAdicColimit
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFiniteFlatTorsionOfIsGt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfBijectiveAffinePts

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt GlobalTheory.AdicColimit IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out (thick thickObj thickMap jK)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinitePartTower

section Formal

variable {R : Type} [CommRing R] {I : Ideal R} {G Gt : Over (Sp R)} {H : ∀ e : ℕ, Over (Sp (R ⧸ I ^ (e + 1)))}
  (F : ∀ e, (H e).left ⟶ G.left) (Ft : ∀ e, (H e).left ⟶ Gt.left)

def Agree {T : Over (Sp R)} (x : T ⟶ G) (y : T ⟶ Gt) : Prop :=
  ∀ (e : ℕ) (Y : Scheme.{0}) (k : Y ⟶ T.left) (s : Y ⟶ Sp (R ⧸ I ^ (e + 1))), k ≫ T.hom = s ≫ thick R I e →
    ∃ a : Y ⟶ (H e).left, a ≫ F e = k ≫ x.left ∧ a ≫ Ft e = k ≫ y.left

variable {F Ft}

theorem mono_of_isPullback {e : ℕ} (h : IsPullback (F e) (H e).hom G.hom (thick R I e)) : Mono (F e) :=
  MorphismProperty.of_isPullback (P := .monomorphisms _) h.flip (mono_thick I e)

theorem Agree.symm {T : Over (Sp R)} {x : T ⟶ G} {y : T ⟶ Gt} (h : Agree F Ft x y) : Agree Ft F y x :=
  fun e Y k s w => (h e Y k s w).imp fun _ h => h.symm

theorem Agree.comp {T T' : Over (Sp R)} {x : T ⟶ G} {y : T ⟶ Gt} (h : Agree F Ft x y) (r : T' ⟶ T) :
    Agree F Ft (r ≫ x) (r ≫ y) := fun e Y k s w => by
  obtain ⟨a, h₁, h₂⟩ := h e Y (k ≫ r.left) s (by rw [Category.assoc, Over.w, w])
  exact ⟨a, h₁.trans (Category.assoc _ _ _), h₂.trans (Category.assoc _ _ _)⟩

theorem Agree.unique (hF : ∀ e, IsPullback (F e) (H e).hom G.hom (thick R I e)) {T : Over (Sp R)}
    (hT : IsAdicColimit I T) {x : T ⟶ G} {y y' : T ⟶ Gt} (h : Agree F Ft x y) (h' : Agree F Ft x y') : y = y' := by
  refine Over.OverMorphism.ext (hT.hom_ext fun e => ?_)
  obtain ⟨a, h₁, h₂⟩ := h e _ (thickι I e T) _ pullback.condition
  obtain ⟨a', h₁', h₂'⟩ := h' e _ (thickι I e T) _ pullback.condition
  have := mono_of_isPullback (hF e)
  rw [← h₂, ← h₂', (cancel_mono _).1 (h₁.trans h₁'.symm)]

theorem exists_agree (hF : ∀ e, IsPullback (F e) (H e).hom G.hom (thick R I e))
    (hFt : ∀ e, Ft e ≫ Gt.hom = (H e).hom ≫ thick R I e) (τ : ∀ e, (H e).left ⟶ (H (e + 1)).left)
    (h₁ : ∀ e, τ e ≫ F (e + 1) = F e) (h₂ : ∀ e, τ e ≫ Ft (e + 1) = Ft e) {T : Over (Sp R)}
    (hT : IsAdicColimit I T) (x : T ⟶ G) : ∃ y : T ⟶ Gt, Agree F Ft x y := by
  have hm : ∀ e, Mono (F e) := fun e => mono_of_isPullback (hF e)
  choose a ha ha' using fun e => (hF e).exists_lift (thickι I e T ≫ x.left) (pullback.snd T.hom (thick R I e))
    (by rw [Category.assoc, Over.w]; exact pullback.condition)
  obtain ⟨g, hg, -⟩ := hT Gt.left (fun e => a e ≫ Ft e) fun e => by
    have : thickMap R I e T ≫ a (e + 1) = a e ≫ τ e := by
      rw [← cancel_mono (F (e + 1)), Category.assoc, Category.assoc, ha, h₁, ha, thickMap_ι_assoc]
    rw [← Category.assoc, this, Category.assoc, h₂]
  refine ⟨Over.homMk g (hT.hom_ext fun e => ?_), fun e Y k s w => ⟨pullback.lift k s w ≫ a e, ?_, ?_⟩⟩
  · rw [← Category.assoc, hg, Category.assoc, hFt, ← Category.assoc, ha']
    exact pullback.condition.symm
  · rw [Category.assoc, ha, ← Category.assoc]
    exact congrArg (· ≫ x.left) (pullback.lift_fst _ _ _)
  · rw [Category.assoc, ← hg, ← Category.assoc]
    exact congrArg (· ≫ g) (pullback.lift_fst _ _ _)

variable [GrpObj G] [GrpObj Gt] [∀ e, GrpObj (H e)]

theorem Agree.mul (hF : ∀ e, IsGrpPullback (H e) G (thick R I e) (F e))
    (hFt : ∀ e, IsGrpPullback (H e) Gt (thick R I e) (Ft e)) {T : Over (Sp R)} {x x' : T ⟶ G} {y y' : T ⟶ Gt}
    (h : Agree F Ft x y) (h' : Agree F Ft x' y') : Agree F Ft (x * x') (y * y') := fun e Y k s w => by
  obtain ⟨a, h₁, h₂⟩ := h e Y k s w
  obtain ⟨a', h₁', h₂'⟩ := h' e Y k s w
  have o : ∀ {b : Y ⟶ (H e).left} {z : T ⟶ G}, b ≫ F e = k ≫ z.left → b ≫ (H e).hom = s := fun {b z} hb => by
    rw [← cancel_mono (thick R I e), Category.assoc, ← (hF e).1.w, ← Category.assoc, hb, Category.assoc, Over.w, w]
  let b : Over.mk s ⟶ H e := Over.homMk a (o h₁)
  let b' : Over.mk s ⟶ H e := Over.homMk a' (o h₁')
  let k' : Over.mk ((Over.mk s).hom ≫ thick R I e) ⟶ T := Over.homMk k w
  refine ⟨(b * b').left, ?_, ?_⟩
  · rw [← (hF e).2 _ b b' (k' ≫ x) (k' ≫ x') h₁.symm h₁'.symm, ← MonObj.comp_mul]; rfl
  · rw [← (hFt e).2 _ b b' (k' ≫ y) (k' ≫ y') h₂.symm h₂'.symm, ← MonObj.comp_mul]; rfl

theorem exists_points {ψ : ∀ e : ℕ, (thickObj R I e G).left ⟶ Gt.left} (h : Raynaud.IsFormalIso I G Gt ψ) :
    ∃ J : ∀ T, IsAdicColimit I T → ((T ⟶ Gt) →* (T ⟶ G)), (∀ T hT, Function.Bijective (J T hT)) ∧
      ∀ T hT T' hT' (r : T' ⟶ T) (y : T ⟶ Gt), J T' hT' (r ≫ y) = r ≫ J T hT y := by
  have h' := Raynaud.isFormalIso_refl I G
  choose j hj using fun T (hT : IsAdicColimit I T) (y : T ⟶ Gt) =>
    exists_agree (fun e => (h.1 e).1) (fun e => (h'.1 e).1.w) _ h.2 h'.2 hT y
  refine ⟨fun T hT => MonoidHom.mk' (j T hT) fun y y' => (hj T hT _).unique (fun e => (h.1 e).1) hT
    ((hj T hT y).mul h.1 h'.1 (hj T hT y')), fun T hT => ⟨fun y y' e => ?_, fun x => ?_⟩,
    fun T hT T' hT' r y => (hj T' hT' _).unique (fun e => (h.1 e).1) hT' ((hj T hT y).comp r)⟩
  · have e' : j T hT y = j T hT y' := e
    exact (hj T hT y).symm.unique (fun e => (h'.1 e).1) hT (e' ▸ (hj T hT y').symm)
  · obtain ⟨y, hy⟩ := exists_agree (fun e => (h'.1 e).1) (fun e => (h.1 e).1.w) _ h'.2 h.2 hT x
    exact ⟨y, (hj T hT y).unique (fun e => (h.1 e).1) hT hy.symm⟩

end Formal

theorem isAdicColimit_of_finite {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (N : Over (Sp R)) [IsFinite N.hom] : IsAdicColimit (maximalIdeal R) N := by
  have : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (N.left.isoSpec.inv ≫ N.hom)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hf
  letI : Algebra R Γ(N.left, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(N.left, ⊤) := hf
  have : HenselianLocalRing R := Raynaud.henselianLocalRing_of_isAdicComplete
  have H := isAdicColimit_finite_henselian_of_local isAdicColimit_spec_of_isLocalRing
    isAdicColimit_of_disjoint_cover R (maximalIdeal R) R Γ(N.left, ⊤) (algebraMap R _)
    (GlobalTheory.isAdicComplete_map_of_finite _ _)
  exact IsAdicColimit.of_iso (Over.isoMk N.left.isoSpec.symm hφ.symm) H

theorem isFinite_flat_torsion {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (D : UU.TQ G X) (N : ℕ) (hN : 1 ≤ N) :
    IsFinite (torsion G N).hom ∧ Flat (torsion G N).hom := by
  obtain ⟨h1, h2⟩ := AbTorsionAnyBase.isFinite_and_flat_torsion S D.B D.isAb N hN
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surj
  have := D.q_affine
  have hN' : N ≠ 0 := by omega
  have hf : IsFinite (mulN (splitTorus S X) N).left := Diag.isFinite_mulN S X hN'
  have hl : Flat (mulN (splitTorus S X) N).left := Diag.flat_mulN S X hN'
  have := flat_descendsAlong_fpqc
  have := isAffineHom_descendsAlong_fpqc.{0}
  have a1 : Flat (ExtensionTorsion.torsionHom D.q N).left :=
    ExtensionTorsion.torsionHom_of_mulN @Flat D.i D.q D.isKernel N hl
  have a2 : IsAffineHom (ExtensionTorsion.torsionHom D.q N).left :=
    ExtensionTorsion.torsionHom_of_mulN @IsAffineHom D.i D.q D.isKernel N inferInstance
  have a3 : UniversallyClosed (ExtensionTorsion.torsionHom D.q N).left :=
    ExtensionTorsion.torsionHom_of_mulN @UniversallyClosed D.i D.q D.isKernel N inferInstance
  have a4 : LocallyOfFiniteType (ExtensionTorsion.torsionHom D.q N).left :=
    ExtensionTorsion.torsionHom_of_mulN @LocallyOfFiniteType D.i D.q D.isKernel N inferInstance
  have a5 : IsFinite (ExtensionTorsion.torsionHom D.q N).left :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
      ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩
  rw [← Over.w (ExtensionTorsion.torsionHom D.q N)]
  exact ⟨inferInstance, inferInstance⟩

theorem mono_of_finite {S : Scheme.{0}} {N G : Over S} [IsFinite N.hom] [IsSeparated G.hom] (y : N ⟶ G)
    (h : ∀ (T : Over S) [IsFinite T.hom] (a b : T ⟶ N), a ≫ y = b ≫ y → a = b) : Mono y := by
  have : IsFinite (y.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsFinite y.left := IsFinite.of_comp _ G.hom
  have P := IsPullback.of_hasPullback y y
  have : IsFinite (pullback.fst y y).left := MorphismProperty.of_isPullback (P := @IsFinite)
    (P.map (Over.forget S)).flip ‹IsFinite y.left›
  have : IsFinite (pullback y y).hom := by rw [← Over.w (pullback.fst y y)]; infer_instance
  have e := h _ _ _ P.w
  exact ⟨fun a b w => (P.lift_fst a b w).symm.trans ((congrArg (P.lift a b w ≫ ·) e).trans (P.lift_snd a b w))⟩

theorem nonempty_finTower {p : ℕ} {R : Type} [CommRing R] {Γ : PDivGroup p R} {G Gt : Over (Sp R)} [GrpObj G]
    [GrpObj Gt] [IsSeparated G.hom] (u : Γ.TorsionTower Gt)
    (J : ∀ (T : Over (Sp R)), IsFinite T.hom → ((T ⟶ Gt) →* (T ⟶ G))) (hJ : ∀ T hT, Function.Bijective (J T hT))
    (hn : ∀ T hT T' hT' (r : T' ⟶ T) (y : T ⟶ Gt), J T' hT' (r ≫ y) = r ≫ J T hT y) : Nonempty (FinTower Γ G) := by
  have hf : ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B], IsFinite (SpAlg R B).hom :=
    fun B _ _ _ => (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  have hi : ∀ {B C : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ ψ : B →ₐ[R] C),
      spOver φ = spOver ψ → φ = ψ := fun φ ψ e => AlgHom.coe_ringHom_injective
    (congrArg CommRingCat.Hom.hom (Spec.map_injective (congrArg (fun z => z.left) e)))
  refine ⟨⟨fun n => J _ (hf _) (u.y n), fun n B _ _ φ ψ => ?_, fun n B _ _ φ ψ e => ?_, fun n B _ _ _ z hz => ?_,
    fun n => ?_⟩⟩
  · let l : WithConv (Γ.A n →ₐ[R] Γ.A n ⊗[R] Γ.A n) := .toConv Algebra.TensorProduct.includeLeft
    let r : WithConv (Γ.A n →ₐ[R] Γ.A n ⊗[R] Γ.A n) := .toConv Algebra.TensorProduct.includeRight
    let c : Γ.A n ⊗[R] Γ.A n →ₐ[R] B := Algebra.TensorProduct.lift φ.ofConv ψ.ofConv fun _ _ => .all _ _
    have c₁ : c.comp l.ofConv = φ.ofConv := Algebra.TensorProduct.lift_comp_includeLeft _ _ _
    have c₂ : c.comp r.ofConv = ψ.ofConv := Algebra.TensorProduct.lift_comp_includeRight _ _ fun _ _ => .all _ _
    have c₃ : c.comp (l * r).ofConv = (φ * ψ).ofConv := by rw [AlgHom.comp_convMul_distrib, c₁, c₂]
    rw [← c₃, ← c₁, ← c₂, ← spOver_comp, ← spOver_comp, ← spOver_comp, Category.assoc, Category.assoc,
      Category.assoc, ← MonObj.comp_mul, ← hn _ _ _ (hf (Γ.A n ⊗[R] Γ.A n)) (spOver (l * r).ofConv), u.mul, map_mul,
      hn _ (hf _), hn _ (hf _)]
  · have := hf (Γ.A n)
    have : Mono (u.y n) := ⟨fun a b w => (TorsionTower.isPullback_y p R Γ Gt u n).hom_ext w (toUnit_unique _ _)⟩
    have : Mono (J _ (hf _) (u.y n)) := mono_of_finite _ fun T hT a b w => by
      rw [← hn _ _ _ hT, ← hn _ _ _ hT] at w
      exact (cancel_mono _).1 ((hJ T hT).1 w)
    exact hi _ _ ((cancel_mono _).1 e)
  · obtain ⟨w, rfl⟩ := (hJ _ (hf B)).2 z
    obtain ⟨φ, rfl⟩ := u.surj n B w ((hJ _ (hf B)).1 (by rw [map_pow, hz, map_one]))
    exact ⟨φ, (hn _ _ _ _ _ _).symm⟩
  · rw [← hn _ _ _ (hf _), u.res]

theorem exists_finTower : GlobalTheory.Published.RaynaudExtension → ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [IsAlgClosed (IsLocalRing.ResidueField R)] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ G.left), IsSemiAbelian G → IsAbelianScheme A → IsGrpPullback A G (spMap (algebraMap R K)) φ → ∃ Γ' : PDivGroup p R, Nonempty (FinTower Γ' G) := by
  intro hR p _ R _ _ _ K _ _ _ _ _ G _ A _ φ hG hA hφ
  have hp : IsProper (pullback.snd G.hom (jK R)) := by
    let e := FractionRing.algEquiv R K
    have he : spMap (e.symm : K →+* FractionRing R) ≫ spMap (algebraMap R K) = jK R := by
      rw [← Cris.spMap_comp]
      exact congrArg spMap (RingHom.ext e.symm.commutes)
    have P := (IsPullback.of_hasPullback A.hom (spMap (e.symm : K →+* FractionRing R))).paste_horiz hφ.1
    rw [he] at P
    have := hA.proper
    rw [← P.isoPullback_inv_snd]
    infer_instance
  obtain ⟨Gt, _, ψ, h₁, ⟨X, _, _, _, ⟨D⟩⟩, h₂⟩ := hR.1 R ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
    G hG hp (hG.fibres _ _)
  have := h₁.comm
  have := hG.separated
  obtain ⟨Γ, ⟨u⟩⟩ := SemiAbelianTower.exists_tower p R Gt h₁ (isFinite_flat_torsion Gt D)
  obtain ⟨J, hJ, hn⟩ := exists_points h₂
  exact ⟨Γ, nonempty_finTower u (fun T _ => J T (isAdicColimit_of_finite T)) (fun _ _ => hJ _ _)
    fun _ _ _ _ => hn _ _ _ _⟩

end GlobalTheory.FinitePartTower

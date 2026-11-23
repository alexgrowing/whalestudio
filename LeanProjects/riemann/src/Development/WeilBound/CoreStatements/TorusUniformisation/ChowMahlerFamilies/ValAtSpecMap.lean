import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsDerAt0
import Development.WeilBound.CoreStatements.HodgeTatePoints.ExtTensor
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBcTors
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumberStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorRegular

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.Num.FamEx

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

section Der

variable {R RC C N W : Type} [CommRing R] [IsDomain R] [CommRing RC] [IsDomain RC] [Field C] [Algebra R RC]
  [Algebra RC C] [AddCommGroup N] [Finite N] [AddCommGroup W] [Module RC W] [Module R W] [IsScalarTower R RC W]

theorem exists_der_ext (h1 : Function.Injective (algebraMap R RC)) (h2 : Function.Injective (algebraMap RC C))
    (φ : R →+* C) (hφ : ∀ r, algebraMap RC C (algebraMap R RC r) = φ r)
    {A : Subalgebra R (Multiplicative N → R)} (hA : IsHopfOrder A) (d : A →ₗ[R] W)
    (hd : ∀ a b : A, d (a * b) = a.1 1 • d b + b.1 1 • d a) (M : Submodule RC (N → C))
    (hM : M = Submodule.span RC {f | ∃ g ∈ A, f = fun x => φ (g (Multiplicative.ofAdd x))}) :
    ∃ Dv : M →ₗ[RC] W, IsDerAt0 M Dv ∧
      ∀ (a : A) (f : M), (∀ x, f.1 x = φ (a.1 (Multiplicative.ofAdd x))) → Dv f = d a := by
  classical
  haveI : Fintype N := Fintype.ofFinite N
  obtain ⟨d₀, hd₀, hfull⟩ := hA.full
  haveI : Module.Projective R A := hA.projective
  let lam : A →ₗ[R] (N → RC) :=
    { toFun := fun a x => algebraMap R RC (a.1 (Multiplicative.ofAdd x))
      map_add' := fun a b => by
        funext x
        simp
      map_smul' := fun r a => by
        funext x
        simp [Algebra.smul_def] }
  let Λ : RC ⊗[R] A →ₗ[RC] (N → RC) := LinearMap.liftBaseChange RC lam
  let D : RC ⊗[R] A →ₗ[RC] W := LinearMap.liftBaseChange RC d
  let Φ : RC ⊗[R] A →ₗ[RC] (N → C) :=
    (LinearMap.pi fun x => (Algebra.linearMap RC C) ∘ₗ LinearMap.proj x) ∘ₗ Λ
  have hΦ : ∀ t x, Φ t x = algebraMap RC C (Λ t x) := fun t x => rfl
  have hΛ : ∀ (c : RC) (a : A) (x : N),
      Λ (c ⊗ₜ a) x = c * algebraMap R RC (a.1 (Multiplicative.ofAdd x)) := by
    intro c a x
    simp [Λ, lam, LinearMap.liftBaseChange_tmul]
  have hΛmul : ∀ t t' : RC ⊗[R] A, Λ (t * t') = Λ t * Λ t' := by
    intro t t'
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
      induction t' using TensorProduct.induction_on with
      | zero => simp
      | tmul c' a' =>
        funext x
        rw [Algebra.TensorProduct.tmul_mul_tmul, Pi.mul_apply, hΛ, hΛ, hΛ]
        simp only [Subalgebra.coe_mul, Pi.mul_apply, map_mul]
        ring
      | add u v hu hv => rw [mul_add, map_add, hu, hv, map_add, mul_add]
    | add u v hu hv => rw [add_mul, map_add, hu, hv, map_add, add_mul]
  have hDmul : ∀ t t' : RC ⊗[R] A, D (t * t') = Λ t 0 • D t' + Λ t' 0 • D t := by
    intro t t'
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
      induction t' using TensorProduct.induction_on with
      | zero => simp
      | tmul c' a' =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hΛ, hΛ]
        simp only [D, LinearMap.liftBaseChange_tmul, ofAdd_zero]
        rw [hd, smul_add, ← algebraMap_smul RC (a.1 1) (d a'), ← algebraMap_smul RC (a'.1 1) (d a)]
        module
      | add u v hu hv =>
        rw [mul_add, map_add, hu, hv, map_add, map_add, Pi.add_apply, add_smul, smul_add]
        abel
    | add u v hu hv =>
      rw [add_mul, map_add, hu, hv, map_add, map_add, Pi.add_apply, add_smul, smul_add]
      abel
  have hinjΛ : Function.Injective Λ := by
    let e : N → A := fun x =>
      ⟨d₀ • (fun y => if Multiplicative.toAdd y = x then (1 : R) else 0), hfull _⟩
    let Ψ : (N → RC) →ₗ[RC] RC ⊗[R] A :=
      { toFun := fun g => ∑ x : N, g x ⊗ₜ e x
        map_add' := by
          intro g g'
          simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
        map_smul' := by
          intro c g
          simp [Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul] }
    have hsum : ∀ a : A, ∑ x : N, a.1 (Multiplicative.ofAdd x) • e x = d₀ • a := by
      intro a
      apply Subtype.ext
      funext y
      simp [e, Finset.sum_apply, mul_ite, Finset.sum_ite_eq]
      ring
    have key : ∀ t, Ψ (Λ t) = algebraMap R RC d₀ • t := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul c a =>
        calc Ψ (Λ (c ⊗ₜ a)) = ∑ x : N, (c * algebraMap R RC (a.1 (Multiplicative.ofAdd x))) ⊗ₜ e x := by
              simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, hΛ]
          _ = ∑ x : N, c ⊗ₜ (a.1 (Multiplicative.ofAdd x) • e x) := by
              congr 1
              funext x
              rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]
          _ = c ⊗ₜ (d₀ • a) := by rw [← TensorProduct.tmul_sum, hsum]
          _ = algebraMap R RC d₀ • (c ⊗ₜ a) := by rw [TensorProduct.tmul_smul, algebraMap_smul]
      | add u v hu hv => rw [map_add, map_add, hu, hv, smul_add]
    intro t t' htt'
    have h0 : algebraMap R RC d₀ • (t - t') = 0 := by
      rw [smul_sub, ← key, ← key, htt', sub_self]
    have hne : algebraMap R RC d₀ ≠ 0 := fun h' => hd₀ (h1 (h'.trans (map_zero _).symm))
    exact sub_eq_zero.1 ((Module.IsTorsionFree.isSMulRegular (isRegular_of_ne_zero hne))
      (h0.trans (smul_zero _).symm))
  have hinj : Function.Injective Φ := by
    intro t t' h
    apply hinjΛ
    funext x
    exact h2 (congrFun h x)
  have hΦ1 : ∀ a : A, Φ (1 ⊗ₜ a) = fun x => φ (a.1 (Multiplicative.ofAdd x)) := by
    intro a
    funext x
    rw [hΦ, hΛ, _root_.one_mul, hφ]
  have hMle : M ≤ LinearMap.range Φ := by
    rw [hM, Submodule.span_le]
    rintro f ⟨g, hg, rfl⟩
    exact ⟨1 ⊗ₜ ⟨g, hg⟩, hΦ1 _⟩
  have hE : ∀ f : M, Φ ((LinearEquiv.ofInjective Φ hinj).symm (Submodule.inclusion hMle f)) = f.1 := by
    intro f
    exact congrArg Subtype.val ((LinearEquiv.ofInjective Φ hinj).apply_symm_apply (Submodule.inclusion hMle f))
  have hpre : ∀ (f : M) (t : RC ⊗[R] A), Φ t = f.1 →
      (LinearEquiv.ofInjective Φ hinj).symm (Submodule.inclusion hMle f) = t := by
    intro f t ht
    apply hinj
    rw [hE, ht]
  refine ⟨D ∘ₗ (LinearEquiv.ofInjective Φ hinj).symm.toLinearMap ∘ₗ Submodule.inclusion hMle, ?_, ?_⟩
  · intro f g h a b hfg ha hb
    have haf : Λ ((LinearEquiv.ofInjective Φ hinj).symm (Submodule.inclusion hMle f)) 0 = a :=
      h2 ((congrFun (hE f) 0).trans ha.symm)
    have hbg : Λ ((LinearEquiv.ofInjective Φ hinj).symm (Submodule.inclusion hMle g)) 0 = b :=
      h2 ((congrFun (hE g) 0).trans hb.symm)
    show D ((LinearEquiv.ofInjective Φ hinj).symm (Submodule.inclusion hMle h)) =
      a • D ((LinearEquiv.ofInjective Φ hinj).symm (Submodule.inclusion hMle g)) +
        b • D ((LinearEquiv.ofInjective Φ hinj).symm (Submodule.inclusion hMle f))
    rw [hpre h (((LinearEquiv.ofInjective Φ hinj).symm (Submodule.inclusion hMle f)) *
      ((LinearEquiv.ofInjective Φ hinj).symm (Submodule.inclusion hMle g))) ?_, hDmul, haf, hbg]
    funext x
    rw [hΦ, hΛmul, Pi.mul_apply, map_mul, ← hΦ, ← hΦ, hE, hE, hfg, Pi.mul_apply]
  · intro a f hf
    show D ((LinearEquiv.ofInjective Φ hinj).symm (Submodule.inclusion hMle f)) = d a
    rw [hpre f (1 ⊗ₜ a) (by
      rw [hΦ1]
      funext x
      exact (hf x).symm)]
    simp [D, LinearMap.liftBaseChange_tmul]

end Der

section Cot

variable {R T W : Type} [CommRing R] [CommGroup T] [AddCommGroup W] [Module R W]

def cotMap (A : Subalgebra R (T → R)) : A →ₗ[R] omega A :=
  ((augIdeal A).toCotangent.restrictScalars R) ∘ₗ
    LinearMap.codRestrict ((augIdeal A).restrictScalars R)
      (LinearMap.id - (Algebra.linearMap R A) ∘ₗ (evalAt A 1).toLinearMap)
      (fun a => by
        change (a - algebraMap R A (a.1 1)).1 1 = 0
        simp)

theorem cotMap_apply (A : Subalgebra R (T → R)) (a : A) (f : augIdeal A) (h : f.1 = a - algebraMap R A (a.1 1)) :
    cotMap A a = (augIdeal A).toCotangent f := by
  unfold cotMap
  exact congrArg (augIdeal A).toCotangent (Subtype.ext h.symm)

theorem cotMap_mul (A : Subalgebra R (T → R)) (a b : A) :
    cotMap A (a * b) = a.1 1 • cotMap A b + b.1 1 • cotMap A a := by
  set_option synthInstance.maxHeartbeats 400000 in
  have mem : ∀ c : A, c - algebraMap R A (c.1 1) ∈ augIdeal A := fun c => by
    change (c - algebraMap R A (c.1 1)).1 1 = 0
    simp
  set_option synthInstance.maxHeartbeats 400000 in
  rw [cotMap_apply A (a * b) ⟨_, mem (a * b)⟩ rfl, cotMap_apply A a ⟨_, mem a⟩ rfl,
    cotMap_apply A b ⟨_, mem b⟩ rfl]
  set_option synthInstance.maxHeartbeats 400000 in
  have key : (⟨_, mem (a * b)⟩ : augIdeal A) =
      ((a - algebraMap R A (a.1 1)) • (⟨_, mem b⟩ : augIdeal A) : augIdeal A) +
        (algebraMap R A (a.1 1) • (⟨_, mem b⟩ : augIdeal A) : augIdeal A) +
          (algebraMap R A (b.1 1) • (⟨_, mem a⟩ : augIdeal A) : augIdeal A) := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, Subalgebra.coe_mul, Pi.mul_apply, map_mul]
    ring
  set_option synthInstance.maxHeartbeats 400000 in
  have z : (augIdeal A).toCotangent
      ((a - algebraMap R A (a.1 1)) • (⟨_, mem b⟩ : augIdeal A) : augIdeal A) = 0 := by
    rw [Ideal.toCotangent_eq_zero, Submodule.coe_smul, smul_eq_mul, pow_two]
    exact Ideal.mul_mem_mul (mem a) (mem b)
  set_option synthInstance.maxHeartbeats 400000 in
  rw [key, map_add, map_add, z, zero_add, map_smul, map_smul, algebraMap_smul, algebraMap_smul]

end Cot

theorem valAt_spec_map' {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (ψ : B →+* C)
    (y : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom ψ) ≫ y) ⊤ le_top s = ψ (valAt y ⊤ le_top s) := by
  unfold valAt
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom ψ)) y ⊤ ⊤ ⊤ le_top le_top]
  have e1 : (Spec.map (CommRingCat.ofHom ψ)).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom ψ)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
  rw [e1]
  have e2 := congrArg (fun φ => φ.hom ((y.appLE ⊤ ⊤ le_top).hom s))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))
  exact e2

private theorem valAt_top_lemma {B : Type} [CommRing B] {X : Scheme} (f : Spec (CommRingCat.of B) ⟶ X)
    (h : ⊤ ≤ f ⁻¹ᵁ ⊤) (s : Γ(X, ⊤)) :
    valAt f ⊤ h s = (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (f.appTop.hom s) := by
  unfold valAt
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

private theorem valAt_comp_lemma_2 {B : Type} [CommRing B] {X Y : Scheme} (f : Spec (CommRingCat.of B) ⟶ Y)
    (g : Y ⟶ X) (h : ⊤ ≤ (f ≫ g) ⁻¹ᵁ ⊤) (h' : ⊤ ≤ f ⁻¹ᵁ ⊤) (s : Γ(X, ⊤)) :
    valAt (f ≫ g) ⊤ h s = valAt f ⊤ h' (g.appTop.hom s) := by
  rw [valAt_top_lemma, valAt_top_lemma, Scheme.Hom.comp_appTop]
  rfl

open PositivityTheory.HtPt.Htat in
theorem isHT_res {R : Type} [CommRing R] [IsDomain R] {T₁ T₂ : Type} [CommGroup T₁] [Finite T₁] [CommGroup T₂]
    (Γ₁ : QFGroup R T₁) (Γ₂ : QFGroup R T₂) {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {N₁ N₂ : ℕ} (hN : N₁ ∣ N₂) {i₁ : Γ₁.G.left ⟶ G.left}
    {i₂ : Γ₂.G.left ⟶ G.left} (h₁ : Γ₁.IsTorsionAlong G x N₁ i₁) (h₂ : Γ₂.IsTorsionAlong G x N₂ i₂)
    {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (α : T₁ →* T₂)
    (hα : ∀ t, (Γ₂.pt (α t)).left ≫ i₂ = (Γ₁.pt t).left ≫ i₁) (χ : T₂ →* Rˣ) (w : Module.Dual R L)
    (h : Γ₂.IsHT i₂ M N₂ χ w) : Γ₁.IsHT i₁ M N₁ (χ.comp α) w := by
  obtain ⟨s₂, hs₂, hv₂⟩ := h
  have hpow : ∀ {Y : Over (Spec (CommRingCat.of R))} (g : Over.mk (Y.hom ≫ x) ⟶ G),
      g ^ N₁ = 1 → g ^ N₂ = 1 := by
    intro Y g hg
    obtain ⟨k, hk⟩ := hN
    rw [hk, pow_mul, hg, one_pow]
  obtain ⟨φ, hφ⟩ := (h₂.kernel Γ₁.G (Over.homMk i₁ h₁.isOver)).1
    (hpow _ ((h₁.kernel Γ₁.G (Over.homMk i₁ h₁.isOver)).2 ⟨𝟙 _, by simp⟩))
  have hφ' : φ.left ≫ i₂ = i₁ := hφ
  refine ⟨φ.left.appTop.hom s₂, fun t => ?_, fun e => ?_⟩
  · have ht : Γ₁.pt t ≫ φ = Γ₂.pt (α t) := h₂.inj (BT.genPt R) _ _ (by
      rw [Over.comp_left, Category.assoc, hφ', hα])
    have h3 := hs₂ (α t)
    rw [← ht] at h3
    exact (valAt_comp_lemma_2 (Γ₁.pt t).left φ.left le_top le_top s₂).symm.trans h3
  · obtain ⟨v₂, hv₂a, hv₂b, hv₂c⟩ := hv₂ e
    have hle : Ideal.span {(N₂ : R)} ≤ Ideal.span {(N₁ : R)} :=
      Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hN)
    have hr1 : (dualMap (Ideal.Quotient.mk (Ideal.span {(N₁ : R)}))).comp (algebraMap R (DualNumber R)) =
        (algebraMap (R ⧸ Ideal.span {(N₁ : R)}) (DualNumber (R ⧸ Ideal.span {(N₁ : R)}))).comp
          (Ideal.Quotient.mk (Ideal.span {(N₁ : R)})) :=
      RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
        (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    have hr2 : (dualMap (Ideal.Quotient.mk (Ideal.span {(N₁ : R)}))).comp (epsMul (N₁ : R)) =
        (dualMap (Ideal.Quotient.mk (Ideal.span {(N₁ : R)}))).comp (epsMul 0) :=
      RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap, epsMul])
        (by
          simp [dualMap, epsMul]
          rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(N₁ : R)})) N₁, ← map_mul,
            Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
          exact dvd_mul_right _ _)
    have hr3 : (dualMap (Ideal.Quotient.factor hle)).comp
        ((algebraMap (R ⧸ Ideal.span {(N₂ : R)}) (DualNumber (R ⧸ Ideal.span {(N₂ : R)}))).comp
          (Ideal.Quotient.mk (Ideal.span {(N₂ : R)}))) =
        (algebraMap (R ⧸ Ideal.span {(N₁ : R)}) (DualNumber (R ⧸ Ideal.span {(N₁ : R)}))).comp
          (Ideal.Quotient.mk (Ideal.span {(N₁ : R)})) :=
      RingHom.ext fun a => TrivSqZeroExt.ext
        (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, Ideal.Quotient.factor_mk])
        (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, Ideal.Quotient.factor_mk])
    have hr4 : (dualMap (Ideal.Quotient.factor hle)).comp
        (dualMap (Ideal.Quotient.mk (Ideal.span {(N₂ : R)}))) =
        dualMap (Ideal.Quotient.mk (Ideal.span {(N₁ : R)})) :=
      RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap, Ideal.Quotient.factor_mk])
        (by simp [dualMap, Ideal.Quotient.factor_mk])
    let Y : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom
      ((algebraMap (R ⧸ Ideal.span {(N₁ : R)}) (DualNumber (R ⧸ Ideal.span {(N₁ : R)}))).comp
        (Ideal.Quotient.mk (Ideal.span {(N₁ : R)})))))
    let f : Over.mk (Y.hom ≫ x) ⟶ epsAt x :=
      Over.homMk (Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N₁ : R)})))))
        (by
          show _ ≫ Spec.map _ ≫ x = Spec.map _ ≫ x
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hr1])
    have hpt0 : M.pt 0 = 1 := by
      have h0 := congrArg (· * (M.pt 0)⁻¹) (M.add 0 0)
      simp only [add_zero, mul_inv_cancel, mul_inv_cancel_right] at h0
      exact h0.symm
    have hptn : ∀ n : ℕ, M.pt (n • e) = M.pt e ^ n := by
      intro n
      induction n with
      | zero => rw [zero_smul, hpt0, pow_zero]
      | succ n ih => rw [succ_nsmul, M.add, ih, pow_succ]
    have hfz : f ≫ M.pt ((N₁ : R) • e) = f ≫ M.pt ((0 : R) • e) := by
      apply Over.OverMorphism.ext
      simp only [f, Over.homMk_left, Over.comp_left, M.smul]
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, hr2]
    have hg : (f ≫ M.pt e) ^ N₁ = 1 := by
      rw [← comp_pow, ← hptn, ← Nat.cast_smul_eq_nsmul R, hfz, zero_smul, hpt0, comp_one]
    obtain ⟨y, hy⟩ := (h₁.kernel Y (f ≫ M.pt e)).1 hg
    have hy' : y.left ≫ i₁ =
        Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N₁ : R)})))) ≫ (M.pt e).left := hy
    let z : Y ⟶ Γ₂.G := Over.homMk (Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.factor hle))) ≫ v₂)
      (by
        show _ = Spec.map _
        rw [Category.assoc, hv₂a, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hr3])
    have hyz : y ≫ φ = z := h₂.inj Y _ _ (by
      rw [Over.comp_left, Category.assoc, hφ', hy']
      show _ = (Spec.map _ ≫ v₂) ≫ i₂
      rw [Category.assoc, hv₂b, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hr4])
    refine ⟨y.left, Over.w y, hy', ?_⟩
    refine (valAt_comp_lemma_2 y.left φ.left le_top _ s₂).symm.trans ?_
    have e2 : y.left ≫ φ.left = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.factor hle))) ≫ v₂ :=
      congrArg Over.Hom.left hyz
    rw [e2, valAt_spec_map', hv₂c]
    simp [dualMap, Ideal.Quotient.factor_mk]

theorem char_mem {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T) (χ : T →* Rˣ)
    (s : Γ(Γ.G.left, ⊤)) (hs : Γ.HasValues s fun t => ((χ t : Rˣ) : R)) :
    (fun t => ((χ t : Rˣ) : R)) ∈ Γ.btOrder ⊤ := by
  apply Algebra.subset_adjoin
  intro t g _
  refine ⟨⊤, trivial, Γ.G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((χ t : Rˣ) : R)) * s,
    fun h hh => ?_⟩
  have h1 := (valAt_top_lemma (Γ.pt h).left hh s).symm.trans (hs h)
  refine (valAt_top_lemma (Γ.pt h).left hh _).trans ?_
  rw [map_mul, map_mul, h1]
  have e1 : (Γ.pt h).left.appTop.hom (Γ.G.hom.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((χ t : Rˣ) : R))) =
      ((Γ.pt h).left ≫ Γ.G.hom).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((χ t : Rˣ) : R)) := by
    rw [Scheme.Hom.comp_appTop]
    rfl
  rw [e1, Over.w (Γ.pt h)]
  have n' := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((χ t : Rˣ) : R)))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  have n'' : (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
      ((Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((χ t : Rˣ) : R))) =
      algebraMap R (FractionRing R) ((χ t : Rˣ) : R) := by
    refine n'.trans ?_
    show algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((χ t : Rˣ) : R))) = _
    rw [Iso.inv_hom_id_apply]
  rw [show (BT.genPt R).hom = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) from rfl, n'']
  show _ = algebraMap R (FractionRing R) ((χ (t * h) : Rˣ) : R)
  rw [map_mul, Units.val_mul, map_mul]

def liftSurj {G T H : Type} [Group G] [Group T] [Group H] (π : G →* T) (hπ : Function.Surjective π)
    (f : G →* H) (hf : ∀ z, π z = 1 → f z = 1) : T →* H :=
  π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
    ⟨f, fun z hz => (MonoidHom.mem_ker).2 (hf z ((MonoidHom.mem_ker).1 hz))⟩

theorem liftSurj_apply {G T H : Type} [Group G] [Group T] [Group H] (π : G →* T)
    (hπ : Function.Surjective π) (f : G →* H) (hf : ∀ z, π z = 1 → f z = 1) (z : G) :
    liftSurj π hπ f hf (π z) = f z :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ z

theorem qhom_surj {E : Type} [Field E] [NumberField E] (N n : ℕ) : Function.Surjective (qhom (E := E) N n) := by
  intro y
  refine ⟨Multiplicative.ofAdd (fun i => Classical.choose (Ideal.Quotient.mk_surjective (Multiplicative.toAdd y i))), ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  exact Classical.choose_spec (Ideal.Quotient.mk_surjective (Multiplicative.toAdd y i))

theorem qhom_eq_one {E : Type} [Field E] [NumberField E] (N n : ℕ) (y : Fin N → 𝓞 E) :
    qhom N n (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = n • y' := by
  constructor
  · intro h
    have hi : ∀ i, y i ∈ Ideal.span {(n : 𝓞 E)} := fun i => by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact congrFun (congrArg Multiplicative.toAdd h) i
    choose c hc using fun i => Ideal.mem_span_singleton'.1 (hi i)
    exact ⟨c, funext fun i => by rw [← hc i, Pi.smul_apply, nsmul_eq_mul, mul_comm]⟩
  · rintro ⟨y', rfl⟩
    apply Multiplicative.toAdd.injective
    funext i
    show Ideal.Quotient.mk _ ((n • y') i) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Pi.smul_apply, nsmul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem exists_alpha {E : Type} [Field E] [NumberField E] (N p m : ℕ) (hm : 1 ≤ m) :
    ∃ α : TorsT E N p →* TorsT E N (p ^ m), ∀ x, α (qmk p x) = qmk (p ^ m) (p ^ (m - 1) • x) := by
  refine ⟨liftSurj (qhom N p) (qhom_surj _ _) ((qhom N (p ^ m)).comp
    (AddMonoidHom.toMultiplicative (nsmulAddMonoidHom (p ^ (m - 1))))) fun z hz => ?_, fun x => ?_⟩
  · obtain ⟨z', hz'⟩ := (qhom_eq_one N p (Multiplicative.toAdd z)).1 hz
    refine (qhom_eq_one N (p ^ m) (p ^ (m - 1) • Multiplicative.toAdd z)).2 ⟨z', ?_⟩
    rw [hz', smul_smul, ← pow_succ, Nat.sub_add_cancel hm]
  · exact liftSurj_apply (qhom N p) _ _ _ (Multiplicative.ofAdd x)

theorem pow_val_add {U : Type} [Monoid U] {n : ℕ} [NeZero n] {ζ : U} (hζ : ζ ^ n = 1) (a b : ZMod n) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add]
  conv_rhs => rw [← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) n, pow_add, pow_mul, hζ, one_pow, _root_.mul_one]

theorem pow_val_nsmul {U : Type} [Monoid U] {n : ℕ} [NeZero n] {ζ : U} (hζ : ζ ^ n = 1) (k : ℕ) (a : ZMod n) :
    ζ ^ (k • a).val = (ζ ^ k) ^ a.val := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul, pow_val_add hζ, ih, pow_succ, (Commute.pow_left (Commute.refl ζ) k).mul_pow]

theorem exists_bichar {E : Type} [Field E] [NumberField E] (N p n : ℕ) [NeZero n] (hn : p ∣ n) {U : Type} [CommGroup U]
    (ζ : U) (hζ : ζ ^ p = 1) (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod n) :
    ∃ β : TorsT E N p →* TorsT E N p →* U, ∀ x x', β (qmk p x) (qmk p x') = ζ ^ (e x x').val := by
  have hζn : ζ ^ n = 1 := by
    obtain ⟨k, hk⟩ := hn
    rw [hk, pow_mul, hζ, one_pow]
  have kk : ∀ a : ZMod n, ζ ^ (p • a).val = 1 := fun a => by
    rw [pow_val_nsmul hζn, hζ, one_pow]
  let inner : (Fin N → 𝓞 E) → (Multiplicative (Fin N → 𝓞 E) →* U) := fun x =>
    { toFun := fun x' => ζ ^ (e x (Multiplicative.toAdd x')).val
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [toAdd_mul, map_add]
        exact pow_val_add hζn _ _ }
  have hin : ∀ x z, qhom N p z = 1 → inner x z = 1 := fun x z hz => by
    obtain ⟨y', hy'⟩ := (qhom_eq_one N p (Multiplicative.toAdd z)).1 hz
    show ζ ^ (e x (Multiplicative.toAdd z)).val = 1
    rw [hy', map_nsmul]
    exact kk _
  let g : (Fin N → 𝓞 E) → (TorsT E N p →* U) := fun x =>
    liftSurj (qhom N p) (qhom_surj N p) (inner x) (hin x)
  have hg : ∀ x (z : Multiplicative (Fin N → 𝓞 E)),
      g x (qhom N p z) = ζ ^ (e x (Multiplicative.toAdd z)).val := fun x z =>
    liftSurj_apply _ _ _ _ z
  let outer : Multiplicative (Fin N → 𝓞 E) →* (TorsT E N p →* U) :=
    { toFun := fun x => g (Multiplicative.toAdd x)
      map_one' := by
        refine MonoidHom.ext fun t => ?_
        obtain ⟨z, rfl⟩ := qhom_surj N p t
        rw [MonoidHom.one_apply, hg]
        simp
      map_mul' := fun a b => by
        refine MonoidHom.ext fun t => ?_
        obtain ⟨z, rfl⟩ := qhom_surj N p t
        rw [MonoidHom.mul_apply, hg, hg, hg, toAdd_mul, map_add, AddMonoidHom.add_apply]
        exact pow_val_add hζn _ _ }
  refine ⟨liftSurj (qhom N p) (qhom_surj N p) outer ?_, fun x x' => ?_⟩
  · intro z hz
    obtain ⟨y', hy'⟩ := (qhom_eq_one N p (Multiplicative.toAdd z)).1 hz
    refine MonoidHom.ext fun t => ?_
    obtain ⟨w, rfl⟩ := qhom_surj N p t
    show g (Multiplicative.toAdd z) (qhom N p w) = 1
    rw [hg, hy', map_nsmul]
    exact kk _
  · show liftSurj _ _ outer _ (qhom N p (Multiplicative.ofAdd x)) (qhom N p (Multiplicative.ofAdd x')) = _
    rw [liftSurj_apply]
    show g x (qhom N p (Multiplicative.ofAdd x')) = _
    rw [hg]
    rfl

end PositivityTheory.Xgn.TestGroupPoint

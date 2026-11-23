import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.Model

theorem one_hom_eq {R₀ : Type} [CommRing R₀] (A : Over (Sp R₀)) [GrpObj A] :
    lift (𝟙 A) (1 : A ⟶ A) = lift (𝟙 A) (toUnit A ≫ η[A]) := rfl

section General

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}

@[nolint unusedArguments] def Idl (_hI : I ^ 2 = 0) (_hs : Function.Surjective π) (_hk : RingHom.ker π = I) : Type := I

variable (hI : I ^ 2 = 0) (hs : Function.Surjective π) (hk : RingHom.ker π = I)

instance : AddCommGroup (Idl hI hs hk) := inferInstanceAs (AddCommGroup I)
instance : Module R (Idl hI hs hk) := inferInstanceAs (Module R I)
instance : SMul R₀ (Idl hI hs hk) := ⟨fun r x ↦ Function.surjInv hs r • x⟩

include hI in
theorem mul_eq_zero_of_mem {a b : R} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 := by
  have := Ideal.mul_mem_mul ha hb
  rw [← pow_two, hI] at this
  simpa using this

theorem smul_idl (r : R) (x : Idl hI hs hk) : π r • x = r • x := by
  change Function.surjInv hs (π r) • x = r • x
  rw [← sub_eq_zero, ← sub_smul]
  refine Subtype.ext (mul_eq_zero_of_mem hI ?_ x.2)
  rw [← hk, RingHom.mem_ker, map_sub, Function.surjInv_eq hs, sub_self]

instance : Module R₀ (Idl hI hs hk) := hs.moduleLeft π (smul_idl hI hs hk)
instance : Module R₀ᵐᵒᵖ (Idl hI hs hk) := Module.compHom _ ((RingHom.id R₀).fromOpposite mul_comm)
instance : IsCentralScalar R₀ (Idl hI hs hk) := ⟨fun _ _ ↦ rfl⟩

def aug : Aug I π (TrivSqZeroExt R₀ (Idl hI hs hk)) where
  q := TrivSqZeroExt.fstHom R₀ R₀ _
  k := { toFun := fun y ↦ (show I from y.snd).1, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  mem y := (show I from y.snd).2
  smul r y := congrArg Subtype.val (smul_idl hI hs hk r y.snd)
  one := rfl
  sq y y' h h' := by
    have h1 : y.fst = 0 := h
    have h2 : y'.fst = 0 := h'
    ext <;> simp [h1, h2]
  inj y h h' := TrivSqZeroExt.ext h (Subtype.ext h')
  surj i hi := ⟨TrivSqZeroExt.inr (show Idl hI hs hk from ⟨i, hi⟩), rfl, rfl⟩

variable {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]

include hk in

theorem sq_of_aug (α : Aug I π R₁) {a b : R} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 := by
  obtain ⟨y, -, rfl⟩ := α.surj b hb
  have : π a = 0 := RingHom.mem_ker.1 (hk ▸ ha)
  rw [← α.smul, this, zero_smul, map_zero]

include hI hs in

theorem exists_isSig (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (semi : SemiHom π p) (surj : Function.Surjective p)
    (ker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) : ∃ σ, α.IsSig p σ := by
  have key : ∀ (y : R₁) (b b' : B), p b = p b' → α.k y • b = α.k y • b' := by
    intro y b b' h
    have h0 : b - b' ∈ I.map (algebraMap R B) := (ker _).1 (by rw [map_sub, h, sub_self])
    rw [← sub_eq_zero, ← smul_sub, Algebra.smul_def]
    exact mul_eq_zero_of_mem (map_sq hI B) (Ideal.mem_map_of_mem _ (α.mem y)) h0
  have e := Function.surjInv_eq surj
  let f : R₁ →+ B₀ →+ B := AddMonoidHom.mk' (fun y ↦ AddMonoidHom.mk' (fun b ↦ α.k y • Function.surjInv surj b)
    fun b b' ↦ by rw [← smul_add]; exact key _ _ _ (by rw [map_add, e, e, e])) fun y y' ↦ by
      ext b; simp [add_smul]
  refine ⟨TensorProduct.liftAddHom f fun r y b ↦ ?_, fun y b ↦ ?_⟩
  · obtain ⟨r, rfl⟩ := hs r
    change α.k (π r • y) • Function.surjInv surj b = α.k y • Function.surjInv surj (π r • b)
    rw [α.smul, mul_comm, mul_smul]
    exact key _ _ _ (by rw [semi, e, e])
  · exact key _ _ _ (e _)

variable {C C' : Type} [Category.{0} C] [Category.{0} C'] {F : C ⥤ CommAlgCat.{0} R₀} {F' : C' ⥤ CommAlgCat.{0} R₀}

include hI hs in

theorem isOb2_zero (L : Pre I π F) (h : L.IsFun) (α : Aug I π R₁) (w : Glob1 F) : L.IsOb2 α w 0 := by
  choose σ hσ using fun T ↦ exists_isSig hI hs α (L.p T) (L.semi T) (L.surj T) (L.ker T)
  refine ⟨0, σ, 0, fun T T' T'' a b ↦ ⟨fun _ _ ↦ by simp, fun x ↦ by simp [h a b x], fun _ ↦ by simp⟩, hσ,
    (map_zero _).symm, fun T T' T'' a b ↦ ⟨map_zero _, map_zero _⟩⟩

include hI hs in

theorem isOb1_zero (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F')
    (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (h : L.IsNat L' n l) (α : Aug I π R₁) (w : Glob1 F) :
    L.IsOb1 L' n l α w 0 := by
  choose σ hσ using fun T ↦ exists_isSig hI hs α (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T)
  refine ⟨0, σ, 0, fun T T' a ↦ ⟨fun _ _ ↦ by simp, fun x ↦ by simp [h a x], fun _ ↦ by simp⟩, hσ,
    (map_zero _).symm, fun T T' a ↦ ⟨map_zero _, map_zero _⟩⟩

end General

section Unique

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]

def sec (α : Aug I π R₁) : I →+ R₁ := AddMonoidHom.mk' (fun i ↦ (α.surj i.1 i.2).choose) fun i j ↦ by
  have h := fun i : I ↦ (α.surj i.1 i.2).choose_spec
  rw [← sub_eq_zero]
  exact α.inj _ (by simp only [map_sub, map_add, (h _).1]; ring) (by simp only [map_sub, map_add, (h _).2]; simp)

theorem q_sec (α : Aug I π R₁) (i : I) : α.q (sec α i) = 0 := (α.surj i.1 i.2).choose_spec.1

theorem k_sec (α : Aug I π R₁) (i : I) : α.k (sec α i) = i := (α.surj i.1 i.2).choose_spec.2

theorem sec_smul (α : Aug I π R₁) (r : R) (i : I) : sec α (r • i) = π r • sec α i := by
  rw [← sub_eq_zero]
  exact α.inj _ (by simp [q_sec]) (by simp [k_sec, α.smul])

theorem sig_inj (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [Module.Flat R B] [CommRing B₀]
    [Algebra R₀ B₀] (p : B →+* B₀) (semi : SemiHom π p) (surj : Function.Surjective p) {σ : R₁ ⊗[R₀] B₀ →+ B}
    (hσ : α.IsSig p σ) {y : R₁ ⊗[R₀] B₀} (hy : α.KerQ y) (h0 : σ y = 0) : y = 0 := by
  let f : I →+ B →+ R₁ ⊗[R₀] B₀ := AddMonoidHom.mk' (fun i ↦ AddMonoidHom.mk' (fun b ↦ sec α i ⊗ₜ p b)
    fun b b' ↦ by rw [map_add, TensorProduct.tmul_add]) fun i j ↦ by
      ext b; simp [TensorProduct.add_tmul]
  let τ : I ⊗[R] B →+ R₁ ⊗[R₀] B₀ := TensorProduct.liftAddHom f fun r i b ↦ by
    change sec α (r • i) ⊗ₜ p b = sec α i ⊗ₜ p (r • b)
    rw [sec_smul, semi, TensorProduct.smul_tmul]
  have hτ : ∀ i b, τ (i ⊗ₜ b) = sec α i ⊗ₜ p b := fun _ _ ↦ rfl
  have h1 : ∀ t, σ (τ t) = TensorProduct.lid R B (I.subtype.rTensor B t) := fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul i b => rw [hτ, hσ, k_sec]; simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have h2 : ∀ y : R₁ ⊗[R₀] B₀, ∃ t, τ t = y - Algebra.TensorProduct.map (Algebra.ofId R₀ R₁) (AlgHom.id R₀ B₀)
      (Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y) := fun y ↦ by
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x b =>
      obtain ⟨b, rfl⟩ := surj b
      refine ⟨(⟨_, α.mem (x - algebraMap R₀ R₁ (α.q x))⟩ : I) ⊗ₜ b, ?_⟩
      have : sec α ⟨_, α.mem (x - algebraMap R₀ R₁ (α.q x))⟩ = x - algebraMap R₀ R₁ (α.q x) := by
        rw [← sub_eq_zero]
        exact α.inj _ (by simp [q_sec]) (by rw [map_sub, k_sec]; simp)
      rw [hτ, this, TensorProduct.sub_tmul]
      simp [Algebra.ofId_apply]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      exact ⟨t + t', by simp only [map_add, ht, ht']; ring⟩
  obtain ⟨t, ht⟩ := h2 y
  rw [show Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y = 0 from hy, map_zero, sub_zero] at ht
  subst ht
  rw [h1, LinearEquiv.map_eq_zero_iff] at h0
  have : t = 0 := Module.Flat.rTensor_preserves_injective_linearMap (M := B) I.subtype Subtype.val_injective
    (h0.trans (map_zero _).symm)
  rw [this, map_zero]

theorem sig_unique (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀]
    [Algebra R₀ B₀] (p : B →+* B₀) (surj : Function.Surjective p) {σ σ' : R₁ ⊗[R₀] B₀ →+ B}
    (hσ : α.IsSig p σ) (hσ' : α.IsSig p σ') (y : R₁ ⊗[R₀] B₀) : σ y = σ' y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => obtain ⟨b, rfl⟩ := surj b; rw [hσ, hσ']
  | add x y hx hy => simp only [map_add, hx, hy]

theorem theta_unique {B B₀ B' : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] [CommRing B']
    [Algebra R B'] {p : B →+* B₀} (surj : Function.Surjective p) {α β : B →ₐ[R] B'} {θ θ' : Ω[B₀⁄R₀] →+ B'}
    (h : IsTheta I p α β θ) (h' : IsTheta I p α β θ') (w : Ω[B₀⁄R₀]) : θ w = θ' w := by
  induction w using ind1 with
  | h b c =>
    obtain ⟨b, rfl⟩ := surj b
    obtain ⟨c, rfl⟩ := surj c
    rw [h.smul, h'.smul, h.der, h'.der]
  | h0 => simp
  | ha x y hx hy => simp only [map_add, hx, hy]

variable {C C' : Type} [Category.{0} C] [Category.{0} C'] {F : C ⥤ CommAlgCat.{0} R₀} {F' : C' ⥤ CommAlgCat.{0} R₀}

theorem isOb2_unique (L : Pre I π F) (α : Aug I π R₁) (w : Glob1 F) {c c' : CatCoh.H2 (ext R₁ F)}
    (h : L.IsOb2 α w c) (h' : L.IsOb2 α w c') : c = c' := by
  obtain ⟨θ, σ, z, hθ, hσ, rfl, hz⟩ := h
  obtain ⟨θ', σ', z', hθ', hσ', rfl, hz'⟩ := h'
  refine congrArg _ (Subtype.ext ?_)
  funext T T' T'' a b
  haveI := L.smooth T''
  refine sub_eq_zero.1 (sig_inj α (L.p T'') (L.semi _) (L.surj _) (hσ T'') ?_ ?_)
  · exact (map_sub _ _ _).trans (by rw [(hz T T' T'' a b).1, (hz' T T' T'' a b).1, sub_zero])
  · rw [map_sub, sig_unique α _ (L.surj _) (hσ T'') (hσ' T'') (z'.1 _ _ _ a b), (hz T T' T'' a b).2,
      (hz' T T' T'' a b).2, theta_unique (L.surj T) (hθ T T' T'' a b) (hθ' T T' T'' a b), sub_self]

theorem isOb1_unique (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F')
    (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (α : Aug I π R₁) (w : Glob1 F) {c c' : CatCoh.H1 (ext R₁ F')}
    (h : L.IsOb1 L' n l α w c) (h' : L.IsOb1 L' n l α w c') : c = c' := by
  obtain ⟨θ, σ, z, hθ, hσ, rfl, hz⟩ := h
  obtain ⟨θ', σ', z', hθ', hσ', rfl, hz'⟩ := h'
  refine congrArg _ (Subtype.ext ?_)
  funext T T' a
  haveI := L'.smooth T'
  refine sub_eq_zero.1 (sig_inj α (L'.p T') (L'.semi _) (L'.surj _) (hσ T') ?_ ?_)
  · exact (map_sub _ _ _).trans (by rw [(hz T T' a).1, (hz' T T' a).1, sub_zero])
  · rw [map_sub, sig_unique α _ (L'.surj _) (hσ T') (hσ' T') (z'.1 _ _ a), (hz T T' a).2,
      (hz' T T' a).2, theta_unique (L.surj _) (hθ T T' a) (hθ' T T' a), sub_self]

end Unique

section Line

open Polynomial

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable (hI : I ^ 2 = 0) (hs : Function.Surjective π) (hk : RingHom.ker π = I)

@[reducible] def lineF (R₀ : Type) [CommRing R₀] (C : Type) [Category.{0} C] : C ⥤ CommAlgCat.{0} R₀ where
  obj _ := CommAlgCat.of R₀ R₀[X]
  map _ := CommAlgCat.ofHom (AlgHom.id R₀ R₀[X])
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev sh (i : I) : R[X] →ₐ[R] R[X] := aeval (X + C (i : R))

theorem sh_comp (i j : I) : (sh j).comp (sh i) = sh (i + j) := by
  ext; simp; ring

include hI in
theorem sh_apply (i : I) (b : R[X]) : sh i b = b + (i : R) • derivative b := by
  have h : (C (i : R) : R[X]) * C (i : R) = 0 := by rw [← C_mul, mul_eq_zero_of_mem hI i.2 i.2, C_0]
  induction b using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, smul_add]; ring
  | monomial n a ih =>
    rw [pow_succ, ← _root_.mul_assoc, map_mul, ih, derivative_mul (f := C a * X ^ n), aeval_X, derivative_X, smul_eq_C_mul, smul_eq_C_mul]
    linear_combination (derivative (C a * X ^ n)) * h

include hk in
theorem map_sh (i : I) (b : R[X]) : mapRingHom π (sh i b) = mapRingHom π b := by
  have hi : π i = 0 := RingHom.mem_ker.1 (hk ▸ i.2)
  have : (mapRingHom π).comp (sh i : R[X] →+* R[X]) = mapRingHom π := by
    ext <;> simp [hi]
  exact RingHom.congr_fun this b

variable {C : Type} [Category.{0} C]

@[reducible] def shPre (c : ∀ T T' : C, (T ⟶ T') → I) : Pre I π (lineF R₀ C) where
  B _ := CommAlgCat.of R R[X]
  p _ := mapRingHom π
  semi _ r b := by simp [smul_eq_C_mul]
  surj _ := Polynomial.map_surjective π hs
  ker _ b := by
    rw [← RingHom.mem_ker, Polynomial.ker_mapRingHom, hk]; rfl
  smooth _ := (⟨inferInstance, inferInstance⟩ : Algebra.Smooth R R[X])
  ρ a := sh (c _ _ a)
  nat a b := map_sh hk _ b

theorem shPre_isFun_iff (c : ∀ T T' : C, (T ⟶ T') → I) : (shPre hs hk c).IsFun ↔
    ∀ ⦃T T' T'' : C⦄ (a : T ⟶ T') (b : T' ⟶ T''), c _ _ (a ≫ b) = c _ _ a + c _ _ b := by
  refine ⟨fun h T T' T'' a b ↦ ?_, fun h T T' T'' a b x ↦ ?_⟩
  · have e : sh (c _ _ (a ≫ b)) X = ((sh (c _ _ b)).comp (sh (c _ _ a))) X := h a b X
    rw [sh_comp, aeval_X, aeval_X, add_right_inj, C_inj] at e
    exact Subtype.ext e
  · change sh (c _ _ (a ≫ b)) x = ((sh (c _ _ b)).comp (sh (c _ _ a))) x
    rw [sh_comp, h]

theorem not_isFun {i : I} (hi : i ≠ 0) : ¬ (shPre (C := Discrete PUnit.{1}) hs hk fun _ _ _ ↦ i).IsFun := fun h ↦
  hi (by simpa using (shPre_isFun_iff hs hk _).1 h (𝟙 ⟨⟨⟩⟩) (𝟙 _))

def th (α : Aug I π R₁) (σ : R₁ ⊗[R₀] R₀[X] →+ R[X]) (i : I) : Ω[R₀[X]⁄R₀] →+ R[X] :=
  AddMonoidHom.mk' (fun w ↦ σ (sec α i ⊗ₜ polynomialEquiv R₀ w)) fun _ _ ↦ by
    rw [map_add, TensorProduct.tmul_add, map_add]

include hI hs in
theorem isTheta_th (α : Aug I π R₁) {σ : R₁ ⊗[R₀] R₀[X] →+ R[X]} (hσ : α.IsSig (mapRingHom π) σ) (i j : I) :
    IsTheta I (mapRingHom π) (sh i) (sh j) (th α σ (i - j)) := by
  have v : ∀ w b, mapRingHom π b = polynomialEquiv R₀ w → th α σ (i - j) w = ((i - j : I) : R) • b := fun w b e ↦ by
    change σ (_ ⊗ₜ polynomialEquiv R₀ w) = _
    rw [← e, hσ, k_sec]
  refine ⟨fun b w ↦ ?_, fun b ↦ ?_, fun w ↦ ?_⟩
  · obtain ⟨u, hu⟩ := Polynomial.map_surjective π hs (polynomialEquiv R₀ w)
    rw [v w u hu, v _ (b * u) (by rw [map_smul, map_mul, ← hu]; rfl), sh_apply hI, add_mul, smul_mul_smul_comm,
      mul_eq_zero_of_mem hI i.2 (i - j).2, zero_smul, add_zero, mul_smul_comm]
  · rw [v _ (derivative b) (by simp), sh_apply hI, sh_apply hI]
    simp [sub_smul]
  · obtain ⟨u, hu⟩ := Polynomial.map_surjective π hs (polynomialEquiv R₀ w)
    rw [v w u hu, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (i - j).2)

def dX (R₀ : Type) [CommRing R₀] (C : Type) [Category.{0} C] : Glob1 (lineF R₀ C) :=
  ⟨fun _ ↦ D R₀ R₀[X] X, fun _ _ a ↦ by
    first | exact p1_D (lineF R₀ C) a X | exact (p1_D (lineF R₀ C) a X).symm⟩

include hI in

theorem exists_isOb2 (c : ∀ T T' : C, (T ⟶ T') → I) (α : Aug I π R₁) :
    ∃ z, (shPre hs hk c).IsOb2 α (dX R₀ C) z := by
  let L := shPre hs hk c
  obtain ⟨σ, hσ⟩ := exists_isSig hI hs α (B := R[X]) (B₀ := R₀[X]) (mapRingHom π)
    (fun r b ↦ by simp [smul_eq_C_mul]) (Polynomial.map_surjective π hs)
    (fun b ↦ by rw [← RingHom.mem_ker, Polynomial.ker_mapRingHom, hk]; rfl)
  let z : Z2 (ext R₁ (lineF R₀ C)) := ⟨fun T T' T'' a b ↦ sec α (c _ _ a + c _ _ b - c _ _ (a ≫ b)) ⊗ₜ 1,
    fun T T' T'' T''' a b d ↦ by
      change extHom R₁ (AlgHom.id R₀ R₀[X]) _ + _ = _
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ← TensorProduct.add_tmul, ← map_add, Category.assoc]
      congr 2; abel⟩
  refine ⟨_, fun T T' T'' a b ↦ th α σ (c _ _ a + c _ _ b - c _ _ (a ≫ b)), fun _ ↦ σ, z, fun T T' T'' a b ↦ ?_,
    fun _ ↦ hσ, rfl, fun T T' T'' a b ↦ ⟨?_, ?_⟩⟩
  · have := isTheta_th hI hs α hσ (c _ _ a + c _ _ b) (c _ _ (a ≫ b))
    rw [← sh_comp] at this
    exact this
  · change Algebra.TensorProduct.map α.q (AlgHom.id R₀ R₀[X]) (_ ⊗ₜ 1) = 0
    simp [q_sec]
  · change σ (_ ⊗ₜ 1) = σ (_ ⊗ₜ polynomialEquiv R₀ (D R₀ R₀[X] X))
    simp

include hI hs hk in

theorem exists_isOb1_ne_zero {i : I} (hi : i ≠ 0) (α : Aug I π R₁) :
    ∃ (L L' : Pre I π (lineF R₀ (SingleObj (Multiplicative I)))) (l : ∀ T, L.B T →ₐ[R] L'.B T) (z : CatCoh.H1 _),
      L.IsFun ∧ L'.IsFun ∧ L.IsLift L' (CoefMap.id _) l ∧ L.IsOb1 L' (CoefMap.id _) l α (dX R₀ _) z ∧ z ≠ 0 := by
  obtain ⟨σ, hσ⟩ := exists_isSig hI hs α (B := R[X]) (B₀ := R₀[X]) (mapRingHom π)
    (fun r b ↦ by simp [smul_eq_C_mul]) (Polynomial.map_surjective π hs)
    (fun b ↦ by rw [← RingHom.mem_ker, Polynomial.ker_mapRingHom, hk]; rfl)
  let c : ∀ T T' : SingleObj (Multiplicative I), (T ⟶ T') → I := fun _ _ a ↦ Multiplicative.toAdd a
  have hc : ∀ ⦃T T' T''⦄ (a : T ⟶ T') (b : T' ⟶ T''), c _ _ (a ≫ b) = c _ _ a + c _ _ b := fun _ _ _ a b ↦ add_comm _ _
  let z : Z1 (ext R₁ (lineF R₀ (SingleObj (Multiplicative I)))) := ⟨fun T T' a ↦ sec α (c _ _ a) ⊗ₜ 1,
    fun T T' T'' a b ↦ by
      change _ = extHom R₁ (AlgHom.id R₀ R₀[X]) _ + _
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ← TensorProduct.add_tmul, ← map_add, hc]⟩
  refine ⟨shPre hs hk fun _ _ _ ↦ 0, shPre hs hk c, fun _ ↦ AlgHom.id R R[X], H1.mk _ z,
    (shPre_isFun_iff hs hk _).2 fun _ _ _ _ _ ↦ (add_zero _).symm, (shPre_isFun_iff hs hk _).2 hc, fun _ _ ↦ rfl,
    ⟨fun T T' a ↦ th α σ (c _ _ a - 0), fun _ ↦ σ, z, fun T T' a ↦ isTheta_th hI hs α hσ _ 0, fun _ ↦ hσ, rfl,
      fun T T' a ↦ ⟨?_, ?_⟩⟩, fun h ↦ hi ?_⟩
  · change Algebra.TensorProduct.map α.q (AlgHom.id R₀ R₀[X]) (_ ⊗ₜ 1) = 0
    simp [q_sec]
  · change σ (_ ⊗ₜ 1) = σ (_ ⊗ₜ polynomialEquiv R₀ (D R₀ R₀[X] X))
    simp
  · obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 h
    have e := congrFun (congrFun (congrFun hg (SingleObj.star _)) (SingleObj.star _)) (Multiplicative.ofAdd i)
    change g _ - extHom R₁ (AlgHom.id R₀ R₀[X]) (g _) = sec α i ⊗ₜ 1 at e
    rw [extHom, Algebra.TensorProduct.map_id, AlgHom.id_apply, sub_self] at e
    have e' := hσ (sec α i) 1
    rw [map_one, ← e, map_zero, k_sec, smul_eq_C_mul, _root_.mul_one, eq_comm, C_eq_zero] at e'
    exact Subtype.ext e'

end Line

theorem four_two : ∃ (I : Ideal (ZMod 4)) (π : ZMod 4 →+* ZMod 2), I ^ 2 = 0 ∧ Function.Surjective π ∧
    RingHom.ker π = I ∧ ∃ i : I, i ≠ 0 := by
  refine ⟨_, ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2), ?_, ZMod.ringHom_surjective _, rfl,
    ⟨2, by rw [RingHom.mem_ker]; decide⟩, fun h ↦ absurd (congrArg Subtype.val h) (by decide)⟩
  rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
  simp only [RingHom.mem_ker, Ideal.mem_bot]
  decide

end GlobalTheory.Obs.Model

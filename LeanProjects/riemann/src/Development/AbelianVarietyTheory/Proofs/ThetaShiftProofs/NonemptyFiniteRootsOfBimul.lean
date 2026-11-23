import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.GlActionMemBalFormsOfSemilinear

open TensorProduct

namespace GlobalTheory.Forms

section Projective

variable (O : Type*) [CommRing O] (X : Type*) [AddCommGroup X] [Module O X]

theorem torsion_eq_bot_of_int [IsDomain O] [Module.Finite ℤ O]
    [Module.IsTorsionFree ℤ X] : Submodule.torsion O X = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  obtain ⟨n, hn, c, hc⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) a).exists_nonzero_dvd ha
  have h : n • x = 0 := by
    have hx' : a • x = 0 := hx
    rw [← Int.cast_smul_eq_zsmul O, ← eq_intCast (algebraMap ℤ O), hc, mul_comm, mul_smul, hx',
      smul_zero]
  exact (smul_eq_zero.1 h).resolve_left hn

theorem projective_of_int [IsDedekindDomain O] [Module.Finite ℤ O] [Module.Finite ℤ X]
    [Module.IsTorsionFree ℤ X] : Module.Projective O X := by
  have : Module.Finite O X := Module.Finite.of_restrictScalars_finite ℤ O X
  have : Module.Flat O X :=
    IsDedekindDomain.flat_iff_torsion_eq_bot.2 (torsion_eq_bot_of_int O X)
  have : Module.FinitePresentation O X := Module.finitePresentation_of_finite O X
  exact Module.Flat.projective_of_finitePresentation

variable {O X} in

theorem exists_linearMap_lift_of_int [IsDedekindDomain O] [Module.Finite ℤ O] [Module.Finite ℤ X]
    [Module.IsTorsionFree ℤ X] {N N' : Type*} [AddCommGroup N] [Module O N] [AddCommGroup N']
    [Module O N'] (p : N →ₗ[O] N') (hp : Function.Surjective p) (f : X →ₗ[O] N') :
    ∃ g : X →ₗ[O] N, ∀ x, p (g x) = f x := by
  have := projective_of_int O X
  obtain ⟨g, hg⟩ := Module.projective_lifting_property p f hp
  exact ⟨g, fun x => congr($hg x)⟩

end Projective

section Lift

variable {O : Type*} [CommRing O] [StarRing O] {X : Type*} [AddCommGroup X] [Module O X]

def pairForm (f g : X →ₗ[O] O) : Bil X O :=
  LinearMap.mk₂ ℤ (fun y x => f y * star (g x) + f x * star (g y))
    (fun _ _ _ => by simp only [map_add, star_add]; ring)
    (fun n _ _ => by simp only [map_zsmul, zsmul_eq_mul, star_mul, star_intCast]; ring)
    (fun _ _ _ => by simp only [map_add, star_add]; ring)
    (fun n _ _ => by simp only [map_zsmul, zsmul_eq_mul, star_mul, star_intCast]; ring)

@[simp] theorem pairForm_apply (f g : X →ₗ[O] O) (y x : X) :
    pairForm f g y x = f y * star (g x) + f x * star (g y) := rfl

theorem pairForm_mem_balForms (f g : X →ₗ[O] O) : pairForm f g ∈ balForms ℤ O X O :=
  ⟨fun y x => by simp only [pairForm_apply]; ring, fun a y x => by
    simp only [pairForm_apply, map_smul, smul_eq_mul, star_mul, star_star]; ring⟩

theorem exists_universal_pi {w : O} (hw : w + star w = 1) [Module.Finite O X]
    [Module.Projective O X] :
    ∃ (n : ℕ) (Φ : Bil X (Fin n × Fin n → O)), Φ ∈ balForms ℤ O X (Fin n × Fin n → O) ∧
      ∃ e : Fin n → X, ∀ {B : Type*} [AddCommGroup B] (τ : Bil X B), τ ∈ balForms ℤ O X B →
        ∀ y x, τ y x = ∑ ij : Fin n × Fin n, τ ((w * Φ y x ij) • e ij.1) (e ij.2) := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective O X
  let c : Fin n → X →ₗ[O] O := fun i => LinearMap.proj i ∘ₗ g
  let e : Fin n → X := fun i => f (Pi.single i 1)
  have he (x : X) : ∑ i, c i x • e i = x := by
    have h1 : f (g x) = x := congr($hfg x)
    conv_rhs => rw [← h1, pi_eq_sum_univ' (g x), map_sum]
    simp [c, e]
  let Φ : Bil X (Fin n × Fin n → O) :=
    LinearMap.mk₂ ℤ (fun y x ij => pairForm (c ij.1) (c ij.2) y x)
      (fun _ _ _ => by ext; simp only [map_add, LinearMap.add_apply, Pi.add_apply])
      (fun _ _ _ => by ext; simp only [map_zsmul, LinearMap.smul_apply, Pi.smul_apply])
      (fun _ _ _ => by ext; simp only [map_add, Pi.add_apply])
      (fun _ _ _ => by ext; simp only [map_zsmul, Pi.smul_apply])
  refine ⟨n, Φ, ⟨fun y x => funext fun ij => (pairForm_mem_balForms _ _).1 y x,
    fun a y x => funext fun ij => (pairForm_mem_balForms _ _).2 a y x⟩, e, ?_⟩
  intro B _ τ hτ
  have key (y x : X) : ∑ ij : Fin n × Fin n,
      τ ((w * (c ij.1 y * star (c ij.2 x))) • e ij.1) (e ij.2) = τ (w • y) x := by
    conv_rhs => rw [← he y, ← he x]
    rw [Fintype.sum_prod_type, Finset.smul_sum, map_sum τ, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hτ.2.right, smul_smul, smul_smul]
    congr 3
    ring
  intro y x
  have h (ij : Fin n × Fin n) : τ ((w * Φ y x ij) • e ij.1) (e ij.2) =
      τ ((w * (c ij.1 y * star (c ij.2 x))) • e ij.1) (e ij.2) +
        τ ((w * (c ij.1 x * star (c ij.2 y))) • e ij.1) (e ij.2) := by
    rw [← LinearMap.add_apply, ← map_add, ← add_smul, ← mul_add]
    rfl
  simp only [h, Finset.sum_add_distrib, key]
  rw [hτ.1 (w • x) y, add_comm, hτ.2.add_of_add_star hw]

theorem exists_balForms_lift {w : O} (hw : w + star w = 1) [Module.Finite O X]
    [Module.Projective O X] [Module.Free ℤ O] {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] (p : A →+ B) (hp : Function.Surjective p) {τ : Bil X B}
    (hτ : τ ∈ balForms ℤ O X B) :
    ∃ T ∈ balForms ℤ O X A, ∀ y x, p (T y x) = τ y x := by
  obtain ⟨n, Φ, hΦ, e, h⟩ := exists_universal_pi (X := X) hw
  let r : (Fin n × Fin n → O) →ₗ[ℤ] B :=
    ∑ ij : Fin n × Fin n, τ.flip (e ij.2) ∘ₗ
      ((LinearMap.toSpanSingleton O X (e ij.1)) ∘ₗ LinearMap.mulLeft O w ∘ₗ
        LinearMap.proj ij).restrictScalars ℤ
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p.toIntLinearMap r hp
  refine ⟨Φ.compr₂ s, ⟨fun y x => congrArg s (hΦ.1 y x), fun a y x => congrArg s (hΦ.2 a y x)⟩,
    fun y x => ?_⟩
  have h1 : p (s (Φ y x)) = r (Φ y x) := congr($hs (Φ y x))
  rw [h τ hτ, LinearMap.compr₂_apply, h1, LinearMap.sum_apply]
  rfl

theorem balRel_eq_span {w : O} (hw : w + star w = 1) [Module.Finite O X]
    [Module.Projective O X] [Module.IsTorsionFree ℤ O] :
    balRel O X = Submodule.span ℤ
      {z : SymSq X | ∃ (a : O) (y x : X), z = SymSq.mk (a • y) x - SymSq.mk y (star a • x)} := by
  refine le_antisymm (fun z hz => ?_) fun z hz => mem_balRel.2 ⟨1, one_ne_zero, by rwa [one_smul]⟩
  set R := Submodule.span ℤ
      {z : SymSq X | ∃ (a : O) (y x : X), z = SymSq.mk (a • y) x - SymSq.mk y (star a • x)}
  obtain ⟨n, Φ, hΦ, e, h⟩ := exists_universal_pi (X := X) hw
  let τ : Bil X (SymSq X ⧸ R) := SymSq.mk.compr₂ R.mkQ
  have hτ : τ ∈ balForms ℤ O X (SymSq X ⧸ R) :=
    ⟨fun y x => congrArg R.mkQ (SymSq.mk_comm y x), fun a y x =>
      (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨a, y, x, rfl⟩)⟩
  let r : (Fin n × Fin n → O) →ₗ[ℤ] SymSq X ⧸ R :=
    ∑ ij : Fin n × Fin n, τ.flip (e ij.2) ∘ₗ
      ((LinearMap.toSpanSingleton O X (e ij.1)) ∘ₗ LinearMap.mulLeft O w ∘ₗ
        LinearMap.proj ij).restrictScalars ℤ
  have h1 : R.mkQ = r ∘ₗ BalSq.lift ℤ O X _ ⟨Φ, hΦ⟩ ∘ₗ (balRel O X).mkQ := by
    refine SymSq.hom_ext fun y x => ?_
    change τ y x = r (Φ y x)
    rw [h τ hτ, LinearMap.sum_apply]
    rfl
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, h1, LinearMap.comp_apply,
    LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hz, map_zero,
    map_zero]

theorem BalSq.exists_lift {w : O} (hw : w + star w = 1) [Module.Finite O X]
    [Module.Projective O X] [Module.IsTorsionFree ℤ O] {B : Type*} [AddCommGroup B] {τ : Bil X B}
    (hτ : τ ∈ balForms ℤ O X B) :
    ∃ l : BalSq O X →ₗ[ℤ] B, ∀ y x, l (BalSq.mk O y x) = τ y x := by
  refine ⟨(balRel O X).liftQ (SymSq.lift ℤ X B ⟨τ, hτ.1⟩) ?_, fun _ _ => rfl⟩
  rw [balRel_eq_span hw, Submodule.span_le]
  rintro _ ⟨a, y, x, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub]
  exact sub_eq_zero.2 (hτ.2 a y x)

variable (O X) in

def balTensorRel : AddSubgroup (X ⊗[ℤ] X) :=
  AddSubgroup.closure
    ({z | ∃ (a : O) (y x : X), z = (a • y) ⊗ₜ x - y ⊗ₜ (star a • x)} ∪
      {z | ∃ y x : X, z = y ⊗ₜ x - x ⊗ₜ y})

variable (O) in

def balTensorMk : Bil X ((X ⊗[ℤ] X) ⧸ balTensorRel O X) :=
  LinearMap.mk₂ ℤ (fun y x => QuotientAddGroup.mk' (balTensorRel O X) (y ⊗ₜ x))
    (fun _ _ _ => by rw [add_tmul, map_add])
    (fun n y y' => by rw [← map_zsmul]; rfl)
    (fun _ _ _ => by rw [tmul_add, map_add])
    (fun n y y' => by rw [← map_zsmul, ← smul_tmul]; rfl)

variable (O X) in
theorem balTensorMk_mem_balForms :
    balTensorMk O ∈ balForms ℤ O X ((X ⊗[ℤ] X) ⧸ balTensorRel O X) :=
  ⟨fun y x => QuotientAddGroup.eq_iff_sub_mem.2 (AddSubgroup.subset_closure (Or.inr ⟨y, x, rfl⟩)),
    fun a y x =>
      QuotientAddGroup.eq_iff_sub_mem.2 (AddSubgroup.subset_closure (Or.inl ⟨a, y, x, rfl⟩))⟩

def balTensorLift {B : Type*} [AddCommGroup B] (τ : balForms ℤ O X B) :
    (X ⊗[ℤ] X) ⧸ balTensorRel O X →+ B :=
  QuotientAddGroup.lift _ (TensorProduct.lift τ.1).toAddMonoidHom <|
    (AddSubgroup.closure_le _).2 <| by
      rintro _ (⟨a, y, x, rfl⟩ | ⟨y, x, rfl⟩) <;>
        rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub]
      · exact sub_eq_zero.2 (τ.2.2 a y x)
      · exact sub_eq_zero.2 (τ.2.1 y x)

@[simp] theorem balTensorLift_mk {B : Type*} [AddCommGroup B] (τ : balForms ℤ O X B) (y x : X) :
    balTensorLift τ (balTensorMk O y x) = (τ : Bil X B) y x := rfl

theorem balTensor_hom_ext {B : Type*} [AddCommGroup B]
    {f g : (X ⊗[ℤ] X) ⧸ balTensorRel O X →+ B}
    (h : ∀ y x, f (balTensorMk O y x) = g (balTensorMk O y x)) : f = g := by
  refine AddMonoidHom.ext fun z => ?_
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective _ z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul y x => exact h y x
  | add x y hx hy => simp only [map_add, hx, hy]

theorem balTensorLift_bijective {w : O} (hw : w + star w = 1) [Module.Finite O X]
    [Module.Projective O X] [Module.IsTorsionFree ℤ O] :
    Function.Bijective (balTensorLift ⟨BalSq.mk O, BalSq.mk_mem_balForms O X⟩) := by
  obtain ⟨l, hl⟩ := BalSq.exists_lift hw (balTensorMk_mem_balForms O X)
  set F := balTensorLift ⟨BalSq.mk O, BalSq.mk_mem_balForms O X⟩
  have h1 : l.toAddMonoidHom.comp F = AddMonoidHom.id _ := balTensor_hom_ext hl
  have h2 : F.toIntLinearMap ∘ₗ l = LinearMap.id := BalSq.hom_ext fun y x => by
    change F (l (BalSq.mk O y x)) = _
    rw [hl]
    rfl
  exact Function.bijective_iff_has_inverse.2 ⟨l, fun z => congr($h1 z), fun z => congr($h2 z)⟩

noncomputable def balTensorEquiv {w : O} (hw : w + star w = 1) [Module.Finite O X]
    [Module.Projective O X] [Module.IsTorsionFree ℤ O] :
    ((X ⊗[ℤ] X) ⧸ balTensorRel O X) ≃+ BalSq O X :=
  AddEquiv.ofBijective _ (balTensorLift_bijective hw)

@[simp] theorem balTensorEquiv_mk {w : O} (hw : w + star w = 1) [Module.Finite O X]
    [Module.Projective O X] [Module.IsTorsionFree ℤ O] (y x : X) :
    balTensorEquiv hw (balTensorMk O y x) = BalSq.mk O y x := rfl

theorem isTorsionFree_balTensor {w : O} (hw : w + star w = 1) [Module.Finite O X]
    [Module.Projective O X] [Module.IsTorsionFree ℤ O] :
    Module.IsTorsionFree ℤ ((X ⊗[ℤ] X) ⧸ balTensorRel O X) :=
  (balTensorEquiv hw).toIntLinearEquiv.injective.moduleIsTorsionFree _
    (balTensorEquiv hw).toIntLinearEquiv.map_smul

theorem finite_balTensor [Module.Finite ℤ X] :
    Module.Finite ℤ ((X ⊗[ℤ] X) ⧸ balTensorRel O X) := by
  have h : Module.Finite ℤ (X ⊗[ℤ] X) := by
    convert Module.Finite.tensorProduct ℤ X X using 0
    congr!
  exact Module.Finite.of_surjective (QuotientAddGroup.mk' (balTensorRel O X)).toIntLinearMap
    (QuotientAddGroup.mk'_surjective _)

theorem free_balTensor {w : O} (hw : w + star w = 1) [Module.Finite ℤ X]
    [Module.Projective O X] [Module.IsTorsionFree ℤ O] :
    Module.Free ℤ ((X ⊗[ℤ] X) ⧸ balTensorRel O X) := by
  have : Module.Finite O X := Module.Finite.of_restrictScalars_finite ℤ O X
  have := isTorsionFree_balTensor (X := X) hw
  have := finite_balTensor (O := O) (X := X)
  exact Module.free_of_finite_type_torsion_free'

def bilOfMul {X G : Type*} [AddCommGroup X] [CommGroup G] (t : X → X → G)
    (h₁ : ∀ y y' x, t (y + y') x = t y x * t y' x) (h₂ : ∀ y x x', t y (x + x') = t y x * t y x') :
    Bil X (Additive G) :=
  (AddMonoidHom.mk' (fun y => (AddMonoidHom.mk' (fun x => Additive.ofMul (t y x))
    (h₂ y)).toIntLinearMap) fun y y' => LinearMap.ext fun x => h₁ y y' x).toIntLinearMap

@[simp] theorem bilOfMul_apply {X G : Type*} [AddCommGroup X] [CommGroup G] (t : X → X → G)
    (h₁ : ∀ y y' x, t (y + y') x = t y x * t y' x) (h₂ : ∀ y x x', t y (x + x') = t y x * t y x')
    (y x : X) : bilOfMul t h₁ h₂ y x = Additive.ofMul (t y x) := rfl

noncomputable def expTwoPiI : ℂ →+ Additive ℂˣ :=
  AddMonoidHom.mk' (fun z => Additive.ofMul
    (Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * z)) (Complex.exp_ne_zero _)))
    fun z z' => Units.ext <| by
      change Complex.exp _ = Complex.exp _ * Complex.exp _
      rw [← Complex.exp_add, mul_add]

theorem coe_expTwoPiI (z : ℂ) :
    ((expTwoPiI z).toMul : ℂ) = Complex.exp (2 * Real.pi * Complex.I * z) := rfl

theorem expTwoPiI_surjective : Function.Surjective expTwoPiI := fun u =>
  ⟨Complex.log (u.toMul : ℂ) / (2 * Real.pi * Complex.I), Units.ext <| by
    change Complex.exp _ = (u.toMul : ℂ)
    rw [mul_div_cancel₀ _ Complex.two_pi_I_ne_zero, Complex.exp_log (Units.ne_zero _)]⟩

theorem exists_balForms_log {w : O} (hw : w + star w = 1) [Module.Finite O X]
    [Module.Projective O X] [Module.Free ℤ O] {τ : Bil X (Additive ℂˣ)}
    (hτ : τ ∈ balForms ℤ O X (Additive ℂˣ)) :
    ∃ T ∈ balForms ℤ O X ℂ,
      ∀ y x, ((τ y x).toMul : ℂ) = Complex.exp (2 * Real.pi * Complex.I * T y x) := by
  obtain ⟨T, hT, h⟩ := exists_balForms_lift hw expTwoPiI expTwoPiI_surjective hτ
  exact ⟨T, hT, fun y x => by rw [← h, coe_expTwoPiI]⟩

theorem exists_log_of_bimul {w : O} (hw : w + star w = 1) [Module.Finite O X]
    [Module.Projective O X] [Module.Free ℤ O] (t : X → X → ℂˣ)
    (h₂ : ∀ y x x', t y (x + x') = t y x * t y x') (hs : ∀ y x, t y x = t x y)
    (hb : ∀ (a : O) y x, t (a • y) x = t y (star a • x)) :
    ∃ T : X →ₗ[ℤ] X →ₗ[ℤ] ℂ, (∀ y x, T y x = T x y) ∧
      (∀ (a : O) y x, T (a • y) x = T y (star a • x)) ∧
      ∀ y x, (t y x : ℂ) = Complex.exp (2 * Real.pi * Complex.I * T y x) := by
  have h₁ : ∀ y y' x, t (y + y') x = t y x * t y' x := fun y y' x => by
    rw [hs, h₂, hs x, hs x]
  obtain ⟨T, hT, h⟩ := exists_balForms_log hw (τ := bilOfMul t h₁ h₂) ⟨hs, hb⟩
  exact ⟨T, hT.1, hT.2, h⟩

theorem exists_log_of_bimul_ne_zero {w : O} (hw : w + star w = 1) [Module.Finite O X]
    [Module.Projective O X] [Module.Free ℤ O] (t : X → X → ℂ) (h₀ : ∀ y x, t y x ≠ 0)
    (h₂ : ∀ y x x', t y (x + x') = t y x * t y x') (hs : ∀ y x, t y x = t x y)
    (hb : ∀ (a : O) y x, t (a • y) x = t y (star a • x)) :
    ∃ T : X →ₗ[ℤ] X →ₗ[ℤ] ℂ, (∀ y x, T y x = T x y) ∧
      (∀ (a : O) y x, T (a • y) x = T y (star a • x)) ∧
      ∀ y x, t y x = Complex.exp (2 * Real.pi * Complex.I * T y x) :=
  exists_log_of_bimul hw (fun y x => Units.mk0 (t y x) (h₀ y x))
    (fun y x x' => Units.ext (h₂ y x x')) (fun y x => Units.ext (hs y x))
    fun a y x => Units.ext (hb a y x)

end Lift

end GlobalTheory.Forms

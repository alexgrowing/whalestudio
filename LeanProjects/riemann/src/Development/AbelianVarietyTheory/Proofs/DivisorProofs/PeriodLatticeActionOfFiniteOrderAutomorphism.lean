import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodLattice

variable {P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)}

theorem one_comp_of_isMonHom (f : P.A ⟶ P.A) (hf : IsMonHom f) :
    (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) ≫ f = 1 :=
  (IsMonHom.monoidHom f (𝟙_ (Over (Sp ℂ)))).map_one

theorem comp_mul' (x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) (f g : P.A ⟶ P.A) : x ≫ (f * g) = (x ≫ f) * (x ≫ g) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

theorem comp_one' (x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) : x ≫ (1 : P.A ⟶ P.A) = 1 := by
  simp [Hom.one_def]

section Lift

variable (u : HolUnif P.A P.L P.g)

theorem ex_zero : u.ex 0 = 1 := by
  have h := u.ex_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem ex_nsmul (k : ℕ) (z : Fin P.g → ℂ) : u.ex (k • z) = u.ex z ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero, ex_zero]
  | succ k ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem lift_unique (f : P.A ⟶ P.A) (F F' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ))
    (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) (hF' : ∀ z, u.ex (F' z) = u.ex z ≫ f) : F = F' := by
  have hmem : ∀ z, (F - F') z ∈ u.Λ := by
    intro z
    rw [← u.ker]
    have h := u.ex_add ((F - F') z) (F' z)
    rw [LinearMap.sub_apply, sub_add_cancel, hF, hF'] at h
    exact mul_eq_right.mp h.symm
  haveI := u.discrete
  let D : (Fin P.g → ℂ) → u.Λ := fun z => ⟨(F - F') z, hmem z⟩
  have hD : Continuous D :=
    Continuous.subtype_mk (LinearMap.continuous_of_finiteDimensional _) _
  refine LinearMap.ext fun z => ?_
  have h1 : D z = D 0 := PreconnectedSpace.constant inferInstance hD
  have h2 : (F - F') z = 0 := by
    have := congrArg Subtype.val h1
    simpa [D] using this
  exact sub_eq_zero.mp (by simpa using h2)

variable (hl : ∀ f : P.A ⟶ P.A, IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f)

def lift (f : P.A ⟶ P.A) (hf : IsMonHom f) : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ) := Classical.choose (hl f hf)

theorem lift_spec (f : P.A ⟶ P.A) (hf : IsMonHom f) (z) : u.ex (lift u hl f hf z) = u.ex z ≫ f :=
  Classical.choose_spec (hl f hf) z

theorem lift_eq (f : P.A ⟶ P.A) (hf : IsMonHom f) (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ))
    (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) : lift u hl f hf = F :=
  lift_unique u f _ _ (lift_spec u hl f hf) hF

theorem lift_mem (f : P.A ⟶ P.A) (hf : IsMonHom f) {z} (hz : z ∈ u.Λ) : lift u hl f hf z ∈ u.Λ := by
  rw [← u.ker] at hz ⊢
  rw [lift_spec, hz, one_comp_of_isMonHom f hf]

def liftZ (f : P.A ⟶ P.A) (hf : IsMonHom f) : Module.End ℤ u.Λ where
  toFun x := ⟨lift u hl f hf x, lift_mem u hl f hf x.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (map_zsmul (lift u hl f hf) c (x : Fin P.g → ℂ))

@[simp] theorem liftZ_val (f : P.A ⟶ P.A) (hf : IsMonHom f) (x : u.Λ) :
    ((liftZ u hl f hf x : u.Λ) : Fin P.g → ℂ) = lift u hl f hf x := rfl

end Lift

section Ring

variable (u : HolUnif P.A P.L P.g)
  (hl : ∀ f : P.A ⟶ P.A, IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f)
  {O : Type} [CommRing O] (act : OAct O P.A)

theorem act_zero : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

def ringAct : O →+* Module.End ℤ u.Λ where
  toFun c := liftZ u hl (act.act c) (act.hom c)
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [liftZ_val, Module.End.one_apply]
    rw [lift_eq u hl _ _ LinearMap.id (fun z => by rw [act.one, Category.comp_id]; rfl)]
    rfl
  map_mul' a b := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [liftZ_val, Module.End.mul_apply]
    rw [lift_eq u hl _ _ ((lift u hl (act.act a) (act.hom a)).comp (lift u hl (act.act b) (act.hom b)))
      (fun z => by rw [LinearMap.comp_apply, lift_spec, lift_spec, Category.assoc, ← act.mul, mul_comm])]
    rfl
  map_zero' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [liftZ_val, LinearMap.zero_apply, ZeroMemClass.coe_zero]
    rw [lift_eq u hl _ _ 0 (fun z => by rw [LinearMap.zero_apply, ex_zero, act_zero, comp_one'])]
    rfl
  map_add' a b := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [liftZ_val, LinearMap.add_apply, Submodule.coe_add]
    rw [lift_eq u hl _ _ (lift u hl (act.act a) (act.hom a) + lift u hl (act.act b) (act.hom b))
      (fun z => by rw [LinearMap.add_apply, u.ex_add, lift_spec, lift_spec, act.add, comp_mul'])]
    rfl

@[simp] theorem ringAct_val (c : O) (x : u.Λ) :
    ((ringAct u hl act c x : u.Λ) : Fin P.g → ℂ) = lift u hl (act.act c) (act.hom c) x := rfl

end Ring

section Main

variable (u : HolUnif P.A P.L P.g)
  (hl : ∀ f : P.A ⟶ P.A, IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f)

theorem lift_pow_spec (θ : P.A ⟶ P.A) (hθ : IsMonHom θ) (k : ℕ) (z : Fin P.g → ℂ) :
    u.ex ((lift u hl θ hθ ^ k) z) = u.ex z ≫ (fun f : P.A ⟶ P.A => f ≫ θ)^[k] (𝟙 P.A) := by
  induction k with
  | zero => rw [pow_zero, Module.End.one_apply, Function.iterate_zero, id, Category.comp_id]
  | succ k ih => rw [pow_succ', Module.End.mul_apply, lift_spec, ih, Function.iterate_succ_apply', Category.assoc]

include u hl in
theorem main_of_unif (E : Type) [Field E] [NumberField E] (act : OAct (𝓞 E) P.A) (θ : P.A ⟶ P.A) (N n : ℕ)
    (hθ : IsMonHom θ) (hN : (fun f : P.A ⟶ P.A => f ≫ θ)^[N] (𝟙 P.A) = 𝟙 P.A)
    (hc : ∀ a, act.act a ≫ θ = θ ≫ act.act a) (hn : 0 < n) :
    ∃ (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (F : Λ →ₗ[𝓞 E] Λ) (ψ : Λ → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)),
      Module.Finite (𝓞 E) Λ ∧ Module.IsTorsionFree (𝓞 E) Λ ∧ F ^ N = 1 ∧ (∀ a b, ψ (a + b) = ψ a * ψ b) ∧
      (∀ (c : 𝓞 E) a, ψ (c • a) = ψ a ≫ act.act c) ∧ (∀ a, ψ a = 1 ↔ ∃ b, a = n • b) ∧
      (∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, q ^ n = 1 → ∃ a, ψ a = q) ∧ ∀ a, ψ (F a) = ψ a ≫ θ := by
  letI inst : Module (𝓞 E) u.Λ := Module.compHom u.Λ (ringAct u hl act)
  have hsmul : ∀ (c : 𝓞 E) (x : u.Λ), ((c • x : u.Λ) : Fin P.g → ℂ) = lift u hl (act.act c) (act.hom c) x :=
    fun _ _ => rfl

  have hcomm : ∀ c, (lift u hl θ hθ).comp (lift u hl (act.act c) (act.hom c)) =
      (lift u hl (act.act c) (act.hom c)).comp (lift u hl θ hθ) := fun c =>
    lift_unique u (act.act c ≫ θ) _ _
      (fun z => by rw [LinearMap.comp_apply, lift_spec, lift_spec, Category.assoc])
      (fun z => by rw [LinearMap.comp_apply, lift_spec, lift_spec, Category.assoc, hc])
  let F : u.Λ →ₗ[𝓞 E] u.Λ :=
    { toFun := liftZ u hl θ hθ
      map_add' := map_add _
      map_smul' := fun c x => Subtype.ext (by
        simp only [RingHom.id_apply, hsmul, liftZ_val]
        exact (LinearMap.congr_fun (hcomm c) x : _)) }
  have hFval : ∀ x : u.Λ, ((F x : u.Λ) : Fin P.g → ℂ) = lift u hl θ hθ x := fun _ => rfl
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  let ψ : u.Λ → (𝟙_ (Over (Sp ℂ)) ⟶ P.A) := fun a => u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ))
  have hψlift : ∀ (f : P.A ⟶ P.A) (hf : IsMonHom f) (a : u.Λ),
      u.ex ((n : ℂ)⁻¹ • lift u hl f hf a) = ψ a ≫ f := fun f hf a => by
    rw [← map_smul, lift_spec]
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  haveI hZ : Module.Finite ℤ u.Λ := ZLattice.module_finite ℝ u.Λ
  refine ⟨u.Λ, inferInstance, inst, F, ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) u.Λ
  · refine Module.IsTorsionFree.of_smul_eq_zero fun c x h => ?_
    by_cases hc0 : c = 0
    · exact Or.inl hc0
    right
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    have hm : Ideal.absNorm (Ideal.span {c}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc0
    have h1 : (Ideal.absNorm (Ideal.span {c}) : 𝓞 E) • x = 0 := by
      rw [← hr, mul_smul, h, smul_zero]
    rw [Nat.cast_smul_eq_nsmul] at h1
    have h2 := congrArg Subtype.val h1
    rw [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero, ← Nat.cast_smul_eq_nsmul ℂ] at h2
    exact Subtype.ext ((smul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr hm))
  · have hpow : lift u hl θ hθ ^ N = 1 := by
      rw [lift_unique u (𝟙 P.A) (lift u hl θ hθ ^ N) 1
        (fun z => by rw [lift_pow_spec, hN]) (fun z => by rw [Module.End.one_apply, Category.comp_id])]
    have hit : ∀ (k : ℕ) (x : u.Λ), (((F ^ k) x : u.Λ) : Fin P.g → ℂ) = (lift u hl θ hθ ^ k) x := by
      intro k
      induction k with
      | zero => intro x; rfl
      | succ k ih => intro x; rw [pow_succ', Module.End.mul_apply, hFval, ih, pow_succ', Module.End.mul_apply]
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [hit, hpow]; rfl
  · intro a b
    simp only [ψ, Submodule.coe_add, smul_add, u.ex_add]
  · intro c a
    simp only [ψ]
    rw [hsmul, hψlift]
  · intro a
    simp only [ψ]
    rw [u.ker]
    constructor
    · intro h
      refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
      rw [AddSubmonoidClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hn']
    · rintro ⟨b, rfl⟩
      rw [AddSubmonoidClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hn']
      exact b.2
  · intro q hq
    obtain ⟨z, rfl⟩ := u.ex_onto q
    have hz : (n : ℂ) • z ∈ u.Λ := by
      rw [← u.ker, Nat.cast_smul_eq_nsmul, ex_nsmul, hq]
    refine ⟨⟨_, hz⟩, ?_⟩
    simp only [ψ]
    rw [inv_smul_smul₀ hn']
  · intro a
    simp only [ψ]
    rw [hFval, hψlift]

end Main

end GlobalTheory.PeriodLattice

theorem GlobalTheory.periodLattice_of_finiteOrder : ∀ (E : Type) [Field E] [NumberField E] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) P.A) (θ : P.A ⟶ P.A) (N n : ℕ), IsMonHom θ → 0 < N → (fun f : P.A ⟶ P.A => f ≫ θ)^[N] (𝟙 P.A) = 𝟙 P.A → (∀ a, act.act a ≫ θ = θ ≫ act.act a) → 0 < n → ∃ (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (F : Λ →ₗ[𝓞 E] Λ) (ψ : Λ → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), Module.Finite (𝓞 E) Λ ∧ Module.IsTorsionFree (𝓞 E) Λ ∧ F ^ N = 1 ∧ (∀ a b, ψ (a + b) = ψ a * ψ b) ∧ (∀ (c : 𝓞 E) a, ψ (c • a) = ψ a ≫ act.act c) ∧ (∀ a, ψ a = 1 ↔ ∃ b, a = n • b) ∧ (∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, q ^ n = 1 → ∃ a, ψ a = q) ∧ ∀ a, ψ (F a) = ψ a ≫ θ := by
  intro E _ _ P act θ N n hθ _ hN hc hn
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, -, -, -, -, -, -, -, hl, -⟩ := GlobalTheory.thetaUnifAV_all P rig hrig
  exact GlobalTheory.PeriodLattice.main_of_unif u hl E act θ N n hθ hN hc hn

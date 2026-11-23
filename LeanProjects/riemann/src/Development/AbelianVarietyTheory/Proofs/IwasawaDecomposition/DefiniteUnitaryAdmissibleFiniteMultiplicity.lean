import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFiniteStatement

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU.admitted

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_fin_mul_inf (y : UA E n) : ∃ a ∈ finU E n, ∃ b ∈ infU E n, y = a * b := by
  let yi := GeneralLinearGroup.map (pInf E) y.1
  have hyi : yi.valᴴ * yi.val = 1 := by
    have hy : cT (conjAd E) y.1.val * 1 * y.1.val = 1 := y.2
    have h3 : (cT (conjAd E) y.1.val).map (pInf E) = yi.valᴴ := by
      ext1 i j
      rw [Matrix.conjTranspose_apply]
      exact (infEq E).symm_apply_apply _
    have h := congrArg (pInf E).mapMatrix hy
    rw [map_mul, map_mul, map_one, mul_one, RingHom.mapMatrix_apply, h3] at h
    exact h
  let b : UA E n := ⟨infGL E n yi, infGL_mem_UA yi hyi⟩
  have hb : b ∈ infU E n := MonoidHom.mem_ker.2 (pFin_infGL yi)
  have ha : b⁻¹ * y ∈ finU E n := by
    refine MonoidHom.mem_ker.2 ?_
    rw [map_mul, map_inv]
    have : cInf b = cInf y := pInf_infGL yi
    rw [this, inv_mul_cancel]
  refine ⟨b⁻¹ * y, ha, b, hb, ?_⟩
  rw [fin_mul_inf ha hb, mul_inv_cancel_left]

def X (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) := Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)

theorem RU_mem_X (φ : UA E n → ℂ) (x : infU E n) {ξ : UA E n → ℂ} (h : ξ ∈ X φ) : RU E n x ξ ∈ X φ := by
  have : X φ ≤ (X φ).comap (RU E n x) := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨x * k, (RU_RU _ _ _).symm⟩)
  exact this h

theorem self_mem_X (φ : UA E n → ℂ) : φ ∈ X φ :=
  Submodule.subset_span ⟨1, by show RU E n 1 φ = φ; rw [map_one]; rfl⟩

def rhoX (φ : UA E n → ℂ) (x : infU E n) : Module.End ℂ (X φ) :=
  (RU E n x).restrict fun _ h => RU_mem_X φ x h

theorem rhoX_mul (φ : UA E n → ℂ) (x y : infU E n) : rhoX φ (x * y) = rhoX φ x * rhoX φ y :=
  LinearMap.ext fun ξ => Subtype.ext (RU_RU (x : UA E n) y ξ.1).symm

def coef (φ : UA E n → ℂ) : Module.Dual ℂ (Module.End ℂ (X φ)) →ₗ[ℂ] (infU E n → ℂ) :=
  LinearMap.pi fun x => LinearMap.applyₗ (rhoX φ x)

def C (φ : UA E n → ℂ) : Submodule ℂ (infU E n → ℂ) := LinearMap.range (coef φ)

theorem mem_C (φ : UA E n → ℂ) (f : X φ →ₗ[ℂ] ℂ) (ξ : X φ) : (fun x : infU E n => f (rhoX φ x ξ)) ∈ C φ :=
  ⟨f ∘ₗ LinearMap.applyₗ ξ, rfl⟩

theorem C_right (φ : UA E n → ℂ) {c : infU E n → ℂ} (hc : c ∈ C φ) (y : infU E n) :
    (fun x => c (x * y)) ∈ C φ := by
  obtain ⟨B, rfl⟩ := hc
  refine ⟨B ∘ₗ LinearMap.mulRight ℂ (rhoX φ y), funext fun x => ?_⟩
  change B (rhoX φ x * rhoX φ y) = B (rhoX φ (x * y))
  rw [rhoX_mul]

def Y (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) :=
  ⨅ g : UA E n, (C φ).comap (LinearMap.funLeft ℂ ℂ fun x : infU E n => g * (x : UA E n))

theorem mem_Y {φ ψ : UA E n → ℂ} : ψ ∈ Y φ ↔ ∀ g : UA E n, (fun x : infU E n => ψ (g * x)) ∈ C φ := by
  simp only [Y, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem le_Y (π : AutSub E n) {φ : UA E n → ℂ} (hφ : φ ∈ π.V) (h0 : φ ≠ 0) : π.V ≤ Y φ := by
  have hφY : φ ∈ Y φ := mem_Y.2 fun g =>
    mem_C φ ((LinearMap.proj g) ∘ₗ (X φ).subtype) ⟨φ, self_mem_X φ⟩
  have hst : ∀ x, ∀ ψ ∈ π.V ⊓ Y φ, RU E n x ψ ∈ π.V ⊓ Y φ := by
    intro x ψ hψ
    refine ⟨π.isAut.stable x ψ hψ.1, mem_Y.2 fun g => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_fin_mul_inf x
    have e : (fun z : infU E n => RU E n (a * b) ψ (g * z)) = fun z => ψ ((g * a) * ((z * ⟨b, hb⟩ : infU E n) : UA E n)) := by
      funext z
      rw [RU_apply, Subgroup.coe_mul, Subgroup.coe_mk, ← mul_assoc, mul_assoc g, ← fin_mul_inf ha z.2, ← mul_assoc, mul_assoc (g * a)]
    rw [e]
    exact C_right φ (mem_Y.1 hψ.2 (g * a)) ⟨b, hb⟩
  rcases π.isAut.irred (π.V ⊓ Y φ) inf_le_left hst with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (⟨hφ, hφY⟩ : φ ∈ π.V ⊓ Y φ))) h0
  · rw [← h]
    exact inf_le_right

theorem eq_zero_of_vanish {K : Subgroup (finU E n)} {S : Finset (UA E n)}
    (hS : ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ x ∈ infU E n, ∃ k ∈ K, g = γ * s * x * (k : UA E n))
    {f : UA E n → ℂ} (hl : ∀ γ ∈ ratU E n, ∀ g, f (γ * g) = f g) (hK : ∀ k ∈ K, RU E n k f = f)
    (h0 : ∀ s ∈ S, ∀ x ∈ infU E n, f (s * x) = 0) : f = 0 := by
  funext g
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
  rw [mul_assoc, mul_assoc, hl γ hγ, ← mul_assoc]
  have := congrFun (hK k hk) (s * x)
  rw [RU_apply] at this
  rw [this, h0 s hs x hx]
  rfl

theorem exists_ne_zero (π : AutSub E n) : ∃ φ ∈ π.V, φ ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot π.isAut.ne_bot

theorem finiteDimensional_fixed (π : AutSub E n) (K : Subgroup (finU E n)) (hK : IsOpen (K : Set (finU E n))) :
    FiniteDimensional ℂ (fixed (π.rep.comp (finU E n).subtype) K) := by
  obtain ⟨φ, hφ, h0⟩ := exists_ne_zero π
  have : FiniteDimensional ℂ (X φ) := (π.isAut.aut φ hφ).kfin
  have : FiniteDimensional ℂ (C φ) := LinearMap.finiteDimensional_range _
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n K hK
  let L : fixed (π.rep.comp (finU E n).subtype) K →ₗ[ℂ] (S → C φ) :=
    LinearMap.pi fun s => LinearMap.codRestrict (C φ)
      ((LinearMap.funLeft ℂ ℂ fun x : infU E n => (s : UA E n) * x) ∘ₗ π.V.subtype ∘ₗ (fixed _ K).subtype)
      (fun ψ => mem_Y.1 (le_Y π hφ h0 ψ.1.2) s)
  refine Module.Finite.of_injective L (LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun ψ hψ => ?_))
  have hK' : ∀ k ∈ K, RU E n k ψ.1.1 = ψ.1.1 := fun k hk => by
    have e : (π.rep.comp (finU E n).subtype) k ψ.1 = (((1 : K →* ℂˣ) ⟨k, hk⟩ : ℂˣ) : ℂ) • ψ.1 := ψ.2 ⟨k, hk⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul] at e
    exact congrArg Subtype.val e
  have hf := eq_zero_of_vanish hS (π.isAut.aut _ ψ.1.2).left hK' fun s hs x hx =>
    congrFun (congrArg Subtype.val (congrFun hψ ⟨s, hs⟩)) ⟨x, hx⟩
  exact Subtype.ext (Subtype.ext hf)

def stab (φ : UA E n → ℂ) : Subgroup (finU E n) where
  carrier := {k | RU E n k φ = φ}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Subgroup.coe_mul, ← RU_RU, hb, ha]
  one_mem' := by
    show RU E n 1 φ = φ
    rw [map_one]
    rfl
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [RU_RU, InvMemClass.coe_inv, inv_mul_cancel, map_one]
    rfl

theorem finiteDimensional_hom (π : AutSub E n) : FiniteDimensional ℂ (π.rep.IntertwiningMap (autRep E n)) := by
  obtain ⟨φ, hφ, h0⟩ := exists_ne_zero π
  have : FiniteDimensional ℂ (X φ) := (π.isAut.aut φ hφ).kfin
  have : FiniteDimensional ℂ (C φ) := LinearMap.finiteDimensional_range _
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n (stab φ) (π.isAut.aut φ hφ).level
  let φV : π.V := ⟨φ, hφ⟩
  have hXV : X φ ≤ π.V := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact π.isAut.stable _ φ hφ)
  have hmem : ∀ (T : π.rep.IntertwiningMap (autRep E n)) (s : UA E n),
      (fun x : infU E n => (T φV).1 (s * x)) ∈ C φ := by
    intro T s
    have e : (fun x : infU E n => (T φV).1 (s * x)) = fun x => ((LinearMap.proj s) ∘ₗ (autU E n).subtype ∘ₗ
        T.toLinearMap ∘ₗ Submodule.inclusion hXV) (rhoX φ x ⟨φ, self_mem_X φ⟩) :=
      funext fun x => (congrFun (congrArg Subtype.val (LinearMap.congr_fun (T.isIntertwining' (x : UA E n)) φV)) s).symm
    rw [e]
    exact mem_C φ _ _
  let Φ : π.rep.IntertwiningMap (autRep E n) →ₗ[ℂ] (S → C φ) :=
    { toFun := fun T s => ⟨fun x : infU E n => (T φV).1 ((s : UA E n) * x), hmem T s⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective Φ (LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun T hT => ?_))
  have hK : ∀ k ∈ stab φ, RU E n k (T φV).1 = (T φV).1 := fun k hk => by
    have e : T (π.rep k φV) = autRep E n k (T φV) := LinearMap.congr_fun (T.isIntertwining' (k : UA E n)) φV
    rw [show π.rep k φV = φV from Subtype.ext hk] at e
    exact (congrArg Subtype.val e).symm
  have hTφ : T φV = 0 := Subtype.ext (eq_zero_of_vanish hS (mem_autU.1 (T φV).2).left hK fun s hs x hx =>
    congrFun (congrArg Subtype.val (congrFun hT ⟨s, hs⟩)) ⟨x, hx⟩)
  let W : Submodule ℂ (UA E n → ℂ) := (LinearMap.ker T.toLinearMap).map π.V.subtype
  have hst : ∀ x, ∀ ψ ∈ W, RU E n x ψ ∈ W := by
    rintro x _ ⟨ψ', hψ', rfl⟩
    refine ⟨π.rep x ψ', ?_, rfl⟩
    have h1 : T ψ' = 0 := hψ'
    change T (π.rep x ψ') = 0
    have h2 : T (π.rep x ψ') = autRep E n x (T ψ') := LinearMap.congr_fun (T.isIntertwining' x) ψ'
    rw [h2, h1, map_zero]
  rcases π.isAut.irred W (Submodule.map_subtype_le _ _) hst with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (⟨φV, hTφ, rfl⟩ : φ ∈ W))) h0
  · refine DFunLike.ext _ _ fun ψ => ?_
    obtain ⟨ψ', hψ', e⟩ : ψ.1 ∈ W := h.symm ▸ ψ.2
    rw [← Subtype.ext e]
    exact hψ'

theorem admissible_finiteMult : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n),
    (∀ K : Subgroup (finU E n), IsOpen (K : Set (finU E n)) →
      FiniteDimensional ℂ (fixed (π.rep.comp (finU E n).subtype) K)) ∧
    FiniteDimensional ℂ (π.rep.IntertwiningMap (autRep E n)) :=
  fun _ _ _ _ _ π => ⟨fun K hK => finiteDimensional_fixed π K hK, finiteDimensional_hom π⟩

end GlobalTheory.DefU.admitted

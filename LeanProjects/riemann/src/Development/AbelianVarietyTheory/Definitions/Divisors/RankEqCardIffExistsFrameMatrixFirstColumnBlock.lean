import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise

noncomputable section
namespace GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def apow (x : kˣ) (z : ℂ) : ℂ := ((nabs k x : ℝ) : ℂ) ^ z

theorem apow_mul (x y : kˣ) (z : ℂ) : apow (x * y) z = apow x z * apow y z := by
  simp only [apow, nabs_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (nabs_pos x).le (nabs_pos y).le z

@[simp] theorem apow_one (z : ℂ) : apow (1 : kˣ) z = 1 := by simp [apow, nabs_one]

theorem apow_add (x : kˣ) (z w : ℂ) : apow x (z + w) = apow x z * apow x w :=
  Complex.cpow_add _ _ (by exact_mod_cast (nabs_pos x).ne')

@[simp] theorem apow_zero (x : kˣ) : apow x 0 = 1 := by simp [apow]

theorem apow_ne_zero (x : kˣ) (z : ℂ) : apow x z ≠ 0 :=
  left_ne_zero_of_mul_eq_one (b := apow x (-z)) (by rw [← apow_add]; simp)

theorem apow_neg (x : kˣ) (z : ℂ) : apow x (-z) = (apow x z)⁻¹ := Complex.cpow_neg _ _

theorem apow_inv (x : kˣ) (z : ℂ) : apow x⁻¹ z = apow x (-z) := by
  rw [apow_neg]; exact eq_inv_of_mul_eq_one_left (by rw [← apow_mul]; simp)

theorem nabs_of_valuation_eq_one {x : kˣ} (hx : valuation k (x : k) = 1) : nabs k x = 1 := by
  borelize k
  have h1 := nabs_le_one x hx.le
  have h2 := nabs_le_one x⁻¹ (by simp [hx])
  have h3 : nabs k x * nabs k x⁻¹ = 1 := by rw [← nabs_mul]; simp [nabs_one]
  nlinarith [nabs_pos x, nabs_pos x⁻¹]

theorem apow_of_valuation_eq_one {x : kˣ} (hx : valuation k (x : k) = 1) (z : ℂ) : apow x z = 1 := by
  simp [apow, nabs_of_valuation_eq_one hx]

def IsUnif (ϖ : kˣ) : Prop := valuation k (ϖ : k) = uniformizer k

def unitCong (c : kˣ) : Subgroup kˣ where
  carrier := {x | valuation k (x : k) = 1 ∧ valuation k ((x : k) - 1) ≤ valuation k (c : k)}
  one_mem' := by simp
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by simp [hx, hy], ?_⟩
    rw [show ((x * y : kˣ) : k) - 1 = x * (y - 1) + (x - 1) by push_cast; ring]
    exact Valuation.map_add_le _ (by rwa [map_mul, hx, one_mul]) hx'
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨by simp [hx], ?_⟩
    rw [show ((x⁻¹ : kˣ) : k) - 1 = -((x : k)⁻¹ * (x - 1)) by simp [mul_sub]]
    rwa [Valuation.map_neg, map_mul, map_inv₀, hx, inv_one, one_mul]

def CondLE (ϖ : kˣ) (e : ℕ) (χ : kˣ →* ℂˣ) : Prop := ∀ x ∈ unitCong (ϖ ^ e), χ x = 1

theorem CondLE.div {ϖ : kˣ} {e : ℕ} {α β : kˣ →* ℂˣ} (hα : CondLE ϖ e α) (hβ : CondLE ϖ e β) :
    CondLE ϖ e (α / β) := fun x hx => by simp [hα x hx, hβ x hx]

theorem CondLE.mul {ϖ : kˣ} {e : ℕ} {α β : kˣ →* ℂˣ} (hα : CondLE ϖ e α) (hβ : CondLE ϖ e β) :
    CondLE ϖ e (α * β) := fun x hx => by simp [hα x hx, hβ x hx]

theorem condLE_of_isUnram (ϖ : kˣ) (e : ℕ) {χ : kˣ →* ℂˣ} (h : IsUnram χ) : CondLE ϖ e χ :=
  fun x hx => h x hx.1

structure IsRightTranslationIsometric (ϖ : kˣ) (ψ : AddChar k Circle) (α β : kˣ →* ℂˣ) (e : ℕ) : Prop where
  unif : IsUnif ϖ
  cond : HasConductor ψ 1
  ram : ¬ IsUnram (α / β)
  unitary : ∀ x, ‖((α / β) x : ℂ)‖ = 1
  one_le : 1 ≤ e
  condα : CondLE ϖ e α
  condβ : CondLE ϖ e β

theorem IsRightTranslationIsometric.condν {ϖ : kˣ} {ψ : AddChar k Circle} {α β : kˣ →* ℂˣ} {e : ℕ} (h : IsRightTranslationIsometric ϖ ψ α β e) :
    CondLE ϖ e (α / β) := h.condα.div h.condβ

structure IsCoeffRing (ϖ : kˣ) (ψ : AddChar k Circle) (α β : kˣ →* ℂˣ) (e : ℕ) (R : Subring ℂ) : Prop where
  inv_card : ((resCard k : ℂ))⁻¹ ∈ R
  psi : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ R
  units : ∀ x : kˣ, valuation k (x : k) = 1 → (α x : ℂ) ∈ R ∧ (β x : ℂ) ∈ R ∧ ((α / β) x : ℂ) ∈ R
  unif : ((α / β) ϖ : ℂ) ∈ R ∧ ((α / β) ϖ⁻¹ : ℂ) ∈ R

example (ϖ : kˣ) (ψ : AddChar k Circle) (α β : kˣ →* ℂˣ) (e : ℕ) : IsCoeffRing ϖ ψ α β e ⊤ :=
  ⟨trivial, fun _ _ => trivial, fun _ _ => ⟨trivial, trivial, trivial⟩, trivial, trivial⟩

theorem IsRightTranslationIsometric.inv {ϖ : kˣ} {ψ : AddChar k Circle} {α β : kˣ →* ℂˣ} {e : ℕ} (h : IsRightTranslationIsometric ϖ ψ α β e) :
    IsRightTranslationIsometric ϖ ψ⁻¹ α β e :=
  { h with cond := fun x => by simpa only [AddChar.inv_apply', inv_eq_one] using h.cond x }

theorem IsCoeffRing.inv {ϖ : kˣ} {ψ : AddChar k Circle} {α β : kˣ →* ℂˣ} {e : ℕ} {R : Subring ℂ}
    (h : IsCoeffRing ϖ ψ α β e R) : IsCoeffRing ϖ ψ⁻¹ α β e R :=
  { h with psi := fun x hx => h.psi (-x) (by rwa [mul_neg, Valuation.map_neg]) }

theorem exists_isUnif : ∃ ϖ : kˣ, IsUnif ϖ := by
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (uniformizer k)
  exact ⟨Units.mk0 t (by rintro rfl; exact ValuativeRel.uniformizer_ne_zero (R := k) (by simpa using ht.symm)), ht⟩

theorem IsUnif.mem {ϖ : kˣ} (hϖ : IsUnif ϖ) : (ϖ : k) ∈ 𝒪[k] :=
  show valuation k (ϖ : k) ≤ 1 from hϖ ▸ uniformizer_lt_one.le

theorem IsUnif.maximalIdeal_eq {ϖ : kˣ} (hϖ : IsUnif ϖ) :
    IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {(⟨ϖ, hϖ.mem⟩ : 𝒪[k])} := by
  ext y
  rw [Ideal.mem_span_singleton, ← (Valuation.integer.integers (valuation k)).le_iff_dvd,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  show _ ↔ valuation k (y : k) ≤ valuation k (ϖ : k)
  rw [hϖ, le_uniformizer_iff]

theorem IsUnif.irreducible {ϖ : kˣ} (hϖ : IsUnif ϖ) : Irreducible (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ (fun h => ϖ.ne_zero (congrArg Subtype.val h))
    hϖ.maximalIdeal_eq

theorem exists_ramified {ϖ : kˣ} (hϖ : IsUnif ϖ) :
    ∃ ν : kˣ →* ℂˣ, ¬ IsUnram ν ∧ CondLE ϖ 2 ν ∧ ∀ x, ‖(ν x : ℂ)‖ = 1 := by
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have h1 : valuation k (1 + (ϖ : k)) = 1 := (valuation k).map_one_add_of_lt hlt
  let u : kˣ := Units.mk0 (1 + ϖ) (by intro h; simp [h] at h1)
  let Q := kˣ ⧸ unitCong (ϖ ^ 2)
  have hne : (Additive.ofMul (QuotientGroup.mk u : Q)) ≠ 0 := by
    intro h
    have h2 := ((QuotientGroup.eq_one_iff u).1 h).2
    simp only [u, Units.val_mk0, add_sub_cancel_left, Units.val_pow_eq_pow_val, map_pow] at h2
    have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
    exact absurd h2 (not_le.2 (by rw [pow_two]; exact mul_lt_of_lt_one_right h0 hlt))
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  let c' : Additive Q →+ AddCircle (1 : ℚ) := c
  let f : kˣ →* ℂˣ :=
    { toFun := fun x => Circle.toUnits (AddCircle.toCircle (ratCircle (c' (Additive.ofMul (QuotientGroup.mk x)))))
      map_one' := by simp
      map_mul' := fun x y => by
        rw [QuotientGroup.mk_mul, ofMul_mul, map_add, map_add, AddCircle.toCircle_add, map_mul] }
  refine ⟨f, fun h => hc (ratCircle_eq_zero _ (AddCircle.injective_toCircle one_ne_zero ?_)), fun x hx => ?_,
    fun x => Circle.norm_coe _⟩
  · have := congrArg Units.val (h u h1)
    rw [AddCircle.toCircle_zero]
    exact Circle.ext this
  · show Circle.toUnits (AddCircle.toCircle (ratCircle (c' (Additive.ofMul (QuotientGroup.mk x))))) = 1
    rw [(QuotientGroup.eq_one_iff x).2 hx]; simp

theorem exists_localSetting : ∃ (ϖ : kˣ) (ψ : AddChar k Circle) (α : kˣ →* ℂˣ), IsRightTranslationIsometric ϖ ψ α 1 2 := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
  obtain ⟨ψ, hψ⟩ := exists_hasConductor (k := k)
  obtain ⟨ν, h1, h2, h3⟩ := exists_ramified hϖ
  exact ⟨ϖ, ψ, ν, hϖ, hψ, by simpa using h1, by simpa using h3, one_le_two, h2, fun _ _ => rfl⟩

section Models
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

abbrev gdet (g : GL D k) : kˣ := Matrix.GeneralLinearGroup.det g

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def invT : GL D k →* GL D k where
  toFun h := ⟨(h⁻¹).valᵀ, h.valᵀ, by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by simp [Matrix.mul_inv_rev])

section
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem invT_val (h : GL D k) : (invT h).val = (h⁻¹).valᵀ := rfl

theorem invT_inv_val (h : GL D k) : ((invT h)⁻¹).val = h.valᵀ := rfl

@[simp] theorem invT_invT (h : GL D k) : invT (invT h) = h := Units.ext rfl

theorem gdet_mul (g h : GL D k) : gdet (g * h) = gdet g * gdet h := map_mul _ _ _

theorem gdet_invT (h : GL D k) : gdet (invT h) = (gdet h)⁻¹ := by
  rw [← map_inv]; exact Units.ext (det_transpose _)
end

theorem valuation_gdet_of_mem_KO {g : GL D k} (hg : g ∈ KO k D) : valuation k (gdet g : k) = 1 := by
  obtain ⟨u, rfl⟩ := hg
  have h : ((gdet (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) : kˣ) : k) = algebraMap 𝒪[k] k u.val.det :=
    (RingHom.map_det _ _).symm
  rw [h]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)

theorem invT_mem_KO {g : GL D k} (hg : g ∈ KO k D) : invT g ∈ KO k D := by
  rw [mem_KO_iff] at hg ⊢
  exact ⟨fun i j => hg.2 j i, fun i j => hg.1 j i⟩

def omA (ν β : kˣ →* ℂˣ) (g : GL A k) (h : GL D k) (Φ : Matrix A D k → ℂ) : Matrix A D k → ℂ := fun X =>
  (((ν (gdet g))⁻¹ : ℂˣ) : ℂ) * β (gdet h) * apow (gdet g) (-(Fintype.card D : ℂ) / 2) *
    apow (gdet h) (-(Fintype.card A : ℂ) / 2) * Φ ((g⁻¹).val * X * (invT h).val)

def omB (ν α : kˣ →* ℂˣ) (g : GL A' k) (h : GL D k) (Ψ : Matrix A' D k → ℂ) : Matrix A' D k → ℂ := fun Y =>
  (ν (gdet g) : ℂ) * α (gdet h) * apow (gdet g) ((Fintype.card D : ℂ) / 2) *
    apow (gdet h) ((Fintype.card A' : ℂ) / 2) * Ψ (g.valᵀ * Y * h.val)

def repA (ν β : kˣ →* ℂˣ) : Representation ℂ (GL A k × GL D k) (Matrix A D k → ℂ) where
  toFun x :=
    { toFun := omA ν β x.1 x.2
      map_add' := fun Φ Φ' => by funext X; simp [omA, mul_add]
      map_smul' := fun c Φ => by funext X; simp only [omA, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_one' := by ext Φ X; simp [omA]
  map_mul' x y := by
    ext Φ X
    simp only [omA, Prod.fst_mul, Prod.snd_mul, map_mul, apow_mul, _root_.mul_inv_rev, Units.val_mul,
      Matrix.mul_assoc, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
    ring

def repB (ν α : kˣ →* ℂˣ) : Representation ℂ (GL A' k × GL D k) (Matrix A' D k → ℂ) where
  toFun x :=
    { toFun := omB ν α x.1 x.2
      map_add' := fun Φ Φ' => by funext X; simp [omB, mul_add]
      map_smul' := fun c Φ => by funext X; simp only [omB, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_one' := by ext Φ X; simp [omB]
  map_mul' x y := by
    ext Φ X
    simp only [omB, Prod.fst_mul, Prod.snd_mul, map_mul, apow_mul, Units.val_mul, transpose_mul,
      Matrix.mul_assoc, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
    ring

theorem omA_mul (ν β : kˣ →* ℂˣ) (g g' : GL A k) (h h' : GL D k) (Φ : Matrix A D k → ℂ) :
    omA ν β (g * g') (h * h') Φ = omA ν β g h (omA ν β g' h' Φ) :=
  LinearMap.congr_fun ((repA ν β).map_mul (g, h) (g', h')) Φ

theorem omB_mul (ν α : kˣ →* ℂˣ) (g g' : GL A' k) (h h' : GL D k) (Ψ : Matrix A' D k → ℂ) :
    omB ν α (g * g') (h * h') Ψ = omB ν α g h (omB ν α g' h' Ψ) :=
  LinearMap.congr_fun ((repB ν α).map_mul (g, h) (g', h')) Ψ

theorem comp_mul_mem_SB (g : GL A k) (h : GL D k) {Φ : Matrix A D k → ℂ} (hΦ : Φ ∈ SB (Matrix A D k)) :
    (fun X => Φ (g.val * X * h.val)) ∈ SB (Matrix A D k) := by
  have := (SB (Matrix A D k)).smul_mem (om 1 h g⁻¹ (fun _ => 1) 0)⁻¹ (om_mem_SB 1 h g⁻¹ hΦ)
  convert this using 1
  funext X
  have h1 := fun (x : kˣ) (r : ℝ) => (Real.rpow_pos_of_pos (nabs_pos x) r).ne'
  simp only [om, Pi.smul_apply, smul_eq_mul, inv_inv, mul_one]
  rw [inv_mul_cancel_left₀]
  simp only [ne_eq, mul_eq_zero, Units.ne_zero, Complex.ofReal_eq_zero, h1, or_self, not_false_eq_true]

theorem omA_mem_SB (ν β : kˣ →* ℂˣ) (g : GL A k) (h : GL D k) {Φ : Matrix A D k → ℂ}
    (hΦ : Φ ∈ SB (Matrix A D k)) : omA ν β g h Φ ∈ SB (Matrix A D k) :=
  (SB (Matrix A D k)).smul_mem _ (comp_mul_mem_SB g⁻¹ (invT h) hΦ)

theorem omB_mem_SB (ν α : kˣ →* ℂˣ) (g : GL A' k) (h : GL D k) {Ψ : Matrix A' D k → ℂ}
    (hΨ : Ψ ∈ SB (Matrix A' D k)) : omB ν α g h Ψ ∈ SB (Matrix A' D k) :=
  (SB (Matrix A' D k)).smul_mem _ (comp_mul_mem_SB (invT g)⁻¹ h hΨ)

section
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def X0 (σ : A ⊕ A' ≃ D) : Matrix A D k := Matrix.of fun i j => if σ (Sum.inl i) = j then 1 else 0

variable (k) in

def Y0 (σ : A ⊕ A' ≃ D) : Matrix A' D k := Matrix.of fun i j => if σ (Sum.inr i) = j then 1 else 0

def stdSplit {a a' d₁ d₂ : ℕ} (h : a + a' = d₁ + d₂) : Fin a ⊕ Fin a' ≃ Fin d₁ ⊕ Fin d₂ :=
  finSumFinEquiv.trans ((finCongr h).trans finSumFinEquiv.symm)

omit [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] in

theorem frameMatrixFirstColumnBlock_mul_apply {B : Type*} (σ : A ⊕ A' ≃ D) (M : Matrix D B k) (i : A) (j : B) :
    (X0 k σ * M) i j = M (σ (Sum.inl i)) j := by simp [X0, Matrix.mul_apply]

omit [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] in

theorem frameMatrixSecondColumnBlock_mul_apply {B : Type*} (σ : A ⊕ A' ≃ D) (M : Matrix D B k) (i : A') (j : B) :
    (Y0 k σ * M) i j = M (σ (Sum.inr i)) j := by simp [Y0, Matrix.mul_apply]

omit [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] in

theorem frameSecondBlock_mul_frameFirstBlock_transpose_eq_zero (σ : A ⊕ A' ≃ D) (h : GL D k) :
    (Y0 k σ * h.val) * (X0 k σ * (invT h).val)ᵀ = 0 := by
  rw [transpose_mul, invT_val, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, Units.mul_inv,
    Matrix.one_mul]
  ext i j; simp [frameMatrixSecondColumnBlock_mul_apply, X0]

omit [DecidableEq A] [DecidableEq A'] in

theorem rank_eq_card_iff_exists_frameMatrixFirstColumnBlock (σ : A ⊕ A' ≃ D) (X : Matrix A D k) :
    X.rank = Fintype.card A ↔ ∃ h : GL D k, X = X0 k σ * (invT h).val := by
  have hli : X.rank = Fintype.card A ↔ LinearIndependent k X.row := by
    rw [rank_eq_finrank_span_row, linearIndependent_iff_card_eq_finrank_span, eq_comm]; rfl
  rw [hli]
  constructor
  · intro hX
    obtain ⟨U, hU⟩ := (Submodule.span k (Set.range X.row)).exists_isCompl
    have hf : Module.finrank k U = Fintype.card A' := by
      have h1 := Submodule.finrank_add_eq_of_isCompl hU
      rw [finrank_span_eq_card hX, Module.finrank_fintype_fun_eq_card, ← Fintype.card_congr σ,
        Fintype.card_sum] at h1
      omega
    let b := (Module.finBasisOfFinrankEq k U hf).reindex (Fintype.equivFin A').symm
    have hb : LinearIndependent k (U.subtype ∘ b) := b.linearIndependent.map' _ U.ker_subtype
    have hs := (hX.sum_type hb (hU.disjoint.mono_right (Submodule.span_le.2 (by
      rintro _ ⟨i, rfl⟩; exact (b i).2)))).comp σ.symm σ.symm.injective
    obtain ⟨B, hB⟩ := (Matrix.linearIndependent_rows_iff_isUnit
      (A := Matrix.of (Sum.elim X.row (U.subtype ∘ b) ∘ σ.symm))).1 hs
    refine ⟨invT B, ?_⟩
    ext i j
    simp [frameMatrixFirstColumnBlock_mul_apply, hB]
  · rintro ⟨h, rfl⟩
    have := (Matrix.linearIndependent_rows_iff_isUnit.2 (invT h).isUnit).comp (σ ∘ Sum.inl)
      (σ.injective.comp Sum.inl_injective)
    convert this using 1
    funext i j
    exact frameMatrixFirstColumnBlock_mul_apply σ _ i j
end
end Models

section Lattices
variable {A D : Type*}

theorem mem_smul_lat (c : kˣ) (Λ : Submodule 𝒪[k] (D → k)) (x : D → k) : x ∈ c • Λ ↔ c⁻¹ • x ∈ Λ := by
  refine (Submodule.mem_smul_pointwise_iff_exists x c Λ).trans ?_
  exact ⟨by rintro ⟨y, hy, rfl⟩; simpa using hy, fun h => ⟨_, h, by simp⟩⟩

variable (A) in

def matLat (Λ : Submodule 𝒪[k] (D → k)) : Submodule 𝒪[k] (Matrix A D k) where
  carrier := {X | ∀ i, X.row i ∈ Λ}
  add_mem' hX hY i := Λ.add_mem (hX i) (hY i)
  zero_mem' _ := Λ.zero_mem
  smul_mem' c _ hX i := Λ.smul_mem c (hX i)

theorem mem_matLat {Λ : Submodule 𝒪[k] (D → k)} {X : Matrix A D k} : X ∈ matLat A Λ ↔ ∀ i, X.row i ∈ Λ := Iff.rfl

def diagLat (c : D → kˣ) : Submodule 𝒪[k] (D → k) where
  carrier := {x | ∀ j, valuation k (x j) ≤ valuation k (c j : k)}
  add_mem' hx hy j := Valuation.map_add_le _ (hx j) (hy j)
  zero_mem' j := by simp
  smul_mem' r x hx j := by
    show valuation k ((r : k) * x j) ≤ _
    rw [map_mul]; exact (mul_le_of_le_one_left' r.2).trans (hx j)

theorem mem_diagLat {c : D → kˣ} {x : D → k} :
    x ∈ diagLat c ↔ ∀ j, valuation k (x j) ≤ valuation k (c j : k) := Iff.rfl

variable (k D) in

def stdLat : Submodule 𝒪[k] (D → k) := diagLat 1

theorem mem_stdLat {x : D → k} : x ∈ stdLat k D ↔ ∀ j, x j ∈ 𝒪[k] := by
  simp [stdLat, mem_diagLat, Valuation.mem_integer_iff]

theorem mem_matLat_stdLat {X : Matrix A D k} : X ∈ matLat A (stdLat k D) ↔ ∀ i j, X i j ∈ 𝒪[k] :=
  forall_congr' fun _ => mem_stdLat

theorem smul_diagLat (u : kˣ) (c : D → kˣ) : u • diagLat c = diagLat fun j => u * c j := by
  ext x
  rw [mem_smul_lat, mem_diagLat, mem_diagLat]
  refine forall_congr' fun j => ?_
  have h0 : 0 < valuation k (u : k) := zero_lt_iff.2 (by simp)
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, Units.val_mul]
  exact inv_mul_le_iff₀ h0

variable [Fintype D]

instance isLattice_diagLat (c : D → kˣ) : Submodule.IsLattice k (diagLat c) := by
  classical
  have hmem : ∀ j, (Pi.single j (c j : k) : D → k) ∈ diagLat c := fun j l => by
    by_cases h : l = j
    · subst h; simp
    · simp [h]
  have hx : ∀ x : D → k, x = ∑ j, (x j / c j) • (Pi.single j (c j : k) : D → k) := fun x => by
    funext l; simp [Finset.sum_apply, Pi.single_apply]
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_def.2 ⟨Set.range fun j => (Pi.single j (c j : k) : D → k), Set.finite_range _, le_antisymm ?_ ?_⟩
    · exact Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hmem j)
    · intro x h
      rw [hx x]
      refine Submodule.sum_mem _ fun j _ => ?_
      have h0 : 0 < valuation k (c j : k) := zero_lt_iff.2 (by simp)
      have h1 : x j / c j ∈ 𝒪[k] := by
        rw [Valuation.mem_integer_iff, map_div₀]; exact (div_le_one₀ h0).2 (h j)
      exact Submodule.smul_mem _ (⟨_, h1⟩ : 𝒪[k]) (Submodule.subset_span ⟨j, rfl⟩)
  · rw [eq_top_iff]
    intro x _
    rw [hx x]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hmem j))

instance isLattice_stdLat : Submodule.IsLattice k (stdLat k D) := isLattice_diagLat 1

def dualLat (Λ : Submodule 𝒪[k] (D → k)) : Submodule 𝒪[k] (D → k) :=
  LinearMap.BilinForm.dualSubmodule (dotProductBilin k k) Λ

theorem mem_dualLat {Λ : Submodule 𝒪[k] (D → k)} {x : D → k} : x ∈ dualLat Λ ↔ ∀ y ∈ Λ, x ⬝ᵥ y ∈ 𝒪[k] := by
  refine forall₂_congr fun y _ => ?_
  rw [Submodule.mem_one]
  exact ⟨by rintro ⟨r, hr⟩; exact (show (r : k) = x ⬝ᵥ y from hr) ▸ r.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

theorem dualLat_diagLat (c : D → kˣ) : dualLat (diagLat c) = diagLat fun j => (c j)⁻¹ := by
  classical
  have h0 : ∀ j, 0 < valuation k (c j : k) := fun j => zero_lt_iff.2 (by simp)
  ext x
  rw [mem_dualLat, mem_diagLat]
  simp only [Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · intro h j
    have := h (Pi.single j (c j : k)) fun l => by
      by_cases h : l = j
      · subst h; simp
      · simp [h]
    rw [dotProduct_single, Valuation.mem_integer_iff, map_mul] at this
    rw [← one_mul (valuation k (c j : k))⁻¹]; exact (le_mul_inv_iff₀ (h0 j)).2 this
  · intro h y hy
    refine Subring.sum_mem _ fun j _ => ?_
    rw [Valuation.mem_integer_iff, map_mul]
    exact (mul_le_mul' (h j) (hy j)).trans (inv_mul_cancel₀ (h0 j).ne').le

def IsPrimFrame [Fintype A] (Λ : Submodule 𝒪[k] (D → k)) (X : Matrix A D k) : Prop :=
  X.rank = Fintype.card A ∧ X ∈ matLat A Λ ∧
    Submodule.span 𝒪[k] (Set.range X.row) = (Submodule.span k (Set.range X.row)).restrictScalars 𝒪[k] ⊓ Λ

theorem isPrimitiveFrame_standardBasis [Fintype A] [DecidableEq D] {A' : Type*} [Fintype A'] (σ : A ⊕ A' ≃ D) :
    IsPrimFrame (stdLat k D) (X0 k σ) := by
  have hm : X0 k σ ∈ matLat A (stdLat k D) := mem_matLat_stdLat.2 fun i j => by
    simp only [X0, of_apply]; split_ifs <;> simp
  refine ⟨(rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ _).2 ⟨1, by simp⟩, hm, le_antisymm ?_ ?_⟩
  · exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ⟨Submodule.subset_span ⟨i, rfl⟩, hm i⟩)
  · rintro x ⟨hx, hx'⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hx
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : c i ∈ 𝒪[k] := by
      classical
      simpa [X0, Finset.sum_apply, Matrix.row] using mem_stdLat.1 hx' (σ (Sum.inl i))
    exact Submodule.smul_mem _ (⟨_, h1⟩ : 𝒪[k]) (Submodule.subset_span ⟨i, rfl⟩)

variable [DecidableEq D]

def glLat (Λ : Submodule 𝒪[k] (D → k)) : Subgroup (GL D k) where
  carrier := {h | ∀ x, x ᵥ* h.val ∈ Λ ↔ x ∈ Λ}
  one_mem' x := by simp
  mul_mem' {g h} hg hh x := by rw [Units.val_mul, ← vecMul_vecMul, hh, hg]
  inv_mem' {h} hh x := by rw [← hh, vecMul_vecMul, Units.inv_mul, vecMul_one]

theorem mem_glLat {Λ : Submodule 𝒪[k] (D → k)} {h : GL D k} : h ∈ glLat Λ ↔ ∀ x, x ᵥ* h.val ∈ Λ ↔ x ∈ Λ := Iff.rfl

theorem mem_glLat_iff_image {Λ : Submodule 𝒪[k] (D → k)} {h : GL D k} :
    h ∈ glLat Λ ↔ (fun x => x ᵥ* h.val) '' Λ = Λ := by
  constructor
  · intro hh
    ext y
    exact ⟨by rintro ⟨x, hx, rfl⟩; exact (hh x).2 hx, fun hy => ⟨y ᵥ* (h⁻¹).val, ((glLat Λ).inv_mem hh y).2 hy, by
      simp only [vecMul_vecMul, Units.inv_mul, vecMul_one]⟩⟩
  · intro hh x
    refine ⟨fun hx => ?_, fun hx => hh.le ⟨x, hx, rfl⟩⟩
    obtain ⟨y, hy, hxy⟩ := hh.ge hx
    have := congrArg (· ᵥ* (h⁻¹).val) hxy
    simp only [vecMul_vecMul, Units.mul_inv, vecMul_one] at this
    exact this ▸ hy

def glLatCong (c : kˣ) (Λ : Submodule 𝒪[k] (D → k)) : Subgroup (GL D k) where
  carrier := {h | h ∈ glLat Λ ∧ ∀ x ∈ Λ, x ᵥ* (h.val - 1) ∈ c • Λ}
  one_mem' := ⟨one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨mul_mem hg hh, fun x hx => ?_⟩
    rw [show (g * h).val - 1 = g.val * (h.val - 1) + (g.val - 1) by simp [mul_sub], vecMul_add, ← vecMul_vecMul]
    exact add_mem (hh' _ ((hg x).2 hx)) (hg' x hx)
  inv_mem' := by
    rintro h ⟨hh, hh'⟩
    refine ⟨inv_mem hh, fun x hx => ?_⟩
    rw [show (h⁻¹).val - 1 = -((h⁻¹).val * (h.val - 1)) by rw [mul_sub, Units.inv_mul, mul_one, neg_sub],
      vecMul_neg, ← vecMul_vecMul]
    exact neg_mem (hh' _ (((glLat Λ).inv_mem hh x).2 hx))

theorem glLat_stdLat : glLat (stdLat k D) = KO k D := by
  have key : ∀ h : GL D k, (∀ x ∈ stdLat k D, x ᵥ* h.val ∈ stdLat k D) ↔ ∀ i j, h.val i j ∈ 𝒪[k] := fun h => by
    constructor
    · intro hh i j
      simpa using mem_stdLat.1 (hh (Pi.single i 1) (mem_stdLat.2 fun l => by
        by_cases h : l = i
        · subst h; simp
        · simp [h])) j
    · intro hh x hx
      exact mem_stdLat.2 fun j => Subring.sum_mem _ fun i _ => mul_mem (mem_stdLat.1 hx i) (hh i j)
  ext h
  rw [mem_KO_iff, ← key, ← key]
  refine ⟨fun hh => ⟨fun x hx => (hh x).2 hx, fun x hx => ((glLat _).inv_mem hh x).2 hx⟩, fun hh x => ⟨fun hx => ?_, hh.1 x⟩⟩
  simpa only [vecMul_vecMul, Units.mul_inv, vecMul_one] using hh.2 _ hx

omit [Fintype D] in

def blockUnits (ϖ : kˣ) (e : ℕ) (P : Finset D) : D → kˣ := fun j => if j ∈ P then (ϖ ^ e)⁻¹ else 1

omit [Fintype D] in

def blockLat (ϖ : kˣ) (e : ℕ) (P : Finset D) : Submodule 𝒪[k] (D → k) := diagLat (blockUnits ϖ e P)

def blockScale (ϖ : kˣ) (e : ℕ) (P : Finset D) : GL D k := diagGL (blockUnits ϖ e P)

instance isLattice_blockLat (ϖ : kˣ) (e : ℕ) (P : Finset D) : Submodule.IsLattice k (blockLat ϖ e P) :=
  isLattice_diagLat _

theorem vecMul_blockScale_mem (ϖ : kˣ) (e : ℕ) (P : Finset D) (x : D → k) :
    x ᵥ* (blockScale ϖ e P).val ∈ blockLat ϖ e P ↔ x ∈ stdLat k D := by
  rw [mem_stdLat]
  refine forall_congr' fun j => ?_
  have h0 : 0 < valuation k (blockUnits ϖ e P j : k) := zero_lt_iff.2 (by simp)
  rw [blockScale, diagGL_val, vecMul_diagonal, map_mul, Valuation.mem_integer_iff]
  exact mul_le_iff_le_one_left h0

omit [Fintype D] in

theorem blockLat_empty (ϖ : kˣ) (e : ℕ) : blockLat ϖ e (∅ : Finset D) = stdLat k D := by
  unfold blockLat stdLat; congr 1

omit [DecidableEq D] in

def latA (ϖ : kˣ) (e : ℕ) (Λ' : Submodule 𝒪[k] (D → k)) : Submodule 𝒪[k] (D → k) := (ϖ ^ e)⁻¹ • dualLat Λ'

theorem latA_blockLat (ϖ : kˣ) (e : ℕ) (P : Finset D) : latA ϖ e (blockLat ϖ e P) = blockLat ϖ e Pᶜ := by
  rw [latA, blockLat, dualLat_diagLat, smul_diagLat, blockLat]
  congr 1
  funext j
  by_cases h : j ∈ P <;> simp [blockUnits, h]

omit [Fintype D] [DecidableEq D]

def HasDepth (ϖ : kˣ) (e : ℕ) (Λ : Submodule 𝒪[k] (D → k)) (Φ : Matrix A D k → ℂ) : Prop :=
  (∀ X, X ∉ matLat A Λ → Φ X = 0) ∧ ∀ X, ∀ Z ∈ matLat A (ϖ ^ e • Λ), Φ (X + Z) = Φ X

variable (A) in

def depthSpace (ϖ : kˣ) (e : ℕ) (Λ : Submodule 𝒪[k] (D → k)) : Submodule ℂ (Matrix A D k → ℂ) where
  carrier := {Φ | HasDepth ϖ e Λ Φ}
  add_mem' h h' := ⟨fun X hX => by simp [h.1 X hX, h'.1 X hX], fun X Z hZ => by simp [h.2 X Z hZ, h'.2 X Z hZ]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  smul_mem' c _ h := ⟨fun X hX => by simp [h.1 X hX], fun X Z hZ => by simp [h.2 X Z hZ]⟩

def IsNatDatum (ϖ : kˣ) (e : ℕ) (Φ : Matrix A D k → ℂ) : Prop := HasDepth ϖ e (stdLat k D) Φ

theorem pow_smul_le {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (Λ : Submodule 𝒪[k] (D → k)) : ϖ ^ e • Λ ≤ Λ := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  have h : ((ϖ ^ e : kˣ) : k) ∈ 𝒪[k] := by
    rw [Units.val_pow_eq_pow_val]
    exact pow_mem (show valuation k (ϖ : k) ≤ 1 from hϖ ▸ uniformizer_lt_one.le) e
  exact Λ.smul_mem ⟨_, h⟩ hy

theorem hasDepth_indicator {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (Λ : Submodule 𝒪[k] (D → k)) :
    HasDepth ϖ e Λ ((matLat A Λ : Set (Matrix A D k)).indicator 1) := by
  refine ⟨fun X hX => Set.indicator_of_notMem hX _, fun X Z hZ => ?_⟩
  have hZ' : Z ∈ matLat A Λ := fun i => pow_smul_le hϖ e Λ (hZ i)
  by_cases hX : X ∈ matLat A Λ
  · rw [Set.indicator_of_mem (add_mem hX hZ'), Set.indicator_of_mem hX]; rfl
  · rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem (fun h => hX ((add_mem_cancel_right hZ').1 h))]

end Lattices

section Fourier
variable {A D : Type*}

variable (k) in

abbrev Res (e : ℕ) : Type _ := 𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ e

instance finite_Res (e : ℕ) : Finite (Res k e) :=
  haveI : Finite (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k]) := inferInstanceAs (Finite 𝓀[k])
  Ideal.finite_quotient_pow (IsNoetherian.noetherian _) e

instance fintype_Res (e : ℕ) : Fintype (Res k e) := Fintype.ofFinite _

def liftRes {B : Type*} {e : ℕ} (T : A → B → Res k e) : Matrix A B k :=
  Matrix.of fun i j => ((Quotient.out (T i j) : 𝒪[k]) : k)

theorem liftRes_mem {B : Type*} {e : ℕ} (T : A → B → Res k e) (i : A) (j : B) : liftRes T i j ∈ 𝒪[k] :=
  (Quotient.out (T i j) : 𝒪[k]).2

variable [DecidableEq D]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def setCols (P : Finset D) (Y : Matrix A D k) (T : Matrix A P k) : Matrix A D k :=
  Matrix.of fun i j => if h : j ∈ P then T i ⟨j, h⟩ else Y i j

variable [Fintype A]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq D] in

def pairCols (P : Finset D) (Y : Matrix A D k) (T : Matrix A P k) : k := ∑ i, ∑ j : P, T i j * Y i j

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq D] in

theorem pairCols_eq_trace (P : Finset D) (Y : Matrix A D k) (T : Matrix A P k) :
    pairCols P Y T = trace (T * (Y.submatrix id (Subtype.val : P → D))ᵀ) := by
  simp [pairCols, trace, Matrix.mul_apply]

def fourierInt [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (m : Measure k) (P : Finset D)
    (Φ : Matrix A D k → ℂ) (Y : Matrix A D k) : ℂ :=
  ∫ T : Matrix A P k, Φ (setCols P Y T) * (ψ (pairCols P Y T) : ℂ) ∂(volM m A P)

variable [DecidableEq A]

open Classical in

def fourierSum (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) :
    (Matrix A D k → ℂ) →ₗ[ℂ] (Matrix A D k → ℂ) where
  toFun Φ Y := if ∀ i, ∀ j ∈ P, ((ϖ ^ e : kˣ) : k) * Y i j ∈ 𝒪[k] then
    ((resCard k : ℂ) ^ (e * Fintype.card A * P.card))⁻¹ *
      ∑ T : A → P → Res k e, Φ (setCols P Y (liftRes T)) * (ψ (pairCols P Y (liftRes T)) : ℂ) else 0
  map_add' Φ Φ' := by
    funext Y; simp only [Pi.add_apply]; split_ifs <;> simp [add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c Φ := by
    funext Y; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · simp only [mul_assoc, ← Finset.mul_sum]; ring
    · simp

open Classical in

def invFourierSum (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) :
    (Matrix A D k → ℂ) →ₗ[ℂ] (Matrix A D k → ℂ) where
  toFun Ψ T := if ∀ i, ∀ j ∈ P, T i j ∈ 𝒪[k] then
    ∑ S : A → P → Res k e, Ψ (setCols P T ((ϖ ^ e)⁻¹ • liftRes S)) *
      (ψ (-pairCols P T ((ϖ ^ e)⁻¹ • liftRes S)) : ℂ) else 0
  map_add' Φ Φ' := by
    funext Y; simp only [Pi.add_apply]; split_ifs <;> simp [add_mul, Finset.sum_add_distrib]
  map_smul' c Φ := by
    funext Y; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · simp only [mul_assoc, ← Finset.mul_sum]
    · simp

open Classical in

theorem fourierSum_apply (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) (Φ : Matrix A D k → ℂ)
    (Y : Matrix A D k) : fourierSum ψ ϖ e P Φ Y = if ∀ i, ∀ j ∈ P, ((ϖ ^ e : kˣ) : k) * Y i j ∈ 𝒪[k] then
    ((resCard k : ℂ) ^ (e * Fintype.card A * P.card))⁻¹ *
      ∑ T : A → P → Res k e, Φ (setCols P Y (liftRes T)) * (ψ (pairCols P Y (liftRes T)) : ℂ) else 0 := rfl

open Classical in

theorem invFourierSum_apply (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) (Ψ : Matrix A D k → ℂ)
    (T : Matrix A D k) : invFourierSum ψ ϖ e P Ψ T = if ∀ i, ∀ j ∈ P, T i j ∈ 𝒪[k] then
    ∑ S : A → P → Res k e, Ψ (setCols P T ((ϖ ^ e)⁻¹ • liftRes S)) *
      (ψ (-pairCols P T ((ϖ ^ e)⁻¹ • liftRes S)) : ℂ) else 0 := rfl

open Classical in

theorem invFourierSum_inv_apply (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) (Ψ : Matrix A D k → ℂ)
    (T : Matrix A D k) : invFourierSum ψ⁻¹ ϖ e P Ψ T = if ∀ i, ∀ j ∈ P, T i j ∈ 𝒪[k] then
    ∑ S : A → P → Res k e, Ψ (setCols P T ((ϖ ^ e)⁻¹ • liftRes S)) *
      (ψ (pairCols P T ((ϖ ^ e)⁻¹ • liftRes S)) : ℂ) else 0 := by
  simp only [invFourierSum_apply, AddChar.inv_apply, neg_neg]

theorem invFourierSum_inv_eq_neg (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) (Ψ : Matrix A D k → ℂ)
    (T : Matrix A D k) : invFourierSum ψ⁻¹ ϖ e P Ψ T =
      invFourierSum ψ ϖ e P Ψ (setCols P T (Matrix.of fun i j => -T i j)) := by
  have h1 : ∀ S, setCols P (setCols P T (Matrix.of fun i j => -T i j)) S = setCols P T S := fun S => by
    ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
  have h2 : ∀ S, -pairCols P (setCols P T (Matrix.of fun i j => -T i j)) S = pairCols P T S := fun S => by
    simp [pairCols, setCols]
  have h3 : (∀ i, ∀ j ∈ P, setCols P T (Matrix.of fun i j => -T i j) i j ∈ 𝒪[k]) ↔ ∀ i, ∀ j ∈ P, T i j ∈ 𝒪[k] :=
    forall_congr' fun i => forall₂_congr fun j h => by simp [setCols, h]
  classical
  rw [invFourierSum_inv_apply, invFourierSum_apply]
  simp only [h1, h2]
  exact if_congr h3.symm rfl rfl

theorem fourierSum_empty (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (Φ : Matrix A D k → ℂ) :
    fourierSum ψ ϖ e ∅ Φ = Φ := by
  funext Y
  have h : ∀ T, setCols ∅ Y T = Y := fun T => by ext i j; simp [setCols]
  simp [fourierSum_apply, h, pairCols]

theorem invFourierSum_empty (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (Φ : Matrix A D k → ℂ) :
    invFourierSum ψ ϖ e ∅ Φ = Φ := by
  funext Y
  have h : ∀ T, setCols ∅ Y T = Y := fun T => by ext i j; simp [setCols]
  simp [invFourierSum_apply, h, pairCols]

end Fourier

section Maps
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

def shellSet (ϖ : kˣ) (n : A → ℤ) : Set (GL A k) :=
  DoubleCoset.doubleCoset (diagGL fun i => ϖ ^ n i) (KO k A) (KO k A)

theorem mem_shellSet {ϖ : kˣ} {n : A → ℤ} {g : GL A k} :
    g ∈ shellSet ϖ n ↔ ∃ x ∈ KO k A, ∃ y ∈ KO k A, g = x * (diagGL fun i => ϖ ^ n i) * y :=
  DoubleCoset.mem_doubleCoset

theorem shellSet_zero (ϖ : kˣ) : shellSet ϖ (0 : A → ℤ) = KO k A := by
  have h1 : (diagGL fun i : A => ϖ ^ (0 : A → ℤ) i) = 1 := Units.ext (by simp)
  ext g
  rw [mem_shellSet, h1]
  exact ⟨by rintro ⟨x, hx, y, hy, rfl⟩; simpa using mul_mem hx hy, fun h => ⟨g, h, 1, one_mem _, by simp⟩⟩

def boxSet (ϖ : kˣ) (e : ℕ) : Set (GL A k) :=
  {g | ∃ n : A → ℤ, (∀ i, 0 ≤ n i ∧ n i < e) ∧ g ∈ shellSet ϖ n}

variable [MeasurableSpace k] [BorelSpace k]

def shell (μ : Measure (GL A k)) (ϖ : kˣ) (ν : kˣ →* ℂˣ) (z : ℂ) (φ : Matrix A A k → ℂ) (n : A → ℤ) : ℂ :=
  ∫ g in shellSet ϖ n, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ

def shellSum {a : ℕ} (μ : Measure (GL (Fin a) k)) (ϖ : kˣ) (ν : kˣ →* ℂˣ) (z : ℂ)
    (φ : Matrix (Fin a) (Fin a) k → ℂ) : ℂ :=
  ∑ᶠ n : {n : Fin a → ℤ // Antitone n}, shell μ ϖ ν z φ n.1

def bigF {a : ℕ} (μ : Measure (GL (Fin a) k)) (ϖ : kˣ) (ν : kˣ →* ℂˣ) (Φ : Matrix (Fin a) D k → ℂ)
    (X : Matrix (Fin a) D k) : ℂ :=
  shellSum μ ϖ ν ((Fintype.card D : ℂ) / 2) fun g => Φ (g * X)

def smallF (μ : Measure (GL A' k)) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (Y : Matrix A' D k) : ℂ :=
  ∫ g, Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card D : ℂ) / 2) ∂μ

def bigP {a : ℕ} (μ : Measure (GL (Fin a) k)) (ϖ : kˣ) (σ : Fin a ⊕ A' ≃ D) (ν β : kˣ →* ℂˣ)
    (Φ : Matrix (Fin a) D k → ℂ) (h : GL D k) : ℂ :=
  bigF μ ϖ ν (omA ν β 1 h Φ) (X0 k σ)

def smallP (μ : Measure (GL A' k)) (σ : A ⊕ A' ≃ D) (ν α : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (h : GL D k) : ℂ :=
  (α (gdet h) : ℂ) * apow (gdet h) ((Fintype.card A' : ℂ) / 2) * smallF μ ν Ψ (Y0 k σ * h.val)

omit [BorelSpace k] in

theorem shellSum_smul {a : ℕ} (μ : Measure (GL (Fin a) k)) (ϖ : kˣ) (ν : kˣ →* ℂˣ) (z c : ℂ)
    (φ : Matrix (Fin a) (Fin a) k → ℂ) : shellSum μ ϖ ν z (fun g => c * φ g) = c * shellSum μ ϖ ν z φ := by
  simp only [shellSum, shell, mul_finsum, mul_assoc, integral_const_mul]

omit [BorelSpace k] [Fintype A'] [DecidableEq A'] in

theorem bigZetaIntegral_eq {a : ℕ} (μ : Measure (GL (Fin a) k)) (ϖ : kˣ) (σ : Fin a ⊕ A' ≃ D) (ν β : kˣ →* ℂˣ)
    (Φ : Matrix (Fin a) D k → ℂ) (h : GL D k) : bigP μ ϖ σ ν β Φ h =
      (β (gdet h) : ℂ) * apow (gdet h) (-(a : ℂ) / 2) * bigF μ ϖ ν Φ (X0 k σ * (invT h).val) := by
  simp [bigP, bigF, omA, ← shellSum_smul, Matrix.mul_assoc]

omit [BorelSpace k] [Fintype A] [DecidableEq A] in

theorem smallP_eq (μ : Measure (GL A' k)) (σ : A ⊕ A' ≃ D) (ν α : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (h : GL D k) :
    smallP μ σ ν α Ψ h = smallF μ ν (omB ν α 1 h Ψ) (Y0 k σ) := by
  simp [smallP, smallF, omB, Matrix.mul_assoc, mul_assoc, integral_const_mul]

omit [DecidableEq D] in

theorem smallF_mul_left (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ)
    (g₀ : GL A' k) (Y : Matrix A' D k) :
    (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card D : ℂ) / 2) * smallF μ ν Ψ (g₀.val * Y) = smallF μ ν Ψ Y := by
  unfold smallF
  rw [← integral_mul_right_eq_self (fun g : GL A' k =>
    Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card D : ℂ) / 2)) g₀, ← integral_const_mul]
  congr 1
  funext g
  simp only [Units.val_mul, map_mul, apow_mul, Matrix.mul_assoc]
  ring

open Classical in

def fFun (μ : Measure (GL A' k)) (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (X : Matrix A D k) : ℂ :=
  if hX : ∃ h : GL D k, X = X0 k σ * (invT h).val then
    (ν (gdet hX.choose) : ℂ) * apow (gdet hX.choose) ((Fintype.card D : ℂ) / 2) *
      smallF μ ν Ψ (Y0 k σ * hX.choose.val) else 0

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in

theorem exists_secondBlock_of_frameFirstBlock_eq (σ : A ⊕ A' ≃ D) {h h' : GL D k} (H : X0 k σ * (invT h').val = X0 k σ * (invT h).val) :
    ∃ C : GL A' k, Y0 k σ * h'.val = C.val * (Y0 k σ * h.val) ∧ gdet h' = gdet C * gdet h := by
  obtain ⟨u, rfl⟩ : ∃ u, h' = u * h := ⟨h' * h⁻¹, by simp⟩
  have H1 : X0 k σ * u.valᵀ = X0 k σ := by
    have h1 := congrArg (· * ((invT h)⁻¹).val) H
    simp only [map_mul, Units.val_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h1
    rw [← invT_inv_val]
    nth_rewrite 1 [← h1]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have H2 : ∀ r i, u.val r (σ (Sum.inl i)) = if σ (Sum.inl i) = r then 1 else 0 := fun r i => by
    have h1 := congrFun (congrFun H1 i) r
    rw [frameMatrixFirstColumnBlock_mul_apply] at h1
    exact h1
  let C : Matrix A' A' k := Matrix.of fun i j => u.val (σ (Sum.inr i)) (σ (Sum.inr j))
  have hdet : u.val.det = C.det := by
    rw [← det_submatrix_equiv_self σ, show u.val.submatrix σ σ =
      fromBlocks 1 (Matrix.of fun i j => u.val (σ (Sum.inl i)) (σ (Sum.inr j))) 0 C from ?_,
      det_fromBlocks_zero₂₁, det_one, one_mul]
    ext (i | i) (j | j) <;> simp [H2, C, one_apply, eq_comm]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero C (hdet ▸ u.det_ne_zero), ?_, ?_⟩
  · rw [Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    congr 1
    ext i j
    obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [frameMatrixSecondColumnBlock_mul_apply, H2, Matrix.mul_apply, Y0, C]
  · rw [gdet_mul]; congr 1; exact Units.ext hdet

theorem splitTheta_fFun_frameFirstBlock_mul (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ)
    (Ψ : Matrix A' D k → ℂ) (h : GL D k) : fFun μ σ ν Ψ (X0 k σ * (invT h).val) =
      (ν (gdet h) : ℂ) * apow (gdet h) ((Fintype.card D : ℂ) / 2) * smallF μ ν Ψ (Y0 k σ * h.val) := by
  have hX : ∃ h' : GL D k, X0 k σ * (invT h).val = X0 k σ * (invT h').val := ⟨h, rfl⟩
  obtain ⟨C, h1, h2⟩ := exists_secondBlock_of_frameFirstBlock_eq σ hX.choose_spec.symm
  rw [fFun, dif_pos hX, h1, h2, ← smallF_mul_left μ ν Ψ C (Y0 k σ * h.val), map_mul, apow_mul, Units.val_mul]
  ring

open Classical in

def phiA (μ : Measure (GL A' k)) (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ) (Λ' : Submodule 𝒪[k] (D → k))
    (Ψ : Matrix A' D k → ℂ) (X : Matrix A D k) : ℂ :=
  if IsPrimFrame (latA ϖ e Λ') X then fFun μ σ ν Ψ X else 0

def squareFlip (μ : Measure (GL A' k)) (σ : A ⊕ A' ≃ D) (ψ : AddChar k Circle) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ)
    (P : Finset D) (ΦB : Matrix A' D k → ℂ) : Matrix A D k → ℂ :=
  invFourierSum ψ⁻¹ ϖ e Pᶜ (phiA μ σ ν ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P ΦB))

theorem shell_zero_example (ϖ : kˣ) (ν : kˣ →* ℂˣ) (z : ℂ) (φ : Matrix A A k → ℂ)
    (hφ : ∀ g ∈ KO k A, φ g.val * (ν (gdet g) : ℂ) = 1) : shell (haarVol (KO k A)) ϖ ν z φ 0 = 1 := by
  rw [shell, shellSet_zero, setIntegral_congr_fun isOpen_KO.measurableSet (g := fun _ => (1 : ℂ))]
  · simp [Measure.real, haarVol_self isOpen_KO le_rfl]
  · intro g hg
    simp only [hφ g hg, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg), one_mul]

theorem smallF_of_isEmpty [IsEmpty A'] (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (Y : Matrix A' D k) :
    smallF (haarVol (KO k A')) ν Ψ Y = Ψ 0 := by
  have h1 : (KO k A' : Set (GL A' k)) = Set.univ :=
    Set.eq_univ_of_forall fun g => Subsingleton.elim 1 g ▸ one_mem _
  have h2 := haarVol_self (k := k) (n := A') isOpen_KO le_rfl
  rw [h1] at h2
  have h3 : ∀ g : GL A' k, gdet g = 1 := fun g => Subsingleton.elim 1 g ▸ map_one _
  have h4 : ∀ g : GL A' k, g.val * Y = 0 := fun g => by ext i; exact isEmptyElim i
  simp [smallF, h3, h4, Measure.real, h2]

theorem schwartzDatum_standardBasis_of_isEmpty [IsEmpty A'] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ) (Ψ : Matrix A' D k → ℂ) :
    phiA (haarVol (KO k A')) σ ν ϖ e (blockLat ϖ e Finset.univ) Ψ (X0 k σ) = Ψ 0 := by
  have := splitTheta_fFun_frameFirstBlock_mul (haarVol (KO k A')) σ ν Ψ 1
  rw [phiA, latA_blockLat, Finset.compl_univ, blockLat_empty, if_pos (isPrimitiveFrame_standardBasis σ)]
  simpa [smallF_of_isEmpty] using this

end Maps

inductive Assignment
  | one
  | two
  deriving DecidableEq

def Assignment.block (s : Assignment) (D₁ D₂ : Type*) [Fintype D₁] [Fintype D₂] : Finset (D₁ ⊕ D₂) :=
  match s with
  | .one => Finset.univ.filter fun j => j.isLeft
  | .two => Finset.univ.filter fun j => j.isRight

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def Assignment.read (s : Assignment) {n : Type*} [Fintype n] [DecidableEq n] : GL n k →* GL n k :=
  match s with
  | .one => invT
  | .two => MonoidHom.id _

section
variable {D₁ D₂ : Type*} [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]

theorem mem_blockLat_two (ϖ : kˣ) (e : ℕ) (x : D₁ ⊕ D₂ → k) :
    x ∈ blockLat ϖ e (Assignment.two.block D₁ D₂) ↔ (∀ j, valuation k (x (.inl j)) ≤ 1) ∧
      ∀ j, valuation k (x (.inr j)) ≤ valuation k (((ϖ ^ e)⁻¹ : kˣ) : k) := by
  simp [blockLat, mem_diagLat, blockUnits, Assignment.block]

theorem mem_blockLat_one (ϖ : kˣ) (e : ℕ) (x : D₁ ⊕ D₂ → k) :
    x ∈ blockLat ϖ e (Assignment.one.block D₁ D₂) ↔
      (∀ j, valuation k (x (.inl j)) ≤ valuation k (((ϖ ^ e)⁻¹ : kˣ) : k)) ∧ ∀ j, valuation k (x (.inr j)) ≤ 1 := by
  simp [blockLat, mem_diagLat, blockUnits, Assignment.block]

theorem compl_block_two : (Assignment.two.block D₁ D₂)ᶜ = Assignment.one.block D₁ D₂ := by
  ext (j | j) <;> simp [Assignment.block]

theorem compl_block_one : (Assignment.one.block D₁ D₂)ᶜ = Assignment.two.block D₁ D₂ := by
  ext (j | j) <;> simp [Assignment.block]
end

inductive Edge

  | theta (i j : ℕ)

  | ex (i j : ℕ)
  deriving DecidableEq

@[reducible] def Edge.src : Edge → ℕ × ℕ
  | .theta i j => (i, j + 1)
  | .ex i j => (i, j)

@[reducible] def Edge.tgt : Edge → ℕ × ℕ
  | .theta i j => (i, j)
  | .ex i j => (i + 1, j)

def Edge.InGrid (m : ℕ) : Edge → Prop
  | .theta i j => i ≤ m ∧ j < m
  | .ex i j => i < m ∧ j ≤ m

def IsPath (γ : List Edge) : Prop := γ.IsChain fun e e' => e.tgt = e'.src

def innerVertices (γ : List Edge) : List (ℕ × ℕ) := γ.tail.map Edge.src

def PassesThrough (i j : ℕ) (γ : List Edge) : Prop := [Edge.theta i j, Edge.ex i j] <:+: γ

def flipPath (i j : ℕ) (γ : List Edge) : List Edge :=
  γ.map fun e => if e = .theta i j then .ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e

inductive CanFlip : List Edge → List (ℕ × ℕ) → Prop
  | nil (γ : List Edge) : CanFlip γ []
  | cons {γ : List Edge} {x : ℕ × ℕ} {l : List (ℕ × ℕ)} :
      PassesThrough x.1 x.2 γ → CanFlip (flipPath x.1 x.2 γ) l → CanFlip γ (x :: l)

def givenPath (m : ℕ) : List Edge := (List.range m).reverse.map (Edge.theta 0) ++ (List.range m).map (Edge.ex · 0)

def oppositePath (m : ℕ) : List Edge :=
  (List.range m).map (Edge.ex · m) ++ (List.range m).reverse.map (Edge.theta m)

example : IsPath (givenPath 2) ∧ innerVertices (givenPath 2) = [(0, 1), (0, 0), (1, 0)] := by
  unfold IsPath; decide

example : CanFlip (givenPath 2) [(0, 0), (0, 1), (1, 0), (1, 1)] ∧
    [(0, 0), (0, 1), (1, 0), (1, 1)].foldl (fun γ x => flipPath x.1 x.2 γ) (givenPath 2) = oppositePath 2 := by
  refine ⟨.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.nil _)))), by decide⟩ <;> unfold PassesThrough <;> decide

variable (k) in

structure Grid where

  m : ℕ

  r : ℕ

  t : ℕ

  s : ℕ

  mu : ℕ → kˣ →* ℂˣ

  chi : ℕ → kˣ →* ℂˣ

  eta : kˣ →* ℂˣ

namespace Grid
variable (G : Grid k)

section
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def rank (X : ℕ × ℕ) : ℕ := G.r + X.2 * G.t + X.1 * G.s

theorem rank_square (i j : ℕ) : G.rank (i + 1, j + 1) + G.rank (i, j) = G.rank (i, j + 1) + G.rank (i + 1, j) := by
  simp only [rank]; ring

def blockChar : Edge → kˣ →* ℂˣ
  | .theta _ j => G.mu (j + 1)
  | .ex i _ => G.chi (G.m - i)

def kappa (e : Edge) (X : ℕ × ℕ) : kˣ →* ℂˣ := G.blockChar e / G.eta ^ ((G.rank X + 1) % 2)

def alpha (i j : ℕ) : kˣ →* ℂˣ := G.mu (j + 1) * G.eta ^ (G.rank (i, j) % 2)

def beta (i j : ℕ) : kˣ →* ℂˣ := G.chi (G.m - i) * G.eta ^ (G.rank (i, j) % 2)

def nu (i j : ℕ) : kˣ →* ℂˣ := G.mu (j + 1) / G.chi (G.m - i)

theorem alpha_div_beta (i j : ℕ) : G.alpha i j / G.beta i j = G.nu i j := mul_div_mul_right_eq_div _ _ _

theorem kappa_inner (i j : ℕ) :
    G.kappa (.ex i j) (i, j) / G.kappa (.theta i j) (i, j) = (G.nu i j)⁻¹ := by
  simp [kappa, blockChar, nu]

theorem kappa_outer (i j : ℕ) :
    G.kappa (.theta (i + 1) j) (i + 1, j + 1) / G.kappa (.ex i (j + 1)) (i + 1, j + 1) = G.nu i j := by
  simp [kappa, blockChar, nu]

abbrev Args : Type _ := ∀ e : Edge, Matrix (Fin (G.rank e.tgt)) (Fin (G.rank e.src)) k

abbrev VertexGroup : Type _ := ∀ X : ℕ × ℕ, GL (Fin (G.rank X)) k

def moveArgs (s : Assignment) (g : G.VertexGroup) (x : G.Args) : G.Args := fun e =>
  ((s.read (g e.tgt))⁻¹).val * x e * (s.read (g e.src)).val
end

structure IsGood (ϖ : kˣ) (ψ : AddChar k Circle) (e : ℕ) : Prop where
  odd_splitThetaGridThetaRankIncrement : Odd G.t
  gridDataAtRealPlace_s_odd : Odd G.s
  eta : IsUnram G.eta
  square : ∀ i < G.m, ∀ j < G.m, IsRightTranslationIsometric ϖ ψ (G.alpha i j) (G.beta i j) e

theorem exists_isGood (m r t s : ℕ) (ht : Odd t) (hs : Odd s) : ∃ (G : Grid k) (ϖ : kˣ) (ψ : AddChar k Circle),
    G.m = m ∧ G.r = r ∧ G.t = t ∧ G.s = s ∧ G.IsGood ϖ ψ 2 := by
  obtain ⟨ϖ, ψ, α, h⟩ := exists_localSetting (k := k)
  exact ⟨⟨m, r, t, s, fun _ => α, fun _ => 1, 1⟩, ϖ, ψ, rfl, rfl, rfl, rfl, ht, hs, fun _ _ => rfl,
    fun i _ j _ => by simpa [alpha, beta] using h⟩

def edgeFactor (s : Assignment) (g : G.VertexGroup) (e : Edge) : ℂ :=
  (G.kappa e e.src (gdet (g e.src)) : ℂ) * (((G.kappa e e.tgt (gdet (g e.tgt)))⁻¹ : ℂˣ) : ℂ) *
    apow (gdet (s.read (g e.src))) ((G.rank e.tgt : ℂ) / 2) * apow (gdet (s.read (g e.tgt))) (-(G.rank e.src : ℂ) / 2)

def pathAct (s : Assignment) (γ : List Edge) (g : G.VertexGroup) (T : G.Args → ℂ) : G.Args → ℂ := fun x =>
  (γ.map (G.edgeFactor s g)).prod * T (G.moveArgs s g x)

theorem pathAct_one (s : Assignment) (γ : List Edge) (T : G.Args → ℂ) : G.pathAct s γ 1 T = T := by
  funext x
  have h1 : G.edgeFactor s 1 = fun _ => 1 := by funext e; simp [edgeFactor]
  have h2 : G.moveArgs s 1 x = x := by funext e; simp [moveArgs]
  simp [pathAct, h1, h2]

theorem pathAct_mul (s : Assignment) (γ : List Edge) (g g' : G.VertexGroup) (T : G.Args → ℂ) :
    G.pathAct s γ (g * g') T = G.pathAct s γ g (G.pathAct s γ g' T) := by
  funext x
  have h1 : G.edgeFactor s (g * g') = fun e => G.edgeFactor s g e * G.edgeFactor s g' e := by
    funext e
    simp only [edgeFactor, Pi.mul_apply, map_mul, apow_mul, _root_.mul_inv_rev, Units.val_mul]
    ring
  have h2 : G.moveArgs s (g * g') x = G.moveArgs s g' (G.moveArgs s g x) := by
    funext e
    simp only [moveArgs, Pi.mul_apply, map_mul, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  simp only [pathAct, h1, h2, List.prod_map_mul, mul_assoc]

def IsTensor (ϖ : kˣ) (e : ℕ) (γ : List Edge) (T : G.Args → ℂ) : Prop :=
  DependsOn T {b | b ∈ γ} ∧ (∀ x : G.Args, ∀ b ∈ γ, x b ∉ matLat _ (stdLat k _) → T x = 0) ∧
    ∀ x z : G.Args, (∀ b, z b ∈ matLat _ (ϖ ^ e • stdLat k _)) → T (x + z) = T x

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def lines₂ (γ : List Edge) (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) :
    G.Args → ℂ := fun x => (γ.map fun b => φ b (x b)).prod

theorem isTensor_pureTensor (ϖ : kˣ) (e : ℕ) (γ : List Edge)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (hφ : ∀ b ∈ γ, IsNatDatum ϖ e (φ b)) :
    G.IsTensor ϖ e γ (G.lines₂ γ φ) := by
  refine ⟨fun x y h => ?_, fun x b hb hx => ?_, fun x z hz => ?_⟩
  · exact congrArg List.prod (List.map_congr_left fun b hb => by rw [h b hb])
  · exact List.prod_eq_zero (List.mem_map.2 ⟨b, hb, (hφ b hb).1 _ hx⟩)
  · exact congrArg List.prod (List.map_congr_left fun b hb => (hφ b hb).2 _ _ (hz b))

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

abbrev Level : Type _ := ∀ X : ℕ × ℕ, Subgroup (GL (Fin (G.rank X)) k)

def IsLevel (γ : List Edge) (J : G.Level) : Prop :=
  ∀ X ∈ innerVertices γ, IsOpen (J X : Set (GL (Fin (G.rank X)) k)) ∧ J X ≤ KO k _

def IsAdmissible (s : Assignment) (γ : List Edge) (J : G.Level) (T : G.Args → ℂ) : Prop :=
  ∀ X ∈ innerVertices γ, ∀ u ∈ J X, G.pathAct s γ (Pi.mulSingle X u) T = T

section
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev Cols (i j : ℕ) : Type := Fin (G.rank (i, j + 1)) ⊕ Fin (G.rank (i + 1, j))

def sliceB (i j : ℕ) (T : G.Args → ℂ) (x : G.Args) (Z : Matrix (Fin (G.rank (i, j))) (G.Cols i j) k) : ℂ :=
  T (Function.update (Function.update x (.theta i j) Z.toCols₁) (.ex i j) Z.toCols₂ᵀ)

def joinA (i j : ℕ) (x : G.Args) : Matrix (Fin (G.rank (i + 1, j + 1))) (G.Cols i j) k :=
  fromCols (x (.ex i (j + 1))) (x (.theta (i + 1) j))ᵀ
end

def flipLevel (i j : ℕ) (J : G.Level) : G.Level := Function.update J (i + 1, j + 1) (KO k _)

variable [MeasurableSpace k] [BorelSpace k]

def flipTensor (s : Assignment) (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (i j : ℕ) (J : G.Level)
    (T : G.Args → ℂ) : G.Args → ℂ := fun x =>
  squareFlip (haarVol ((J (i, j)).map invT)) (stdSplit (G.rank_square i j)) ψ (G.nu i j) ϖ e
    (s.block _ _) (G.sliceB i j T x) (G.joinA i j x)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in

structure PiLocalization₂ where

  path : List Edge

  level : G.Level

  tensor : G.Args → ℂ

variable {G}

omit [MeasurableSpace k] [BorelSpace k] in

structure PiLocalization₂.IsAdmissible (S : G.PiLocalization₂) (s : Assignment) (ϖ : kˣ) (e : ℕ) : Prop where
  path : IsPath S.path
  level : G.IsLevel S.path S.level
  tensor : G.IsTensor ϖ e S.path S.tensor
  invariant : G.IsAdmissible s S.path S.level S.tensor

def PiLocalization₂.flip (s : Assignment) (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (S : G.PiLocalization₂) (x : ℕ × ℕ) : G.PiLocalization₂ :=
  ⟨flipPath x.1 x.2 S.path, G.flipLevel x.1 x.2 S.level, G.flipTensor s ψ ϖ e x.1 x.2 S.level S.tensor⟩

def PiLocalization₂.flips (s : Assignment) (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (S : G.PiLocalization₂) (l : List (ℕ × ℕ)) :
    G.PiLocalization₂ := l.foldl (PiLocalization₂.flip s ψ ϖ e) S

end Grid

def detCong (c : kˣ) (n : Type*) [Fintype n] [DecidableEq n] : Subgroup (GL n k) :=
  KO k n ⊓ (unitCong c).comap Matrix.GeneralLinearGroup.det

theorem isOpen_detCong (c : kˣ) (n : Type*) [Fintype n] [DecidableEq n] : IsOpen (detCong c n : Set (GL n k)) := by
  have hc : Continuous fun g : GL n k => (g.val.det - 1) / (c : k) :=
    (Units.continuous_val.matrix_det.sub continuous_const).div_const _
  convert isOpen_KO.inter (isOpen_int.preimage hc) using 1
  ext g
  have h0 : 0 < valuation k (c : k) := zero_lt_iff.2 (by simp)
  have h : (g.val.det - 1) / (c : k) ∈ 𝒪[k] ↔ valuation k (g.val.det - 1) ≤ valuation k (c : k) := by
    rw [Valuation.mem_integer_iff, map_div₀, div_le_one₀ h0]
  exact ⟨fun hg => ⟨hg.1, h.2 hg.2.2⟩, fun hg => ⟨hg.1, valuation_gdet_of_mem_KO hg.1, h.1 hg.2⟩⟩

theorem mul_mul_mem_matLat_iff {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {g : GL m k} {h : GL n k} (hg : g ∈ KO k m) (hh : h ∈ KO k n) (X : Matrix m n k) :
    g.val * X * h.val ∈ matLat m (stdLat k n) ↔ X ∈ matLat m (stdLat k n) := by
  have key : ∀ {g : GL m k} {h : GL n k}, g ∈ KO k m → h ∈ KO k n → ∀ X ∈ matLat m (stdLat k n),
      g.val * X * h.val ∈ matLat m (stdLat k n) := fun hg hh X hX =>
    mem_matLat_stdLat.2 fun i j => Subring.sum_mem _ fun l _ => mul_mem (Subring.sum_mem _ fun l' _ =>
      mul_mem (((mem_KO_iff _).1 hg).1 _ _) (mem_matLat_stdLat.1 hX _ _)) (((mem_KO_iff _).1 hh).1 _ _)
  refine ⟨fun H => ?_, key hg hh X⟩
  have := key (inv_mem hg) (inv_mem hh) _ H
  rwa [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
    Units.inv_mul, Matrix.one_mul] at this

theorem Assignment.read_mem_KO (s : Assignment) {n : Type*} [Fintype n] [DecidableEq n] {g : GL n k}
    (hg : g ∈ KO k n) : s.read g ∈ KO k n := by
  cases s
  · exact invT_mem_KO hg
  · exact hg

theorem Grid.IsGood.condLE_kappa {G : Grid k} {ϖ : kˣ} {ψ : AddChar k Circle} {e : ℕ} (h : G.IsGood ϖ ψ e)
    {b : Edge} (hb : b.InGrid G.m) (X : ℕ × ℕ) : CondLE ϖ e (G.kappa b X) := by
  intro x hx
  have h1 : G.eta x = 1 := h.eta x hx.1
  cases b with
  | theta i j =>
    have := (h.square 0 (by have := hb.2; omega) j hb.2).condα x hx
    simpa [Grid.kappa, Grid.blockChar, Grid.alpha, h1] using this
  | ex i j =>
    have := (h.square i hb.1 0 (by have := hb.1; omega)).condβ x hx
    simpa [Grid.kappa, Grid.blockChar, Grid.beta, h1] using this

theorem Grid.IsGood.exists_isAdmissible {G : Grid k} {ϖ : kˣ} {ψ : AddChar k Circle} {e : ℕ} (h : G.IsGood ϖ ψ e)
    (hϖ : IsUnif ϖ) (s : Assignment) {γ : List Edge} (hγ : IsPath γ) (hm : ∀ b ∈ γ, b.InGrid G.m) :
    ∃ S : G.PiLocalization₂, S.path = γ ∧ S.IsAdmissible s ϖ e ∧ S.tensor 0 = 1 := by
  refine ⟨⟨γ, fun X => detCong (ϖ ^ e) _, G.lines₂ γ fun b =>
      Set.indicator (SetLike.coe (matLat (Fin (G.rank b.tgt)) (stdLat k (Fin (G.rank b.src))))) 1⟩, rfl,
    ⟨hγ, fun X _ => ⟨isOpen_detCong _ _, inf_le_left⟩,
      G.isTensor_pureTensor ϖ e γ _ fun b _ => hasDepth_indicator hϖ e _, fun X _ u hu => ?_⟩, ?_⟩
  · have hg : ∀ Y, (Pi.mulSingle X u : G.VertexGroup) Y ∈ detCong (ϖ ^ e) _ := fun Y => by
      by_cases hY : Y = X
      · subst hY; simpa using hu
      · simp [hY, one_mem]
    generalize (Pi.mulSingle X u : G.VertexGroup) = g at hg
    funext x
    have h1 : (γ.map (G.edgeFactor s g)).prod = 1 := List.prod_eq_one fun c hc => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
      simp only [Grid.edgeFactor, h.condLE_kappa (hm b hb) _ _ (hg _).2,
        apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (s.read_mem_KO (hg _).1))]
      simp
    simp only [Grid.pathAct, h1, one_mul, Grid.lines₂]
    refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
    have h2 := mul_mul_mem_matLat_iff (inv_mem (s.read_mem_KO (hg b.tgt).1)) (s.read_mem_KO (hg b.src).1) (x b)
    simp only [Grid.moveArgs]
    by_cases hx : x b ∈ matLat _ (stdLat k _)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (h2.2 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun H => hx (h2.1 H))]
  · refine List.prod_eq_one fun c hc => ?_
    obtain ⟨b, _, rfl⟩ := List.mem_map.1 hc
    exact Set.indicator_of_mem (zero_mem (matLat _ (stdLat k _))) _

theorem isOpen_map_invT {n : Type*} [Fintype n] [DecidableEq n] {J : Subgroup (GL n k)}
    (ho : IsOpen (J : Set (GL n k))) (hK : J ≤ KO k n) :
    IsOpen (J.map invT : Set (GL n k)) ∧ J.map invT ≤ KO k n := by
  refine ⟨?_, by rintro _ ⟨g, hg, rfl⟩; exact invT_mem_KO (hK hg)⟩
  have hc : Continuous (invT : GL n k → GL n k) :=
    Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩
  convert ho.preimage hc using 1
  ext g
  exact ⟨by rintro ⟨g, hg, rfl⟩; simpa using hg, fun hg => ⟨invT g, hg, invT_invT g⟩⟩

end GlobalTheory.SplitFlip

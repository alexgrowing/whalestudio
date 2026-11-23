import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.SmGL

section Local

open Matrix

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nabs_pos' (x : kˣ) : 0 < nabs k x := by
  unfold nabs; exact_mod_cast MeasureTheory.distribHaarChar_pos

theorem nabs_mul' (x y : kˣ) : nabs k (x * y) = nabs k x * nabs k y := by simp [nabs]

open scoped Pointwise in

theorem nabs_eq_one {x : kˣ} (hx : valuation k (x : k) = 1) : nabs k x = 1 := by
  borelize k
  have hc : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  let K : TopologicalSpace.PositiveCompacts k := ⟨⟨(𝒪[k] : Set k), hc⟩, by
    rw [show interior ((⟨(𝒪[k] : Set k), hc⟩ : TopologicalSpace.Compacts k).carrier) =
      (𝒪[k] : Set k) from ho.interior_eq]
    exact ⟨0, zero_mem _⟩⟩
  have h1 : MeasureTheory.Measure.addHaarMeasure K (𝒪[k] : Set k) = 1 :=
    MeasureTheory.Measure.addHaarMeasure_self
  have hs : x • (𝒪[k] : Set k) = (𝒪[k] : Set k) := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show valuation k (((x⁻¹ : kˣ) : k) * y) ≤ 1 ↔ valuation k y ≤ 1
    simp [hx]
  have := MeasureTheory.distribHaarChar_eq_of_measure_smul_eq_mul
    (μ := MeasureTheory.Measure.addHaarMeasure K) (s := (𝒪[k] : Set k)) (g := x) (r := 1)
    (by simp [h1]) (by simp [h1]) (by simp [hs])
  simp [nabs, this]

def absPow (s : ℂ) : kˣ →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := fun x => ((nabs k x : ℝ) : ℂ) ^ s
      map_one' := by simp [nabs]
      map_mul' := fun x y => by
        rw [nabs_mul', Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg (nabs_pos' k x).le (nabs_pos' k y).le] }

theorem val_absPow (s : ℂ) (x : kˣ) : (absPow k s x : ℂ) = ((nabs k x : ℝ) : ℂ) ^ s := rfl

theorem val_absPow_ofReal (s : ℝ) (x : kˣ) : (absPow k s x : ℂ) = ((nabs k x ^ s : ℝ) : ℂ) :=
  (Complex.ofReal_cpow (nabs_pos' k x).le s).symm

theorem absPow_add (s t : ℂ) : absPow k (s + t) = absPow k s * absPow k t := by
  ext x
  simp only [val_absPow, MonoidHom.mul_apply, Units.val_mul]
  exact Complex.cpow_add _ _ (by exact_mod_cast (nabs_pos' k x).ne')

@[simp] theorem absPow_zero : absPow k 0 = 1 := by
  ext x; simp [val_absPow]

theorem absPow_neg (s : ℂ) : absPow k (-s) = (absPow k s)⁻¹ := by
  ext x; simp [val_absPow, Complex.cpow_neg]

theorem isUnram_absPow (s : ℂ) : IsUnram (absPow k s) := fun x hx => by
  ext; simp [val_absPow, nabs_eq_one k hx]

variable {k} in

theorem isSmoothChar_of_isUnram {χ : kˣ →* ℂˣ} (h : IsUnram χ) : IsSmoothChar χ := by
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have h1 : IsOpen ({x : kˣ | (x : k) ∈ (𝒪[k] : Set k)} ∩
      {x : kˣ | ((x⁻¹ : kˣ) : k) ∈ (𝒪[k] : Set k)}) :=
    (ho.preimage Units.continuous_val).inter (ho.preimage Units.continuous_coe_inv)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (h1.mem_nhds ?_) ?_)
  · exact ⟨one_mem 𝒪[k], by simpa using one_mem 𝒪[k]⟩
  · rintro x ⟨hx, hx'⟩
    have a1 : valuation k (x : k) ≤ 1 := hx
    have a2 : valuation k ((x⁻¹ : kˣ) : k) ≤ 1 := hx'
    refine h x (le_antisymm a1 ?_)
    rw [Units.val_inv_eq_inv_val, map_inv₀] at a2
    exact (inv_le_one₀ (zero_lt_iff.2 (by simp))).1 a2

def ord (x : kˣ) : ℤ :=
  -WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k (valuation k (x : k)))

theorem ord_mul (x y : kˣ) : ord k (x * y) = ord k x + ord k y := by
  simp only [ord, Units.val_mul, map_mul]
  rw [WithZero.log_mul (by simp) (by simp)]
  ring

variable {k} in

theorem ord_eq_zero {x : kˣ} (hx : valuation k (x : k) = 1) : ord k x = 0 := by simp [ord, hx]

variable {k} in

theorem ord_eq_one {x : kˣ} (hx : valuation k (x : k) = uniformizer k) : ord k x = 1 := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (uniformizer k) ≠ 0 := by simp
  have key : φ (uniformizer k) = WithZero.exp (-1) := by
    apply le_antisymm
    · have : φ (uniformizer k) < φ 1 := φ.strictMono uniformizer_lt_one
      rw [map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      omega
    · have : φ.symm (WithZero.exp (-1)) ≤ uniformizer k := by
        rw [le_uniformizer_iff, ← map_one φ.symm]
        exact φ.symm.strictMono (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
      simpa using φ.strictMono.monotone this
  simp [ord, hx, φ, key]

variable {k} in

theorem ord_eq_zero_iff {x : kˣ} : ord k x = 0 ↔ valuation k (x : k) = 1 := by
  refine ⟨fun h => ?_, ord_eq_zero⟩
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (valuation k (x : k)) ≠ 0 := by simp
  have h1 : WithZero.log (φ (valuation k (x : k))) = 0 := neg_eq_zero.1 h
  apply φ.strictMono.injective
  rw [map_one, ← WithZero.exp_log h0, h1, WithZero.exp_zero]

def unrChar (α : ℂˣ) : kˣ →* ℂˣ where
  toFun x := α ^ ord k x
  map_one' := by rw [ord_eq_zero (by simp), zpow_zero]
  map_mul' x y := by rw [ord_mul, _root_.zpow_add]

theorem unrChar_apply (α : ℂˣ) (x : kˣ) : unrChar k α x = α ^ ord k x := rfl

theorem isUnram_unrChar (α : ℂˣ) : IsUnram (unrChar k α) := fun x hx => by
  rw [unrChar_apply, ord_eq_zero hx, zpow_zero]

theorem unrChar_uniformizer (α : ℂˣ) {x : kˣ} (hx : valuation k (x : k) = uniformizer k) :
    unrChar k α x = α := by
  rw [unrChar_apply, ord_eq_one hx, zpow_one]

variable {k} in

theorem eq_unrChar {χ : kˣ →* ℂˣ} (h : IsUnram χ) {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) : χ = unrChar k (χ ϖ) := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  refine MonoidHom.ext fun x => ?_
  have h1 : o (x / ϖ ^ ord k x) = 1 := by
    rw [map_div, map_zpow, show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd (ord_eq_one hϖ), ← ofAdd_zsmul,
      smul_eq_mul, mul_one]
    exact div_self' _
  have h2 := h _ (ord_eq_zero_iff.1 (ofAdd_eq_one.1 h1))
  rw [map_div, map_zpow, div_eq_one] at h2
  exact h2

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

section Det

variable {R : Type} [CommRing R]

def detChar (n : Type) [Fintype n] [DecidableEq n] (χ : Rˣ →* ℂˣ) : GL n R →* ℂˣ :=
  χ.comp GeneralLinearGroup.det

@[simp] theorem detChar_apply (χ : Rˣ →* ℂˣ) (g : GL n R) :
    detChar n χ g = χ (GeneralLinearGroup.det g) := rfl

def detRep (n : Type) [Fintype n] [DecidableEq n] (χ : Rˣ →* ℂˣ) : Representation ℂ (GL n R) ℂ :=
  ofChar (detChar n χ)

theorem continuous_glDet [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (GeneralLinearGroup.det : GL n R → Rˣ) := by
  refine Units.continuous_iff.2 ⟨Units.continuous_val.matrix_det, ?_⟩
  simp only [← map_inv]
  exact Units.continuous_coe_inv.matrix_det

theorem IsSmoothChar.detChar [TopologicalSpace R] [IsTopologicalRing R] {χ : Rˣ →* ℂˣ}
    (h : IsSmoothChar χ) : IsSmoothChar (detChar n χ) :=
  h.comp _ continuous_glDet

def HasCentralChar (π : Representation ℂ (GL n R) V) (ω : Rˣ →* ℂˣ) : Prop :=
  ∀ z v, π (GeneralLinearGroup.scalar n z) v = (ω z : ℂ) • v

def torusChar {n : Type} [Fintype n] (χ : n → Rˣ →* ℂˣ) : (n → Rˣ) →* ℂˣ :=
  ∏ i, (χ i).comp (Pi.evalMonoidHom (fun _ => Rˣ) i)

@[simp] theorem torusChar_apply {n : Type} [Fintype n] (χ : n → Rˣ →* ℂˣ) (t : n → Rˣ) :
    torusChar χ t = ∏ i, χ i (t i) := by
  simp [torusChar, MonoidHom.finsetProd_apply]

end Det

def modExp (m : α → Type) [∀ a, Fintype (m a)] (a : α) : ℤ :=
  (∑ b with a < b, (Fintype.card (m b) : ℤ)) - ∑ b with b < a, (Fintype.card (m b) : ℤ)

def modulus (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (g : Levi k m) : ℝ :=
  ∏ a, nabs k (GeneralLinearGroup.det (g a)) ^ modExp m a

def deltaHalf (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] : Levi k m →* ℂˣ :=
  ∏ a, (detChar (m a) (absPow k ((modExp m a : ℂ) / 2))).comp (Pi.evalMonoidHom (fun a => GL (m a) k) a)

theorem deltaHalf_apply (g : Levi k m) :
    deltaHalf k m g = ∏ a, absPow k ((modExp m a : ℂ) / 2) (GeneralLinearGroup.det (g a)) := by
  simp [deltaHalf, MonoidHom.finsetProd_apply]

theorem modulus_pos (g : Levi k m) : 0 < modulus k m g :=
  Finset.prod_pos fun _ _ => zpow_pos (nabs_pos' k _) _

theorem val_deltaHalf (g : Levi k m) : (deltaHalf k m g : ℂ) = (√(modulus k m g) : ℝ) := by
  rw [deltaHalf_apply, Units.coe_prod, modulus,
    Real.sqrt_prod _ fun _ _ => (zpow_pos (nabs_pos' k _) _).le, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  have : ((modExp m a : ℂ) / 2) = (((modExp m a : ℝ) * (1 / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [this, val_absPow_ofReal, Real.sqrt_eq_rpow, Real.rpow_mul (nabs_pos' k _).le, Real.rpow_intCast]

theorem isSmoothChar_deltaHalf : IsSmoothChar (deltaHalf k m) := by
  unfold deltaHalf
  refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) ?_ fun a _ => ?_
  · unfold IsSmoothChar; simp
  · exact (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar.comp _ (continuous_apply a)

variable {k}

abbrev IndSp (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) : Type :=
  smoothPart (ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)))

def parInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    Representation ℂ (GL n k) (IndSp e ρ) :=
  smInd (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e))

theorem parInd_law (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W)
    (f : IndSp e ρ)
    (p : parab k e) (g : GL n k) :
    f.1.1 (p * g) = (deltaHalf k m (leviProj k e p) : ℂ) • ρ (leviProj k e p) (f.1.1 g) :=
  f.1.2 p g

@[simp] theorem parInd_apply (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) (g x : GL n k)
    (f : IndSp e ρ) :
    (parInd e ρ g f).1.1 x = f.1.1 (x * g) := rfl

theorem isSmooth_parInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    IsSmooth (parInd e ρ) := isSmooth_smoothRep _

def parIndMap (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) V}
    {σ : Representation ℂ (Levi k m) W} (f : ρ.IntertwiningMap σ) :
    (parInd e ρ).IntertwiningMap (parInd e σ) :=
  smIndMap (compMap (twistMap f _) _)

def jacU {R : Type} [CommRing R] (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n R) V) :
    Representation ℂ (Levi R m) (Jacquet π (unipRad R e)) :=
  jacquet π (unipRad R e) (leviEmb R e) (leviEmb_mem_normalizer R e)

def jac (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n k) V) :
    Representation ℂ (Levi k m) (Jacquet π (unipRad k e)) :=
  twist (jacU e π) (deltaHalf k m)⁻¹

theorem jac_mk (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n k) V) (g : Levi k m) (v : V) :
    jac e π g (Submodule.Quotient.mk v) =
      (((deltaHalf k m g)⁻¹ : ℂˣ) : ℂ) • Submodule.Quotient.mk (π (leviEmb k e g) v) := rfl

theorem isSmooth_jacU (e : (Σ a, m a) ≃ n) {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) :
    IsSmooth (jacU e π) :=
  isSmooth_jacquet hπ _ _ _ (continuous_leviEmb k e)

theorem isSmooth_jac (e : (Σ a, m a) ≃ n) {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) :
    IsSmooth (jac e π) :=
  isSmooth_twist (isSmooth_jacU e hπ) (isSmoothChar_deltaHalf k).inv

def jacMap (e : (Σ a, m a) ≃ n) {π : Representation ℂ (GL n k) V} {τ : Representation ℂ (GL n k) W}
    (f : π.IntertwiningMap τ) : (jac e π).IntertwiningMap (jac e τ) :=
  twistMap (jacquetMap f _ _ _) _

omit [∀ a, DecidableEq (m a)] in

theorem modExp_opp (a : α) :
    modExp (fun a : αᵒᵈ => m (OrderDual.ofDual a)) (OrderDual.toDual a) = -modExp m a := by
  unfold modExp
  rw [neg_sub]
  rfl

theorem deltaHalf_opp (g : Levi k m) :
    deltaHalf k (fun a : αᵒᵈ => m (OrderDual.ofDual a)) g = (deltaHalf k m g)⁻¹ := by
  rw [deltaHalf_apply k g, ← Finset.prod_inv_distrib]
  refine (deltaHalf_apply k (m := fun a : αᵒᵈ => m (OrderDual.ofDual a)) g).trans
    (Finset.prod_congr rfl fun a _ => ?_)
  have key : ∀ (z : ℤ) (x : kˣ), z = -modExp m a →
      absPow k ((z : ℂ) / 2) x = (absPow k ((modExp m a : ℂ) / 2) x)⁻¹ := by
    rintro _ x rfl
    rw [Int.cast_neg, neg_div, absPow_neg]
    rfl
  exact key _ _ (modExp_opp (m := m) a)

abbrev IndSpLower (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) : Type :=
  smoothPart (ind (parabLower k e) ((twist ρ (deltaHalf k m)⁻¹).comp (leviProjLower k e)))

def parIndLower (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    Representation ℂ (GL n k) (IndSpLower e ρ) :=
  smInd (parabLower k e) ((twist ρ (deltaHalf k m)⁻¹).comp (leviProjLower k e))

@[simp] theorem parIndLower_apply (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W)
    (g x : GL n k) (f : IndSpLower e ρ) : (parIndLower e ρ g f).1.1 x = f.1.1 (x * g) := rfl

def jacLower (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n k) V) :
    Representation ℂ (Levi k m) (Jacquet π (unipRadLower k e)) :=
  twist (jacquet π (unipRadLower k e) (leviEmb k e) (leviEmb_mem_normalizer_lower k e)) (deltaHalf k m)

theorem jacLower_eq (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n k) V) (g : Levi k m) :
    jacLower e π g = jac (opp e) π g := by
  have h : deltaHalf k m g = (deltaHalf k (fun a : αᵒᵈ => m (OrderDual.ofDual a)) g)⁻¹ :=
    ((inv_inv _).symm.trans (congrArg _ (deltaHalf_opp g).symm))
  exact congrArg (fun c : ℂˣ => (c : ℂ) • jacU (opp e) π g) h

theorem isSmooth_jacLower (e : (Σ a, m a) ≃ n) {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) :
    IsSmooth (jacLower e π) :=
  isSmooth_twist (isSmooth_jacquet hπ _ _ _ (continuous_leviEmb k e)) (isSmoothChar_deltaHalf k)

def multiProd (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (π : ∀ a, Representation ℂ (GL (m a) k) (X a)) :=
  parInd e (piTensor π)

section Two

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem deltaHalf_two (g : GL a k × GL b k) :
    deltaHalf k (Two a b) (leviTwo k a b g) =
      absPow k ((Fintype.card b : ℂ) / 2) (GeneralLinearGroup.det g.1) *
        absPow k (-(Fintype.card a : ℂ) / 2) (GeneralLinearGroup.det g.2) := by
  have h1 : modExp (Two a b) false = Fintype.card b := by
    simp [modExp, Finset.sum_filter]
  have h2 : modExp (Two a b) true = -Fintype.card a := by
    simp [modExp, Finset.sum_filter]
  rw [deltaHalf_apply, Fintype.prod_bool, h1, h2, mul_comm]
  push_cast
  rfl

def ind₂ (e : a ⊕ b ≃ n) (ρ : Representation ℂ (GL a k × GL b k) W) :=
  parInd (two e) (ρ.comp (leviTwo k a b).symm.toMonoidHom)

def ind₂Lower (e : a ⊕ b ≃ n) (ρ : Representation ℂ (GL a k × GL b k) W) :=
  parIndLower (two e) (ρ.comp (leviTwo k a b).symm.toMonoidHom)

def jacU₂ (e : a ⊕ b ≃ n) (π : Representation ℂ (GL n k) V) :
    Representation ℂ (GL a k × GL b k) (Jacquet π (unipRad k (two e))) :=
  (jacU (two e) π).comp (leviTwo k a b).toMonoidHom

def jac₂ (e : a ⊕ b ≃ n) (π : Representation ℂ (GL n k) V) :
    Representation ℂ (GL a k × GL b k) (Jacquet π (unipRad k (two e))) :=
  (jac (two e) π).comp (leviTwo k a b).toMonoidHom

def jac₂Lower (e : a ⊕ b ≃ n) (π : Representation ℂ (GL n k) V) :
    Representation ℂ (GL a k × GL b k) (Jacquet π (unipRadLower k (two e))) :=
  (jacLower (two e) π).comp (leviTwo k a b).toMonoidHom

theorem isSmooth_jac₂ (e : a ⊕ b ≃ n) {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) :
    IsSmooth (jac₂ e π) :=
  isSmooth_comp (isSmooth_jac _ hπ) _ (continuous_leviTwo k)

theorem isSmooth_jac₂Lower (e : a ⊕ b ≃ n) {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) :
    IsSmooth (jac₂Lower e π) :=
  isSmooth_comp (isSmooth_jacLower _ hπ) _ (continuous_leviTwo k)

def prod₂ {r t : ℕ} (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :=
  ind₂ (stdSum (rfl : r + t = r + t)) (extTensor π₁ π₂)

theorem isSmooth_prod₂ {r t : ℕ} (π₁ : Representation ℂ (GL (Fin r) k) V)
    (π₂ : Representation ℂ (GL (Fin t) k) W) : IsSmooth (prod₂ π₁ π₂) := isSmooth_parInd _ _

theorem jac₂_detRep (e : a ⊕ b ≃ n) (χ : kˣ →* ℂˣ) (g : GL a k × GL b k)
    (x : Jacquet (detRep n χ) (unipRad k (two e))) :
    jac₂ e (detRep n χ) g x =
      ((detChar a (χ * absPow k (-(Fintype.card b : ℂ) / 2)) g.1 *
        detChar b (χ * absPow k ((Fintype.card a : ℂ) / 2)) g.2 : ℂˣ) : ℂ) • x := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h := jac_mk (two e) (detRep n χ) (leviTwo k a b g) v
  have h2 : detRep n χ (leviEmb k (two e) (leviTwo k a b g)) v =
      ((χ (GeneralLinearGroup.det g.1) * χ (GeneralLinearGroup.det g.2) : ℂˣ) : ℂ) • v := by
    rw [← map_mul, ← det_emb₂ k e g]
    exact ofChar_apply _ _ _
  rw [h2, Submodule.Quotient.mk_smul, smul_smul, deltaHalf_two] at h
  refine h.trans ?_
  congr 1
  rw [← Units.val_mul]
  congr 1
  simp only [detChar_apply, MonoidHom.mul_apply, neg_div, absPow_neg, MonoidHom.inv_apply, mul_inv,
    inv_inv]
  simp only [mul_comm, mul_left_comm, mul_assoc]

end Two

theorem twKer_detRep {R : Type} [CommRing R] (e : (Σ a, m a) ≃ n) (χ : Rˣ →* ℂˣ) :
    twKer (detRep n χ) (unipRad R e) 1 = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨u, v, rfl⟩
  simp [detRep, det_eq_one_of_mem_unipRad R u.2]

def IsCuspidal (π : Representation ℂ (GL n k) V) : Prop :=
  IsSmooth π ∧ ∀ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ n), unipRad k e ≠ ⊥ →
    Subsingleton (Jacquet π (unipRad k e))

def IsCuspSupport (π : Representation ℂ (GL n k) V) {s : ℕ} (d : Fin s → ℕ) {X : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) : Prop :=
  π.IsIrreducible ∧ (∀ a, 0 < d a ∧ (σ a).IsIrreducible ∧ IsCuspidal (σ a)) ∧
    ∃ e : (Σ a, Fin (d a)) ≃ n, IsSubquotient π (multiProd e σ)

def InSupport (π : Representation ℂ (GL n k) V) (χ : kˣ →* ℂˣ) : Prop :=
  ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ n) (a : Fin s), d a = 1 ∧
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y)
      (σ : Representation ℂ (Levi k fun a => Fin (d a)) Y),
      σ.IsIrreducible ∧ IsSubquotient σ (jac e π) ∧
        ∀ (g : GL (Fin (d a)) k) (y : Y),
          σ (Pi.mulSingle a g) y = (χ (GeneralLinearGroup.det g) : ℂ) • y

section Borel

variable [LinearOrder n]

theorem modulus_torus {n : Type} [Fintype n] [LinearOrder n] (t : n → kˣ) :
    modulus k (fun _ : n => Unit) (leviTorus k n t) =
      ∏ i, ∏ j with i < j, nabs k (t i / t j) := by
  have hd : ∀ i, GeneralLinearGroup.det (leviTorus k n t i) = t i :=
    congrFun ((leviTorus k n).left_inv t)
  have hq : ∀ x y : kˣ, nabs k (x / y) = nabs k x / nabs k y := fun x y => by simp [nabs]
  simp only [modulus, hd, modExp, hq, Finset.prod_div_distrib, Fintype.card_unique, Nat.cast_one,
    Finset.sum_const, nsmul_eq_mul, mul_one, zpow_sub₀ (nabs_pos' k _).ne', zpow_natCast,
    Finset.prod_const]
  congr 1
  simp only [← Finset.prod_const, Finset.prod_filter]
  exact Finset.prod_comm

def indB (ρ : Representation ℂ (n → kˣ) W) :=
  parInd (points n) (ρ.comp (leviTorus k n).symm.toMonoidHom)

def jacBU (π : Representation ℂ (GL n k) V) : Representation ℂ (n → kˣ) (Jacquet π (unipB k n)) :=
  (jacU (points n) π).comp (leviTorus k n).toMonoidHom

def jacB (π : Representation ℂ (GL n k) V) : Representation ℂ (n → kˣ) (Jacquet π (unipB k n)) :=
  (jac (points n) π).comp (leviTorus k n).toMonoidHom

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem jacBU_mk (π : Representation ℂ (GL n k) V) (t : n → kˣ) (v : V) :
    jacBU π t (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π (diagT k n t) v) := rfl

theorem isSmooth_jacBU {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) : IsSmooth (jacBU π) :=
  isSmooth_comp (isSmooth_jacU _ hπ) _ (continuous_leviTorus k n)

theorem isSmooth_jacB {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) : IsSmooth (jacB π) :=
  isSmooth_comp (isSmooth_jac _ hπ) _ (continuous_leviTorus k n)

def prinSeries (χ : n → kˣ →* ℂˣ) := indB (ofChar (torusChar χ))

variable (k n)

def iwahori : Subgroup (GL n k) :=
  ((borel 𝓀[k] n).comap (GeneralLinearGroup.map (n := n) (IsLocalRing.residue 𝒪[k]))).map
    (GeneralLinearGroup.map (n := n) (algebraMap 𝒪[k] k))

def torusO (n : Type) : Subgroup (n → kˣ) where
  carrier := {t | ∀ i, valuation k (t i : k) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro s t hs ht i
    simp [hs i, ht i]
  inv_mem' := by
    intro t ht i
    simp [ht i]

theorem iwahori_le_KO : iwahori k n ≤ KO k n := Subgroup.map_le_range _ _

theorem KOne_le_iwahori : KOne k n ≤ iwahori k n :=
  Subgroup.map_mono fun g hg => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hg]
    exact one_mem _

variable {k n}

theorem mem_iwahori {g : GL n k} :
    g ∈ iwahori k n ↔ g ∈ KO k n ∧ ∀ i j, j < i → valuation k ((g : Matrix n n k) i j) < 1 := by
  have key : ∀ x : 𝒪[k], IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
    intro x
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
    exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, rfl⟩, fun i j hij => (key _).1 ((mem_borel _).1 hh i j hij)⟩
  · rintro ⟨⟨h, rfl⟩, hh⟩
    exact ⟨h, (mem_borel _).2 fun i j hij => (key _).2 (hh i j hij), rfl⟩

theorem diagT_mem_iwahori {t : n → kˣ} (ht : t ∈ torusO k n) : diagT k n t ∈ iwahori k n := by
  let u : n → 𝒪[k]ˣ := fun i => ⟨⟨t i, (ht i).le⟩, ⟨((t i)⁻¹ : kˣ), (inv_mem ht i).le⟩,
    Subtype.ext (t i).mul_inv, Subtype.ext (t i).inv_mul⟩
  refine mem_iwahori.2 ⟨⟨diagT _ n u, ?_⟩, fun i j hij => ?_⟩
  · ext i j
    show algebraMap 𝒪[k] k ((diagT _ n u : Matrix n n 𝒪[k]) i j) = _
    rw [val_diagT, val_diagT, diagonal_apply, diagonal_apply]
    split_ifs
    · rfl
    · simp
  · rw [val_diagT, diagonal_apply_ne _ hij.ne']
    simp

def iwahoriProj (π : Representation ℂ (GL n k) V) :
    fixed π (iwahori k n) →ₗ[ℂ] fixed (jacBU π) (torusO k n) :=
  (twKer π (unipB k n) 1).mkQ.restrict fun v hv t => by
    have h : π (diagT k n t) v = v := by simpa using hv ⟨_, diagT_mem_iwahori t.2⟩
    show jacBU π t (Submodule.Quotient.mk v) = _
    rw [jacBU_mk, h]
    simp

def jacBUFixed (π : Representation ℂ (GL n k) V) :
    Representation ℂ (n → kˣ) (fixed (jacBU π) (torusO k n)) :=
  onFixed (jacBU π) (torusO k n) (MonoidHom.id _) fun _ => by
    rw [Subgroup.normalizer_eq_top]; trivial

def expMult (π : Representation ℂ (GL n k) V) (χ : (n → kˣ) →* ℂˣ) : ℕ∞ :=
  jhMult (ofChar χ) (jacBUFixed π)

omit [LinearOrder n] in

def IsSpherical (π : Representation ℂ (GL n k) V) : Prop := IsSphericalFor π (KO k n)

def HasSatake (π : Representation ℂ (GL n k) V) (α : n → ℂˣ) : Prop :=
  π.IsIrreducible ∧ IsSpherical π ∧ IsSubquotient π (prinSeries fun i => unrChar k (α i))

end Borel

end Local

section Examples

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

def detLevi (e : (Σ a, m a) ≃ n) (χ : kˣ →* ℂˣ) : Levi k m →* ℂˣ :=
  (detChar n χ).comp (leviEmb k e) * (deltaHalf k m)⁻¹

theorem detLevi_apply (e : (Σ a, m a) ≃ n) (χ : kˣ →* ℂˣ) (g : Levi k m) :
    detLevi e χ g = ∏ a, (χ * absPow k (-(modExp m a : ℂ) / 2)) (GeneralLinearGroup.det (g a)) := by
  simp [detLevi, det_leviEmb, deltaHalf_apply, neg_div, absPow_neg, Finset.prod_mul_distrib]

theorem isSubquotient_jac_detRep (e : (Σ a, m a) ≃ n) (χ : kˣ →* ℂˣ) :
    IsSubquotient (ofChar (detLevi e χ)) (jac e (detRep n χ)) := by
  refine .of_surjective ⟨(twKer (detRep n χ) (unipRad k e) 1).liftQ LinearMap.id
    (by rw [twKer_detRep]; exact bot_le), fun g => ?_⟩ fun x => ⟨Submodule.Quotient.mk x, rfl⟩
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  show (((deltaHalf k m g)⁻¹ : ℂˣ) : ℂ) • detRep n χ (leviEmb k e g) v = ofChar (detLevi e χ) g v
  simp [detRep, detLevi, mul_comm, mul_left_comm]

theorem isSubquotient_detRep_parInd (e : (Σ a, m a) ≃ n) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsSubquotient (detRep n χ) (parInd e (ofChar (detLevi e χ))) := by
  let f : ℂ →ₗ[ℂ] IndSp e (ofChar (detLevi e χ)) :=
    { toFun := fun c => ⟨⟨fun g => (detChar n χ g : ℂ) * c, fun p g => by
          have : GeneralLinearGroup.det (leviEmb k e (leviProj k e p)) =
              GeneralLinearGroup.det (p : GL n k) := by rw [det_leviEmb, det_parab]
          show _ = (deltaHalf k m _ : ℂ) • ofChar (detLevi e χ) (leviProj k e p) _
          simp [detLevi, this, mul_assoc, mul_left_comm (deltaHalf k m (leviProj k e p) : ℂ)]⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset
          (IsOpen.mem_nhds (hχ.detChar (n := n)) (one_mem _)) fun g hg => by
            have hg' : detChar n χ g = 1 := hg
            apply Subtype.ext
            funext x
            show (detChar n χ (x * g) : ℂ) * c = (detChar n χ x : ℂ) * c
            rw [map_mul, hg', mul_one])⟩
      map_add' := fun c d => by ext g; exact mul_add _ _ _
      map_smul' := fun c d => by ext g; exact mul_left_comm _ _ _ }
  refine .of_injective ⟨f, fun g => ?_⟩ fun c d h => ?_
  · refine LinearMap.ext fun c => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show (detChar n χ x : ℂ) * (detRep n χ g c) = (detChar n χ (x * g) : ℂ) * c
    simp [detRep, mul_assoc]
  · simpa [f] using congrFun (congrArg (fun φ => φ.1.1) h) 1

theorem modExp_fin {N : ℕ} (X : Fin N → Type) [∀ i, Fintype (X i)] (hX : ∀ i, Fintype.card (X i) = 1)
    (i : Fin N) : modExp X i = (N : ℤ) - 1 - 2 * (i : ℕ) := by
  have h1 : Finset.univ.filter (fun b => i < b) = Finset.Ioi i := by ext; simp
  have h2 : Finset.univ.filter (fun b => b < i) = Finset.Iio i := by ext; simp
  have := i.2
  simp only [modExp, hX, h1, h2, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio, Nat.cast_one,
    nsmul_eq_mul, mul_one]
  omega

theorem inSupport_detRep {N : ℕ} (χ : kˣ →* ℂˣ) (i : Fin N) :
    InSupport (detRep (Fin N) χ) (χ * absPow k (((i : ℕ) : ℂ) - ((N : ℂ) - 1) / 2)) := by
  let e : (Σ _ : Fin N, Fin 1) ≃ Fin N := Equiv.sigmaUnique _ _
  refine ⟨N, fun _ => 1, e, i, rfl, ℂ, inferInstance, inferInstance, ofChar (detLevi e χ),
    isIrreducible_ofChar _, isSubquotient_jac_detRep e χ, fun g y => ?_⟩
  rw [ofChar_apply, detLevi_apply, Finset.prod_eq_single i, Pi.mulSingle_eq_same,
    modExp_fin _ (fun _ => by simp), smul_eq_mul]
  · congr 6
    push_cast
    ring
  · intro j _ hj
    rw [Pi.mulSingle_eq_of_ne hj, map_one, map_one]
  · simp

theorem isSpherical_detRep {χ : kˣ →* ℂˣ} (h : IsUnram χ) : IsSpherical (detRep n χ) := by
  refine (Submodule.ne_bot_iff _).2 ⟨1, ?_, one_ne_zero⟩
  rintro ⟨_, g, rfl⟩
  have : χ (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g)) = 1 := by
    apply h
    have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
        algebraMap 𝒪[k] k (GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
      ((algebraMap 𝒪[k] k).map_det _).symm
    rw [h1]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
  simp [detRep, this]

theorem hasSatake_detRep {N : ℕ} {χ : kˣ →* ℂˣ} (h : IsUnram χ) {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) :
    HasSatake (detRep (Fin N) χ)
      fun i => χ ϖ * absPow k (((i : ℕ) : ℂ) - ((N : ℂ) - 1) / 2) ϖ := by
  refine ⟨isIrreducible_ofChar _, isSpherical_detRep h, ?_⟩
  have key : (ofChar (torusChar fun i : Fin N => unrChar k
      (χ ϖ * absPow k (((i : ℕ) : ℂ) - ((N : ℂ) - 1) / 2) ϖ))).comp
        (leviTorus k (Fin N)).symm.toMonoidHom = ofChar (detLevi (points (Fin N)) χ) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun y => ?_
    show ofChar _ _ y = _
    rw [ofChar_apply, ofChar_apply, detLevi_apply, torusChar_apply]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    have hu : IsUnram (χ * absPow k (((i : ℕ) : ℂ) - ((N : ℂ) - 1) / 2)) := fun x hx => by
      rw [MonoidHom.mul_apply, h x hx, isUnram_absPow k _ x hx, one_mul]
    rw [← MonoidHom.mul_apply, ← eq_unrChar hu hϖ, modExp_fin _ (fun _ => by simp)]
    congr 3
    push_cast
    ring
  have := isSubquotient_detRep_parInd (points (Fin N)) (isSmoothChar_of_isUnram h)
  rw [← key] at this
  exact this

theorem isCuspidal_detRep_one {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsCuspidal (detRep (Fin 1) χ) := by
  refine ⟨(isSmooth_ofChar_iff _).2 hχ.detChar, fun s d e he => absurd ?_ he⟩
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
  ext i j
  obtain rfl : i = j := Subsingleton.elim _ _
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  simpa using (mem_unipRad.1 hu).2 a i i

theorem not_isCuspidal_detRep_two (χ : kˣ →* ℂˣ) : ¬ IsCuspidal (detRep (Fin 2) χ) := by
  intro h
  let e : (Σ _ : Fin 2, Fin 1) ≃ Fin 2 := Equiv.sigmaUnique _ _
  let u : GL (Fin 2) k := GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by simp)
  have hu : u ∈ unipRad k e := by
    refine mem_unipRad.2 ⟨mem_parab_iff.2 fun a b i j hab => ?_, fun a i j => ?_⟩
    · show (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) k) a b = 0
      fin_cases a <;> fin_cases b <;> simp at hab ⊢
    · show (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) k) a a = _
      rw [Subsingleton.elim i j]
      fin_cases a <;> simp
  have hne : unipRad k e ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.mem_bot] at hu
    have : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) k) 0 1 = (1 : Matrix (Fin 2) (Fin 2) k) 0 1 :=
      congrArg (fun g : GL (Fin 2) k => (g : Matrix (Fin 2) (Fin 2) k) 0 1) hu
    simp at this
  have := Submodule.Quotient.subsingleton_iff.1 (h.2 2 (fun _ => 1) e hne)
  rw [twKer_detRep] at this
  exact bot_ne_top this

example (χ : kˣ →* ℂˣ) : HasCentralChar (detRep n χ) (χ ^ Fintype.card n) := fun z v => by
  have : GeneralLinearGroup.det (GeneralLinearGroup.scalar n z) = z ^ Fintype.card n := by
    ext; simp [GeneralLinearGroup.scalar]
  simp [detRep, this]

example {χ : kˣ →* ℂˣ} (h : IsUnitaryChar χ) : IsUnitarisable (detRep n χ) :=
  (isUnitarisable_ofChar_iff _).2 fun _ => h _

example {G : Type} [Group G] (χ : G →* ℂˣ) : 1 ≤ jhMult (ofChar χ) (ofChar χ) := by
  refine le_iSup₂_of_le 1 ⟨fun _ => ⊤, fun _ => ⊥, fun _ => bot_le,
    fun i j h => absurd (Subsingleton.elim i j) h.ne, fun _ => ⟨.mk ((Submodule.quotEquivOfEqBot _
      (by ext; simp [show (⊥ : Subrepresentation (ofChar χ)).toSubmodule = ⊥ from rfl])).trans
        Submodule.topEquiv) fun g => ?_⟩⟩ le_rfl
  exact Submodule.linearMap_qext _ rfl

end Examples

end GlobalTheory.SmGL

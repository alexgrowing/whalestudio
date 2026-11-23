import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemShaKernelIffLocallyTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsingletonComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerSimilitudeBaseChange

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LKInv

open GlobalTheory.LKTorus

section General

variable (k : Type) [Field k] {B L : Type} [Ring B] [StarRing B] [Algebra k B] [CommRing L] [Algebra k L]

def StConj (γ₀ γ : Bˣ) : Prop :=
  ∃ ν : kˣ, (γ₀ : B) * star (γ₀ : B) = algebraMap k B ν ∧ (γ : B) * star (γ : B) = algebraMap k B ν ∧
    ∃ g : Bˣ, (g : B) * γ₀ = γ * g

variable {k}

theorem star_mul_conj {γ₀ γ g : Bˣ} (n : B) (hn : ∀ x : B, n * x = x * n)
    (h0 : (γ₀ : B) * star (γ₀ : B) = n) (h1 : (γ : B) * star (γ : B) = n) (hg : (g : B) * γ₀ = γ * g) :
    star (g : B) * γ = γ₀ * star (g : B) := by
  have hu : IsUnit (star (γ : B)) := (Units.isUnit γ).star
  apply hu.mul_right_cancel
  calc star (g : B) * γ * star (γ : B) = star (g : B) * n := by rw [mul_assoc, h1]
    _ = n * star (g : B) := (hn _).symm
    _ = γ₀ * star (γ₀ : B) * star (g : B) := by rw [h0]
    _ = γ₀ * star ((g : B) * γ₀) := by rw [star_mul, mul_assoc]
    _ = γ₀ * star ((γ : B) * g) := by rw [hg]
    _ = γ₀ * star (g : B) * star (γ : B) := by rw [star_mul, mul_assoc]

theorem star_mul_self_comm {γ₀ γ g : Bˣ} (n : B) (hn : ∀ x : B, n * x = x * n)
    (h0 : (γ₀ : B) * star (γ₀ : B) = n) (h1 : (γ : B) * star (γ : B) = n) (hg : (g : B) * γ₀ = γ * g) :
    ((star g * g : Bˣ) : B) * γ₀ = γ₀ * ((star g * g : Bˣ) : B) := by
  rw [Units.val_mul, Units.coe_star, mul_assoc, hg, ← mul_assoc, star_mul_conj n hn h0 h1 hg, mul_assoc]

theorem inv_comm {γ₀ : B} (u : Bˣ) (hu : (u : B) * γ₀ = γ₀ * u) :
    ((u⁻¹ : Bˣ) : B) * γ₀ = γ₀ * ((u⁻¹ : Bˣ) : B) :=
  calc ((u⁻¹ : Bˣ) : B) * γ₀ = ((u⁻¹ : Bˣ) : B) * (γ₀ * u) * ((u⁻¹ : Bˣ) : B) := by
        rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
    _ = ((u⁻¹ : Bˣ) : B) * ((u : B) * γ₀) * ((u⁻¹ : Bˣ) : B) := by rw [hu]
    _ = γ₀ * ((u⁻¹ : Bˣ) : B) := by rw [← mul_assoc, Units.inv_mul, one_mul]

def liftUnit (ι : L →ₐ[k] B) (hι : Function.Injective ι) (γ₀ : B)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (u : Bˣ) (hu : (u : B) * γ₀ = γ₀ * u) : Lˣ where
  val := ((hcent u).1 hu).choose
  inv := ((hcent ((u⁻¹ : Bˣ) : B)).1 (inv_comm u hu)).choose
  val_inv := hι (by
    have h1 := ((hcent u).1 hu).choose_spec
    have h2 := ((hcent ((u⁻¹ : Bˣ) : B)).1 (inv_comm u hu)).choose_spec
    rw [map_mul, h1, h2, Units.mul_inv, map_one])
  inv_val := hι (by
    have h1 := ((hcent u).1 hu).choose_spec
    have h2 := ((hcent ((u⁻¹ : Bˣ) : B)).1 (inv_comm u hu)).choose_spec
    rw [map_mul, h1, h2, Units.inv_mul, map_one])

@[simp] theorem ι_liftUnit (ι : L →ₐ[k] B) (hι : Function.Injective ι) (γ₀ : B)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (u : Bˣ) (hu : (u : B) * γ₀ = γ₀ * u) :
    ι ((liftUnit ι hι γ₀ hcent u hu : Lˣ) : L) = u :=
  ((hcent u).1 hu).choose_spec

def cocyc (ι : L →ₐ[k] B) (hι : Function.Injective ι) (γ₀ : B)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (c : L →ₐ[k] L)
    (hc : ∀ a, ι (c a) = star (ι a)) (g : Bˣ) (hg : ((star g * g : Bˣ) : B) * γ₀ = γ₀ * ((star g * g : Bˣ) : B)) :
    fixU k c :=
  ⟨liftUnit ι hι γ₀ hcent (star g * g) hg, hι (by
    rw [hc, ι_liftUnit, Units.val_mul, Units.coe_star, star_mul, star_star])⟩

@[simp] theorem ι_cocyc (ι : L →ₐ[k] B) (hι : Function.Injective ι) (γ₀ : B)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (c : L →ₐ[k] L)
    (hc : ∀ a, ι (c a) = star (ι a)) (g : Bˣ) (hg : ((star g * g : Bˣ) : B) * γ₀ = γ₀ * ((star g * g : Bˣ) : B)) :
    ι (((cocyc ι hι γ₀ hcent c hc g hg : fixU k c) : Lˣ) : L) = star (g : B) * g := by
  simp [cocyc]

section Inv

variable (ι : L →ₐ[k] B) (hι : Function.Injective ι) (γ₀ : Bˣ)
  (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (c : L →ₐ[k] L) (hc : ∀ a, ι (c a) = star (ι a))

theorem mk_eq_mk_of {c : L →ₐ[k] L} (a b : fixU k c) (t : kˣ) (y : Lˣ)
    (h : ((b : Lˣ) : L) = algebraMap k L t * ((a : Lˣ) : L) * ((y : L) * c y)) :
    (QuotientGroup.mk a : H1 k c) = QuotientGroup.mk b := by
  apply QuotientGroup.eq.2
  rw [GlobalTheory.LKTorus.Model.mem_normSub_iff]
  refine ⟨t, y, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, h]
  calc ((((a : Lˣ))⁻¹ : Lˣ) : L) * (algebraMap k L t * ((a : Lˣ) : L) * ((y : L) * c y))
      = algebraMap k L t * ((y : L) * c y) * ((((a : Lˣ))⁻¹ : Lˣ) * (a : Lˣ) : Lˣ) := by
        rw [Units.val_mul]; ring
    _ = _ := by rw [inv_mul_cancel, Units.val_one, mul_one]

theorem StConj.comm {γ₀ γ : Bˣ} (ν : kˣ) (h0 : (γ₀ : B) * star (γ₀ : B) = algebraMap k B ν)
    (h1 : (γ : B) * star (γ : B) = algebraMap k B ν) {g : Bˣ} (hg : (g : B) * γ₀ = γ * g) :
    ((star g * g : Bˣ) : B) * γ₀ = γ₀ * ((star g * g : Bˣ) : B) :=
  star_mul_self_comm _ (fun x => Algebra.commutes _ x) h0 h1 hg

def invCls {γ : Bˣ} (h : StConj k γ₀ γ) : H1 k c :=
  QuotientGroup.mk (cocyc ι hι (γ₀ : B) hcent c hc h.choose_spec.2.2.choose
    (StConj.comm h.choose h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2.choose_spec))

theorem mk_cocyc_eq {γ : Bˣ} (g g' : Bˣ) (hg : (g : B) * γ₀ = γ * g) (hg' : (g' : B) * γ₀ = γ * g')
    (hgc : ((star g * g : Bˣ) : B) * γ₀ = γ₀ * ((star g * g : Bˣ) : B))
    (hgc' : ((star g' * g' : Bˣ) : B) * γ₀ = γ₀ * ((star g' * g' : Bˣ) : B)) :
    (QuotientGroup.mk (cocyc ι hι (γ₀ : B) hcent c hc g hgc) : H1 k c) =
      QuotientGroup.mk (cocyc ι hι (γ₀ : B) hcent c hc g' hgc') := by
  have hq : ((g⁻¹ * g' : Bˣ) : B) * γ₀ = γ₀ * ((g⁻¹ * g' : Bˣ) : B) := by
    have e : (γ : B) = g * γ₀ * ((g⁻¹ : Bˣ) : B) := by
      calc (γ : B) = γ * g * ((g⁻¹ : Bˣ) : B) := by rw [mul_assoc, Units.mul_inv, mul_one]
        _ = _ := by rw [← hg]
    rw [Units.val_mul, mul_assoc, hg', e]
    simp only [← mul_assoc, Units.inv_mul, one_mul]
  set y := liftUnit ι hι (γ₀ : B) hcent (g⁻¹ * g') hq with hy
  have hιy : ι (y : L) = ((g⁻¹ * g' : Bˣ) : B) := ι_liftUnit ι hι _ hcent _ hq
  have hgy : (g' : B) = g * ι (y : L) := by
    rw [hιy, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
  set a := cocyc ι hι (γ₀ : B) hcent c hc g hgc with hadef
  have ha : star (g : B) * g = ι (((a : Lˣ)) : L) := by
    rw [hadef, ι_cocyc]
  apply mk_eq_mk_of _ _ 1 y
  apply hι
  rw [ι_cocyc, hgy]
  calc star ((g : B) * ι (y : L)) * ((g : B) * ι (y : L))
      = star (ι (y : L)) * (star (g : B) * g) * ι (y : L) := by rw [star_mul]; simp only [mul_assoc]
    _ = ι (c (y : L) * ((a : Lˣ) : L) * (y : L)) := by rw [← hc, ha, map_mul, map_mul]
    _ = _ := by congr 1; rw [Units.val_one, map_one, one_mul]; ring

theorem invCls_eq {γ : Bˣ} (h : StConj k γ₀ γ) (g : Bˣ) (hg : (g : B) * γ₀ = γ * g)
    (hgc : ((star g * g : Bˣ) : B) * γ₀ = γ₀ * ((star g * g : Bˣ) : B)) :
    invCls ι hι γ₀ hcent c hc h = QuotientGroup.mk (cocyc ι hι (γ₀ : B) hcent c hc g hgc) :=
  mk_cocyc_eq ι hι γ₀ hcent c hc _ g h.choose_spec.2.2.choose_spec hg _ hgc

theorem StConj.refl' (ν : kˣ) (h0 : (γ₀ : B) * star (γ₀ : B) = algebraMap k B ν) : StConj k γ₀ γ₀ :=
  ⟨ν, h0, h0, 1, by simp⟩

theorem invCls_self (h : StConj k γ₀ γ₀) : invCls ι hι γ₀ hcent c hc h = 1 := by
  have h1 : ((star (1 : Bˣ) * 1 : Bˣ) : B) * γ₀ = γ₀ * ((star (1 : Bˣ) * 1 : Bˣ) : B) := by simp
  have e : cocyc ι hι (γ₀ : B) hcent c hc 1 h1 = 1 := by
    ext
    apply hι
    rw [ι_cocyc]
    simp
  rw [invCls_eq ι hι γ₀ hcent c hc h 1 (by simp) h1, e]
  rfl

theorem mul_star_of_star_mul (x : Bˣ) (n : B) (hn : ∀ y : B, n * y = y * n)
    (h : star (x : B) * x = n) : (x : B) * star (x : B) = n := by
  calc (x : B) * star (x : B) = x * (star (x : B) * x) * ((x⁻¹ : Bˣ) : B) := by
        rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
    _ = n := by rw [h, mul_assoc, hn, ← mul_assoc, Units.mul_inv, one_mul]

def kerG : Set (H1 k c) :=
  {X | ∃ a : fixU k c, (QuotientGroup.mk a : H1 k c) = X ∧
    ∃ (t : kˣ) (g : Bˣ), ι (algebraMap k L t * ((a : Lˣ) : L)) = star (g : B) * g}

end Inv

end General

section Local

variable (S : Type) [Field S] [CharZero S] {B L : Type} [Ring B] [StarRing B] [Algebra ℚ B] [CommRing L]
  [Algebra ℚ L]

def locMap (ι : L →ₐ[ℚ] B) : S ⊗[ℚ] L →ₐ[S] S ⊗[ℚ] B := Algebra.TensorProduct.map (AlgHom.id S S) ι

def locElt (γ₀ : Bˣ) : (S ⊗[ℚ] B)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] S ⊗[ℚ] B).toMonoidHom γ₀

@[simp] theorem coe_locElt (γ₀ : Bˣ) : ((locElt S γ₀ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) = (1 : S) ⊗ₜ[ℚ] (γ₀ : B) :=
  rfl

variable {S}

theorem locMap_cent (ι : L →ₐ[ℚ] B) (hι : Function.Injective ι) (γ₀ : Bˣ)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) :
    Function.Injective (locMap S ι) ∧ ∀ y : S ⊗[ℚ] B, y * (locElt S γ₀ : S ⊗[ℚ] B) = (locElt S γ₀ : S ⊗[ℚ] B) * y ↔
      y ∈ Set.range (locMap S ι) :=
  GlobalTheory.LKCent.baseChange_centralizer ℚ S B L (γ₀ : B) ι hι hcent

theorem locMap_star (ι : L →ₐ[ℚ] B) (c : L →ₐ[ℚ] L) (hc : ∀ a, ι (c a) = star (ι a))
    [StarRing (S ⊗[ℚ] B)] (hstar : ∀ (s : S) (b : B), star (s ⊗ₜ[ℚ] b) = s ⊗ₜ[ℚ] star b) (a : S ⊗[ℚ] L) :
    locMap S ι (locInv S c a) = star (locMap S ι a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul s x =>
    simp only [locMap, locInv, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hstar, hc]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, star_add]

def invLoc (ι : L →ₐ[ℚ] B) (hι : Function.Injective ι) (γ₀ : Bˣ)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (c : L →ₐ[ℚ] L) (hc : ∀ a, ι (c a) = star (ι a))
    [StarRing (S ⊗[ℚ] B)] (hstar : ∀ (s : S) (b : B), star (s ⊗ₜ[ℚ] b) = s ⊗ₜ[ℚ] star b)
    {γ : (S ⊗[ℚ] B)ˣ} (h : StConj S (locElt S γ₀) γ) : H1 S (locInv S c) :=
  invCls (locMap S ι) (locMap_cent ι hι γ₀ hcent).1 (locElt S γ₀) (locMap_cent ι hι γ₀ hcent).2 (locInv S c)
    (locMap_star ι c hc hstar) h

def invL (ℓ : ℕ) [Fact ℓ.Prime] (ι : L →ₐ[ℚ] B) (hι : Function.Injective ι) (γ₀ : Bˣ)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (c : L →ₐ[ℚ] L) (hc : ∀ a, ι (c a) = star (ι a))
    [StarRing (ℚ_[ℓ] ⊗[ℚ] B)] (hstar : ∀ (s : ℚ_[ℓ]) (b : B), star (s ⊗ₜ[ℚ] b) = s ⊗ₜ[ℚ] star b)
    {γ : (ℚ_[ℓ] ⊗[ℚ] B)ˣ} (h : StConj ℚ_[ℓ] (locElt ℚ_[ℓ] γ₀) γ) : H1 ℚ_[ℓ] (locInv ℚ_[ℓ] c) :=
  invLoc ι hι γ₀ hcent c hc hstar h

end Local

end GlobalTheory.LKInv

section Examples

open GlobalTheory.LKInv

example : invCls (k := ℝ) (AlgHom.id ℝ ℂ) (fun _ _ h => h) (Units.mk0 Complex.I Complex.I_ne_zero)
    (fun x => ⟨fun _ => ⟨x, rfl⟩, fun _ => mul_comm _ _⟩) (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) (fun _ => rfl)
    (StConj.refl' (Units.mk0 Complex.I Complex.I_ne_zero) 1 (by
      simp [Complex.ext_iff])) = 1 :=
  invCls_self _ _ _ _ _ _ _

example (x : ℂˣ) (h : star (x : ℂ) * x = 2) : (x : ℂ) * star (x : ℂ) = 2 :=
  mul_star_of_star_mul x 2 (fun y => mul_comm _ _) h

example (B : Type) [Ring B] [Algebra ℚ B] (γ₀ : Bˣ) [Fact (Nat.Prime 5)] :
    ((locElt ℚ_[5] γ₀ : (ℚ_[5] ⊗[ℚ] B)ˣ) : ℚ_[5] ⊗[ℚ] B) = (1 : ℚ_[5]) ⊗ₜ[ℚ] (γ₀ : B) := rfl

end Examples

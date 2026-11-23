import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemRootsBarXSubC
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab

noncomputable section

namespace GlobalTheory.GLp.Model

open Polynomial GlobalTheory.GLq GlobalTheory.GLp
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem red_surjective (n : ℕ) : Function.Surjective (red g n) := by
  intro x
  have hs : Function.Surjective (PadicInt.toZMod (p := g)) := ZMod.ringHom_surjective _
  let M : Matrix (Fin n) (Fin n) ℤ_[g] := fun i j => Function.surjInv hs ((x : Mt g n) i j)
  have hM : (PadicInt.toZMod (p := g)).mapMatrix M = (x : Mt g n) := by
    ext i j; exact Function.surjInv_eq hs _
  have hd : IsUnit M.det := by
    by_contra h
    have h1 : M.det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod]; exact h
    rw [RingHom.mem_ker, RingHom.map_det, hM] at h1
    exact (Matrix.isUnit_iff_isUnit_det _ |>.1 x.isUnit).ne_zero h1
  refine ⟨((Matrix.isUnit_iff_isUnit_det M).2 hd).unit, ?_⟩
  ext i j
  exact congrFun (congrFun hM i) j

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_principalCongruenceFixedVectors_iff (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (v : V) :
    v ∈ fixK1 π ↔ ∀ k, red g n k = 1 → π (inc g n k) v = v := by
  simp [fixK1, Submodule.mem_iInf, sub_eq_zero, MonoidHom.mem_ker]

theorem lift_red (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) {v : V} (hv : v ∈ fixK1 π)
    (k : GL (Fin n) ℤ_[g]) : π (lift g n (red g n k)) v = π (inc g n k) v := by
  have h := Function.invFun_eq (f := red g n) ⟨k, rfl⟩
  have h2 := (mem_principalCongruenceFixedVectors_iff π v).1 hv (k⁻¹ * Function.invFun (red g n) (red g n k)) (by simp [h])
  have : lift g n (red g n k) = inc g n k * inc g n (k⁻¹ * Function.invFun (red g n) (red g n k)) := by
    simp [lift]
  rw [this, map_mul, Module.End.mul_apply, h2]

theorem padicIntGL_smul_mem_principalCongruenceFixed (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) {v : V} (hv : v ∈ fixK1 π)
    (k : GL (Fin n) ℤ_[g]) : π (inc g n k) v ∈ fixK1 π := by
  rw [mem_principalCongruenceFixedVectors_iff] at hv ⊢
  intro m hm
  have h := hv (k⁻¹ * m * k) (by simp [hm])
  have : inc g n m * inc g n k = inc g n k * inc g n (k⁻¹ * m * k) := by simp [mul_assoc]
  rw [← Module.End.mul_apply, ← map_mul, this, map_mul, Module.End.mul_apply, h]

theorem lift_mul (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) {v : V} (hv : v ∈ fixK1 π) (x y : Gn g n) :
    π (lift g n (x * y)) v = π (lift g n x) (π (lift g n y) v) := by
  obtain ⟨k, rfl⟩ := red_surjective n x
  obtain ⟨m, rfl⟩ := red_surjective n y
  rw [← map_mul, lift_red π hv, lift_red π hv, lift_red π (padicIntGL_smul_mem_principalCongruenceFixed π hv m), map_mul, map_mul,
    Module.End.mul_apply]

theorem isIrrRep_iff {G : Type} [Group G] (π : Representation ℂ G V) : IsIrrRep π ↔ π.IsIrreducible := by
  constructor
  · rintro ⟨hn, h⟩
    haveI : Nontrivial (Subrepresentation π) := ⟨⊥, ⊤, fun e => by
      have : (⊥ : Submodule ℂ V) = ⊤ := congrArg Subrepresentation.toSubmodule e
      exact bot_ne_top this⟩
    refine ⟨fun W => ?_⟩
    rcases h W.toSubmodule (fun x v hv => W.apply_mem_toSubmodule x hv) with e | e
    · left; exact Subrepresentation.toSubmodule_injective e
    · right; exact Subrepresentation.toSubmodule_injective e
  · intro h
    refine ⟨?_, fun W hW => ?_⟩
    · by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      have : (⊥ : Subrepresentation π) = ⊤ := Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
      exact bot_ne_top this
    · rcases eq_bot_or_eq_top (⟨W, fun x v hv => hW x v hv⟩ : Subrepresentation π) with e | e
      · left; exact congrArg Subrepresentation.toSubmodule e
      · right; exact congrArg Subrepresentation.toSubmodule e

def chRep {G : Type} [Group G] (φ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun x := (φ x : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_comm]

@[simp] theorem chRep_apply {G : Type} [Group G] (φ : G →* ℂˣ) (x : G) (v : ℂ) : chRep φ x v = φ x * v := by
  simp [chRep]

theorem isIrrRep_chRep {G : Type} [Group G] (φ : G →* ℂˣ) : IsIrrRep (chRep φ) :=
  ⟨inferInstance, fun W _ => eq_bot_or_eq_top W⟩

def unitPart : ℚ_[g]ˣ →* ℤ_[g]ˣ where
  toFun x := PadicInt.mkUnits (u := (x : ℚ_[g]) * (g : ℚ_[g]) ^ (-(x : ℚ_[g]).valuation)) (by
    have hg : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
    rw [norm_mul, Padic.norm_eq_zpow_neg_valuation x.ne_zero, norm_zpow, Padic.norm_p, inv_zpow', neg_neg,
      ← zpow_add₀ hg]; simp)
  map_one' := by
    apply Units.ext; apply Subtype.ext; simp
  map_mul' x y := by
    have hg : (g : ℚ_[g]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
    apply Units.ext; apply Subtype.ext
    simp only [PadicInt.mkUnits_eq, Units.val_mul, PadicInt.coe_mul, Padic.valuation_mul x.ne_zero y.ne_zero,
      neg_add, zpow_add₀ hg]
    ring

theorem unitPart_unit (u : ℤ_[g]ˣ) : unitPart (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) = u := by
  have h : ((u : ℤ_[g]) : ℚ_[g]).valuation = 0 := by
    have h1 : ‖((u : ℤ_[g]) : ℚ_[g])‖ = 1 := PadicInt.norm_units u
    have h0 : ((u : ℤ_[g]) : ℚ_[g]) ≠ 0 := by intro e; rw [e] at h1; simp at h1
    rw [Padic.norm_eq_zpow_neg_valuation h0] at h1
    have hg : (1 : ℝ) < g := by exact_mod_cast (Fact.out : g.Prime).one_lt
    have := (zpow_eq_one_iff_right₀ (by positivity) hg.ne').1 h1
    omega
  apply Units.ext; apply Subtype.ext
  simp [unitPart, h]

def tame (χ : (ZMod g)ˣ →* ℂˣ) : ℚ_[g]ˣ →* ℂˣ :=
  χ.comp ((Units.map (PadicInt.toZMod (p := g)).toMonoidHom).comp unitPart)

def detRep (n : ℕ) (μ : ℚ_[g]ˣ →* ℂˣ) : Representation ℂ (GL (Fin n) ℚ_[g]) ℂ :=
  chRep (μ.comp Matrix.GeneralLinearGroup.det)

theorem tame_inc (χ : (ZMod g)ˣ →* ℂˣ) (k : GL (Fin n) ℤ_[g]) :
    tame χ (Matrix.GeneralLinearGroup.det (inc g n k)) = χ (Matrix.GeneralLinearGroup.det (red g n k)) := by
  have h1 : Matrix.GeneralLinearGroup.det (inc g n k) =
      Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
    ext; simp [inc, RingHom.map_det]
  have h2 : Matrix.GeneralLinearGroup.det (red g n k) =
      Units.map (PadicInt.toZMod (p := g)).toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
    ext; simp [red, RingHom.map_det]
  rw [h1, h2, tame, MonoidHom.comp_apply, MonoidHom.comp_apply, unitPart_unit]

theorem tame_mem_fixK1 (χ : (ZMod g)ˣ →* ℂˣ) (v : ℂ) : v ∈ fixK1 (detRep n (tame χ)) := by
  rw [mem_principalCongruenceFixedVectors_iff]; intro k hk
  simp [detRep, tame_inc, hk]

theorem tame_lift (χ : (ZMod g)ˣ →* ℂˣ) (x : Gn g n) (v : ℂ) :
    detRep n (tame χ) (lift g n x) v = χ (Matrix.GeneralLinearGroup.det x) * v := by
  obtain ⟨k, rfl⟩ := red_surjective n x
  rw [lift_red _ (tame_mem_fixK1 χ v)]
  simp [detRep, tame_inc]

theorem det_one' {R : Type} [CommRing R] (y : GL (Fin 1) R) :
    ((Matrix.GeneralLinearGroup.det y : Rˣ) : R) = (y : Matrix (Fin 1) (Fin 1) R) 0 0 := by
  simp [Matrix.det_fin_one]

theorem det_two' {R : Type} [CommRing R] (y : GL (Fin 2) R) (h : (y : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) :
    ((Matrix.GeneralLinearGroup.det y : Rˣ) : R) =
      (y : Matrix (Fin 2) (Fin 2) R) 0 0 * (y : Matrix (Fin 2) (Fin 2) R) 1 1 := by
  simp [Matrix.det_fin_two, h]

theorem det_surj_one {R : Type} [CommRing R] (u : Rˣ) :
    ∃ y : GL (Fin 1) R, Matrix.GeneralLinearGroup.det y = u :=
  ⟨Matrix.GeneralLinearGroup.scalar (Fin 1) u, by ext; simp⟩

theorem det_blk (x y : Gn g 1) : Matrix.GeneralLinearGroup.det (blk 1 1 2 x y) =
    Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det y := by
  set M : Mt g 2 := fun i j : Fin 2 =>
    if (i : ℕ) < 1 ∧ (j : ℕ) < 1 then Formalism.MainNotions.ArithmeticCylinders.entN (x : Mt g 1) i j
    else if 1 ≤ (i : ℕ) ∧ 1 ≤ (j : ℕ) then Formalism.MainNotions.ArithmeticCylinders.entN (y : Mt g 1) (i - 1) (j - 1) else 0 with hM
  have hd : M.det = (Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det y : (ZMod g)ˣ) := by
    rw [Units.val_mul, det_one', det_one', Matrix.det_fin_two]
    simp [hM, Formalism.MainNotions.ArithmeticCylinders.entN]
  have hu : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, hd]; exact Units.isUnit _
  have : blk 1 1 2 x y = hu.unit := by
    show toG M = _
    rw [toG, dif_pos hu]
  rw [this]; ext; rw [← hd]; simp

theorem isParVec_tame (χ χ' : (ZMod g)ˣ →* ℂˣ) (v : ℂ) (hv : v ≠ 0) :
    IsParVec (detRep 2 (tame χ)) 1 1 χ' v ↔ χ' = χ := by
  constructor
  · rintro ⟨-, -, h⟩
    ext u
    obtain ⟨y, rfl⟩ := det_surj_one u
    have := h y
    rw [tame_lift, det_blk, map_one, one_mul, smul_eq_mul] at this
    exact (mul_right_cancel₀ hv this).symm
  · rintro rfl
    refine ⟨tame_mem_fixK1 _ _, fun u h1 h2 h3 => ?_, fun y => ?_⟩
    · have e1 := congrFun (congrFun h2 0) 0
      have e2 := congrFun (congrFun h3 0) 0
      have e3 := h1 1 0 (by simp) (by simp)
      have : Matrix.GeneralLinearGroup.det u = 1 := by
        ext; rw [det_two' u e3]
        simp [tl, br, Formalism.MainNotions.ArithmeticCylinders.entN] at e1 e2
        simp [e1, e2]
      rw [tame_lift, this]; simp
    · rw [tame_lift, det_blk, map_one, one_mul, smul_eq_mul]

theorem mapsToInd_det (μ ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) :
    MapsToInd (detRep 2 μ) 1 1 (detRep 1 1) ν₁ ν₂ ↔ ν₁ = μ ∧ ν₂ = μ := by
  constructor
  · rintro ⟨Λ, h0, h⟩
    have hΛ : Λ 1 ≠ 0 := fun e => h0 (by ext; simpa using e)
    have key : ∀ a d : ℚ_[g]ˣ, μ a * μ d = ν₁ a * ν₂ d := by
      intro a d
      let p : GL (Fin 2) ℚ_[g] := Matrix.GeneralLinearGroup.mkOfDetNeZero !![(a : ℚ_[g]), 0; 0, d] (by
        simp [Matrix.det_fin_two])
      have hp : Matrix.GeneralLinearGroup.det p = a * d := by ext; simp [p, Matrix.det_fin_two]
      have hs : ∀ u : ℚ_[g]ˣ, Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) u) = u :=
        fun u => by ext; simp
      have := h p (Matrix.GeneralLinearGroup.scalar (Fin 1) a) (Matrix.GeneralLinearGroup.scalar (Fin 1) d)
        (fun i j hj hi => by fin_cases i <;> fin_cases j <;> simp_all [p])
        (fun i j => by fin_cases i; fin_cases j; simp [p, Formalism.MainNotions.ArithmeticCylinders.entN])
        (fun i j => by fin_cases i; fin_cases j; simp [p, Formalism.MainNotions.ArithmeticCylinders.entN]) 1
      simp only [detRep, chRep_apply, MonoidHom.comp_apply, hp, hs, MonoidHom.one_apply, Units.val_one, one_mul,
        mul_one, smul_eq_mul] at this
      have e : Λ (μ (a * d) : ℂ) = (μ (a * d) : ℂ) * Λ 1 := by
        simpa using Λ.map_smul (μ (a * d) : ℂ) 1
      rw [e] at this
      rw [← map_mul]; exact Units.ext (mul_right_cancel₀ hΛ this)
    constructor
    · ext a; have := key a 1; simp at this; rw [this]
    · ext a; have := key 1 a; simp at this; rw [this]
  · rintro ⟨rfl, h⟩
    subst h
    refine ⟨LinearMap.id, fun e => by simpa using LinearMap.congr_fun e 1, fun p x y h1 h2 h3 v => ?_⟩
    have hp : Matrix.GeneralLinearGroup.det p = Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det y := by
      ext
      rw [det_two' p (h1 1 0 (by simp) (by simp)), Units.val_mul, det_one', det_one', h2, h3]
      simp [Formalism.MainNotions.ArithmeticCylinders.entN]
    simp [detRep, hp]

theorem exists_gen (L : LabelDatum g) : ∃ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 ∧
    orderOf u = g - 1 := by
  have hp : g.Prime := Fact.out
  have ho := L.gen_order 1 one_pos
  rw [pow_one] at ho
  have h1 : L.gen 1 ^ (g - 1) = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
  have hpos : 0 < g - 1 := by have := hp.two_le; omega
  have h2 : L.gen 1 ^ g = L.gen 1 := by
    have : L.gen 1 ^ g = L.gen 1 ^ (g - 1 + 1) := by congr 1; omega
    rw [this, pow_succ, h1, one_mul]
  obtain ⟨c, hc⟩ : ∃ c : ZMod g, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c = L.gen 1 := by
    obtain ⟨m, hm⟩ := (mem_bot_iff_intCast g (Formalism.CyclotomicNorms.Fbar g)).1
      ((Subfield.mem_bot_iff_pow_eq_self (Formalism.CyclotomicNorms.Fbar g) g).2 h2)
    exact ⟨m, by simpa using hm⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [← hc] at h1; simp [hpos.ne'] at h1
  refine ⟨Units.mk0 c hc0, hc, ?_⟩
  rw [← ho, ← hc, ← orderOf_units, Units.val_mk0]
  exact (orderOf_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom (algebraMap (ZMod g) _).injective c).symm

def dch (χ : (ZMod g)ˣ →* ℂˣ) : Gn g 1 → ℂ := fun y => (χ (Matrix.GeneralLinearGroup.det y) : ℂ)

theorem isIrr_dch (χ : (ZMod g)ˣ →* ℂˣ) : IsIrr (dch χ) := by
  have hc : ∀ x, (FDRep.of (chRep (χ.comp (Matrix.GeneralLinearGroup.det (n := Fin 1))))).character x =
      dch χ x := fun x => by
    change LinearMap.trace ℂ ℂ (((χ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) • LinearMap.id) = _
    simp [dch]
  refine ⟨_, ?_, hc⟩
  rw [FDRep.simple_iff_char_is_norm_one]
  simp [hc, dch]

theorem eq_of_ip {G : Type} [Group G] [Fintype G] {α β : G → ℂ} (ha : IsIrr α) (hb : IsIrr β) (h : ip α β ≠ 0) :
    α = β := by
  obtain ⟨A, hA, ha⟩ := ha
  obtain ⟨B, hB, hb⟩ := hb
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have := FDRep.char_orthonormal A B
  simp only [ha, hb, Nat.card_eq_fintype_card] at this
  by_cases hi : Nonempty (A ≅ B)
  · obtain ⟨i⟩ := hi
    funext x; rw [← ha, ← hb, FDRep.char_iso i]
  · rw [if_neg hi] at this; exact absurd this h

theorem theta_eq (L : LabelDatum g) {χ : (ZMod g)ˣ →* ℂˣ} {c : ZMod g} (hc : IsCharLab L χ c) (y : Gn g 1)
    {z : Formalism.CyclotomicNorms.Fbar g} (hz : z ∈ Formalism.CyclotomicNorms.rootsBar (y : Mt g 1).charpoly) :
    (-1) ^ (1 - 1) * ∑ i ∈ Finset.range 1, thetaOf L 1 (algebraMap (ZMod g) _ c) (z ^ (g ^ i)) = dch χ y := by
  have hcp : (y : Mt g 1).charpoly = X - C ((y : Mt g 1) 0 0) := by
    simp [Matrix.charpoly, Matrix.det_fin_one]
  rw [hcp] at hz
  have hz1 := GLq.Model.mem_rootsBar_X_sub_C hz
  obtain ⟨u, hu, ho⟩ := exists_gen L
  have hgen : ∀ w : (ZMod g)ˣ, ∃ m : ℕ, u ^ m = w := fun w => by
    have : Subgroup.zpowers u = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, ho, Nat.card_eq_fintype_card, ZMod.card_units]
    exact (mem_powers_iff_mem_zpowers.2 (this ▸ Subgroup.mem_top w))
  obtain ⟨m, hm⟩ := hgen (Matrix.GeneralLinearGroup.det y)
  have hz2 : z = L.gen 1 ^ m := by
    rw [hz1, ← det_one', ← hm, ← hu]; simp
  have hcp : (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c) ^ (g ^ 1 - 1) = 1 := by
    rw [← map_pow, pow_one, ZMod.pow_card_sub_one_eq_one hc.1, map_one]
  simp [hz2, GLq.Model.thetaOf_gen_pow L one_pos hcp, dch, ← hm, hc.2 u hu]

theorem isCuspOf_iff (L : LabelDatum g) {χ : (ZMod g)ˣ →* ℂˣ} {c : ZMod g} (hc : IsCharLab L χ c)
    (τ : Gn g 1 → ℂ) : IsCuspOf L (X - C c) τ ↔ τ = dch χ := by
  constructor
  · rintro ⟨-, -, h⟩
    funext y
    have hcp : (y : Mt g 1).charpoly = X - C ((y : Mt g 1) 0 0) := by
      simp [Matrix.charpoly, Matrix.det_fin_one]
    have hz : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) ((y : Mt g 1) 0 0) ∈ Formalism.CyclotomicNorms.rootsBar (y : Mt g 1).charpoly := by
      rw [hcp]; simp [Formalism.CyclotomicNorms.rootsBar]
    rw [h (algebraMap (ZMod g) _ c) (by simp [Formalism.CyclotomicNorms.rootsBar]) y (hcp ▸ irreducible_X_sub_C _) _ hz,
      theta_eq L hc y hz]
  · rintro rfl
    refine ⟨⟨monic_X_sub_C _, irreducible_X_sub_C _, by simpa using hc.1, natDegree_X_sub_C _⟩,
      ⟨one_pos, isIrr_dch χ, fun a h1 h2 => by omega⟩, ?_⟩
    intro x hx y _ z hz
    rw [GLq.Model.mem_rootsBar_X_sub_C hx, theta_eq L hc y hz]

theorem isClass_dch (χ : (ZMod g)ˣ →* ℂˣ) : IsClass (dch χ) := fun x y => by
  simp [dch, mul_comm]

theorem ip_dch (χ : (ZMod g)ˣ →* ℂˣ) : ip (dch χ) (dch χ) = 1 := by
  simp [ip, dch]

theorem eSerC_one (L : LabelDatum g) {χ : (ZMod g)ˣ →* ℂˣ} {c : ZMod g} (hc : IsCharLab L χ c) :
    eSerC L 1 (X - C c) = zOf (dch χ) := by
  have : {τ : Gn g 1 → ℂ | IsIrr τ ∧ HasLabel L τ (X - C c)} = {dch χ} := by
    ext τ
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hτ, Q, hQ, hd, hf, hip⟩
      match Q, hQ, hd, hf, hip with
      | [], _, hd, _, _ => simp [degL] at hd
      | [(P, ⟨d, σ⟩)], hQ, hd, hf, hip =>
        have : d = 1 := by simpa [degL] using hd
        subst this
        have hP : X - C c = P := by simpa using hf
        subst hP
        have := (isCuspOf_iff L hc σ).1 (hQ _ List.mem_cons_self)
        subst this
        have e : hcL ([(X - C c, (⟨1, dch χ⟩ : Pc g))].map Prod.snd) 1 = dch χ :=
          GLq.Model.hc_full _ (isClass_dch χ)
        rw [e] at hip
        exact eq_of_ip hτ (isIrr_dch χ) hip
      | p :: q :: R, hQ, hd, _, _ =>
        have h1 := (hQ p (by simp)).2.1.1
        have h2 := (hQ q (by simp)).2.1.1
        simp [degL] at hd
        omega
    · rintro rfl
      refine ⟨isIrr_dch χ, [(X - C c, ⟨1, dch χ⟩)], ?_, by simp [degL], by simp, ?_⟩
      · intro p hp
        rw [List.mem_singleton.1 hp]; exact (isCuspOf_iff L hc _).2 rfl
      · have e : hcL ([(X - C c, (⟨1, dch χ⟩ : Pc g))].map Prod.snd) 1 = dch χ :=
          GLq.Model.hc_full _ (isClass_dch χ)
        rw [e, ip_dch]; exact one_ne_zero
  unfold eSerC
  rw [this, finsum_mem_singleton]

theorem hasLab_tame (L : LabelDatum g) {χ : (ZMod g)ˣ →* ℂˣ} {c : ZMod g} (hc : IsCharLab L χ c)
    (χ' : (ZMod g)ˣ →* ℂˣ) : HasLab L (detRep 1 (tame χ')) (X - C c) ↔ χ' = χ := by
  have key : ∀ v, actK (detRep 1 (tame χ')) (eSerC L 1 (X - C c)) v = ip (dch χ') (dch χ) * v := fun v => by
    have hco : ∀ x, (zOf (dch χ)).coeff x = (Fintype.card (Gn g 1) : ℂ)⁻¹ * dch χ x⁻¹ := fun x => by
      simp [zOf, Finsupp.single_apply, dch]
    rw [eSerC_one L hc, actK, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, tame_lift, hco, smul_eq_mul, ip, Finset.mul_sum, Finset.sum_mul, dch]
    exact Finset.sum_congr rfl fun x _ => by ring
  constructor
  · rintro ⟨v, -, hv⟩
    rw [key] at hv
    have := eq_of_ip (isIrr_dch χ') (isIrr_dch χ) (left_ne_zero_of_mul hv)
    ext u
    obtain ⟨y, rfl⟩ := det_surj_one u
    exact congrFun this y
  · rintro rfl
    exact ⟨1, tame_mem_fixK1 _ _, by rw [key, ip_dch]; simp⟩

theorem isCharLab_unique (L : LabelDatum g) {χ : (ZMod g)ˣ →* ℂˣ} {c c' : ZMod g} (h : IsCharLab L χ c)
    (h' : IsCharLab L χ c') : c = c' := by
  obtain ⟨u, hu, -⟩ := exists_gen L
  exact (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
    (L.teich_inj _ _ (by simpa using h.1) (by simpa using h'.1) ((h.2 u hu).symm.trans (h'.2 u hu)))

theorem isCharLab_exists (L : LabelDatum g) (χ : (ZMod g)ˣ →* ℂˣ) : ∃ c, IsCharLab L χ c := by
  obtain ⟨u, hu, ho⟩ := exists_gen L
  have hpos : 0 < g - 1 := by have := (Fact.out : g.Prime).two_le; omega
  haveI : NeZero (g - 1) := ⟨hpos.ne'⟩
  let T : (ZMod g)ˣ →* ℂ := L.teich.comp ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom.comp (Units.coeHom _))
  have hT : Function.Injective T := fun a b e => Units.ext <| (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
    (L.teich_inj _ _ (by simp) (by simp) e)
  have hprim : IsPrimitiveRoot (T u) (g - 1) := by
    rw [← ho, ← orderOf_injective T hT u]; exact IsPrimitiveRoot.orderOf _
  obtain ⟨m, -, hm⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (χ u : ℂ)) (by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← ho, pow_orderOf_eq_one]; simp)
  refine ⟨(u ^ m : (ZMod g)ˣ), Units.ne_zero _, fun w hw => ?_⟩
  have : w = u := Units.ext ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective (hw.trans hu.symm))
  rw [this, ← hm, ← map_pow]; rfl

theorem hasLab_monic (L : LabelDatum g) (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (f : (ZMod g)[X])
    (h : HasLab L π f) : f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0 := by
  by_contra hf
  obtain ⟨v, -, hv⟩ := h
  simp [GLq.Model.eSerC_zero L n f hf, actK] at hv

theorem mapsToInd_of_too_large (μ μ' ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) : MapsToInd (detRep 1 μ) 1 1 (detRep 1 μ') ν₁ ν₂ := by
  refine ⟨LinearMap.id, fun e => by simpa using LinearMap.congr_fun e 1, fun p x y _ _ h3 v => ?_⟩
  have h := h3 0 0
  have := y.det_ne_zero
  simp [Formalism.MainNotions.ArithmeticCylinders.entN] at h
  simp [Matrix.det_fin_one, h] at this

theorem actTop_tame (χ : (ZMod g)ˣ →* ℂˣ) (x : Gn g 1) (v : ℂ) :
    actTop (detRep 2 (tame χ)) 1 1 (MonoidAlgebra.single x 1) v = dch χ x * v := by
  simp [actTop, LinearMap.sum_apply, tame_lift, det_blk, Finsupp.single_apply, dch]

theorem hasLab_inhabited (χ : (ZMod g)ˣ →* ℂˣ) :
    ∃ f, HasLab (GLq.Model.datum g) (detRep 1 (tame χ)) f := by
  obtain ⟨c, hc⟩ := isCharLab_exists (GLq.Model.datum g) χ
  exact ⟨_, (hasLab_tame _ hc χ).2 rfl⟩

end GlobalTheory.GLp.Model

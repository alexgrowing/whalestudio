import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPModel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

attribute [local instance] CategoryTheory.Hom.group CategoryTheory.Hom.commGroup

namespace GlobalTheory.RealMult.LevelComb

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}}

def actHom (X : Obj F 𝔠 S) {T : Over S} (u : T ⟶ 𝟙_ (Over S)) (z : 𝟙_ (Over S) ⟶ X.A) :
    𝓞 F →+ Additive (T ⟶ X.A) :=
  AddMonoidHom.mk' (fun c ↦ Additive.ofMul (u ≫ z ≫ X.rm.act c)) (fun a b ↦ by
    simp only [X.rm.add, comp_mul]; rfl)

theorem comp_act_add (X : Obj F 𝔠 S) {T : Over S} (u : T ⟶ 𝟙_ (Over S)) (z : 𝟙_ (Over S) ⟶ X.A) (a b : 𝓞 F) :
    u ≫ z ≫ X.rm.act (a + b) = (u ≫ z ≫ X.rm.act a) * (u ≫ z ≫ X.rm.act b) := by
  simp only [X.rm.add, comp_mul]

theorem comp_act_zsmul (X : Obj F 𝔠 S) {T : Over S} (u : T ⟶ 𝟙_ (Over S)) (z : 𝟙_ (Over S) ⟶ X.A) (n : ℤ)
    (c : 𝓞 F) : u ≫ z ≫ X.rm.act (n • c) = (u ≫ z ≫ X.rm.act c) ^ n := by
  have h := map_zsmul (actHom X u z) n c
  exact congrArg Additive.toMul h

theorem comp_pow_act (X : Obj F 𝔠 S) {T : Over S} (u : T ⟶ 𝟙_ (Over S)) (z : 𝟙_ (Over S) ⟶ X.A) (m : ℕ)
    (c : 𝓞 F) : u ≫ (z ^ m) ≫ X.rm.act c = (u ≫ z ≫ X.rm.act c) ^ m := by
  haveI := X.rm.hom c
  rw [pow_comp, comp_pow]

end GlobalTheory.RealMult.LevelComb

open GlobalTheory.RealMult.LevelComb in

theorem GlobalTheory.RealMult.Obj.Level.comb : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} {X : Obj F 𝔠 S} {N N' : ℕ}, Nat.Coprime N N' → ∀ (β : X.Level N) (β' : X.Level N'),
    ∃ ξ : X.Level (N * N'), (∀ i, ξ.pt i ^ N' = β.pt i) ∧ ∀ i, ξ.pt i ^ N = β'.pt i := by
  intro F _ _ 𝔠 S X N N' hc β β'
  obtain ⟨p, q, hpq⟩ : IsCoprime (N : ℤ) (N' : ℤ) := Nat.isCoprime_iff_coprime.2 hc
  let pt : Fin 2 → (𝟙_ (Over S) ⟶ X.A) := fun i ↦ β.pt i ^ q * β'.pt i ^ p
  have h1 : ∀ i, pt i ^ N' = β.pt i := by
    intro i
    have hb : β.pt i ^ (q * (N' : ℤ)) = β.pt i := by
      rw [show q * (N' : ℤ) = 1 - (N : ℤ) * p by linarith, zpow_sub, zpow_one, zpow_mul, zpow_natCast,
        β.tors i, one_zpow, inv_one, _root_.mul_one]
    have hb' : β'.pt i ^ (p * (N' : ℤ)) = 1 := by
      rw [mul_comm, zpow_mul, zpow_natCast, β'.tors i, one_zpow]
    show (β.pt i ^ q * β'.pt i ^ p) ^ N' = β.pt i
    rw [← zpow_natCast, mul_zpow, ← zpow_mul, ← zpow_mul, hb, hb', _root_.mul_one]
  have h2 : ∀ i, pt i ^ N = β'.pt i := by
    intro i
    have hb : β'.pt i ^ (p * (N : ℤ)) = β'.pt i := by
      rw [show p * (N : ℤ) = 1 - (N' : ℤ) * q by linarith, zpow_sub, zpow_one, zpow_mul, zpow_natCast,
        β'.tors i, one_zpow, inv_one, _root_.mul_one]
    have hb' : β.pt i ^ (q * (N : ℤ)) = 1 := by
      rw [mul_comm, zpow_mul, zpow_natCast, β.tors i, one_zpow]
    show (β.pt i ^ q * β'.pt i ^ p) ^ N = β'.pt i
    rw [← zpow_natCast, mul_zpow, ← zpow_mul, ← zpow_mul, hb, hb', _root_.one_mul]
  refine ⟨{ pt := pt, tors := ?_, inj := ?_, surj := ?_ }, h1, h2⟩
  · intro i
    rw [mul_comm, pow_mul, h1, β.tors]
  · intro Ω _ _ t a b h
    set u := toUnit (Over.mk t)
    have hβ : (u ≫ β.pt 0 ≫ X.rm.act a) * (u ≫ β.pt 1 ≫ X.rm.act b) = 1 := by
      rw [← h1, ← h1, comp_pow_act, comp_pow_act, ← mul_pow, h, one_pow]
    have hβ' : (u ≫ β'.pt 0 ≫ X.rm.act a) * (u ≫ β'.pt 1 ≫ X.rm.act b) = 1 := by
      rw [← h2, ← h2, comp_pow_act, comp_pow_act, ← mul_pow, h, one_pow]
    obtain ⟨ha, hb⟩ := β.inj Ω t a b hβ
    obtain ⟨ha', hb'⟩ := β'.inj Ω t a b hβ'
    have hco : IsCoprime ((N : 𝓞 F)) ((N' : 𝓞 F)) := by
      simpa using (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 F))
    rw [Nat.cast_mul]
    exact ⟨hco.mul_dvd ha ha', hco.mul_dvd hb hb'⟩
  · intro Ω _ _ t y hy
    set u := toUnit (Over.mk t)
    have hy1 : (y ^ N') ^ N = 1 := by rw [← pow_mul, mul_comm, hy]
    have hy2 : (y ^ N) ^ N' = 1 := by rw [← pow_mul, hy]
    obtain ⟨a, b, hab⟩ := β.surj Ω t (y ^ N') hy1
    obtain ⟨a', b', hab'⟩ := β'.surj Ω t (y ^ N) hy2
    rw [← h1, ← h1, comp_pow_act, comp_pow_act] at hab
    rw [← h2, ← h2, comp_pow_act, comp_pow_act] at hab'
    refine ⟨((N : ℤ) * p) • a' + ((N' : ℤ) * q) • a, ((N : ℤ) * p) • b' + ((N' : ℤ) * q) • b, ?_⟩
    rw [comp_act_add, comp_act_add, comp_act_zsmul, comp_act_zsmul, comp_act_zsmul, comp_act_zsmul]
    have hy0 : y = y ^ ((N : ℤ) * p + (N' : ℤ) * q) := by
      rw [show (N : ℤ) * p + (N' : ℤ) * q = 1 by linarith, zpow_one]
    rw [hy0, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hab, hab', mul_zpow, mul_zpow,
      zpow_mul, zpow_mul, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast]
    exact mul_mul_mul_comm _ _ _ _

end

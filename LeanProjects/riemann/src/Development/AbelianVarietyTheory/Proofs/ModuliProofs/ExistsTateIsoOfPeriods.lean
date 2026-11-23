import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PeriodTate

theorem exists_pairing_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    [Nontrivial D.La] : ∃ a b, D.EF a b = 1 := by
  have := D.fin
  have := D.proj
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  have : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ D.La
  obtain ⟨i⟩ := b.index_nonempty
  obtain ⟨a, ha⟩ := D.unimod.2 (b.coord i)
  exact ⟨a, b i, by rw [ha]; simp⟩

def rt (n : ℕ) (x : ℤ) : ℂˣ :=
  Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / n)) (Complex.exp_ne_zero _)

theorem rt_val (n : ℕ) (x : ℤ) : (rt n x : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / n) := rfl

theorem rt_mul (n : ℕ) (x y : ℤ) : rt n (x * y) = rt n x ^ y := by
  apply Units.ext
  rw [Units.val_zpow_eq_zpow_val, rt_val, rt_val, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem rt_congr {n : ℕ} (hn : 0 < n) {x y : ℤ} (h : (n : ℤ) ∣ x - y) : rt n x = rt n y := by
  obtain ⟨c, hc⟩ := h
  apply Units.ext
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [rt_val, rt_val, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-c, ?_⟩
  rw [sub_eq_iff_eq_add.1 hc]
  push_cast
  field_simp
  ring

theorem rt_pow {n m : ℕ} (hm : 0 < m) (x : ℤ) : rt (n * m) x ^ m = rt n x := by
  apply Units.ext
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Units.val_pow_eq_pow_val, rt_val, rt_val, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  rw [← div_div, mul_div_cancel₀ _ hm']

theorem rt_prim {n : ℕ} (hn : 0 < n) {x : ℤ} (h : IsCoprime x n) : IsPrimitiveRoot (rt n x) n := by
  rw [← IsPrimitiveRoot.coe_units_iff, rt_val]
  have := Complex.isPrimitiveRoot_exp_of_isCoprime (-x) n hn.ne' h.neg_left
  convert this using 2
  push_cast
  ring

theorem pre_injective {k : Type} [Field k] (β : ℂ →+* k) (A : Over (Sp ℂ)) :
    Function.Injective fun x : 𝟙_ (Over (Sp ℂ)) ⟶ A => toUnit (Over.mk (spMap β)) ≫ x := by
  intro x y h
  have e : (toUnit (Over.mk (spMap β))).left = spMap β := by
    simpa using Over.w (toUnit (Over.mk (spMap β)))
  have hf : Flat (spMap β) := by
    rw [Flat.SpecMap_iff]
    letI := β.toAlgebra
    exact (inferInstance : Module.Flat ℂ k)
  have hs : Surjective (spMap β) := ⟨fun p => ⟨default, Subsingleton.elim (α := PrimeSpectrum ℂ) _ _⟩⟩
  have : Epi (spMap β) := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  have h' := congrArg (fun z => z.left) h
  simp only [Over.comp_left, e] at h'
  exact (cancel_epi (spMap β)).1 h'

theorem pre_onto (hM : Out.MulNSt) {k : Type} [Field k] [IsAlgClosed k] (β : ℂ →+* k) (Q : Out.PolAV (Sp ℂ))
    {n : ℕ} (hn : 0 < n) (x : Over.mk (spMap β) ⟶ Q.A) (hx : x ^ n = 1) :
    ∃ y : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A, y ^ n = 1 ∧ toUnit _ ≫ y = x := by
  have hk : (n : k) ≠ 0 := by
    rw [← map_natCast β]
    exact (map_ne_zero β).2 (by exact_mod_cast hn.ne')
  have c₁ := (hM _ Q n hn).2.2.2.2 k (spMap β) hk
  have c₀ : Nat.card {x : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A // x ^ n = 1} = n ^ (2 * Q.g) :=
    (hM _ Q n hn).2.2.2.2 ℂ (𝟙 _) (by exact_mod_cast hn.ne')
  have : Finite {x : Over.mk (spMap β) ⟶ Q.A // x ^ n = 1} :=
    Nat.finite_of_card_ne_zero (by rw [c₁]; positivity)
  let F : {x : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A // x ^ n = 1} → {x : Over.mk (spMap β) ⟶ Q.A // x ^ n = 1} :=
    fun y => ⟨toUnit _ ≫ y.1, by
      have := map_pow (preHom (G := Q.A) (toUnit (Over.mk (spMap β)))) y.1 n
      rw [y.2, map_one] at this
      exact this.symm⟩
  have hF : Function.Injective F := fun y y' h => Subtype.ext (pre_injective β Q.A (congrArg Subtype.val h))
  obtain ⟨y, hy⟩ := (hF.bijective_of_nat_card_le (by rw [c₀, c₁])).2 ⟨x, hx⟩
  exact ⟨y.1, y.2, congrArg Subtype.val hy⟩

theorem unitOn_pull {k : Type} [Field k] (β : ℂ →+* k) (c : ℂˣ) :
    Units.map (toUnit (Over.mk (spMap β))).left.appTop.hom.toMonoidHom (unitOn c) =
      unitOn (Units.map β.toMonoidHom c) := by
  have e : (toUnit (Over.mk (spMap β))).left = spMap β := by
    simpa using Over.w (toUnit (Over.mk (spMap β)))
  rw [e]
  apply Units.ext
  exact (congrArg (fun q => q.hom (c : ℂ)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

end GlobalTheory.PeriodTate

namespace GlobalTheory

open PeriodTate in

theorem exists_tateIso_of_periods : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D'.La →+ (Fin g → ℂ)) (Q : Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) Q.A) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ Q.A)) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), 1 ≤ D.p + D.q → IsPeriod D' ty P → (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → (∀ z, e z = 1 ↔ z ∈ P.range) → (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ act.act a) → (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs Q.A Q.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) → (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) → (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) → (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') → ∀ (k : Type) [Field k] [IsAlgClosed k] (β : ℂ →+* k), ∃ I : TateIso D k (Over.mk (spMap β) ⟶ Q.A) (fun a x => x ≫ act.act a) (fun n x x' c => Out.WeilIs Q.A Q.L n x x' (unitOn c)), (∀ n : ℕ, (I.ζ n : k) = β (Complex.exp (-(2 * Real.pi * Complex.I) * (ν n : ℂ) / n))) ∧ ∀ (n : ℕ) a, I.ev n a = toUnit _ ≫ e ((n : ℂ)⁻¹ • P (f n a)) := by
  intro hL E _ _ _ H D D' g ty P Q act e f ν hpq hP hadd hsurj hker hact hW htow hmod hν k _ _ β
  have : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D.rank]; omega)
  obtain ⟨a₀, b₀, h₀⟩ := exists_pairing_one D
  have : Nontrivial D'.La := by
    refine ⟨f 2 a₀, 0, fun h => ?_⟩
    obtain ⟨c, hc⟩ := ((hmod 2 two_pos).1 a₀).1 ⟨0, by rw [h, smul_zero]⟩
    rw [hc, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h₀
    omega
  obtain ⟨a₁, b₁, h₁⟩ := exists_pairing_one D'
  have hcong : ∀ (n : ℕ) (a b c d : D'.La), (n : ℤ) ∣ D'.EF (a + n • c) (b + n • d) - D'.EF a b := by
    intro n a b c d
    refine ⟨D'.EF a d + D'.EF c b + n * D'.EF c d, ?_⟩
    simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
    ring
  have hcop : ∀ n : ℕ, 0 < n → IsCoprime (ν n) n := by
    intro n hn
    obtain ⟨a, c, ha⟩ := (hmod n hn).2 a₁
    obtain ⟨b, d, hb⟩ := (hmod n hn).2 b₁
    obtain ⟨u, hu⟩ := hcong n (f n a) (f n b) c d
    obtain ⟨v, hv⟩ := hν n hn a b
    rw [← ha, ← hb, h₁] at hu
    exact ⟨D.EF a b, u + v, by linear_combination -hu - hv⟩
  have hνt : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n := by
    intro n m hn hm
    obtain ⟨c, hc⟩ := htow n m hn hm a₀
    obtain ⟨d, hd⟩ := htow n m hn hm b₀
    obtain ⟨u, hu⟩ := hcong n (f n a₀) (f n b₀) c d
    obtain ⟨v, hv⟩ := hν n hn a₀ b₀
    obtain ⟨w, hw⟩ := hν (n * m) (Nat.mul_pos hn hm) a₀ b₀
    rw [← hc, ← hd] at hu
    rw [h₀] at hv hw
    push_cast at hw
    exact ⟨u + v - m * w, by linear_combination hu + hv - hw⟩
  let e' : Multiplicative (Fin g → ℂ) →* (𝟙_ (Over (Sp ℂ)) ⟶ Q.A) :=
    MonoidHom.mk' (fun z => e z.toAdd) fun z w => hadd _ _
  have hpow : ∀ (n : ℕ) z, e z ^ n = e (n • z) := fun n z => (map_pow e' (Multiplicative.ofAdd z) n).symm
  let ρ := preHom (G := Q.A) (toUnit (Over.mk (spMap β)))
  have hρ : Function.Injective ρ := pre_injective β Q.A
  have hsm : ∀ n : ℕ, 0 < n → ∀ z : Fin g → ℂ, n • (n : ℂ)⁻¹ • z = z := fun n hn z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
  have hsm' : ∀ n : ℕ, 0 < n → ∀ z : Fin g → ℂ, (n : ℂ)⁻¹ • n • z = z := fun n hn z => by
    rw [smul_comm, hsm n hn]
  have hshift : ∀ n : ℕ, 0 < n → ∀ a c : D'.La, e ((n : ℂ)⁻¹ • P (a + n • c)) = e ((n : ℂ)⁻¹ • P a) := by
    intro n hn a c
    rw [map_add, smul_add, hadd, map_nsmul, hsm' n hn, (hker _).2 ⟨c, rfl⟩, _root_.mul_one]
  refine ⟨{ ζ := fun n => Units.map β.toMonoidHom (rt n (ν n))
            ζ_prim := fun n hn => (rt_prim hn (hcop n hn)).map_of_injective (Units.map_injective β.injective)
            ζ_pow := fun n m hn hm => by rw [← map_pow, rt_pow hm, rt_congr hn (hνt n m hn hm)]
            ev := fun n a => ρ (e ((n : ℂ)⁻¹ • P (f n a)))
            add := fun n a b => by rw [map_add, map_add, smul_add, hadd, map_mul]
            lin := fun n c a => ?_
            ker := fun n hn a => ?_
            onto := fun n hn x => ?_
            tower := fun n m hn hm a => ?_
            isom := fun n hn a b => ?_ }, fun n => rfl, fun n a => rfl⟩
  · show toUnit (Over.mk (spMap β)) ≫ _ = (toUnit (Over.mk (spMap β)) ≫ _) ≫ _
    rw [Category.assoc, ← hact, map_smul]
    congr 2
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, hP.1, smul_eq_mul, smul_eq_mul, mul_left_comm]
  · rw [map_eq_one_iff ρ hρ, hker, ← (hmod n hn).1 a]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, hP.2.1 (by rw [map_nsmul, hc, hsm n hn])⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [hc, map_nsmul, hsm' n hn]⟩
  · constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := pre_onto hL.mulN β Q hn x hx
      obtain ⟨z, rfl⟩ := hsurj y
      rw [hpow, hker] at hy
      obtain ⟨a', ha'⟩ := hy
      obtain ⟨a, c, rfl⟩ := (hmod n hn).2 a'
      refine ⟨a, congrArg ρ ?_⟩
      rw [← hshift n hn _ c, ha', hsm' n hn]
    · rintro ⟨a, rfl⟩
      rw [← map_pow, hpow, hsm n hn, (hker _).2 ⟨_, rfl⟩, map_one]
  · obtain ⟨c, hc⟩ := htow n m hn hm a
    rw [← map_pow, hpow, Nat.cast_mul, mul_inv_rev, mul_smul, hsm m hm, hc, hshift n hn]
  · have h := CommPairing.weilIs_pull hL.globalFns Q.isAb Q.isLB (toUnit (Over.mk (spMap β)))
      (hW n (f n a) (f n b) (rt n _) hn (rt_val _ _))
    rw [unitOn_pull, rt_congr hn (hν n hn a b), rt_mul, map_zpow] at h
    exact h

end GlobalTheory

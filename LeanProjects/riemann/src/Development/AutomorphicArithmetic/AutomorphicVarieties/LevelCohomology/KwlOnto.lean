import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbsRam
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Mathlib.RingTheory.ZMod.UnitsCyclic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

private theorem kwl_fix {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (g : G ℚ Ω) :
    g ∈ fixMu ℚ Ω N ↔ Chr.cls ℚ Ω N g = 1 := by
  have key : ∀ x : Ω, x ^ N = 1 → x ^ ((1 : (ZMod N)ˣ) : ZMod N).val = x := fun x hx => by
    rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hx, pow_one]
  refine ⟨fun h => (Chr.clsFacts ℚ Ω N).2.2.1 g 1 fun x hx => (h x hx).trans (key x hx).symm, fun h x hx => ?_⟩
  rw [Chr.cls_spec N g x hx, h, key x hx]

private theorem kwl_onto {Ω : Type} [Field Ω] [inst : Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] :
    Function.Surjective (Chr.cls ℚ Ω N) := by
  have hch : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact (Chr.clsOnto Ω N).1

private theorem kwl_pow (l : ℕ) (hl : l.Prime) (h2 : l ≠ 2) (n : ℕ) (hd : l ^ 2 ∣ l ^ (n + 2)) (u : (ZMod (l ^ (n + 2)))ˣ)
    (hu : ZMod.unitsMap hd u = 1) : ∃ v, v ^ l = u := by
  haveI : NeZero (l ^ (n + 2)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero (l ^ 2) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI := ZMod.isCyclic_units_of_prime_pow l hl h2 (n + 2)
  have hl0 : 0 < l - 1 := Nat.sub_pos_of_lt hl.one_lt
  have hcard : ∀ e : ℕ, 0 < e → Nat.card (ZMod (l ^ e))ˣ = l ^ (e - 1) * (l - 1) := by
    intro e he
    haveI : NeZero (l ^ e) := ⟨pow_ne_zero _ hl.ne_zero⟩
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hl he]
  have hG := hcard (n + 2) (by omega)
  have hH := hcard 2 (by omega)
  have e1 : n + 2 - 1 = n + 1 := by omega
  rw [e1] at hG
  simp only [show (2 - 1 : ℕ) = 1 from rfl, pow_one] at hH
  have hrange : (ZMod.unitsMap hd).range = ⊤ :=
    MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective hd)
  have hker : Nat.card (ZMod.unitsMap hd).ker = l ^ n := by
    have h1 := Subgroup.card_mul_index (ZMod.unitsMap hd).ker
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, hH, hG] at h1
    have hpos : 0 < l * (l - 1) := Nat.mul_pos hl.pos hl0
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1]
    ring
  have hu1 : u ^ (l ^ n) = 1 := by
    have := pow_card_eq_one' (G := (ZMod.unitsMap hd).ker) (x := ⟨u, hu⟩)
    rw [hker] at this
    exact congrArg Subtype.val this
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := (ZMod (l ^ (n + 2)))ˣ)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hγ u)
  have hord : orderOf γ = l ^ (n + 1) * (l - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, hG]
  rw [← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hord] at hu1
  have hlk : (l : ℤ) ∣ k := by
    have h3 : ((l ^ (n + 1) : ℕ) : ℤ) ∣ k * ((l ^ n : ℕ) : ℤ) :=
      (Int.natCast_dvd_natCast.2 (Dvd.intro _ rfl)).trans hu1
    push_cast at h3
    rw [pow_succ, mul_comm ((l : ℤ) ^ n)] at h3
    exact (mul_dvd_mul_iff_right (pow_ne_zero _ (by exact_mod_cast hl.ne_zero))).1 h3
  obtain ⟨j, rfl⟩ := hlk
  refine ⟨γ ^ j, ?_⟩
  rw [← zpow_natCast, ← zpow_mul, mul_comm]

theorem UpperTheory.V.X.kwl :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ φ ∈ UnrHom ℚ Ω l, ∀ g ∈ fixMu ℚ Ω (l ^ 2), φ g = 0 := by
  intro Ω _ _ _ l hlf h2 φ hφ g hg
  have hl : l.Prime := hlf.out
  obtain ⟨hlc, hadd, hunr⟩ := hφ
  let ψ : G ℚ Ω →* Multiplicative (ZMod l) :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd (φ x)) (fun a b => by
      simp only [hadd, ofAdd_add])
  have hψ : ∀ x, ψ x = Multiplicative.ofAdd (φ x) := fun x => rfl
  have hkerset : ((ψ.ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) = {x | φ x = 0} := by
    ext x
    simp [MonoidHom.mem_ker, hψ]
  have hVo : IsOpen ((ψ.ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
    rw [hkerset]
    exact hlc.isOpen_fiber 0
  have hVc : commutator (G ℚ Ω) ≤ ψ.ker := Abelianization.commutator_subset_ker ψ
  have hI : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ ψ.ker := by
    intro A hA x hx
    rw [MonoidHom.mem_ker, hψ, hunr A hA x hx]
    rfl
  obtain ⟨n, hn⟩ := UpperTheory.V.CF.kwAbsRam Ω ψ.ker hVo hVc l hl.pos hI
  haveI : NeZero (l ^ (n + 2)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero (l ^ 2) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hfix : fixMu ℚ Ω (l ^ (n + 2)) ≤ ψ.ker := by
    intro x hx
    apply hn x
    exact fixMu_le ℚ Ω (pow_dvd_pow l (by omega)) hx
  have hd : l ^ 2 ∣ l ^ (n + 2) := pow_dvd_pow l (by omega)
  have hc2 : ZMod.unitsMap hd (Chr.cls ℚ Ω (l ^ (n + 2)) g) = 1 := by
    have := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω (l ^ (n + 2))).2.1 (l ^ 2) hd) g
    rw [MonoidHom.comp_apply] at this
    rw [this]
    exact (kwl_fix (l ^ 2) g).1 hg
  obtain ⟨v, hv⟩ := kwl_pow l hl h2 n hd _ hc2
  obtain ⟨h, rfl⟩ := kwl_onto (Ω := Ω) (l ^ (n + 2)) v
  have hk : g * (h ^ l)⁻¹ ∈ fixMu ℚ Ω (l ^ (n + 2)) := by
    rw [kwl_fix, map_mul, map_inv, map_pow, hv, mul_inv_cancel]
  have h0 := hfix hk
  rw [MonoidHom.mem_ker] at h0
  have hg' : g = g * (h ^ l)⁻¹ * h ^ l := by group
  have : ψ g = 1 := by
    rw [hg', map_mul, h0, one_mul, map_pow, hψ, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rfl
  rw [hψ] at this
  exact this

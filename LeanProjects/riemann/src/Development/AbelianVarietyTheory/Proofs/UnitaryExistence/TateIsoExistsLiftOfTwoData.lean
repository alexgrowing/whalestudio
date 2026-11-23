import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsoDifferBySimilitude

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem tateIso_ev_eq_iff_add (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a b : D.La) :
    I.ev n a = I.ev n b ↔ ∃ c, a = b + n • c := by
  rw [tateIso_ev_eq_iff I hn]
  exact exists_congr fun c => sub_eq_iff_eq_add'

theorem tateIso_exists_lift_of_two_data (I : TateIso D k Q act e) (I' : TateIso D' k Q act e) {n : ℕ} (hn : 0 < n) :
    ∃ f : D.La →ₗ[𝓞 E] D'.La, ∀ a, I.ev n a = I'.ev n (f a) := by
  let R : Submodule (𝓞 E) (D.La × D'.La) :=
    { carrier := {p | I.ev n p.1 = I'.ev n p.2}
      add_mem' := fun {p q} hp hq => by
        change I.ev n (p.1 + q.1) = I'.ev n (p.2 + q.2)
        rw [I.add, I'.add, show I.ev n p.1 = I'.ev n p.2 from hp, show I.ev n q.1 = I'.ev n q.2 from hq]
      zero_mem' := by
        change I.ev n 0 = I'.ev n 0
        rw [(I.ker n hn 0).2 ⟨0, by simp⟩, (I'.ker n hn 0).2 ⟨0, by simp⟩]
      smul_mem' := fun c p hp => by
        change I.ev n (c • p.1) = I'.ev n (c • p.2)
        rw [I.lin, I'.lin, show I.ev n p.1 = I'.ev n p.2 from hp] }
  have hs : Function.Surjective ((LinearMap.fst (𝓞 E) D.La D'.La).comp R.subtype) := fun a => by
    obtain ⟨b, hb⟩ := (I'.onto n hn _).1 (tateIso_ev_pow I hn a)
    exact ⟨⟨(a, b), hb.symm⟩, rfl⟩
  haveI := D.proj
  obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hs
  refine ⟨((LinearMap.snd (𝓞 E) D.La D'.La).comp R.subtype).comp s, fun a => ?_⟩
  have h1 : (s a).1.1 = a := LinearMap.congr_fun hs a
  have h2 : I.ev n (s a).1.1 = I'.ev n (s a).1.2 := (s a).2
  rw [h1] at h2
  exact h2

theorem tateIso_similar_of_two_data
    (he : ∀ n x y c c', e n x y c → e n x y c' → c = c') (I : TateIso D k Q act e) (I' : TateIso D' k Q act e) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) ∧
      (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) ∧
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧
      ∀ n : ℕ, 0 < n → ∀ a, I.ev n a = I'.ev n (f n a) := by
  have h1 : ∀ n : ℕ, ∃ f : D.La →ₗ[𝓞 E] D'.La, 0 < n → ∀ a, I.ev n a = I'.ev n (f a) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨0, fun h' => absurd h h'.ne'⟩
    · obtain ⟨f, hf⟩ := tateIso_exists_lift_of_two_data I I' h
      exact ⟨f, fun _ => hf⟩
  have h2 : ∀ n : ℕ, ∃ ν : ℕ, 0 < n → I.ζ n = I'.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | hn
    · exact ⟨1, fun h' => absurd h h'.ne'⟩
    · haveI : NeZero n := ⟨hn.ne'⟩
      obtain ⟨i, -, hi⟩ := (I'.ζ_prim n hn).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity _ _).2 (I.ζ_prim n hn).pow_eq_one)
      exact ⟨i, fun _ => hi.symm⟩
  choose f hf using h1
  choose ν hν using h2
  refine ⟨f, fun n => ν n, ?_, ?_, ?_, ?_, ?_, hf⟩
  · intro n m hn hm a
    rw [← tateIso_ev_eq_iff_add I' hn, ← hf n hn, ← I'.tower n m hn hm, ← hf (n * m) (Nat.mul_pos hn hm),
      I.tower n m hn hm]
  · intro n hn
    refine ⟨fun a => ?_, fun a' => ?_⟩
    · rw [← I'.ker n hn, ← I.ker n hn, hf n hn]
    · obtain ⟨a, ha⟩ := (I.onto n hn _).1 (tateIso_ev_pow I' hn a')
      rw [hf n hn] at ha
      exact ⟨a, (tateIso_ev_eq_iff_add I' hn _ _).1 ha.symm⟩
  · intro n hn
    have h := I.ζ_prim n hn
    rw [hν n hn] at h
    exact Nat.isCoprime_iff_coprime.2 (((I'.ζ_prim n hn).pow_iff_coprime hn _).1 h)
  · intro n m hn hm
    have h : I'.ζ n ^ ν (n * m) = I'.ζ n ^ ν n := by
      rw [← hν n hn, ← I.ζ_pow n m hn hm, hν (n * m) (Nat.mul_pos hn hm), ← I'.ζ_pow n m hn hm, ← pow_mul,
        ← pow_mul, mul_comm m]
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, zpow_natCast, zpow_natCast, h, mul_inv_cancel]
  · intro n hn a b
    have e1 := I'.isom n hn (f n a) (f n b)
    have e2 := I.isom n hn a b
    rw [hf n hn a, hf n hn b] at e2
    have h := he n _ _ _ _ e1 e2
    rw [hν n hn, ← zpow_natCast, ← zpow_mul] at h
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]

end

noncomputable def expNegUnit (n : ℕ) : ℂˣ :=
  (Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / n)) (Complex.exp_ne_zero _))⁻¹

theorem expNegUnit_zpow_val (n : ℕ) (j : ℤ) :
    ((expNegUnit n ^ j : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (j : ℂ) / n) := by
  rw [Units.val_zpow_eq_zpow_val, expNegUnit, Units.val_inv_eq_inv_val, Units.val_mk0, ← Complex.exp_neg,
    ← Complex.exp_int_mul]
  congr 1
  ring

theorem expNegUnit_isPrimitiveRoot {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (expNegUnit n) n :=
  (IsPrimitiveRoot.coe_units_iff.1 (Complex.isPrimitiveRoot_exp n hn.ne')).inv

theorem expNegUnit_mul_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : expNegUnit (n * m) ^ m = expNegUnit n := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  apply Units.ext
  rw [← zpow_natCast, expNegUnit_zpow_val, ← zpow_one (expNegUnit n), expNegUnit_zpow_val]
  congr 1
  push_cast
  field_simp

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) {i : Fin U.n}
  {P : (U.Di i).La →+ (Fin g → ℂ)}

theorem familyUnif_ex_nsmul (hP : IsPeriod (U.Di i) ty P) (n : ℕ) (z : Fin g → ℂ) :
    U.ex i P ((n : ℂ) • z) = U.ex i P z ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_smul, pow_zero]
    exact (U.ex_ker i P hP 0).2 (zero_mem _)
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, U.ex_add i P hP, ih, pow_succ]

noncomputable def familyUnifTateIso (hP : IsPeriod (U.Di i) ty P) :
    TateIso (U.Di i) ℂ (Over.mk (U.u i P) ⟶ Xo.univ.t.G) (fun a x => x ≫ Xo.univ.t.act.act a)
      (fun n x x' c => Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n x x' (unitOn c)) where
  ζ := expNegUnit
  ζ_prim _ hn := expNegUnit_isPrimitiveRoot hn
  ζ_pow _ _ hn hm := expNegUnit_mul_pow hn hm
  ev n a := U.ex i P ((n : ℂ)⁻¹ • P a)
  add n a b := by rw [map_add, smul_add, U.ex_add i P hP]
  lin n c a := by
    rw [← U.ex_lin i P hP]
    congr 1
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, hP.1]
    ring
  ker n hn a := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    rw [U.ex_ker i P hP]
    refine exists_congr fun b => ?_
    rw [eq_inv_smul_iff₀ hn', Nat.cast_smul_eq_nsmul, ← map_nsmul, hP.2.1.eq_iff, eq_comm]
  onto n hn x := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := U.ex_onto i P hP x
      rw [← familyUnif_ex_nsmul U hP, U.ex_ker i P hP] at hx
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [ha, inv_smul_smul₀ hn']⟩
    · rintro ⟨a, rfl⟩
      rw [← familyUnif_ex_nsmul U hP, smul_inv_smul₀ hn', U.ex_ker i P hP]
      exact ⟨a, rfl⟩
  tower n m hn hm a := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    rw [← familyUnif_ex_nsmul U hP, smul_smul]
    congr 2
    push_cast
    field_simp
  isom n hn a b := U.ex_weil i P hP n a b _ hn (expNegUnit_zpow_val n _)

end

theorem familyUnif_lattice_similar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)), IsPeriod (U.Di i) ty P → ∃ (f : ℕ → D.La →ₗ[𝓞 E] (U.Di i).La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) ∧ (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ (U.Di i).EF (f n a) (f n a') - ν n * D.EF a a') ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, f l.M a = U.t i a + l.M • e) ∧ ∀ a, ∃ e, f l.A a = U.t i a + l.A • e := by
  intro E _ _ _ H D l Xo σ g ty U i P hP
  obtain ⟨-, I, -, hA, hM⟩ := Xo.univ.geom ℂ (U.u i P) σ (U.over_σ i P hP)
  obtain ⟨f, ν, h1, h2, h3, h4, h5, h6⟩ := tateIso_similar_of_two_data
    (fun n x y c c' => weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ _ n x y c c') I (familyUnifTateIso U hP)
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  refine ⟨f, ν, h1, h2, h3, h4, h5, fun a ha => ?_, fun a => ?_⟩
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) hM0, ← h6 _ hM0, ← hM a ha]
    exact U.ex_eta i P hP a ha
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) l.A_pos, ← h6 _ l.A_pos, ← hA a]
    exact U.ex_etaA i P hP a

end GlobalTheory

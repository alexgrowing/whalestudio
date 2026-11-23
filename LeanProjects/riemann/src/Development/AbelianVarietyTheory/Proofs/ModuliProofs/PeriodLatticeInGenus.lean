import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsoDifferBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertUniformisationRiemannFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsionGenus

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_eq_iff (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a b : D.La) :
    I.ev n a = I.ev n b ↔ ∃ y, a = b + n • y := by
  rw [tateIso_ev_eq_iff I hn]
  unfold Datum.ModN
  exact exists_congr fun y => sub_eq_iff_eq_add'

theorem exists_lift (I' : TateIso D' k Q act e) (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) :
    ∃ f : D.La →ₗ[𝓞 E] D'.La, ∀ a, I.ev n a = I'.ev n (f a) := by
  have hs : ∀ a, ∃ b, I'.ev n b = I.ev n a := fun a => (I'.onto n hn _).1 (tateIso_ev_pow I hn a)
  choose s hs using hs
  let N : Submodule (𝓞 E) D'.La := LinearMap.range (n • (LinearMap.id : D'.La →ₗ[𝓞 E] D'.La))
  have hN : ∀ a b : D'.La, N.mkQ a = N.mkQ b ↔ I'.ev n a = I'.ev n b := by
    intro a b
    rw [tateIso_ev_eq_iff I' hn, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
  let φ : D.La →ₗ[𝓞 E] D'.La ⧸ N :=
    { toFun := fun a => N.mkQ (s a)
      map_add' := fun a b => by
        rw [← map_add, hN, I'.add, hs, hs, hs, I.add]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← map_smul, hN, I'.lin, hs, hs, I.lin] }
  have := D.proj
  obtain ⟨f, hf⟩ := Module.projective_lifting_property N.mkQ φ N.mkQ_surjective
  refine ⟨f, fun a => ?_⟩
  have h : N.mkQ (f a) = N.mkQ (s a) := LinearMap.congr_fun hf a
  rw [(hN _ _).1 h, hs]

theorem genus_of_tateIso
    (he : ∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c')
    (I' : TateIso D' k Q act e) (I : TateIso D k Q act e) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
      ((∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧
      (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧
      ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧
      ∀ n, 0 < n → I.ζ n = I'.ζ n ^ ν n ∧ ∀ a, I.ev n a = I'.ev n (f n a) := by
  have h1 : ∀ n : ℕ, ∃ f : D.La →ₗ[𝓞 E] D'.La, 0 < n → ∀ a, I.ev n a = I'.ev n (f a) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨0, fun h' => absurd h h'.ne'⟩
    · obtain ⟨f, hf⟩ := exists_lift I' I h
      exact ⟨f, fun _ => hf⟩
  have h2 : ∀ n : ℕ, ∃ ν : ℤ, 0 < n → I.ζ n = I'.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨1, fun h' => absurd h h'.ne'⟩
    · have : NeZero n := ⟨h.ne'⟩
      obtain ⟨i, -, hi⟩ := (I'.ζ_prim n h).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity _ _).2 (I.ζ_prim n h).pow_eq_one)
      exact ⟨i, fun _ => by rw [zpow_natCast, hi]⟩
  choose f hf using h1
  choose ν hν using h2
  refine ⟨f, ν, ⟨?_, ?_, ?_⟩, fun n hn => ⟨hν n hn, hf n hn⟩⟩
  · intro n m hn hm a
    rw [← ev_eq_iff I' hn, ← hf n hn, ← I'.tower n m hn hm, ← hf (n * m) (Nat.mul_pos hn hm),
      I.tower n m hn hm]
  · intro n hn
    refine ⟨fun x => ?_, fun x' => ?_⟩
    · rw [← I'.ker n hn, ← I.ker n hn, hf n hn]
    · obtain ⟨x, hx⟩ := (I.onto n hn _).1 (tateIso_ev_pow I' hn x')
      refine ⟨x, (ev_eq_iff I' hn _ _).1 ?_⟩
      rw [← hf n hn, hx]
  · intro n hn a b
    have e1 := I'.isom n hn (f n a) (f n b)
    have e2 := I.isom n hn a b
    rw [hf n hn a, hf n hn b] at e2
    have h := he n _ _ _ _ hn (tateIso_ev_pow I' hn _) (tateIso_ev_pow I' hn _) e1 e2
    rw [hν n hn, ← zpow_mul] at h
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]

end

theorem unitOn_injective {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := fun a b h => by
  have h1 := congrArg (fun x : (Γ(Sp R, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x.val) h
  apply Units.ext
  simpa [unitOn] using h1

noncomputable def expRoot (n : ℕ) : ℂˣ :=
  Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) / n)) (Complex.exp_ne_zero _)

theorem expRoot_zpow (n : ℕ) (m : ℤ) :
    ((expRoot n ^ m : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / n) := by
  rw [Units.val_zpow_eq_zpow_val, expRoot, Units.val_mk0, ← Complex.exp_int_mul]
  congr 1
  ring

theorem expRoot_prim {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (expRoot n) n := by
  rw [← IsPrimitiveRoot.coe_units_iff]
  have h := (Complex.isPrimitiveRoot_exp n hn.ne').inv
  rw [← Complex.exp_neg] at h
  rw [expRoot, Units.val_mk0, neg_div]
  exact h

theorem expRoot_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : expRoot (n * m) ^ m = expRoot n := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, expRoot, expRoot, Units.val_mk0, Units.val_mk0, ← Complex.exp_nat_mul]
  congr 1
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

section

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem

theorem ex_nsmul (n : ℕ) (z : Fin g → ℂ) : u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  induction n with
  | zero => simp [ex_zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

end

noncomputable def periodTateIso {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H)
    {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (act : OAct (𝓞 E) A)
    (Q : D'.La →+ (Fin g → ℂ)) (hQ : Function.Injective Q) (hΛ : ∀ z, z ∈ u.Λ ↔ z ∈ Q.range)
    (hact : ∀ (a : 𝓞 E) (n : ℕ) x, u.ex ((n : ℂ)⁻¹ • Q (a • x)) = u.ex ((n : ℂ)⁻¹ • Q x) ≫ act.act a)
    (hW : ∀ (n : ℕ) (a b : D'.La) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / n) →
      Out.WeilIs A L n (u.ex ((n : ℂ)⁻¹ • Q a)) (u.ex ((n : ℂ)⁻¹ • Q b)) (unitOn c)) :
    TateIso D' ℂ (𝟙_ (Over (Sp ℂ)) ⟶ A) (fun c y => y ≫ act.act c)
      (fun n y y' c => Out.WeilIs A L n y y' (unitOn c)) where
  ζ := expRoot
  ζ_prim _ hn := expRoot_prim hn
  ζ_pow _ _ hn hm := expRoot_pow hn hm
  ev n x := u.ex ((n : ℂ)⁻¹ • Q x)
  add n a b := by rw [map_add, smul_add, u.ex_add]
  lin n c a := hact c n a
  ker n hn a := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [u.ker, hΛ]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, hQ ?_⟩
      rw [map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hn', one_smul]
    · rintro ⟨b, rfl⟩
      refine ⟨b, ?_⟩
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn', one_smul]
  onto n hn x := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := u.ex_onto x
      rw [← ex_nsmul, u.ker, hΛ] at hx
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [ha, smul_smul, inv_mul_cancel₀ hn', one_smul]⟩
    · rintro ⟨a, rfl⟩
      rw [← ex_nsmul, u.ker, hΛ, smul_smul, mul_inv_cancel₀ hn', one_smul]
      exact ⟨a, rfl⟩
  tower n m hn hm a := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [← ex_nsmul, smul_smul]
    congr 2
    push_cast
    field_simp
  isom n hn a b := hW n a b _ hn (expRoot_zpow n _)

theorem period_lattice_in_genus :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (D' : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (Q : D'.La →+ (Fin P.g → ℂ)), D'.p = D.p → D'.q = D.q → u.IsAH Hm χ → Function.Injective Q → (∀ z, z ∈ u.Λ ↔ z ∈ Q.range) → (∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) → (∀ (a : 𝓞 E) (n : ℕ) x, u.ex ((n : ℂ)⁻¹ • Q (a • x)) = u.ex ((n : ℂ)⁻¹ • Q x) ≫ act.act a) → ∀ I : TateIso D ℂ (Over.mk (𝟙 (Sp ℂ)) ⟶ P.A) (fun c y => y ≫ act.act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧ ∀ n : ℕ, 0 < n → (I.ζ n : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν n : ℂ) / n) ∧ ∀ x, (I.ev n x).left = (u.ex ((n : ℂ)⁻¹ • Q (f n x))).left := by
  intro hL hL2 hT hU E _ _ _ H D D' P u Hm χ act Q hp hq hAH hQ hΛ hE hact I
  obtain ⟨Ef, hEf, -, -, -, -, -, -, hW⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm hL hL2 hT hU P u Hm χ hAH
  have hW' : ∀ (n : ℕ) (a b : D'.La) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / n) →
      Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • Q a)) (u.ex ((n : ℂ)⁻¹ • Q b)) (unitOn c) := by
    intro n a b c hn hc
    refine hW n ⟨Q a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨Q b, (hΛ _).2 ⟨b, rfl⟩⟩ c hn ?_
    have h := hEf ⟨Q a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨Q b, (hΛ _).2 ⟨b, rfl⟩⟩
    rw [hE] at h
    rw [Int.cast_injective h]
    exact hc
  obtain ⟨f, ν, ⟨h1, h2, h3⟩, h4⟩ := genus_of_tateIso (D := D) (D' := D')
    (fun n x y c c' _ hx hy ha hb =>
      unitOn_injective (((hL.weil _ P n (Over.mk (𝟙 (Sp ℂ)))).1 x y hx hy).unique ha hb))
    (periodTateIso D' u act Q hQ hΛ hact hW') I
  refine ⟨f, ν, ⟨hp, hq, h1, h2, h3⟩, fun n hn => ⟨?_, fun x => ?_⟩⟩
  · rw [(h4 n hn).1]
    exact expRoot_zpow n _
  · rw [(h4 n hn).2]
    rfl

end GlobalTheory.TorsionGenus

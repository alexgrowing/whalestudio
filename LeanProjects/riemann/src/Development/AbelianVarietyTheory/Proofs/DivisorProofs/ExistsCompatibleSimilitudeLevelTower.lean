import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.TowerLev

theorem compat_seq {X : Type} (A : ℕ → Set X) (hfin : ∀ j, (A j).Finite)
    (hne : ∀ j, (A j).Nonempty) (φ : ℕ → X → X) (hφ : ∀ j, ∀ x ∈ A (j + 1), φ j x ∈ A j) :
    ∃ s : ℕ → X, ∀ j, s j ∈ A j ∧ φ j (s (j + 1)) = s j := by
  let F : ℕᵒᵖ ⥤ Type := Functor.ofOpSequence (X := fun j => ↥(A j))
    (fun j => TypeCat.ofHom (fun x => ⟨φ j x.1, hφ j x.1 x.2⟩ : ↥(A (j + 1)) → ↥(A j)))
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => (hfin j.unop).to_subtype
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => (hne j.unop).to_subtype
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun j => (s (Opposite.op j)).1, fun j => ⟨(s (Opposite.op j)).2, ?_⟩⟩
  have h := hs (homOfLE (Nat.le_add_right j 1)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  exact congrArg Subtype.val h

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] {Q : Type} [CommGroup Q]

def IsLev (D : Datum p) (act : D.O → Q → Q) (W : ℕ → Q → Q → kˣ) (ζ : ℕ → kˣ) (r : ℕ) (f : D.La → Q) : Prop :=
  ((∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧
    (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g)) ∧
    ∀ x y, W r (f x) (f y) = ζ r ^ D.EF x y

variable {D : Datum p}

theorem map_zero_of_add {f : D.La → Q} (hf : ∀ x y, f (x + y) = f x * f y) : f 0 = 1 := by
  have h := hf 0 0
  rw [add_zero] at h
  simpa using h.symm

theorem map_nsmul_of_add {f : D.La → Q} (hf : ∀ x y, f (x + y) = f x * f y) (n : ℕ) (x : D.La) :
    f (n • x) = f x ^ n := by
  induction n with
  | zero => simp [map_zero_of_add hf]
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem cancel_nsmul (D : Datum p) (n : ℕ) (hn : n ≠ 0) {a b : D.La} (h : n • a = n • b) : a = b := by
  haveI := D.freeLa
  have h' : (n : ℤ) • a = (n : ℤ) • b := by simpa [natCast_zsmul] using h
  exact smul_right_injective D.La (by exact_mod_cast hn : (n : ℤ) ≠ 0) h'

theorem IsLev.step {act : D.O → Q → Q} {W : ℕ → Q → Q → kˣ} {ζ : ℕ → kˣ}
    (hact : ∀ c a b, act c (a * b) = act c a * act c b) (hζ : ∀ r, ζ (r + 1) ^ p = ζ r)
    (hW : ∀ r (a b : Q), a ^ (p ^ (r + 1)) = 1 → b ^ (p ^ (r + 1)) = 1 →
      W r (a ^ p) (b ^ p) = W (r + 1) a b ^ p)
    (r : ℕ) (f : D.La → Q) (hf : IsLev D act W ζ (r + 1) f) : IsLev D act W ζ r (fun x => f x ^ p) := by
  obtain ⟨⟨hadd, hlin, hker, honto⟩, hpair⟩ := hf
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hkill : ∀ x, f x ^ (p ^ (r + 1)) = 1 := fun x => (honto _).2 ⟨x, rfl⟩
  refine ⟨⟨fun x y => ?_, fun c x => ?_, fun x => ?_, fun g => ?_⟩, fun x y => ?_⟩
  · simp only
    rw [hadd, mul_pow]
  · simp only
    rw [hlin]
    exact (map_pow (MonoidHom.mk' (act c) (hact c)) (f x) p).symm
  · simp only
    rw [← map_nsmul_of_add hadd, hker]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, cancel_nsmul D p hp0 (by rw [hy, pow_succ', mul_smul])⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [pow_succ', mul_smul]⟩
  · simp only
    constructor
    · intro hg
      have hg' : g ^ (p ^ (r + 1)) = 1 := by rw [pow_succ, pow_mul, hg, one_pow]
      obtain ⟨x, rfl⟩ := (honto g).1 hg'
      rw [← map_nsmul_of_add hadd, hker] at hg
      obtain ⟨y, hy⟩ := hg
      have hx : x = p • y := cancel_nsmul D (p ^ r) (pow_ne_zero _ hp0) (by rw [hy, pow_succ, mul_smul])
      exact ⟨y, by rw [hx, map_nsmul_of_add hadd]⟩
    · rintro ⟨x, rfl⟩
      rw [← pow_mul, ← pow_succ', hkill]
  · simp only
    rw [hW r (f x) (f y) (hkill x) (hkill y), hpair, ← hζ r, ← zpow_natCast (ζ (r + 1) ^ _),
      ← zpow_natCast (ζ (r + 1)), ← zpow_mul, ← zpow_mul, mul_comm]

theorem finite_range_of_add {f : D.La → Q} (hadd : ∀ x y, f (x + y) = f x * f y) {n : ℕ} (hn : n ≠ 0)
    (hker : ∀ y, f (n • y) = 1) : (Set.range f).Finite := by
  haveI := D.freeLa
  haveI := D.finLa
  let B := Module.Free.chooseBasis ℤ D.La
  have hpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine ((Set.Finite.pi (fun _ : Module.Free.ChooseBasisIndex ℤ D.La => Set.finite_Ico (0 : ℤ) n)).image
    (fun v => f (∑ i, v i • B i))).subset ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨fun i => B.repr x i % n, fun i _ => ⟨Int.emod_nonneg _ hpos.ne', Int.emod_lt_of_pos _ hpos⟩, ?_⟩
  have hx : x = ∑ i, (B.repr x i % n) • B i + n • ∑ i, (B.repr x i / n) • B i := by
    rw [← natCast_zsmul, Finset.smul_sum, ← Finset.sum_add_distrib]
    conv_lhs => rw [← B.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← add_smul, Int.emod_add_mul_ediv]
  rw [congrArg f hx, hadd, hker, _root_.mul_one]

def toLin (f : D.La → Q) (hf : ∀ x y, f (x + y) = f x * f y) : D.La →ₗ[ℤ] Additive Q :=
  (AddMonoidHom.mk' (fun x => Additive.ofMul (f x)) (fun x y => by rw [hf]; rfl)).toIntLinearMap

theorem finite_isLev {act : D.O → Q → Q} {W : ℕ → Q → Q → kˣ} {ζ : ℕ → kˣ} (r : ℕ) :
    {f | IsLev D act W ζ r f}.Finite := by
  rcases Set.eq_empty_or_nonempty {f | IsLev D act W ζ r f} with h | ⟨f0, hf0⟩
  · rw [h]; exact Set.finite_empty
  haveI := D.freeLa
  haveI := D.finLa
  let B := Module.Free.chooseBasis ℤ D.La
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hT : (Set.range f0).Finite :=
    finite_range_of_add hf0.1.1 (pow_ne_zero r hp0) (fun y => (hf0.1.2.2.1 _).2 ⟨y, rfl⟩)
  refine Set.Finite.of_finite_image (f := fun f : D.La → Q => fun i => f (B i)) ?_ ?_
  · refine (Set.Finite.pi (fun _ => hT)).subset ?_
    rintro _ ⟨f, hf, rfl⟩ i _
    exact (hf0.1.2.2.2 _).1 ((hf.1.2.2.2 _).2 ⟨B i, rfl⟩)
  · intro f hf g hg hfg
    have key : toLin f hf.1.1 = toLin g hg.1.1 :=
      B.ext (fun i => congrArg Additive.ofMul (congrFun hfg i))
    funext x
    exact congrArg Additive.toMul (LinearMap.congr_fun key x)

theorem exists_compatible : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] (Q : Type) [CommGroup Q]
    (act : D.O → Q → Q) (W : ℕ → Q → Q → kˣ) (ζ : ℕ → kˣ), (∀ c a b, act c (a * b) = act c a * act c b) →
    (∀ r, ζ (r + 1) ^ p = ζ r) →
    (∀ r (a b : Q), a ^ (p ^ (r + 1)) = 1 → b ^ (p ^ (r + 1)) = 1 → W r (a ^ p) (b ^ p) = W (r + 1) a b ^ p) →
    (∀ r, ∃ f : D.La → Q, ((∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧
      (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g)) ∧
      ∀ x y, W r (f x) (f y) = ζ r ^ D.EF x y) →
    ∃ ev : ℕ → D.La → Q, (∀ r, ((∀ x y, ev r (x + y) = ev r x * ev r y) ∧
      (∀ (c : D.O) x, ev r (c • x) = act c (ev r x)) ∧ (∀ x, ev r x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧
      (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, ev r x = g)) ∧ ∀ x y, W r (ev r x) (ev r y) = ζ r ^ D.EF x y) ∧
      ∀ r x, ev (r + 1) x ^ p = ev r x := by
  intro p _ D k _ Q _ act W ζ hact hζ hW hex
  obtain ⟨s, hs⟩ := compat_seq (fun r => {f | IsLev D act W ζ r f}) (fun r => finite_isLev r) hex
    (fun _ f x => f x ^ p) (fun r f hf => IsLev.step hact hζ hW r f hf)
  exact ⟨s, fun r => (hs r).1, fun r x => congrFun (hs r).2 x⟩

end GlobalTheory.TowerLev

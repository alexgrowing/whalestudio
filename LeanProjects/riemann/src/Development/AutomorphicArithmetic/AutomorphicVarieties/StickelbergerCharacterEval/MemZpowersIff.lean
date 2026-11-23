import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle

noncomputable section

namespace UpperTheory.V.B5

open UpperTheory.V.Bern UpperTheory.V.B4

section Ring

variable (A : Type) [CommRing A] {Γ : Type} [CommGroup Γ]

def rel (c : Γ) (ε : ℤ) : MonoidAlgebra A Γ := MonoidAlgebra.single c 1 - (ε : MonoidAlgebra A Γ)

abbrev Rq (c : Γ) (ε : ℤ) : Type := MonoidAlgebra A Γ ⧸ Ideal.span {rel A c ε}

abbrev Rqz (c : Γ) (ε : ℤ) (z : MonoidAlgebra A Γ) : Type := MonoidAlgebra A Γ ⧸ Ideal.span {rel A c ε, z}

abbrev cls (c : Γ) (ε : ℤ) : MonoidAlgebra A Γ →+* Rq A c ε := Ideal.Quotient.mk _

variable {A}

def Qc (c : Γ) : Type := Γ ⧸ Subgroup.zpowers c

instance (c : Γ) : DecidableEq (Qc c) := Classical.decEq _

instance (c : Γ) : Inhabited (Qc c) := ⟨(QuotientGroup.mk 1 : Γ ⧸ Subgroup.zpowers c)⟩

instance [Finite Γ] (c : Γ) : Fintype (Qc c) := @Fintype.ofFinite (Γ ⧸ Subgroup.zpowers c) inferInstance

def Qc.mk (c : Γ) (g : Γ) : Qc c := (QuotientGroup.mk g : Γ ⧸ Subgroup.zpowers c)

def rep {c : Γ} (i : Qc c) : Γ := Quotient.out (i : Γ ⧸ Subgroup.zpowers c)

def coord (c : Γ) (ε : ℤ) (w : MonoidAlgebra A Γ) : Qc c → A :=
  fun i => w.coeff (rep i) + (ε : A) * w.coeff (c * rep i)

def mat (c : Γ) (ε : ℤ) (z : MonoidAlgebra A Γ) : Matrix (Qc c) (Qc c) A :=
  Matrix.of fun i j => z.coeff (rep i * (rep j)⁻¹) + (ε : A) * z.coeff (c * (rep i * (rep j)⁻¹))

def detR [Finite Γ] (c : Γ) (ε : ℤ) (z : MonoidAlgebra A Γ) : A := (mat c ε z).det

theorem mk_rep {c : Γ} (i : Qc c) : Qc.mk c (rep i) = i := Quotient.out_eq _

theorem mem_zpowers_iff {c : Γ} (h2 : c * c = 1) (g : Γ) : g ∈ Subgroup.zpowers c ↔ g = 1 ∨ g = c := by
  constructor
  · rintro ⟨n, rfl⟩
    have h : c ^ (2 : ℤ) = 1 := by rw [zpow_two, h2]
    rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
    · left; simp only [zpow_mul, h, one_zpow]
    · right; simp only [zpow_add, zpow_mul, h, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    exacts [one_mem _, Subgroup.mem_zpowers _]

theorem mk_eq_mk {c : Γ} (h2 : c * c = 1) (g h : Γ) : Qc.mk c g = Qc.mk c h ↔ h = g ∨ h = c * g := by
  refine QuotientGroup.eq.trans ((mem_zpowers_iff h2 _).trans ?_)
  rw [inv_mul_eq_one, inv_mul_eq_iff_eq_mul, mul_comm g c, eq_comm]

theorem sum_rep [Fintype Γ] {M : Type} [AddCommMonoid M] {c : Γ} (h2 : c * c = 1) (h1 : c ≠ 1) (f : Γ → M) :
    ∑ g, f g = ∑ i : Qc c, (f (rep i) + f (c * rep i)) := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (Qc.mk c) f]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Finset.univ.filter (fun g => Qc.mk c g = i) = {rep i, c * rep i} := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    rw [← mk_eq_mk h2, mk_rep, eq_comm]
  rw [this, Finset.sum_pair]
  intro h
  exact h1 (by simpa using h)

theorem card_Qc [Finite Γ] {c : Γ} (h2 : c * c = 1) (h1 : c ≠ 1) : Nat.card Γ = 2 * Fintype.card (Qc c) := by
  have := Fintype.ofFinite Γ
  have h := sum_rep h2 h1 (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  rw [Nat.card_eq_fintype_card, h, mul_comm]

theorem card_Qc' [Finite Γ] {c : Γ} (h2 : c * c = 1) (h1 : c ≠ 1) : Fintype.card (Qc c) = Nat.card Γ / 2 := by
  rw [card_Qc h2 h1]; omega

theorem mat_map {B : Type} [CommRing B] (f : A →+* B) (c : Γ) (ε : ℤ) (z : MonoidAlgebra A Γ) :
    mat c ε (MonoidAlgebra.mapRingHom Γ f z) = (mat c ε z).map f := by
  ext i j
  simp [mat]

theorem detR_map [Finite Γ] {B : Type} [CommRing B] (f : A →+* B) (c : Γ) (ε : ℤ) (z : MonoidAlgebra A Γ) :
    detR c ε (MonoidAlgebra.mapRingHom Γ f z) = f (detR c ε z) := by
  rw [detR, mat_map, detR, RingHom.map_det, RingHom.mapMatrix_apply]

theorem mat_smul (c : Γ) (ε : ℤ) (s : A) (z : MonoidAlgebra A Γ) : mat c ε (s • z) = s • mat c ε z := by
  ext i j
  simp [mat]; ring

theorem detR_smul [Finite Γ] (c : Γ) (ε : ℤ) (s : A) (z : MonoidAlgebra A Γ) :
    detR c ε (s • z) = s ^ Fintype.card (Qc c) * detR c ε z := by
  rw [detR, mat_smul, Matrix.det_smul, detR]

theorem coefMap_eq (B : Type) [CommRing B] : coefMap B Γ = MonoidAlgebra.mapRingHom Γ (Int.castRingHom B) := by
  refine RingHom.ext fun z => ?_
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single g n => simp [coefMap_single]

theorem coeff_coefMap (B : Type) [CommRing B] (z : MonoidAlgebra ℤ Γ) (g : Γ) :
    (coefMap B Γ z).coeff g = ((z.coeff g : ℤ) : B) := by
  simp [coefMap_eq]

theorem detR_coefMap [Finite Γ] (B : Type) [CommRing B] (c : Γ) (ε : ℤ) (z : MonoidAlgebra ℤ Γ) :
    detR c ε (coefMap B Γ z) = ((detR c ε z : ℤ) : B) := by
  rw [coefMap_eq, detR_map]; rfl

end Ring

section Chars

variable {Γ : Type} [CommGroup Γ]

def Ch (Ω : Type) [Field Ω] (c : Γ) (ε : ℤ) : Type := {χ : Γ →* Ωˣ // ((χ c : Ωˣ) : Ω) = (ε : Ω)}

instance (Ω : Type) [Field Ω] (c : Γ) : Inhabited (Ch Ω c 1) := ⟨⟨1, by simp⟩⟩

instance (Ω : Type) [Field Ω] (c : Γ) (ε : ℤ) : DecidableEq (Ch Ω c ε) := Classical.decEq _

instance [Finite Γ] (Ω : Type) [Field Ω] (c : Γ) (ε : ℤ) : Fintype (Ch Ω c ε) :=
  @Fintype.ofFinite {χ : Γ →* Ωˣ // ((χ c : Ωˣ) : Ω) = (ε : Ω)} inferInstance

def ev (A : Type) [CommRing A] {Ω : Type} [Field Ω] [Algebra A Ω] (χ : Γ →* Ωˣ) : MonoidAlgebra A Γ →ₐ[A] Ω :=
  MonoidAlgebra.lift A Ω Γ ((Units.coeHom Ω).comp χ)

@[simp] theorem ev_single (A : Type) [CommRing A] {Ω : Type} [Field Ω] [Algebra A Ω] (χ : Γ →* Ωˣ) (g : Γ) (s : A) :
    ev A χ (MonoidAlgebra.single g s) = algebraMap A Ω s * ((χ g : Ωˣ) : Ω) := by
  simp [ev, Algebra.smul_def]

def dirOf {N : ℕ} {Ω : Type} [Field Ω] (π : (ZMod N)ˣ →* Γ) (χ : Γ →* Ωˣ) : DirichletCharacter Ω N :=
  MulChar.ofUnitHom (χ⁻¹.comp π)

@[simp] theorem dirOf_unit {N : ℕ} {Ω : Type} [Field Ω] (π : (ZMod N)ˣ →* Γ) (χ : Γ →* Ωˣ) (b : (ZMod N)ˣ) :
    dirOf π χ (b : ZMod N) = ((χ (π b)⁻¹ : Ωˣ) : Ω) := by
  simp [dirOf]

end Chars

def InPow (l : ℕ) [Fact l.Prime] (t : ℕ) (x : ℚ) : Prop := x / (l : ℚ) ^ t ∈ Zl l

theorem intAt_iff {Γ : Type} [CommGroup Γ] (l : ℕ) [Fact l.Prime] (t : ℕ) (z : MonoidAlgebra ℚ Γ) :
    IntAt l t z ↔ ∀ g, InPow l t (z.coeff g) := Iff.rfl

theorem InPow.zero (l : ℕ) [Fact l.Prime] (t : ℕ) : InPow l t 0 := by
  simp [InPow]

theorem InPow.add {l : ℕ} [Fact l.Prime] {t : ℕ} {x y : ℚ} (hx : InPow l t x) (hy : InPow l t y) : InPow l t (x + y) := by
  rw [InPow, add_div]; exact (Zl l).add_mem hx hy

theorem InPow.mul {l : ℕ} [Fact l.Prime] {t : ℕ} {x y : ℚ} (hx : x ∈ Zl l) (hy : InPow l t y) : InPow l t (x * y) := by
  rw [InPow, mul_div_assoc]; exact (Zl l).mul_mem hx hy

theorem InPow.mem {l : ℕ} [Fact l.Prime] {t : ℕ} {x : ℚ} (hx : InPow l t x) : x ∈ Zl l := by
  have hl : (l : ℚ) ^ t ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have := (Zl l).mul_mem hx (pow_mem (natCast_mem (Zl l) l) t)
  rwa [div_mul_cancel₀ _ hl] at this

def denY (N k : ℕ) : ℕ := N * k * (k + 1).factorial

def sizeY (N a k : ℕ) : ℕ := 2 * a ^ k * N ^ k * k.factorial

def bdX (N a k : ℕ) : ℕ := denY N k * sizeY N a k

def BD (r N a e : ℕ) : ℝ :=
  r * ((e + 2) * Real.logb 2 N + (e + 1) * Real.logb 2 a + 1 +
    Real.logb 2 ((e + 1) * (e + 1).factorial * (e + 2).factorial))

theorem denY_pos {N k : ℕ} (hN : 0 < N) (hk : 0 < k) : 0 < denY N k := by
  unfold denY; positivity

end UpperTheory.V.B5

end

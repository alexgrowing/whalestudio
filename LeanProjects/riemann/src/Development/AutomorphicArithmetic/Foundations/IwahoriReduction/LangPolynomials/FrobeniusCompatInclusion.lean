import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def R0 (A : ValuationSubring Ω) : Subring Ω where
  carrier := {x | x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x}
  mul_mem' ha hb := ⟨A.mul_mem _ _ ha.1 hb.1, fun s hs => by rw [map_mul, ha.2 s hs, hb.2 s hs]⟩
  one_mem' := ⟨A.one_mem, fun s _ => map_one s⟩
  add_mem' ha hb := ⟨A.add_mem _ _ ha.1 hb.1, fun s hs => by rw [map_add, ha.2 s hs, hb.2 s hs]⟩
  zero_mem' := ⟨A.zero_mem, fun s _ => map_zero s⟩
  neg_mem' ha := ⟨A.neg_mem _ ha.1, fun s hs => by rw [map_neg, ha.2 s hs]⟩

variable (l : ℕ) [Fact l.Prime]

def Hm (A : ValuationSubring Ω) (m : ℕ) : Subgroup (G ℚ Ω) := Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker

structure Fr (A : ValuationSubring Ω) (j : Ω →+* Qbar l) : Type 1 where
  R : Type
  [cr : CommRing R]
  [al : Algebra ℤ_[l] R]
  σ : R ≃+* R
  fl : FrobLift R l σ
  closed : ∀ P : Polynomial R, P.Monic → 0 < P.natDegree → ∃ x : R, P.eval x ∈ Ideal.span {(l : R)}
  unit : ∀ x : R, x ∉ Ideal.span {(l : R)} → IsUnit x
  fixed : ∀ x : R, σ x = x → ∃ z : ℤ_[l], algebraMap ℤ_[l] R z = x
  i0 : R0 A →+* R
  dense : ∀ (x : R) (n : ℕ), ∃ y : R0 A, x - i0 y ∈ Ideal.span {(l : R) ^ n}
  sep : ∀ (y : R0 A) (n : ℕ), i0 y ∈ Ideal.span {(l : R) ^ n} → y ∈ Ideal.span {(l : R0 A) ^ n}
  fr : G ℚ Ω
  fr_dec : fr ∈ Dec (F := ℚ) A
  fr_frob : IsFrob A l fr
  fr_cyc : cycBar ℚ Ω l fr = 1
  frobenius_compat_inclusion : ∀ y y' : R0 A, (y' : Ω) = fr y → σ (i0 y) = i0 y'
  jh : R →+* ℂ_[l]
  jh_comp_incl : ∀ y : R0 A, jh (i0 y) = algebraMap (PadicAlgCl l) ℂ_[l] (j y)
  jh_alg : ∀ z : ℤ_[l], jh (algebraMap ℤ_[l] R z) = algebraMap (PadicAlgCl l) ℂ_[l] (algebraMap ℤ_[l] (PadicAlgCl l) z)
  jh_le : ∀ x, ‖jh x‖ ≤ 1

attribute [instance] Fr.cr Fr.al

variable {l}

structure Bas (c : Coef l) where
  d : ℕ
  e : Module.Basis (Fin d) ℤ_[l] c.O

def Bas.val {c : Coef l} (β : Bas c) (i : Fin β.d) : Qbar l := ((β.e i : c.O) : PadicAlgCl l)

def Bas.mat {c : Coef l} (β : Bas c) (b : c.O) : Matrix (Fin β.d) (Fin β.d) ℤ_[l] := Algebra.leftMulMatrix β.e b

abbrev Sy (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] : Type := ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l

abbrev red (l r : ℕ) : (ZMod (l ^ (r + 1)))ˣ →* (ZMod (l ^ r))ˣ :=
  Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom

structure IwI (c : Coef l) (A : ValuationSubring Ω) (Z : Sy Ω l) : Prop where
  int : ∀ r, ∀ s ∈ Ine (F := ℚ) A, ∀ x, Z r s x ∈ c.O
  coc : ∀ r, ∀ s ∈ Ine (F := ℚ) A, ∀ t ∈ Ine (F := ℚ) A, ∀ x, Z r (s * t) x = Z r s x + Z r t (x * (cycMod ℚ Ω l r s)⁻¹)
  nrm : ∀ r, ∀ s ∈ Ine (F := ℚ) A, ∀ x : (ZMod (l ^ r))ˣ,
    Z r s x = ∑ x' ∈ (Finset.univ.filter fun x' : (ZMod (l ^ (r + 1)))ˣ => red l r x' = x), Z (r + 1) s x'

def Cont (A : ValuationSubring Ω) (Z : Sy Ω l) : Prop :=
  ∀ r n : ℕ, ∃ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ s ∈ U, s ∈ Ine (F := ℚ) A → ∀ x, Cg n (Z r s x) 0

def un (b : ℕ) (hb : ¬ l ∣ b) (r : ℕ) : (ZMod (l ^ r))ˣ :=
  ZMod.unitOfCoprime b (((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hb).symm.pow_right r)

def tr (b : ℕ) (hb : ¬ l ∣ b) (Z : Sy Ω l) : Sy Ω l := fun r s x => Z r s (x * un b hb r)

def sharp (b : ℕ) (hb : ¬ l ∣ b) (Z : Sy Ω l) : Sy Ω l := fun r s x => Z r s x - (b : Qbar l) * tr b hb Z r s x

def Roots (l : ℕ) (ζ : ℕ → Ω) : Prop := ∀ m, IsPrimitiveRoot (ζ m) (l ^ m) ∧ ζ (m + 1) ^ l = ζ m

def pv {A : ValuationSubring Ω} (P : Polynomial (R0 A)) (z : Ω) : Ω := P.eval₂ (R0 A).subtype z

def BPres {c : Coef l} (β : Bas c) (A : ValuationSubring Ω) (ζ : ℕ → Ω) (Z : Sy Ω l) (m n : ℕ)
    (P : Fin β.d → Polynomial (R0 A)) : Prop :=
  KumPres A n m (ζ n) (Z m) (fun i => pv (P i) (ζ m)) β.val

def HasPres {c : Coef l} (β : Bas c) (A : ValuationSubring Ω) (ζ : ℕ → Ω) (Z : Sy Ω l) : Prop :=
  ∃ c₀ m₀ : ℕ, ∀ m, m₀ ≤ m → ∃ P, BPres β A ζ Z m (m - c₀) P

section Frame

variable {A : ValuationSubring Ω} {j : Ω →+* Qbar l} (Φ : Fr l A j)

def Fr.ser (P : Polynomial (R0 A)) : PowerSeries Φ.R := (P.map Φ.i0).eval₂ PowerSeries.C (1 + PowerSeries.X)

def Fr.tw (m : ℕ) (h : PowerSeries Φ.R) : PowerSeries Φ.R := PowerSeries.map (((Φ.σ.symm : Φ.R ≃+* Φ.R) : Φ.R →+* Φ.R) ^ m) h

def Fr.act {d : ℕ} (M : Matrix (Fin d) (Fin d) ℤ_[l]) (D : Fin d → PowerSeries Φ.R) : Fin d → PowerSeries Φ.R :=
  fun i => ∑ k, PowerSeries.C (algebraMap ℤ_[l] Φ.R (M i k)) * D k

def Fr.lam {c : Coef l} (β : Bas c) (x : Fin β.d → Φ.R) : ℂ_[l] := ∑ i, algebraMap (PadicAlgCl l) ℂ_[l] (β.val i) * Φ.jh (x i)

end Frame

def LC {R : Type} [CommRing R] (l m n : ℕ) (f g : PowerSeries R) : Prop :=
  ev R l m f - ev R l m g ∈ Ideal.span {((l : ℕ) : lev R l m) ^ n}

def dl {R : Type} [CommRing R] (f : PowerSeries R) : PowerSeries R := dd f * Ring.inverse f

def Rep {A : ValuationSubring Ω} {j : Ω →+* Qbar l} (Φ : Fr l A j) {c : Coef l} (β : Bas c) (ζ : ℕ → Ω) (Z : Sy Ω l)
    (D : Fin β.d → PowerSeries Φ.R) : Prop :=
  ∃ c₁ m₁ : ℕ, ∀ m, m₁ ≤ m → ∃ P, BPres β A ζ Z m (m - c₁) P ∧ ∀ i, LC l m (m - c₁) (Φ.tw m (D i)) (dl (Φ.ser (P i)))

abbrev eta (φ : DirichletCharacter (Qbar l) l) (k r : ℕ) : (ZMod (l ^ r))ˣ → Qbar l :=
  fun x => (φ (x : ZMod (l ^ r)).val)⁻¹ * ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ k)⁻¹

def SpZero (A : ValuationSubring Ω) (φ : DirichletCharacter (Qbar l) l) (k : ℕ) (Z : Sy Ω l) : Prop :=
  ∀ n : ℕ, ∃ r₀, ∀ r, r₀ ≤ r → ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 → Cg n (sp (eta φ k r) (Z r) s) 0

abbrev intg (φ : DirichletCharacter (Qbar l) l) (k : ℕ) (L : PowerSeries (Qbar l)) (r : ℕ) (ξ : Qbar l) : Qbar l :=
  ∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ k) * mass L r ξ x

def IntZero (φ : DirichletCharacter (Qbar l) l) (k : ℕ) (L : PowerSeries (Qbar l)) : Prop :=
  ∀ n : ℕ, ∃ r₁, ∀ r, r₁ ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) → Cg (n + r) (intg φ k L r ξ) 0

theorem iwI_zero (c : Coef l) (A : ValuationSubring Ω) : IwI c A (fun _ _ _ => 0) :=
  ⟨fun _ _ _ _ => zero_mem _, by simp, by simp⟩

end UpperTheory.Kd.C7

import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.ScaledValuations.ValuationApplyLtOneIff
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CocyclesCyclotomicFinrankThree

noncomputable section

namespace GlobalTheory.OrdLoc.Dcmp

open Formalism.ConjugateSelfDual Formalism.MainNotions.V

section Level

variable {G : Type} [Group G] [TopologicalSpace G] {R : Type} [CommRing R]

def finiteCocycles (γ : G →* Rˣ) : Set (G → R) :=
  {z | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + (γ g : R) * z h}

def IsTwistedTwoCocycle (γ : G →* Rˣ) (f : G × G → R) : Prop :=
  IsLocallyConstant f ∧ ∀ g h k, (γ g : R) * f (h, k) - f (g * h, k) + f (g, h * k) - f (g, h) = 0

def IsTwistedTwoCoboundary (γ : G →* Rˣ) (f : G × G → R) : Prop :=
  ∃ b : G → R, IsLocallyConstant b ∧ ∀ g h, f (g, h) = (γ g : R) * b h - b (g * h) + b g

def chR {H S T : Type} [Group H] [CommRing S] [CommRing T] (z : S →+* T) (χ : H →* Sˣ) : H →* Tˣ :=
  (Units.map z.toMonoidHom).comp χ

@[simp] theorem chR_apply {H S T : Type} [Group H] [CommRing S] [CommRing T] (z : S →+* T) (χ : H →* Sˣ) (g : H) :
    (chR z χ g : T) = z (χ g : S) := rfl

def diffId {H : Type} [Group H] (γ δ : H →* Rˣ) : Ideal R := Ideal.span (Set.range fun g => (γ g : R) - (δ g : R))

variable {l : ℕ} [Fact l.Prime]

def FinCount (χ : G →* ℤ_[l]ˣ) : Prop :=
  ∀ (R : Type) [CommRing R] [Finite R] (r : ℕ), (l : R) ^ r = 0 → ∀ (z : ℤ_[l] →+* R) (γ : G →* Rˣ),
    IsLocallyConstant (fun g => (γ g : R)) →
      (finiteCocycles γ).Finite ∧ (finiteCocycles γ).ncard = Nat.card (R ⧸ diffId γ (chR z χ)) * Nat.card R ^ 2

def FinKill (χ : G →* ℤ_[l]ˣ) : Prop :=
  ∀ (R : Type) [CommRing R] [Finite R] (r : ℕ), (l : R) ^ r = 0 → ∀ (z : ℤ_[l] →+* R) (γ : G →* Rˣ),
    IsLocallyConstant (fun g => (γ g : R)) → ∀ f, IsTwistedTwoCocycle γ f → ∀ a ∈ diffId γ (chR z χ), IsTwistedTwoCoboundary γ (a • f)

def FinTop (χ : G →* ℤ_[l]ˣ) : Prop :=
  ∀ (R : Type) [CommRing R] [Finite R] (r : ℕ), (l : R) ^ r = 0 → ∀ (z : ℤ_[l] →+* R) (f f' : G × G → R),
    IsTwistedTwoCocycle (chR z χ) f → IsTwistedTwoCocycle (chR z χ) f' →
      ∃ x y : R, ∀ a b : R, a * x + b * y = 0 → IsTwistedTwoCoboundary (chR z χ) (a • f + b • f')

def CocZ (I : Subgroup G) (χ : G →* ℤ_[l]ˣ) (c : G → ℤ_[l]) : Prop :=
  ContinuousOn c I ∧ ∀ s ∈ I, ∀ t ∈ I, c (s * t) = c s + (χ s : ℤ_[l]) * c t

def IsValZ (I : Subgroup G) (χ : G →* ℤ_[l]ˣ) (v : (G → ℤ_[l]) → ℤ_[l]) : Prop :=
  (∀ c c', CocZ I χ c → CocZ I χ c' → v (c + c') = v c + v c') ∧
  (∀ (a : ℤ_[l]) c, CocZ I χ c → v (a • c) = a * v c) ∧
  (∀ c c', CocZ I χ c → (∀ s ∈ I, c s = c' s) → v c = v c') ∧
  v (fun s => (χ s : ℤ_[l]) - 1) = 0 ∧
  ∀ c, CocZ I χ c → ∀ g : G, v (fun s => (χ g : ℤ_[l]) * c (g⁻¹ * s * g)) = v c

end Level

section Ints

variable (l : ℕ) [Fact l.Prime] (E : Type) [NontriviallyNormedField E] [NormedAlgebra ℚ_[l] E]

def zE : ℤ_[l] →+* E := (algebraMap ℚ_[l] E).comp PadicInt.Coe.ringHom

theorem zE_apply (x : ℤ_[l]) : zE l E x = algebraMap ℚ_[l] E (x : ℚ_[l]) := rfl

theorem norm_zE (x : ℤ_[l]) : ‖zE l E x‖ = ‖x‖ := by
  rw [zE_apply, norm_algebraMap']; rfl

theorem zE_injective : Function.Injective (zE l E) :=
  (algebraMap ℚ_[l] E).injective.comp Subtype.val_injective

theorem l_ne_zero : (l : E) ≠ 0 := by
  rw [← map_natCast (zE l E), map_ne_zero_iff _ (zE_injective l E)]
  exact_mod_cast (Fact.out : l.Prime).ne_zero

def Oi : Subring E where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    have : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by
    show ‖-a‖ ≤ 1
    rw [norm_neg]; exact ha

theorem mem_Oi {x : E} : x ∈ Oi l E ↔ ‖x‖ ≤ 1 := Iff.rfl

def zO : ℤ_[l] →+* Oi l E := (zE l E).codRestrict _ fun x => by
  rw [mem_Oi, norm_zE]; exact x.2

@[simp] theorem coe_zO (x : ℤ_[l]) : (zO l E x : E) = zE l E x := rfl

abbrev Qn (n : ℕ) : Type := Oi l E ⧸ Ideal.span {(l : Oi l E) ^ n}

def red (n : ℕ) : Oi l E →+* Qn l E n := Ideal.Quotient.mk _

def fac {m n : ℕ} (h : m ≤ n) : Qn l E n →+* Qn l E m :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h))

@[simp] theorem fac_red {m n : ℕ} (h : m ≤ n) (x : Oi l E) : fac l E h (red l E n x) = red l E m x := rfl

theorem red_surjective (n : ℕ) : Function.Surjective (red l E n) := Ideal.Quotient.mk_surjective

theorem red_eq_zero_iff_dvd (n : ℕ) (x : Oi l E) : red l E n x = 0 ↔ (l : Oi l E) ^ n ∣ x := by
  rw [red, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem dvd_iff_norm_le {a x : Oi l E} (ha : a ≠ 0) : a ∣ x ↔ ‖(x : E)‖ ≤ ‖(a : E)‖ := by
  have ha' : (a : E) ≠ 0 := fun h => ha (Subtype.ext h)
  constructor
  · rintro ⟨y, rfl⟩
    rw [Subring.coe_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) y.2
  · intro h
    refine ⟨⟨x / a, ?_⟩, Subtype.ext ?_⟩
    · rw [mem_Oi, norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
    · show (x : E) = a * (x / a)
      field_simp

theorem lO_ne_zero : (l : Oi l E) ≠ 0 := fun h => l_ne_zero l E (by simpa using congrArg Subtype.val h)

theorem red_eq_zero_iff (n : ℕ) (x : Oi l E) : red l E n x = 0 ↔ ‖(x : E)‖ ≤ ‖(l : E)‖ ^ n := by
  rw [red_eq_zero_iff_dvd, dvd_iff_norm_le l E (pow_ne_zero _ (lO_ne_zero l E))]
  simp

theorem red_eq_iff (n : ℕ) (x y : Oi l E) : red l E n x = red l E n y ↔ ‖(x : E) - y‖ ≤ ‖(l : E)‖ ^ n := by
  rw [← sub_eq_zero, ← map_sub, red_eq_zero_iff]; rfl

theorem isLocallyConstant_red' (n : ℕ) : IsLocallyConstant (red l E n) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hp : 0 < ‖(l : E)‖ ^ n := pow_pos (norm_pos_iff.2 (l_ne_zero l E)) n
  filter_upwards [Metric.closedBall_mem_nhds x hp] with y hy
  rw [red_eq_iff, ← dist_eq_norm]
  exact hy

def mulL (m n : ℕ) : Qn l E m →ₗ[Oi l E] Qn l E (m + n) :=
  Submodule.mapQ _ _ (LinearMap.mul _ _ ((l : Oi l E) ^ n)) fun x hx => by
    rw [Submodule.mem_comap, Ideal.mem_span_singleton, pow_add, mul_comm]
    exact mul_dvd_mul_left _ (Ideal.mem_span_singleton.1 hx)

@[simp] theorem mulL_red (m n : ℕ) (x : Oi l E) :
    mulL l E m n (red l E m x) = red l E (m + n) ((l : Oi l E) ^ n * x) := rfl

variable [FiniteDimensional ℚ_[l] E]

include l in
theorem properSpace : ProperSpace E := FiniteDimensional.proper ℚ_[l] E

instance compactSpace_Oi : CompactSpace (Oi l E) := by
  have := properSpace l E
  have h : IsCompact (Oi l E : Set E) := by
    convert isCompact_closedBall (0 : E) 1 using 1
    ext x
    simp [mem_Oi]
  exact isCompact_iff_compactSpace.1 h

instance finite_Qn (n : ℕ) : Finite (Qn l E n) := by
  have h := (isLocallyConstant_red' l E n).range_finite
  rw [(red_surjective l E n).range_eq] at h
  exact Set.finite_univ_iff.1 h

end Ints

section Kummer

abbrev DecA (A : ValuationSubring (AlgebraicClosure ℚ)) : Type := Lang.Dec (F := ℚ) A

def IneA (A : ValuationSubring (AlgebraicClosure ℚ)) : Subgroup (DecA A) :=
  (Lang.Ine (F := ℚ) A).subgroupOf (Lang.Dec (F := ℚ) A)

instance normal_IneA (A : ValuationSubring (AlgebraicClosure ℚ)) : (IneA A).Normal := Lang.normal_Ine_subgroupOf A

variable (l : ℕ) [Fact l.Prime]

def chi (A : ValuationSubring (AlgebraicClosure ℚ)) : DecA A →* ℤ_[l]ˣ :=
  (Lang.cycZ ℚ (AlgebraicClosure ℚ) l).comp (Lang.Dec (F := ℚ) A).subtype

def IsMuSys (ζ : ℕ → AlgebraicClosure ℚ) : Prop :=
  (∀ n, IsPrimitiveRoot (ζ n) (l ^ n)) ∧ ∀ n, ζ (n + 1) ^ l = ζ n

variable {A : ValuationSubring (AlgebraicClosure ℚ)}

def ActsAt (ζ : ℕ → AlgebraicClosure ℚ) (S : Set (DecA A)) (c : DecA A → ℤ_[l]) (n : ℕ) (β : AlgebraicClosure ℚ) :
    Prop :=
  ∀ s ∈ S, s.1 β = ζ n ^ (PadicInt.toZModPow n (c s)).val * β

def IsKummerCoc (ζ : ℕ → AlgebraicClosure ℚ) (a : AlgebraicClosure ℚ) (κ : DecA A → ℤ_[l]) : Prop :=
  ∃ x : ℕ → AlgebraicClosure ℚ, x 0 = a ∧ (∀ n, x (n + 1) ^ l = x n) ∧ ∀ n, ActsAt l ζ Set.univ κ n (x n)

def HasKumVal (ζ : ℕ → AlgebraicClosure ℚ) (c : DecA A → ℤ_[l]) (t : ℤ_[l]) : Prop :=
  ∀ (n : ℕ) (β : AlgebraicClosure ℚ) (m : ℤ), β ≠ 0 → ActsAt l ζ (IneA A) c n β →
    A.valuation (β ^ l ^ n) = A.valuation (l : AlgebraicClosure ℚ) ^ m → PadicInt.toZModPow n t = (m : ZMod (l ^ n))

end Kummer

end GlobalTheory.OrdLoc.Dcmp

import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.RealCyclotomicTwoPower
import Formalism.CyclotomicNorms.StatementT

noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace Formalism.L2.NT

open Formalism.L2.Host

def plOver (L : Fld) (p : ℕ) : Set (HeightOneSpectrum (𝓞 L)) :=
  {v | ((p : ℕ) : 𝓞 L) ∈ v.asIdeal}

def SplitsIn (L : Fld) (p : ℕ) : Prop :=
  (plOver L p).ncard = Module.finrank ℚ L

def IsRayPrime (K : Fld) (m p : ℕ) : Prop :=
  p.Prime ∧ ∃ π : Qb, π ∈ K ∧ IsIntegral ℤ π ∧ IsIntegral ℤ ((π - 1) / (m : Qb)) ∧
    ∃ σ : Qb →ₐ[ℚ] Qb, π * σ π = (p : Qb)

def RayAdm (K : Fld) (m : ℕ) (L : Fld) : Prop :=
  K ≤ L ∧ FiniteDimensional ℚ L ∧ ∀ p, IsRayPrime K m p → SplitsIn L p

def rayField (K : Fld) (m : ℕ) : Fld := ⨆ (L : Fld) (_ : RayAdm K m L), L

theorem le_rayField {K L : Fld} {m : ℕ} (h : RayAdm K m L) : L ≤ rayField K m :=
  le_iSup₂_of_le L h le_rfl

def RayCFT (K : Fld) (m : ℕ) : Prop := RayAdm K m (rayField K m)

theorem ncard_places_of_equiv {A B : Type} [Field A] [Field B] (e : A ≃+* B) (p : ℕ) :
    ({v : HeightOneSpectrum (𝓞 A) | ((p : ℕ) : 𝓞 A) ∈ v.asIdeal}).ncard =
      ({v : HeightOneSpectrum (𝓞 B) | ((p : ℕ) : 𝓞 B) ∈ v.asIdeal}).ncard := by
  set e' := NumberField.RingOfIntegers.mapRingEquiv e
  have nb : ∀ {R S : Type} [CommRing R] [CommRing S] (f : R ≃+* S) (I : Ideal R), I ≠ ⊥ → I.comap f.symm ≠ ⊥ := by
    intro R S _ _ f I hI h
    apply hI
    have := Ideal.map_comap_of_surjective f.symm f.symm.surjective I
    rw [h, Ideal.map_bot] at this
    exact this.symm
  refine Set.ncard_congr (fun v _ => (⟨v.asIdeal.comap e'.symm, Ideal.comap_isPrime _ _, nb e' _ v.ne_bot⟩ :
    HeightOneSpectrum (𝓞 B))) ?_ ?_ ?_
  · intro v hv
    simp only [Set.mem_ofPred_eq, Ideal.mem_comap, map_natCast] at hv ⊢
    exact hv
  · intro v w _ _ h
    have h' : v.asIdeal.comap e'.symm = w.asIdeal.comap e'.symm := congrArg HeightOneSpectrum.asIdeal h
    exact HeightOneSpectrum.ext (Ideal.comap_injective_of_surjective e'.symm e'.symm.surjective h')
  · intro w hw
    refine ⟨⟨w.asIdeal.comap e'.symm.symm, Ideal.comap_isPrime _ _, nb e'.symm _ w.ne_bot⟩, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, Ideal.mem_comap, map_natCast] at hw ⊢
      exact hw
    · apply HeightOneSpectrum.ext
      ext x
      simp only [Ideal.mem_comap, RingEquiv.symm_symm, RingEquiv.apply_symm_apply]

theorem finrank_eq_of_equiv {A B : Type} [Field A] [Field B] [CharZero A] [CharZero B] (e : A ≃+* B) :
    Module.finrank ℚ A = Module.finrank ℚ B :=
  LinearEquiv.finrank_eq e.toRatAlgEquiv.toLinearEquiv

def IsTeich {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p : ℕ} [Fact p.Prime]
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p) (t : Formalism.CyclotomicNorms.Fbar p →* Ω) : Prop :=
  ∀ x, ∃ h : t x ∈ A, κ (IsLocalRing.residue A ⟨t x, h⟩) = x

theorem IsTeich.injective {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {p : ℕ} [Fact p.Prime]
    {κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p} {t : Formalism.CyclotomicNorms.Fbar p →* Ω} (h : IsTeich A κ t) :
    Function.Injective t := by
  intro x y hxy
  obtain ⟨hx, ex⟩ := h x
  obtain ⟨hy, ey⟩ := h y
  rw [← ex, ← ey]
  congr 2
  exact Subtype.ext hxy

theorem IsTeich.map_zero {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {p : ℕ} [Fact p.Prime]
    {κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p} {t : Formalism.CyclotomicNorms.Fbar p →* Ω} (h : IsTeich A κ t) : t 0 = 0 := by
  have h0 : t 0 * t 0 = t 0 := by rw [← map_mul, mul_zero]
  by_contra hne
  have h1 : t 0 = 1 := mul_left_cancel₀ hne (by rw [h0, mul_one])
  obtain ⟨hx, ex⟩ := h 0
  have : (⟨t 0, hx⟩ : A) = 1 := Subtype.ext h1
  rw [this, map_one, map_one] at ex
  exact one_ne_zero ex

def redThrough {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {l : ℕ} [Fact l.Prime]
    (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l) (z : Ω) : Formalism.CyclotomicNorms.Fbar l :=
  open Classical in if h : z ∈ B then κ (IsLocalRing.residue B ⟨z, h⟩) else 0

section Red

variable {Ω : Type} [Field Ω]

theorem mem_of_pow_eq_one (B : ValuationSubring Ω) {z : Ω} {n : ℕ} (hn : 0 < n) (h : z ^ n = 1) : z ∈ B := by
  rcases B.mem_or_inv_mem z with hz | hz
  · exact hz
  · have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at h
      exact zero_ne_one h
    have e : z = z⁻¹ ^ (n - 1) := by
      have h1 : z ^ (n - 1) * z = 1 := by rw [← pow_succ, Nat.sub_add_cancel hn, h]
      rw [inv_pow]
      exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1)
    rw [e]
    exact pow_mem hz _

variable (B : ValuationSubring Ω) {l : ℕ} [Fact l.Prime] (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l)

theorem redThrough_mul {z w : Ω} (hz : z ∈ B) (hw : w ∈ B) :
    redThrough B κ (z * w) = redThrough B κ z * redThrough B κ w := by
  unfold redThrough
  rw [dif_pos (mul_mem hz hw), dif_pos hz, dif_pos hw, ← map_mul, ← map_mul]
  rfl

theorem redThrough_one : redThrough B κ 1 = 1 := by
  unfold redThrough
  rw [dif_pos (one_mem B)]
  have : (⟨1, one_mem B⟩ : B) = 1 := rfl
  rw [this, map_one, map_one]

theorem redThrough_pow {z : Ω} (hz : z ∈ B) (n : ℕ) : redThrough B κ (z ^ n) = redThrough B κ z ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, redThrough_one]
  | succ n ih => rw [pow_succ, redThrough_mul B κ (pow_mem hz n) hz, ih, pow_succ]

theorem pow_eq_one_of_charP {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (y : k) (a m : ℕ)
    (h : y ^ (l ^ a * m) = 1) : y ^ m = 1 := by
  have h2 : (y ^ m - 1) ^ (l ^ a) = 0 := by
    rw [sub_pow_char_pow, one_pow, ← pow_mul, mul_comm, h, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.mp h2)

theorem redThrough_primeToPart {M : Type} [Monoid M] (t : M →* Ω) (u : M) (hu : 0 < orderOf u) :
    redThrough B κ (t (Formalism.CyclotomicNorms.primeToPart l u)) = redThrough B κ (t u) := by
  have hB : t u ∈ B := mem_of_pow_eq_one B hu (by rw [← map_pow, pow_orderOf_eq_one, map_one])
  set y := redThrough B κ (t u) with hy
  set m := orderOf u
  set a := m.factorization l
  set m' := m / l ^ a
  have hm : l ^ a * m' = m := Nat.ordProj_mul_ordCompl_eq_self m l
  have hy1 : y ^ m = 1 := by
    rw [hy, ← redThrough_pow B κ hB, ← map_pow, pow_orderOf_eq_one, map_one, redThrough_one]
  haveI : CharP (Formalism.CyclotomicNorms.Fbar l) l := inferInstance
  have hy2 : y ^ m' = 1 := pow_eq_one_of_charP l y a m' (by rw [hm]; exact hy1)
  have hm'0 : m' ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hm
    exact hu.ne' hm.symm
  haveI : NeZero m' := ⟨hm'0⟩
  have hcop : Nat.Coprime (l ^ a) m' :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl (Fact.out : l.Prime) hu.ne')
  have hc : ((l ^ a * ((l ^ a : ℕ) : ZMod m')⁻¹.val : ℕ) : ZMod m') = ((1 : ℕ) : ZMod m') := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ hcop
  rw [ZMod.natCast_eq_natCast_iff'] at hc
  unfold Formalism.CyclotomicNorms.primeToPart
  rw [map_pow, redThrough_pow B κ hB, ← hy, pow_eq_pow_mod _ hy2, hc, ← pow_eq_pow_mod _ hy2, pow_one]

end Red

def degSer {G : Type} [Group G] {g : ℕ} (f₀ : (ZMod g)[X]) (f : (ZMod g)[X]) : MonoidAlgebra ℂ G :=
  open Classical in if f = f₀ then 1 else 0

section Series

def ipG {G : Type} [Fintype G] (χ ψ : G → ℂ) : ℂ := ∑ x, χ x * star (ψ x)

def IsChar {G : Type} [Group G] (χ : G → ℂ) : Prop :=
  ∃ (n : ℕ) (ρ : G →* GL (Fin n) ℂ), ∀ x, χ x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ)

def IsIrrChar {G : Type} [Group G] [Fintype G] (χ : G → ℂ) : Prop :=
  IsChar χ ∧ ipG χ χ = (Fintype.card G : ℂ)

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def unipBlock (d a : ℕ) : Set (GL (Fin d) F) :=
  {u | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}

def IsCuspChar {d : ℕ} (χ : GL (Fin d) F → ℂ) : Prop :=
  IsIrrChar χ ∧ ∀ a, 0 < a → a < d →
    ∑ u : GL (Fin d) F, (open Classical in if u ∈ (unipBlock d a : Set (GL (Fin d) F)) then χ u else 0) = 0

def offs {m : ℕ} (c : Fin m → ℕ) (i : Fin m) : ℕ := ∑ j : Fin m, if j < i then c j else 0

def IsBaseBlockVar {m : ℕ} (c : Fin m → ℕ) (i : Fin m) (x : ℕ) : Prop := offs c i ≤ x ∧ x < offs c i + c i

def IsParab {m r : ℕ} (c : Fin m → ℕ) (p : GL (Fin r) F) : Prop :=
  ∀ (x y : Fin r) (i j : Fin m), IsBaseBlockVar c i x.val → IsBaseBlockVar c j y.val → j < i →
    (p : Matrix (Fin r) (Fin r) F) x y = 0

def blkOf {m r : ℕ} (c : Fin m → ℕ) (i : Fin m) (M : Matrix (Fin r) (Fin r) F) :
    Matrix (Fin (c i)) (Fin (c i)) F :=
  fun a b => if h : offs c i + a.val < r ∧ offs c i + b.val < r then M ⟨_, h.1⟩ ⟨_, h.2⟩ else 0

def onMat {n : ℕ} (χ : GL (Fin n) F → ℂ) (M : Matrix (Fin n) (Fin n) F) : ℂ :=
  open Classical in if h : IsUnit M then χ h.unit else 0

def eOf {G : Type} [Group G] [Fintype G] (χ : G → ℂ) : MonoidAlgebra ℂ G :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun x => χ 1 / (Fintype.card G : ℂ) * χ x⁻¹)

variable {g : ℕ} [Fact g.Prime]

def GreenAt (teich : Formalism.CyclotomicNorms.Fbar g →* ℂ) {d : ℕ} (χ : GL (Fin d) (ZMod g) → ℂ) (k : ℕ) : Prop :=
  ∀ x : GL (Fin d) (ZMod g), Irreducible (Matrix.charpoly (x : Matrix (Fin d) (Fin d) (ZMod g))) →
    χ x = (-1) ^ (d - 1) *
      ((Formalism.CyclotomicNorms.rootsBar (Matrix.charpoly (x : Matrix (Fin d) (Fin d) (ZMod g)))).map fun α => teich α ^ k).sum

def IsGenSys (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) : Prop :=
  ∀ d, 0 < d → orderOf (ζ d) = g ^ d - 1 ∧
    ∀ d', d ∣ d' → 0 < d' → ζ d' ^ ((g ^ d' - 1) / (g ^ d - 1)) = ζ d

def labCusp (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (d k : ℕ) : (ZMod g)[X] := minpoly (ZMod g) (ζ d ^ k)

def InSeries (teich : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) {r : ℕ} (χ : GL (Fin r) (ZMod g) → ℂ)
    (f : (ZMod g)[X]) : Prop :=
  ∃ (m : ℕ) (c : Fin m → ℕ) (χs : ∀ i, GL (Fin (c i)) (ZMod g) → ℂ) (ks : Fin m → ℕ),
    (∀ i, 0 < c i) ∧ ∑ i, c i = r ∧
    (∀ i, IsCuspChar (χs i) ∧ GreenAt teich (χs i) (ks i) ∧ (labCusp ζ (c i) (ks i)).natDegree = c i) ∧
    ∏ i, labCusp ζ (c i) (ks i) = f ∧
    ∑ p : GL (Fin r) (ZMod g),
      (open Classical in if IsParab c p then χ p * star (∏ i, onMat (χs i) (blkOf (r := r) c i (p : Matrix (Fin r) (Fin r) (ZMod g)))) else 0) ≠ 0

def CuspGreenUnique (teich : Formalism.CyclotomicNorms.Fbar g →* ℂ) : Prop :=
  ∀ (d k : ℕ) (χ χ' : GL (Fin d) (ZMod g) → ℂ), IsCuspChar χ → IsCuspChar χ' →
    GreenAt teich χ k → GreenAt teich χ' k → χ = χ'

def eSerC (teich : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (r : ℕ) (f : (ZMod g)[X]) :
    MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) :=
  ∑ᶠ (χ : GL (Fin r) (ZMod g) → ℂ) (_ : IsIrrChar χ ∧ InSeries teich ζ χ f), eOf χ

end Series

section SeriesLemmas

variable {g : ℕ} [Fact g.Prime]

theorem InSeries.label {teich : Formalism.CyclotomicNorms.Fbar g →* ℂ} {ζ : ℕ → Formalism.CyclotomicNorms.Fbar g} {r : ℕ}
    {χ : GL (Fin r) (ZMod g) → ℂ} {f : (ZMod g)[X]} (hζ : IsGenSys ζ) (h : InSeries teich ζ χ f) :
    f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0 := by
  obtain ⟨m, c, χs, ks, hpos, hsum, hcusp, hprod, -⟩ := h
  subst hprod
  have hint : ∀ i, IsIntegral (ZMod g) (ζ (c i) ^ ks i) := fun i => Algebra.IsIntegral.isIntegral _
  have hmon : ∀ i ∈ (Finset.univ : Finset (Fin m)), (labCusp ζ (c i) (ks i)).Monic :=
    fun i _ => minpoly.monic (hint i)
  refine ⟨Polynomial.monic_prod_of_monic _ _ hmon, ?_, ?_⟩
  · rw [Polynomial.natDegree_prod_of_monic _ _ hmon, ← hsum]
    exact Finset.sum_congr rfl fun i _ => (hcusp i).2.2
  · rw [Polynomial.coeff_zero_prod, Finset.prod_ne_zero_iff]
    intro i _
    apply minpoly.coeff_zero_ne_zero (hint i)
    apply pow_ne_zero
    intro h0
    have ho := (hζ (c i) (hpos i)).1
    rw [h0] at ho
    have hg : 2 ≤ g := (Fact.out : g.Prime).two_le
    have h1 : 1 ≤ g ^ c i - 1 := by
      have : 2 ≤ g ^ c i := le_trans hg (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp (hpos i)) g)
      omega
    have hz : orderOf (0 : Formalism.CyclotomicNorms.Fbar g) = 0 := by
      rw [orderOf_eq_zero_iff']
      intro n hn
      rw [zero_pow (Nat.pos_iff_ne_zero.mp hn)]
      exact zero_ne_one
    omega

end SeriesLemmas

section SeriesTriv

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem offs_add_le {m : ℕ} (c : Fin m → ℕ) {i j : Fin m} (h : j < i) : offs c j + c j ≤ offs c i := by
  unfold offs
  have e : c j = ∑ k : Fin m, if k = j then c k else 0 := by rw [Finset.sum_ite_eq']; simp
  rw [e, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  by_cases h1 : k < j
  · have h2 : k < i := lt_trans h1 h
    have h3 : k ≠ j := ne_of_lt h1
    simp [h1, h2, h3]
  · by_cases h3 : k = j
    · subst h3
      simp [h]
    · simp [h1, h3]

theorem offs_add_le_sum {m : ℕ} (c : Fin m → ℕ) (i : Fin m) : offs c i + c i ≤ ∑ k, c k := by
  unfold offs
  have e : c i = ∑ k : Fin m, if k = i then c k else 0 := by rw [Finset.sum_ite_eq']; simp
  rw [e, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  by_cases h1 : k < i
  · simp [h1, ne_of_lt h1]
  · by_cases h3 : k = i
    · subst h3; simp
    · simp [h1, h3]

variable {g : ℕ} [Fact g.Prime]

end SeriesTriv

section TameChar

def TameCoupled {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) {p : ℕ} [Fact p.Prime]
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p) (σ : Ω ≃ₐ[E] Ω) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar p) : Prop :=
  ∀ d, 0 < d → ∀ y : Ω, y ^ (p ^ d - 1) = (p : Ω) → redThrough A κ (σ y / y) = ζ d

theorem tameQuot_pow {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (σ : Ω ≃ₐ[E] Ω) {y : Ω} {m p : ℕ}
    (hp : (p : Ω) ≠ 0) (hy : y ^ m = (p : Ω)) : (σ y / y) ^ m = 1 := by
  have hy0 : y ^ m ≠ 0 := hy ▸ hp
  rw [div_pow, ← map_pow, hy, map_natCast, div_self hp]

theorem tameQuot_mem {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω) {y : Ω}
    {m p : ℕ} (hm : 0 < m) (hp : (p : Ω) ≠ 0) (hy : y ^ m = (p : Ω)) : σ y / y ∈ A :=
  mem_of_pow_eq_one A hm (tameQuot_pow σ hp hy)

end TameChar

section SeriesAut

variable {g : ℕ} [Fact g.Prime]

def toZModAlgEquiv (φ : Formalism.CyclotomicNorms.Fbar g ≃+* Formalism.CyclotomicNorms.Fbar g) : Formalism.CyclotomicNorms.Fbar g ≃ₐ[ZMod g] Formalism.CyclotomicNorms.Fbar g :=
  { φ with
    commutes' := fun r => by
      have h := RingHom.ext_zmod ((φ : Formalism.CyclotomicNorms.Fbar g →+* Formalism.CyclotomicNorms.Fbar g).comp (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)))
        (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))
      exact congrArg (fun f : ZMod g →+* Formalism.CyclotomicNorms.Fbar g => f r) h }

end SeriesAut

end Formalism.L2.NT

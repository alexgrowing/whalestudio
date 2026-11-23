import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StepBoxIffStepSuppDeg

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (JetsRatDeg)

section Deg

variable {T : Type} {a b : ℕ}

open Classical in

def monoDeg (e : DVar T a b →₀ ℕ) (τ : T) : ℕ := ∑ k ∈ e.support.filter (fun k => k.1 = τ), e k

theorem monoDeg_eq_sum [Fintype T] (e : DVar T a b →₀ ℕ) (τ : T) : monoDeg e τ = ∑ β, ∑ α, e (τ, β, α) := by
  unfold monoDeg
  rw [Finset.sum_filter, Finset.sum_subset (Finset.subset_univ e.support) (fun k _ hk => by
    simp only [Finsupp.mem_support_iff, not_not] at hk
    simp [hk])]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · simp [Fintype.sum_prod_type]
  · intro t _ ht
    simp [ht]
  · intro h
    exact absurd (Finset.mem_univ τ) h

theorem exists_monoDeg [Fintype T] (ha : 0 < a) (hb : 0 < b) (n : T → ℕ) : ∃ e : DVar T a b →₀ ℕ, ∀ τ, monoDeg e τ = n τ := by
  classical
  refine ⟨∑ t, Finsupp.single (t, (⟨0, hb⟩ : Fin b), (⟨0, ha⟩ : Fin a)) (n t), fun τ => ?_⟩
  rw [monoDeg_eq_sum, Finset.sum_eq_single (⟨0, hb⟩ : Fin b)]
  · rw [Finset.sum_eq_single (⟨0, ha⟩ : Fin a)]
    · simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
    · intro α _ hα
      simp [Finsupp.finsetSum_apply, Ne.symm hα]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro β _ hβ
    refine Finset.sum_eq_zero fun α _ => ?_
    simp [Finsupp.finsetSum_apply, Ne.symm hβ]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Deg

namespace ColIn

variable {B : Base} {X : PreX B.toPre} (I : ColIn B X)

abbrev Sb (a : I.ι) (u : B.Word) : Finset (HeightOneSpectrum (𝓞 B.fields.E)) :=
  Sall (Pr := B.primes X) I.sel (I.tup a) u

abbrev modulus (a : I.ι) (u : B.Word) : ℕ :=
  cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) * cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u

end ColIn

abbrev nuDeg (B : Base) (u : B.Word) (i : ℕ) (τ : B.fields.Tau) : ℤ := ∑ r, (B.wts.nuW u (i + 1) τ).w r

theorem nuDeg_nonneg (B : Base) (u : B.Word) {i : ℕ} (hi : i < B.R.m) (τ : B.fields.Tau) : 0 ≤ nuDeg B u i τ := by
  have h0 := GlobalTheory.MoveCompare.nuW_detShift_nonneg B.wts u hi τ
  unfold nuDeg
  refine Finset.sum_nonneg fun r _ => le_trans h0 ?_
  unfold DomWeight.detShift
  split_ifs with h
  · apply DomWeight.anti
    rw [Fin.le_iff_val_le_val]
    have := r.isLt
    simp only
    omega
  · exact absurd (lt_of_le_of_lt (Nat.zero_le _) r.isLt) h

theorem exists_monoDeg_nuDeg (B : Base) (u : B.Word) {i : ℕ} (hi : i < B.R.m) :
    ∃ e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ, ∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ := by
  have hk := B.R.m_add_three_le_k
  have h1 : 0 < B.R.N i := by
    show 0 < B.R.k + i * (B.R.t + 1)
    omega
  have h2 : 0 < B.R.N (i + 1) := by
    show 0 < B.R.k + (i + 1) * (B.R.t + 1)
    omega
  obtain ⟨e, he⟩ := exists_monoDeg (T := B.fields.Tau) h1 h2 (fun τ => (nuDeg B u i τ).toNat)
  exact ⟨e, fun τ => by rw [he τ]; exact Int.toNat_of_nonneg (nuDeg_nonneg B u hi τ)⟩

private theorem monoDeg_eq_sum_filter {T : Type} {a b : ℕ} {d : DecidableEq T} (e : DVar T a b →₀ ℕ) (τ : T) :
    monoDeg e τ = ∑ k ∈ e.support.filter (fun k => k.1 = τ), e k := by
  unfold monoDeg
  congr

namespace ColIn

variable {B : Base} {X : PreX B.toPre} (I : ColIn B X)

def jetNum (a : I.ι) (u : B.Word) (i : ℕ) (N : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i)))
    (N' : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N (i + 1)))) (c : ℕ) (x : HomE B.fields.E (B.R.N i) (B.R.N (i + 1)))
    (e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ) : ℂ :=
  (I.A.chiF _ _ N N')⁻¹ * jetC I.A.cD (I.A.thInd (I.Sb a u) N N' c x) e

abbrev JetRange (a : I.ι) (u : B.Word) (i : ℕ) (N : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i)))
    (N' : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N (i + 1)))) (c : ℕ) (x : HomE B.fields.E (B.R.N i) (B.R.N (i + 1))) : Prop :=
  letI := B.fields.starE
  InRange (I.Sb a u) (I.modulus a u) c N N' x

def JetsIn : Prop :=
  ∀ (a : I.ι) (u : B.Word) (i : ℕ), i < B.R.m →
    JetsRatDeg I.A (B.R.N i) (B.R.N (i + 1)) (Sall (Pr := B.primes X) I.sel (I.tup a) u)
      (cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) * cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u)
      (fun τ => ∑ r, (B.wts.nuW u (i + 1) τ).w r)

theorem jetsIn_iff : I.JetsIn ↔ ∀ (a : I.ι) (u : B.Word) (i : ℕ), i < B.R.m → ∀ N N' c x,
    I.JetRange a u i N N' c x → ∀ e, (∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) →
      I.jetNum a u i N N' c x e ∈ B.embLL.fieldRange := by
  constructor
  · intro h a u i hi N N' c x hx e he
    obtain ⟨y, hy⟩ := h a u i hi N N' c x hx e (fun τ => by rw [← monoDeg_eq_sum_filter]; exact he τ)
    refine RingHom.mem_fieldRange.mpr ⟨y, ?_⟩
    rw [← I.A_σ₀]
    exact hy
  · intro h a u i hi N N' c x hx e he
    obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.mp
      (h a u i hi N N' c x hx e (fun τ => by rw [monoDeg_eq_sum_filter]; exact he τ))
    refine ⟨y, ?_⟩
    rw [I.A_σ₀]
    exact hy

theorem jetRange_std (a : I.ι) (u : B.Word) (i : ℕ) :
    I.JetRange a u i (stdLat B.fields.E (B.R.N i)) (stdLat B.fields.E (B.R.N (i + 1))) 1 0 := by
  letI := B.fields.starE
  show IsSdLat _ ∧ IsSdLat _ ∧ 0 < 1 ∧ 1 ∣ _ ∧ _
  exact ⟨And.intro Formalism.L2.Col.stdLat_lattice Formalism.L2.Col.stdLat_unimodular,
    And.intro Formalism.L2.Col.stdLat_lattice Formalism.L2.Col.stdLat_unimodular, Nat.one_pos, one_dvd _, zero_mem _⟩

variable {I} {a : I.ι} {u : B.Word} {i : ℕ} {N : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i))}
  {N' : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N (i + 1)))} {c : ℕ} {x : HomE B.fields.E (B.R.N i) (B.R.N (i + 1))}
  {e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ}

theorem JetsIn.exists_eq (h : I.JetsIn) (hi : i < B.R.m) (hx : I.JetRange a u i N N' c x)
    (he : ∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) : ∃ y : B.LL, B.embLL y = I.jetNum a u i N N' c x e := by
  exact RingHom.mem_fieldRange.mp ((jetsIn_iff I).mp h a u i hi N N' c x hx e he)

theorem JetsIn.isAlgebraic (h : I.JetsIn) (hi : i < B.R.m) (hx : I.JetRange a u i N N' c x)
    (he : ∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) : IsAlgebraic ℚ (I.jetNum a u i N N' c x e) := by
  obtain ⟨y, hy⟩ := h.exists_eq hi hx he
  rw [← hy]
  exact IsAlgebraic.algHom B.embLL.toRatAlgHom (Algebra.IsAlgebraic.isAlgebraic y)

end ColIn

example {B : Base} {X : PreX B.toPre} (I : ColIn B X) (h : I.JetsIn) (u : B.Word) (i : ℕ) (hi : i < B.R.m) :
    ∃ e, (∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) ∧
      I.jetNum I.mu0 u i (stdLat _ _) (stdLat _ _) 1 0 e ∈ B.embLL.fieldRange := by
  obtain ⟨e, he⟩ := exists_monoDeg_nuDeg B u hi
  exact ⟨e, he, h.exists_eq hi (I.jetRange_std _ u i) he⟩

example {B : Base} {X : PreX B.toPre} (I : ColIn B X) (u : B.Word) (i : ℕ) (hi : i < B.R.m) (e)
    (he : ∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ)
    (ht : Transcendental ℚ (I.jetNum I.mu0 u i (stdLat _ _) (stdLat _ _) 1 0 e)) : ¬ I.JetsIn :=
  fun h => ht (h.isAlgebraic hi (I.jetRange_std _ u i) he)

example : monoDeg (Finsupp.single ((true, 0, 1) : DVar Bool 2 1) 3) true = 3 ∧
    monoDeg (Finsupp.single ((true, 0, 1) : DVar Bool 2 1) 3) false = 0 := by
  simp [monoDeg_eq_sum, Finsupp.single_apply, Prod.ext_iff]

example {T : Type} [Fintype T] {a b : ℕ} (cD : T → ℂ) (G : VCx T a b → ℂ) : jetC cD G 0 = G 0 := by
  have h : ∀ (n : ℕ) (_ : n = 0) (v : Fin n → VCx T a b), iteratedFDeriv ℂ n G 0 v = G 0 := by
    rintro _ rfl v
    simp
  simp only [jetC, derivAt0, Finsupp.prod_zero_index, one_mul]
  exact h _ (by simp) _

end GlobalTheory.Mem.Col2

end

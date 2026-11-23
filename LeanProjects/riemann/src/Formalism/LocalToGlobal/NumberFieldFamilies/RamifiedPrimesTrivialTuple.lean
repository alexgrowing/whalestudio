import Formalism.LocalToGlobal.UnitaryNorms.CharDiv
import Formalism.LocalToGlobal.UnitaryNorms.UnrAEPf

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Fam.DivCQ

open Formalism.BasicNotions Formalism.L2.Host

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

def QpSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) : Set ℕ :=
  {p | p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w}

def QPlSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  {v | Tp.InQ' μ v}

def XiRamFin (Tp : TupTied D C nch) : Prop :=
  ∀ μ, (QpSet Tp μ).Finite ∧ (QPlSet Tp μ).Finite

def XiUnrG (Tp : TupTied D C nch) : Prop :=
  ∀ μ i w, OverP D.host (D.host.g i) w → (Tp.xi μ).UnrAt w

def QDegOne (Tp : TupTied D C nch) : Prop :=
  ∀ μ v, Tp.InQ' μ v → (Ideal.absNorm v.asIdeal).Prime

def QpOf (Tp : TupTied D C nch) (hf : XiRamFin Tp) (μ : D.what₂.Tup) : Finset ℕ := (hf μ).1.toFinset

def QPlOf (Tp : TupTied D C nch) (μ : D.what₂.Tup) : Type := {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}

@[instance_reducible] def finQOf (Tp : TupTied D C nch) (hf : XiRamFin Tp) (μ : D.what₂.Tup) : Fintype (QPlOf Tp μ) := (hf μ).2.fintype

def qvOf (Tp : TupTied D C nch) (μ : D.what₂.Tup) (v : QPlOf Tp μ) : ℕ := Ideal.absNorm v.1.asIdeal

theorem mem_QpOf (Tp : TupTied D C nch) (hf : XiRamFin Tp) (μ : D.what₂.Tup) (p : ℕ) :
    p ∈ QpOf Tp hf μ ↔ p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w :=
  Set.Finite.mem_toFinset _

theorem unrAt_one {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).UnrAt w :=
  fun _ _ => rfl

theorem unrAt_mul {L : Type} [Field L] [NumberField L] {χ ψ : HChar L} {w : HeightOneSpectrum (𝓞 L)}
    (hχ : χ.UnrAt w) (hψ : ψ.UnrAt w) : (χ * ψ).UnrAt w := fun x hx => by
  show χ.loc w x * ψ.loc w x = 1
  rw [hχ x hx, hψ x hx, one_mul]

theorem overP_unique {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h1 : OverP D.host p w) (h2 : OverP D.host q w) : p = q := by
  by_contra hne
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  have h1' : (1 : 𝓞 D.host.E) ∈ w.asIdeal := by
    have e : ((a : ℤ) : 𝓞 D.host.E) * ((p : ℕ) : 𝓞 D.host.E) + ((b : ℤ) : 𝓞 D.host.E) * ((q : ℕ) : 𝓞 D.host.E) = 1 := by
      have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
      push_cast at this
      exact this
    rw [← e]
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h1) (w.asIdeal.mul_mem_left _ h2)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1')

theorem delAt_unr (l : ℕ) (hl : l.Prime) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : OverP D.host l w) :
    (C.delAt l).UnrAt w := by
  unfold CharFrame.delAt
  split_ifs with h
  · refine C.isDel'.unr w fun h' => D.host.pde_ne ?_
    rw [← h]
    exact overP_unique hl D.host.pde'_prime hw h'
  · refine C.isDel.unr w fun h' => h ?_
    exact overP_unique hl D.host.pde_prime hw h'

theorem ramified_primes_trivial_tuple (Tp : TupTied D C nch) (hf : XiRamFin Tp) : QpOf Tp hf D.what₂.mu0 = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 fun p hp => ?_
  obtain ⟨-, w, -, hw⟩ := (mem_QpOf Tp hf _ p).1 hp
  rw [Tp.trueColumnChoices_heckeChar_reference_eq_one] at hw
  exact hw (unrAt_one w)

theorem QpOf_muAt (Tp : TupTied D C nch) (hf : XiRamFin Tp) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w ∉ QpOf Tp hf (D.what₂.muAt w) := by
  intro hm
  obtain ⟨-, v, hv, hnu⟩ := (mem_QpOf Tp hf _ _).1 hm
  by_cases h0 : D.what₂.muAt w = D.what₂.mu0
  · rw [h0, Tp.trueColumnChoices_heckeChar_reference_eq_one] at hnu
    exact hnu (unrAt_one v)
  · have ht : D.what₂.muAt w = D.what₂.muTw w := (D.what₂.muAt_or w).resolve_left h0
    rw [ht, Tp.xi_tw] at hnu
    exact hnu (unrAt_mul (delAt_unr _ (D.what₂.places.resChar_prime w) v hv)
      (fun x _ => (Tp.psi_is w h0).atl v hv x))

theorem QpOf_g (Tp : TupTied D C nch) (hf : XiRamFin Tp) (hg : XiUnrG Tp) (μ : D.what₂.Tup) (i) :
    D.host.g i ∉ QpOf Tp hf μ := by
  intro hm
  obtain ⟨-, w, hw, hnu⟩ := (mem_QpOf Tp hf _ _).1 hm
  exact hnu (hg μ i w hw)

theorem absNorm_mem_above (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ aboveF (L := D.host.E) D.host.F v) : OverP D.host (Ideal.absNorm v.asIdeal) w := by
  have hw' : w ∈ {P : HeightOneSpectrum (𝓞 D.host.E) | P.under (𝓞 D.host.F) = v} :=
    (Set.Finite.mem_toFinset (finite_aboveF _ v)).1 hw
  replace hw' : w.under (𝓞 D.host.F) = v := hw'
  have h0 : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
    rw [hw']; exact Ideal.absNorm_mem _
  have h1 := Ideal.mem_comap.1 h0
  rw [map_natCast] at h1
  exact h1

theorem qvOf_char (Tp : TupTied D C nch) (hf : XiRamFin Tp) (hd : QDegOne Tp) (μ : D.what₂.Tup) (v : QPlOf Tp μ) :
    ∃ p ∈ QpOf Tp hf μ, p.Prime ∧ qvOf Tp μ v = p := by
  refine ⟨qvOf Tp μ v, ?_, hd μ v.1 v.2, rfl⟩
  obtain ⟨w, hw, hnu⟩ := v.2
  exact (mem_QpOf Tp hf _ _).2 ⟨hd μ v.1 v.2, w, absNorm_mem_above v.1 w hw, hnu⟩

theorem mem_QpOf_iff (Tp : TupTied D C nch) (hf : XiRamFin Tp) (μ p) :
    p ∈ QpOf Tp hf μ ↔ p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w := mem_QpOf Tp hf μ p

def mult (P : HeightOneSpectrum (𝓞 D.host.E)) (I : Ideal (𝓞 D.host.E)) : ℕ :=
  Multiset.count P.asIdeal (UniqueFactorizationMonoid.normalizedFactors I)

def vddOf (pr : ℕ → D.what₂.Tau → HeightOneSpectrum (𝓞 D.host.E)) (p : ℕ) (τ : D.what₂.Tau) : ℝ :=
  if p.Prime then
    (mult (pr p τ) (differentIdeal ℤ (𝓞 D.host.E)) : ℝ) / (mult (pr p τ) (Ideal.span {((p : ℕ) : 𝓞 D.host.E)}) : ℝ)
  else 0

theorem vddOf_nonneg (pr : ℕ → D.what₂.Tau → HeightOneSpectrum (𝓞 D.host.E)) (p τ) : 0 ≤ vddOf pr p τ := by
  unfold vddOf
  split_ifs
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact le_rfl

theorem dvd_of_mult_ne {P : HeightOneSpectrum (𝓞 D.host.E)} {I : Ideal (𝓞 D.host.E)} (h : mult P I ≠ 0) : P.asIdeal ∣ I :=
  UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.count_ne_zero.1 h)

theorem prime_dvd_absNorm {p : ℕ} (hp : p.Prime) {P : HeightOneSpectrum (𝓞 D.host.E)} (h : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    p ∣ Ideal.absNorm P.asIdeal := by
  by_contra hn
  have hc : IsCoprime (p : ℤ) (Ideal.absNorm P.asIdeal : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (1 : 𝓞 D.host.E) ∈ P.asIdeal := by
    have e : ((a : ℤ) : 𝓞 D.host.E) * ((p : ℕ) : 𝓞 D.host.E) +
        ((b : ℤ) : 𝓞 D.host.E) * ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) = 1 := by
      have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
      push_cast at this
      exact this
    rw [← e]
    exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h) (P.asIdeal.mul_mem_left _ (Ideal.absNorm_mem _))
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem vddOf_unram (pr : ℕ → D.what₂.Tau → HeightOneSpectrum (𝓞 D.host.E)) (p τ) (hu : DV.UnramE D p) : vddOf pr p τ = 0 := by
  unfold vddOf
  split_ifs with hp
  · by_cases h2 : mult (pr p τ) (Ideal.span {((p : ℕ) : 𝓞 D.host.E)}) = 0
    · rw [h2, Nat.cast_zero, div_zero]
    · by_cases h1 : mult (pr p τ) (differentIdeal ℤ (𝓞 D.host.E)) = 0
      · rw [h1, Nat.cast_zero, zero_div]
      · exfalso
        apply hu
        have hin : ((p : ℕ) : 𝓞 D.host.E) ∈ (pr p τ).asIdeal := Ideal.dvd_span_singleton.1 (dvd_of_mult_ne h2)
        have hd : Ideal.absNorm (pr p τ).asIdeal ∣ Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.E)) :=
          Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd (dvd_of_mult_ne h1))
        rw [NumberField.absNorm_differentIdeal D.host.E (𝓞 D.host.E)] at hd
        exact (prime_dvd_absNorm hp hin).trans hd
  · rfl

def XiRamFinE (Tp : TupTied D C nch) : Prop :=
  ∀ μ, {w : HeightOneSpectrum (𝓞 D.host.E) | ¬ (Tp.xi μ).UnrAt w}.Finite

theorem xiRamFin_of (Tp : TupTied D C nch) (h : XiRamFinE Tp) : XiRamFin Tp := fun μ => by
  constructor
  · refine ((h μ).biUnion fun w _ => (Finset.finite_toSet (Ideal.absNorm w.asIdeal).divisors)).subset ?_
    rintro p ⟨hp, w, hw, hnu⟩
    refine Set.mem_iUnion₂.2 ⟨w, hnu, ?_⟩
    have hn : Ideal.absNorm w.asIdeal ≠ 0 := fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact Finset.mem_coe.2 (Nat.mem_divisors.2 ⟨prime_dvd_absNorm hp hw, hn⟩)
  · refine ((h μ).image fun w => w.under (𝓞 D.host.F)).subset ?_
    rintro v ⟨w, hw, hnu⟩
    have hw' : w ∈ {P : HeightOneSpectrum (𝓞 D.host.E) | P.under (𝓞 D.host.F) = v} :=
      (Set.Finite.mem_toFinset (finite_aboveF _ v)).1 hw
    exact ⟨w, hnu, hw'⟩

theorem xiRamFinE (Tp : TupTied D C nch) : XiRamFinE Tp := fun μ =>
  Filter.eventually_cofinite.1 (HChar.unr_ae (unrAE D.host.E) (Tp.xi μ))

theorem xiRamFin (Tp : TupTied D C nch) : XiRamFin Tp := xiRamFin_of Tp (xiRamFinE Tp)

structure ConjAt (D : D7) where
  M : ℕ → Type
  [instM : ∀ j, NormedAddCommGroup (M j)]
  [instMi : ∀ j, InnerProductSpace ℂ (M j)]
  [instMf : ∀ j, FiniteDimensional ℂ (M j)]
  T : ℕ → Type
  [instT : ∀ j, NormedAddCommGroup (T j)]
  [instTi : ∀ j, InnerProductSpace ℂ (T j)]
  [instTf : ∀ j, FiniteDimensional ℂ (T j)]
  th : ∀ j, T j →ₗ[ℂ] M j
  part : ∀ j, D.what₂.FT → Submodule ℂ (M j)

attribute [instance] ConjAt.instM ConjAt.instMi ConjAt.instMf ConjAt.instT ConjAt.instTi ConjAt.instTf

def lamAt (A : ConjAt D) (j : ℕ) (π : D.what₂.FT) : ℝ :=
  (LinearMap.trace ℂ (A.M j) (A.th j ∘ₗ LinearMap.adjoint (A.th j) ∘ₗ
    ((A.part j π).starProjection : A.M j →ₗ[ℂ] A.M j))).re / (Module.finrank ℂ (A.part j π) : ℝ)

open Classical in

def logLamOf (A : (D.what₂.LL →+* ℂ) → ConjAt D) (j : ℕ) (π : D.what₂.FT) (e : D.what₂.LL →+* ℂ) : ℝ :=
  if e = D.what₂.embLL then Real.log (D.what₂.lamP D.what₂.mu0 j π) else Real.log (lamAt (A e) j π)

theorem logLamOf_base (A : (D.what₂.LL →+* ℂ) → ConjAt D) (j π) :
    logLamOf A j π D.what₂.embLL = Real.log (D.what₂.lamP D.what₂.mu0 j π) := if_pos rfl

end Formalism.L2.Fam.DivCQ

end

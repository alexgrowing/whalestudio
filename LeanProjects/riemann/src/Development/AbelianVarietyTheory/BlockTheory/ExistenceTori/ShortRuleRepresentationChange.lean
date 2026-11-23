import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ReflexNormIndexIdeal
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.NormFactorThetaValue
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.DeltaDatumCombinedCoefficient

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab)

def CoverVal {S : Type} [CommRing S] [Algebra Δ.cov.c₂.F S] (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S) {n : ℕ} (Λ : Lat E n)
    (N : ℕ) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (v : S) : Prop :=
  ThVal Δ.cov.Xo₂ Δ.cov.c₂ Δ.nab₂ y₂ Λ N (Δ.cov.incl β) (Δ.combinedCoeff x₀) a (MvPolynomial.map Δ.cov.incl P) v

def IsShortRule {n : ℕ} (Λ : Lat E n) (N : ℕ) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R),
    (∃ (S' : Type) (_ : CommRing S') (_ : Algebra Δ.cov.c₂.F S') (φ : p.R →+* S')
      (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S'), φ.FaithfullyFlat ∧ Δ.cov.LiesOver φ y₂ y) ∧
    ∀ (S' : Type) [CommRing S'] [Algebra Δ.cov.c₂.F S'] (φ : p.R →+* S') (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S'),
      Δ.cov.LiesOver φ y₂ y → ∃ v, CoverVal Δ y₂ Λ N β x₀ a P v ∧ φ (f p y) = v * Δ.fnVal y₂

def ramPart (E : Type) [Field E] [NumberField E] : ℕ := 2 * (discr E).natAbs

def reps (n : ℕ) (s : ℕ+) : Set (Lat E n) :=
  {Λ | Λ.InGenus ∧ Λ.StdAt (ramPart E * Δ.a.l₂.M * s)}

def IsPairIso {n : ℕ} (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)) (Λ Λ' : Lat E n) : Prop :=
  IsUnitary γ ∧ (Λ.map γ).L = Λ'.L ∧
    ∀ x ∈ Λ.L, ∃ k : ℕ, k.Coprime Δ.a.l₂.M ∧ k • (γ x - x) ∈ mulStd E n Δ.a.l₂.M

def MeetsAllClasses {n : ℕ} (T : Set (Lat E n)) : Prop :=
  T ⊆ reps Δ n 1 ∧ ∀ Λ ∈ reps Δ n 1, ∃ Λ' ∈ T, ∃ γ, IsPairIso Δ γ Λ Λ'

def IsSeriesData {n : ℕ} (Λ : Lat E n) (N : ℕ) (β : c.F) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  Λ ∈ reps Δ n 1 ∧ Λ.Admissible Δ.a.l₂.M N ∧ IsBeLat Dw c Λ β ∧ P ∈ harmLat Dw c a Λ

def genOn (hK : ReflexLe Dw c) {n : ℕ} (T : Set (Lat E n)) (adm : (Fin n → ConjCl Dw l) → Prop)
    (B : Lat E n → Set (MvPolynomial (LtN Dw n) c.F)) (a : (E →+* ℂ) × ℕ → ℕ) : Set (Rul Xo c) :=
  {f | ∃ Λ ∈ T, ∃ (N : ℕ) (x₀ : Fin n → ConjCl Dw l), ∃ P ∈ B Λ,
    IsSeriesData Δ Λ N (be hK Λ) a P ∧ adm x₀ ∧ IsShortRule Δ Λ N (be hK Λ) x₀ a P f}

def shortGen (hK : ReflexLe Dw c) (nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Rul Xo c) :=
  {f | ∃ (Λ : Lat E n) (N : ℕ) (x₀ : Fin n → ConjCl Dw l) (P : MvPolynomial (LtN Dw n) c.F),
    IsSeriesData Δ Λ N (be hK Λ) a P ∧ LevelSpanSeparation.Admissible nV x₀ ∧ IsShortRule Δ Λ N (be hK Λ) x₀ a P f}

def shortGenAny (nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Rul Xo c) :=
  {f | ∃ (Λ : Lat E n) (N : ℕ) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (P : MvPolynomial (LtN Dw n) c.F),
    IsSeriesData Δ Λ N β a P ∧ LevelSpanSeparation.Admissible nV x₀ ∧ IsShortRule Δ Λ N β x₀ a P f}

def shortSpan (hK : ReflexLe Dw c) (nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule (𝓞 c.F) (Rul Xo c) :=
  Submodule.span (𝓞 c.F) (shortGen Δ hK nV a n)

def CoverTot : Prop :=
  ∀ (n N : ℕ) (Λ : Lat E n) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F), IsSeriesData Δ Λ N β a P →
    ∀ (S : Type) [CommRing S] [Algebra Δ.cov.c₂.F S] (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S),
      ∃! v, CoverVal Δ y₂ Λ N β x₀ a P v

def Descends : Prop :=
  ∀ (n N : ℕ) (Λ : Lat E n) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F), IsSeriesData Δ Λ N β a P →
    ∃ f ∈ sec Xo c a n, IsShortRule Δ Λ N β x₀ a P f

def ShortRat : Prop := CoverTot Δ ∧ Descends Δ

def ShortFreeOfN : Prop :=
  ∀ (n N N' : ℕ) (Λ : Lat E n) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), IsSeriesData Δ Λ N β a P → Λ.Admissible Δ.a.l₂.M N' →
    IsShortRule Δ Λ N β x₀ a P f → IsShortRule Δ Λ N' β x₀ a P f

def OnePos (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∃ τ : E →+* ℂ, InPsi H τ ∧ (0 < Dw.p → 1 ≤ a (τ, Dw.p - 1))

def SeriesInCusp (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → OnePos Dw a →
    ∀ (N : ℕ) (Λ : Lat E n) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c),
      IsSeriesData Δ Λ N β a P → IsShortRule Δ Λ N β x₀ a P f → f ∈ cusp a n

def ShortInCusp (hK : ReflexLe Dw c) (nV : ℕ)
    (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → OnePos Dw a → ∀ f ∈ shortGen Δ hK nV a n, f ∈ cusp a n

def RepChange : Prop :=
  IsGalois ℚ E → Odd (Dw.p + Dw.q) → ∀ (n : ℕ), Even n →
    ∀ (Λ Λ' : Lat E n) (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)) (N N' : ℕ) (β β' : c.F),
      Λ' ∈ reps Δ n 1 → IsPairIso Δ γ Λ Λ' → Λ'.Admissible Δ.a.l₂.M N' → IsBeLat Dw c Λ' β' →
      ∃ ζ : c.F, IsOfFinOrder ζ ∧
        ∀ (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c),
          IsSeriesData Δ Λ N β a P → IsShortRule Δ Λ N β x₀ a P f →
          IsShortRule Δ Λ' N' β' x₀ a (push Dw c γ P) fun p y => algebraMap c.F p.R ζ * f p y

def FiniteReps : Prop :=
  ∀ (n : ℕ) (s : ℕ+), ∃ T : Set (Lat E n), T.Finite ∧ T ⊆ reps Δ n s ∧ MeetsAllClasses Δ T

def SpanOfReps (hK : ReflexLe Dw c) (nV : ℕ) : Prop :=
  IsGalois ℚ E → Odd (Dw.p + Dw.q) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Even n →
    Submodule.span (𝓞 c.F) (shortGenAny Δ nV a n) = shortSpan Δ hK nV a n ∧
    ∀ (T : Set (Lat E n)) (B : Lat E n → Set (MvPolynomial (LtN Dw n) c.F)), MeetsAllClasses Δ T →
      (∀ Λ ∈ T, (Submodule.span (𝓞 c.F) (B Λ) : Set (MvPolynomial (LtN Dw n) c.F)) = harmLat Dw c a Λ) →
      Submodule.span (𝓞 c.F) (genOn Δ hK T (LevelSpanSeparation.Admissible nV) B a) = shortSpan Δ hK nV a n

variable (Xo c) in

def ShortRatCanonical : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ Δ : DeltaDatum Xo c nab, ShortRat Δ

variable (Xo c) in

def ShortInCuspCanonical (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ),
    ShortInCusp Δ hK nV cusp

theorem IsShortRule.unique (h : CoverTot Δ) {n N : ℕ} {Λ : Lat E n} {β : c.F} {x₀ : Fin n → ConjCl Dw l}
    {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F} (hd : IsSeriesData Δ Λ N β a P) {f g : Rul Xo c}
    (hf : IsShortRule Δ Λ N β x₀ a P f) (hg : IsShortRule Δ Λ N β x₀ a P g) : f = g := by
  funext p y
  obtain ⟨⟨S', _, _, φ, y₂, hff, hl⟩, hf2⟩ := hf p y
  obtain ⟨v, hv, hfv⟩ := hf2 S' φ y₂ hl
  obtain ⟨w, hw, hgw⟩ := (hg p y).2 S' φ y₂ hl
  obtain ⟨u, -, hu⟩ := h n N Λ β x₀ a P hd S' y₂
  have hvw : v = w := (hu v hv).trans (hu w hw).symm
  apply hff.injective
  rw [hfv, hgw, hvw]

private theorem eqAtPrime_refl {n : ℕ} (p : ℕ) (hp : p.Prime) (L : Submodule (𝓞 E) (Fin n → E)) :
    EqAtPrime p L L :=
  ⟨fun x hx => ⟨1, hp.not_dvd_one, by simpa using hx⟩, fun x hx => ⟨1, hp.not_dvd_one, by simpa using hx⟩⟩

theorem std_mem_reps (n : ℕ) (s : ℕ+) : Lat.std E n ∈ reps Δ n s := by
  refine ⟨fun p hp => ⟨LinearEquiv.refl E _, fun x y => rfl, ?_⟩, fun p hp _ => eqAtPrime_refl p hp _⟩
  have hm : ((Lat.std E n).map (LinearEquiv.refl E _)).L = (Lat.std E n).L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [hm]
  exact eqAtPrime_refl p hp _

theorem exists_inPsi (H : Host E) : ∃ τ : E →+* ℂ, InPsi H τ := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  have e : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have h0 := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
    simpa using h0
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (e.trans H.sqrt_neg_disc_sq.symm) with h | h
  · exact ⟨τ, h⟩
  · refine ⟨(starRingEnd ℂ).comp τ, ?_⟩
    show starRingEnd ℂ (τ (H.rt : E)) = H.rt0
    rw [h, map_neg]
    have hs := H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have h1 := congrArg Complex.re hs
    have h2 := congrArg Complex.im hs
    simp [sq] at h1 h2
    have hre : H.rt0.re = 0 := by
      rcases mul_eq_zero.1 (show H.rt0.re * H.rt0.im = 0 by nlinarith [h2]) with h3 | h3
      · exact h3
      · rw [h3] at h1
        nlinarith [sq_nonneg H.rt0.re]
    apply Complex.ext <;> simp [hre]

end GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

set_option autoImplicit false

noncomputable section

open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.TL

variable {O : Type} [CommRing O] {d : ℕ}

def Fmod (p : ℕ) (F : FGLaw O d) (n : ℕ) : Fin d → PS (O ⧸ Ideal.span {(p : O) ^ (n + 1)}) 2 d :=
  fun i => MvPowerSeries.map (Ideal.Quotient.mk _) (F.F i)

theorem Fmod_const (p : ℕ) (F : FGLaw O d) (n : ℕ) (i : Fin d) : constantCoeff (Fmod p F n i) = 0 := by
  simp [Fmod, F.const i]

def redQ (p : ℕ) (n : ℕ) : O ⧸ Ideal.span {(p : O) ^ (n + 1 + 1)} →+* O ⧸ Ideal.span {(p : O) ^ (n + 1)} :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ _)))

def jetMap {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (κ : Type) (k : ℕ) :
    JetR A κ k →+* JetR B κ k :=
  Ideal.quotientMap _ (MvPolynomial.map g) (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, Ideal.map_span]
    refine Ideal.pow_right_mono (Ideal.span_mono ?_) _
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (MvPolynomial.map_X g i).symm⟩)

def LimSt : Prop :=
  ∀ (O : Type) [CommRing O] (p : ℕ) [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d)
    (U : ∀ n k : ℕ, JetR (O ⧸ Ideal.span {(p : O) ^ (n + 1)}) (Fin 1 × Fin d) k), 0 < d →
    (∀ n k, jetMap (redQ p n) (Fin 1 × Fin d) k (U (n + 1) k) = U n k) →
    (∀ n k, jetTruncR _ (Fin 1 × Fin d) k (U n (k + 1)) = U n k) →
    (∀ n k, jetZeroR _ (Fin 1 × Fin d) k (U n k) = 1) →
    (∀ n k, substJ (n := 2) k (Fmod p F n) (Fmod_const p F n) (U n k) =
      jetPt (n := 2) (0 : Fin 2) k (U n k) * jetPt (n := 2) (1 : Fin 2) k (U n k)) →
    ∃ u : PS O 1 d, IsCh F.F u ∧
      ∀ n k, psJet k (MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : O) ^ (n + 1)})) u) = U n k

end ReciprocityTheory.ChartRestriction.G.Pdiv.TL

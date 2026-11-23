import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial Filter

section Vol

variable {o : Type*} [CommRing o] {Ω : Type*} [CommRing Ω] [Algebra o Ω] {ι : Type*}

def ratVals (m : ConeMetric ℂ ι) (σ : o →+* ℂ) (x : ι → Ω) (τ : ℕ) (s : Ω) : Set ℝ :=
  {r | ∃ (e : ℕ) (g h : MvPolynomial ι o) (z : ι → ℂ),
    g ∈ homogeneousSubmodule ι o (e + τ) ∧ h ∈ homogeneousSubmodule ι o e ∧
    aeval x g = s * aeval x h ∧ z ∈ conePts σ (coordIdeal o x) ∧ eval z (map σ h) ≠ 0 ∧
    r = ‖eval z (map σ g)‖ / (‖eval z (map σ h)‖ * m.ρ z ^ τ)}

def ratSupNorm (m : ConeMetric ℂ ι) (σ : o →+* ℂ) (x : ι → Ω) (τ : ℕ) (s : Ω) : ℝ :=
  sSup (ratVals m σ x τ s)

def supNormAll {E : Type*} [Fintype E] (m : E → ConeMetric ℂ ι) (σ : E → (o →+* ℂ)) (x : ι → Ω)
    (τ : ℕ) (s : Ω) : ℝ :=
  ⨆ e, ratSupNorm (m e) (σ e) x τ s

def IsSmall {E : Type*} (m : E → ConeMetric ℂ ι) (σ : E → (o →+* ℂ)) (x : ι → Ω) (τ : ℕ) (s : Ω) : Prop :=
  ∀ e (d : ℕ) (g h : MvPolynomial ι o) (z : ι → ℂ),
    g ∈ homogeneousSubmodule ι o (d + τ) → h ∈ homogeneousSubmodule ι o d →
    aeval x g = s * aeval x h → z ∈ conePts (σ e) (coordIdeal o x) →
    ‖eval z (map (σ e) g)‖ ≤ ‖eval z (map (σ e) h)‖ * (m e).ρ z ^ τ

def smallSectionCount (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (τ : ℕ) : ℝ :=
  Real.log (Nat.card {s : La τ // P τ (s : Ω)})

def arVolP (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (a D : ℕ) : ℝ :=
  limsup (fun k : ℕ => smallSectionCount P La (a * k) /
    (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop

theorem ptNorm_mem_ratVals (m : ConeMetric ℂ ι) (σ : o →+* ℂ) (x : ι → Ω) {τ : ℕ}
    {f : MvPolynomial ι o} (hf : f ∈ homogeneousSubmodule ι o τ) {z : ι → ℂ}
    (hz : z ∈ conePts σ (coordIdeal o x)) :
    ptNorm m σ τ f z ∈ ratVals m σ x τ (aeval x f) := by
  refine ⟨0, f, 1, z, by simpa using hf, ?_, by simp, hz, by simp, ?_⟩
  · exact (MvPolynomial.mem_homogeneousSubmodule 0 1).2 (MvPolynomial.isHomogeneous_one ι o)
  · simp [ptNorm]

end Vol

end ReciprocityTheory.ChartRestriction.G.Geo

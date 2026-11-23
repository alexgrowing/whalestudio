import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace PositivityTheory.UnitarySelfGeneration

theorem same_orbit_log_height_difference {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A B : HermLine ι)
    (hab : B.a = A.a) (w z : (Σ k, ι k) → ℂ) (r : ℝ) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (hs : SameOrbit w z)
    (h : Real.log (A.h w) = Real.log (B.h w) + r) :
    0 < A.h z ∧ 0 < B.h z ∧ Real.log (A.h z) = Real.log (B.h z) + r := by
  obtain ⟨c, hc, rfl⟩ := hs
  have hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hw k
    exact ⟨i, fun h0 => hi (by simp [h0])⟩
  have hA := A.pos z hz
  have hB := B.pos z hz
  refine ⟨hA, hB, ?_⟩
  have hC : (∏ k, ‖c k‖ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [A.smul c z hc, B.smul c z hc, hab, Real.log_mul hC hA.ne', Real.log_mul hC hB.ne'] at h
  linarith

theorem h_samesing_ne {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (hP : P.IsPrime) (f g : MRing ι) (hu : UnitRatio P f g) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P)
    (u v : MRing ι) (huv : u * f - v * g ∈ P) (hu0 : evC z u ≠ 0) : evC z v ≠ 0 := by
  intro hv0
  obtain ⟨hf, -, hW⟩ := hu
  let φ : MRing ι →+* ℂ := (MvPolynomial.eval z).comp (MvPolynomial.map (Int.castRingHom ℂ))
  have hφ : ∀ h, φ h = evC z h := fun h => rfl
  have hWp : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hPW : P ≤ RingHom.ker φ := fun h hh => (RingHom.mem_ker).2 (by rw [hφ]; exact hz.2 h hh)
  have hrel : IsRelevant (RingHom.ker φ) := by
    intro k
    obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, fun h => hi ?_⟩
    have := (RingHom.mem_ker).1 h
    simpa [φ] using this
  obtain ⟨u', v', -, hv', h'⟩ := hW _ hWp hPW hrel
  have hmem : (u * v' - v * u') * f ∈ P := by
    have e : (u * v' - v * u') * f = v' * (u * f - v * g) - v * (u' * f - v' * g) := by ring
    rw [e]
    exact P.sub_mem (P.mul_mem_left _ huv) (P.mul_mem_left _ h')
  have hin : u * v' - v * u' ∈ P := (hP.mem_or_mem hmem).resolve_right hf
  have h0 : φ (u * v' - v * u') = 0 := by rw [hφ]; exact hz.2 _ hin
  rw [map_sub, map_mul, map_mul, hφ v, hv0, zero_mul, sub_zero] at h0
  have hv'' : φ v' ≠ 0 := fun h => hv' (RingHom.mem_ker.2 h)
  exact mul_ne_zero (by rw [hφ]; exact hu0) hv'' h0

theorem h_samesing : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (P : Ideal (MRing ι)) (P₁ : Ideal (MRing ι₁)) (P₂ : Ideal (MRing ι₂)) (D : ℕ) (σ₁ σ₂ : Type) (S₁ : PB.AnSys D σ₁) (S₂ : PB.AnSys D σ₂) (Re₁ : PB.Realis S₁ P₁) (Re₂ : PB.Realis S₂ P₂) (β : MRing ι) (a₁ : σ₁) (a₂ : σ₂) (A₁ : HermLine ι₁) (A₂ : HermLine ι₂) (A₁' A₂' : HermLine ι), IsBlockMap κ₁ v₁ → IsBlockMap κ₂ v₂ → IsPullHerm κ₁ v₁ A₁ A₁' → IsPullHerm κ₂ v₂ A₂ A₂' → (Re₁.ref a₁).a = A₁.a → (Re₂.ref a₂).a = A₂.a → (∀ x, Re₁.π x ∉ ReciprocityTheory.AnForm.P.bdry S₁.s → Real.log (A₁.h (Re₁.R.lift x x)) = Real.log ((Re₁.ref a₁).h (Re₁.R.lift x x)) + S₁.ph a₁ (Re₁.π x)) → (∀ x, Re₂.π x ∉ ReciprocityTheory.AnForm.P.bdry S₂.s → Real.log (A₂.h (Re₂.R.lift x x)) = Real.log ((Re₂.ref a₂).h (Re₂.R.lift x x)) + S₂.ph a₂ (Re₂.π x)) → IsMultiProjPrime P → IsoLineOn P {z | z ∈ mcPts P ∧ evC z β ≠ 0} A₁' A₂' → SameSing Re₁ Re₂ P κ₁ v₁ κ₂ v₂ β a₁ a₂ := by
  intro K _ ι _ K₁ _ ι₁ _ K₂ _ ι₂ _ κ₁ v₁ κ₂ v₂ P P₁ P₂ D σ₁ σ₂ S₁ S₂ Re₁ Re₂ β a₁ a₂ A₁ A₂ A₁' A₂'
    hb₁ hb₂ hp₁ hp₂ ha₁ ha₂ hφ₁ hφ₂ hP hiso
  obtain ⟨f, g, hfg, hdef⟩ := hiso
  refine ⟨f, g, ?_, ?_⟩
  · rw [ha₁, ha₂, ← hp₁.1, ← hp₂.1]
    exact hfg
  · intro z hz hβ x₁ x₂ hs₁ hs₂ hb₁' hb₂' u v huv hu
    have hw₁ := (Re₁.R.mem x₁ x₁ (Re₁.R.mem_U x₁)).1
    have hw₂ := (Re₂.R.mem x₂ x₂ (Re₂.R.mem_U x₂)).1
    obtain ⟨q₁, r₁, e₁⟩ := same_orbit_log_height_difference A₁ (Re₁.ref a₁) ha₁ _ _ _ hw₁ hs₁ (hφ₁ x₁ hb₁')
    obtain ⟨q₂, r₂, e₂⟩ := same_orbit_log_height_difference A₂ (Re₂.ref a₂) ha₂ _ _ _ hw₂ hs₂ (hφ₂ x₂ hb₂')
    have hv := h_samesing_ne P hP.1 f g hfg.2 z hz u v huv hu
    have hd := hdef z ⟨hz, hβ⟩ u v huv hu
    rw [← hp₁.2 z] at q₁ e₁
    rw [← hp₂.2 z] at q₂ e₂
    have hu' : 0 < ‖evC z v‖ / ‖evC z u‖ := div_pos (norm_pos_iff.2 hv) (norm_pos_iff.2 hu)
    rw [Real.log_div (mul_pos hu' q₂).ne' q₁.ne', Real.log_mul hu'.ne' q₂.ne'] at hd
    rw [Real.log_div (mul_pos hu' r₂).ne' r₁.ne', Real.log_mul hu'.ne' r₂.ne']
    linarith

end PositivityTheory.UnitarySelfGeneration

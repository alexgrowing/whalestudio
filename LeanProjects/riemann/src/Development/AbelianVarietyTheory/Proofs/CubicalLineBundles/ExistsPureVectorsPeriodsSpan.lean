import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSymplecticCoordinatesOfIsPeriod

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem span_pure_periods_eq_top {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe) {p q : ℕ} (Z : CMLat hP p q) :
    Submodule.span ℂ {v : Fin g → ℂ | ∃ (ε : ℤˣ) (a : PureType.lat hP (((ε : ℤ) : ℂ) * H.rt0)), Pe a = v} = ⊤ := by
  set W := Submodule.span ℂ {v : Fin g → ℂ | ∃ (ε : ℤˣ) (a : PureType.lat hP (((ε : ℤ) : ℂ) * H.rt0)), Pe a = v}
  obtain ⟨n, hn, h⟩ := Z.span
  have key : ∀ a, Pe a ∈ W := by
    intro a
    obtain ⟨x, hx⟩ := h a
    have h1 : (n : ℂ) • Pe a ∈ W := by
      rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, hx, map_sum]
      refine W.sum_mem fun j _ => Submodule.subset_span ?_
      have h2 := Z.pure j (x j)
      rcases j with j | j
      · exact ⟨1, ⟨_, by simpa using h2⟩, rfl⟩
      · exact ⟨-1, ⟨_, by simpa using h2⟩, rfl⟩
    exact (W.smul_mem_iff (Nat.cast_ne_zero.2 hn.ne')).1 h1
  have h3 : Submodule.span ℝ (Set.range Pe) ≤ W.restrictScalars ℝ :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact key a)
  rw [hP.2.2.2.1] at h3
  exact eq_top_iff.2 fun v _ => h3 Submodule.mem_top

theorem exists_pure_vectors_periods_span :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty Pe) (p q : ℕ) (Z : CMLat hP p q), ∃ (ε : Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) → ℤˣ) (a : ∀ i, PureType.lat hP (((ε i : ℤ) : ℂ) * H.rt0)), ∀ z : Fin g → ℂ, ∃ c : Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) → ℂ, z = ∑ i, c i • Pe (a i) := by
  intro E _ _ _ H D g ty Pe hP p q Z
  have h1 := (FibreExp.free_finite_finrank_of_isPeriod hP).2.2
  rw [datum_finrank_int D] at h1
  have hs := span_pure_periods_eq_top hP Z
  have h2 := Submodule.exists_fun_fin_finrank_span_eq ℂ
    {v : Fin g → ℂ | ∃ (ε : ℤˣ) (a : PureType.lat hP (((ε : ℤ) : ℂ) * H.rt0)), Pe a = v}
  rw [hs, finrank_top, Module.finrank_fin_fun] at h2
  have hg : Module.finrank ℚ E / 2 * (D.p + D.q) = g := by omega
  rw [hg]
  obtain ⟨f, hf, hsp, -⟩ := h2
  choose ε a ha using hf
  refine ⟨ε, a, fun z => ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hsp ▸ Submodule.mem_top (x := z))
  exact ⟨c, by simp [ha, hc]⟩

end GlobalTheory.CM

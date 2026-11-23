import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPureVectorsPeriodsSpan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

theorem pure_type_periods_span_whole_space {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) {n : ℕ} (hn : 0 < n)
    (h : ∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) :
    Submodule.span ℂ {v : Fin g → ℂ | ∃ (bo : Bool) (a : PureType.lat hP (sgnRt H bo)), P a = v} = ⊤ := by
  classical
  set S := {v : Fin g → ℂ | ∃ (bo : Bool) (a : PureType.lat hP (sgnRt H bo)), P a = v} with hS
  have hsub : Set.range P ⊆ (Submodule.span ℂ S : Set (Fin g → ℂ)) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := h y
    have h1 : P a ∈ Submodule.span ℂ S := Submodule.subset_span ⟨true, ⟨a, ha⟩, rfl⟩
    have h2 : P b ∈ Submodule.span ℂ S := Submodule.subset_span ⟨false, ⟨b, hb⟩, rfl⟩
    have h3 : (n : ℂ) • P y = P a + P b := by
      rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, hab, map_add]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have h4 : P y = (n : ℂ)⁻¹ • (P a + P b) := by
      rw [← h3, smul_smul, inv_mul_cancel₀ hn', one_smul]
    rw [SetLike.mem_coe, h4]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ h1 h2)
  have hR := hP.2.2.2.1
  rw [eq_top_iff]
  rintro z -
  have hz : z ∈ Submodule.span ℝ (Set.range P) := by rw [hR]; trivial
  have hle : Submodule.span ℝ (Set.range P) ≤ (Submodule.span ℂ S).restrictScalars ℝ :=
    Submodule.span_le.mpr hsub
  exact hle hz

theorem periods_span_pure_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (n : ℕ), 0 < n → (∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))), ∀ z : Fin g → ℂ, ∃ s : Fin g → ℂ, z = ∑ k, s k • P (a k) := by
  intro E _ _ _ H D g ty P hP n hn h
  classical
  refine ⟨?_, ?_⟩
  · have h1 := (GlobalTheory.FibreExp.free_finite_finrank_of_isPeriod hP).2.2
    have h2 := GlobalTheory.datum_finrank_int D
    exact Nat.eq_of_mul_eq_mul_left two_pos (h1.symm.trans h2)
  · have hspan := pure_type_periods_span_whole_space hP hn h
    set S := {v : Fin g → ℂ | ∃ (bo : Bool) (a : PureType.lat hP (sgnRt H bo)), P a = v} with hS
    obtain ⟨s, hsS, hs, hli⟩ := exists_linearIndependent ℂ S
    have hst : Submodule.span ℂ (Set.range ((↑) : s → (Fin g → ℂ))) = ⊤ := by
      rw [Subtype.range_coe, hs, hspan]
    let bs := Module.Basis.mk hli (le_of_eq hst.symm)
    let e : Fin g ≃ s := (bs.indexEquiv (Pi.basisFun ℂ (Fin g))).symm
    have hmem : ∀ k, ∃ (bo : Bool) (a : PureType.lat hP (sgnRt H bo)), P a = (e k : Fin g → ℂ) :=
      fun k => hsS (e k).2
    choose bf af haf using hmem
    refine ⟨bf, af, fun z => ?_⟩
    have hz : z ∈ Submodule.span ℂ (Set.range fun k => P (af k)) := by
      have hr : (Set.range fun k => P (af k)) = Set.range ((↑) : s → (Fin g → ℂ)) := by
        ext v
        constructor
        · rintro ⟨k, rfl⟩
          exact ⟨e k, (haf k).symm⟩
        · rintro ⟨t, rfl⟩
          exact ⟨e.symm t, by simp [haf]⟩
      rw [hr, hst]
      trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hz
    exact ⟨c, hc.symm⟩

end PositivityTheory.Xgf

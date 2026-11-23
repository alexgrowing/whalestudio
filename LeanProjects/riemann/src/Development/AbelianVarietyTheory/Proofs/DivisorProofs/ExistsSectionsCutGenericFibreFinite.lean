import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimDropAndFiniteOfDimZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowerSectionNonvanishingOnFiniteStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.GenCut

theorem exists_finite_drop {T : Type} [TopologicalSpace T] [NoetherianSpace T] (Y : Set T) (d : ℕ)
    (hY : topologicalKrullDim Y ≤ (d + 1 : ℕ)) :
    ∃ S : Set T, S.Finite ∧ ∀ U : Set T, IsOpen U → S ⊆ U → topologicalKrullDim ↥(Y \ U) ≤ d := by
  classical
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := Y)
  have hne : ∀ C : irreducibleComponents Y, ∃ y : Y, y ∈ C.1 := fun C => C.2.1.nonempty
  choose y hy using hne
  have : Finite (irreducibleComponents Y) := hfin.to_subtype
  refine ⟨Set.range fun C => (y C : T), Set.finite_range _, fun U hU hS => ?_⟩
  have hC : IsClosed ((Subtype.val : Y → T) ⁻¹' Uᶜ) := hU.isClosed_compl.preimage continuous_subtype_val
  have h := (GlobalTheory.T.topologicalKrullDim_drop_and_finite_of_dim_zero Y).1 _ (d + 1) hC hY fun Z hZ _ hsub =>
    hsub (hy ⟨Z, hZ⟩) (hS ⟨⟨Z, hZ⟩, rfl⟩)
  let f : ↥(Y \ U) → ↥((Subtype.val : Y → T) ⁻¹' Uᶜ) := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  have hf : IsInducing f := by
    refine (IsInducing.subtypeVal.comp IsInducing.subtypeVal).of_comp_iff.1 ?_
    exact IsInducing.subtypeVal
  have h2 := lt_of_le_of_lt hf.topologicalKrullDim_le h
  rw [Nat.cast_add, Nat.cast_one] at h2
  exact ENat.WithBot.lt_add_one_iff.1 h2

theorem exists_sections_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (d : ℕ) (Z : Set X), IsClosed Z → topologicalKrullDim ↥(Z ∩ fib X 0) ≤ d → ∃ (e : Fin d → ℕ) (g : Fin d → X.functionField), (∀ j, 0 < e j ∧ g j ∈ P.H (e j) 0) ∧ ((Z \ ⋃ j, NV P (e j) 0 (g j)) ∩ fib X 0).Finite := by
  intro k _ X _ p D hp P hA d
  have := hp.isNoetherian
  induction d with
  | zero =>
    intro Z _ hd
    have hf : Finite ↥(Z ∩ fib X 0) := (GlobalTheory.T.topologicalKrullDim_drop_and_finite_of_dim_zero ↥(Z ∩ fib X 0)).2 inferInstance (by simpa using hd)
    refine ⟨Fin.elim0, Fin.elim0, fun j => j.elim0, ?_⟩
    exact (Set.toFinite (Z ∩ fib X 0)).subset (Set.inter_subset_inter_left _ Set.sdiff_subset)
  | succ d ih =>
    intro Z hZ hd
    obtain ⟨S, hS, hdrop⟩ := exists_finite_drop (Z ∩ fib X 0) d hd
    obtain ⟨e₀, he₀, f, hf, hSf⟩ := GlobalTheory.T.exists_ample_power_section_nonvanishing_on_finite k X p D hp P hA S hS
    have hU : IsOpen (NV P e₀ 0 f) := (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e₀ 0 f hf).1
    have h := hdrop _ hU hSf
    rw [show (Z ∩ fib X 0) \ NV P e₀ 0 f = (Z \ NV P e₀ 0 f) ∩ fib X 0 from by
      ext x; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto] at h
    obtain ⟨e, g, heg, hfin⟩ := ih _ (hZ.sdiff hU) h
    refine ⟨Fin.cons e₀ e, Fin.cons f g, fun j => ?_, hfin.subset ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact ⟨he₀, hf⟩
      · exact heg j
    · rintro x ⟨⟨hxZ, hx⟩, hx0⟩
      simp only [Set.mem_iUnion, not_exists] at hx
      refine ⟨⟨⟨hxZ, hx 0⟩, ?_⟩, hx0⟩
      simp only [Set.mem_iUnion, not_exists]
      exact fun j => hx j.succ

end GlobalTheory.HSAmp.GenCut

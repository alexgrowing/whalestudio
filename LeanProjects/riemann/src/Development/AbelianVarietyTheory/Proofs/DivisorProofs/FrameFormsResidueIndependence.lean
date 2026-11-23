import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentImagesLinearIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndepDiscrep

theorem neg_one_lt_formOrd_sub_sum : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], topologicalKrullDim Y = n → ∀ (y : Y) (U : Y.Opens) (hy : y ∈ U) (ω : FormsOn q n U), IsFrame ω → ∀ (J : Type) [Fintype J] (a : J → Y.presheaf.stalk y) (ha : ∀ j, a j ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (v : J → Y.functionFieldˣ) (c : J → ℚ), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨a j, ha j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y))) → (∀ j, (v j : Y.functionField) = algebraMap (Y.presheaf.stalk y) Y.functionField (a j)) → (∀ j, c j < 1) → ∀ E : DivOver q, E.Through y → -1 < (E.formOrd (formOf U (gen_mem hy) ω) : ℚ) - ∑ j, c j * E.ord (v j) := by
  classical
  intro Y _ _ q n _ hn y U hy ω hω J _ a ha v c hind hv hc E hE
  haveI := SmoothOfRelativeDimension.smooth n q
  haveI : GlobalTheory.IsNormalScheme Y := GlobalTheory.ModifSections.isNormalScheme_of_smooth q
  obtain ⟨U', hy', z, e, he, hze, hz⟩ :=
    GlobalTheory.AdaptedFrame.exists_adapted_frame (p := q) (n := n) y a ha hind
  have h0 : formOf U (gen_mem hy) ω ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hy) hω).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  have h0' : formOf U' (gen_mem hy') (dOn q z) ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hy') hz).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨f, hf⟩ := (isFreeGen_formOf (gen_mem hy') hz).2 (formOf U (gen_mem hy) ω)
  have hf0 : f ≠ 0 := fun h => h0 (by rw [← hf, h]; exact zero_smul _ _)
  set u : Y.functionFieldˣ := Units.mk0 f hf0 with hu
  have hfu : ((u : Y.functionField) • formOf U' (gen_mem hy') (dOn q z)) = formOf U (gen_mem hy) ω :=
    by rw [hu, Units.val_mk0]; exact hf
  have hF (Fd : DivOver q) : Fd.formOrd (formOf U (gen_mem hy) ω) =
      Fd.ord u + Fd.formOrd (formOf U' (gen_mem hy') (dOn q z)) := by
    rw [← Fd.formOrd_smul hn h0' u, hfu]
  have h0z : ∀ w, w ⤳ y → ∀ Fd : DivOver q, Fd.IsAt w → Fd.ord u = 0 := by
    intro w hw Fd hFd
    have h1 := hF Fd
    have a1 := DivOver.formOrd_formOf_eq_zero (hw.mem_open U.isOpen hy) hFd hω
    have a2 := DivOver.formOrd_formOf_eq_zero (hw.mem_open U'.isOpen hy') hFd hz
    rw [a1, a2] at h1
    omega
  have reg : ∀ w : Y.functionFieldˣ,
      (∀ x, x ⤳ y → ∀ Fd : DivOver q, Fd.IsAt x → 0 ≤ Fd.ord w) → 0 ≤ E.ord w := fun w hw =>
    (E.ord_nonneg_iff w).2 (hE _ (regAt_of_forall_coheight_eq_one fun x hx h1 =>
      have ⟨Fd, hFd⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := q) h1
      (hFd _).1 ((Fd.ord_nonneg_iff w).1 (hw x hx Fd hFd))))
  have hu1 := reg u fun x hx Fd hFd => (h0z x hx Fd hFd).ge
  have hu2 := reg u⁻¹ fun x hx Fd hFd => by rw [Fd.ord_inv, h0z x hx Fd hFd, neg_zero]
  rw [E.ord_inv] at hu2
  have hu0 : E.ord u = 0 := by omega
  have hA := DivOver.sum_ord_sub_one_le_formOrd_dOn hn E hy' hE z h0' e he v fun j => by
    rw [hv, ← hze j, algebraMap_germ]
  have hN := DivOver.formOrd_formOf_nonneg hn hy' hE (dOn q z) h0'
  have hnn : ∀ j, 0 ≤ E.ord (v j) := fun j => (E.ord_nonneg_iff _).2 (hE _ ⟨a j, (hv j).symm⟩)
  rw [hF E, hu0, zero_add]
  have hAq : (∑ j, (E.ord (v j) : ℚ)) - 1 ≤ (E.formOrd (formOf U' (gen_mem hy') (dOn q z)) : ℚ) := by
    exact_mod_cast hA
  have hNq : (0 : ℚ) ≤ (E.formOrd (formOf U' (gen_mem hy') (dOn q z)) : ℚ) := by exact_mod_cast hN
  have hle : ∀ j, c j * (E.ord (v j) : ℚ) ≤ E.ord (v j) := fun j => by
    have : (0 : ℚ) ≤ E.ord (v j) := by exact_mod_cast hnn j
    nlinarith [hc j]
  by_cases h : ∃ j, 0 < E.ord (v j)
  · obtain ⟨j, hj⟩ := h
    have hlt : ∑ j, c j * (E.ord (v j) : ℚ) < ∑ j, (E.ord (v j) : ℚ) :=
      Finset.sum_lt_sum (fun j _ => hle j) ⟨j, Finset.mem_univ _, by
        have : (0 : ℚ) < E.ord (v j) := by exact_mod_cast hj
        nlinarith [hc j]⟩
    linarith
  · push_neg at h
    have h' : ∀ j, E.ord (v j) = 0 := fun j => le_antisymm (h j) (hnn j)
    simp only [h', Int.cast_zero, mul_zero, Finset.sum_const_zero, sub_zero]
    linarith

end GlobalTheory.IndepDiscrep

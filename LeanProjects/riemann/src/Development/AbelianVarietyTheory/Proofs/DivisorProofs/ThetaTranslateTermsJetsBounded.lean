import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyTermTranslateBoundFunctionalEquationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateSectionValuesBoundedIntegralTangentStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow

theorem jc_bound_k (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V))
    (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C]
    (hC : CExt V (IsLocalRing.maximalIdeal V) C) (N : NumD C) (ν : NumOf D.toPre C N) (hν : ν.IntN)
    (q : QuadraticMap ℤ N.X ℝ) (hq : N.Int q) (k : ℕ) (hk1 : 1 ≤ k) (s : Fam D.toPre C k) (gm₀ : GtPt D.toPre (epsR V))
    (gm : GtPt D.toPre (TE V C)) (htan : GtTan gm₀) (hpull : GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm) :
    ∃ b : ℝ, ∀ α, ‖(jc ν s gm α).fst / ν.rg ^ k‖ ≤ b * Real.exp (-(q α / (k : ℝ))) ∧
      ‖(jc ν s gm α).snd / ν.rg ^ k‖ ≤ b * Real.exp (-(q α / (k : ℝ))) := by
  have H1 := GlobalTheory.T.familyTerm_translate_bound_functionalEquation V D C hC N ν hν q hq k hk1 s gm₀ gm htan hpull
  have H2 := GlobalTheory.T.translate_section_values_bounded_integral_tangent V D C hC N ν hν k hk1 s gm₀ gm htan hpull
  choose bb hbb using H2
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hk1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  let bs := Module.Free.chooseBasis ℤ N.X
  let g : (Module.Free.ChooseBasisIndex ℤ N.X → Fin k) → N.X := fun c => ∑ i, ((c i : ℕ) : ℤ) • bs i
  let quo : N.X → N.X := fun χ => ∑ i, (bs.repr χ i / (k : ℤ)) • bs i
  let cOf : N.X → Module.Free.ChooseBasisIndex ℤ N.X → Fin k := fun χ i =>
    ⟨(bs.repr χ i % (k : ℤ)).toNat, by
      have h1 := Int.emod_nonneg (bs.repr χ i) hk0.ne'
      have h2 := Int.emod_lt_of_pos (bs.repr χ i) hk0
      omega⟩
  have hdec : ∀ χ, χ = g (cOf χ) + k • quo χ := by
    intro χ
    have e1 : ∀ i, (((cOf χ i : ℕ) : ℤ)) = bs.repr χ i % (k : ℤ) := fun i =>
      Int.toNat_of_nonneg (Int.emod_nonneg _ hk0.ne')
    have e2 : k • quo χ = ∑ i, ((k : ℤ) * (bs.repr χ i / (k : ℤ))) • bs i := by
      rw [← natCast_zsmul, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
    rw [e2]
    simp only [g, e1, ← Finset.sum_add_distrib, ← add_smul]
    conv_lhs => rw [← bs.sum_repr χ]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have := Int.mul_ediv_add_emod (bs.repr χ i) (k : ℤ)
    linarith
  have hqk : ∀ a mu : N.X, q (a + k • mu) = q a + (k : ℝ) ^ 2 * q mu + (k : ℝ) * QuadraticMap.polar q mu a := by
    intro a mu
    have e1 : q (k • mu + a) = q (k • mu) + q a + QuadraticMap.polar q (k • mu) a := by
      simp only [QuadraticMap.polar]; ring
    have e2 : q (k • mu) = ((k : ℤ) * (k : ℤ)) • q mu := by
      rw [← natCast_zsmul]; exact QuadraticMap.map_smul q _ _
    have e3 : QuadraticMap.polar q (k • mu) a = (k : ℤ) • QuadraticMap.polar q mu a := by
      rw [← natCast_zsmul]; exact QuadraticMap.polar_smul_left q _ _ _
    rw [add_comm, e1, e2, e3, zsmul_eq_mul, zsmul_eq_mul]
    push_cast; ring
  have hexp : ∀ a mu : N.X, Real.exp (-((k : ℝ) * q mu + QuadraticMap.polar q mu a)) =
      Real.exp (q a / k) * Real.exp (-(q (a + k • mu) / k)) := by
    intro a mu
    rw [← Real.exp_add, hqk]
    congr 1
    field_simp
    ring
  let B : ℝ := ∑ c, max 0 (bb (g c) * Real.exp (q (g c) / k))
  have hB : ∀ c, bb (g c) * Real.exp (q (g c) / k) ≤ B := fun c =>
    (le_max_right _ _).trans (Finset.single_le_sum (f := fun c => max 0 (bb (g c) * Real.exp (q (g c) / k)))
      (fun _ _ => le_max_left _ _) (Finset.mem_univ c))
  refine ⟨‖ν.rg ^ k‖⁻¹ * B, fun α => ?_⟩
  have hα := hdec α
  obtain ⟨h1, h2⟩ := H1 (g (cOf α)) (quo α)
  obtain ⟨h3, h4⟩ := hbb (g (cOf α)) (quo α)
  have hE := hexp (g (cOf α)) (quo α)
  rw [← hα] at h1 h2 hE
  have key : ∀ x : ℝ, x ≤ Real.exp (-((k : ℝ) * q (quo α) + QuadraticMap.polar q (quo α) (g (cOf α)))) * bb (g (cOf α)) →
      x ≤ B * Real.exp (-(q α / k)) := by
    intro x hx
    refine hx.trans ?_
    rw [hE]
    calc Real.exp (q (g (cOf α)) / k) * Real.exp (-(q α / k)) * bb (g (cOf α)) =
        (bb (g (cOf α)) * Real.exp (q (g (cOf α)) / k)) * Real.exp (-(q α / k)) := by ring
      _ ≤ B * Real.exp (-(q α / k)) := mul_le_mul_of_nonneg_right (hB _) (Real.exp_pos _).le
  have hE0 := Real.exp_pos (-((k : ℝ) * q (quo α) + QuadraticMap.polar q (quo α) (g (cOf α))))
  have hr0 : 0 ≤ ‖ν.rg ^ k‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  constructor
  · rw [norm_div, div_eq_mul_inv, mul_comm, _root_.mul_assoc]
    exact mul_le_mul_of_nonneg_left (key _ (h1.trans (mul_le_mul_of_nonneg_left h3 hE0.le))) hr0
  · rw [norm_div, div_eq_mul_inv, mul_comm, _root_.mul_assoc]
    exact mul_le_mul_of_nonneg_left (key _ (h2.trans (mul_le_mul_of_nonneg_left (max_le h3 h4) hE0.le))) hr0

theorem jc_bound : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ q, N.Int q → ∀ (m : ℕ), Odd m → ∀ (p : N.QT (m ^ 2)) (s : Fam D.toPre C (m ^ 2)) (f : N.X → N.A → C), ν.FamV s f → IsEvFam N m p f → ∀ (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∃ b : ℝ, ∀ α, ‖(jc ν s gm α).fst / ν.rg ^ (m ^ 2)‖ ≤ b * Real.exp (-(q α / (m : ℝ) ^ 2)) ∧ ‖(jc ν s gm α).snd / ν.rg ^ (m ^ 2)‖ ≤ b * Real.exp (-(q α / (m : ℝ) ^ 2)) := by
  intro V _ _ _ D C _ _ _ _ _ hC N ν hν q hq m hm p s f hf hev gm₀ gm htan hpull
  have hk1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  obtain ⟨b, hb⟩ := jc_bound_k V D C hC N ν hν q hq (m ^ 2) hk1 s gm₀ gm htan hpull
  refine ⟨b, fun α => ?_⟩
  have hcast : (((m ^ 2 : ℕ) : ℝ)) = (m : ℝ) ^ 2 := by push_cast; ring
  rw [← hcast]
  exact hb α

end GlobalTheory.MBLow

end

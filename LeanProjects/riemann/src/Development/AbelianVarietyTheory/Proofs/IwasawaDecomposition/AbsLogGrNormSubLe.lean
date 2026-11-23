import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleStageOfPackage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatDRSubsetLatHT

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.FactorDepth

namespace GlobalTheory.HTFrame

attribute [local instance] Over.cartesianMonoidalCategory

theorem abs_log_sInf_sub_le {A B : Set ℝ} {c : ℝ} (hc : 1 ≤ c) (hB : ∀ r ∈ B, 0 ≤ r) (hAB : A ⊆ B)
    (hBA : ∀ r ∈ B, c * r ∈ A) : |Real.log (sInf A) - Real.log (sInf B)| ≤ Real.log c := by
  have hc0 : 0 < c := by linarith
  rcases B.eq_empty_or_nonempty with rfl | hne
  · rw [Set.subset_empty_iff.1 hAB, sub_self, abs_zero]
    exact Real.log_nonneg hc
  obtain ⟨r0, hr0⟩ := hne
  have bB : BddBelow B := ⟨0, hB⟩
  have bA : BddBelow A := bB.mono hAB
  have h1 : sInf B ≤ sInf A := csInf_le_csInf bB ⟨_, hBA r0 hr0⟩ hAB
  have h2 : sInf A ≤ c * sInf B := by
    rw [← div_le_iff₀' hc0]
    exact le_csInf ⟨r0, hr0⟩ fun r hr => (div_le_iff₀' hc0).2 (csInf_le bA (hBA r hr))
  have h0 : 0 ≤ sInf B := le_csInf ⟨r0, hr0⟩ hB
  rcases h0.eq_or_lt with h | h
  · have : sInf A = sInf B := le_antisymm (by rw [← h] at h2 ⊢; simpa using h2) h1
    rw [this, sub_self, abs_zero]
    exact Real.log_nonneg hc
  · have h3 := Real.log_le_log h h1
    have h4 := Real.log_le_log (h.trans_le h1) h2
    rw [Real.log_mul hc0.ne' h.ne'] at h4
    rw [abs_of_nonneg (by linarith)]
    linarith

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

open MonObj in

theorem comb_smul {S : Type} [CommRing S] (a : S) {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) : IsCombAtG t x v (fun i => a * cf i) (spMap (epsMul a) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG x ⟶ tEpsG x := Over.homMk (spMap (epsMul a)) (by
    show spMap (epsMul a) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S (DualNumber S)) ≫ x
    rw [← Category.assoc, spMap_comp']
    congr 2
    refine RingHom.ext fun r => ?_
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, spMap_comp']
    congr 2
    refine RingHom.ext fun r => ?_
    ext
    · simp [epsMul]
    · simp [epsMul]
      ring
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

theorem abs_log_grNorm_sub_le (x : Sp C ⟶ X) {Λ Λ' : Set (Sp (DualNumber C) ⟶ t.G.left)} {a : C} (ha : a ≠ 0)
    (ha1 : ‖a‖ ≤ 1) (h1 : Λ ⊆ Λ') (h2 : ∀ v ∈ Λ', spMap (epsMul a) ≫ v ∈ Λ) {m : ℕ}
    (u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)) (i : Fin m) :
    |Real.log (grNorm t x Λ u i) - Real.log (grNorm t x Λ' u i)| ≤ Real.log ‖a‖⁻¹ := by
  refine abs_log_sInf_sub_le ((one_le_inv₀ (norm_pos_iff.2 ha)).2 ha1) ?_ ?_ ?_
  · rintro r ⟨cf, -, -, -, rfl⟩
    positivity
  · rintro r ⟨cf, h3, h4, ⟨w, hw, hc⟩, rfl⟩
    exact ⟨cf, h3, h4, ⟨w, h1 hw, hc⟩, rfl⟩
  · rintro r ⟨cf, h3, h4, ⟨w, hw, hc⟩, rfl⟩
    refine ⟨fun k => a * cf k, mul_ne_zero ha h3, fun k hk => by simp [h4 k hk], ⟨_, h2 w hw, comb_smul t a hc⟩, ?_⟩
    rw [norm_mul, mul_inv]

end Lat

section Ext

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem existsUnique_ext (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] (x : Sp C ⟶ Z.X) : ∃! xO : Sp ↥(intO C) ⟶ Z.X, spMap (intO C).subtype ≫ xO = x := by
  obtain ⟨-, xO, hx, -⟩ := GlobalTheory.ShFam.Pad.Test.latDR_nonempty Z x
  refine ⟨xO, hx, fun xO' hx' => ?_⟩
  have := isProper_toroidalModel_structureMap Z
  have hs : IsSeparated (terminal.from Z.X) := by
    rw [← terminal.comp_from Z.s]
    infer_instance
  let S : ValuativeCommSq (terminal.from Z.X) :=
    { R := intO C, K := C, i₁ := x, i₂ := terminal.from _, commSq := ⟨terminal.hom_ext _ _⟩ }
  have hu := IsSeparated.valuativeCriterion (terminal.from Z.X) S
  exact congrArg CommSq.LiftStruct.l
    (hu.elim ⟨xO', hx', terminal.hom_ext _ _⟩ ⟨xO, hx, terminal.hom_ext _ _⟩)

end Ext

end GlobalTheory.HTFrame

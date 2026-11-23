import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarsInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTwistedGeneratorOfFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordTermTranslateNormalisedGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSectionRelatedAtZeroShiftStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam

theorem exists_secT_weight_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (a : D.P.A ⟶ D.P.A) (N : ℕ) (σ₀ : LB.Sec (LB.LinComb D.P.L (K := Fin 2) ![𝟙 D.P.A.left, a.left] ![(N : ℤ), -1])) (β : D.X), β = 0 → ∃ s : SecT D a N (-1) β, ∀ (Z : Scheme.{0}) (x : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J → sval s x z J = sval σ₀ x z J := by
  intro R _ _ D a N σ₀ β hβ
  subst hβ
  have hc : (toUnit D.P.A ≫ D.c 0) = (1 : D.P.A ⟶ D.P.A) := GlobalTheory.CoordToExt.c_zero D D.P.A
  have h1 : (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0)).left = 𝟙 D.P.A.left := by
    rw [hc]
    have e : padd D.P.A (𝟙 D.P.A) (1 : D.P.A ⟶ D.P.A) = 𝟙 D.P.A * 1 := rfl
    rw [e, _root_.mul_one]
    rfl
  have h2 : (toUnit D.P.A ≫ D.c 0).left = (toUnit D.P.A ≫ η[D.P.A]).left := by
    rw [hc]
    rfl
  obtain ⟨d, hd⟩ := GlobalTheory.exists_sec_relation_defect D.P.A.left D.P.A.left D.P.A.left D.P.L D.P.isLB _ _ _
    ![𝟙 D.P.A.left, a.left] ![(N : ℤ), -1] (tφ D a 0) (tε N (-1)) _ _ (𝟙 _) σ₀
    (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.secZero _) (LB.oneGen D.P.L) (-1) 0 GlobalTheory.CoordToExt.isGen_one
    (fun U _ f => by
      simp only [tφ, tε, h1, h2, Fin.prod_univ_five, Fin.prod_univ_two, Fintype.prod_sum_type,
        Sum.elim_inl, Sum.elim_inr, Category.id_comp, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]
      simp
      group)
  refine ⟨d, fun Z x z J hJ => ?_⟩
  have k0 : gs x z ⊤ (0 : Γ(D.P.A.left, ⊤)) = 0 := by
    rw [gs_eq x z ⊤ (by simp)]
    first
      | (rw [map_zero, map_zero]; done)
      | simp [map_zero]
  have k1 : gs x z ⊤ (-1 : Γ(D.P.A.left, ⊤)) = -1 := by
    rw [gs_eq x z ⊤ (by simp)]
    first
      | (rw [map_neg, map_one, map_neg, map_one]; done)
      | simp [map_neg, map_one]
  rw [hd Z x z J hJ, val_one, k0, k1, Category.comp_id]
  simp

theorem exists_terms : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])), ∃ (s₀ : SecT D.toPre a N (-1) 0) (s : ∀ ν, SecT D.toPre a N (-1) (shift h h' N (-1) ν)), (∀ ν, TRel h ν s₀ (s ν)) ∧ Small (maximalIdeal R) s ∧ (∀ ν, ν ≠ 0 → Van (maximalIdeal R) (s ν) 0) ∧ (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (s 0) x z J = sval σ₀ x z J) := by
  intro R _ _ _ hB D a a' h h' hE N hN hP σ₀
  obtain ⟨r, g, hg, hr, hfin, hval⟩ := GlobalTheory.MumInt.main R hB D a a' h h' hE N hN hP
  obtain ⟨s₀, hs₀⟩ := exists_secT_weight_zero R D.toPre a N σ₀ 0 rfl
  have h0 : shift h h' (N : ℤ) (-1) (0 : D.toPre.X) = 0 := by simp [shift]
  obtain ⟨z₀, hz₀⟩ := exists_secT_weight_zero R D.toPre a N σ₀ _ h0
  have key : ∀ ν, ∃ t : SecT D.toPre a N (-1) (shift h h' N (-1) ν), TRel h ν s₀ t ∧
      ∀ e : ℕ, r ν ∈ maximalIdeal R ^ (e + 1) → Van (maximalIdeal R) t e := by
    intro ν
    obtain ⟨u₀, hu₀, hfac⟩ := GlobalTheory.T.exists_normalised_twistedGenerator_of_factor R hB D a a' h h' hE N hN r g hg hval ν
    exact GlobalTheory.T.exists_mumfordTerm_translate_normalisedGenerator R D a h h' N s₀ ν u₀ hu₀ (r ν) hfac
  choose t ht using key
  have hz : TRel h 0 s₀ z₀ :=
    GlobalTheory.T.twisted_section_related_at_zero_shift R hB D a a' h h' hE N hN s₀ z₀ fun Z x z J hJ => (hz₀ Z x z J hJ).trans (hs₀ Z x z J hJ).symm
  classical
  let s : ∀ ν, SecT D.toPre a N (-1) (shift h h' N (-1) ν) := fun ν =>
    if hν : ν = 0 then hν.symm ▸ z₀ else t ν
  have hs0 : s 0 = z₀ := dif_pos rfl
  have hsν : ∀ ν, ν ≠ 0 → s ν = t ν := fun ν hν => dif_neg hν
  refine ⟨s₀, s, fun ν => ?_, fun e => ?_, fun ν hν => ?_, fun Z x z J hJ => ?_⟩
  · by_cases hν : ν = 0
    · subst hν
      rw [hs0]
      exact hz
    · rw [hsν ν hν]
      exact (ht ν).1
  · refine ((hfin (e + 1)).insert 0).subset fun ν hν => ?_
    by_cases h0' : ν = 0
    · exact Or.inl h0'
    · refine Or.inr fun hm => hν ?_
      rw [hsν ν h0']
      exact (ht ν).2 e hm
  · rw [hsν ν hν]
    exact (ht ν).2 0 (by rw [zero_add, pow_one]; exact hr ν hν)
  · rw [hs0]
    exact hz₀ Z x z J hJ

end GlobalTheory.TwFam

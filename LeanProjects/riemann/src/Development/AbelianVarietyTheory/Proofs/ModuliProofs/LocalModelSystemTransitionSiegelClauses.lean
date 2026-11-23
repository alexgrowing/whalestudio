import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoprimeLevelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMonoStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelStructureConditionsAndSplitFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelsSiegelFamilyComparisonStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTransitionMapRaisedModelsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

section Incl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H} {c : Coeff l}
  {c₂ : Coeff l₂} {W : ValuationSubring ℂ}

theorem exists_isIncl (hc : c.F ≤ c₂.F) : ∃ b : c.V W →+* c₂.V W, IsIncl b := by
  refine ⟨RingHom.codRestrict ((IntermediateField.inclusion hc).toRingHom.comp (c.V W).subtype) (c₂.V W)
    (fun x => x.2), fun x => rfl⟩

theorem isIncl_unique {b b' : c.V W →+* c₂.V W} (hb : IsIncl b) (hb' : IsIncl b') : b = b' := by
  refine RingHom.ext fun x => Subtype.ext (Subtype.ext ?_)
  exact (hb x).trans (hb' x).symm

end Incl

theorem system_clauses : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW, N2 (S.Y p W hp hW) := by
  intro hext L1 L2 L3 E _ _ _ H D Xo hD hN S p W hp hW
  refine ⟨fun i => (GlobalTheory.T.localModel_oneModel_and_splitFibres hext L1 L2 L3 E H D Xo hD hN S p W hp hW i).1, ?_⟩
  obtain ⟨hnp, hodd, h3, h4⟩ := S.aux (S.ch p)
  have hcop := (GlobalTheory.T.exists_two_inert_odd_primes_coprime_level E H).2 _ (S.aux (S.ch p))
  obtain ⟨-, hl2, hl3⟩ := GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp
  have key : ∀ i i₂ : Idx H p, i.l.Dvd i₂.l → i.c.F ≤ i₂.c.F →
      ∃ π : (S.Y p W hp hW i₂).X ⟶ (S.Y p W hp hW i).X, ∀ b : i.c.V W →+* i₂.c.V W, IsIncl b →
        IsTransition (S.Y p W hp hW i) (S.Y p W hp hW i₂) b π := by
    intro i i₂ hl hc
    obtain ⟨b, hb⟩ := exists_isIncl (W := W) hc
    obtain ⟨l₀, h₀, hr⟩ := S.raises p W hp hW i
    obtain ⟨l₀', h₀', hr'⟩ := S.raises p W hp hW i₂
    obtain ⟨π, hπ⟩ := GlobalTheory.T.exists_transition_map_raised_models hext L1 L2 L3 E H D Xo _ _ (S.T (S.ch p)) hN l₀ l₀' _ _ i.l i.c _ _
      (S.Y p W hp hW i) i₂.l i₂.c _ _ (S.Y p W hp hW i₂) b hnp.pos ⟨_, dvd_rfl⟩ (hl3 _ _ _ _ h₀ h₀' hl)
      (hl2 _ _ h₀).1 (hl2 _ _ h₀').1 hl hc ((GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H i.l i.c).2.2.2 p W hp hW).1
      ((GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H i₂.l i₂.c).2.2.2 p W hp hW).1 hb hr hr'
    exact ⟨π, fun b' hb' => isIncl_unique hb hb' ▸ hπ⟩
  choose π hπ using key
  obtain ⟨Ag, hAg⟩ := GlobalTheory.T.cm_models_siegel_family_comparison L1 L2 L3 E H D Xo _ _ (S.T (S.ch p)) hN p hp (S.ch_ne p).symm hnp ⟨_, rfl⟩
  refine ⟨π, hπ, S.n (S.ch p), S.J (S.ch p), Ag, hnp, hodd, S.ch_ne p, ?_, hcop, ?_⟩
  · have h2 : 3 ≤ S.n (S.ch p) := by
      have := hnp.two_le
      obtain ⟨k, hk⟩ := hodd
      omega
    exact h2.trans (Nat.le_self_pow (by have := S.J_pos (S.ch p); omega) _)
  · intro i i₁ hl hc b z hb hz hM hMb hA hF
    obtain ⟨l₀, h₀, hr⟩ := S.raises p W hp hW i
    obtain ⟨l₀', h₀', hr'⟩ := S.raises p W hp hW i₁
    have h₁ : IsPrimeToPart l₀' i.l p := by
      obtain ⟨a1, a2, a3⟩ := h₀'
      exact ⟨a1, hM ▸ a2, hMb ▸ a3⟩
    obtain rfl : l₀' = l₀ := (hl2 _ _ h₀).2.2 _ h₁
    exact hAg W l₀' _ i.l i₁.l i.c i₁.c _ _ b z _ hW h₀ (hcop _) hb hz hM hMb hA hF hr hr' (hπ i i₁ hl hc b hb)

end GlobalTheory.Models

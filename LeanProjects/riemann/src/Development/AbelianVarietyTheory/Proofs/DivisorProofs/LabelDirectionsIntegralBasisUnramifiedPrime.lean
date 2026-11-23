import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingReducedResidueFieldBijectiveUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDualFormsOfSeparatedTypes
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralTypesAndDirections
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.FlatGenInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigDirInt

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.PrimePart

theorem exists_integral_inverse_lieVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), UnramIn E p → ∀ [DecidableEq (Lt1 Dw)], ∃ L : Matrix (Lt1 Dw) (Fin (chD Ch.ch)) X.C, (∀ a b, IsIntV (vX_vp X) (L a b)) ∧ L * (Matrix.of fun e ℓ => lieVec Ch X ℓ e) = 1 ∧ (Matrix.of fun e ℓ => lieVec Ch X ℓ e) * L = 1 := by
  intro E _ _ _ H Dw l Xo c _ p _ T io X y Ch hp inst
  have hbij := GlobalTheory.T.embeddingReducedResidueField_bijective_unramified E H l c p T io X hp
  choose σV hσV using fun τ : E →+* ℂ =>
    GlobalTheory.PowGerm.exists_lift_ringOfIntegers (V := T.V) (io.comp (embK c τ))
  have hσV' : ∀ τ a, algebraMap T.V T.Fr (σV τ a) = io (embK c τ a) := hσV
  have hι : ∀ τ a, X.ι (σV τ a) = embO io X τ a := fun τ a => X.ints.hom_inj (by
    rw [algebraMap_embO, ← X.comp, hσV']; rfl)
  have hsep : ∀ τ τ' : E →+* ℂ, τ ≠ τ' → ∃ a, IsUnit (σV τ a - σV τ' a) := by
    intro τ τ' hne
    have h1 : red io X τ ≠ red io X τ' := fun h => hne (hbij.1 h)
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 h1
    refine ⟨a, ?_⟩
    have := X.ι_local
    refine (isUnit_map_iff X.ι _).1 ?_
    rw [map_sub, hι, hι]
    by_contra hu
    apply ha
    rw [← sub_eq_zero]
    show residue X.O _ - residue X.O _ = 0
    rw [← map_sub, residue_eq_zero_iff]
    exact (mem_maximalIdeal _).2 hu
  have hex : ∃ lam : Lt1 Dw → Fin (chD Ch.ch) → T.V, ∀ l l', ∑ s, lam l s * Ch.uvecT l' s = if l = l' then 1 else 0 := by
    classical
    obtain ⟨lam, hlam⟩ := GlobalTheory.exists_dual_forms_of_separated_types T.V (𝓞 E) (chD Ch.ch)
      (fun a => Matrix.of fun m j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Ch.actT a m))
      (E →+* ℂ) Dw.mult (fun τ a => σV τ a) Ch.uvecT hsep
      (fun a ℓ => ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.eigDir_int Xo c T io y Ch ℓ a _ (hσV' _ _)) (fun τ => by
        obtain ⟨⟨w, emb, hw, hb⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y Ch τ
        exact GlobalTheory.PowGerm.exists_dual_of_extends (fun i => Ch.uvecT ⟨τ, i⟩) w emb hw hb)
    exact ⟨lam, fun l l' => by convert hlam l l'⟩
  obtain ⟨lam, hlam⟩ := hex
  have h1 : (Matrix.of fun ℓ e => jX X (lam ℓ e)) * (Matrix.of fun e ℓ => lieVec Ch X ℓ e) = 1 := by
    ext ℓ ℓ'
    have h := congrArg (jX X) (hlam ℓ ℓ')
    rw [map_sum] at h
    simp only [map_mul] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply, lieVec]
    rw [h]
    split_ifs
    · exact map_one _
    · exact map_zero _
  refine ⟨Matrix.of fun ℓ e => jX X (lam ℓ e), fun a b => isIntV_jX X _, h1, ?_⟩
  have e : Lt1 Dw ≃ Fin (chD Ch.ch) := Fintype.equivFinOfCardEq (GlobalTheory.IntChartCheck.dim_eq Ch).symm
  exact (Matrix.mul_eq_one_comm_of_equiv e).1 h1

end GlobalTheory.PrimePart

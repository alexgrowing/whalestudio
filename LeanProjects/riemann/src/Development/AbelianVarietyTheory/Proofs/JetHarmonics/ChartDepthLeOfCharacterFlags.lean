import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharacterGermValuationEqColumnTypedStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartLocalDepthLeOfValuedExtensionBoundStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmTypeDirectionsEigenbasisValuedIntegersStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalBiextensionIntegralChartValuedExtensStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValuationBlockPolynomialGeProdStatement

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem crP_map_ringHom {Ty : Type} [Fintype Ty] [DecidableEq Ty] (r : Ty → ℕ) (n : ℕ) {R S : Type} [CommRing R]
    [CommRing S] (φ : R →+* S) (β : (Σ σ : Ty, Fin (r σ)) → Fin n) (a : Ty → ℕ → ℕ) :
    MvPolynomial.map φ (Crude.crP r n R β a) = Crude.crP r n S β a := by
  rw [← Crude.crP_map R, ← Crude.crP_map S, MvPolynomial.map_map]
  congr 2
  exact RingHom.ext_int _ _

theorem exists_col_extend {ι κ α : Type} (β : ι → κ) (hβ : Function.Injective β) (g : ι → α) (x : α) :
    ∃ G : κ → α, (∀ i, G (β i) = g i) ∧ ∀ b, G b = x ∨ ∃ i, G b = g i := by
  classical
  refine ⟨Function.extend β g (fun _ => x), fun i => hβ.extend_apply _ _ _, fun b => ?_⟩
  by_cases hb : ∃ i, β i = b
  · obtain ⟨i, rfl⟩ := hb
    exact Or.inr ⟨i, hβ.extend_apply _ _ _⟩
  · exact Or.inl (Function.extend_apply' _ _ _ hb)

theorem nuLocC_le_of_character_flags : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (τO : (E →+* ℂ) → (𝓞 E →+* X.O)), IsTypes X io τO → (∀ τ, ∃ a0, IsUnit (τO τ a0 - τO τ (star a0))) → (∀ x : X.O, x ≠ 0 → ∃ N : ℕ, X.v (N : X.C) < X.v (algebraMap X.O X.C x) ∧ ∀ τ, ∃ a : 𝓞 E, star a * a = (N : 𝓞 E) ∧ X.v (algebraMap X.O X.C (τO τ a - 1)) < X.v (algebraMap X.O X.C x)) → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ (len : (E →+* ℂ) → ℝ), (∀ τ, 0 ≤ len τ) → (∀ τ, ∃ χ : Fin (Dw.mult τ) → PS X.O 1 (chD Ch.ch), (∀ b, IsCh (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (χ b)) ∧ ∀ i : Fin (Dw.mult τ), (X.v (p : X.C) : ℝ) ^ len τ ≤ (X.v (algebraMap X.O X.C (Matrix.of fun s b : Fin (i.val + 1) => ∑ j, X.ι (Ch.uvecT ⟨τ, Fin.castLE i.isLt s⟩ j) * dl (χ (Fin.castLE i.isLt b)) j).det) : ℝ)) → nuLocC Ch e k a n ≤ (((vV T.V (p : T.Fr) : ℝ) / (e : ℝ) * ∑ τ, len τ * (a (τ, 0) : ℝ) : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch p _ X τO hty hun happ e k n a he ha hn len hlen hχ
  classical
  obtain ⟨B, hF, hact, hg⟩ := GlobalTheory.T.exists_formalBiextension_integral_chart_valuedExtension E H Dw l Xo c T io y Ch p X
  choose χ hχ1 hχ2 using hχ
  have hβ : Function.Injective (colP Dw hn) := fun p q h =>
    (Fintype.equivFin _).injective (Fin.castLE_injective hn h)
  obtain ⟨ty, hty1, -⟩ := exists_col_extend (colP Dw hn) hβ (fun q : Lt1 Dw => q.1) (Classical.arbitrary _)
  obtain ⟨χ', hχ'1, hχ'2⟩ := exists_col_extend (colP Dw hn) hβ (fun q : Lt1 Dw => χ q.1 q.2) 1
  have hp0 : X.v (p : X.C) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hp1 : X.v (p : X.C) ≤ 1 := by
    have := X.ints.map_le_one (p : X.O)
    rwa [map_natCast] at this
  obtain ⟨hval, hsupp⟩ := GlobalTheory.T.valuation_blockPolynomial_ge_prod X.C X.v X.O X.ints (E →+* ℂ) Dw.mult n (colP Dw hn) hβ
    (fun τ i => a (τ, i)) ha
    (fun ℓ : LtN Dw n => ∑ j, X.ι (Ch.uvecT ⟨ℓ.1, ℓ.2.1⟩ j) * dl (χ' ℓ.2.2) j)
    (fun τ => X.v (p : X.C) ^ len τ) (fun τ => NNReal.rpow_le_one hp1 (hlen τ))
    (fun τ i => by
      have h := hχ2 τ i
      rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
      simp only [hχ'1]
      exact h)
  have hprod : ∏ τ, (X.v (p : X.C) ^ len τ) ^ (a (τ, 0)) =
      X.v (p : X.C) ^ (∑ τ, len τ * (a (τ, 0) : ℝ)) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_rpow, Real.rpow_sum_of_pos (by exact_mod_cast pos_iff_ne_zero.2 hp0), NNReal.coe_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [NNReal.coe_pow, NNReal.coe_rpow, Real.rpow_mul_natCast (NNReal.coe_nonneg _)]
  rw [hprod] at hval
  have hne : MvPolynomial.eval
      (fun ℓ : LtN Dw n => ∑ j, X.ι (Ch.uvecT ⟨ℓ.1, ℓ.2.1⟩ j) * dl (χ' ℓ.2.2) j)
      (Crude.crP Dw.mult n X.O (colP Dw hn) (fun τ i => a (τ, i))) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hval
    exact absurd hval (not_le.2 (NNReal.rpow_pos (pos_iff_ne_zero.2 hp0)))
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_characterGerm_valuation_eq_columnTyped X.C X.v X.O X.ints (chD Ch.ch) (𝓞 E) B _ hg H.w0 k n (E →+* ℂ) Dw.mult τO
    (fun q j => X.ι (Ch.uvecT q j))
    (fun q a0 => by
      rw [hact]
      exact (GlobalTheory.T.cmTypeDirections_eigenbasis_valuedIntegers E H Dw l Xo c T io y Ch p X τO hty q.1).1.1 q.2 a0)
    hun happ ty (Crude.crP Dw.mult n X.O (colP Dw hn) (fun τ i => a (τ, i)))
    (fun mo hmo ℓ hℓ => by
      obtain ⟨i, hi⟩ := hsupp mo hmo ℓ hℓ
      rw [← hi, hty1])
    χ'
    (fun b => by
      rw [hF]
      rcases hχ'2 b with h | ⟨q, h⟩
      · rw [h]
        exact ⟨by simp, by simp⟩
      · rw [h]
        exact hχ1 q.1 q.2)
    hne
  refine GlobalTheory.T.chart_local_depth_le_of_valuedExtension_bound E H Dw l Xo c T io y Ch p X B hF hact e k n a he
    (Crude.crP Dw.mult n X.O (colP Dw hn) (fun τ i => a (τ, i))) ?_ f _ ?_
  · rw [crP_map_ringHom, ← Crude.crP_map]
    exact (Crude.Pmin_mem Dw.mult n X.C (colP Dw hn) _ ⊤ _ _ (fun τ _ => conj_ne_self_of_CM τ) hβ ha).1
  · rw [← NNReal.coe_rpow, NNReal.coe_le_coe]
    exact hval.trans (le_of_eq hf.symm)

end GlobalTheory.CharDepth

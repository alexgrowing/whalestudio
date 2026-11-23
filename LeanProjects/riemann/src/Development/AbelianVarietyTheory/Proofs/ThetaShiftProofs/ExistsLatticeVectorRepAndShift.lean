import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpAdditiveSurjectiveLinearStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpKernelIotaTorusPointsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.GtRep

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem exists_rep_and_shift : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (k : ℕ), 1 ≤ k → (∀ p, ∃ la, Λ.Rep k p la) ∧ ∀ p la e, Λ.Rep k p la → ∃ q : Out.QkPt a.D₀ ℂ k, q.y = Λ.ε (la + k • e).y ∧ q.g = Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 (la + k • e)) ∧ ∀ q', QkExt (algebraMap _ ℂ) p q' → Out.QkPt.Equiv a.D₀ ℂ q q' := by
  intro h1 h2 E _ _ _ H _ D l c O _ β _ _ b a Λ k hk
  obtain ⟨hadd, hsurj, -⟩ := GlobalTheory.T.analyticDictionaryExp_additive_surjective_linear h1 h2 E H D l c O β b a Λ
  obtain ⟨hker, hio, -⟩ := GlobalTheory.T.analyticDictionaryExp_kernel_iota_torusPoints E H D l c O β b a Λ
  have hB := a.bimult
  let ex : Λ.A.V →+ Out.GtPtF a.D₀ ℂ :=
    AddMonoidHom.mk' Λ.ex0 fun z z' => (isAdd_iff_eq _ _ _).1 (hadd z z')
  have hex : ∀ z, Λ.ex0 z = ex z := fun _ => rfl
  have hio' : ∀ la : Λ.A.La, ex (Λ.A.P0 la) = iota hB ℂ (Λ.ε la.y) := fun la => (isIota_iff_eq hB _ _).1 (hio la)
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hf : (algebraMap (FractionRing ℂ) ℂ).comp (algebraMap (FractionRing ℂ) (FractionRing ℂ)) =
      algebraMap (FractionRing ℂ) ℂ := RingHom.ext fun _ => rfl
  have hkk : ∀ v : Λ.A.V, (k : ℂ)⁻¹ • k • v = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk0]
  have hkk' : ∀ v : Λ.A.V, k • (k : ℂ)⁻¹ • v = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk0]
  refine ⟨fun p => ?_, fun p la e hrep => ?_⟩
  · obtain ⟨q, -, huniq⟩ := existsUnique_qkExt hB _ hf p
    obtain ⟨z, hz⟩ := hsurj q.g
    let l0 : Λ.A.La := AnArc.La.mk (Λ.ε.symm q.y) 0 0
    have hl0 : Λ.ε l0.y = q.y := Λ.ε.apply_symm_apply _
    have hzero : (Λ.ex0 (k • z - Λ.A.P0 l0)).IsZero := by
      rw [isZero_iff_eq, hex, map_sub, map_nsmul, ← hex z, hz, qk_nsmul hB, hio', hl0, sub_self]
    obtain ⟨l1, hl1, hl1'⟩ := (hker _).1 hzero
    refine ⟨l1 + l0, fun q' hq' => ?_⟩
    obtain rfl := huniq q' hq'
    refine ⟨by rw [AnArc.La.add_y, hl1, zero_add, hl0], ?_⟩
    rw [map_add, ← hl1', sub_add_cancel, hkk, hz]
  · refine ⟨qkMk hB (Λ.ε (la + k • e).y) (Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 (la + k • e)))
      (by rw [hex, ← map_nsmul, hkk', hio']), rfl, rfl, fun q' hq' => ?_⟩
    obtain ⟨hy, hg⟩ := hrep q' hq'
    refine equiv_symm hB ((equiv_iff hB _ _).2 ⟨Λ.ε e.y, ?_, ?_⟩)
    · rw [qkMk_y, hy, AnArc.La.add_y, AnArc.La.nsmul_y, map_add, map_nsmul]
    · rw [qkMk_g, hg, hex, hex, map_add, map_nsmul, smul_add, hkk, map_add, hio']

end GlobalTheory.GtRep

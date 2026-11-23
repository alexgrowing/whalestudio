import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsIntegralDiscrMulOfTraceInt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLamLettersIsGood
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLamObjGoodOfCmObj
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignatureStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsSplit
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcPointTangentPart
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangent
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.DimPosOfHasType

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcCM.Letters

theorem exists_scaled {R : Type} [CommRing R] [IsDomain R] {D₀ : Out.DegPre R} {n : ℕ}
    {sB : ∀ T : Over (Sp R), (T ⟶ D₀.P.A) → Out.GtPt D₀ T} (h : IsSplit D₀ n sB) (r : R) {w : epsR R ⟶ D₀.P.A}
    (hw : IsTangent w) : ∃ ν, GtTanR ν ∧ Out.GtPt.IsPull (spMap (epsScaleR r)) (sB (epsR R) w) ν := by
  let sc : epsR R ⟶ epsR R := Over.homMk (spMap (epsScaleR r)) (by
    show spMap (epsScaleR r) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R))
    rw [spMap_comp_spMap]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])
  let z : Over.mk (𝟙 (Sp R)) ⟶ epsR R := Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (by
    show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _
    rw [spMap_comp_spMap]
    have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]
    exact Spec.map_id (CommRingCat.of R))
  have hz : z ≫ sc ≫ w = 1 := by
    apply Over.OverMorphism.ext
    have e : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (epsScaleR r) =
        spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
      rw [spMap_comp_spMap]
      congr 1
      ext a <;> simp [epsScaleR]
    show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (epsScaleR r) ≫ w.left = _
    rw [← Category.assoc, e, hw]
    exact (Category.id_comp _).symm
  refine ⟨sB _ (sc ≫ w), ⟨sB _ 1, TanPart.isZero_of_isAdd (by simpa using h.2.1 _ 1 1), ?_⟩, h.2.2 _ _ sc w⟩
  have := h.2.2 _ _ z (sc ≫ w)
  rwa [hz] at this

theorem exists_kind {I J : Type} (N m : I → ℕ) (h : ∀ τ, N τ = m τ + 1) (e : (Σ b, Fin (m b)) ≃ J) :
    ∃ kind : ∀ τ, Fin (N τ) → Option J, ∀ τ, Function.Injective (kind τ) ∧ (∃ k, kind τ k = none) ∧
      ∀ j, (∃ k, kind τ k = some j) ↔ (e.symm j).1 = τ := by
  let u : ∀ τ, Fin (N τ) ≃ Option (Fin (m τ)) := fun τ => (finCongr (h τ)).trans (finSuccEquiv _)
  refine ⟨fun τ k => (u τ k).map fun i => e ⟨τ, i⟩, fun τ => ⟨?_, ⟨(u τ).symm none, by simp⟩, fun j => ⟨?_, ?_⟩⟩⟩
  · exact (Option.map_injective (e.injective.comp sigma_mk_injective)).comp (u τ).injective
  · rintro ⟨k, hk⟩
    obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 hk
    simp
  · rintro rfl
    exact ⟨(u _).symm (some (e.symm j).2), by simp⟩

theorem exists_section (hT : Out.SecTwistSt) {K : Type} [Field K] (P : Out.PolAV (Sp K)) :
    ∃ th : P.L.Sec, ∀ s : Sp K, ∃ x : P.A.left, P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th := by
  obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section hT P
  obtain ⟨a, -, hu⟩ := hb b
  refine ⟨b, KeyPow.exists_mem_nonzeroLocus _ b ?_⟩
  by_contra hn
  push Not at hn
  exact zero_ne_one ((hu 0 fun i => by rw [hn i, mul_zero]).trans (hu 1 fun i => by rw [hn i, mul_zero]).symm)

theorem exists_cmIn : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (ρ : 𝓞 K₁) (σ₁ : K₁ →+* ℂ) (X : GlobalTheory.CM.CMObj H K₁ ρ σ₁ (Dw.p - 1) (Dw.q - 1)) (ψ : a.D₀.P.A.left ⟶ X.B.pol.A.left) (n' : ℕ) (La c₁ : ℝ) (ξ : Module.Dual ℤ a.D₀.X) (ν₀ : E) (jj : ℤ), letI := H.starRing; 1 ≤ Dw.p → 1 ≤ Dw.q → 3 ≤ Dw.p + Dw.q → σ₁.comp (algebraMap c.F K₁) = c.F.val.toRingHom → σ₁ (ρ : K₁) = H.rt0 → (∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) → IsPolFibre (algebraMap (𝓞 K₁) K₁) X.B.pol a.D₀.P ψ → (∀ x, (a.oa.onB.act x).left ≫ ψ = ψ ≫ (X.B.t.act.act x).left) → 0 < n' → TauCan a.D₀ n' → Module.finrank (𝓞 E) a.D₀.X = 1 → ξ ≠ 0 → BetaAt ξ l.M' a.be ν₀ jj → ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) / 2 ≤ c₁ → ∃ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (s : CMIn a e th jj n' La c₁), s.ξ = ξ ∧ s.ν₀ = ν₀ := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a ρ σ₁ X ψ n' La c₁ ξ ν₀ jj hp hq hpq hσ hρ hLa hψ hact hn hτ hrk hξ hβ htr
  letI := H.starRing
  obtain ⟨th, hth⟩ := exists_section hK.laws2.secTwist a.D₀.P
  obtain ⟨v, hv⟩ := KeyPow.exists_isLieBasis a.D₀.P.A a.D₀.P.smoothDim
  have hf : 0 < Module.finrank ℚ E / 2 := by
    have e := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at e
    have : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  have gB : X.B.g = Module.finrank ℚ E / 2 * (Dw.p - 1 + (Dw.q - 1)) :=
    (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K₁ ρ X.B ⟨a.D₀.P, ψ, hψ, v, hv⟩ _ _ X.split X.typeB X.ρ_sq).2.2.2.1
  have hg : 1 ≤ a.D₀.P.g := by
    rw [hψ.1]
    show 1 ≤ X.B.g
    rw [gB]
    exact Nat.mul_pos hf (by omega)
  have hlab : ∀ τ, τ ∈ psiSet H ↔ labK c K₁ τ (H.rt : E) = (ρ : K₁) := fun τ => by
    have e : σ₁ (labK c K₁ τ (H.rt : E)) = τ (H.rt : E) := RingHom.congr_fun hσ (embF c τ (H.rt : E))
    rw [← σ₁.injective.eq_iff, e, hρ]
    rfl
  let xB : KeyIn K₁ := ⟨a.D₀.P, hg, a.D₀.rig, a.D₀.rig_gen, th, hth, v, hv⟩
  obtain ⟨oa, oaΨ, oa', xΨ, x', φΨ, φ', τΨ, τ', ℓΨ, ℓ', Tl, LamL, hoa, -, -, hgood⟩ :=
    exists_lamObjGood_of_cmObj hK.laws2.secTwist hK.theta hK.laws hK.hom E H l c (fun _ => rfl) K₁ ρ σ₁ _ _ X La hlab
      hLa xB ψ ((isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K₁) K₁) X.B.pol xB ψ).2 hψ)
  obtain ⟨L, hL, hm⟩ := exists_lamLetters_isGood E H l c _ _ _ _ La hgood
  obtain ⟨kind, hkind⟩ := exists_kind Dw.mult L.m (fun τ => by
    unfold Datum.mult
    split_ifs with h
    · rw [(hm τ).1 h]; omega
    · rw [(hm τ).2 h]; omega) L.e
  obtain ⟨sB, hsB⟩ := GlobalTheory.ArcCM.exists_isSplit hK K₁ a.D₀ n' hn hτ.1
  have tor : ∀ τ : E →+* ℂ, ∃ ν : Out.GtPt a.D₀ (epsR K₁), GtTanR ν ∧ ν.b = Out.DegPre.zeroT a.D₀ (epsR K₁) ∧
      ∀ x, DlogTan ν x (labK c K₁ τ (cc (pairE ξ x))) := fun τ =>
    ((GlobalTheory.TorusTangent.main hK.laws.globalFns K₁ a.D₀).1 (AddMonoidHom.mk' (fun x => labK c K₁ τ (cc (pairE ξ x)))
      fun x y => by rw [(pairE_properties E a.D₀.X ξ).2.1, cc, map_add, map_add]; rfl)).exists
  have ab : ∀ m : Fin a.D₀.P.g, ∃ ν : Out.GtPt a.D₀ (epsR K₁), GtTanR ν ∧ ∃ w : epsR K₁ ⟶ a.D₀.P.A, L.IsLetter m w ∧
      Out.GtPt.IsPull (spMap (epsScaleR ((n' : K₁)⁻¹))) (sB (epsR K₁) w) ν := fun m => by
    obtain ⟨w, hw, hc⟩ := hL.2.2.1 m
    obtain ⟨ν, h₁, h₂⟩ := exists_scaled hsB ((n' : K₁)⁻¹) (w := w) (GlobalTheory.Reg.isTangent_of_isLieComb hv.1 hc)
    exact ⟨ν, h₁, w, hw, h₂⟩
  choose et het using tor
  choose ea hea using ab
  refine ⟨fun τ k => (kind τ k).elim (et τ) ea, th,
    { B := X.B.pol, oa := oa, AΨ := (X.A true).pol, oaΨ := oaΨ, A' := (X.A false).pol, oa' := oa'
      φΨ := fun i => X.φ (Sum.inl i), φ' := fun i => X.φ (Sum.inr i)
      hΨ := fun i => X.hh (Sum.inl i), h' := fun i => X.hh (Sum.inr i)
      g_pos := hg, th_nz := hth, v := v, basis := hv, xΨ := xΨ, x' := x', φB := ψ, φΨg := φΨ, φ'g := φ'
      τΨ := τΨ, τ' := τ', ℓΨ := ℓΨ, ℓ' := ℓ', Tl := Tl, LamL := LamL
      good := hgood, act := fun x => by rw [hoa]; exact hact x
      L := L, L_good := hL, n_pos := hn, tau := hτ, sB := sB, split := hsB, rk := hrk, ξ := ξ, ξ_ne := hξ
      ν₀ := ν₀, beta := hβ, tr := htr, kind := kind, full := hkind
      tan := fun τ k => ?_, xi := fun τ k h => ?_, eta := fun τ k m h => ?_ }, rfl, rfl⟩
  · cases kind τ k with
    | none => exact (het τ).1
    | some m => exact (hea m).1
  · rw [h]; exact (het τ).2
  · rw [h]; exact (hea m).2

end GlobalTheory.ArcCM.Letters

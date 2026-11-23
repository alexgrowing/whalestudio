import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsoOfSamePeriodMatrixLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FibreAtPeriod

section Reparam

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left}

theorem exists_reparam_isAH {g g' : ℕ} (u : HolUnif A L g') (X : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ))
    (Hm : Matrix (Fin g') (Fin g') ℂ) (Hf : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (hAH : u.IsAH Hm χ)
    (hHf : Hf.IsHermitian) (hf : ∀ x y, hermForm Hf x y = hermForm Hm (X x) (X y)) :
    ∃ (u₂ : HolUnif A L g) (χ₂ : u₂.Λ → ℂ), (∀ z, u₂.ex z = u.ex (X z)) ∧ (∀ z, z ∈ u₂.Λ ↔ X z ∈ u.Λ) ∧
      u₂.IsAH Hf χ₂ ∧ ∀ w v, u.IsDiff (X w) v → u₂.IsDiff w v := by
  have hg : g = g' := by simpa using X.finrank_eq
  subst hg
  refine ⟨GlobalTheory.holUnifReparam u X (fun _ => 1) (differentiable_const _) (fun _ => one_ne_zero),
    fun l => χ ⟨X l, l.2⟩, fun _ => rfl, fun _ => Iff.rfl, ⟨hHf, ?_, fun l => hAH.2.2.1 _, ?_⟩, ?_⟩
  · intro z hz
    have h := hAH.2.1 (X z) ((LinearEquiv.map_ne_zero_iff X).2 hz)
    have e := hf z z
    unfold hermForm at e
    rw [e]
    exact h
  · intro l i z hz
    have h := hAH.2.2.2 ⟨X l, l.2⟩ i (X z) hz
    have e1 := hf z l
    have e2 := hf l l
    unfold hermForm at e1 e2
    show u.fr i (X z) / 1 = χ ⟨X l, l.2⟩ * Complex.exp (Real.pi * (z ⬝ᵥ Hf.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hf.mulVec (star (l : Fin g → ℂ)))) * (u.fr i (X (z + l)) / 1)
    rw [div_one, div_one, map_add, h, e1, e2]
  · intro w v hv U h f
    rw [hv U h f]
    have key := X.toContinuousLinearEquiv.comp_right_fderiv
      (f := fun z => valAt' (u.ex z).left U f) (x := 0)
    have h2 := congrArg (fun T => T w) key
    simp only [map_zero] at h2
    exact h2.symm

end Reparam

theorem fibreLatVec_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (R : RiemLat E g (FU.Di i).La) (P : (FU.Di i).La →+ (Fin g → ℂ)) (h : Matrix (Fin g) (Fin g) ℂ), IsPeriod (FU.Di i) ty P → R.form = (FU.Di i).EF → IsUnit h.det → (∀ x, P x = h *ᵥ R.P x) → ∀ (A₀ : Type) (x : A₀ → Fin g → ℂ) (v : A₀ → (epsAt (FU.u i P) ⟶ Xo.univ.t.G)), (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (h *ᵥ x a) (v a).left) → FibreLatVec Xo.univ.t (FU.u i P) R x v := by
  intro E _ _ _ H D l Xo σ g ty FU i R P h hP hRf hdet hPh A₀ x v hd
  let hl : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := h.toLinearEquiv' (h.invertibleOfIsUnitDet hdet)
  have hla : ∀ z, hl z = h *ᵥ z := fun z => by
    show Matrix.toLin' h z = h *ᵥ z
    exact Matrix.toLin'_apply h z
  have hlP : ∀ a, hl (R.P a) = P a := fun a => by rw [hla, hPh]
  have hlP' : ∀ a, hl.symm (P a) = R.P a := fun a => by rw [← hlP, hl.symm_apply_apply]
  obtain ⟨Q, ψ, -, hQ, hQL, -⟩ := GlobalTheory.exists_polAV_pullback_of_isLocalRing E H _ Xo.univ.t Xo.univ.proper
    Xo.univ.ample Xo.univ.ktriv ℂ (FU.u i P)
  obtain ⟨u, H₂, χ, F, hAH, -, d₂, -, hF, hΛ, hE⟩ :=
    GlobalTheory.familyUnif_fibre_theta GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1.weil E H D l Xo σ g ty FU i P hP
      Q ψ hQ hQL
  obtain ⟨w, hw⟩ := hQL

  have hLB : (Xo.univ.t.PP.L.pull ψ).IsLB := LB.isLB_pull Xo.univ.t.PP.isLB ψ
  let ub : HolUnif Q.A (Xo.univ.t.PP.L.pull ψ) Q.g := GlobalTheory.ArchMetricCompare.carry u Q.isLB hLB hw
  have hAHb : ub.IsAH H₂ χ := GlobalTheory.ArchMetricCompare.carry_isAH Q.isLB hLB hw hAH
  let T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin Q.g → ℂ) := hl.trans F
  have hf : ∀ x y, hermForm R.Hm x y = hermForm H₂ (T x) (T y) := fun x y => by
    have key := GlobalTheory.KeyFam.SamePeriod.hermForm_eq_of_im H₂ F.toLinearMap R.Hm hl.symm.toLinearMap hP.2.2.2.1 (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      have h1 := hE a b
      have h2 := R.im a b
      rw [hRf] at h2
      show (hermForm H₂ (F (P a)) (F (P b))).im = (hermForm R.Hm (hl.symm (P a)) (hl.symm (P b))).im
      rw [hlP', hlP', h1]
      exact h2.symm) (hl x) (hl y)
    show _ = hermForm H₂ (F (hl x)) (F (hl y))
    simpa using key.symm
  obtain ⟨u', χ', hue, huΛ, huAH, hud⟩ := exists_reparam_isAH ub T H₂ R.Hm χ hAHb R.herm hf
  have hex : ∀ q, (u'.ex q).left ≫ ψ = (FU.ex i P (hl q)).left := fun q => by
    rw [hue]
    exact hF (hl q)

  have hB : ∀ (a : 𝓞 E) (p : Fin g → ℂ), hl (R.B a p) = fun k => ty k (a : E) * hl p k := fun a p => by
    let Da : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun z k => ty k (a : E) * z k
        map_add' := fun z z' => by
          ext k
          simp [mul_add]
        map_smul' := fun c z => by
          ext k
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          ring }
    let N : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      hl.toLinearMap.comp ((R.B a).comp hl.symm.toLinearMap) - Da
    have hN : N.restrictScalars ℝ = 0 := LinearMap.ext_on hP.2.2.2.1 (by
      rintro _ ⟨y, rfl⟩
      show hl (R.B a (hl.symm (P y))) - (fun k => ty k (a : E) * P y k) = 0
      rw [hlP', ← R.act, hlP, sub_eq_zero]
      exact funext (hP.1 a y))
    have h0 : N (hl p) = 0 := congrArg (fun f => f (hl p)) hN
    have h1 : hl (R.B a (hl.symm (hl p))) - (fun k => ty k (a : E) * hl p k) = 0 := h0
    rw [hl.symm_apply_apply] at h1
    exact sub_eq_zero.1 h1
  refine ⟨Q.A, inferInstance, ψ, u', χ', hQ, huAH, fun a p => ?_, fun y y' hy => ?_, fun p => ?_, fun a => ?_⟩
  · rw [hex, hB, FU.ex_lin i P hP a (hl p), Over.comp_left, ← Category.assoc, hex]
  · exact hP.2.1 (by rw [hPh, hPh, hy])
  · rw [huΛ]
    show F (hl p) ∈ u.Λ ↔ _
    rw [hΛ]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, hl.injective (by rw [hlP, hy])⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, (hlP y).symm⟩
  · have hd' : IsDerivAt0 (fun z => (FU.ex i P z).left) (hl (x a)) (v a).left := by
      rw [hla]
      exact hd a
    obtain ⟨t, ⟨h₁, h₂⟩, -⟩ := d₂ (F (hl (x a)))
    refine ⟨t, GlobalTheory.VerticalDeriv.isDerivAt0_unique
      (Flat.PerGram.isDerivAt0_of_fibre ψ u F.toLinearMap hF h₁ h₂) hd', hud (x a) t h₂⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.FibreAtPeriod

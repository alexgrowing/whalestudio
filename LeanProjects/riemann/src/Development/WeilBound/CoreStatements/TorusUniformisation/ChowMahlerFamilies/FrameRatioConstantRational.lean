import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFramesInvertibleChange
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FramedPointSpecialization
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MemOfFixedByAutomorphisms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace PositivityTheory.Xgn.FrameRatioConstant

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem ratio_frames {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ φ' : FrameFn Xo c} (h : IsLineFn U τ φ)
    (h' : IsLineFn U τ φ') {F : Type} [Field F] {β : c.F →+* F} {y : Sp F ⟶ Xo.XF c} {v v' : Vecs y D.p}
    {w w' : Vecs y D.q} (hf : IsFramed U τ β y v w) (hf' : IsFramed U τ β y v' w') {r : F}
    (hr : φ' F y v w = r * φ F y v w) : φ' F y v' w' = r * φ F y v' w' := by
  obtain ⟨-, A, hA, A', hA', -⟩ := GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange.eigFrame_change _ F Xo.univ.t.G (under y) _
    Xo.univ.t.act _ _ _ v v' hf.2.2.1 hf'.2.2.1
  obtain ⟨-, B, hB, -⟩ := GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange.eigFrame_change _ F Xo.univ.t.G (under y) _
    Xo.univ.t.act _ _ _ w w' hf.2.2.2 hf'.2.2.2
  have hd : A.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hA'
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have e := h.chg F β y v w v' w' A B hf hf' hA hB
  have e' := h'.chg F β y v w v' w' A B hf hf' hA hB
  apply mul_right_cancel₀ hd
  rw [e', hr, _root_.mul_assoc, _root_.mul_assoc, e]

theorem ratio_spec {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ φ' : FrameFn Xo c} {κ : ℂ} (h : IsLineFn U τ φ)
    (h' : IsLineFn U τ φ')
    (hκ : ∀ y v w, IsFramed U τ (algebraMap c.F ℂ) y v w → φ' ℂ y v w = κ * φ ℂ y v w)
    {F : Type} [Field F] {β : c.F →+* F} {y : Sp F ⟶ Xo.XF c} {v : Vecs y D.p}
    {w : Vecs y D.q} (hf : IsFramed U τ β y v w) :
    ∃ (k : Type) (_ : Field k) (β₀ : c.F →+* k) (f : k →+* F) (j : k →+* ℂ) (r : k), r ≠ 0 ∧ f.comp β₀ = β ∧
      j.comp β₀ = algebraMap c.F ℂ ∧ φ' F y v w = f r * φ F y v w ∧
      ∀ j' : k →+* ℂ, j'.comp β₀ = algebraMap c.F ℂ → j' r = κ := by
  obtain ⟨k, _, β₀, y₀, v₀, w₀, f, j, h₀, hβ, hj, rfl, up⟩ :=
    PositivityTheory.Xgn.framed_point_specialization E H D l Xo c U τ F β y v w hf
  have n0 := h.ne k β₀ y₀ v₀ w₀ h₀
  have n0' := h'.ne k β₀ y₀ v₀ w₀ h₀
  refine ⟨k, inferInstance, β₀, f, j, φ' k y₀ v₀ w₀ / φ k y₀ v₀ w₀, div_ne_zero n0' n0, hβ, hj, ?_, ?_⟩
  · obtain ⟨v', w', hf', ev, ew⟩ := up F f
    rw [hβ] at hf'
    refine ratio_frames h h' hf' hf ?_
    rw [h.nat k F f β₀ y₀ v₀ w₀ _ v' w' h₀ rfl ev ew, h'.nat k F f β₀ y₀ v₀ w₀ _ v' w' h₀ rfl ev ew, ← map_mul,
      div_mul_cancel₀ _ n0]
  · intro j' hj'
    obtain ⟨v', w', hf', ev, ew⟩ := up ℂ j'
    rw [hj'] at hf'
    have e := hκ _ v' w' hf'
    rw [h.nat k ℂ j' β₀ y₀ v₀ w₀ _ v' w' h₀ rfl ev ew, h'.nat k ℂ j' β₀ y₀ v₀ w₀ _ v' w' h₀ rfl ev ew] at e
    rw [map_div₀, e, mul_div_cancel_right₀ _ ((map_ne_zero j').2 n0)]

end PositivityTheory.Xgn.FrameRatioConstant

open PositivityTheory.Xgn.FrameRatioConstant in
theorem PositivityTheory.Xgn.frame_ratio_constant_rational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c) (κ : ℂ), τ (H.rt : E) = H.rt0 → IsLineFn U τ φ → IsLineFn U τ φ' → (∀ y v w, IsFramed U τ (algebraMap c.F ℂ) y v w → φ' ℂ y v w = κ * φ ℂ y v w) → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  intro E _ _ _ H D l Xo c U τ φ φ' κ _ h h' hκ
  by_cases hex : ∃ (F : Type) (_ : Field F) (β : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q),
      IsFramed U τ β y v w
  · obtain ⟨F₀, _, β₁, y₁, v₁, w₁, hf₁⟩ := hex
    obtain ⟨k, _, β₀, -, j, r, hr, -, hj, -, hall⟩ := ratio_spec h h' hκ hf₁
    have hjr := hall j hj
    have hmem : κ ∈ c.F := by
      refine PositivityTheory.Xgn.mem_of_fixed_by_automorphisms c.F κ c.fin fun g hg => ?_
      have := hall (g.toRingHom.comp j) (by
        rw [RingHom.comp_assoc, hj]
        ext a
        exact hg a a.2)
      rw [RingHom.comp_apply, hjr] at this
      exact this
    refine ⟨⟨κ, hmem⟩, fun h0 => ?_, fun F _ βF y v w hf => ?_⟩
    · have : κ = 0 := congrArg Subtype.val h0
      exact (map_ne_zero j).2 hr (hjr.trans this)
    · obtain ⟨k', _, β₀', f, j', r', -, hβ, hj', e, hall'⟩ := ratio_spec h h' hκ hf
      have : r' = β₀' ⟨κ, hmem⟩ := j'.injective (by
        rw [hall' j' hj']
        exact (DFunLike.congr_fun hj' ⟨κ, hmem⟩).symm)
      rw [e, this, ← hβ]
      rfl
  · exact ⟨1, one_ne_zero, fun F _ βF y v w hf => absurd ⟨F, inferInstance, βF, y, v, w, hf⟩ hex⟩

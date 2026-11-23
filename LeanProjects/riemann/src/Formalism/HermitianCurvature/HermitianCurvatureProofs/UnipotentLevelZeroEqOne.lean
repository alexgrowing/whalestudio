import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadCorrespondenceOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WittOrthonormalBasis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SupportPhiZeroSubset

namespace Formalism.FourierDecayAlt.P.PBI

open Finset MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate Matrix

noncomputable section

section unit

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem inner_map_of_norm (A : Wp →L[ℂ] Wp) (hA : ∀ v, ‖A v‖ = ‖v‖) (v v' : Wp) :
    inner ℂ (A v) (A v') = inner ℂ v v' := (LinearMap.norm_map_iff_inner_map_map A).1 hA v v'

theorem hsInner_comp_left [FiniteDimensional ℂ Wq] (A : Wp →L[ℂ] Wp) (hA : ∀ v, ‖A v‖ = ‖v‖)
    (U V : Wq →L[ℂ] Wp) : B.hsInner (A.comp U) (A.comp V) = B.hsInner U V := by
  simp only [Formalism.FourierDecayAlt.P.Topx1.hsInner_eq, ContinuousLinearMap.comp_apply, inner_map_of_norm A hA]

theorem sum_inner_onb [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ Wq) (U V : Wq →L[ℂ] Wp) :
    ∑ i, inner ℂ (V (b i)) (U (b i)) =
      LinearMap.trace ℂ Wq ((ContinuousLinearMap.adjoint V).comp U).toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ContinuousLinearMap.adjoint_inner_right]

theorem hsInner_comp_right [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bm : Wq →L[ℂ] Wq)
    (hB : ∀ v, ‖Bm v‖ = ‖v‖) (U V : Wq →L[ℂ] Wp) :
    B.hsInner (U.comp Bm) (V.comp Bm) = B.hsInner U V := by
  let e : Wq ≃ₗᵢ[ℂ] Wq := LinearIsometry.toLinearIsometryEquiv ⟨Bm.toLinearMap, hB⟩ rfl
  let b := stdOrthonormalBasis ℂ Wq
  have h1 : B.hsInner (U.comp Bm) (V.comp Bm) = ∑ i, inner ℂ (V ((b.map e) i)) (U ((b.map e) i)) := by
    rw [Formalism.FourierDecayAlt.P.Topx1.hsInner_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [b, e, OrthonormalBasis.map_apply]
  rw [h1, sum_inner_onb, ← sum_inner_onb b, ← Formalism.FourierDecayAlt.P.Topx1.hsInner_eq]

end unit

section lev0

theorem unipotent_level_zero_eq_one {k r' : ℕ} (hr : r' = 0) (m : B.Mat k r') (hm : m ∈ Nset k r') : m = 1 := by
  subst hr
  ext i j
  have hj := j.isLt
  have := hm.2.2 i j (by omega) (by omega) (by omega)
  simpa [Matrix.one_apply] using this

theorem zetaL_eq_zhat {k r' : ℕ} (z z' : Fin (2 * r' + k + 1) → ℂ) (g : B.Mat k r') :
    Q.zetaL k r' z z' (Fin.last r') g = Zhat k r' z z' g (Fin.last r') (Fin.last r') := by
  simp only [Q.zetaL, Zhat]

theorem corner_matrix_level_zero_eq {k r' : ℕ} (hr : r' = 0) (z z' : Fin (2 * r' + k + 1) → ℂ) (g g' : B.Mat k r')
    (h : Q.zetaL k r' z z' (Fin.last r') g = Q.zetaL k r' z z' (Fin.last r') g') :
    Zhat k r' z z' g = Zhat k r' z z' g' := by
  subst hr
  ext a b
  have ha : a = Fin.last 0 := Fin.ext (by have := a.isLt; first | simp | omega)
  have hb : b = Fin.last 0 := Fin.ext (by have := b.isLt; first | simp | omega)
  subst ha hb
  rw [← zetaL_eq_zhat, ← zetaL_eq_zhat, h]

theorem gram_function_level_zero {k r' : ℕ} (hr : r' = 0) (z z' : Fin (2 * r' + k + 1) → ℂ) (g : B.Mat k r') :
    Gf k r' z z' g = Complex.normSq (Q.zetaL k r' z z' (Fin.last r') g) - Tz k r' z * Tz k r' z' := by
  subst hr
  rw [gf_eq_gPoly k 0 z z' g, zetaL_eq_zhat]
  unfold gPoly
  rw [Matrix.det_fin_one, Matrix.det_isEmpty]
  simp

end lev0

def HeadTypesAt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (Cb : ℝ) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → LevFrame p ν'r m₀r →
    ∀ x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z',
    ∀ γ₀ ∈ B.GV P.k (P.r - P.r),
      Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
        Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 →
      D.IsDFrame (p.T.bs P.r) ν'r m₀r γ₀ →
    (∀ Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
          (p.T.bs P.r).π',
        ∑ ρ : M.Ty P, (p.TP.E ρ).comp ((Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) =
          (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) ∧
    (∀ h : C.LPt, D.IsLocPt h P.r →
        ∀ (y : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
          (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π') e,
        (P5.act ((Fr.ofWord L st (D.positionted w)).d L) y e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀ =
          ∑ ρ : M.Ty P, ((Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w
              (h ++ [(1, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)]) e ρ ^ 2 : ℝ) : ℂ) •
            (p.TP.E ρ).comp ((y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀))

end

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped Matrix

theorem head_types_of_types_at : PBI.HeadTypesAt → PBI.HeadTypes := by
  intro hAt Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb ν'r m₀r hD hdd hF hcut hLev x hx γ₀ hγ hζ hfr
  obtain ⟨hex0, hd0⟩ := hAt Wp Wq P p F w X μ L st Cb ν'r m₀r hD hdd hF hcut hLev x hx γ₀ hγ hζ hfr
  set Bs := p.T.bs P.r with hBs
  have hr0 : P.r - P.r = 0 := Nat.sub_self _
  have hstd : C2.Std P.k (P.r - P.r) Bs.z Bs.z' := ⟨Bs.k_pos, ⟨Bs.z_mem, Bs.T_pos⟩, ⟨Bs.z'_mem, Bs.T'_pos⟩⟩
  have hx2G : x.2 ∈ B.GV P.k (P.r - P.r) := hx.2.1.1
  have hGG : 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) Bs.z Bs.z' (Fin.last _) x.2) -
      Tz P.k (P.r - P.r) Bs.z * Tz P.k (P.r - P.r) Bs.z' := hx.2.2
  have hGpos : 0 < Gf P.k (P.r - P.r) Bs.z Bs.z' γ₀ := by
    rw [PBI.gram_function_level_zero hr0, hζ]; exact hGG
  have hZ : Zhat P.k (P.r - P.r) Bs.z Bs.z' γ₀ = Zhat P.k (P.r - P.r) Bs.z Bs.z' x.2 :=
    PBI.corner_matrix_level_zero_eq hr0 _ _ _ _ hζ
  obtain ⟨s0, hs0, s0', hs0', hgs⟩ :=
    Formalism.FourierDecayAlt.P.fibre_orbit_description P.k (P.r - P.r) Bs.z Bs.z' hstd γ₀ hγ x.2 hx2G hGpos hZ
  obtain ⟨⟨h1, hh1, m1, hm1, rfl⟩, -⟩ := hs0
  obtain ⟨⟨h2, hh2, m2, hm2, rfl⟩, -⟩ := hs0'
  rw [PBI.unipotent_level_zero_eq_one hr0 m1 hm1, PBI.unipotent_level_zero_eq_one hr0 m2 hm2, Matrix.mul_one, Matrix.mul_one] at hgs
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed P.k (P.r - P.r) Bs.z
  have hW' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed P.k (P.r - P.r) Bs.z'
  have hsi : h1⁻¹ ∈ UWset P.k (P.r - P.r) Bs.z := hW.inv_mem _ hh1
  have hs'i : h2⁻¹ ∈ UWset P.k (P.r - P.r) Bs.z' := hW'.inv_mem _ hh2
  have hu1 : IsUnit h1.det := hW.unit _ hh1
  have hu2 : IsUnit h2.det := hW'.unit _ hh2
  have hπ1 : ∀ v, Bs.π h1 (Bs.π h1⁻¹ v) = v := by
    intro v
    rw [← ContinuousLinearMap.comp_apply, ← Bs.π_rep.2 _ hh1 _ hsi, Matrix.mul_nonsing_inv _ hu1, Bs.π_rep.1]
    rfl
  have hπ2 : ∀ v, Bs.π h1⁻¹ (Bs.π h1 v) = v := by
    intro v
    rw [← ContinuousLinearMap.comp_apply, ← Bs.π_rep.2 _ hsi _ hh1, Matrix.nonsing_inv_mul _ hu1, Bs.π_rep.1]
    rfl
  have hπ'1 : ∀ v, Bs.π' h2 (Bs.π' h2⁻¹ v) = v := by
    intro v
    rw [← ContinuousLinearMap.comp_apply, ← Bs.π'_rep.2 _ hh2 _ hs'i, Matrix.mul_nonsing_inv _ hu2, Bs.π'_rep.1]
    rfl
  have hx0 : (x.1, γ₀) ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r Bs.z Bs.z' := by
    have hpr : (JC.parLev P P.r).r = 0 := Nat.sub_self P.r
    refine ⟨hx.1, ⟨hγ, fun a _ => absurd a.isLt (by omega)⟩, ?_⟩
    change 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) Bs.z Bs.z' (Fin.last _) γ₀) -
      Tz P.k (P.r - P.r) Bs.z * Tz P.k (P.r - P.r) Bs.z'
    rw [hζ]; exact hGG
  have heq : ∀ Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r Bs.z Bs.z' Bs.π Bs.π',
      (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2 =
        (Bs.π h1⁻¹).comp (((Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀).comp
          (Bs.π' h2)) := by
    intro Ψ
    have := Ψ.2.2.2 (x.1, γ₀) hx0 h1⁻¹ hsi h2 hh2
    rw [hgs]; exact this
  have hidem : ∀ ρ u, p.TP.E ρ (p.TP.E ρ u) = p.TP.E ρ u := fun ρ u => by
    rw [← ContinuousLinearMap.comp_apply, p.TP.idem ρ]
  refine ⟨fun U => (Bs.π h1).comp (U.comp (Bs.π' h2⁻¹)),
    fun ρ => (Bs.π h1⁻¹).comp ((p.TP.E ρ).comp (Bs.π h1)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U V
    rw [PBI.hsInner_comp_left _ (Bs.π_unitary _ hh1), PBI.hsInner_comp_right _ (Bs.π'_unitary _ hs'i)]
  · intro ρ U
    ext v
    simp only [ContinuousLinearMap.comp_apply, hπ1]
  · intro ρ
    ext v
    simp only [ContinuousLinearMap.comp_apply, hπ1, hidem]
  · intro ρ v v'
    simp only [ContinuousLinearMap.comp_apply]
    calc inner ℂ (Bs.π h1⁻¹ (p.TP.E ρ (Bs.π h1 v))) v'
        = inner ℂ (Bs.π h1 (Bs.π h1⁻¹ (p.TP.E ρ (Bs.π h1 v)))) (Bs.π h1 v') :=
          (PBI.inner_map_of_norm _ (Bs.π_unitary _ hh1) _ _).symm
      _ = inner ℂ (p.TP.E ρ (Bs.π h1 v)) (Bs.π h1 v') := by rw [hπ1]
      _ = inner ℂ (Bs.π h1 v) (p.TP.E ρ (Bs.π h1 v')) := p.TP.selfAdj ρ _ _
      _ = inner ℂ (Bs.π h1 v) (Bs.π h1 (Bs.π h1⁻¹ (p.TP.E ρ (Bs.π h1 v')))) := by rw [hπ1]
      _ = inner ℂ v (Bs.π h1⁻¹ (p.TP.E ρ (Bs.π h1 v'))) := PBI.inner_map_of_norm _ (Bs.π_unitary _ hh1) _ _
  · intro y e
    rw [heq (y e)]
    ext v
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, hπ1]
    rw [← map_sum]
    congr 1
    have := congrArg (fun T : Wq →L[ℂ] Wp => T (Bs.π' h2 v)) (hex0 (y e))
    simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply] using this
  · intro h hh y e
    rw [heq (P5.act _ y e), hd0 h hh y e, heq (y e)]
    ext v
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      map_sum, map_smul, hπ1]
  · intro Ψ
    rw [heq Ψ]
    ext v
    simp only [ContinuousLinearMap.comp_apply, hπ1, hπ'1]

end Formalism.FourierDecayAlt.P

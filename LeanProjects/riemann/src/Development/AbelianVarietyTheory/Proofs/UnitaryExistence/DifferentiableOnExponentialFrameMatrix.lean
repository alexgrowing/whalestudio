import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHolomorphicLieFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

open Filter Topology GlobalTheory.TangentOrigin GlobalTheory.HolLieFrame

namespace GlobalTheory.HolFrameMatrix

theorem differentiableAt_of_mul_eq_one {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ}
    (G A : V → Matrix (Fin n) (Fin n) ℂ) (b₀ : V) (hA : ∀ i j, DifferentiableAt ℂ (fun b => A b i j) b₀)
    (h : ∀ᶠ b in 𝓝 b₀, G b * A b = 1) (i j : Fin n) : DifferentiableAt ℂ (fun b => G b i j) b₀ := by
  refine differentiableAt_pi.1 (differentiableAt_of_forms (fun b => G b i) b₀ fun w hw => ?_) j
  have h0 : w ᵥ* A b₀ = 0 := by
    funext i'
    have := hw (fun b => ∑ j, A b j i' • ContinuousLinearMap.proj j)
      (DifferentiableAt.fun_sum fun j _ => (hA j i').smul_const _) ?_
    · simpa [Matrix.vecMul, dotProduct, mul_comm] using this
    · refine (differentiableAt_const ((1 : Matrix (Fin n) (Fin n) ℂ) i i')).congr_of_eventuallyEq ?_
      filter_upwards [h] with b hb
      rw [← hb]
      simp [Matrix.mul_apply, mul_comm]
  have h1 : A b₀ * G b₀ = 1 := mul_eq_one_comm.1 h.self_of_nhds
  have := congrArg (· ᵥ* G b₀) h0
  simpa [Matrix.vecMul_vecMul, h1] using this

theorem differentiableAt_coord {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n) {m : ℕ} {B : Set (Fin m → ℂ)}
    {P : (Fin m → ℂ) → ((U.Di i).La →+ (Fin g → ℂ))} {R : Type} [CommRing R]
    (v : Sp (DualNumber R) ⟶ Xo.univ.t.G.left) (ev : (Fin m → ℂ) → (R →+* ℂ)) (hB : IsOpen B)
    (hP : IsHolPeriods (U.Di i) ty B P) (W : (Fin m → ℂ) → Fin g → ℂ)
    (hW : ∀ b ∈ B, IsDerivAt0 (fun z => (U.ex i (P b) z).left) (W b) (spMap (Chart.dualMapR (ev b)) ≫ v))
    {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) (hev : ∀ t, DifferentiableAt ℂ (fun b => ev b t) b₀) :
    DifferentiableAt ℂ W b₀ := by
  obtain ⟨hol₁, hol₂⟩ := U.hol i m B P hB hP
  refine differentiableAt_of_forms _ b₀ fun w hw => ?_
  have hw' : ∀ (O : Xo.univ.t.G.left.Opens) (f : Γ(Xo.univ.t.G.left, O)), ⊤ ≤ (U.ex i (P b₀) 0).left ⁻¹ᵁ O →
      fderiv ℂ (fun z => valAt' (U.ex i (P b₀) z).left O f) 0 w = 0 := by
    intro O f hO
    refine hw (fun b => fderiv ℂ (fun z => valAt' (U.ex i (P b) z).left O f) 0)
      (differentiableAt_fderiv (e := fun b z => (U.ex i (P b) z).left) hol₂ hb₀ O f hO) ?_
    obtain ⟨F, hF, hF'⟩ := exists_hol_snd v ev b₀ hev O f
      ((top_le_preimage_iff _ O).2 (by rw [(hW b₀ hb₀).1]; exact hO))
    refine hF.congr_of_eventuallyEq ?_
    filter_upwards [hF', hB.mem_nhds hb₀] with b ⟨h, e⟩ hb
    exact ((hW b hb).2 O h f).symm.trans e
  have d₁ := LocalLift.isDerivAt0_const (fun z => (U.ex i (P b₀) z).left) w hw'
  have d₀ := LocalLift.isDerivAt0_const (fun z => (U.ex i (P b₀) z).left) 0 fun _ _ _ => map_zero _
  let v₀ : epsPt (U.u i (P b₀)) ⟶ Xo.univ.t.G :=
    Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (U.ex i (P b₀) 0).left)
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w (U.ex i (P b₀) 0))))
  exact ((U.ex_diff i _ (hP.1 b₀ hb₀)).2 v₀ d₁.1).unique d₁ d₀

theorem dualMap_eq {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) : dualMap φ = Chart.dualMapR φ := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap, Chart.dualMapR]

theorem differentiableOn_frameMatrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (R : Type) [CommRing R] [Algebra c.F R] (y₀ : FrPt Xo c R) (B : Set (Fin T.m → ℂ)) (ψ : (Fin T.m → ℂ) → (R →ₐ[c.F] CAt σ)) (κ : (Fin T.m → ℂ) → ℂ) (z y : (Fin T.m → ℂ) → FrPt Xo c (CAt σ)) (G : (Fin T.m → ℂ) → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : (Fin T.m → ℂ) → CAt σ), IsOpen B → B ⊆ T.co ⁻¹' (M.X k).dom → (∀ t : R, DifferentiableOn ℂ (fun b => toC (ψ b t)) B) → (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b) ∧ IsThetaPt T b (κ b) (y b)) → ∀ τ i j, DifferentiableOn ℂ (fun b => toC (G b τ i j)) B := by
  intro E _ _ _ H Dw l Xo c σ g e F r M k T R _ _ y₀ B ψ κ z y G a hB hsub hψ h τ i j
  have hP : IsHolPeriods (F.Di k) (fun j => relab c σ (e j).1) B (fun b => T.Pf (T.co b)) :=
    ⟨fun b hb => T.holPer.1 b (hsub hb), fun x => (T.holPer.2 x).mono hsub⟩
  have hx : ∀ b ∈ B, (z b).x = F.u k (T.Pf (T.co b)) := fun b hb => (h b hb).2.1.1.symm.trans (h b hb).2.2.1
  have hI := fun b hb => GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k _ (hP.1 b hb)
  have htan : ∀ b ∈ B, ∀ j, IsTanAt (S := ℂ) (F.u k (T.Pf (T.co b))) ((z b).u τ j) := fun b hb j => by
    rw [← hx b hb]; exact (z b).tan τ j
  choose! W hW using fun b hb j => ((hI b hb).2.2 _ (htan b hb j)).exists
  let ev : (Fin T.m → ℂ) → (R →+* ℂ) := fun b => (ψ b).toRingHom
  intro b₀ hb₀
  refine DifferentiableAt.differentiableWithinAt ?_
  refine differentiableAt_of_mul_eq_one (fun b => Matrix.of fun i j => toC (G b τ i j))
    (fun b => Matrix.of fun j i' => W b j (e.symm ⟨τ, i'⟩)) b₀ (fun j i' => ?_) ?_ i j
  · refine differentiableAt_pi.1 (differentiableAt_coord F k (y₀.u τ j) ev hB hP (fun b => W b j) (fun b hb => ?_) hb₀
      fun t => (hψ t).differentiableAt (hB.mem_nhds hb₀)) _
    have := hW b hb j
    rw [(h b hb).1.2.1 τ j] at this
    rw [← dualMap_eq]
    exact this
  · filter_upwards [hB.mem_nhds hb₀] with b hb
    ext i i'
    have hc : IsCombAt (S := ℂ) (F.u k (T.Pf (T.co b))) ((z b).u τ) (fun j => toC (G b τ i j)) ((y b).u τ i) := by
      rw [← hx b hb]; exact (h b hb).2.1.2.1 τ i
    have hd := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k _ (hP.1 b hb) _ _ _ (hW b hb) _ _).1 hc
    have hd' := (h b hb).2.2.2.1 τ i
    have := congrFun (((hI b hb).2.2 _ ((hI b hb).1 _ _ hd)).unique hd hd') (e.symm ⟨τ, i'⟩)
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Pi.single_apply, eq_comm] using this

end GlobalTheory.HolFrameMatrix

import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegSqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentEqOfSameModulusPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHoloFrameChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHoloCoordFrameAt
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open GlobalTheory.PointFormSign Matrix
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.LocalModel

theorem differentiableAt_det {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} {u : V} (hA : ∀ a b, DifferentiableAt ℂ (fun v => A v a b) u) :
    DifferentiableAt ℂ (fun v => (A v).det) u := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _
  have key : ∀ t : Finset (Fin d), DifferentiableAt ℂ (fun v => ∏ i ∈ t, A v (σ i) i) u := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hA _ _).mul ih
  exact key _

theorem differentiableAt_inv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} {u : V} (hA : ∀ a b, DifferentiableAt ℂ (fun v => A v a b) u)
    (hd : (A u).det ≠ 0) (i k : Fin d) : DifferentiableAt ℂ (fun v => (A v)⁻¹ i k) u := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine ((differentiableAt_det hA).inv hd).mul (differentiableAt_det fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableAt_const _
  · exact hA _ _

theorem differentiableAt_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {a b d : ℕ}
    {A : V → Matrix (Fin a) (Fin b) ℂ} {B : V → Matrix (Fin b) (Fin d) ℂ} {u : V}
    (hA : ∀ i k, DifferentiableAt ℂ (fun v => A v i k) u) (hB : ∀ i k, DifferentiableAt ℂ (fun v => B v i k) u)
    (i k : Fin _) : DifferentiableAt ℂ (fun v => (A v * B v) i k) u := by
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun c _ => (hA i c).mul (hB c k)

theorem gram_cast {n m q q' : ℕ} (h : n = m) (h' : q' = q) (κ : ℂ) (Gm Mu : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin m) ℂ) (z : Matrix (Fin m) (Fin q) ℂ)
    (hG : Gm.submatrix (Fin.cast h.symm) (Fin.cast h.symm) = κ • (Cᴴ * (Formalism.DegreeFormula.hP z)⁻¹ * C)) :
    (Muᴴ * Gm * Mu)ᵀ = κ • ((C.submatrix (Fin.cast h) (Fin.cast h) * Mu)ᵀ *
      GlobalTheory.PointFormSign.domGram n q' (fun a b => z (Fin.cast h a) (Fin.cast h' b)) *
        (C.submatrix (Fin.cast h) (Fin.cast h) * Mu)ᴴᵀ) := by
  subst h h'
  have hG' : Gm = κ • (Cᴴ * (Formalism.DegreeFormula.hP z)⁻¹ * C) := by simpa using hG
  subst hG'
  simp only [GlobalTheory.PointFormSign.domGram, Formalism.DegreeFormula.hP, Fin.cast_eq_self, Matrix.submatrix_id_id, Matrix.of_apply]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]
  rfl

theorem posDef_cast {n m q q' : ℕ} (h : n = m) (h' : q' = q) (z : Matrix (Fin m) (Fin q) ℂ)
    (hz : (1 - z * zᴴ).PosDef) :
    (1 - Matrix.of (fun a b => z (Fin.cast h a) (Fin.cast h' b)) *
      (Matrix.of (fun a b => z (Fin.cast h a) (Fin.cast h' b)))ᴴ).PosDef := by
  subst h h'
  simp only [Fin.cast_eq_self]
  exact hz

theorem lieGram_local_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ τ : GlobalTheory.AllWt.Psi H, ∃ (κ : ℝ) (W : V X.dim → Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) ℂ) (Z : V X.dim → (Fin (Dw.mult τ.1) → Fin (Dw.p + Dw.q - Dw.mult τ.1) → ℂ)), 0 < κ ∧ (∀ᶠ u in 𝓝 (c'.e y), lieGram e U hj f₀ A₀ A (c'.e.symm u) τ.1 = (κ : ℂ) • ((W u)ᵀ * domGram _ _ (Z u) * (W u)ᴴᵀ)) ∧ (∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ Z u) ∧ (∀ i j, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => W u i j) u) ∧ IsUnit (W (c'.e y)).det ∧ (1 - Matrix.of (Z (c'.e y)) * (Matrix.of (Z (c'.e y)))ᴴ).PosDef := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hLie y hy c' hyc A hA τ
  obtain ⟨kU, G, hG⟩ := GlobalTheory.LieBase.HoloFrame.exists_holo_frame_chart E H Dw l Xo c O β Y T F e σ U hσ hU X j hLie.1
    hj y hy c' hyc
  have hF : ∀ᶠ u in 𝓝 (c'.e y), ∃ h : G u ∈ (U.X kU).dom,
      cxPt T.Z (U.un kU ⟨G u, h⟩) = cxOf e σ hj (c'.e.symm u) := hG.mono fun u ⟨h, h1, _⟩ => ⟨h, h1⟩
  have hGd : ∀ τ' a b, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u :=
    fun τ' a b => hG.mono fun u ⟨_, _, h2⟩ => h2 τ' a b
  obtain ⟨M, hMd, hMu, hMc⟩ := GlobalTheory.LieBase.exists_holo_coord_frameAt E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀
    Eb A₀ hj hLie y hy c' hyc A hA τ kU G hF hGd
  have hle : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right _ _
  have hp : (U.X kU).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 kU).1]; omega
  have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.HodgeGenUnf.mult_psi τ
  have hq : Dw.p + Dw.q - Dw.mult τ.1 = Dw.p + Dw.q - Dw.p := by rw [hm]
  set τ' := GlobalTheory.HodgeGenUnf.letter hσ hU kU τ with hτ'

  have hco : ∀ u, (∀ τ'' a b, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ'' a b) u) →
      ∀ a b, DifferentiableAt ℂ (fun v => GlobalTheory.TrueCx.frameCo (U.X kU) hle (G v) τ' a b) u := by
    intro u hd a b
    simp only [GlobalTheory.TrueCx.frameCo, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun c _ => (hd _ _ _).const_mul _
  have hmo : ∀ u, (∀ τ'' a b, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ'' a b) u) →
      G u ∈ (U.X kU).dom → ∀ a b,
      DifferentiableAt ℂ (fun v => Formalism.MJ.moeb (GlobalTheory.TrueCx.frameCo (U.X kU) hle (G v) τ') 0 a b) u := by
    intro u hd hdom a b
    simp only [GlobalTheory.TrueCx.moeb_zero]
    refine differentiableAt_mul (fun i k => hco u hd _ _) (differentiableAt_inv (fun i k => hco u hd _ _) ?_) a b
    exact (GlobalTheory.TrueCx.frameCo_isUnit₂₂ (U.X kU) hle hp hdom τ').ne_zero
  refine ⟨2 * Real.pi,
    fun u => (GlobalTheory.ShFam.coW (U.X kU) hle (G u) τ').submatrix (Fin.cast hm) (Fin.cast hm) * M u,
    fun u a b => Formalism.MJ.moeb (GlobalTheory.TrueCx.frameCo (U.X kU) hle (G u) τ') 0 (Fin.cast hm a) (Fin.cast hq b),
    Real.two_pi_pos, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hMc, hF] with u hu1 hu2
    obtain ⟨h, ⟨g, hg⟩, hc⟩ := hu1
    obtain ⟨h', hx⟩ := hu2
    have hex : ∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm u)).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (c'.e.symm u) g :=
      ⟨g, hg⟩
    rw [lieGram, dif_pos hex]
    show ((hodgeMet T.Z U).gram _ hex.choose τ.1)ᵀ = _
    rw [GlobalTheory.HodgeOnDomain.eigGram_transport (hodgeMet T.Z U) hx.symm hex.choose (cxFrame T.Z (U.un kU ⟨G u, h⟩)) τ.1
      (M u) (hc _ _ hex.choose_spec)]
    exact gram_cast hm hq _ _ _ _ _ (GlobalTheory.HodgeGenUnf.hodgeMet_gram_frame T.Z hσ hU kU ⟨G u, h⟩ τ τ' rfl hle)
  · filter_upwards [hG] with u hu
    obtain ⟨h, -, hd⟩ := hu
    exact differentiableAt_pi.2 fun a => differentiableAt_pi.2 fun b => hmo u hd h _ _
  · intro a b
    filter_upwards [hG, Filter.eventually_all.2 fun c => Filter.eventually_all.2 fun d => hMd c d] with u hu hM
    obtain ⟨h, -, hd⟩ := hu
    refine differentiableAt_mul (fun i k => ?_) (fun i k => hM i k) a b
    simp only [Matrix.submatrix_apply, GlobalTheory.ShFam.coW, Matrix.sub_apply]
    exact (hco u hd _ _).sub (differentiableAt_mul (fun i k => hmo u hd h _ _) (fun i k => hco u hd _ _) _ _)
  · obtain ⟨h, -, -⟩ := hG.self_of_nhds
    rw [Matrix.det_mul]
    refine IsUnit.mul ?_ hMu
    have e1 : ((GlobalTheory.ShFam.coW (U.X kU) hle (G (c'.e y)) τ').submatrix (Fin.cast hm) (Fin.cast hm)).det =
        (GlobalTheory.ShFam.coW (U.X kU) hle (G (c'.e y)) τ').det := Matrix.det_submatrix_equiv_self (finCongr hm) _
    rw [e1]
    exact GlobalTheory.ShFam.isUnit_coW (U.X kU) hle hp h τ'
  · obtain ⟨h, -, -⟩ := hG.self_of_nhds
    have hz := GlobalTheory.TrueCx.domPt_mem (U.X kU) hle id hp h τ'
    exact posDef_cast hm hq _ (GlobalTheory.HodgeDomain.hP_posDef hz)

end GlobalTheory.LieBase.LocalModel

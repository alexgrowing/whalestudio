import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ContinuousTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdCharHalfSymplecticFormRealCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHomActionRealCoordinatesEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalvedSymplecticFormFiniteRealOrthogonalStatement
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW.TauSpanIdentities

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}

theorem fin_smul_eq (z : AEF F E) :
    (pairA F 0 1 : AF F) • z = (TensorProduct.map (LinearMap.inr F (Ainf F) (Af F)) LinearMap.id (finPartF F E z) : AEF F E) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero]; rfl
  | tmul a e =>
    rw [TensorProduct.smul_tmul']
    show _ = TensorProduct.map (LinearMap.inr F (Ainf F) (Af F)) LinearMap.id
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (a ⊗ₜ[F] e))
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul]
    congr 1
    exact Prod.ext (zero_mul _) (one_mul _)
  | add z z' hz hz' => rw [smul_add, hz, hz', map_add (finPartF F E)]; exact (map_add (TensorProduct.map (LinearMap.inr F (Ainf F) (Af F)) LinearMap.id) _ _).symm

theorem inf_smul_eq (z : AEF F E) :
    (pairA F 1 0 : AF F) • z = (TensorProduct.map (LinearMap.inl F (Ainf F) (Af F)) LinearMap.id (infPartF F E z) : AEF F E) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero]; rfl
  | tmul a e =>
    rw [TensorProduct.smul_tmul']
    show _ = TensorProduct.map (LinearMap.inl F (Ainf F) (Af F)) LinearMap.id
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (a ⊗ₜ[F] e))
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul]
    congr 1
    exact Prod.ext (one_mul _) (zero_mul _)
  | add z z' hz hz' => rw [smul_add, hz, hz', map_add (infPartF F E)]; exact (map_add (TensorProduct.map (LinearMap.inl F (Ainf F) (Af F)) LinearMap.id) _ _).symm

theorem finIdem_mul_of_fin {z : AEF F E} (hz : infPartF F E z = 0) : finIdem F E * z = z := by
  have h1 : (pairA F 0 1 : AF F) + pairA F 1 0 = 1 := Prod.ext (zero_add 1) (add_zero 1)
  have h2 := inf_smul_eq z
  rw [hz, map_zero] at h2
  rw [finIdem, ← Algebra.smul_def]
  calc (pairA F 0 1 : AF F) • z = pairA F 0 1 • z + pairA F 1 0 • z := by rw [h2]; exact (add_zero _).symm
    _ = z := by rw [← add_smul, h1, one_smul]

theorem finIdem_mul_of_real {z : AEF F E} (hz : finPartF F E z = 0) : finIdem F E * z = 0 := by
  rw [finIdem, ← Algebra.smul_def, fin_smul_eq, hz, map_zero]; rfl

theorem finPartF_finIdem : finPartF F E (finIdem F E) = 1 := by
  show Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (pairA F 0 1 ⊗ₜ 1) = 1
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem cAF_inc (e : E) : cAF σ (incAF F E e) = incAF F E (σ e) := by
  simp [cAF, incAF, sigR, inclR]

theorem finIdem_smul_of_fin {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) : finIdem F E • u = u := by
  funext i j
  exact finIdem_mul_of_fin (congrFun (congrFun hu i) j)

theorem finIdem_smul_of_real {u : WOF F E nS nT} (hu : u.map (finPartF F E) = 0) : finIdem F E • u = 0 := by
  funext i j
  exact finIdem_mul_of_real (congrFun (congrFun hu i) j)

theorem piWF_iotaVF (hι : IsChartF θ ι) (v : IxF F nS nT → ℂ) : piWF θ (iotaVF ι v) = v := by
  funext p
  exact hι.comp _ p.2

theorem piWF_ratWF (C : Ctx σ B JS JT ξ₀ θ ι) (y : Matrix (Fin nT) (Fin nS) E) :
    piWF θ (ratWF (F := F) y) = infRatF (tauB B) y := by
  funext p
  exact PositivityTheory.ThKW.RealC.theta_inc (C.inf p.2) _

theorem finIdem_add_iota (hι : IsChartF θ ι) (x : WOF F E nS nT) : x = finIdem F E • x + iotaVF ι (piWF θ x) := by
  funext i j
  show x i j = finIdem F E * x i j + ι (fun w => θ w (infPartF F E (x i j)))
  refine (sub_eq_zero.1 (hι.ext _ ?_ ?_)).symm.symm
  · simp only [map_sub, map_add, map_mul, finPartF_finIdem, one_mul, hι.fin, add_zero, sub_self]
  · intro w
    simp only [map_sub, map_add, map_mul, infPartF_finIdem, zero_mul, zero_add, hι.comp, sub_self]

theorem continuous_piWF (C : Ctx σ B JS JT ξ₀ θ ι) : Continuous (piWF (nS := nS) (nT := nT) θ) :=
  continuous_pi fun p => (PositivityTheory.ThKW.RealC.continuous_theta (C.inf p.2)).comp
    ((continuous_apply p.1.2).comp (continuous_apply p.1.1))

theorem beta_iota_right (C : Ctx σ B JS JT ξ₀ θ ι) (x : WOF F E nS nT) (v : IxF F nS nT → ℂ) :
    B.ψ (symplOHF σ JS JT ξ₀ x (iotaVF ι v)) =
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (piWF θ x) v : ℝ)) := by
  have hx := finIdem_add_iota C.chart x
  have h0 := (GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀ (finIdem F E • x) (iotaVF ι v) (finIdem_smul_fin x)
    (real_iotaVF C.chart v)).1
  conv_lhs => rw [hx]
  rw [GlobalTheory.RealWeilF.symplOHF_add_left, h0, zero_add,
    GlobalTheory.T.stdChar_half_symplecticForm_real_coordinates F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf ι C.chart, omV_apply]
  congr 1
  push_cast
  ring

theorem beta_iota_left (C : Ctx σ B JS JT ξ₀ θ ι) (v : IxF F nS nT → ℂ) (x : WOF F E nS nT) :
    B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι v) x) =
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) v (piWF θ x) : ℝ)) := by
  have hx := finIdem_add_iota C.chart x
  have h0 := (GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀ (finIdem F E • x) (iotaVF ι v) (finIdem_smul_fin x)
    (real_iotaVF C.chart v)).2
  conv_lhs => rw [hx]
  rw [GlobalTheory.RealWeilF.symplOHF_add_right, h0, zero_add,
    GlobalTheory.T.stdChar_half_symplecticForm_real_coordinates F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf ι C.chart, omV_apply]
  congr 1
  push_cast
  ring

theorem piWF_add (x y : WOF F E nS nT) : piWF θ (x + y) = piWF θ x + piWF θ y := (piWA θ).map_add x y

theorem piWF_of_fin {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) : piWF θ u = 0 := by
  funext p
  show θ p.2 (infPartF F E (u p.1.1 p.1.2)) = 0
  rw [show infPartF F E (u p.1.1 p.1.2) = 0 from congrFun (congrFun hu p.1.1) p.1.2, map_zero]

theorem actOF_fin (g : GAF σ JS) (h : GAF σ JT) {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) :
    (actOF σ JS JT g h u).map (infPartF F E) = 0 := by
  unfold actOF
  rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]

theorem piWF_actOF (C : Ctx σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x : WOF F E nS nT) :
    piWF θ (actOF σ JS JT g h x) = mMF σ JS JT θ (g, h) *ᵥ piWF θ x := by
  have hx := finIdem_add_iota C.chart x
  conv_lhs => rw [hx]
  rw [GlobalTheory.RealWeilF.actOF_add, piWF_add, piWF_of_fin (actOF_fin g h (finIdem_smul_fin x)), zero_add,
    GlobalTheory.T.adelicHomAction_realCoordinates_eq F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf ι C.chart g h, piWF_iotaVF C.chart]

theorem hOF_rat (x y : Matrix (Fin nT) (Fin nS) E) :
    hOF σ JS JT (ratWF (F := F) x) (ratWF (F := F) y) = incAF F E (hRatF σ JS JT x y) := by
  simp only [hOF, hRatF, ratWF, Matrix.map_apply, cAF_inc, map_sum, map_mul]

theorem trace_inc (e : E) :
    Algebra.trace (AF F) (AEF F E) (incAF F E e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem symplOHF_rat (x y : Matrix (Fin nT) (Fin nS) E) :
    symplOHF σ JS JT ξ₀ (ratWF (F := F) x) (ratWF (F := F) y) =
      algebraMap F (AF F) (1 / 2 * Algebra.trace F E (ξ₀ * hRatF σ JS JT x y)) := by
  rw [symplOHF, symplOF, hOF_rat, ← map_mul, trace_inc, ← map_mul]

theorem psi_rat (C : Ctx σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    B.ψ (symplOHF σ JS JT ξ₀ (ratWF x) (ratWF y)) = 1 := by
  rw [symplOHF_rat]
  exact C.good.std.2.1 _

theorem rhoFF_finRatF {g : GAF σ JS} {h : GAF σ JT} {a b} (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (y : Matrix (Fin nT) (Fin nS) E) : rhoFF σ JS JT (g⁻¹, h⁻¹) (finRatF F y) = finRatF F (b * y * a) := by
  apply XFF.ext
  show actOF σ JS JT g⁻¹ h⁻¹ (finIdem F E • ratWF (F := F) y) = finIdem F E • ratWF (F := F) (b * y * a)
  unfold actOF
  rw [inv_inv, ha, hb, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [ratWF, ratWF, Matrix.map_mul, Matrix.map_mul]

theorem infRatF_injective (B : Base F E) : Function.Injective (infRatF (nS := nS) (nT := nT) (tauB B)) := by
  intro x y hxy
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  funext i j
  exact (tauB B w).injective (congrFun hxy ((i, j), w))

theorem sum3 {α β γ M : Type} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M] (f : α → β → γ → M) :
    ∑ b, ∑ c, ∑ d, f b c d = ∑ d, ∑ c, ∑ b, f b c d :=
  calc ∑ b, ∑ c, ∑ d, f b c d = ∑ c, ∑ b, ∑ d, f b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ b, f b c d := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ b, f b c d := Finset.sum_comm

theorem hOF_trace (x y : WOF F E nS nT) :
    hOF σ JS JT x y = Matrix.trace (JS⁻¹.map (incAF F E) * (y.map (cAF σ))ᵀ * JT.map (incAF F E) * x) := by
  simp only [hOF, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => sum3 _

theorem hOF_actOF (hS : IsHermND σ JS) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    hOF σ JS JT (actOF σ JS JT g h x) (actOF σ JS JT g h y) = hOF σ JS JT x y := by
  have hu : IsUnit JS.det := isUnit_iff_ne_zero.mpr hS.2
  have hg : (((mtF σ JS g⁻¹).map (cAF σ))ᵀ * JS.map (incAF F E)) * mtF σ JS g⁻¹ = JS.map (incAF F E) := (g⁻¹).2
  have hh : (((mtF σ JT h).map (cAF σ))ᵀ * JT.map (incAF F E)) * mtF σ JT h = JT.map (incAF F E) := h.2
  rw [hOF_trace, hOF_trace]
  unfold actOF
  set G := mtF σ JS g⁻¹
  set H := mtF σ JT h
  set Si := JS⁻¹.map (incAF F E)
  set Sm := JS.map (incAF F E)
  set Tm := JT.map (incAF F E)
  have hi1 : Si * Sm = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hi2 : Sm * Si = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hK' : (Si * (G.map (cAF σ))ᵀ * Sm) * G = 1 := by
    have e : Si * (G.map (cAF σ))ᵀ * Sm * G = Si * ((G.map (cAF σ))ᵀ * Sm * G) := by simp only [Matrix.mul_assoc]
    rw [e, hg, hi1]
  have hK : G * (Si * (G.map (cAF σ))ᵀ * Sm) = 1 := by
    first | exact mul_eq_one_comm.1 hK' | exact Matrix.mul_eq_one_comm.1 hK' | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) hK'
  have hGJ : G * Si * (G.map (cAF σ))ᵀ = Si := by
    calc G * Si * (G.map (cAF σ))ᵀ = G * (Si * (G.map (cAF σ))ᵀ * Sm) * Si := by
          simp only [Matrix.mul_assoc, hi2, Matrix.mul_one]
      _ = Si := by rw [hK, Matrix.one_mul]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  have e1 : Si * ((G.map (cAF σ))ᵀ * ((y.map (cAF σ))ᵀ * (H.map (cAF σ))ᵀ)) * Tm * (H * x * G) =
      (Si * (G.map (cAF σ))ᵀ * (y.map (cAF σ))ᵀ * ((H.map (cAF σ))ᵀ * Tm * H) * x) * G := by
    simp only [Matrix.mul_assoc]
  rw [e1, hh, Matrix.trace_mul_comm]
  have e2 : G * (Si * (G.map (cAF σ))ᵀ * (y.map (cAF σ))ᵀ * Tm * x) =
      (G * Si * (G.map (cAF σ))ᵀ) * ((y.map (cAF σ))ᵀ * Tm * x) := by
    simp only [Matrix.mul_assoc]
  rw [e2, hGJ]
  simp only [Matrix.mul_assoc]

theorem symplOF_actOF (C : Ctx σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOF σ JS JT ξ₀ x y := by
  unfold symplOF
  rw [hOF_actOF C.hS]

theorem symplOF_eq_add (x y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ x y = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y := by
  rw [symplOHF, ← add_mul, ← map_add]
  norm_num

theorem gamQF_eq_one_iff (C : Ctx σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔
      ∃ z : ℤ, omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) x) (infRatF (tauB B) y) = z := by
  have hx : ratWF (F := F) x = finIdem F E • ratWF (F := F) x + iotaVF ι (infRatF (tauB B) x) := by
    have := finIdem_add_iota C.chart (ratWF (F := F) x); rwa [piWF_ratWF C] at this
  have hy : ratWF (F := F) y = finIdem F E • ratWF (F := F) y + iotaVF ι (infRatF (tauB B) y) := by
    have := finIdem_add_iota C.chart (ratWF (F := F) y); rwa [piWF_ratWF C] at this
  have cross : ∀ (a : WOF F E nS nT) (b : IxF F nS nT → ℂ), a.map (infPartF F E) = 0 →
      symplOHF σ JS JT ξ₀ a (iotaVF ι b) = 0 ∧ symplOHF σ JS JT ξ₀ (iotaVF ι b) a = 0 :=
    fun a b ha => GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀ a (iotaVF ι b) ha (real_iotaVF C.chart b)
  have hr := psi_rat C x y
  rw [hx, hy, GlobalTheory.RealWeilF.symplOHF_add_left, GlobalTheory.RealWeilF.symplOHF_add_right, GlobalTheory.RealWeilF.symplOHF_add_right,
    (cross _ _ (finIdem_smul_fin _)).1, (cross _ _ (finIdem_smul_fin _)).2, add_zero, zero_add,
    AddChar.map_add_eq_mul, beta_iota_right C, piWF_iotaVF C.chart] at hr
  set om := omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) x) (infRatF (tauB B) y)
  set P := B.ψ (symplOHF σ JS JT ξ₀ (finIdem F E • ratWF (F := F) x) (finIdem F E • ratWF (F := F) y))
  have hg : gamQF σ JS JT ξ₀ B.ψ x y = P * P := by
    show B.ψ (symplOF σ JS JT ξ₀ (finIdem F E • ratWF (F := F) x) (finIdem F E • ratWF (F := F) y)) = _
    rw [symplOF_eq_add, AddChar.map_add_eq_mul]
  have hP : P = Complex.exp (Real.pi * Complex.I * (om : ℂ)) := by
    calc P = P * (Complex.exp (-(Real.pi * Complex.I) * (om : ℂ)) * Complex.exp (Real.pi * Complex.I * (om : ℂ))) := by
          rw [← Complex.exp_add, show -(Real.pi * Complex.I) * (om : ℂ) + Real.pi * Complex.I * (om : ℂ) = 0 by ring,
            Complex.exp_zero, mul_one]
      _ = _ := by rw [← mul_assoc, hr, one_mul]
  rw [hg, hP, ← Complex.exp_add, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (2 : ℂ) * (Real.pi * Complex.I) ≠ 0 :=
      mul_ne_zero two_ne_zero (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero)
    have : (om : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ hpi
      linear_combination hn
    exact_mod_cast this
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn]; push_cast; ring⟩

section Lin

variable {κ : Type} [Fintype κ]

theorem dot_conj (M : Matrix κ κ ℂ) (x y : κ → ℂ) : star y ⬝ᵥ (Mᴴ *ᵥ x) = star (star x ⬝ᵥ (M *ᵥ y)) := by
  simp only [dotProduct, mulVec, conjTranspose_apply, star_sum, star_mul', star_star, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem dot_mul (s H : Matrix κ κ ℂ) (x y : κ → ℂ) : star (s *ᵥ y) ⬝ᵥ (H *ᵥ x) = star y ⬝ᵥ ((sᴴ * H) *ᵥ x) := by
  first
  | rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  | (simp only [dotProduct, mulVec, Matrix.mul_apply, conjTranspose_apply, star_sum, star_mul', Pi.star_apply,
      Finset.mul_sum, Finset.sum_mul]
     rw [Finset.sum_comm]
     refine Finset.sum_congr rfl fun _ _ => ?_
     rw [Finset.sum_comm]
     exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

theorem omV_laws [DecidableEq κ] {H s : Matrix κ κ ℂ} (hH : Hᴴ = H) (hs : s * s = 1) (hQ : (H * s).PosDef) :
    (∀ x y, omV H x y = -omV H y x) ∧ (∀ v, jV s (jV s v) = -v) ∧ (∀ x y, omV H x (jV s y) = omV H y (jV s x)) ∧
      ∀ v, v ≠ 0 → 0 < omV H v (jV s v) := by
  have hM : (H * s)ᴴ = H * s := hQ.1
  have hsH : sᴴ * H = H * s := by rw [← hM, Matrix.conjTranspose_mul, hH]
  have hj : ∀ x y, omV H x (jV s y) = (star y ⬝ᵥ ((H * s) *ᵥ x)).re := by
    intro x y
    rw [omV_apply, jV_apply, star_smul, smul_dotProduct, dot_mul, hsH, smul_eq_mul]
    simp only [Complex.star_def, Complex.conj_I, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im]
    ring
  refine ⟨fun x y => ?_, fun v => ?_, fun x y => ?_, fun v hv => ?_⟩
  · rw [omV_apply, omV_apply]
    have := dot_conj H x y
    rw [hH] at this
    rw [this, Complex.star_def, Complex.conj_im]
  · rw [jV_apply, jV_apply, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hs, Matrix.one_mulVec, smul_smul, Complex.I_mul_I,
      neg_one_smul]
  · rw [hj, hj]
    have := dot_conj (H * s) y x
    rw [hM] at this
    rw [this, Complex.star_def, Complex.conj_re]
  · rw [hj]
    have hp : 0 < star v ⬝ᵥ ((H * s) *ᵥ v) := by
      first | exact hQ.2 v hv | exact hQ.dotProduct_mulVec_pos hv | exact hQ.2 hv
    exact (Complex.pos_iff.1 hp).1

end Lin

theorem sig_sig (hB : B.IsGood σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])

theorem trace_places [IsTotallyReal F] (t : F) :
    algebraMap ℚ ℂ (Algebra.trace ℚ F t) = ∑ w : InfinitePlace F, w.embedding t := by
  first | rw [trace_eq_sum_embeddings (E := ℂ)] | rw [trace_eq_sum_embeddings ℂ]
  symm
  refine Fintype.sum_equiv (Equiv.ofBijective (fun w : InfinitePlace F => w.embedding.toRatAlgHom) ⟨?_, ?_⟩) _ _
    (fun w => rfl)
  · intro w w' h
    have := congrArg (fun φ : F →ₐ[ℚ] ℂ => InfinitePlace.mk (φ : F →+* ℂ)) h
    simpa [InfinitePlace.mk_embedding] using this
  · intro φ
    refine ⟨InfinitePlace.mk (φ : F →+* ℂ), ?_⟩
    have hr : ComplexEmbedding.IsReal (φ : F →+* ℂ) := InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
    have he : (InfinitePlace.mk (φ : F →+* ℂ)).embedding = (φ : F →+* ℂ) := by
      first
      | exact InfinitePlace.embedding_mk_eq_of_isReal hr
      | exact (InfinitePlace.embedding_mk_eq (φ : F →+* ℂ)).elim id (fun e => e.trans (ComplexEmbedding.isReal_iff.1 hr))
    ext x
    show (InfinitePlace.mk (φ : F →+* ℂ)).embedding x = φ x
    rw [he]
    rfl

theorem gamQF_eq_one_iff' (C : Ctx σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT x y) = n := by
  haveI : IsTotallyReal F := C.good.cm.1
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 : gamQF σ JS JT ξ₀ B.ψ x y =
      B.ψ (pairA F 0 (algebraMap F (Af F) (Algebra.trace F E (ξ₀ * hRatF σ JS JT x y)))) := by
    have := LatC.sympl_ft (σ := σ) (JS := JS) (JT := JT) (ξ₀ := ξ₀) (sig_sig C.good) 1 1 x y
    rw [one_mul, one_mul] at this
    show B.ψ (symplOF σ JS JT ξ₀ (finIdem F E • ratWF (F := F) x) (finIdem F E • ratWF (F := F) y)) = _
    exact congrArg B.ψ this
  have h2 : ∀ t : F, pairA F 0 (algebraMap F (Af F) t) = algebraMap F (AF F) t + pairA F (-(algebraMap F (Ainf F) t)) 0 := by
    intro t
    refine Prod.ext ?_ ?_
    · show (0 : Ainf F) = algebraMap F (Ainf F) t + -(algebraMap F (Ainf F) t)
      rw [add_neg_cancel]
    · show algebraMap F (Af F) t = algebraMap F (Af F) t + 0
      rw [add_zero]
  have h3 : ∀ t : F, B.ψ (pairA F (-(algebraMap F (Ainf F) t)) 0) =
      Complex.exp (2 * Real.pi * Complex.I * algebraMap ℚ ℂ (Algebra.trace ℚ F t)) := by
    intro t
    have hw : ∀ w, θ w ((-(algebraMap F (Ainf F) t)) ⊗ₜ[F] (1 : E)) = -(w.embedding t) := by
      intro w
      have e : (algebraMap F (Ainf F) t) ⊗ₜ[F] (1 : E) = (1 : Ainf F) ⊗ₜ[F] algebraMap F E t := by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      rw [TensorProduct.neg_tmul, map_neg, e, (C.inf w).1]
      exact congrArg Neg.neg (RingHom.congr_fun (B.emb w).2 t)
    rw [GlobalTheory.StdCharWeilDatum.psi_pairA C.good.std, ← GlobalTheory.StdCharWeilDatum.sum_infFam B θ C.inf, trace_places]
    congr 1
    simp only [hw, Finset.sum_neg_distrib]
    ring
  rw [h1, h2, AddChar.map_add_eq_mul, C.good.std.2.1, one_mul, h3, Complex.exp_eq_one_iff, Algebra.trace_trace]
  have hpi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h4 : algebraMap ℚ ℂ (Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT x y)) = (n : ℂ) :=
      mul_left_cancel₀ hpi (by linear_combination hn)
    rw [eq_ratCast (algebraMap ℚ ℂ)] at h4
    exact_mod_cast h4
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn, map_intCast]; ring⟩

section Span

def wE (B : Base F E) (w : InfinitePlace F) : InfinitePlace E := InfinitePlace.mk (B.emb w).1

def cw (B : Base F E) (w : InfinitePlace F) : ℂ →ₗ[ℝ] ℂ :=
  if (wE B w).embedding = (B.emb w).1 then LinearMap.id else Complex.conjAe.toLinearEquiv.toLinearMap

theorem cw_emb (B : Base F E) (w : InfinitePlace F) (e : E) : cw B w ((wE B w).embedding e) = (B.emb w).1 e := by
  unfold cw
  split_ifs with h
  · rw [h]; rfl
  · have h' := (InfinitePlace.embedding_mk_eq (B.emb w).1).resolve_left h
    show Complex.conjAe ((InfinitePlace.mk (B.emb w).1).embedding e) = (B.emb w).1 e
    rw [h']
    simp [ComplexEmbedding.conjugate_coe_eq]

theorem cw_cw (B : Base F E) (w : InfinitePlace F) (z : ℂ) : cw B w (cw B w z) = z := by
  unfold cw
  split_ifs
  · rfl
  · simp

theorem wE_comap (B : Base F E) (w : InfinitePlace F) : (wE B w).comap (algebraMap F E) = w := by
  rw [wE, InfinitePlace.comap_mk, (B.emb w).2, InfinitePlace.mk_embedding]

def Lm (B : Base F E) [IsTotallyComplex E] : mixedEmbedding.mixedSpace E →ₗ[ℝ] (InfinitePlace F → ℂ) :=
  LinearMap.pi fun w => (cw B w).comp ((LinearMap.proj (R := ℝ) (φ := fun _ : {W : InfinitePlace E // W.IsComplex} => ℂ)
    ⟨wE B w, IsTotallyComplex.isComplex _⟩).comp (LinearMap.snd ℝ _ _))

theorem span_tau (hB : B.IsGood σ) :
    Submodule.span ℝ (Set.range fun e : E => fun w : InfinitePlace F => (B.emb w).1 e) = ⊤ := by
  haveI : IsTotallyComplex E := hB.cm.2.1
  have hall : ∀ z ∈ Submodule.span ℝ (Set.range (mixedEmbedding E)),
      Lm B z ∈ Submodule.span ℝ (Set.range fun e : E => fun w : InfinitePlace F => (B.emb w).1 e) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨e, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨e, ?_⟩
      funext w
      show (B.emb w).1 e = cw B w ((wE B w).embedding e)
      rw [cw_emb]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have htop : Submodule.span ℝ (Set.range (mixedEmbedding E)) = ⊤ := by
    refine eq_top_iff.2 (le_trans (le_of_eq (mixedEmbedding.latticeBasis E).span_eq.symm) (Submodule.span_mono ?_))
    rintro _ ⟨i, rfl⟩
    exact ⟨_, (mixedEmbedding.latticeBasis_apply E i).symm⟩
  rw [eq_top_iff]
  rintro f -
  let z : mixedEmbedding.mixedSpace E :=
    (0, fun W => cw B (W.1.comap (algebraMap F E)) (f (W.1.comap (algebraMap F E))))
  have hz : Lm B z = f := by
    funext w
    show cw B w (cw B ((wE B w).comap (algebraMap F E)) (f ((wE B w).comap (algebraMap F E)))) = f w
    rw [wE_comap, cw_cw]
  rw [← hz]
  exact hall z (htop ▸ Submodule.mem_top)

theorem span_infRatF (hB : B.IsGood σ) :
    Submodule.span ℝ (Set.range (infRatF (nS := nS) (nT := nT) (tauB B))) = ⊤ := by
  set V := Submodule.span ℝ (Set.range (infRatF (nS := nS) (nT := nT) (tauB B)))
  have key : ∀ (q : Fin nT × Fin nS) (g : InfinitePlace F → ℂ),
      (fun p : IxF F nS nT => if p.1 = q then g p.2 else 0) ∈ V := by
    intro q g
    have hg : g ∈ Submodule.span ℝ (Set.range fun e : E => fun w : InfinitePlace F => (B.emb w).1 e) := by
      rw [span_tau hB]; trivial
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨e, rfl⟩ := hg
      apply Submodule.subset_span
      refine ⟨Matrix.of fun a b => if (a, b) = q then e else 0, ?_⟩
      funext p
      show (B.emb p.2).1 (if (p.1.1, p.1.2) = q then e else 0) = if p.1 = q then (B.emb p.2).1 e else 0
      by_cases h : p.1 = q
      · rw [if_pos h, if_pos (by rw [← h])]
      · rw [if_neg h, if_neg (by intro h'; exact h (by rw [← h'])), map_zero]
    | zero =>
      convert V.zero_mem using 1
      funext p
      split_ifs <;> rfl
    | add g g' _ _ hg hg' =>
      convert V.add_mem hg hg' using 1
      funext p
      by_cases h : p.1 = q <;> simp [h]
    | smul c g _ hg =>
      convert V.smul_mem c hg using 1
      funext p
      by_cases h : p.1 = q <;> simp [h]
  rw [eq_top_iff]
  rintro v -
  have hv : v = ∑ q : Fin nT × Fin nS, (fun p : IxF F nS nT => if p.1 = q then v (q, p.2) else 0) := by
    funext p
    rw [Finset.sum_apply, Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [hv]
  exact V.sum_mem fun q _ => key q (fun w => v (q, w))

end Span

end PositivityTheory.ThKW.TauSpanIdentities

end

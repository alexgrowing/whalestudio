import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFrameOneStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodEigenFrame
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodHermitianTypeCompatibilityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FcHoloDetDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnExponentialFrameMatrix
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.AnHol

variable {m : ℕ}

theorem inv_differentiableAt {n : ℕ} (M : (Fin m → ℂ) → Matrix (Fin n) (Fin n) ℂ) (b₀ : Fin m → ℂ)
    (hM : ∀ i j, DifferentiableAt ℂ (fun b => M b i j) b₀) (h0 : (M b₀).det ≠ 0) (i j : Fin n) :
    DifferentiableAt ℂ (fun b => (M b)⁻¹ i j) b₀ := by
  have hd := fcHolo_det_differentiableAt M b₀ hM
  refine GlobalTheory.HolFrameMatrix.differentiableAt_of_mul_eq_one (fun b => (M b)⁻¹) M b₀ hM ?_ i j
  filter_upwards [hd.continuousAt.eventually_ne h0] with b hb
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hb)

theorem exists_rightInverse_of_li {r g : ℕ} (X : Fin r → Fin g → ℂ) (hX : LinearIndependent ℂ X) :
    ∃ N : Matrix (Fin g) (Fin r) ℂ, Matrix.of X * N = 1 := by
  classical
  have hr : (Matrix.of X).rank = r := by
    simpa using LinearIndependent.rank_matrix (M := Matrix.of X) hX
  have hs : Function.Surjective (Matrix.of X).mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank] using hr
  choose c hc using fun a : Fin r => hs (Pi.single a 1)
  refine ⟨Matrix.of fun k a => c a k, ?_⟩
  ext a b
  have := congrFun (hc b) a
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem coef_differentiableAt {r g : ℕ} {κ : Type*}
    (X : (Fin m → ℂ) → Fin r → Fin g → ℂ) (Y : (Fin m → ℂ) → κ → Fin g → ℂ)
    (A : (Fin m → ℂ) → Matrix (Fin r) κ ℂ) (b₀ : Fin m → ℂ)
    (hX : ∀ i, DifferentiableAt ℂ (fun b => X b i) b₀) (hY : ∀ n, DifferentiableAt ℂ (fun b => Y b n) b₀)
    (hli : LinearIndependent ℂ (X b₀))
    (hA : ∀ᶠ b in 𝓝 b₀, ∀ n, Y b n = ∑ i, A b i n • X b i) (i : Fin r) (n : κ) :
    DifferentiableAt ℂ (fun b => A b i n) b₀ := by
  classical
  obtain ⟨N, hN⟩ := exists_rightInverse_of_li (X b₀) hli
  let G : (Fin m → ℂ) → Matrix (Fin r) (Fin r) ℂ := fun b => Matrix.of (X b) * N
  have hG : ∀ i j, DifferentiableAt ℂ (fun b => G b i j) b₀ := fun i j => by
    simp only [G, Matrix.mul_apply, Matrix.of_apply]
    exact DifferentiableAt.fun_sum fun k _ => (differentiableAt_pi.1 (hX i) k).mul_const _
  have hG0 : (G b₀).det ≠ 0 := by simp [G, hN]
  have hdet := (fcHolo_det_differentiableAt G b₀ hG).continuousAt.eventually_ne hG0
  have hZ : ∀ j, DifferentiableAt ℂ (fun b => ∑ k, Y b n k * N k j) b₀ := fun j =>
    DifferentiableAt.fun_sum fun k _ => (differentiableAt_pi.1 (hY n) k).mul_const _
  have hI := inv_differentiableAt G b₀ hG hG0
  have hR : DifferentiableAt ℂ (fun b => ∑ j, (∑ k, Y b n k * N k j) * (G b)⁻¹ j i) b₀ :=
    DifferentiableAt.fun_sum fun j _ => (hZ j).mul (hI j i)
  refine hR.congr_of_eventuallyEq ?_
  filter_upwards [hA, hdet] with b hb hd
  have e1 : ∀ j, ∑ k, Y b n k * N k j = ∑ i', A b i' n * G b i' j := fun j => by
    simp only [hb n, G, Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun k _ => by ring
  have e2 : G b * (G b)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd)
  simp only [e1, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [_root_.mul_assoc, ← Finset.mul_sum]
  have e3 : ∀ i', ∑ j, G b i' j * (G b)⁻¹ j i = (1 : Matrix (Fin r) (Fin r) ℂ) i' i := fun i' => by
    rw [← e2, Matrix.mul_apply]
  simp [e3, Matrix.one_apply]

theorem tyPart_differentiableAt {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ)
    (f : (Fin m → ℂ) → Fin g → ℂ) (b₀ : Fin m → ℂ) (hf : DifferentiableAt ℂ f b₀) :
    DifferentiableAt ℂ (fun b => tyPart ty τ (f b)) b₀ := by
  refine differentiableAt_pi.2 fun k => ?_
  by_cases h : ty k = τ
  · simpa [tyPart, h] using differentiableAt_pi.1 hf k
  · simp [tyPart, h]

theorem tyPart_sum_smul {E : Type} [Field E] {g : ℕ} {κ : Type*} [Fintype κ] (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ)
    (c : κ → ℂ) (z : κ → Fin g → ℂ) : tyPart ty τ (∑ m, c m • z m) = ∑ m, c m • tyPart ty τ (z m) := by
  funext k
  by_cases h : ty k = τ
  · simp [tyPart, h, Finset.sum_apply]
  · simp [tyPart, h, Finset.sum_apply]

theorem dualMap_eq {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    GlobalTheory.CompanionTheory.Ar.dualMap φ = Chart.dualMapR φ := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, Chart.dualMapR]

end GlobalTheory.CompanionTheory.Ar.Flat.AnHol

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.Flat.AnHol in

theorem anHol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (e : ∀ i : Fin FU.n, Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : Fin FU.n → ℂ) (Φ : CFn Xo c), (∀ i, LinearIndependent (𝓞 E) (e i)) → (∀ i, IsFlatAn Set.univ τ τ' σ Φ FU i (e i) (ρ i)) → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Xo.XF c) (vR : Fin D.p → (epsAt (under x) ⟶ Xo.univ.t.G)) (wR : Fin D.q → (epsAt (under x) ⟶ Xo.univ.t.G)) (m : ℕ) (B : Set (Fin m → ℂ)) (ψ : (Fin m → ℂ) → (R →+* ℂ)) (v : ∀ b, Vecs (spMap (ψ b) ≫ x) D.p) (w : ∀ b, Vecs (spMap (ψ b) ≫ x) D.q), IsOpen B → (∀ r, DifferentiableOn ℂ (fun b => ψ b r) B) → (∀ b ∈ B, IsFramed Set.univ τ σ (spMap (ψ b) ≫ x) (v b) (w b) ∧ (∀ a, (v b a).left = spMap (dualMap (ψ b)) ≫ (vR a).left) ∧ ∀ j, (w b j).left = spMap (dualMap (ψ b)) ≫ (wR j).left) → DifferentiableOn ℂ (fun b => Φ (spMap (ψ b) ≫ x) (v b) (w b)) B := by
  intro E _ _ _ H D l Xo c τ τ' σ g ty FU hty hrt hτ e ρ Φ he hflat R _ x vR wR m B ψ v w hB hψ hfr b₀ hb₀
  classical
  refine DifferentiableAt.differentiableWithinAt ?_
  have hev : ∀ t, DifferentiableAt ℂ (fun b => ψ b t) b₀ := fun t => (hψ t).differentiableAt (hB.mem_nhds hb₀)
  have h₁ : IsHolTo B (fun b => spMap (ψ b)) := GlobalTheory.ThetaValueCont.isHolTo_spMap hB ψ hψ
  have h₂ : IsHolTo B (fun b => spMap (ψ b) ≫ under x) :=
    GlobalTheory.HolHom.isHolTo_of_holAt hB fun z hz => (GlobalTheory.HolHom.holAt_of_isHolTo h₁ hz).comp _
  have hov : ∀ b ∈ B, (spMap (ψ b) ≫ under x) ≫ Xo.s =
      spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := fun b hb => by
    have h := (hfr b hb).1.1
    have h' := congrArg (· ≫ spMap (IntermediateField.inclusion c.le).toRingHom) h
    simp only [Category.assoc] at h'
    simp only [under, Category.assoc]
    rw [pullback.condition, h']
    simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ :=
    FU.lift m B (fun b => spMap (ψ b) ≫ under x) hB hov h₂ b₀ hb₀
  have hun : ∀ b ∈ B', under (spMap (ψ b) ≫ x) = FU.u i (P b) := fun b hb => by
    rw [hu b hb]; simp only [under, Category.assoc]
  have hc : ∀ a : 𝓞 E, (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) a =
      ComplexEmbedding.conjugate τ' (a : E) := by
    intro a
    have h1 : tauIn c (ComplexEmbedding.conjugate τ) a = tauIn c τ (H.bar a) := by
      apply Subtype.ext
      show ComplexEmbedding.conjugate τ (a : E) = τ ((H.bar a : 𝓞 E) : E)
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
      rfl
    show σ (tauIn c (ComplexEmbedding.conjugate τ) a) = _
    rw [h1, hτ, H.bar_eq, IsCMField.complexEmbedding_complexConj]
    rfl
  choose! xx hxx using fun b (hb : b ∈ B') =>
    (GlobalTheory.T.uniformised_eigen_frame_one E H D l Xo c τ τ' σ g ty FU hty hrt hτ i (e i) (P b) _ (v b) (w b) (he i) (hP.1 b hb)
      (hun b hb) (hfr b (hsub hb)).1).exists
  have hVW : ∀ b ∈ B', LinearIndependent ℂ (xx b).1 ∧
      (∀ z, tyPart ty τ' z ∈ Submodule.span ℂ (Set.range (xx b).1)) ∧ LinearIndependent ℂ (xx b).2.1 := by
    intro b hb
    obtain ⟨-, -, hv, hw⟩ := (hfr b (hsub hb)).1
    obtain ⟨V, hVd, hVl, hVs⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i (P b) _
      (σ.comp (tauIn c τ)) τ' D.p (v b) (hP.1 b hb) (hun b hb) hτ hv
    obtain ⟨W, hWd, hWl, -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i (P b) _
      _ (ComplexEmbedding.conjugate τ') D.q (w b) (hP.1 b hb) (hun b hb) hc hw
    have eV : (xx b).1 = V := funext fun a => (hVd a _).1 ((hxx b hb).1 a)
    have eW : (xx b).2.1 = W := funext fun a => (hWd a _).1 ((hxx b hb).2.1 a)
    rw [eV, eW]
    exact ⟨hVl, hVs, hWl⟩
  have hnb : ∀ᶠ b in 𝓝 b₀, b ∈ B' := hB'.mem_nhds hb'

  have hVd : ∀ a, DifferentiableAt ℂ (fun b => (xx b).1 a) b₀ := fun a =>
    GlobalTheory.HolFrameMatrix.differentiableAt_coord FU i (vR a).left ψ hB' hP (fun b => (xx b).1 a) (fun b hb => by
      have := (hxx b hb).1 a
      rw [(hfr b (hsub hb)).2.1 a, dualMap_eq] at this
      exact this) hb' hev
  have hWd : ∀ a, DifferentiableAt ℂ (fun b => (xx b).2.1 a) b₀ := fun a =>
    GlobalTheory.HolFrameMatrix.differentiableAt_coord FU i (wR a).left ψ hB' hP (fun b => (xx b).2.1 a) (fun b hb => by
      have := (hxx b hb).2.1 a
      rw [(hfr b (hsub hb)).2.2 a, dualMap_eq] at this
      exact this) hb' hev
  have hPd : ∀ n, DifferentiableAt ℂ (fun b => P b (e i n)) b₀ := fun n =>
    (hP.2 (e i n)).differentiableAt (hB'.mem_nhds hb')

  have hBd : ∀ j n, DifferentiableAt ℂ (fun b => (xx b).2.2.2.1 j n) b₀ := fun j n =>
    coef_differentiableAt (fun b => (xx b).2.1)
      (fun b n => tyPart ty (ComplexEmbedding.conjugate τ') (P b (e i n))) (fun b => (xx b).2.2.2.1) b₀ hWd
      (fun n => tyPart_differentiableAt ty _ _ b₀ (hPd n)) (hVW b₀ hb').2.2
      (by filter_upwards [hnb] with b hb n using (hxx b hb).2.2.1 n) j n
  obtain ⟨Hm, hHh, -, hHi⟩ := id (hP.1 b₀ hb').2.2.2.2
  obtain ⟨-, -, hd⟩ := GlobalTheory.T.period_hermitian_type_compatibility E H (FU.Di i) g ty (P b₀) Hm (hP.1 b₀ hb') hHh hHi
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    rw [(FU.sig i).1, (FU.sig i).2]; simp
  let S : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ :=
    Matrix.of fun m n => τ' (sesq (FU.Di i) (e i m) (e i n))
  have hS : S.det ≠ 0 := by
    have := hd 0 _ (e i) hcard (he i)
    have h2 : S = (Matrix.of fun m n => sesq (FU.Di i) (e i m) (e i n)).map τ' := rfl
    rw [h2, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ').2 this
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.2 hS
  have hFe : ∀ b ∈ B', (xx b).2.2.1 = (xx b).2.2.2.1 * S⁻¹ := fun b hb => by
    have : (xx b).2.2.1 * S = (xx b).2.2.2.1 := by
      ext j n
      rw [Matrix.mul_apply]
      exact (hxx b hb).2.2.2.1 j n
    rw [← this, Matrix.mul_nonsing_inv_cancel_right _ _ hSu]
  have hFd : ∀ j n, DifferentiableAt ℂ (fun b => (xx b).2.2.1 j n) b₀ := fun j n => by
    have : DifferentiableAt ℂ (fun b => ((xx b).2.2.2.1 * S⁻¹) j n) b₀ := by
      simp only [Matrix.mul_apply]
      exact DifferentiableAt.fun_sum fun k _ => (hBd j k).mul_const _
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [hnb] with b hb
    rw [hFe b hb]

  choose! A hA using fun b (hb : b ∈ B') (n : Fin D.p ⊕ Fin D.q) =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 ((hVW b hb).2.1 (P b (e i n)))
  let Am : (Fin m → ℂ) → Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ := fun b => Matrix.of fun k n => A b n k
  have hAd : ∀ k n, DifferentiableAt ℂ (fun b => Am b k n) b₀ := fun k n =>
    coef_differentiableAt (fun b => (xx b).1) (fun b n => tyPart ty τ' (P b (e i n))) Am b₀ hVd
      (fun n => tyPart_differentiableAt ty _ _ b₀ (hPd n)) (hVW b₀ hb').1
      (by filter_upwards [hnb] with b hb n using (hA b hb n).symm) k n
  have hexp : ∀ b ∈ B', ∀ (C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ) (a : Fin D.p),
      tyPart ty τ' (∑ m, C a m • P b (e i m)) = ∑ k, (Am b * C.transpose) k a • (xx b).1 k := by
    intro b hb C a
    rw [tyPart_sum_smul]
    simp_rw [← hA b hb, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [Am, mul_comm]
  obtain ⟨C₀, hC₀⟩ := (hxx b₀ hb').2.2.2.2.2.1
  have hM0 : Am b₀ * C₀.transpose = 1 := by
    ext k a
    have h1 := hexp b₀ hb' C₀ a
    rw [hC₀ a] at h1
    have h2 := Fintype.linearIndependent_iff.1 (hVW b₀ hb').1
      (fun k => (Am b₀ * C₀.transpose) k a - (1 : Matrix (Fin D.p) (Fin D.p) ℂ) k a)
      (by simp [sub_smul, Finset.sum_sub_distrib, ← h1, Matrix.one_apply]) k
    exact sub_eq_zero.1 h2
  let M : (Fin m → ℂ) → Matrix (Fin D.p) (Fin D.p) ℂ := fun b => Am b * C₀.transpose
  have hMd : ∀ k a, DifferentiableAt ℂ (fun b => M b k a) b₀ := fun k a => by
    simp only [M, Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun n _ => (hAd k n).mul_const _
  have hM0' : (M b₀).det ≠ 0 := by simp [M, hM0]
  have hMe := (fcHolo_det_differentiableAt M b₀ hMd).continuousAt.eventually_ne hM0'
  have hMi := inv_differentiableAt M b₀ hMd hM0'
  let Cb : (Fin m → ℂ) → Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ := fun b => (C₀.transpose * (M b)⁻¹).transpose
  have hCd : ∀ a n, DifferentiableAt ℂ (fun b => Cb b a n) b₀ := fun a n => by
    simp only [Cb, Matrix.transpose_apply, Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun k _ => (hMi k a).const_mul _
  have hlift : ∀ᶠ b in 𝓝 b₀, b ∈ B' ∧ ∀ a, tyPart ty τ' (∑ m, Cb b a m • P b (e i m)) = (xx b).1 a := by
    filter_upwards [hnb, hMe] with b hb hdet
    refine ⟨hb, fun a => ?_⟩
    have h1 : Am b * (Cb b).transpose = 1 := by
      simp only [Cb, Matrix.transpose_transpose]
      rw [← Matrix.mul_assoc]
      exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)
    rw [hexp b hb, h1]
    simp [Matrix.one_apply]

  let Dt : (Fin m → ℂ) → ℂ := fun b => (Matrix.fromRows (Cb b) (xx b).2.2.1).det
  have hDd : DifferentiableAt ℂ Dt b₀ := by
    refine fcHolo_det_differentiableAt (fun b => Matrix.fromRows (Cb b) (xx b).2.2.1) b₀ fun r n => ?_
    rcases r with r | r
    · simpa using hCd r n
    · simpa using hFd r n
  have hDe : ∀ᶠ b in 𝓝 b₀, b ∈ B' ∧ Dt b = (xx b).2.2.2.2 := by
    filter_upwards [hlift] with b hb
    exact ⟨hb.1, (hxx b hb.1).2.2.2.2.2.2 _ hb.2⟩
  have hD0 : Dt b₀ ≠ 0 := by
    rw [hDe.self_of_nhds.2]
    exact (hxx b₀ hb').2.2.2.2.1
  have hq : DifferentiableAt ℂ (fun b => ρ i / Dt b) b₀ := by
    simp only [div_eq_mul_inv]
    exact hDd.fun_inv hD0 |>.const_mul _
  refine hq.congr_of_eventuallyEq ?_
  filter_upwards [hlift, hDe] with b hb hb'
  have hne : Dt b ≠ 0 := by
    rw [hb'.2]
    exact (hxx b hb.1).2.2.2.2.1
  have hfl := hflat i (P b) _ (v b) (w b) (xx b).1 (xx b).2.1 (Cb b) (xx b).2.2.1 (xx b).2.2.2.1 (hP.1 b hb.1)
    (hun b hb.1) (hfr b (hsub hb.1)).1 (hxx b hb.1).1 (hxx b hb.1).2.1 hb.2 (hxx b hb.1).2.2.1
    (hxx b hb.1).2.2.2.1
  rw [eq_div_iff hne]
  exact hfl

end GlobalTheory.CompanionTheory.Ar.Flat

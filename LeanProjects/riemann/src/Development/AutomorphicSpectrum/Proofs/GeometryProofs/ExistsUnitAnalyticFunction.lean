import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFramesAllStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFramesTwoStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFrameTwoStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFrameOneStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodEigenFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.Unit

open Matrix

variable {p q : ℕ} {g : ℕ}

theorem det_fromRows_mul_top (A : Matrix (Fin p) (Fin p) ℂ) (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ)
    (F : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) :
    (Matrix.fromRows (A * C) F).det = A.det * (Matrix.fromRows C F).det := by
  have h : Matrix.fromRows (A * C) F = Matrix.fromBlocks A 0 0 1 * Matrix.fromRows C F := by
    ext (a | b) m <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  rw [h, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem det_fromRows_mul_bot (B : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ)
    (F : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) :
    (Matrix.fromRows C (B * F)).det = B.det * (Matrix.fromRows C F).det := by
  have h : Matrix.fromRows C (B * F) = Matrix.fromBlocks 1 0 0 B * Matrix.fromRows C F := by
    ext (a | b) m <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  rw [h, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem det_chg (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Pe Tc : Fin p ⊕ Fin q → Fin g → ℂ)
    (S : Fin p ⊕ Fin q → Fin p ⊕ Fin q → ℂ) (V V' : Fin p → Fin g → ℂ) (W W' : Fin q → Fin g → ℂ)
    (Fm Fm' B₀ B' : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) (d d' : ℂ)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ)
    (hV : ∀ a, V' a = ∑ b, A a b • V b) (hW : ∀ j, W' j = ∑ k, B j k • W k)
    (hWi : LinearIndependent ℂ W) (hWi' : LinearIndependent ℂ W')
    (k3 : ∀ n, Tc n = ∑ j, B₀ j n • W j) (l3 : ∀ n, Tc n = ∑ j, B' j n • W' j)
    (l4 : ∀ j n, ∑ m, Fm' j m * S m n = B' j n) (hd' : d' ≠ 0)
    (k6 : ∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, ∀ a, T (∑ m, C a m • Pe m) = V a)
    (l7 : ∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (∀ a, T (∑ m, C a m • Pe m) = V' a) →
      (Matrix.fromRows C Fm').det = d')
    (hu : ∀ (F₂ : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) (d₂ : ℂ), (∀ j n, ∑ m, F₂ j m * S m n = B₀ j n) → d₂ ≠ 0 →
      (∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (∀ a, T (∑ m, C a m • Pe m) = V a) →
        (Matrix.fromRows C F₂).det = d₂) → d₂ = d) :
    d * A.det = d' * B.det := by
  have lift : ∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (∀ a, T (∑ m, C a m • Pe m) = V a) →
      ∀ a, T (∑ m, (A * C) a m • Pe m) = V' a := by
    intro C hC a
    have : ∑ m, (A * C) a m • Pe m = ∑ b, A a b • ∑ m, C b m • Pe m := by
      simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
      exact Finset.sum_comm
    rw [this, map_sum, hV a]
    exact Finset.sum_congr rfl fun b _ => by rw [map_smul, hC b]
  obtain ⟨C₀, hC₀⟩ := k6
  have hA : A.det ≠ 0 := by
    intro h0
    have := l7 _ (lift C₀ hC₀)
    rw [det_fromRows_mul_top, h0, zero_mul] at this
    exact hd' this.symm
  have hB : B.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hcB⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    apply hc
    have hz : ∑ j, c j • W' j = 0 := by
      simp only [hW, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [← Finset.sum_smul]
      have := congrFun hcB k
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
      rw [this, zero_smul]
    funext j
    exact Fintype.linearIndependent_iff.1 hWi' c hz j
  have hB₀ : ∀ k n, B₀ k n = ∑ j, B j k * B' j n := by
    intro k n
    have hz : ∑ k, (B₀ k n - ∑ j, B j k * B' j n) • W k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← k3 n]
      rw [sub_eq_zero, l3 n]
      simp only [hW, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [_root_.mul_comm]
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hWi _ hz k)
  have hfin := hu (Bᵀ * Fm') (B.det * d' / A.det) ?_ (div_ne_zero (mul_ne_zero hB hd') hA) ?_
  · rw [← hfin]; field_simp
  · intro j n
    rw [hB₀]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, ← l4]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum, _root_.mul_assoc]
  · intro C hC
    have h1 := l7 _ (lift C hC)
    rw [det_fromRows_mul_top] at h1
    rw [det_fromRows_mul_bot, Matrix.det_transpose, ← h1]
    field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.Unit

namespace GlobalTheory.CompanionTheory.Ar.Flat.Unit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l}

theorem isDerivAt0_of_isComb {σK : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σK ty)
    (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (x : Sp ℂ ⟶ Xo.X)
    (hx : x = FU.u i P) {n : ℕ} (a : Fin n → ℂ) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G))
    (w : epsAt x ⟶ Xo.univ.t.G) (V : Fin n → Fin g → ℂ)
    (hV : ∀ k, IsDerivAt0 (fun z => (FU.ex i P z).left) (V k) (v k).left) (h : IsComb a v w) :
    IsDerivAt0 (fun z => (FU.ex i P z).left) (∑ k, a k • V k) w.left := by
  subst hx
  exact (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H D l Xo σK g ty FU i P hP n (fun k => (v k).left) V hV a w.left).1
    ((EigDir.isComb_iff_isCombAt _ a v w).1 h)

theorem tauIn_conj {c : Coeff l} {τ τ' : E →+* ℂ} {σ : c.F →+* ℂ}
    (hτ : ∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) (a : 𝓞 E) :
    (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) a = ComplexEmbedding.conjugate τ' (a : E) := by
  have h1 : tauIn c (ComplexEmbedding.conjugate τ) a = tauIn c τ (H.bar a) := by
    apply Subtype.ext
    show ComplexEmbedding.conjugate τ (a : E) = τ ((H.bar a : 𝓞 E) : E)
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
    rfl
  show σ (tauIn c (ComplexEmbedding.conjugate τ) a) = _
  rw [h1, hτ, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  rfl

theorem isLinearMap_tyPart {g : ℕ} (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ) : IsLinearMap ℂ (tyPart ty τ) := by
  constructor
  · intro a b; funext k; simp only [tyPart, Pi.add_apply]; split_ifs <;> simp
  · intro a b; funext k; simp only [tyPart, Pi.smul_apply]; split_ifs <;> simp

theorem chg_of_isFlatAn {c : Coeff l} {τ τ' : E →+* ℂ} {σ : c.F →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    (hT : IsTypeFn H D.p D.q ty) (hrt : τ' (H.rt : E) = H.rt0) (hτ : ∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E))
    (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (he : LinearIndependent (𝓞 E) e)
    (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (y : Sp ℂ ⟶ Xo.XF c)
    (hy : under y = FU.u i P) (v v' : Vecs y D.p) (w w' : Vecs y D.q)
    (A : Matrix (Fin D.p) (Fin D.p) ℂ) (Bm : Matrix (Fin D.q) (Fin D.q) ℂ)
    (hf : IsFramed Set.univ τ σ y v w) (hf' : IsFramed Set.univ τ σ y v' w')
    (hA : ∀ a, IsComb (A a) v (v' a)) (hB : ∀ j, IsComb (Bm j) w (w' j))
    (Φ : CFn Xo c) (ρ : ℂ) (hΦ : IsFlatAn Set.univ τ τ' σ Φ FU i e ρ) :
    Φ y v' w' * A.det = Φ y v w * Bm.det := by
  obtain ⟨⟨V, W, Fm, B₀, d⟩, ⟨k1, k2, k3, k4, k5, ⟨C, hC⟩, k7⟩, hu⟩ :=
    GlobalTheory.T.uniformised_eigen_frame_one E H D l Xo c τ τ' σ g ty FU hT hrt hτ i e P y v w he hP hy hf
  obtain ⟨⟨V', W', Fm', B', d'⟩, ⟨l1, l2, l3, l4, l5, ⟨C', hC'⟩, l7⟩, -⟩ :=
    GlobalTheory.T.uniformised_eigen_frame_one E H D l Xo c τ τ' σ g ty FU hT hrt hτ i e P y v' w' he hP hy hf'
  have f1 : Φ y v w * d = ρ := by
    have := hΦ P y v w V W C Fm B₀ hP hy hf k1 k2 hC k3 k4
    rwa [k7 C hC] at this
  have f2 : Φ y v' w' * d' = ρ := by
    have := hΦ P y v' w' V' W' C' Fm' B' hP hy hf' l1 l2 hC' l3 l4
    rwa [l7 C' hC'] at this
  obtain ⟨V₀, hV₀, -, -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y) _ τ' D.p v' hP hy hτ hf'.2.2.1
  obtain ⟨W₀, hW₀, hWi, -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y) _
    (ComplexEmbedding.conjugate τ') D.q w hP hy (tauIn_conj hτ) hf.2.2.2
  obtain ⟨W₁, hW₁, hWi', -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y) _
    (ComplexEmbedding.conjugate τ') D.q w' hP hy (tauIn_conj hτ) hf'.2.2.2
  have eW : W = W₀ := funext fun j => (hW₀ j _).1 (k2 j)
  have eW' : W' = W₁ := funext fun j => (hW₁ j _).1 (l2 j)
  have hV : ∀ a, V' a = ∑ b, A a b • V b := fun a =>
    ((hV₀ a _).1 (l1 a)).trans ((hV₀ a _).1 (isDerivAt0_of_isComb FU i P hP _ hy _ v _ V k1 (hA a))).symm
  have hW : ∀ j, W' j = ∑ k, Bm j k • W k := fun j =>
    ((hW₁ j _).1 (l2 j)).trans ((hW₁ j _).1 (isDerivAt0_of_isComb FU i P hP _ hy _ w _ W k2 (hB j))).symm
  have key := det_chg ((isLinearMap_tyPart ty τ').mk' _) (fun m => P (e m))
    (fun n => tyPart ty (ComplexEmbedding.conjugate τ') (P (e n)))
    (fun m n => τ' (sesq (FU.Di i) (e m) (e n))) V V' W W' Fm Fm' B₀ B' d d' A Bm hV hW
    (eW ▸ hWi) (eW' ▸ hWi') k3 l3 l4 l5 ⟨C, hC⟩ l7
    (fun F₂ d₂ h4 h5 h7 => congrArg (fun x => x.2.2.2.2) (hu (V, W, F₂, B₀, d₂) ⟨k1, k2, k3, h4, h5, ⟨C, hC⟩, h7⟩))
  apply mul_right_cancel₀ (mul_ne_zero k5 l5)
  linear_combination (A.det * d) * f2 - (Bm.det * d') * f1 + ρ * key

end GlobalTheory.CompanionTheory.Ar.Flat.Unit

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem anUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∃ Φ : CFn Xo c, IsUnitAn τ σ Φ ∧ ∀ i : Fin FU.n, ∃ (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), ρ ≠ 0 ∧ LinearIndependent (𝓞 E) e ∧ IsFlatAn Set.univ τ τ' σ Φ FU i e ρ := by
  intro E _ _ _ H D l Xo c τ τ' σ g ty FU hT hrt hτ
  have hrank : ∀ i, ∃ e : Fin D.p ⊕ Fin D.q → (FU.Di i).La, LinearIndependent (𝓞 E) e := by
    intro i
    have hr : D.p + D.q ≤ Module.finrank (𝓞 E) (FU.Di i).La := by
      rw [(FU.Di i).rank, (FU.sig i).1, (FU.sig i).2]
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hr
    exact ⟨f ∘ finSumFinEquiv, hf.comp _ finSumFinEquiv.injective⟩
  choose e he using hrank
  choose t ht hN using fun i => GlobalTheory.T.uniformised_eigen_frame_two E H D l Xo c τ τ' σ g ty FU hT hrt hτ i (e i) (he i)
  let ρ : Fin FU.n → ℂ := fun i => (((Real.sqrt (t i))⁻¹ : ℝ) : ℂ)
  have hs : ∀ i, Real.sqrt (t i) ≠ 0 := fun i => (Real.sqrt_pos.2 (ht i)).ne'
  have hρ : ∀ i, ρ i ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (inv_ne_zero (hs i))
  have hρt : ∀ i, ‖ρ i‖ ^ 2 * t i = 1 := by
    intro i
    have h1 : ‖ρ i‖ = (Real.sqrt (t i))⁻¹ := by
      show ‖(((Real.sqrt (t i))⁻¹ : ℝ) : ℂ)‖ = _
      rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    rw [h1, inv_pow, Real.sq_sqrt (ht i).le, inv_mul_cancel₀ (ht i).ne']
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.uniformised_eigen_frames_all E H D l Xo c τ τ' σ g ty FU hT hrt hτ e ρ he
  have hloc : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap σ →
      ∃ (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)), IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P := by
    intro y hy
    obtain ⟨i, P, hP, hu⟩ := FU.onto (under y) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy]
      simp only [spMap, ← Spec.map_comp]
      rfl)
    exact ⟨i, P, hP, hu.symm⟩
  refine ⟨Φ, { ne := ?_, chg := ?_, norm := ?_, hol := ?_ }, fun i => ⟨e i, ρ i, hρ i, he i, hΦ i⟩⟩
  · intro y v w hf h0
    obtain ⟨i, P, hP, hy⟩ := hloc y hf.1
    obtain ⟨⟨V, W, Fm, B₀, d⟩, ⟨k1, k2, k3, k4, k5, ⟨C, hC⟩, k7⟩, -⟩ :=
      GlobalTheory.T.uniformised_eigen_frame_one E H D l Xo c τ τ' σ g ty FU hT hrt hτ i (e i) P y v w (he i) hP hy hf
    have := hΦ i P y v w V W C Fm B₀ hP hy hf k1 k2 hC k3 k4
    rw [h0, zero_mul] at this
    exact hρ i this.symm
  · intro y v w v' w' A B hf hf' hA hB
    obtain ⟨i, P, hP, hy⟩ := hloc y hf.1
    exact Unit.chg_of_isFlatAn FU hT hrt hτ i (e i) (he i) P hP y hy v v' w w' A B hf hf' hA hB Φ (ρ i) (hΦ i)
  · intro y v w Γ Δ hf hΓ hΔ
    obtain ⟨i, P, hP, hy⟩ := hloc y hf.1
    have := hN i (ρ i) Φ (hΦ i) P y v w Γ Δ hP hy hf hΓ hΔ
    rw [this, hρt i, _root_.one_mul]
  · intro R _ x vR wR m B ψ v w h1 h2 h3
    exact GlobalTheory.T.uniformised_eigen_frames_two E H D l Xo c τ τ' σ g ty FU hT hrt hτ e ρ Φ he hΦ R x vR wR m B ψ v w h1 h2 h3

end GlobalTheory.CompanionTheory.Ar.Flat

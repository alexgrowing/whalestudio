import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodHermitianTypeCompatibilityStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodEigenFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianPeriodLinearAlgebraStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Flat.Ratio

open Matrix

local notation "HF" => ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm

theorem hf_sum_left {g : ℕ} {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ)
    (c : κ → ℂ) (V : κ → Fin g → ℂ) (w : Fin g → ℂ) :
    HF Hm (∑ i, c i • V i) w = ∑ i, c i * HF Hm (V i) w := by
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, sum_dotProduct, smul_dotProduct]

theorem hf_sum_right {g : ℕ} {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ)
    (c : κ → ℂ) (V : κ → Fin g → ℂ) (z : Fin g → ℂ) :
    HF Hm z (∑ i, c i • V i) = ∑ i, star (c i) * HF Hm z (V i) := by
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_sum, Matrix.mulVec_sum, dotProduct_sum,
    Matrix.mulVec_smul, dotProduct_smul]

theorem exists_row {R M I : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Fintype I]
    (e : I → M) (he : LinearIndependent R e) (hc : Fintype.card I = Module.finrank R M) (x : M) :
    ∃ (n : R) (c : I → R), n ≠ 0 ∧ n • x = ∑ m, c m • e m := by
  classical
  have hnot : ¬ LinearIndependent R (fun o : Option I => o.elim x e) := by
    intro h
    have := h.fintype_card_le_finrank
    rw [Fintype.card_option, hc] at this
    omega
  obtain ⟨c, hsum, o, ho⟩ := Fintype.not_linearIndependent_iff.1 hnot
  rw [Fintype.sum_option] at hsum
  simp only [Option.elim] at hsum
  have hn : c none ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_add] at hsum
    have := Fintype.linearIndependent_iff.1 he (fun m => c (some m)) hsum
    cases o with
    | none => exact ho h0
    | some m => exact ho (this m)
  refine ⟨c none, fun m => - c (some m), hn, ?_⟩
  simp only [neg_smul, Finset.sum_neg_distrib]
  exact eq_neg_of_add_eq_zero_left hsum

theorem lifts_change {p q g : ℕ} (T T' : (Fin g → ℂ) → (Fin g → ℂ)) (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ)
    (π π₀ : Fin p ⊕ Fin q → Fin g → ℂ) (S S₀ Tm : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hT : IsLinearMap ℂ T) (hH : Hm.IsHermitian)
    (hHp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) (hS : S.det ≠ 0) (hS₀ : S₀.det ≠ 0)
    (hV : LinearIndependent ℂ V) (hW : LinearIndependent ℂ W)
    (hVs : ∀ n, T (π n) ∈ Submodule.span ℂ (Set.range V)) (hWs : ∀ n, T' (π n) ∈ Submodule.span ℂ (Set.range W))
    (hVs₀ : ∀ n, T (π₀ n) ∈ Submodule.span ℂ (Set.range V)) (hWs₀ : ∀ n, T' (π₀ n) ∈ Submodule.span ℂ (Set.range W))
    (hF : ∀ m n, hermForm Hm (T (π m)) (T (π n)) - star (hermForm Hm (T' (π m)) (T' (π n))) = 2 * Complex.I * S m n)
    (hF₀ : ∀ m n, hermForm Hm (T (π₀ m)) (T (π₀ n)) - star (hermForm Hm (T' (π₀ m)) (T' (π₀ n))) = 2 * Complex.I * S₀ m n)
    (hc : ∀ m, T (π m) = ∑ k, Tm m k • T (π₀ k)) (hc' : ∀ m, T' (π m) = ∑ k, star (Tm m k) • T' (π₀ k)) :
    Tm.det ≠ 0 ∧ ∃ (C C₀ : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ) (Fm B Fm₀ B₀ : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ),
      (∀ a, T (∑ m, C a m • π m) = V a) ∧ (∀ n, T' (π n) = ∑ j, B j n • W j) ∧ (∀ j n, ∑ m, Fm j m * S m n = B j n) ∧
      (∀ a, T (∑ m, C₀ a m • π₀ m) = V a) ∧ (∀ n, T' (π₀ n) = ∑ j, B₀ j n • W j) ∧
      (∀ j n, ∑ m, Fm₀ j m * S₀ m n = B₀ j n) ∧ (Matrix.fromRows C Fm).det ≠ 0 ∧
      (Matrix.fromRows C₀ Fm₀).det = (Matrix.fromRows C Fm).det * Tm.det := by
  obtain ⟨⟨Fm, B, d⟩, ⟨h1, h2, h3, ⟨C, hC⟩, h5⟩, -⟩ :=
    GlobalTheory.T.hermitian_period_linear_algebra p q g T T' V W π S Hm hT hH hHp hS hV hW hVs hWs hF
  obtain ⟨⟨Fm₀, B₀, d₀⟩, ⟨k1, k2, k3, -, k5⟩, -⟩ :=
    GlobalTheory.T.hermitian_period_linear_algebra p q g T T' V W π₀ S₀ Hm hT hH hHp hS₀ hV hW hVs₀ hWs₀ hF₀
  simp only at h1 h2 h3 hC h5 k1 k2 k3 k5
  have lin : ∀ (c : Fin p ⊕ Fin q → ℂ) (x : Fin p ⊕ Fin q → Fin g → ℂ), T (∑ m, c m • x m) = ∑ m, c m • T (x m) := by
    intro c x
    have := map_sum (hT.mk' T) (fun m => c m • x m) Finset.univ
    simpa using this

  have hmat : S = Tm * S₀ * Tmᴴ := by
    ext m n
    have e0 := hF m n
    rw [hc m, hc n, hc' m, hc' n] at e0
    simp only [hf_sum_left, hf_sum_right, star_sum, star_mul', star_star, Finset.mul_sum] at e0
    have e1 : (2 * Complex.I) * (Tm * S₀ * Tmᴴ) m n = 2 * Complex.I * S m n := by
      rw [← e0, ← Finset.sum_sub_distrib]
      simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Matrix.conjTranspose_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := hF₀ j i
      linear_combination (- (Tm m j * star (Tm n i))) * this
    have h2I : (2 * Complex.I) ≠ 0 := by simp
    exact (mul_left_cancel₀ h2I e1).symm
  have hdetH : Tmᴴ.det = star Tm.det := Matrix.det_conjTranspose Tm
  have hTdet : Tm.det ≠ 0 := by
    intro h0
    apply hS
    rw [hmat, Matrix.det_mul, Matrix.det_mul, h0]
    simp
  have hTH : Tmᴴ.det ≠ 0 := by
    rw [hdetH]; simpa using hTdet
  have hBm : B = B₀ * Tmᴴ := by
    ext j n
    have e0 : ∑ j, (B j n - (B₀ * Tmᴴ) j n) • W j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← h1 n, hc' n, sub_eq_zero]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [k1 k, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, mul_comm]
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hW _ e0 j)
  have hFS : Fm * S = B := by
    ext j n
    simpa [Matrix.mul_apply] using h2 j n
  have hFS₀ : Fm₀ * S₀ = B₀ := by
    ext j n
    simpa [Matrix.mul_apply] using k2 j n
  have hFm : Fm * Tm = Fm₀ := by
    have a1 : (Fm * Tm * S₀) * Tmᴴ = (Fm₀ * S₀) * Tmᴴ := by
      rw [hFS₀, ← hBm, ← hFS, hmat]
      simp only [Matrix.mul_assoc]
    have iTH : IsUnit Tmᴴ.det := isUnit_iff_ne_zero.2 hTH
    have iS : IsUnit S₀.det := isUnit_iff_ne_zero.2 hS₀
    have a2 : Fm * Tm * S₀ = Fm₀ * S₀ := by
      have := congrArg (· * Tmᴴ⁻¹) a1
      simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ iTH] using this
    have := congrArg (· * S₀⁻¹) a2
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ iS] using this
  have hC₀ : ∀ a, T (∑ m, (C * Tm) a m • π₀ m) = V a := by
    intro a
    rw [← hC a, lin, lin]
    simp only [hc, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
  have hd : d ≠ 0 := h3
  have hd' : (Matrix.fromRows C Fm).det = d := h5 C hC
  refine ⟨hTdet, C, C * Tm, Fm, B, Fm₀, B₀, hC, h1, h2, hC₀, k1, k2, by rw [hd']; exact hd, ?_⟩
  rw [← hFm, ← Matrix.fromRows_mul, Matrix.det_mul]

end GlobalTheory.CompanionTheory.Ar.Flat.Ratio

namespace GlobalTheory.CompanionTheory.Ar.Flat.Ratio

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem tyPart_add {g : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) : IsLinearMap ℂ (tyPart ty σ) := by
  constructor
  · intro a b; funext k; simp only [tyPart, Pi.add_apply]; split_ifs <;> simp
  · intro a b; funext k; simp only [tyPart, Pi.smul_apply]; split_ifs <;> simp

theorem tyPart_row {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    (σ : E →+* ℂ) {I : Type} [Fintype I] (e : I → D.La) (x : D.La) (n : 𝓞 E) (c : I → 𝓞 E) (hn : n ≠ 0)
    (h : n • x = ∑ m, c m • e m) :
    tyPart ty σ (P x) = ∑ m, (σ (c m : E) / σ (n : E)) • tyPart ty σ (P (e m)) := by
  have hσ : σ (n : E) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hn
  funext k
  simp only [tyPart, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with hk
  · have e1 := congrFun (congrArg P h) k
    rw [hP.1, map_sum, Finset.sum_apply] at e1
    simp only [hP.1, hk] at e1
    rw [eq_comm, ← mul_right_inj' hσ, e1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    field_simp
  · simp

end GlobalTheory.CompanionTheory.Ar.Flat.Ratio

open GlobalTheory.CompanionTheory.Ar.Flat.Ratio in

theorem GlobalTheory.CompanionTheory.Ar.Flat.flatGen_ratio_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ φ₀ : FrameFn Xo c) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → IsFlatGen U τ φ FU i → IsFlatGen U τ φ₀ FU i → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → ∃ a : ℂ, ∀ y v w, IsFramed U τ (algebraMap c.F ℂ) y v w → φ ℂ y v w = a * φ₀ ℂ y v w := by
  intro E _ _ _ H D l Xo c U τ φ φ₀ g ty FU i _ h1 h2 hU
  obtain ⟨e, ρ, he, hc⟩ := h1.flat
  obtain ⟨e₀, ρ₀, he₀, hc₀⟩ := h2.flat
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    rw [(FU.sig i).1, (FU.sig i).2]; simp
  have hcard' : Fintype.card (Fin D.p ⊕ Fin D.q) = Module.finrank (𝓞 E) (FU.Di i).La := by
    rw [hcard, (FU.Di i).rank]
  haveI := (FU.Di i).fin
  choose n cf hn hrow using fun m => exists_row e₀ he₀ hcard' (e m)
  set Tm : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ :=
    Matrix.of fun m k => τ (cf m k : E) / τ (n m : E) with hTm
  refine ⟨ρ * Tm.det / ρ₀, fun y v w hfr => ?_⟩
  obtain ⟨P, hP, hy⟩ := hU y hfr.1 hfr.2.1
  have hfv := hfr.2.2.1
  have hfw := hfr.2.2.2
  obtain ⟨V, hVd, hVl, hVs⟩ := GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) _ τ D.p v hP hy (fun a => rfl) hfv
  obtain ⟨W, hWd, hWl, hWs⟩ := GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) _ (ComplexEmbedding.conjugate τ) D.q w hP hy
    (fun a => rfl) hfw
  obtain ⟨Hm, hHh, hHp, hHi⟩ := id hP.2.2.2.2
  obtain ⟨-, hs, hd⟩ := GlobalTheory.T.period_hermitian_type_compatibility E H (FU.Di i) g ty P Hm hP hHh hHi
  have hSdet : ∀ e' : Fin D.p ⊕ Fin D.q → (FU.Di i).La, LinearIndependent (𝓞 E) e' →
      (Matrix.of fun m n => τ (sesq (FU.Di i) (e' m) (e' n))).det ≠ 0 := by
    intro e' he'
    have := hd 0 _ e' hcard he'
    have h2 : (Matrix.of fun m n => τ (sesq (FU.Di i) (e' m) (e' n))) =
        (Matrix.of fun m n => sesq (FU.Di i) (e' m) (e' n)).map τ := rfl
    rw [h2, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ).2 this
  obtain ⟨hTdet, C, C₀, Fm, B, Fm₀, B₀, a1, a2, a3, b1, b2, b3, hdet, hrel⟩ :=
    lifts_change (tyPart ty τ) (tyPart ty (ComplexEmbedding.conjugate τ)) V W (fun m => P (e m)) (fun m => P (e₀ m)) _ _ Tm Hm
      (tyPart_add ty τ) hHh hHp (hSdet e he) (hSdet e₀ he₀) hVl hWl (fun _ => hVs _) (fun _ => hWs _) (fun _ => hVs _)
      (fun _ => hWs _) (fun m n => hs τ _ _) (fun m n => hs τ _ _)
      (fun m => tyPart_row hP τ e₀ (e m) (n m) (cf m) (hn m) (hrow m))
      (fun m => by
        rw [tyPart_row hP (ComplexEmbedding.conjugate τ) e₀ (e m) (n m) (cf m) (hn m) (hrow m)]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [hTm, ComplexEmbedding.conjugate_coe_eq])
  have c1 := hc P y v w V W C Fm B hP hy hfr (fun a => (hVd a _).2 rfl) (fun j => (hWd j _).2 rfl) a1 a2 a3
  have c2 := hc₀ P y v w V W C₀ Fm₀ B₀ hP hy hfr (fun a => (hVd a _).2 rfl) (fun j => (hWd j _).2 rfl) b1 b2 b3
  have hφ₀ : φ₀ ℂ y v w ≠ 0 := h2.line.ne ℂ _ y v w hfr
  have hρ₀ : ρ₀ ≠ 0 := by
    rw [← c2, hrel]
    exact mul_ne_zero hφ₀ (mul_ne_zero hdet hTdet)
  rw [← c1, ← c2, hrel]
  field_simp

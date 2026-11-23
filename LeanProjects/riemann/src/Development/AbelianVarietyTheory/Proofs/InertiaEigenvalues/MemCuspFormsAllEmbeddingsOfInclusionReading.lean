import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCuspOfVanishOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedIsSecZeroKeySection
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralDetSubOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RdIndepOfLawsM
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.ExtEmbEquivComp
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank

noncomputable section

namespace GlobalTheory.CuspAllEmb

section Analytic

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem isSec_mul {la la' : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) (hQ : X.IsSec la' Q) :
    X.IsSec (la + la') (P * Q) := by
  refine ⟨hP.1.mul hQ.1, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have hne : ∀ τ i, b τ i i ≠ 0 := fun τ i => by
      have hdet := (hb τ).1
      rw [Matrix.det_of_upperTriangular (M := mat b τ) (fun a c hac => (hb τ).2 a c hac)] at hdet
      exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
    have e : bchar (la + la') b = bchar la b * bchar la' b := by
      simp only [bchar, Pi.add_apply, zpow_add₀ (hne _ _), Finset.prod_mul_distrib]
    rw [Pi.mul_apply, Pi.mul_apply, hP.2.1 x hx b hb, hQ.2.1 x hx b hb, e]
    ring
  · rw [Pi.mul_apply, Pi.mul_apply, hP.2.2 γ hγ x hx, hQ.2.2 γ hγ x hx, X.χ_add _ _ γ hγ]
    ring

theorem fj_mul (hf : 1 < Module.finrank ℚ E / 2) {la la' : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    (hQ : X.IsSec la' Q) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.fj (la + la') ξ 0 (P * Q) x = X.fj la ξ 0 P x * X.fj la' ξ 0 Q x := by
  have mP := GlobalTheory.CuspFrom.isModerate X hf hP
  have mQ := GlobalTheory.CuspFrom.isModerate X hf hQ
  have hs := coefficientConvolution_holds (E := E) r X la la' P Q hP hQ mP mQ ξ hξ x hx 0
  obtain ⟨C, A, hC⟩ := mP
  obtain ⟨C', A', hC'⟩ := mQ
  have h1 : HasSum (fun ν' : X.Ψ → ℝ => X.fj la ξ ν' P x * X.fj la' ξ (0 - ν') Q x)
      (X.fj la ξ 0 P x * X.fj la' ξ (0 - 0) Q x) := by
    refine hasSum_single 0 fun ν' hν => ?_
    by_cases a1 : X.fj la ξ ν' P x = 0
    · rw [a1, zero_mul]
    by_cases a2 : X.fj la' ξ (0 - ν') Q x = 0
    · rw [a2, mul_zero]
    refine absurd (funext fun τ => ?_) hν
    have b1 := (moderateCoefficientPositivity_holds (E := E) r X la P C A hP hC).1 ξ hξ ν' x hx a1 τ
    have b2 := (moderateCoefficientPositivity_holds (E := E) r X la' Q C' A' hQ hC').1 ξ hξ (0 - ν') x hx a2 τ
    simp only [Pi.sub_apply, Pi.zero_apply] at b2 ⊢
    linarith
  rw [sub_zero] at h1
  exact hs.unique h1

theorem ss_mul (hf : 1 < Module.finrank ℚ E / 2) {la la' : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la)
    (hQ : X.IsSec la' Q) : P * Q ∈ X.SS (la + la') := by
  have hs : X.IsSec (la + la') (P * Q) := isSec_mul X hP.1.1 hQ
  refine GlobalTheory.FJZero.mem_SS_of_isModerate X _ _ hs (GlobalTheory.CuspFrom.isModerate X hf hs) fun ξ hξ x hx => ?_
  rw [fj_mul X hf hP.1.1 hQ hξ hx, hP.2 ξ hξ x hx, zero_mul]

theorem isSec_pow {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) (n : ℕ) :
    X.IsSec ((n + 1) • la) (P ^ (n + 1)) := by
  induction n with
  | zero => simpa using hP
  | succ n ih => rw [succ_nsmul, pow_succ]; exact isSec_mul X ih hP

theorem ss_of_pow (hf : 1 < Module.finrank ℚ E / 2) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) (n : ℕ)
    (h : P ^ (n + 1) ∈ X.SS ((n + 1) • la)) : P ∈ X.SS la := by
  refine GlobalTheory.FJZero.mem_SS_of_isModerate X _ _ hP (GlobalTheory.CuspFrom.isModerate X hf hP) fun ξ hξ x hx => ?_
  have key : ∀ m : ℕ, X.fj ((m + 1) • la) ξ 0 (P ^ (m + 1)) x = X.fj la ξ 0 P x ^ (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [succ_nsmul, pow_succ, fj_mul X hf (isSec_pow X hP m) hP hξ hx, ih, ← pow_succ]
  have := h.2 ξ hξ x hx
  rw [key] at this
  exact pow_eq_zero_iff (Nat.succ_ne_zero n) |>.1 this

theorem ss_of_finite_ratio (hf : 1 < Module.finrank ℚ E / 2) {la : Wt X.Ψ r} {Q G : Frame X.Ψ r → ℂ} (hQ : X.IsSec la Q)
    (hG : G ∈ X.SS la) (Λ : Finset ℂ) (h0 : ∀ t ∈ Λ, t ≠ 0)
    (h : ∀ x ∈ X.dom, Q x ≠ 0 → ∃ t ∈ Λ, t * Q x = G x) : Q ∈ X.SS la := by
  classical
  have m5 := fun w => (siegelSpaceAlgebra_holds (E := E) r X w w 0).1
  have key : ∀ s : Finset ℂ, ∃ S ∈ X.SS ((s.card + 1) • la), ∀ x,
      Q x * ∏ t ∈ s, (t * Q x - G x) = (∏ t ∈ s, t) * Q x ^ (s.card + 1) + S x := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, (m5 _).1, fun x => by simp⟩
    | insert t s ht ih =>
      obtain ⟨S, hS, e⟩ := ih
      have a1 := ss_mul X hf hS hQ
      have a2 := ss_mul X hf hG (isSec_pow X hQ s.card)
      have a3 := ss_mul X hf hS hG.1.1
      rw [add_comm la] at a2
      rw [← succ_nsmul] at a1 a2 a3
      rw [Finset.card_insert_of_notMem ht]
      refine ⟨_, (m5 _).2.1 _ ((m5 _).2.1 _ ((m5 _).2.2 t _ a1) _ ((m5 _).2.2 (-∏ t ∈ s, t) _ a2)) _
        ((m5 _).2.2 (-1) _ a3), fun x => ?_⟩
      rw [Finset.prod_insert ht, Finset.prod_insert ht, mul_left_comm, e x]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
      ring
  obtain ⟨S, hS, e⟩ := key Λ
  have hc : ∏ t ∈ Λ, t ≠ 0 := Finset.prod_ne_zero_iff.2 h0
  refine ss_of_pow X hf hQ Λ.card ?_
  refine (GlobalTheory.DomCongr.bddSec_cusp_congr E r X _ _ _ fun x hx => ?_).2 ((m5 _).2.2 (-(∏ t ∈ Λ, t)⁻¹) _ hS)
  have z : Q x * ∏ t ∈ Λ, (t * Q x - G x) = 0 := by
    by_cases q : Q x = 0
    · rw [q, zero_mul]
    obtain ⟨t, ht, e⟩ := h x hx q
    rw [Finset.prod_eq_zero (f := fun t => t * Q x - G x) ht (sub_eq_zero.2 e), mul_zero]
  rw [e] at z
  simp only [Pi.smul_apply, Pi.pow_apply, smul_eq_mul]
  field_simp
  linear_combination -z

theorem exists_det_pow (E : Type) [Field E] [NumberField E] [IsCMField E] :
    ∃ K : ℕ, 0 < K ∧ ∀ (r : ℕ) (X : Data E r), ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det ^ K = 1 := by
  classical
  have hfin := NumberField.Embeddings.finite_of_norm_le E ℂ 1
  have hex : ∀ x : E, ∃ n : ℕ, 0 < n ∧ (IsIntegral ℤ x → (∀ φ : E →+* ℂ, ‖φ x‖ = 1) → x ^ n = 1) := fun x => by
    by_cases h : IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ = 1
    · obtain ⟨n, hn, e⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ h.1 h.2
      exact ⟨n, hn, fun _ _ => e⟩
    · exact ⟨1, one_pos, fun a b => absurd ⟨a, b⟩ h⟩
  choose n hn hn' using hex
  refine ⟨∏ x ∈ hfin.toFinset, n x, Finset.prod_pos fun x _ => hn x, fun r X γ hγ => ?_⟩
  set u := (γ : Matrix (Fin r) (Fin r) E).det
  have hU := X.Γ_stab γ hγ
  have hi : IsIntegral ℤ u := by
    have h1 := GlobalTheory.CongruenceDet.isIntegral_det_sub_one (R := 𝓞 E) (M := 1) one_ne_zero X.Λ
      (γ : Matrix (Fin r) (Fin r) E) X.Λ_fg X.Λ_span
      (fun v hv => ⟨_, X.Λ.sub_mem ((hU.2 v).1 hv) hv, by simp⟩)
    have h2 : IsIntegral ℤ ((u - 1) / ((1 : ℕ) : E)) := isIntegral_trans (A := 𝓞 E) _ h1
    simpa using h2.add isIntegral_one
  have hc : u * IsCMField.complexConj E u = 1 := GlobalTheory.CongruenceDet.det_mul_conj X.Gm _ X.Gm_det hU.1
  have h1 : ∀ σ : E →+* ℂ, ‖σ u‖ = 1 := fun σ => by
    have := congrArg (fun z => ‖σ z‖) hc
    simp only [map_mul, IsCMField.complexEmbedding_complexConj, norm_mul, map_one, norm_one,
      Complex.norm_conj] at this
    nlinarith [norm_nonneg (σ u)]
  obtain ⟨c, hc⟩ : n u ∣ ∏ x ∈ hfin.toFinset, n x :=
    Finset.dvd_prod_of_mem _ (by simpa using ⟨hi, fun σ => (h1 σ).le⟩)
  rw [hc, pow_mul, hn' u hi h1, one_pow]

def detPow (Ψ : Finset (E →+* ℂ)) (r : ℕ) (m : ℤ) (x : Frame Ψ r) : ℂ := (∏ τ, (mat x τ).det) ^ m

theorem detPow_ne_zero (m : ℤ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : detPow X.Ψ r m x ≠ 0 :=
  zpow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun τ _ => (hx τ).1)

theorem detPow_mul_neg (m : ℤ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : detPow X.Ψ r m x * detPow X.Ψ r (-m) x = 1 := by
  have := detPow_ne_zero X m hx
  unfold detPow at *
  rw [zpow_neg, mul_inv_cancel₀ this]

theorem isSec_detPow (m : ℤ) (hdet : ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det ^ m = 1)
    (hχ : ∀ γ ∈ X.Γ, X.χ (fun _ _ => m) γ = 1) : X.IsSec (fun _ _ => m) (detPow X.Ψ r m) := by
  classical
  refine ⟨fun y hy => ?_, fun x _ b hb => ?_, fun γ hγ x _ => ?_⟩
  · have hd : Differentiable ℂ fun y : Frame X.Ψ r => ∏ τ, (mat y τ).det := by
      simp only [Matrix.det_apply', mat, Matrix.of_apply]
      fun_prop
    exact ((hd y).zpow (Or.inl (Finset.prod_ne_zero_iff.2 fun τ _ => (hy τ).1))).differentiableWithinAt
  · have hd : ∀ τ, (mat b τ).det = ∏ i, b τ i i := fun τ =>
      Matrix.det_of_upperTriangular (M := mat b τ) fun a c h => (hb τ).2 a c h
    have e : ∀ τ, (mat (rmul x b) τ).det = (mat x τ).det * ∏ i, b τ i i := fun τ => by
      rw [← hd, ← Matrix.det_mul]; rfl
    simp only [detPow, bchar, e, Finset.prod_mul_distrib, mul_zpow, Finset.prod_zpow]
    ring
  · have e : ∀ τ : X.Ψ, (mat (lact γ x) τ).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det * (mat x τ).det := fun τ => by
      rw [RingHom.map_det, ← Matrix.det_mul]; rfl
    simp only [detPow, e, Finset.prod_mul_distrib, mul_zpow, hχ γ hγ]
    rw [← Finset.prod_zpow]
    simp only [← map_zpow₀, hdet γ hγ, map_one, Finset.prod_const_one]

end Analytic

section Linear

theorem transfer {K R V W : Type} [Field K] [AddCommGroup R] [Module K R] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ₀ σ : K →+* ℂ} (α : ℂ →+* ℂ) (hα : ∀ x, α (σ₀ x) = σ x) (ρ₀ : R →ₛₗ[σ₀] V) (ρ : R →ₛₗ[σ] W)
    (S : Submodule K R)
    (hS : ∀ (n : ℕ) (b : Fin n → R), (∀ i, b i ∈ S) → LinearIndependent K b → LinearIndependent ℂ fun i => ρ₀ (b i))
    {I J : Type} [Fintype I] [Fintype J] (h : I → R) (h' : J → R) (hh : ∀ i, h i ∈ S) (hh' : ∀ j, h' j ∈ S)
    (c : I → ℂ) (c' : J → ℂ) (e : ∑ i, c i • ρ₀ (h i) = ∑ j, c' j • ρ₀ (h' j)) :
    ∑ i, α (c i) • ρ (h i) = ∑ j, α (c' j) • ρ (h' j) := by
  classical
  let M : Submodule K R := Submodule.span K (Set.range (Sum.elim h h'))
  haveI : FiniteDimensional K M := FiniteDimensional.span_of_finite K (Set.finite_range _)
  have hM : M ≤ S := Submodule.span_le.2 (by rintro _ ⟨i | j, rfl⟩; exacts [hh i, hh' j])
  let b := Module.finBasis K M
  have hb := hS _ (fun i => (b i : R)) (fun i => hM (b i).2) (b.linearIndependent.map' M.subtype (Submodule.ker_subtype _))
  have hex : ∀ y ∈ M, ∃ a : _ → K, y = ∑ l, a l • (b l : R) := fun y hy =>
    ⟨b.repr ⟨y, hy⟩, by
      have := congrArg M.subtype (b.sum_repr ⟨y, hy⟩).symm
      rw [map_sum] at this
      exact this⟩
  choose a ha using fun i => hex (h i) (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
  choose a' ha' using fun j => hex (h' j) (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
  have ex : ∀ {L Z : Type} [Fintype L] [AddCommGroup Z] [Module ℂ Z] {s : K →+* ℂ} (p : R →ₛₗ[s] Z) (d : L → ℂ)
      (t : L → Fin (Module.finrank K M) → K),
      ∑ i, d i • p (∑ l, t i l • (b l : R)) = ∑ l, (∑ i, d i * s (t i l)) • p (b l) := by
    intro L Z _ _ _ s p d t
    simp only [map_sum, map_smulₛₗ, Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm
  have e1 : ∑ i, c i • ρ₀ (h i) = _ := (Finset.sum_congr rfl fun i _ => by rw [ha i]).trans (ex ρ₀ c a)
  have e2 : ∑ i, c' i • ρ₀ (h' i) = _ := (Finset.sum_congr rfl fun i _ => by rw [ha' i]).trans (ex ρ₀ c' a')
  have e3 : ∑ i, α (c i) • ρ (h i) = _ := (Finset.sum_congr rfl fun i _ => by rw [ha i]).trans (ex ρ _ a)
  have e4 : ∑ i, α (c' i) • ρ (h' i) = _ := (Finset.sum_congr rfl fun i _ => by rw [ha' i]).trans (ex ρ _ a')
  rw [e1, e2] at e
  have e5 : (fun l => ∑ i, c i * σ₀ (a i l)) = fun l => ∑ i, c' i * σ₀ (a' i l) := funext fun l =>
    Fintype.linearIndependent_iffₛ.1 hb _ _ e l
  rw [e3, e4]
  refine Finset.sum_congr rfl fun l _ => ?_
  have := congrArg α (congrFun e5 l)
  simp only [map_sum, map_mul, hα] at this
  rw [this]

theorem ratio_eigen {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] (D : I → J → ℂ) (D' : J → I → ℂ)
    (B : J → I → ℂ) (B' : I → J → ℂ) (β : I → ℂ) (s : J → ℂ) (u v F G : ℂ) (hu : u ≠ 0) (hβ : β ≠ 0)
    (h1 : ∀ i i', ∑ j, D i j * (β i' * s j) = ∑ j, D i' j * (β i * s j))
    (h2 : ∀ i, ∑ j, D i j * (F * s j) = G * β i)
    (h3 : ∀ j, s j = ∑ p : I × J, D' j p.1 * D p.1 p.2 * s p.2)
    (h4 : ∀ j, s j * v = ∑ i, B j i * β i) (h5 : ∀ i, β i * u = ∑ j, B' i j * s j) (hv : v ≠ 0) :
    ∃ t, t ≠ 0 ∧ Module.End.HasEigenvalue (Matrix.toLin' (Matrix.of D * Matrix.of B)) t ∧ t * F = G * v := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hβ
  replace hi₀ : β i₀ ≠ 0 := hi₀
  set w : I → ℂ := fun i => ∑ j, D i j * s j with hw
  have k1 : ∀ i, β i₀ * w i = β i * w i₀ := fun i => by
    simp only [hw, Finset.mul_sum]
    simpa only [mul_left_comm] using h1 i i₀
  have k2 : F * w i₀ = G * β i₀ := by
    simp only [hw, Finset.mul_sum]
    simpa only [mul_left_comm] using h2 i₀
  refine ⟨w i₀ * v / β i₀, fun h0 => ?_, Module.End.hasEigenvalue_of_hasEigenvector (x := β) ⟨?_, hβ⟩, ?_⟩
  · have w0 : w i₀ = 0 := by simpa [hi₀, hv] using h0
    have wz : ∀ i, w i = 0 := fun i => by
      have := k1 i
      rw [w0, mul_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hi₀
    have sz : ∀ j, s j = 0 := fun j => by
      rw [h3, Fintype.sum_prod_type]
      refine Finset.sum_eq_zero fun i _ => ?_
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [show ∑ j, D i j * s j = 0 from wz i, mul_zero]
    have := h5 i₀
    simp [sz, hu, hi₀] at this
  · rw [Module.End.mem_eigenspace_iff]
    funext i
    have : (Matrix.toLin' (Matrix.of D * Matrix.of B)) β i = w i * v := by
      rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, hw, Finset.sum_mul, mul_assoc, h4]
    rw [this, Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination k1 i
  · field_simp
    linear_combination k2

end Linear

section Geometric

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem exists_sec_ne_zero (Xo : Moduli Dw l) (c : Coeff l) : ∃ m : ℕ, ∀ (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r)
    (k : U.Comp) (x₀ : Frame (U.X k).Ψ r), x₀ ∈ (U.X k).dom →
    ∃ f : Rul Xo c, f ∈ sec Xo c 0 (2 * (m + 1)) ∧ rdU U f k x₀ ≠ 0 := by
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
  have hR : Odd 3 := by decide
  have h1 : 1 < 3 := by norm_num
  obtain ⟨hfG, hfL, -⟩ := GlobalTheory.EtaCard.card_levGrp_and_span E H Dw 3 h1
  letI hFin : Fintype (GlobalTheory.EtaForm.LatMod Dw 3) := Fintype.ofFinite _
  have hpos : 0 < Nat.card (GlobalTheory.EtaForm.LevGrp Dw (3 ^ 4)) := Nat.card_pos
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  refine ⟨m, fun σ r U k x₀ hx₀ => ?_⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨cf, -, hne⟩ := GlobalTheory.EtaForm.exists_small_coeff_etaValAt_ne_zero GlobalTheory.firstFiveLaws.1 E H Dw l Xo c 3 hR h1
    2 0 (CAt σ) 1 (fun _ => U.un k ⟨x₀, hx₀⟩)
  obtain ⟨⟨f, hrule, -⟩, hsec⟩ := GlobalTheory.EtaForm.isEtaRule_existsUnique_mem_sec GlobalTheory.firstFiveLaws.1 E H Dw l Xo c 3 hR
    (Fin 2 → GlobalTheory.EtaForm.LatMod Dw 3) 2 (fun j => (cf j : ℤ)) (GlobalTheory.EtaForm.shiftFam 3 0)
  refine ⟨f, by have := hsec f hrule; rwa [hm] at this, ?_⟩
  have hv := (GlobalTheory.EtaForm.etaValAt_evR_of_fromTest E H Dw l Xo c 3 hR _ _ _ _ f hrule (CAt σ) (U.un k ⟨x₀, hx₀⟩)
    (hT _ _)).1
  have h0 := hne 0 _ hv
  have e1 : rdU U f k x₀ = toC (evR Xo c f (U.un k ⟨x₀, hx₀⟩)) := dif_pos hx₀
  rw [e1]
  exact h0

theorem rd_mul {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (f g : Rul Xo c) : rdU U (f * g) = rdU U f * rdU U g :=
  GlobalTheory.CuspProduct.rdU_mul (Formalism.L2.PjFree.Unf.ofPj U) f g

theorem rd_pow {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (f : Rul Xo c) (n : ℕ) : rdU U (f ^ (n + 1)) = rdU U f ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, rd_mul, ih, ← pow_succ]

theorem la_add {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a a' : (E →+* ℂ) × ℕ → ℕ) {n n' : ℕ} (hn : Even n)
    (hn' : Even n') (k : U.Comp) : laU U (a + a') (n + n') k = laU U a n k + laU U a' n' k :=
  GlobalTheory.CuspProduct.laU_add (Formalism.L2.PjFree.Unf.ofPj U) a a' n n' hn hn' k

theorem la_smul {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (hn : Even n) (N : ℕ)
    (k : U.Comp) : laU U ((N + 1) • a) ((N + 1) * n) k = (N + 1) • laU U a n k := by
  induction N with
  | zero => simp
  | succ N ih => rw [succ_nsmul, add_mul _ 1, one_mul, la_add U _ _ (hn.mul_left _) hn, ih, ← succ_nsmul]

theorem pow_mem_sec {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) (N : ℕ) :
    f ^ (N + 1) ∈ sec Xo c ((N + 1) • a) ((N + 1) * n) := by
  induction N with
  | zero => simpa using hf
  | succ N ih => rw [succ_nsmul, add_mul _ 1, one_mul, pow_succ]; exact sec_mul Xo c _ _ _ _ ih hf

theorem mem_holSub {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X) :
    P ∈ holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) :=
  GlobalTheory.CuspProduct.mem_holSub_iff X la P

theorem dom_add {a a' : (E →+* ℂ) × ℕ → ℕ} {n n' : ℕ} (h : Dom a n) (h' : Dom a' n') : Dom (a + a') (n + n') :=
  ⟨fun τ => (h.1 τ).add (h'.1 τ), h.2.add h'.2⟩

open Classical in

def shift (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) : (E →+* ℂ) × ℕ → ℕ :=
  fun x => a x - if InPsi H x.1 then 2 * k else 0

theorem dom_shift {a : (E →+* ℂ) × ℕ → ℕ} {n n' : ℕ} (h : Dom a n) (hn : Even n') (k : ℕ) : Dom (shift H k a) n' :=
  ⟨fun τ _ _ hij => Nat.sub_le_sub_right (h.1 τ hij) _, hn⟩

theorem la_shift {σ : c.F →+* ℂ} {U : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf U) {a : (E →+* ℂ) × ℕ → ℕ} {k : ℕ}
    (ha : ∀ τ, InPsi H τ → ∀ i < Dw.p, 2 * k ≤ a (τ, i)) {n : ℕ} (hn : Even n) (j : U.Comp) :
    laU U (shift H k a) (n + 2 * k) j = laU U a n j + fun _ _ => -(k : ℤ) := by
  obtain ⟨hb, hp, hc, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  change Function.Bijective (relab c σ) at hb
  change ∀ τ, relab c σ τ _ = _ ↔ _ at hp
  obtain ⟨m, rfl⟩ := hn
  have h1 : (m + m) / 2 = m := by omega
  have h2 : (m + m + 2 * k) / 2 = m + k := by omega
  funext τ i
  have hτ := ((hU.2.1 j).2 τ.1).1 τ.2
  have hi := Function.invFun_eq (hb.2 τ.1)
  have p1 : InPsi H (Function.invFun (relab c σ) τ.1) := (hp _).1 (by rw [hi]; exact hτ)
  have p2 : ¬ InPsi H (Function.invFun (relab c σ) (conjEmb τ.1)) := fun h => by
    have := (hp _).2 h
    rw [Function.invFun_eq (hb.2 _), ← (hU.2.1 j).2] at this
    exact ((U.X j).cmType τ.1).1 τ.2 this
  simp only [laU, shift, Pi.add_apply, h1, h2, if_pos p1, if_neg p2]
  split_ifs with h
  · have := ha _ p1 (i - (U.X j).p0) (by have := hU.1; have := (hU.2.1 j).1; have := i.2; omega)
    push_cast [this]
    ring
  · push_cast [Nat.sub_zero]
    ring

def detU {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (m : ℤ) : FDSec U.X := fun k => detPow (U.X k).Ψ r m

theorem mul_detU_cancel {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (m : ℤ) {P : FDSec U.X} (hP : P ∈ offZero U.X) :
    P * detU U m * detU U (-m) = P := by
  funext k x
  by_cases hx : x ∈ (U.X k).dom
  · show P k x * detPow _ r m x * detPow _ r (-m) x = _
    rw [mul_assoc, detPow_mul_neg _ m hx, mul_one]
  · show P k x * _ * _ = _
    rw [hP k x hx, zero_mul, zero_mul]

theorem mul_detU_mem (hf : 1 < Module.finrank ℚ E / 2) {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (m : ℤ)
    (hdet : ∀ k, ∀ γ ∈ (U.X k).Γ, (γ : Matrix (Fin r) (Fin r) E).det ^ m = 1) {la la' : ∀ k, Wt (U.X k).Ψ r}
    (e : ∀ k, la' k = la k + fun _ _ => m) (h : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (la k) γ = 1)
    (h' : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (la' k) γ = 1) {P : FDSec U.X} (hP : P ∈ holSub0 U.X la) :
    P * detU U m ∈ holSub0 U.X la' := by
  refine ⟨(mem_holSub _ _ _).2 fun k => ?_, fun k x hx => ?_⟩
  · rw [e k]
    refine ss_mul _ hf ((mem_holSub _ _ _).1 hP.1 k) (isSec_detPow _ m (hdet k) fun γ hγ => ?_)
    have := h' k γ hγ
    rwa [e k, (U.X k).χ_add _ _ γ hγ, h k γ hγ, one_mul] at this
  · show P k x * _ = 0
    rw [hP.2 k x hx, zero_mul]

set_option maxHeartbeats 2000000 in

theorem mem_cusp_of_span (hf : 1 < Module.finrank ℚ E / 2) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hχ : ∀ σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (laU (U σ) a n k) γ = 1)
    (hI : RdIndep Xo c U c.F.val.toRingHom) (L : ℕ)
    (hspan : ∀ a n, Dom a n → LastPos Dw a → L ≤ n → ∃ (m : ℕ) (b : Fin m → Rul Xo c), (∀ i, b i ∈ cusp Xo c U a n) ∧
      ∀ σ, GoodEmb c σ → ∀ P ∈ holSub0 (U σ).X (laU (U σ) a n), ∃ e : Fin m → ℂ, P = ∑ i, e i • rdU (U σ) (b i))
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n) (hl : LastPos Dw a) {f : Rul Xo c} (hfs : f ∈ sec Xo c a n)
    (hf0 : rdU (U c.F.val.toRingHom) f ∈ holSub0 (U c.F.val.toRingHom).X (laU (U c.F.val.toRingHom) a n)) :
    f ∈ cusp Xo c U a n := by
  classical
  set σ₀ : c.F →+* ℂ := c.F.val.toRingHom with hσ₀
  have g₀ : GoodEmb c σ₀ := rfl
  refine (mem_cusp _ _ _ _ _ _).2 ⟨hfs, fun σ hσ => (mem_holSub _ _ _).2 fun k₀ => ?_⟩
  haveI := c.fin
  obtain ⟨α, hα⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.extendEmb_holds c.F inferInstance σ.toRatAlgHom
  obtain ⟨K, hK, hKdet⟩ := exists_det_pow E
  obtain ⟨m, hm⟩ := exists_sec_ne_zero Xo c
  set k := K * (L + 1) with hk
  have hkL : L + 1 ≤ k := Nat.le_mul_of_pos_left _ hK
  set A := (2 * k + 1) • a with hA
  set nA := (2 * k + 1) * n with hnA
  set nW := nA + (L + 1) * (2 * (m + 1)) with hnW
  have dA : ∀ n', Even n' → Dom A n' := fun n' h =>
    ⟨fun τ _ _ hij => Nat.mul_le_mul_left _ (hd.1 τ hij), h⟩
  have eA : Even nA := hd.2.mul_left _
  have eW : Even nW := eA.add ((even_two_mul _).mul_left _)
  have e2 : ∀ {n'}, Even n' → Even (n' + 2 * k) := fun h => h.add (even_two_mul _)
  have hAge : ∀ τ, InPsi H τ → ∀ i < Dw.p, 2 * k + 1 ≤ A (τ, i) := fun τ hτ i hi => by
    have hmu : Dw.mult τ = Dw.p := if_pos hτ
    have h1 := hl τ hτ (by omega)
    have h2 : a (τ, Dw.mult τ - 1) ≤ a (τ, i) := hd.1 τ (by omega : i ≤ Dw.mult τ - 1)
    exact Nat.le_mul_of_pos_right _ (by omega)
  have lA : LastPos Dw A := fun τ hτ h => by
    have hmu : Dw.mult τ = Dw.p := if_pos hτ
    have := hAge τ hτ (Dw.mult τ - 1) (by omega)
    omega
  have lS : LastPos Dw (shift H k A) := fun τ hτ h => by
    have hmu : Dw.mult τ = Dw.p := if_pos hτ
    have := hAge τ hτ (Dw.mult τ - 1) (by omega)
    simp only [shift, if_pos hτ]
    omega
  have dS : ∀ n', Even n' → Dom (shift H k A) (n' + 2 * k) := fun n' h => dom_shift (dA _ h) (e2 h) k
  have hdet : ∀ (r : ℕ) (X : Data E r), ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det ^ (k : ℤ) = 1 :=
    fun r X γ hγ => by rw [zpow_natCast, hk, pow_mul, hKdet r X γ hγ, one_pow]
  have sh := fun s (hs : GoodEmb c s) n' (hn' : Even n') j =>
    la_shift hs (hU s hs) (a := A) (k := k) (fun τ hτ i hi => (Nat.le_succ _).trans (hAge τ hτ i hi)) hn' j
  have down : ∀ s, GoodEmb c s → ∀ n', Even n' → ∀ P ∈ holSub0 (U s).X (laU (U s) A n'),
      P * detU (U s) (-(k : ℤ)) ∈ holSub0 (U s).X (laU (U s) (shift H k A) (n' + 2 * k)) := fun s hs n' hn' P hP =>
    mul_detU_mem hf _ _ (fun j γ hγ => by rw [zpow_neg, hdet _ _ γ hγ, inv_one]) (sh s hs n' hn')
      (hχ s hs _ _ (dA _ hn')) (hχ s hs _ _ (dS _ hn')) hP
  have up : ∀ s, GoodEmb c s → ∀ n', Even n' → ∀ P ∈ holSub0 (U s).X (laU (U s) (shift H k A) (n' + 2 * k)),
      P * detU (U s) (k : ℤ) ∈ holSub0 (U s).X (laU (U s) A n') := fun s hs n' hn' P hP =>
    mul_detU_mem hf _ _ (fun j γ hγ => hdet _ _ γ hγ) (fun j => by rw [sh s hs n' hn']; funext τ i; simp)
      (hχ s hs _ _ (dS _ hn')) (hχ s hs _ _ (dA _ hn')) hP
  obtain ⟨mb, b, hb, sb⟩ := hspan A nW (dA _ eW) lA (by nlinarith [Nat.zero_le nA, Nat.zero_le m])
  obtain ⟨ms, s, hs, ss⟩ := hspan _ _ (dS _ eW) lS (by omega)
  obtain ⟨mg, g, hg, sg⟩ := hspan _ _ (dS _ eA) lS (by omega)
  have rdm : ∀ {a n} {t : Rul Xo c}, t ∈ cusp Xo c U a n → ∀ s, GoodEmb c s →
      rdU (U s) t ∈ holSub0 (U s).X (laU (U s) a n) := fun ht s hs =>
    ⟨((mem_cusp _ _ _ _ _ _).1 ht).2 s hs, rdU_mem_offZero _ _⟩
  have cs : ∀ {a n} {t : Rul Xo c}, t ∈ cusp Xo c U a n → t ∈ sec Xo c a n := fun ht => cusp_le_sec _ _ _ _ _ ht
  set F := f ^ (2 * k + 1) with hF
  have hFs : F ∈ sec Xo c A nA := pow_mem_sec hfs _
  have hF0 : rdU (U σ₀) F ∈ holSub0 (U σ₀).X (laU (U σ₀) A nA) := by
    refine ⟨(mem_holSub _ _ _).2 fun j => ?_, rdU_mem_offZero _ _⟩
    have h1 := (mem_holSub _ _ _).1 hf0.1 j
    have h2 := ss_mul _ hf h1 (isSec_pow _ h1.1.1 (2 * k - 1))
    rw [la_smul _ _ hd.2, rd_pow]
    have e : 2 * k - 1 + 1 = 2 * k := by omega
    rw [e, ← pow_succ', ← succ_nsmul'] at h2
    exact h2
  choose D hD using fun i => ss σ₀ g₀ _ (down σ₀ g₀ _ eW _ (rdm (hb i) σ₀ g₀))
  choose D' hD' using fun j => sb σ₀ g₀ _ (up σ₀ g₀ _ eW _ (rdm (hs j) σ₀ g₀))
  choose B hB using fun j => sb σ hσ _ (up σ hσ _ eW _ (rdm (hs j) σ hσ))
  choose B' hB' using fun i => ss σ hσ _ (down σ hσ _ eW _ (rdm (hb i) σ hσ))
  obtain ⟨cg, hcg⟩ := sg σ₀ g₀ _ (down σ₀ g₀ _ eA _ hF0)
  have tr := fun a n (h : Dom a n) => @transfer c.F (Rul Xo c) _ _ _ _ _ _ _ _ _ σ₀ σ (α : ℂ →+* ℂ) hα
    (rdU (U σ₀)) (rdU (U σ)) (sec Xo c a n) (hI a n h)
  have R1 : ∀ i i', ∑ j, α (D i j) • rdU (U σ) (b i' * s j) = ∑ j, α (D i' j) • rdU (U σ) (b i * s j) := fun i i' => by
    refine tr _ _ (dom_add (dA _ eW) (dS _ eW)) _ _ (fun j => sec_mul Xo c _ _ _ _ (cs (hb i')) (cs (hs j)))
      (fun j => sec_mul Xo c _ _ _ _ (cs (hb i)) (cs (hs j))) _ _ ?_
    simp only [rd_mul, ← mul_smul_comm, ← Finset.mul_sum, ← hD]
    ring
  have R2 : ∀ i, ∑ j, α (D i j) • rdU (U σ) (F * s j) = ∑ j, α (cg j) • rdU (U σ) (b i * g j) := fun i => by
    refine tr _ _ (dom_add (dA _ eA) (dS _ eW)) _ _ (fun j => sec_mul Xo c _ _ _ _ hFs (cs (hs j)))
      (fun j => ?_) _ _ ?_
    · have := sec_mul Xo c _ _ _ _ (cs (hb i)) (cs (hg j))
      rwa [show nW + (nA + 2 * k) = nA + (nW + 2 * k) by ring] at this
    · simp only [rd_mul, ← mul_smul_comm, ← Finset.mul_sum, ← hD, ← hcg]
      ring
  have R3 : ∀ j, ∑ _u : Unit, α 1 • rdU (U σ) (s j) =
      ∑ p : Fin mb × Fin ms, α (D' j p.1 * D p.1 p.2) • rdU (U σ) (s p.2) := fun j => by
    refine tr _ _ (dS _ eW) (fun _ : Unit => s j) (fun p : Fin mb × Fin ms => s p.2) (fun _ => cs (hs j))
      (fun p => cs (hs p.2)) (fun _ => 1) (fun p => D' j p.1 * D p.1 p.2) ?_
    rw [Fintype.sum_unique, one_smul, ← mul_detU_cancel (U σ₀) k (rdU_mem_offZero _ (s j)), hD', Finset.sum_mul,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, hD, Finset.smul_sum]
    simp only [mul_smul]
  set G : FDSec (U σ).X := ∑ j, α (cg j) • rdU (U σ) (g j) with hG
  have hGm := up σ hσ _ eA G (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (rdm (hg j) σ hσ))
  have hP := (hU σ hσ).2.2.2.2.1 a n hd f hfs k₀
  refine ss_of_pow _ hf hP (2 * k) ?_
  have hGk := (mem_holSub _ _ _).1 hGm.1 k₀
  rw [la_smul _ _ hd.2] at hGk
  have fin := Module.End.finite_hasEigenvalue (Matrix.toLin' (Matrix.of (fun i j => α (D i j)) * Matrix.of B))
  refine ss_of_finite_ratio _ hf (isSec_pow _ hP _) hGk (fin.toFinset.erase 0) (fun t ht => Finset.ne_of_mem_erase ht)
    fun x hx hne => ?_
  have hFx : rdU (U σ) F k₀ x = (rdU (U σ) f k₀ ^ (2 * k + 1)) x := by rw [hF, rd_pow]; rfl
  obtain ⟨η, hη, hηx⟩ := hm σ r (U σ) k₀ x hx
  have hηL := pow_mem_sec hη L
  rw [smul_zero] at hηL
  have hts := sec_mul Xo c _ _ _ _ hFs hηL
  rw [add_zero] at hts
  have ht0 : rdU (U σ₀) (F * η ^ (L + 1)) ∈ holSub0 (U σ₀).X (laU (U σ₀) A nW) := by
    refine ⟨(mem_holSub _ _ _).2 fun j => ?_, rdU_mem_offZero _ _⟩
    have ev : Even ((L + 1) * (2 * (m + 1))) := (even_two_mul _).mul_left _
    have := ss_mul _ hf ((mem_holSub _ _ _).1 hF0.1 j)
      ((hU σ₀ g₀).2.2.2.2.1 0 _ ⟨fun _ _ _ _ => le_rfl, ev⟩ _ hηL j)
    rw [← la_add _ _ _ eA ev, add_zero] at this
    rw [rd_mul]
    exact this
  obtain ⟨et, het⟩ := sb σ₀ g₀ _ ht0
  have R4 : ∑ _u : Unit, α 1 • rdU (U σ) (F * η ^ (L + 1)) = ∑ i, α (et i) • rdU (U σ) (b i) :=
    tr _ _ (dA _ eW) (fun _ : Unit => F * η ^ (L + 1)) b (fun _ => hts) (fun i => cs (hb i)) (fun _ => 1) et
      (by rw [Fintype.sum_unique, one_smul, het])
  have ev : ∀ {I : Type} [Fintype I] (e : I → ℂ) (P : I → FDSec (U σ).X), (∑ i, e i • P i) k₀ x = ∑ i, e i * P i k₀ x := by
    intro I _ e P
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hβ : (fun i => rdU (U σ) (b i) k₀ x) ≠ 0 := fun h0 => by
    have := congrFun (congrFun R4 k₀) x
    rw [ev, ev, Fintype.sum_unique, map_one, one_mul, rd_mul, rd_pow (U σ) η,
      Finset.sum_eq_zero fun i _ => by rw [show rdU (U σ) (b i) k₀ x = 0 from congrFun h0 i, mul_zero]] at this
    rcases mul_eq_zero.1 this with h | h
    · exact hne (hFx ▸ h)
    · exact hηx (pow_eq_zero_iff (Nat.succ_ne_zero L) |>.1 h)
  obtain ⟨t, t0, te, tF⟩ := ratio_eigen (fun i j => α (D i j)) (fun j i => α (D' j i)) B B'
    (fun i => rdU (U σ) (b i) k₀ x) (fun j => rdU (U σ) (s j) k₀ x) (detU (U σ) (-(k : ℤ)) k₀ x) (detU (U σ) k k₀ x)
    (rdU (U σ) F k₀ x) (G k₀ x) (detPow_ne_zero _ _ hx) hβ
    (fun i i' => by
      have := congrFun (congrFun (R1 i i') k₀) x
      rw [ev, ev] at this
      simpa only [rd_mul, Pi.mul_apply] using this)
    (fun i => by
      have := congrFun (congrFun (R2 i) k₀) x
      rw [ev, ev] at this
      simp only [rd_mul, Pi.mul_apply] at this
      rw [this, hG, ev, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring)
    (fun j => by
      have := congrFun (congrFun (R3 j) k₀) x
      rw [ev, ev, Fintype.sum_unique, map_one, one_mul] at this
      simpa only [map_mul] using this)
    (fun j => by
      have := congrFun (congrFun (hB j) k₀) x
      rwa [ev] at this)
    (fun i => by
      have := congrFun (congrFun (hB' i) k₀) x
      rwa [ev] at this)
    (detPow_ne_zero _ _ hx)
  exact ⟨t, Finset.mem_erase.2 ⟨t0, fin.mem_toFinset.2 te⟩, hFx ▸ tF⟩

end Geometric

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem mem_cuspA_of_rdU_mem_holSub0 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j, w.LastPos → ∀ f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n, rdU (T.U j T.σ₀) f ∈ holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) → f ∈ T.cuspA j (wtA w) w.n := by
  intro D T h j hj w hw f hf hfh
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := Formalism.L2.Pj.hostSize_finrank D
  have h8 := D.eight_le_f
  refine mem_cusp_of_span (by omega) (T.U j) (h.unf j hj) (h.chiTriv j hj)
    (GlobalTheory.rdIndep_of_lawsM D T.toCore h.toLawsM j hj T.σ₀ T.toCore.good_σ₀) (4 * (Module.finrank ℚ D.host.E * D.R.r) + 4)
    (fun a n hd hl hn => ?_) (dom_wtA w) (GlobalTheory.lastPos_wtA_of_pins D T.Q h.pins j hj w hw) hf hfh
  set S := T.cuspA j a n with hS
  haveI : FiniteDimensional T.Q.c.F S := h.toLawsM.cuspFD j hj a n hd
  haveI : Module.Free T.Q.c.F S := Module.Free.of_divisionRing _ _
  let b := Module.finBasis T.Q.c.F S
  refine ⟨_, fun i => (b i : T.R j), fun i => (b i).2, fun σ hσ P hP => ?_⟩
  obtain ⟨hrk, hM⟩ := h.modelW j hj σ hσ
  have key := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E T.Q.H (T.Q.Dw j) T.Q.l
    (T.Q.Xo j) T.Q.c D.R.r (fun s => Formalism.L2.PjFree.Unf.ofPj (T.U j s)) hr h.pins.2.1.2
    (fun s hs => (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj s hs)) σ hσ
    (fun k k' => ⟨(hM k).1.trans (hM k').1.symm, (hM k).2.trans (hM k').2.symm⟩)
    (fun k => GlobalTheory.PrincCore.mem_group_of_congruent D T.toCore h.toLawsM j hj σ hσ k)
    a n hd hl hn (fun k => h.chiTriv j hj σ hσ a n hd k)
  have hspan : P ∈ Submodule.span ℂ (rdU (T.U j σ) '' (S : Set (T.R j))) := key ⟨hP.1, hP.2⟩
  have h2 : P ∈ Submodule.span ℂ (Set.range fun i => rdU (T.U j σ) (b i : T.R j)) := by
    refine (Submodule.span_le.2 ?_) hspan
    rintro _ ⟨y, hy, rfl⟩
    have e := congrArg S.subtype (b.sum_repr ⟨y, hy⟩).symm
    rw [map_sum] at e
    replace e : y = ∑ i, b.repr ⟨y, hy⟩ i • (b i : T.R j) := e
    rw [e, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 h2
  exact ⟨e, he.symm⟩

end GlobalTheory.CuspAllEmb

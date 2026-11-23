import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomologyWedgeCoordinateNonzero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLinearAlgebraHodgeSequenceExact

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open scoped Matrix

namespace GlobalTheory.DetLine.WedgePer

open GlobalTheory.DetLine.WedgeCoord GlobalTheory.ShFam.HodgeSeq

theorem left_inv_of_decomp {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (Γ : Matrix (m ⊕ n) (m ⊕ n) ℂ) (C M : Matrix n (m ⊕ n) ℂ) (C' M' : Matrix m (m ⊕ n) ℂ) (hΓ : Γ.det ≠ 0)
    (h : Γ = Cᵀ * M + M'ᵀ * C') : M' * ((Γᵀ)⁻¹ * C'ᵀ) = 1 := by
  have hu : IsUnit (Γᵀ).det := by rw [Matrix.det_transpose]; exact hΓ.isUnit
  have h1 : Matrix.fromCols ((Γᵀ)⁻¹ * C'ᵀ) ((Γᵀ)⁻¹ * Mᵀ) * Matrix.fromRows M' C = 1 := by
    rw [Matrix.fromCols_mul_fromRows, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add]
    have : C'ᵀ * M' + Mᵀ * C = Γᵀ := by
      rw [h, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.transpose_transpose, add_comm]
    rw [this, Matrix.nonsing_inv_mul _ hu]
  have h2 := mul_eq_one_comm.1 h1
  rw [Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h2
  exact h2.1

theorem det_fromRows_smul {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (a : ℂ)
    (R : Matrix m (m ⊕ n) ℂ) (C : Matrix n (m ⊕ n) ℂ) :
    (Matrix.fromRows (a • R) C).det = a ^ Fintype.card m * (Matrix.fromRows R C).det := by
  have : Matrix.fromRows (a • R) C = Matrix.fromBlocks (a • (1 : Matrix m m ℂ)) 0 0 1 * Matrix.fromRows R C := by
    rw [Matrix.fromBlocks_mul_fromRows]; simp
  rw [this, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem herm_sum {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) {L L' : Type} [Fintype L] [Fintype L'] (W : L → Fin g → ℂ)
    (W' : L' → Fin g → ℂ) (u : L → ℂ) (v : L' → ℂ) :
    herm Hm (∑ z, u z • W z) (∑ w, v w • W' w) = ∑ z, ∑ w, u z * herm Hm (W z) (W' w) * starRingEnd ℂ (v w) := by
  simp only [herm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [starRingEnd_apply]; ring

theorem herm_sum_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) {L : Type} [Fintype L] (u : Fin g → ℂ)
    (W : L → Fin g → ℂ) (v : L → ℂ) :
    herm Hm u (∑ w, v w • W w) = ∑ w, herm Hm u (W w) * starRingEnd ℂ (v w) := by
  simpa using herm_sum Hm (fun _ : Unit => u) W (fun _ => 1) v

theorem herm_sum_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) {L : Type} [Fintype L] (u : Fin g → ℂ)
    (W : L → Fin g → ℂ) (v : L → ℂ) :
    herm Hm (∑ w, v w • W w) u = ∑ w, v w * herm Hm (W w) u := by
  simpa using herm_sum Hm W (fun _ : Unit => u) v (fun _ => 1)

theorem proj_unique {g p : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (herm Hm z z).re)
    {V : Fin p → Fin g → ℂ} (hV : LinearIndependent ℂ V) {y : Fin g → ℂ} {a b : Fin p → ℂ}
    (ha : ∀ i, herm Hm (y - ∑ m, a m • V m) (V i) = 0) (hb : ∀ i, herm Hm (y - ∑ m, b m • V m) (V i) = 0) : a = b := by
  have h0 : ∑ m, (a m - b m) • V m = 0 := by
    by_contra hne
    have h1 := hpos _ hne
    have h2 : ∀ i, herm Hm (∑ m, (a m - b m) • V m) (V i) = 0 := fun i => by
      have e : ∑ m, (a m - b m) • V m = (y - ∑ m, b m • V m) - (y - ∑ m, a m • V m) := by
        simp only [sub_smul, Finset.sum_sub_distrib]; abel
      rw [e, ← hl_apply, map_sub, hl_apply, hl_apply, ha, hb, sub_self]
    rw [herm_sum_right] at h1
    simp [h2] at h1
  funext i
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hV _ h0 i)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}
  {c : Coeff l} {e : c.F →+* ℂ} {τ : E →+* ℂ} {Di : Datum H} {x : Hor.Idx D τ → Di.La}
  {hm : Matrix (Hor.Idx D τ) (Hor.Idx D τ) E} {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} {P : Di.La →+ (Fin g → ℂ)}
  {W : Pad.Letter D → Fin g → ℂ} {Q : Di.La →+ (Pad.Letter D → ℂ)}

theorem relab_inj (c : Coeff l) (e : c.F →+* ℂ) : Function.Injective (Formalism.L2.PjFree.relab (E := E) c e) :=
  fun _ _ h => GlobalTheory.DerivEig.eq_of_relab_eq c e fun a => by rw [h]

theorem relab_conj (c : Coeff l) (e : c.F →+* ℂ) (φ : E →+* ℂ) :
    Formalism.L2.PjFree.relab c e (conjEmb φ) = conjEmb (Formalism.L2.PjFree.relab (E := E) c e φ) := by
  ext a
  have h1 : Formalism.L2.Pj.embF c (conjEmb φ) a = Formalism.L2.Pj.embF c φ (IsCMField.complexConj E a) :=
    Subtype.ext (IsCMField.complexEmbedding_complexConj E φ a).symm
  show e (Formalism.L2.Pj.embF c (conjEmb φ) a) = starRingEnd ℂ (Formalism.L2.PjFree.relab c e φ a)
  rw [h1]
  exact IsCMField.complexEmbedding_complexConj E (Formalism.L2.PjFree.relab c e φ) a

theorem span_coord (h : PerData c e Di Hm P W Q) : Submodule.span ℝ (Set.range Q) = ⊤ := by
  obtain ⟨-, -, hspan, -, hW, hPQ, -⟩ := h
  let T : (Pad.Letter D → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ W
  have hT : Function.Injective T := hW.fintypeLinearCombination_injective
  have hTQ : ∀ v, T (Q v) = P v := fun v => (hPQ v).symm
  refine Submodule.map_injective_of_injective (f := T.restrictScalars ℝ) hT ?_
  have h1 : (Submodule.span ℝ (Set.range Q)).map (T.restrictScalars ℝ) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp, ← hspan]
    exact congrArg (fun f => Submodule.span ℝ (Set.range f)) (funext hTQ)
  rw [h1]
  exact (top_unique (h1 ▸ Submodule.map_mono le_top)).symm

theorem im_form (h : PerData c e Di Hm P W Q) (a b : Di.La) :
    (form (fun z w => herm Hm (W z) (W w)) (Q a) (Q b)).im = Di.EF a b := by
  obtain ⟨-, -, -, hEF, -, hPQ, -⟩ := h
  rw [← hEF, hPQ, hPQ, herm_sum]
  rfl

theorem orth (h : PerData c e Di Hm P W Q) {z w : Pad.Letter D} (hzw : z.1 ≠ w.1) : herm Hm (W z) (W w) = 0 :=
  block Di (fun z => Formalism.L2.PjFree.relab c e z.1) Q (fun z w => herm Hm (W z) (W w)) h.2.2.2.2.2.2 (span_coord h)
    (im_form h) (fun h' => hzw (relab_inj c e h'))

def dualMat (Hm : Matrix (Fin g) (Fin g) ℂ) (W : Pad.Letter D → Fin g → ℂ) (x : Hor.Idx D τ → Di.La)
    (Q : Di.La →+ (Pad.Letter D → ℂ)) : Matrix (Fin (D.mult (conjEmb τ))) (Hor.Idx D τ) ℂ :=
  Matrix.of fun j k => -(2 * Complex.I)⁻¹ *
    ∑ i, starRingEnd ℂ (Q (x k) ⟨conjEmb τ, i⟩ * herm Hm (W ⟨conjEmb τ, i⟩) (W ⟨conjEmb τ, j⟩))

theorem dualMat_mul (hx : IsPerBasis Di x hm) (h : PerData c e Di Hm P W Q) :
    dualMat Hm W x Q * kerMat c e τ x hm Q = 1 := by
  have hI : (2 * Complex.I) ≠ 0 := by simp
  refine left_inv_of_decomp _ (perMat x Q τ)
    (Matrix.of fun i k => (2 * Complex.I)⁻¹ * ∑ j, herm Hm (W ⟨τ, i⟩) (W ⟨τ, j⟩) * starRingEnd ℂ (Q (x k) ⟨τ, j⟩)) _ _
    ?_ ?_
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hx.2.2.2
  · ext k k'
    have := emb_eq (relab_inj c e) (relab_conj c e) Di Q _ h.2.2.2.2.2.2 (span_coord h) (im_form h)
      (fun a => hx.2.2.1 a k k') τ
    rw [Matrix.map_apply, (eq_mul_inv_iff_mul_eq₀ hI).2 this, sub_mul, sub_eq_add_neg, Matrix.add_apply]
    congr 1
    · simp only [part, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, perMat, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    · simp only [part, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, perMat, dualMat, Finset.sum_mul,
        Finset.mul_sum, map_sum, map_mul, Complex.conj_conj, ← Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def IsCoef (x : Hor.Idx D τ → Di.La) (Q : Di.La →+ (Pad.Letter D → ℂ)) (t : Hor.Idx D τ → ℂ)
    (s : Pad.Letter D → ℂ) : Prop :=
  (∀ i, s ⟨τ, i⟩ = ∑ k, t k * Q (x k) ⟨τ, i⟩) ∧
    ∀ j, starRingEnd ℂ (s ⟨conjEmb τ, j⟩) = ∑ k, t k * starRingEnd ℂ (Q (x k) ⟨conjEmb τ, j⟩)

theorem IsCoef.add {t t' : Hor.Idx D τ → ℂ} {s s' : Pad.Letter D → ℂ} (h : IsCoef x Q t s) (h' : IsCoef x Q t' s') :
    IsCoef x Q (t + t') (s + s') :=
  ⟨fun i => by simp only [Pi.add_apply, h.1, h'.1, add_mul, Finset.sum_add_distrib],
    fun j => by simp only [Pi.add_apply, map_add, h.2, h'.2, add_mul, Finset.sum_add_distrib]⟩

theorem IsCoef.smul {t : Hor.Idx D τ → ℂ} {s : Pad.Letter D → ℂ} (h : IsCoef x Q t s) (r : ℝ) :
    IsCoef x Q (r • t) (r • s) :=
  ⟨fun i => by simp only [Pi.smul_apply, Complex.real_smul, h.1, Finset.mul_sum, _root_.mul_assoc],
    fun j => by simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, h.2, Finset.mul_sum,
      _root_.mul_assoc]⟩

theorem isCoef_zero : IsCoef x Q 0 0 := ⟨fun i => by simp, fun j => by simp⟩

theorem isCoef_per (h : PerData c e Di Hm P W Q) {v : Di.La} {n : ℕ} (hn : n ≠ 0) {b : Hor.Idx D τ → 𝓞 E}
    (hb : ∑ k, b k • x k = n • v) :
    IsCoef x Q (fun k => (n : ℂ)⁻¹ * Formalism.L2.PjFree.relab c e τ (b k : E)) (Q v) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have key : ∀ z : Pad.Letter D, Q v z = ∑ k, (n : ℂ)⁻¹ * Formalism.L2.PjFree.relab c e z.1 (b k : E) * Q (x k) z := fun z => by
    have := congrFun (congrArg Q hb) z
    rw [map_sum, map_nsmul, Finset.sum_apply, Pi.smul_apply, nsmul_eq_mul] at this
    simp only [h.2.2.2.2.2.2] at this
    simp only [_root_.mul_assoc, ← Finset.mul_sum]
    rw [this, inv_mul_cancel_left₀ hn']
  refine ⟨fun i => key _, fun j => ?_⟩
  rw [key, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [relab_conj]
  simp [conjEmb]

theorem exists_coef {g' : ℕ} {Hm' : Matrix (Fin g') (Fin g') ℂ} {P' : Di.La →+ (Fin g' → ℂ)}
    {W' : Pad.Letter D → Fin g' → ℂ} {Q' : Di.La →+ (Pad.Letter D → ℂ)} {φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ)}
    (hx : IsPerBasis Di x hm) (h : PerData c e Di Hm P W Q) (h' : PerData c e Di Hm' P' W' Q')
    (hφ : ∀ a, φ (P a) = P' a) (u : Fin g → ℂ) :
    ∃ t s s', u = ∑ z, s z • W z ∧ φ u = ∑ z, s' z • W' z ∧ IsCoef x Q t s ∧ IsCoef x Q' t s' := by
  have hu : u ∈ Submodule.span ℝ (Set.range P) := h.2.2.1 ▸ Submodule.mem_top
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨v, rfl⟩ := hu
    obtain ⟨n, hn, hv⟩ := hx.2.1 v
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
    exact ⟨_, Q v, Q' v, h.2.2.2.2.2.1 v, (hφ v).trans (h'.2.2.2.2.2.1 v), isCoef_per h hn hb, isCoef_per h' hn hb⟩
  | zero => exact ⟨0, 0, 0, by simp, by simp, isCoef_zero, isCoef_zero⟩
  | add u u' _ _ h1 h2 =>
    obtain ⟨t, s, s', a1, a2, a3, a4⟩ := h1
    obtain ⟨t₂, s₂, s₂', b1, b2, b3, b4⟩ := h2
    refine ⟨_, _, _, ?_, ?_, a3.add b3, a4.add b4⟩
    · simp only [a1, b1, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    · simp only [map_add, a2, b2, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  | smul r u _ h1 =>
    obtain ⟨t, s, s', a1, a2, a3, a4⟩ := h1
    refine ⟨_, _, _, ?_, ?_, a3.smul r, a4.smul r⟩
    · rw [a1, Finset.smul_sum]
      simp only [Pi.smul_apply, smul_assoc]
    · rw [map_smul, a2, Finset.smul_sum]
      simp only [Pi.smul_apply, smul_assoc]

theorem sum_type (ρ : E →+* ℂ) (f : Pad.Letter D → ℂ) (hf : ∀ z, z.1 ≠ ρ → f z = 0) : ∑ z, f z = ∑ i, f ⟨ρ, i⟩ := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single ρ (fun ψ _ hψ => Finset.sum_eq_zero fun j _ => hf _ hψ) (by simp)]

theorem wedge_eq (hp : D.p = D.mult τ) (hq : D.q = D.mult (conjEmb τ)) (hx : IsPerBasis Di x hm)
    (h : PerData c e Di Hm P W Q) (hG : GoodPer c e τ x hm Q) {V : Fin D.p → Fin g → ℂ} {W₀ : Fin D.q → Fin g → ℂ}
    (hM : MatchVec τ W V W₀) {y : Fin D.q ⊕ Fin D.p → Fin g → ℂ} {Δ : ℂ} (hΔ : IsWedgeCoord Hm V W₀ y Δ)
    {t : Fin D.q ⊕ Fin D.p → Hor.Idx D τ → ℂ} {s : Fin D.q ⊕ Fin D.p → Pad.Letter D → ℂ}
    (hy : ∀ k, y k = ∑ z, s k z • W z) (ht : ∀ k, IsCoef x Q (t k) (s k)) :
    Δ = (Matrix.of fun k => t ((Equiv.sumCongr (finCongr hq) (finCongr hp)).symm k)).det *
      ((2 * Real.pi * Complex.I) ^ Fintype.card (Fin (D.mult (conjEmb τ))) * perVal c e τ x hm Q) := by
  obtain ⟨a, ha, rfl⟩ := hΔ
  obtain ⟨-, h0, -, S, hS⟩ := hG
  have hV : ∀ i, V i = W ⟨τ, finCongr hp i⟩ := fun i => hM.1 i _ rfl
  have hW : ∀ j, W₀ j = W ⟨conjEmb τ, finCongr hq j⟩ := fun j => hM.2 j _ rfl
  have hli : LinearIndependent ℂ V := by
    rw [funext hV]
    exact h.2.2.2.2.1.comp (fun i => (⟨τ, finCongr hp i⟩ : Pad.Letter D))
      fun i i' hi => (finCongr hp).injective (eq_of_heq (Sigma.mk.inj hi).2)
  have haeq : ∀ k, a k = fun i => s k ⟨τ, finCongr hp i⟩ := fun k => by
    refine proj_unique h.2.1 hli (ha k) fun i => ?_
    rw [← hl_apply, map_sub, hl_apply, hl_apply, hy, herm_sum_left, herm_sum_left, hV i,
      sum_type τ _ (fun z hz => by rw [orth h hz, mul_zero]), sub_eq_zero]
    simp only [hV]
    exact ((finCongr hp).sum_comp (fun m => s k ⟨τ, m⟩ * herm Hm (W ⟨τ, m⟩) (W ⟨τ, finCongr hp i⟩))).symm
  rw [perVal, horVal_eq h0 (dualMat_mul hx h) hS, ← det_fromRows_smul,
    ← Matrix.det_transpose (Matrix.fromRows _ _), ← Matrix.det_mul,
    ← Matrix.det_submatrix_equiv_self (Equiv.sumCongr (finCongr hq) (finCongr hp))]
  congr 1
  ext k m
  rw [Matrix.submatrix_apply, Matrix.mul_apply]
  simp only [Matrix.of_apply, Equiv.symm_apply_apply]
  rcases m with j | i
  · simp only [Matrix.of_apply, Sum.elim_inl,  Matrix.transpose_apply, Equiv.sumCongr_apply, Sum.map_inl, Matrix.fromRows_apply_inl, Matrix.smul_apply, dualMat,
      smul_eq_mul]
    rw [hW, hy, herm_sum_right, sum_type (conjEmb τ) _ (fun z hz => by rw [orth h (Ne.symm hz), zero_mul])]
    simp only [(ht k).2, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun i _ => ?_
    rw [herm_symm Hm h.1, map_mul, ← starRingEnd_apply]
    have hI := Complex.I_ne_zero
    field_simp
  · simp only [Matrix.of_apply, Sum.elim_inr,  Matrix.transpose_apply, Equiv.sumCongr_apply, Sum.map_inr, Matrix.fromRows_apply_inr, perMat, haeq, (ht k).1]

end GlobalTheory.DetLine.WedgePer

open GlobalTheory.DetLine.WedgePer in

theorem GlobalTheory.DetLine.perVal_mul_wedgeCoord : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (c : Coeff l) (e : c.F →+* ℂ) (τ : E →+* ℂ) (Di : Datum H) (x : Hor.Idx D τ → Di.La) (hm : Matrix (Hor.Idx D τ) (Hor.Idx D τ) E) (g g' : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (Hm' : Matrix (Fin g') (Fin g') ℂ) (P : Di.La →+ (Fin g → ℂ)) (P' : Di.La →+ (Fin g' → ℂ)) (W : Pad.Letter D → Fin g → ℂ) (W' : Pad.Letter D → Fin g' → ℂ) (Q Q' : Di.La →+ (Pad.Letter D → ℂ)) (φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ)) (V : Fin D.p → Fin g → ℂ) (W₀ : Fin D.q → Fin g → ℂ) (V' : Fin D.p → Fin g' → ℂ) (W₀' : Fin D.q → Fin g' → ℂ) (y : Fin D.q ⊕ Fin D.p → Fin g → ℂ) (Δ Δ' : ℂ), τ (H.rt : E) = H.rt0 → IsPerBasis Di x hm → PerData c e Di Hm P W Q → PerData c e Di Hm' P' W' Q' → GoodPer c e τ x hm Q → GoodPer c e τ x hm Q' → (∀ a, φ (P a) = P' a) → MatchVec τ W V W₀ → MatchVec τ W' V' W₀' → IsWedgeCoord Hm V W₀ y Δ → IsWedgeCoord Hm' V' W₀' (fun k => φ (y k)) Δ' → perVal c e τ x hm Q * Δ' = perVal c e τ x hm Q' * Δ := by
  intro E _ _ _ H D l c e τ Di x hm g g' Hm Hm' P P' W W' Q Q' φ V W₀ V' W₀' y Δ Δ' hτ hx h h' hG hG' hφ hM hM' hΔ hΔ'
  have hp : D.p = D.mult τ := (if_pos hτ).symm
  have hq : D.q = D.mult (conjEmb τ) := by
    refine (if_neg fun hc => ?_).symm
    have h1 : starRingEnd ℂ H.rt0 = H.rt0 := by rw [← hτ]; exact hc.trans hτ.symm
    have h2 := H.sqrt_neg_disc_sq
    rw [← Complex.conj_eq_iff_re.1 h1] at h2
    have h3 : H.rt0.re ^ 2 = -(H.d : ℝ) := by exact_mod_cast h2
    have h4 : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
    nlinarith [sq_nonneg H.rt0.re]
  choose t s s' hy hy' ht ht' using fun k => exists_coef hx h h' hφ (y k)
  rw [wedge_eq hp hq hx h hG hM hΔ hy ht, wedge_eq hp hq hx h' hG' hM' hΔ' hy' ht']
  ring

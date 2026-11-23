import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairAtTAdjCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurableOfContinuousOnZero

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section L2

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hs_self_re (A : Wq →L[ℂ] Wp) : (B.hsInner A A).re = ‖B.hsVec A‖ ^ 2 := by
  unfold B.hsInner
  simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (B.hsVec A)

theorem norm_hs_le (A C : Wq →L[ℂ] Wp) : ‖B.hsInner A C‖ ≤ ‖B.hsInner A A‖ + ‖B.hsInner C C‖ := by
  unfold B.hsInner
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (B.hsVec C) (B.hsVec A)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp only [norm_pow, RCLike.norm_ofReal, Complex.norm_real, abs_norm, norm_norm]
  nlinarith [norm_nonneg (B.hsVec A), norm_nonneg (B.hsVec C), sq_nonneg (‖B.hsVec A‖ - ‖B.hsVec C‖)]

end L2

section Cls

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem slice_pair_measurable (c : Fin r → ℂ) (Φ Ψ : RadSp k r z z' π π') :
    Measurable (fun x : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) := by
  obtain ⟨s, hs⟩ : ∃ s : Set (Mt k r), s = (fun x : Mt k r => (c, Matrix.of x)) ⁻¹' DomR k r z z' := ⟨_, rfl⟩
  have hsm : MeasurableSet s := by
    rw [hs, DomR_eq, Set.preimage_inter]
    exact ((P.Qx5.isOpen_OpR k r z z').preimage (cslice_continuous c)).measurableSet.inter
      (((P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage (cslice_continuous c)).measurableSet
  have hA : ∀ Ξ : RadSp k r z z' π π', ContinuousOn (fun x : Mt k r => (Ξ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) s :=
    fun Ξ => (radSp_continuousOn Ξ).comp ((cslice_continuous c).continuousOn : ContinuousOn _ s)
      (fun x hx => by rw [hs] at hx; exact hx)
  refine measurable_of_continuousOn_zero hsm
    ((P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn ((hA Φ).prodMk (hA Ψ))) ?_
  intro x hx
  have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) = 0 :=
    radSp_zero_off Φ (x := (c, Matrix.of x)) (by rw [hs] at hx; exact hx)
  show B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) _ = 0
  rw [h0, hsInner_zero_left]

def SliceSquareIntegrable (μ : Measure (Mt k r)) (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) : Prop :=
  Integrable (fun x : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
    ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ

theorem integrable_pair_of_square_integrable (μ : Measure (Mt k r)) {Φ Ψ : RadSp k r z z' π π'} {c : Fin r → ℂ} (hΦ : SliceSquareIntegrable μ Φ c)
    (hΨ : SliceSquareIntegrable μ Ψ c) :
    Integrable (fun x : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ := Integrable.mono' (hΦ.norm.add hΨ.norm) (slice_pair_measurable c Φ Ψ).aestronglyMeasurable
  (ae_of_all _ fun x => norm_hs_le _ _)

theorem slice_square_integrable_zero (μ : Measure (Mt k r)) (c : Fin r → ℂ) : SliceSquareIntegrable μ (0 : RadSp k r z z' π π') c := by
  have h0 : ∀ A : Wq →L[ℂ] Wp, B.hsInner 0 A = 0 := by
    intro A
    have h : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
      unfold B.hsVec; ext i; simp
    unfold B.hsInner
    rw [h, inner_zero_right]
  unfold SliceSquareIntegrable
  simpa [h0] using (integrable_zero (Mt k r) ℂ μ)

theorem slice_square_integrable_add (μ : Measure (Mt k r)) {Φ Ψ : RadSp k r z z' π π'} {c : Fin r → ℂ} (hΦ : SliceSquareIntegrable μ Φ c)
    (hΨ : SliceSquareIntegrable μ Ψ c) : SliceSquareIntegrable μ (Φ + Ψ) c := by
  have hΦΨ := integrable_pair_of_square_integrable μ hΦ hΨ
  have hΨΦ := integrable_pair_of_square_integrable μ hΨ hΦ
  unfold SliceSquareIntegrable at *
  simp only [Submodule.coe_add, Pi.add_apply, hs_add_left, hs_add_right]
  exact (hΦ.add hΨΦ).add (hΦΨ.add hΨ)

theorem slice_square_integrable_smul (μ : Measure (Mt k r)) (a : ℂ) {Φ : RadSp k r z z' π π'} {c : Fin r → ℂ} (hΦ : SliceSquareIntegrable μ Φ c) :
    SliceSquareIntegrable μ (a • Φ) c := by
  unfold SliceSquareIntegrable at *
  have e : ∀ x : Mt k r, B.hsInner (((a • Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      (((a • Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) =
      a * (conj a * B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
        ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) := by
    intro x
    rw [Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hs_smul_left, hs_smul_right]
  exact ((hΦ.const_mul (conj a)).const_mul a).congr (ae_of_all _ fun x => (e x).symm)

abbrev Lt := (Fin 2 × Fin 2 × ℂ) ⊕ Fin 6

def lop (X : ActualOps k r z z' π π') : Lt → Module.End ℂ (RadSp k r z z' π π') :=
  Sum.elim (fun p => X.t p.2.2 p.1 p.2.1) (fun j => X.fn j)

def wop (X : ActualOps k r z z' π π') (w : List Lt) : Module.End ℂ (RadSp k r z z' π π') :=
  (w.map (lop X)).prod

theorem wop_append_single (X : ActualOps k r z z' π π') (w : List Lt) (l : Lt) :
    wop X (w ++ [l]) = wop X w * lop X l := by
  simp [wop, List.prod_append]

def TopCls (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) : Submodule ℂ (RadSp k r z z' π π') where
  carrier := {Φ | ∀ c ∈ OmX r, (∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ Glev k r (Fin.last r), GGl k r z z' g < ε →
      (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) ∧ ∀ w : List Lt, SliceSquareIntegrable μ (wop X w Φ) c}
  zero_mem' := fun c _ => ⟨⟨1, one_pos, fun _ _ _ => rfl⟩, fun w => by rw [map_zero]; exact slice_square_integrable_zero μ c⟩
  add_mem' := by
    intro Φ Ψ hΦ hΨ c hc
    obtain ⟨⟨ε1, h1, h10⟩, hΦw⟩ := hΦ c hc
    obtain ⟨⟨ε2, h2, h20⟩, hΨw⟩ := hΨ c hc
    refine ⟨⟨min ε1 ε2, lt_min h1 h2, fun g hg hG => ?_⟩, fun w => ?_⟩
    · show (Φ : Fn k r (Wq →L[ℂ] Wp)) c g + (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0
      rw [h10 g hg (lt_of_lt_of_le hG (min_le_left _ _)), h20 g hg (lt_of_lt_of_le hG (min_le_right _ _)), add_zero]
    · rw [map_add]; exact slice_square_integrable_add μ (hΦw w) (hΨw w)
  smul_mem' := by
    intro a Φ hΦ c hc
    obtain ⟨⟨ε, h1, h10⟩, hΦw⟩ := hΦ c hc
    refine ⟨⟨ε, h1, fun g hg hG => ?_⟩, fun w => ?_⟩
    · show a • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0
      rw [h10 g hg hG, smul_zero]
    · rw [map_smul]; exact slice_square_integrable_smul μ a (hΦw w)

theorem lop_vanish (X : ActualOps k r z z' π π') (l : Lt) (Φ : RadSp k r z z' π π') (c : Fin r → ℂ)
    (hc : c ∈ OmX r) (ε : ℝ)
    (h0 : ∀ g ∈ Glev k r (Fin.last r), GGl k r z z' g < ε → (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) :
    ∀ g ∈ Glev k r (Fin.last r), GGl k r z z' g < ε → (lop X l Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 := by
  intro g hg hG
  by_cases hd : (c, g) ∈ DomR k r z z'
  · rcases l with ⟨a, b, Y⟩ | j
    · show (X.t Y a b Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0
      have e := X.t_apply Y a b Φ (c, g) hd
      simp only at e
      rw [e]
      set D : Set (Mx k r) := {g | 0 < GGl k r z z' g ∧ GGl k r z z' g < ε} with hDdef
      have hDo : IsOpen D := (isOpen_lt continuous_const (P.Qx5.GGl_continuous k r z z')).inter
        (isOpen_lt (P.Qx5.GGl_continuous k r z z') continuous_const)
      have hDG : D ⊆ {g | 0 < GGl k r z z' g} := fun g hg => hg.1
      have hgD : g ∈ Glev k r (Fin.last r) ∩ D := ⟨hg, hd.2.2, hG⟩
      have hS1 := smoothLev_slice Φ c hc D hDG
      have hS0 : SmoothLev k r (Fin.last r) D (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) := by
        intro g₀ _
        exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
      have hL := Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) D Y a b
        (fun g => (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) (fun _ => 0) 1 hDo hS1 hS0 g hgD
      have hL0 := Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) D Y a b
        (fun _ => (0 : Wq →L[ℂ] Wp)) (fun _ => 0) 1 hDo hS0 hS0 g hgD
      have h00 : tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g = 0 := by
        have h := hL0.1
        simp only [smul_zero, add_zero, one_smul] at h
        have h2 : tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g +
            tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g =
            tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g + 0 := by
          rw [add_zero]; exact h.symm
        exact add_left_cancel h2
      have hloc := hL.2 (fun x hx => h0 x hx.1 hx.2.2)
      rw [show (Φ : Fn k r (Wq →L[ℂ] Wp)) c = fun g => (Φ : Fn k r (Wq →L[ℂ] Wp)) c g from rfl, hloc, h00]
    · show (X.fn j Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0
      have e := X.fn_apply j Φ (c, g) hd
      simp only at e
      rw [e, h0 g hg hG, smul_zero]
  · exact radSp_zero_off (lop X l Φ) (x := (c, g)) hd

theorem lop_mem (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) (l : Lt) :
    ∀ Φ ∈ TopCls X μ, lop X l Φ ∈ TopCls X μ := by
  intro Φ hΦ c hc
  obtain ⟨⟨ε, hε, h0⟩, hw⟩ := hΦ c hc
  refine ⟨⟨ε, hε, lop_vanish X l Φ c hc ε h0⟩, fun w => ?_⟩
  have := hw (w ++ [l])
  rw [wop_append_single] at this
  exact this

theorem square_integrable_slice_of_mem (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) {Φ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ TopCls X μ) {c : Fin r → ℂ} (hc : c ∈ OmX r) : SliceSquareIntegrable μ Φ c := by
  have := (hΦ c hc).2 []
  simpa [wop] using this

theorem intOn_topCls (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) : IntOn μ (TopCls X μ) := fun c hc Φ hΦ Ψ hΨ => integrable_pair_of_square_integrable μ (square_integrable_slice_of_mem X μ hΦ hc) (square_integrable_slice_of_mem X μ hΨ hc)

end Cls

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

def UpperLeftBlockAdjoint (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r)) : Prop :=
  ∀ Y : ℂ, star Y = Y → ∀ c ∈ OmX P.r, ∀ Φ ∈ TopCls X μ, ∀ Ψ ∈ TopCls X μ,
    pairAt μ (X.t Y 0 0 Φ) Ψ c = pairAt μ Φ (X.t (star Y) 0 0 Ψ) c

theorem QQ_mem_adjAlg_top (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (hP : IsPlace P z z' π π') (X : ActualOps P.k P.r z z' π π')
    (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ)
    (h11 : UpperLeftBlockAdjoint P z z' π π' X μ) (Y : ℂ) (hY : star Y = Y) (a b : Fin 2) :
    X.QQ Y a b ∈ adjAlg μ (TopCls X μ) (intOn_topCls X μ) := by
  refine ⟨lop_mem X μ (Sum.inl (a, b, Y)), lop_mem X μ (Sum.inl (b, a, star Y)), fun c hc Φ hΦ Ψ hΨ => ?_⟩
  show pairAt μ (X.t Y a b Φ) Ψ c = pairAt μ Φ (X.t (star Y) b a Ψ) c
  by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    exact h11 Y hY c hc Φ hΦ Ψ hΨ
  · have hab' : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push_neg at h
      exact hab h
    obtain ⟨⟨ε1, h1, h10⟩, -⟩ := hΦ c hc
    obtain ⟨⟨ε2, h2, h20⟩, -⟩ := hΨ c hc
    have hm := fun (l : Lt) (Θ : RadSp P.k P.r z z' π π') (hΘ : Θ ∈ TopCls X μ) =>
      square_integrable_slice_of_mem X μ (lop_mem X μ l Θ hΘ) hc
    exact pairAt_t_adj_cut P z z' π π' hP X μ hμ Φ Ψ c hc (min ε1 ε2) (lt_min h1 h2)
      (fun g hg hG => h10 g hg (lt_of_lt_of_le hG (min_le_left _ _)))
      (fun g hg hG => h20 g hg (lt_of_lt_of_le hG (min_le_right _ _))) Y a b hab'
      (integrable_pair_of_square_integrable μ (hm (Sum.inl (a, b, Y)) Φ hΦ) (square_integrable_slice_of_mem X μ hΨ hc))
      (integrable_pair_of_square_integrable μ (square_integrable_slice_of_mem X μ hΦ hc) (hm (Sum.inl (b, a, star Y)) Ψ hΨ))
      (integrable_pair_of_square_integrable μ (hm (Sum.inl (1, 1, Y)) Φ hΦ) (square_integrable_slice_of_mem X μ hΨ hc))
      (integrable_pair_of_square_integrable μ (square_integrable_slice_of_mem X μ hΦ hc) (hm (Sum.inl (1, 1, star Y)) Ψ hΨ))

theorem adjTop_topCls (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (h11 : UpperLeftBlockAdjoint P z z' π π' X μ)
    (hK : K (Fin.last P.r) ≤ TopCls X μ) :
    AdjTop (S := S) P z z' π π' μ L st K l0 := by
  exact adjTop_of_tAdj (S := S) P z z' π π' X μ L st K l0 hD (TopCls X μ) (intOn_topCls X μ) hK
    (fun j Φ hΦ => lop_mem X μ (Sum.inr j) Φ hΦ)
    (fun Y hY a b => QQ_mem_adjAlg_top P z z' π π' hD.1 X μ hD.2.1 h11 Y hY a b)

end Top

end Formalism.FourierDecayAlt.P5.HerB

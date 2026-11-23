import Formalism.HermitianCurvature.StatementHeads
import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ}

def shS (l : Fin ρ) : Fin (1 + ρ) := ⟨l.val + 1, by omega⟩

theorem consC_sh (t : ℂ) (c : Fin ρ → ℂ) (l : Fin ρ) : consC t c (shS l) = c l := by
  simp [consC, shS]

theorem consC_zero (t : ℂ) (c : Fin ρ → ℂ) : consC t c ⟨0, by omega⟩ = t := by
  simp [consC]

theorem omX_consC {t : ℂ} (ht : t ≠ 0) (c : Fin ρ → ℂ) : consC t c ∈ OmX (1 + ρ) ↔ c ∈ OmX ρ := by
  simp only [OmX, Set.mem_setOf_eq]
  constructor
  · intro h l
    have := h (shS l)
    rwa [consC_sh] at this
  · intro h l
    unfold consC
    split_ifs with hl
    · exact ht
    · exact h _

def trF {E : Type*} (t : ℂ) (Φ : Fn k (1 + ρ) E) : Fn k ρ E := fun c g => Φ (consC t c) (ιLev k 1 ρ g)

theorem ιLev_comp (g : Mx k 0) : ιLev k 1 ρ (ιLev k ρ 0 g) = ιLev k (1 + ρ) 0 g := by
  ext p q
  simp only [ιLev]
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk] at *) <;> first | rfl | omega | (congr 1 <;> ext <;> simp only [Fin.val_mk] <;> omega)

theorem liftVec_comp (v : Fin (2 * 0 + k + 1) → ℂ) : liftVec k 1 ρ (liftVec k ρ 0 v) = liftVec k (1 + ρ) 0 v := by
  funext p
  simp only [liftVec]
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk] at *) <;> first | rfl | omega | (congr 1 <;> ext <;> simp only [Fin.val_mk] <;> omega)

def blk0 (z : Fin (2 * ρ + k + 1) → ℂ) : Fin (2 * 0 + k + 1) → ℂ := fun j => z ⟨ρ + j.val, by omega⟩

theorem lift_vector_zero_block {z : Fin (2 * ρ + k + 1) → ℂ} (hz : inWb k ρ z) : liftVec k ρ 0 (blk0 z) = z := by
  funext p
  have hp := p.isLt
  unfold liftVec blk0
  split_ifs with h
  · congr 1
    ext
    simp only [Fin.val_mk]
    omega
  · exact (hz p (by omega)).symm

theorem ιLev_inj {g g' : Mx k ρ} (h : ιLev k 1 ρ g = ιLev k 1 ρ g') : g = g' := by
  ext a b
  have h1 := congrFun (congrFun h ⟨a.val + 1, by omega⟩) ⟨b.val + 1, by omega⟩
  have ha : a.val ≤ 2 * ρ + k := by have := a.isLt; omega
  have hb : b.val ≤ 2 * ρ + k := by have := b.isLt; omega
  simpa [ιLev, ha, hb] using h1

theorem glev_image_last (r : ℕ) : Glev k r (Fin.last r) = ιLev k r 0 '' UH (Hpk k 0) :=
  QnGlevImageW.glevImage_of PI.QnLevBasicsW.level_group_homomorphism PI.QnLevBasicsW.level_group_unitary_hermitian k r 0

theorem glev_iota (g : Mx k ρ) : ιLev k 1 ρ g ∈ Glev k (1 + ρ) (Fin.last (1 + ρ)) ↔ g ∈ Glev k ρ (Fin.last ρ) := by
  rw [glev_image_last, glev_image_last]
  constructor
  · rintro ⟨g0, hg0, he⟩
    exact ⟨g0, hg0, ιLev_inj ((ιLev_comp g0).trans he)⟩
  · rintro ⟨g0, hg0, rfl⟩
    exact ⟨g0, hg0, (ιLev_comp g0).symm⟩

theorem fvec_last (r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]

theorem zeta_iota (z z' : Fin (2 * ρ + k + 1) → ℂ) (g : Mx k ρ) :
    zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (ιLev k 1 ρ g) =
      zetaL k ρ z z' (Fin.last ρ) g := by
  unfold zetaL
  rw [fvec_last, fvec_last, fvec_last, fvec_last, PIQnLT.mulVec_liftVec, PIQnLT.herm_liftVec]

theorem tz_iota (z : Fin (2 * ρ + k + 1) → ℂ) : Tz k (1 + ρ) (liftVec k 1 ρ z) = Tz k ρ z := by
  unfold Tz; rw [PIQnLT.herm_liftVec]

theorem ggl_iota (z z' : Fin (2 * ρ + k + 1) → ℂ) (g : Mx k ρ) :
    GGl k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (ιLev k 1 ρ g) = GGl k ρ z z' g := by
  unfold GGl; rw [zeta_iota, tz_iota, tz_iota]

theorem domR_iota {t : ℂ} (ht : t ≠ 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (c : Fin ρ → ℂ) (g : Mx k ρ) :
    (consC t c, ιLev k 1 ρ g) ∈ DomR k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') ↔ (c, g) ∈ DomR k ρ z z' := by
  show (consC t c ∈ OmX (1 + ρ) ∧ ιLev k 1 ρ g ∈ Glev k (1 + ρ) (Fin.last (1 + ρ)) ∧
      0 < GGl k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (ιLev k 1 ρ g)) ↔
    (c ∈ OmX ρ ∧ g ∈ Glev k ρ (Fin.last ρ) ∧ 0 < GGl k ρ z z' g)
  rw [omX_consC ht, glev_iota, ggl_iota]

theorem contDiff_consC (t : ℂ) : ContDiff ℝ ∞ (consC (ρ := ρ) t) := by
  refine contDiff_pi.2 (fun l => ?_)
  by_cases h : l.val = 0
  · simp only [consC, h, ↓reduceDIte]
    exact contDiff_const
  · simp only [consC, h, ↓reduceDIte]
    exact contDiff_pi.1 contDiff_id _

theorem contDiff_ιLev : ContDiff ℝ ∞ (ιLev k 1 ρ) := by
  refine contDiff_pi.2 (fun p => contDiff_pi.2 (fun q => ?_))
  unfold ιLev
  split_ifs
  · exact contDiff_pi.1 (contDiff_pi.1 contDiff_id _) _
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const

variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

theorem trF_mem {t : ℂ} (ht : t ≠ 0) {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)}
    {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)} {Φ : Fn k (1 + ρ) (Wq →L[ℂ] Wp)}
    (hΦ : Φ ∈ RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π') :
    trF t Φ ∈ RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)) := by
  obtain ⟨h0, hs, he⟩ := hΦ
  refine ⟨fun x hx => h0 _ fun h => hx ((domR_iota ht z z' x.1 x.2).1 h), fun x₀ hx₀ => ?_,
    fun x hx h hh h' hh' => ?_⟩
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hs _ ((domR_iota ht z z' x₀.1 x₀.2).2 hx₀)
    let e : (Fin ρ → ℂ) × Mx k ρ → (Fin (1 + ρ) → ℂ) × Mx k (1 + ρ) := fun x => (consC t x.1, ιLev k 1 ρ x.2)
    have he_c : ContDiff ℝ ∞ e :=
      ((contDiff_consC t).comp contDiff_fst).prodMk (contDiff_ιLev.comp contDiff_snd)
    refine ⟨e ⁻¹' U, F ∘ e, hU.preimage he_c.continuous, hxU, hF.comp he_c.contDiffOn (fun x hx => hx),
      fun x hx hg => ?_⟩
    exact hΦF (e x) hx ((glev_iota x.2).2 hg)
  · have hx' := (domR_iota ht z z' x.1 x.2).2 hx
    show Φ (consC t x.1) (ιLev k 1 ρ (h * x.2 * h')) = _
    rw [(PI.QnLevBasicsW.level_group_homomorphism k 1 ρ).2, (PI.QnLevBasicsW.level_group_homomorphism k 1 ρ).2]
    exact he _ hx' _ (PI.QnLevBasicsW.level_group_unitary_weyl k 1 ρ z h hh) _ (PI.QnLevBasicsW.level_group_unitary_weyl k 1 ρ z' h' hh')

def trL {t : ℂ} (ht : t ≠ 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp))
    (π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)) :
    RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π' →ₗ[ℂ]
      RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)) where
  toFun Φ := ⟨trF t (Φ : Fn k (1 + ρ) (Wq →L[ℂ] Wp)), trF_mem ht Φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem trL_apply {t : ℂ} (ht : t ≠ 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp))
    (π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)) (Φ : RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π') :
    ((trL ht z z' π π' Φ : RadSp k ρ z z' _ _) : Fn k ρ (Wq →L[ℂ] Wp)) = trF t (Φ : Fn k (1 + ρ) (Wq →L[ℂ] Wp)) := rfl

theorem tL_iota {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : inWb k ρ z) (hz' : inWb k ρ z') (Y : ℂ) (a b : Fin 2) (f : Mx k (1 + ρ) → E) {g : Mx k ρ}
    (hg : g ∈ Glev k ρ (Fin.last ρ)) :
    tL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) Y a b f (ιLev k 1 ρ g) =
      tL k ρ z z' (Fin.last ρ) Y a b (fun x => f (ιLev k 1 ρ x)) g := by
  rw [glev_image_last] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  obtain ⟨z0, rfl⟩ : ∃ z0, z = liftVec k ρ 0 z0 := ⟨blk0 z, (lift_vector_zero_block hz).symm⟩
  obtain ⟨z0', rfl⟩ : ∃ z0', z' = liftVec k ρ 0 z0' := ⟨blk0 z', (lift_vector_zero_block hz').symm⟩
  have e1 := Formalism.FourierDecayAlt.P.level_transfer E k (1 + ρ) 0 z0 z0' Y a b f g0 hg0
  have e2 := Formalism.FourierDecayAlt.P.level_transfer E k ρ 0 z0 z0' Y a b (fun x => f (ιLev k 1 ρ x)) g0 hg0
  have e3 : (fun x => f (ιLev k 1 ρ (ιLev k ρ 0 x))) = fun x => f (ιLev k (1 + ρ) 0 x) :=
    funext fun x => by rw [ιLev_comp]
  rw [liftVec_comp, liftVec_comp, ιLev_comp]
  calc _ = _ := e1
    _ = _ := by rw [← e3]; exact e2.symm

theorem diff_rad {r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') (g : Mx k r) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    DifferentiableAt ℝ (fun c' => Φ c' g) c := by
  by_cases hx : (c, g) ∈ DomR k r z z'
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hΦ.2.1 (c, g) hx
    have hU' : IsOpen ((fun c' => (c', g)) ⁻¹' U) := hU.preimage (continuous_id.prodMk continuous_const)
    have hd : DifferentiableAt ℝ (fun c' => F (c', g)) c :=
      ((hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)).comp c
        ((differentiableAt_id).prodMk (differentiableAt_const _))
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hU'.mem_nhds (show (c, g) ∈ U from hxU)] with c' hc'
    exact hΦF (c', g) hc' hx.2.1
  · have h0 : (fun c' => Φ c' g) = fun _ => 0 := by
      funext c'
      refine hΦ.1 (c', g) fun h => hx ⟨hc, h.2.1, h.2.2⟩
    rw [h0]; exact differentiableAt_const _

def insL : (Fin ρ → ℂ) →L[ℝ] (Fin (1 + ρ) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := consC 0
      map_add' := fun u v => by
        ext l; simp only [consC, Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun a v => by
        ext l; simp only [consC, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }

theorem insL_apply (v : Fin ρ → ℂ) : insL v = consC 0 v := rfl

theorem hasFDerivAt_consC (t : ℂ) (c : Fin ρ → ℂ) : HasFDerivAt (consC t) (insL (ρ := ρ)) c := by
  have e : consC (ρ := ρ) t = fun c' => insL c' + consC t 0 := by
    funext c' l
    simp only [insL_apply, consC, Pi.add_apply]
    split_ifs <;> simp
  rw [e]
  exact (insL (ρ := ρ)).hasFDerivAt.add_const _

theorem insL_single (l : Fin ρ) (x : ℂ) : insL (Pi.single l x) = Pi.single (shS l) x := by
  rw [insL_apply]
  funext j
  by_cases hj : j = shS l
  · subst hj
    simp [consC, shS]
  · rw [Pi.single_eq_of_ne hj]
    unfold consC
    split_ifs with h0
    · rfl
    · apply Pi.single_eq_of_ne
      intro e
      apply hj
      have := congrArg Fin.val e
      simp at this
      ext
      simp [shS]
      omega

theorem fderiv_consC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (t : ℂ) (f : (Fin (1 + ρ) → ℂ) → E)
    (c : Fin ρ → ℂ) (hf : DifferentiableAt ℝ f (consC t c)) (l : Fin ρ) (x : ℂ) :
    fderiv ℝ (fun c' => f (consC t c')) c (Pi.single l x) = fderiv ℝ f (consC t c) (Pi.single (shS l) x) := by
  have h := hf.hasFDerivAt.comp c (hasFDerivAt_consC t c)
  rw [show (fun c' => f (consC t c')) = f ∘ consC t from rfl, h.fderiv, ContinuousLinearMap.comp_apply, insL_single]

theorem opL_consC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {t : ℂ} (ht : t ≠ 0)
    (f : (Fin (1 + ρ) → ℂ) → E) (c : Fin ρ → ℂ) (hf : consC t c ∈ OmX (1 + ρ) → DifferentiableAt ℝ f (consC t c))
    (l : Fin ρ) (i : Fin 6) :
    opL l i (fun c' => f (consC t c')) c = opL (shS l) i f (consC t c) := by
  fin_cases i
  · show pOp l (fun c' => f (consC t c')) c = pOp (shS l) f (consC t c)
    unfold pOp
    by_cases hc : c ∈ OmX ρ
    · have hc' := (omX_consC ht c).2 hc
      rw [if_pos hc, if_pos hc', consC_sh]
      unfold wirt
      rw [fderiv_consC t f c (hf hc'), fderiv_consC t f c (hf hc')]
    · rw [if_neg hc, if_neg (fun h => hc ((omX_consC ht c).1 h))]
  · show cOp l (fun c' => f (consC t c')) c = cOp (shS l) f (consC t c)
    simp only [cOp, consC_sh]
  · show ciOp l (fun c' => f (consC t c')) c = ciOp (shS l) f (consC t c)
    simp only [ciOp, consC_sh]
  · show pbOp l (fun c' => f (consC t c')) c = pbOp (shS l) f (consC t c)
    unfold pbOp
    by_cases hc : c ∈ OmX ρ
    · have hc' := (omX_consC ht c).2 hc
      rw [if_pos hc, if_pos hc', consC_sh]
      unfold wirtBar
      rw [fderiv_consC t f c (hf hc'), fderiv_consC t f c (hf hc')]
    · rw [if_neg hc, if_neg (fun h => hc ((omX_consC ht c).1 h))]
  · show cbOp l (fun c' => f (consC t c')) c = cbOp (shS l) f (consC t c)
    simp only [cbOp, consC_sh]
  · show cbiOp l (fun c' => f (consC t c')) c = cbiOp (shS l) f (consC t c)
    simp only [cbiOp, consC_sh]

end Formalism.FourierDecayAlt.P.PBH

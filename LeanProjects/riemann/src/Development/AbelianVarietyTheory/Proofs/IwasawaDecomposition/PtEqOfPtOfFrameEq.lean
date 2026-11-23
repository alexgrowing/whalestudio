import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.TrueCx.PointWell

open Formalism.L2.PjFree ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem moeb_mul {p q : ℕ} (g h : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ)
    (hu : IsUnit (h.toBlocks₂₁ * z + h.toBlocks₂₂).det) : moeb g (moeb h z) = moeb (g * h) z := by
  set A := h.toBlocks₁₁ * z + h.toBlocks₁₂ with hA
  set C := h.toBlocks₂₁ * z + h.toBlocks₂₂ with hC
  have e1 : (g * h).toBlocks₁₁ * z + (g * h).toBlocks₁₂ = (g.toBlocks₁₁ * (A * C⁻¹) + g.toBlocks₁₂) * C := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one, hA, hC]
    conv_lhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_toBlocks h, fromBlocks_multiply]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  have e2 : (g * h).toBlocks₂₁ * z + (g * h).toBlocks₂₂ = (g.toBlocks₂₁ * (A * C⁻¹) + g.toBlocks₂₂) * C := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one, hA, hC]
    conv_lhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_toBlocks h, fromBlocks_multiply]
    simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  show _ = ((g * h).toBlocks₁₁ * z + (g * h).toBlocks₁₂) * ((g * h).toBlocks₂₁ * z + (g * h).toBlocks₂₂)⁻¹
  rw [e1, e2, Matrix.mul_inv_rev, ← Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hu]
  rfl

theorem moeb_one {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) : moeb 1 z = z := by
  rw [← fromBlocks_one, moeb, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂]
  simp

theorem orbR_symm {ι : Type} [Fintype ι] {p q : ℕ} {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (hΓ : Γ ≤ UpqI ι p q)
    {z z' : DomI ι p q} (h : orbR Γ z z') : orbR Γ z' z := by
  obtain ⟨γ, hγ, e⟩ := h
  refine ⟨γ⁻¹, Γ.inv_mem hγ, ?_⟩
  rw [← e]
  funext t
  have hu := kapQ_isUnit (hΓ hγ t trivial) (z.2 t)
  show moeb (γ t)⁻¹.1 (moeb (γ t).1 (z.1 t)) = _
  rw [moeb_mul _ _ _ hu, Units.inv_mul, moeb_one]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem block_of_moeb_eq {j : ℕ} (hj : j ≤ r) (hp : X.p0 = r - j) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hx' : x' ∈ X.dom) (τ : X.Ψ) (h : moeb (frameCo X hj x τ) 0 = moeb (frameCo X hj x' τ) 0) (a b : Fin r)
    (ha : X.p0 ≤ a) (hb : (b : ℕ) < X.p0) : ((mat x τ)⁻¹ * mat x' τ) a b = 0 := by
  have hu := frameCo_isUnit₂₂ X hj hp hx τ
  have hu' := frameCo_isUnit₂₂ X hj hp hx' τ
  have hd : IsUnit (mat x τ).det := (hx τ).1.isUnit
  have hd0 : IsUnit (mat (x0F X) τ).det := (det_x0F X τ).isUnit
  have hN : (frameCo X hj x τ)⁻¹ * frameCo X hj x' τ = reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ) := by
    simp only [frameCo, inv_reindex]
    simp only [reindex_apply, submatrix_mul_equiv]
    rw [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hd0, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd0]
  have hf : IsUnit (frameCo X hj x τ).det := by
    rw [frameCo, det_reindex_self, det_mul]
    exact (isUnit_nonsing_inv_det _ hd0).mul hd
  rw [moeb_zero, moeb_zero] at h
  generalize frameCo X hj x τ = f at *
  generalize frameCo X hj x' τ = f' at *
  have h1 : f'.toCols₂ = f * fromRows (0 : Matrix (Fin j) (Fin (r - j)) ℂ) (f.toBlocks₂₂⁻¹ * f'.toBlocks₂₂) := by
    have h0 := fromBlocks_mul_fromRows (0 : Matrix (Fin j) (Fin (r - j)) ℂ) (f.toBlocks₂₂⁻¹ * f'.toBlocks₂₂)
      f.toBlocks₁₁ f.toBlocks₁₂ f.toBlocks₂₁ f.toBlocks₂₂
    rw [fromBlocks_toBlocks] at h0
    refine Eq.trans ?_ h0.symm
    simp only [Matrix.mul_zero, zero_add]
    rw [mul_nonsing_inv_cancel_left _ _ hu, ← Matrix.mul_assoc, h, nonsing_inv_mul_cancel_right _ _ hu']
    ext (a | a) b <;> rfl
  have h2 : (f⁻¹ * f').toCols₂ = fromRows (0 : Matrix (Fin j) (Fin (r - j)) ℂ) (f.toBlocks₂₂⁻¹ * f'.toBlocks₂₂) :=
    (congrArg (f⁻¹ * ·) h1).trans (nonsing_inv_mul_cancel_left f _ hf)
  have hb' : (b : ℕ) < r - j := hp ▸ hb
  have ha' : (a : ℕ) - (r - j) < j := by have := a.2; omega
  have h3 := congrFun (congrFun h2 (Sum.inl ⟨_, ha'⟩)) ⟨_, hb'⟩
  rw [hN] at h3
  have ea : (idx hj).symm (Sum.inl ⟨_, ha'⟩) = a := Fin.ext (by rw [idx_symm_inl]; simp only; omega)
  have eb : (idx hj).symm (Sum.inr ⟨_, hb'⟩) = b := Fin.ext (by rw [idx_symm_inr])
  simpa [toCols₂, ea, eb] using h3

theorem perFr_mem {A : Type} (S : Submodule ℂ (A → ℂ)) (w : A → Fin r → E) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h1 : ∀ τ (a b : Fin r), X.p0 ≤ a → (b : ℕ) < X.p0 → ((mat x τ)⁻¹ * mat x' τ) a b = 0)
    (h2 : ∀ τ (a b : Fin r), X.p0 ≤ a → (b : ℕ) < X.p0 → ((mat x' τ)⁻¹ * mat x τ) a b = 0)
    (τ : E →+* ℂ) (m : ℕ) (hm : τ ∈ X.Ψ → m = r - X.p0) (hm' : τ ∉ X.Ψ → m = X.p0)
    (hS : ∀ i < m, (fun a => perFr X x (w a) τ i) ∈ S) (i : ℕ) (hi : i < m) :
    (fun a => perFr X x' (w a) τ i) ∈ S := by
  have hp := X.p0_le
  by_cases h : τ ∈ X.Ψ
  · have hm := hm h
    have hd : IsUnit (mat x ⟨τ, h⟩).det := (hx _).1.isUnit
    have hi' : X.p0 + i < r := by omega
    have key : (∑ b : Fin r, ((mat x' ⟨τ, h⟩)⁻¹ * mat x ⟨τ, h⟩) ⟨_, hi'⟩ b •
        fun a => ((mat x ⟨τ, h⟩)⁻¹.mulVec (Data.emb τ (w a))) b) ∈ S := by
      refine Submodule.sum_mem _ fun b _ => ?_
      by_cases hb : (b : ℕ) < X.p0
      · rw [h2 _ _ _ (Nat.le_add_right _ _) hb, zero_smul]; exact zero_mem _
      · refine Submodule.smul_mem _ _ ?_
        have hbr := b.2
        convert hS (b - X.p0) (by omega) using 2 with a
        unfold perFr
        rw [dif_pos h, dif_pos (by omega)]
        congr 1
        exact Fin.ext (by simp; omega)
    convert key using 2 with a
    unfold perFr
    rw [dif_pos h, dif_pos hi']
    conv_lhs => rw [← mul_nonsing_inv_cancel_right (mat x ⟨τ, h⟩) (mat x' ⟨τ, h⟩)⁻¹ hd, ← mulVec_mulVec]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  · have hm := hm' h
    have h' : conjEmb τ ∈ X.Ψ := by_contra fun h' => h ((X.cmType τ).2 h')
    have hd : IsUnit (mat x ⟨_, h'⟩).det := (hx _).1.isUnit
    have hi' : X.p0 - 1 - i < r := by omega
    have key : (∑ b : Fin r, ((mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩) b ⟨_, hi'⟩ •
        fun a => hermC (conjEmb τ) X.Gm (ReciprocityTheory.ChartRestriction.G.FD.col (mat x ⟨_, h'⟩) b) (Data.emb (conjEmb τ) (w a))) ∈ S := by
      refine Submodule.sum_mem _ fun b _ => ?_
      by_cases hb : (b : ℕ) < X.p0
      · refine Submodule.smul_mem _ _ ?_
        convert hS (X.p0 - 1 - b) (by omega) using 2 with a
        unfold perFr
        rw [dif_neg h, dif_pos h', dif_pos (by omega)]
        congr 2
        exact Fin.ext (by simp; omega)
      · rw [h1 _ _ _ (not_lt.1 hb) (by simp only; omega), zero_smul]; exact zero_mem _
    convert key using 2 with a
    unfold perFr
    rw [dif_neg h, dif_pos h', dif_pos hi']
    conv_lhs => rw [← mul_nonsing_inv_cancel_left (mat x ⟨_, h'⟩) (mat x' ⟨_, h'⟩) hd]
    generalize (mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩ = n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, mul_apply, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (f := fun b c => ∑ d, n b _ * _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}
  {U : Unf Xo c σ r}

theorem pt_eq_of_block (hU : IsUnf U) (hσ : GoodEmb c σ) (k : U.Comp) (x x' : (U.X k).dom)
    (h1 : ∀ τ (a b : Fin r), (U.X k).p0 ≤ a → (b : ℕ) < (U.X k).p0 → ((mat x.1 τ)⁻¹ * mat x'.1 τ) a b = 0)
    (h2 : ∀ τ (a b : Fin r), (U.X k).p0 ≤ a → (b : ℕ) < (U.X k).p0 → ((mat x'.1 τ)⁻¹ * mat x.1 τ) a b = 0) :
    (U.un k x).x = (U.un k x').x := by
  obtain ⟨hr, hty, -, -, -, g, e, F, ik, φ, -, hF⟩ := hU
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hty k
  obtain ⟨P, hP, hper, hx, -⟩ := hF k x
  obtain ⟨P', hP', hper', hx', -⟩ := hF k x'
  have hmem : ∀ j, (fun a => P' a j) ∈ Submodule.span ℂ (Set.range fun (j : Fin g) a => P a j) := by
    intro j
    simp only [hP']
    refine perFr_mem (U.X k) _ (fun a => (φ k a : Fin r → E)) x.2 h1 h2 _ (Dw.mult (e j).1) (fun h => ?_)
      (fun h => ?_) (fun i hi => ?_) _ (e j).2.2
    · exact (if_pos ((hrt _).1 ((hty _).1 h))).trans (by omega)
    · exact (if_neg (fun h' => h ((hty _).2 ((hrt _).2 h')))).trans hp0.symm
    · refine Submodule.subset_span ⟨e.symm ⟨(e j).1, ⟨i, hi⟩⟩, funext fun a => ?_⟩
      dsimp only
      rw [hP, Equiv.apply_symm_apply]
  choose μ hμ using fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hmem j)
  have hL : ∀ a, P' a = mulVecLin (of μ) (P a) := fun a => funext fun j => by
    have := congrFun (hμ j) a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    rfl
  have hsurj : Function.Surjective (mulVecLin (of μ)) := by
    intro y
    have hy : y ∈ Submodule.span ℝ (Set.range P') := by rw [hper'.2.2.2.1]; trivial
    refine (Submodule.span_le (p := (LinearMap.range (mulVecLin (of μ))).restrictScalars ℝ)).2 ?_ hy
    rintro _ ⟨a, rfl⟩
    exact ⟨P a, (hL a).symm⟩
  rw [hx, hx']
  exact (F.fibre _ P P' hper hper').2 ⟨LinearEquiv.refl _ _,
    LinearEquiv.ofBijective _ ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩, fun _ _ => rfl,
    fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hL⟩

theorem pt_lact (hU : IsUnf U) (k : U.Comp) (x : (U.X k).dom) {γ : GL (Fin r) E} (hγ : γ ∈ (U.X k).Γ) :
    (U.un k ⟨lact γ x.1, KU.lact_dom _ hγ x.2⟩).x = (U.un k x).x := by
  obtain ⟨t, ht⟩ := (hU.2.2.2.1 k k x ⟨lact γ x.1, KU.lact_dom _ hγ x.2⟩).2
    ⟨γ, hγ, fun _ => (1 : Matrix (Fin r) (Fin r) ℂ), fun τ => ⟨by
      show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
      simp, fun a b h => one_apply_ne h.ne'⟩, by
      congr 1
      funext τ
      exact (Matrix.mul_one (mat (lact γ x.1) τ)).symm⟩
  exact ht.1

theorem pt_eq_of_ptOfFrame_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r j : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (hU : Formalism.L2.PjFree.IsUnf U) (e : Dw.p = j) (Tau : Type) [Fintype Tau] (hr : 0 < r) (T : Tau ≃ {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}) (B : ∀ k, BdData Tau j (r - j) (gammaU (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k))) (s : U.Comp → Tau → ℂˣ), Formalism.L2.PjFree.GoodEmb c σ → ∀ (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom), ptOfFrame (le_of_isUnf U hU e) U.X hr (first_index_eq_of_unfolded U hU e) (cmEquiv U hU T) B s k x = ptOfFrame (le_of_isUnf U hU e) U.X hr (first_index_eq_of_unfolded U hU e) (cmEquiv U hU T) B s k' x' → (U.un k x).x = (U.un k' x').x := by
  intro E _ _ _ H Dw l Xo c σ r j U hU e Tau _ hr T B s hσ k k' x x' h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj h
  have h3 := eq_of_heq h2
  have hj := le_of_isUnf U hU e
  have hp := first_index_eq_of_unfolded U hU e k
  let S : DomI Tau j (r - j) → Set _ := fun z =>
    {y | ∃ w : (U.X k).dom, domPt (U.X k) hj (cmEquiv U hU T k) w = z ∧ (U.un k w).x = y}
  have hle : ∀ z z', orbR (gammaU (U.X k) hj (cmEquiv U hU T k)) z z' → S z ⊆ S z' := by
    rintro z z' ⟨_, ⟨γ, hγ, rfl⟩, hz⟩ _ ⟨w, hw, rfl⟩
    exact ⟨_, by rw [← hz, ← hw]; exact domPt_lact _ _ _ hp γ w.2, pt_lact hU k w hγ⟩
  have h4 := congrArg (Quot.lift S fun z z' hz =>
    (hle z z' hz).antisymm (hle z' z (orbR_symm (gammaU_le _ _ _ hp) hz))) h3
  obtain ⟨w, hw, hy⟩ : (U.un k x).x ∈ S ⟨_, domPt_mem (U.X k) hj (cmEquiv U hU T k) hp x'.2⟩ := by
    have : (U.un k x).x ∈ S ⟨_, domPt_mem (U.X k) hj (cmEquiv U hU T k) hp x.2⟩ := ⟨x, rfl, rfl⟩
    exact (Set.ext_iff.1 h4 _).1 this
  have h5 : ∀ τ, moeb (frameCo (U.X k) hj w.1 τ) 0 = moeb (frameCo (U.X k) hj x'.1 τ) 0 := fun τ => by
    obtain ⟨t, rfl⟩ := (cmEquiv U hU T k).surjective τ
    exact congrFun hw t
  rw [← hy]
  exact pt_eq_of_block hU hσ k w x' (fun τ => block_of_moeb_eq _ hj hp w.2 x'.2 τ (h5 τ))
    fun τ => block_of_moeb_eq _ hj hp x'.2 w.2 τ (h5 τ).symm

end GlobalTheory.TrueCx.PointWell

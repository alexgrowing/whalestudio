import Formalism.LocalToGlobal.GroupLattices.FockModels.ElementaryDivisorBasis

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

theorem edgeLat_of_G {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) (e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1))
    (g : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) (hgE : IsEdgeBasis p G.P.r e g) :
    (∀ s, extO G.O (G.P.ι v) (G.P.σ v) s e.src = colSpan G.O (la_tw (G.P.ι v) (G.P.σ v) s g)) ∧
      (∀ s, LeAt p (G.P.ι v) (G.P.σ v) G.P.w s e =
        colSpan G.O (la_tw (G.P.ι v) (G.P.σ v) s g * lb_D (G.P.m + 1) G.P.r (algebraMap G.O G.Kf G.P.w))) ∧
      (∀ s, extO G.O (G.P.ι v) (G.P.σ v) s e.tgt =
        colSpan G.O (la_tw (G.P.ι v) (G.P.σ v) s g * lb_D (G.P.m + 1) G.P.r (algebraMap G.O G.Kf G.P.w) *
          lb_D (G.P.m + 1) G.P.r (algebraMap G.O G.Kf G.P.w))) := by
  obtain ⟨hg, hsrc, htgt⟩ := hgE
  unfold lb_D
  set c : G.Kf := algebraMap G.O G.Kf G.P.w with hc
  have hw : c ≠ 0 := ch_w_ne_zero G v
  have hpK : (p : G.Kf) = c ^ 2 := nt_p_eq G v
  have hpK0 : (p : G.Kf) ≠ 0 := by rw [hpK]; exact pow_ne_zero _ hw
  have hpQ0 : (p : G.P.Qq v) ≠ 0 := by
    intro h0
    apply hpK0
    have := congrArg (G.P.ι v) h0
    simpa using this
  set dK : Fin (G.P.m + 1) → G.Kf := fun a => if a.val < G.P.r then c⁻¹ else 1 with hdK
  set dQ : Fin (G.P.m + 1) → G.P.Qq v := fun a => if a.val < G.P.r then ((p : G.P.Qq v))⁻¹ else 1 with hdQ
  have hDD : ∀ s, la_tw (G.P.ι v) (G.P.σ v) s (g * Matrix.diagonal dQ) =
      la_tw (G.P.ι v) (G.P.σ v) s g * Matrix.diagonal dK * Matrix.diagonal dK := by
    intro s
    ext i j
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.mul_diagonal, lb_tw_apply, lb_tw_apply,
      Matrix.mul_diagonal, map_mul, map_mul]
    congr 1
    simp only [hdQ, hdK]
    split_ifs
    · rw [map_inv₀, map_inv₀, map_natCast, map_natCast, hpK, pow_two, mul_inv]
    · simp
  have e1 : ∀ s, extO G.O (G.P.ι v) (G.P.σ v) s e.src = colSpan G.O (la_tw (G.P.ι v) (G.P.σ v) s g) :=
    fun s => by rw [hsrc]; exact la_extO_G G v s g
  have e3 : ∀ s, extO G.O (G.P.ι v) (G.P.σ v) s e.tgt =
      colSpan G.O (la_tw (G.P.ι v) (G.P.σ v) s g * Matrix.diagonal dK * Matrix.diagonal dK) :=
    fun s => by rw [htgt, la_extO_G, hDD]
  refine ⟨e1, ?_, e3⟩
  intro s
  set gK := la_tw (G.P.ι v) (G.P.σ v) s g with hgK
  apply le_antisymm
  · unfold LeAt
    refine sup_le ?_ ?_
    · rw [e1]
      intro x hx
      have h1 : gK = gK * Matrix.diagonal dK *
          Matrix.diagonal (fun a : Fin (G.P.m + 1) => if a.val < G.P.r then c else 1) := by
        rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
        have h2 : (fun a : Fin (G.P.m + 1) => dK a * (if a.val < G.P.r then c else 1)) = fun _ => 1 := by
          funext a
          simp only [hdK]
          split_ifs
          · exact inv_mul_cancel₀ hw
          · simp
        rw [h2, Matrix.diagonal_one, Matrix.mul_one]
      have hx' : x ∈ colSpan G.O gK := hx
      rw [h1] at hx'
      have h3 := lb_col (gK * Matrix.diagonal dK) _
        (fun a : Fin (G.P.m + 1) => if a.val < G.P.r then G.P.w else 1) 1
        (by intro j; split_ifs <;> simp [hc]) x hx'
      rw [one_smul] at h3
      exact h3
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h1 : c⁻¹ • twistVec (G.P.ι v) (G.P.σ v) s ((p : G.P.W v) • x) =
          G.P.w • twistVec (G.P.ι v) (G.P.σ v) s x := by
        funext i
        rw [Pi.smul_apply, Pi.smul_apply, lb_tw_p, smul_eq_mul, Algebra.smul_def, ← hc, hpK]
        show c⁻¹ * (c ^ 2 * _) = c * (G.P.ι v) ((G.P.σ v ^ s) (x i))
        field_simp
      have h2 : twistVec (G.P.ι v) (G.P.σ v) s x ∈
          colSpan G.O (gK * Matrix.diagonal dK * Matrix.diagonal dK) := by
        rw [← e3]; exact Submodule.subset_span ⟨x, hx, rfl⟩
      show c⁻¹ • twistVec (G.P.ι v) (G.P.σ v) s ((p : G.P.W v) • x) ∈ _
      rw [h1]
      exact lb_col (gK * Matrix.diagonal dK) dK
        (fun a : Fin (G.P.m + 1) => if a.val < G.P.r then 1 else G.P.w) G.P.w
        (by
          intro j
          simp only [hdK]
          split_ifs
          · rw [← hc, mul_inv_cancel₀ hw, map_one]
          · rw [mul_one]) _ h2
  · unfold colSpan
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    unfold LeAt
    by_cases hj : j.val < G.P.r
    · apply Submodule.mem_sup_right
      apply Submodule.subset_span
      refine ⟨fun i => (g * Matrix.diagonal dQ) i j, ?_, ?_⟩
      · rw [htgt]; exact Submodule.subset_span ⟨j, rfl⟩
      · funext i
        show c⁻¹ • twistVec (G.P.ι v) (G.P.σ v) s
          ((p : G.P.W v) • fun i => (g * Matrix.diagonal dQ) i j) i = (gK * Matrix.diagonal dK) i j
        rw [lb_tw_p, Matrix.mul_diagonal, Matrix.mul_diagonal, smul_eq_mul, hgK, lb_tw_apply]
        simp only [hdQ, hdK, hj, if_true, map_mul, map_inv₀, map_natCast]
        field_simp
    · apply Submodule.mem_sup_left
      apply Submodule.subset_span
      refine ⟨fun i => g i j, ?_, ?_⟩
      · rw [hsrc]; exact Submodule.subset_span ⟨j, rfl⟩
      · funext i
        simp only [twistVec, Matrix.mul_diagonal, hdK, hj, if_false, mul_one]
        rfl

section
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem edgeLat_of (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (e : Edge W Qq (m + 1))
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hgE : IsEdgeBasis p r e g) :
    (∀ s, extO O ι σ s e.src = colSpan O (la_tw ι σ s g)) ∧
      (∀ s, LeAt p ι σ w s e = colSpan O (la_tw ι σ s g * lb_D (m + 1) r (algebraMap O Kf w))) ∧
      (∀ s, extO O ι σ s e.tgt = colSpan O (la_tw ι σ s g * lb_D (m + 1) r (algebraMap O Kf w) *
          lb_D (m + 1) r (algebraMap O Kf w))) :=
  edgeLat_of_G (mkG h m r (fun _ _ => 0) (fun _ _ _ _ => le_rfl)) (0 : Fin 1) e g hgE

theorem extO_col (h : HidaSetting p n' W Qq O Kf ι σ j w) (m : ℕ) (s : ℕ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) : extO O ι σ s (colSpan W g) = colSpan O (la_tw ι σ s g) := by
  have hσ : ∀ (n : ℕ) (a : W), ∃ b : W, (σ ^ n) (algebraMap W Qq a) = algebraMap W Qq b := by
    intro n
    induction n with
    | zero => intro a; exact ⟨a, by simp⟩
    | succ n ih =>
      intro a
      obtain ⟨y, hy⟩ := h.frob a
      obtain ⟨b, hb⟩ := ih (a ^ p + (p : W) * y)
      exact ⟨b, by rw [pow_succ]; show (σ ^ n) (σ ((algebraMap W Qq) a)) = _; rw [hy, hb]⟩
  unfold extO colSpan
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact Submodule.subset_span ⟨c, rfl⟩
    | zero =>
      have h0 : twistVec ι σ s (0 : Fin (m + 1) → Qq) = 0 := by
        funext i
        simp [twistVec]
      rw [h0]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have h0 : twistVec ι σ s (x + y) = twistVec ι σ s x + twistVec ι σ s y := by
        funext i
        simp [twistVec]
      rw [h0]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      obtain ⟨b, hb⟩ := hσ s a
      have h0 : twistVec ι σ s (a • x) = j b • twistVec ι σ s x := by
        funext i
        simp only [twistVec, Pi.smul_apply, Algebra.smul_def, map_mul, hb, h.ι_comp]
      rw [h0]
      exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact Submodule.subset_span ⟨fun i => g i c, Submodule.subset_span ⟨c, rfl⟩, rfl⟩

end

end Formalism.L2.G.Model

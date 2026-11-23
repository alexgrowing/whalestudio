import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideLat

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

private theorem exists_twistVec_smul_eq_smul_twistVec {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
    (h : HidaSetting p n' W Qq O Kf ι σ j w) {k : ℕ} (s : ℕ) (a : W) (x : Fin k → Qq) :
    ∃ b : O, twistVec ι σ s (a • x) = b • twistVec ι σ s x := by
  have hσ : ∀ (t : ℕ) (x : W), ∃ y : W, (σ ^ t) (algebraMap W Qq x) = algebraMap W Qq y := by
    intro t
    induction t with
    | zero => exact fun x => ⟨x, by simp⟩
    | succ t ih =>
      intro x
      obtain ⟨y, hy⟩ := ih x
      obtain ⟨z, hz⟩ := h.frob y
      refine ⟨y ^ p + (p : W) * z, ?_⟩
      have hs : (σ ^ (t + 1)) (algebraMap W Qq x) = σ ((σ ^ t) (algebraMap W Qq x)) := by
        rw [pow_succ']
        rfl
      rw [hs, hy, hz]
  obtain ⟨y, hy⟩ := hσ s a
  refine ⟨j y, ?_⟩
  funext i
  simp only [twistVec, Pi.smul_apply, Algebra.smul_def, map_mul, hy, h.ι_comp]

private theorem leAt_eq_colSpan_la_tw_mul_lb_D_of_edgeBasis {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
    (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (e : Edge W Qq (m + 1))
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hgb : IsEdgeBasis p r e g) (s : ℕ) :
    LeAt p ι σ w s e = colSpan O (la_tw ι σ s g * lb_D (m + 1) r (algebraMap O Kf w)) := by
  obtain ⟨_, hsrc, htgt⟩ := hgb
  haveI := h.frac_alt
  have hpW : (p : W) ≠ 0 := h.p_unif.ne_zero
  have hpQ : (p : Qq) ≠ 0 := by
    have := (IsFractionRing.injective W Qq).ne hpW
    simpa using this
  have hpK : (p : Kf) ≠ 0 := by
    have := (map_ne_zero ι).mpr hpQ
    simpa using this
  have hpw : (p : Kf) = (algebraMap O Kf w) ^ 2 := by rw [← map_pow, h.w_sq, map_natCast]
  have hw0 : algebraMap O Kf w ≠ 0 := by
    intro h0
    apply hpK
    rw [hpw, h0]
    ring
  have tadd : ∀ x y : Fin (m + 1) → Qq, twistVec ι σ s (x + y) = twistVec ι σ s x + twistVec ι σ s y := by
    intro x y
    funext i
    simp [twistVec]
  have tzero : twistVec ι σ s (0 : Fin (m + 1) → Qq) = 0 := by
    funext i
    simp [twistVec]
  have tcol : ∀ c : Fin (m + 1), twistVec ι σ s (fun i => g i c) = fun i => la_tw ι σ s g i c := by
    intro c
    funext i
    simp [twistVec, la_tw, RingHom.mapMatrix_apply]
  have Rcol : ∀ c : Fin (m + 1), (fun i => (la_tw ι σ s g * lb_D (m + 1) r (algebraMap O Kf w)) i c) =
      (if c.val < r then (algebraMap O Kf w)⁻¹ else 1) • fun i => la_tw ι σ s g i c := by
    intro c
    funext i
    unfold lb_D
    rw [Matrix.mul_diagonal]
    split_ifs <;> simp [mul_comm]
  unfold LeAt
  rw [htgt]
  set T : (Fin (m + 1) → Qq) → (Fin (m + 1) → Kf) :=
    fun v => (algebraMap O Kf w)⁻¹ • twistVec ι σ s ((p : W) • v) with hT
  have Tadd : ∀ x y, T (x + y) = T x + T y := by
    intro x y
    simp only [hT, smul_add, tadd]
  have Tzero : T 0 = 0 := by
    simp only [hT, smul_zero, tzero]
  have Tsmul : ∀ (a : W) (x : Fin (m + 1) → Qq), ∃ b : O, T (a • x) = b • T x := by
    intro a x
    obtain ⟨b, hb⟩ := exists_twistVec_smul_eq_smul_twistVec h s a ((p : W) • x)
    refine ⟨b, ?_⟩
    simp only [hT]
    rw [smul_comm (p : W) a x, hb]
    exact smul_comm _ _ _
  have key : ∀ c : Fin (m + 1),
      T (fun i => (g * Matrix.diagonal fun c : Fin (m + 1) => if c.val < r then ((p : Qq))⁻¹ else 1) i c) =
        (if c.val < r then (algebraMap O Kf w)⁻¹ else algebraMap O Kf w) • fun i => la_tw ι σ s g i c := by
    clear Tadd Tzero Tsmul Rcol tcol tadd tzero hsrc htgt hpW hpQ
    intro c
    funext i
    have e1 : (g * Matrix.diagonal fun c : Fin (m + 1) => if c.val < r then ((p : Qq))⁻¹ else 1) i c =
        g i c * (if c.val < r then ((p : Qq))⁻¹ else 1) := Matrix.mul_diagonal _ _ _ _
    simp only [hT, Pi.smul_apply, smul_eq_mul, twistVec, e1]
    simp only [Algebra.smul_def, map_natCast, map_mul]
    split_ifs with hc
    · simp [la_tw, RingHom.mapMatrix_apply, map_inv₀]
      field_simp
      try simp
    · simp [la_tw, RingHom.mapMatrix_apply]
      rw [hpw]
      field_simp
  have hext : extO O ι σ s e.src = colSpan O (la_tw ι σ s g) := by
    rw [hsrc]
    unfold extO colSpan
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe] at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨c, rfl⟩ := hx
        exact Submodule.subset_span ⟨c, (tcol c).symm⟩
      | zero => rw [tzero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [tadd]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        obtain ⟨b, hb⟩ := exists_twistVec_smul_eq_smul_twistVec h s a x
        rw [hb]
        exact Submodule.smul_mem _ _ hx
    · rw [Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      exact Submodule.subset_span ⟨fun i => g i c, Submodule.subset_span ⟨c, rfl⟩, tcol c⟩
  rw [hext]
  unfold colSpan
  apply le_antisymm
  · apply sup_le
    · rw [Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      by_cases hc : c.val < r
      · have hA : (fun i => la_tw ι σ s g i c) =
            w • (fun i => (la_tw ι σ s g * lb_D (m + 1) r (algebraMap O Kf w)) i c) := by
          rw [Rcol c, if_pos hc, ← algebraMap_smul Kf w, smul_smul, mul_inv_cancel₀ hw0, one_smul]
        rw [SetLike.mem_coe]
        beta_reduce
        rw [hA]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
      · have hA : (fun i => la_tw ι σ s g i c) =
            (fun i => (la_tw ι σ s g * lb_D (m + 1) r (algebraMap O Kf w)) i c) := by
          rw [Rcol c, if_neg hc, one_smul]
        rw [SetLike.mem_coe]
        beta_reduce
        rw [hA]
        exact Submodule.subset_span ⟨c, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe] at hv ⊢
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨c, rfl⟩ := hx
        beta_reduce
        rw [key c]
        by_cases hc : c.val < r
        · rw [if_pos hc]
          exact Submodule.subset_span ⟨c, by beta_reduce; rw [Rcol c, if_pos hc]⟩
        · rw [if_neg hc, algebraMap_smul]
          refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, ?_⟩)
          beta_reduce
          rw [Rcol c, if_neg hc, one_smul]
      | zero => rw [Tzero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [Tadd]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        obtain ⟨b, hb⟩ := Tsmul a x
        rw [hb]
        exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe]
    beta_reduce
    by_cases hc : c.val < r
    · have hk := key c
      rw [if_pos hc] at hk
      rw [Rcol c, if_pos hc, ← hk]
      apply Submodule.mem_sup_right
      exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, rfl⟩, rfl⟩
    · rw [Rcol c, if_neg hc, one_smul]
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨c, rfl⟩)

theorem leAt_of_basis_G {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) (e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1))
    (g : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) (hgb : IsEdgeBasis p G.P.r e g) :
    ∀ s, LeAt p (G.P.ι v) (G.P.σ v) G.P.w s e =
      colSpan G.O (la_tw (G.P.ι v) (G.P.σ v) s g * lb_D (G.P.m + 1) G.P.r (algebraMap G.O G.Kf G.P.w)) := by
  intro s
  exact leAt_eq_colSpan_la_tw_mul_lb_D_of_edgeBasis (G.P.setting v) G.P.m G.P.r e g hgb s

section
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem leAt_of_basis (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (e : Edge W Qq (m + 1))
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hgb : IsEdgeBasis p r e g) (s : ℕ) :
    LeAt p ι σ w s e = colSpan O (la_tw ι σ s g * lb_D (m + 1) r (algebraMap O Kf w)) := by
  exact leAt_eq_colSpan_la_tw_mul_lb_D_of_edgeBasis h m r e g hgb s

theorem extO_colSpan (h : HidaSetting p n' W Qq O Kf ι σ j w) {k : ℕ} (g : Matrix (Fin k) (Fin k) Qq) (s : ℕ) :
    extO O ι σ s (colSpan W g) = colSpan O (la_tw ι σ s g) := by
  have hσ : ∀ (t : ℕ) (x : W), ∃ y : W, (σ ^ t) (algebraMap W Qq x) = algebraMap W Qq y := by
    intro t
    induction t with
    | zero => exact fun x => ⟨x, by simp⟩
    | succ t ih =>
      intro x
      obtain ⟨y, hy⟩ := ih x
      obtain ⟨z, hz⟩ := h.frob y
      refine ⟨y ^ p + (p : W) * z, ?_⟩
      have hs : (σ ^ (t + 1)) (algebraMap W Qq x) = σ ((σ ^ t) (algebraMap W Qq x)) := by
        rw [pow_succ']
        rfl
      rw [hs, hy, hz]
  have tadd : ∀ x y : Fin k → Qq, twistVec ι σ s (x + y) = twistVec ι σ s x + twistVec ι σ s y := by
    intro x y
    funext i
    simp [twistVec]
  have tzero : twistVec ι σ s (0 : Fin k → Qq) = 0 := by
    funext i
    simp [twistVec]
  have tsmul : ∀ (a : W) (x : Fin k → Qq), ∃ b : O, twistVec ι σ s (a • x) = b • twistVec ι σ s x := by
    intro a x
    obtain ⟨y, hy⟩ := hσ s a
    refine ⟨j y, ?_⟩
    funext i
    simp only [twistVec, Pi.smul_apply, Algebra.smul_def, map_mul, hy, h.ι_comp]
  have tcol : ∀ c : Fin k, twistVec ι σ s (fun i => g i c) = fun i => la_tw ι σ s g i c := by
    intro c
    funext i
    simp [twistVec, la_tw, RingHom.mapMatrix_apply]
  unfold extO colSpan
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ Submodule.span W (Set.range fun c : Fin k => fun i => g i c) := hv
    clear hv
    induction hv' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact Submodule.subset_span ⟨c, (tcol c).symm⟩
    | zero => rw [tzero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [tadd]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      obtain ⟨b, hb⟩ := tsmul a x
      rw [hb]
      exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact Submodule.subset_span ⟨fun i => g i c, Submodule.subset_span ⟨c, rfl⟩, tcol c⟩

end

section
variable {Qq Kf : Type} [Field Qq] [Field Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (s : ℕ) {k : ℕ}

theorem tw_mul (A B : Matrix (Fin k) (Fin k) Qq) : la_tw ι σ s (A * B) = la_tw ι σ s A * la_tw ι σ s B := by
  unfold la_tw
  exact map_mul _ A B

theorem tw_invT (g : Matrix (Fin k) (Fin k) Qq) (hg : IsUnit g.det) :
    la_tw ι σ s (g⁻¹).transpose = ((la_tw ι σ s g)⁻¹).transpose := by
  have key : la_tw ι σ s g⁻¹ = (la_tw ι σ s g)⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    rw [← tw_mul, Matrix.nonsing_inv_mul _ hg]
    unfold la_tw
    exact map_one _
  rw [← key]
  ext a b
  rfl

theorem tw_dE (r p : ℕ) : la_tw ι σ s (dE k r (p : Qq)) = dE k r (p : Kf) := by
  unfold la_tw dE
  rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext a
  split_ifs <;> simp

theorem dE_sq_D (r : ℕ) (c : Kf) (hc : c ≠ 0) : dE k r (c ^ 2) * lb_D k r c = dE k r c := by
  unfold dE lb_D
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  split_ifs <;> simp [pow_two, mul_assoc, hc]

end

theorem det_invT_zpow {Kf : Type} [Field Kf] {k : ℕ} (M : Matrix (Fin k) (Fin k) Kf) (hM : IsUnit M.det) (e : ℤ) :
    M.det ^ e * ((M⁻¹).transpose).det ^ e = 1 := by
  rw [Matrix.det_transpose, Matrix.det_nonsing_inv, ← mul_zpow, Ring.mul_inverse_cancel _ hM, one_zpow]

theorem posCore_of_form {O Kf : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (p m : ℕ) (lam : Fin (m + 1) → ℤ) (N : ℕ)
    (B : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] Kf)
    (ha : ∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf),
        B (rowAct Kf g P) Q = B P (rowAct Kf g.transpose Q))
    (hb : ∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam),
        (∀ P ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam), B P Q = 0) → Q = 0)
    (hc : ∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam),
        (∀ P ∈ nabO O Kf m (nuOf lam), B P Q ∈ Set.range (algebraMap O Kf)) → Q ∈ nabO O Kf m (nuOf lam))
    (hdd : ∀ Q ∈ nabO O Kf m (nuOf lam), ∀ P ∈ nabO O Kf m (nuOf lam),
        B P (((p : Kf) ^ N) • Q) ∈ Set.range (algebraMap O Kf)) :
    ∃ β, PosCore O Kf p m lam N β := by
  classical
  set V := dualWeyl Kf (m + 1) (m + 1) (nuOf lam) with hV
  obtain ⟨Z0, -⟩ := latBasis (O := O) hinj m lam 1 (by simp)
  have hfinI : Finite ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) := (sSIdxFinite (m + 1) (m + 1) (nuOf lam)).to_subtype
  have hfd : FiniteDimensional Kf V := Module.Finite.of_basis Z0
  let β0 : V →ₗ[Kf] Module.Dual Kf V :=
    LinearMap.mk₂ Kf (fun (Q P : V) => B (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) Q)
      (by intro Q Q' P; simp)
      (by intro c Q P; simp)
      (by intro Q P P'; simp)
      (by intro c Q P; simp)
  have hβ0 : ∀ Q P : V, β0 Q P = B (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) Q := fun _ _ => rfl
  have hinjβ : Function.Injective β0 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Q hQ
    apply Subtype.ext
    apply hb _ Q.2
    intro P hP
    have := congrArg (fun f => f ⟨P, hP⟩) hQ
    exact this
  let β : V ≃ₗ[Kf] Module.Dual Kf V := LinearMap.linearEquivOfInjective β0 hinjβ Subspace.dual_finrank_eq.symm
  have hβ : ∀ Q P : V, β Q P = B (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) Q := fun _ _ => rfl
  set e : ℤ := lam (Fin.last m) with he
  have key : ∀ (M : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf), IsUnit M.det →
      ∀ P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf,
      B (M.det ^ e • rowAct Kf M P) (((M⁻¹).transpose).det ^ e • rowAct Kf (M⁻¹).transpose Q) = B P Q := by
    intro M hM P Q
    rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, smul_eq_mul, mul_comm (((M⁻¹).transpose).det ^ e),
      det_invT_zpow M hM e, one_mul, ← ha, ldlat_rowAct_inv_right rowActMul M hM]
  have mem_iff : ∀ (M : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf), IsUnit M.det →
      ∀ F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf,
      F ∈ nablaLTw O Kf m lam M ↔ M.det ^ e • rowAct Kf M F ∈ nabO O Kf m (nuOf lam) :=
    fun M hM F => nablaLTwMem O Kf m lam M hM F
  refine ⟨β, ⟨?_, ?_⟩⟩
  · intro M hM Q hQ
    rw [mem_iff _ (det_invT M hM)]
    apply hc
    · exact Submodule.smul_mem _ _ (dualWeylRowStable Kf _ _ _ _ _ Q.2)
    · intro P0 hP0
      set P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf := M.det ^ (-e) • rowAct Kf M⁻¹ P0 with hP
      have h1 : M.det ^ e • rowAct Kf M P = P0 := by
        rw [hP, map_smul, smul_smul, ← zpow_add₀ hM.ne_zero, add_neg_cancel, zpow_zero, one_smul,
          ldlat_rowAct_inv_left rowActMul M hM]
      have h2 : P ∈ nablaLTw O Kf m lam M := by
        rw [mem_iff M hM, h1]; exact hP0
      have h3 := hQ ⟨P, la_nablaLTw_le m lam M hM P h2⟩ h2
      rw [hβ, ← key M hM, h1] at h3
      exact h3
  · intro M hM Q P hQ hP
    rw [hβ]
    have h1 := (mem_iff M hM _).1 hP
    have h2 := (mem_iff _ (det_invT M hM) _).1 hQ
    have h3 := hdd _ h2 _ h1
    rw [map_smul, key M hM] at h3
    rw [Submodule.coe_smul, map_smul]
    exact h3

end Formalism.L2.G.Model

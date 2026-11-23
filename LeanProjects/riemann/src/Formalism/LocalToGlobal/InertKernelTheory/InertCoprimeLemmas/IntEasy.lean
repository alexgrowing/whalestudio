import Formalism.LocalToGlobal.InertKernelTheory.DefsInt

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Comb

variable {D : D7} {N N' r : ℕ} {p : ℕ} [Fact p.Prime]

theorem ie_flog_const (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (flog W wq) = 0 := by
  simp [flog]

theorem ie_atLog_hasSubst (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) :
    MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin N' × Fin N => ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p])
      (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
      PowerSeries.subst (MvPowerSeries.X i) (flog (C • wModel lam Λ) wq)) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro k
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_mul, PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ (ie_flog_const _ _),
    mul_zero]

theorem ie_atLog_comb (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (m : ℕ) (c : Fin m → ℂ_[p])
    (F : Fin m → MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    atLog D lam Λ C wq b (∑ k, algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (c k) * F k) =
      ∑ k, c k • atLog D lam Λ C wq b (F k) := by
  have ha := ie_atLog_hasSubst (D := D) lam Λ C wq b
  have e : (∑ k, algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (c k) * F k) = ∑ k, c k • F k := by
    simp only [Algebra.smul_def]
  rw [e]
  unfold atLog
  dsimp only
  rw [← MvPowerSeries.substAlgHom_apply ha, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, MvPowerSeries.substAlgHom_apply]

end Comb

theorem combination_fact : CombFact := by
  intro D T p _ lam N N' L L' m r F hr hF C wq rr b hC hW hb ho n
  rw [ie_atLog_comb, Finset.sum_mul]
  simp only [smul_mul_assoc, map_sum, map_smul, smul_eq_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hr k) (norm_nonneg _) (hF k C wq rr b hC hW hb ho n)

section Lin

variable {D : D7} {N N' : ℕ}

theorem ie_smooth {G : VC D N N' → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ) (n : ℕ) : ContDiff ℂ n G :=
  contDiffOn_univ.1 (hG.contDiffOn uniqueDiffOn_univ)

theorem ie_taylor_lin {m : ℕ} (c : Fin m → ℂ) (G : Fin m → VC D N N' → ℂ)
    (hG : ∀ k (n : ℕ), ContDiff ℂ n (G k)) (α : Mono D N N') :
    taylor D (fun z => ∑ k, c k * G k z) α = ∑ k, c k * taylor D (G k) α := by
  unfold taylor
  have h1 : (fun z => ∑ k, c k * G k z) = fun z => ∑ k ∈ Finset.univ, c k • G k z := rfl
  rw [h1, iteratedFDeriv_sum (fun k _ => (hG k _).const_smul (c k)), Finset.sum_apply, _root_.sum_apply,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : (fun x => c k • G k x) = c k • G k := rfl
  rw [e, iteratedFDeriv_const_smul_apply ((hG k _).contDiffAt), _root_.smul_apply, smul_eq_mul, mul_div_assoc]

variable {p : ℕ} [Fact p.Prime]

theorem ie_lamC_of_mem (lam : Qbar →+* ℂ_[p]) {x : ℂ} (h : x ∈ Qbar) : lamC lam x = lam ⟨x, h⟩ := dif_pos h

theorem ie_lamC_mul (lam : Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar) :
    lamC lam (x * y) = lamC lam x * lamC lam y := by
  rw [ie_lamC_of_mem lam hx, ie_lamC_of_mem lam hy, ie_lamC_of_mem lam (mul_mem hx hy), ← map_mul]
  rfl

theorem ie_lamC_sum (lam : Qbar →+* ℂ_[p]) {m : ℕ} (f : Fin m → ℂ) (h : ∀ k, f k ∈ Qbar) :
    lamC lam (∑ k, f k) = ∑ k, lamC lam (f k) := by
  rw [ie_lamC_of_mem lam (sum_mem fun k _ => h k)]
  simp only [ie_lamC_of_mem lam (h _)]
  rw [← map_sum]
  congr 1
  ext
  simp

end Lin

theorem power_series_linearity : PSerLin := by
  intro D p _ lam N N' m c G hc hG
  have hsm : ∀ k (n : ℕ), ContDiff ℂ n (G k) := fun k n => ie_smooth (hG k).1 n
  ext α
  rw [map_sum]
  simp only [← Algebra.smul_def, map_smul, smul_eq_mul]
  show lamC lam (taylor D (fun z => ∑ k, c k * G k z) α) = ∑ k, lamC lam (c k) * lamC lam (taylor D (G k) α)
  rw [ie_taylor_lin c G hsm α, ie_lamC_sum lam _ fun k => mul_mem (hc k) ((hG k).2 α)]
  exact Finset.sum_congr rfl fun k _ => ie_lamC_mul lam (hc k) ((hG k).2 α)

section Pull

variable {D : D7}

theorem ie_emb_star (φ : D.host.E →+* ℂ) (x : D.host.E) :
    φ (@star D.host.E (@InvolutiveStar.toStar _ (@StarMul.toInvolutiveStar _ _
      (@StarRing.toStarMul _ _ D.host.cmStar))) x) = (starRingEnd ℂ) (φ x) := by
  haveI := D.host.isCMField_hostE
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E φ x

theorem ie_mem_smulLat {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (x : Fin n → D.host.E) : x ∈ SDLat.smulLat γ L ↔ ∃ w ∈ L, γ.mulVec w = x := by
  simp [SDLat.smulLat, Submodule.mem_map, Matrix.toLin'_apply]

variable {N N' : ℕ}

theorem ie_homL_pull (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1' : (letI := D.host.cmStar; star γ' * γ') = 1) {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ homL D (SDLat.smulLat γ M) (SDLat.smulLat γ' M')) :
    (letI := D.host.cmStar; star γ' * A * γ) ∈ homL D M M' := by
  letI := D.host.cmStar
  induction hA using Submodule.span_induction with
  | mem A hA =>
    refine Submodule.subset_span fun x hx => ?_
    obtain ⟨y, hy, hxy⟩ := (ie_mem_smulLat γ' M' _).1 (hA _ ((ie_mem_smulLat γ M _).2 ⟨x, hx, rfl⟩))
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hxy, Matrix.mulVec_mulVec, h1', Matrix.one_mulVec]
    exact hy
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [Matrix.mul_smul, Matrix.smul_mul]; exact Submodule.smul_mem _ c hx

theorem ie_yy_pull (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1' : (letI := D.host.cmStar; star γ' * γ') = 1) {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ YYl D (SDLat.smulLat γ M) (SDLat.smulLat γ' M')) :
    (letI := D.host.cmStar; star γ' * A * γ) ∈ YYl D M M' := by
  letI := D.host.cmStar
  induction hA using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A₀, hA₀, rfl⟩ := hB
    refine Submodule.subset_span ⟨a, ha, _, ie_homL_pull γ γ' h1' hA₀, ?_⟩
    rw [Matrix.mul_smul, Matrix.smul_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [Matrix.mul_smul, Matrix.smul_mul]; exact Submodule.smul_mem _ c hx

variable (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)

theorem ie_tPull_add (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (x y : VC D N N') :
    tPull D (tor0 D cc δ) γ γ' (x + y) = tPull D (tor0 D cc δ) γ γ' x + tPull D (tor0 D cc δ) γ γ' y := by
  funext τ
  show _ * (Matrix.of (x τ) + Matrix.of (y τ)) * _ = _
  rw [Matrix.mul_add, Matrix.add_mul]
  rfl

theorem ie_tPull_smul (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (c : ℂ)
    (x : VC D N N') : tPull D (tor0 D cc δ) γ γ' (c • x) = c • tPull D (tor0 D cc δ) γ γ' x := by
  funext τ
  simp only [tPull, Pi.smul_apply]
  rw [show (Matrix.of (c • x τ) : Matrix (Fin N') (Fin N) ℂ) = c • Matrix.of (x τ) from rfl, Matrix.mul_smul,
    Matrix.smul_mul]
  rfl

def ieTPullHom (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) :
    VC D N N' →+ VC D N N' :=
  AddMonoidHom.mk' (tPull D (tor0 D cc δ) γ γ') (ie_tPull_add cc δ γ γ')

theorem ie_tPull_embV (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (A : Matrix (Fin N') (Fin N) D.host.E) :
    tPull D (tor0 D cc δ) γ γ' (embV D (tor0 D cc δ) A) =
      embV D (tor0 D cc δ) (letI := D.host.cmStar; star γ' * A * γ) := by
  letI := D.host.cmStar
  funext τ
  have e1 : (star γ').map (embT D τ) = Matrix.conjTranspose (γ'.map (embT D τ)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.star_apply, Matrix.conjTranspose_apply]
    exact ie_emb_star (embT D τ) (γ' j i)
  have e2 : (star γ' * A * γ).map (embT D τ) =
      Matrix.conjTranspose (γ'.map (embT D τ)) * A.map (embT D τ) * γ.map (embT D τ) := by
    rw [Matrix.map_mul, Matrix.map_mul, e1]
  exact e2.symm

theorem ie_La_pull (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1' : (letI := D.host.cmStar; star γ' * γ') = 1) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    La D (tor0 D cc δ) (SDLat.smulLat γ M) (SDLat.smulLat γ' M') ≤
      (La D (tor0 D cc δ) M M').comap (ieTPullHom cc δ γ γ') := by
  unfold La
  rw [AddSubgroup.closure_le]
  rintro z ⟨w, hw, A, hA, rfl⟩
  simp only [SetLike.mem_coe, AddSubgroup.mem_comap, ieTPullHom, AddMonoidHom.mk'_apply]
  rw [ie_tPull_smul, ie_tPull_embV]
  exact AddSubgroup.subset_closure ⟨w, hw, _, ie_yy_pull γ γ' h1' hA, rfl⟩

end Pull

theorem pullback_torsion : PullTors := by
  intro D cc δ p _ N N' γ γ' M M' t ⟨n, hn, hcop, hmem⟩
  refine ⟨n, hn, hcop, ?_⟩
  have h1' : (letI := D.host.cmStar; star (γ' : Matrix (Fin N') (Fin N') D.host.E) * γ') = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp γ'.2
  have h := ie_La_pull cc δ (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) h1' M M' hmem
  rw [AddSubgroup.mem_comap] at h
  have e : ieTPullHom cc δ (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (n • t) =
      n • tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) t :=
    map_nsmul _ n t
  rw [e] at h
  exact h

section Pair

variable {D : D7} {N N' : ℕ}

theorem ie_homL_scale {M₁ M₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {M₁' M₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (s s' : ℕ)
    (h1 : ∀ x ∈ M₂, (s : D.host.E) • x ∈ M₁) (h2 : ∀ y ∈ M₁', (s' : D.host.E) • y ∈ M₂')
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ homL D M₁ M₁') :
    (((s * s' : ℕ) : D.host.E)) • A ∈ homL D M₂ M₂' := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    refine Submodule.subset_span fun x hx => ?_
    have e : ((((s * s' : ℕ) : D.host.E)) • A).mulVec x = (s' : D.host.E) • A.mulVec ((s : D.host.E) • x) := by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, Nat.cast_mul, mul_comm]
    rw [e]
    exact h2 _ (hA _ (h1 x hx))
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem ie_yy_scale {M₁ M₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {M₁' M₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (s s' : ℕ)
    (h1 : ∀ x ∈ M₂, (s : D.host.E) • x ∈ M₁) (h2 : ∀ y ∈ M₁', (s' : D.host.E) • y ∈ M₂')
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ YYl D M₁ M₁') :
    (((s * s' : ℕ) : D.host.E)) • A ∈ YYl D M₂ M₂' := by
  induction hA using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A₀, hA₀, rfl⟩ := hB
    refine Submodule.subset_span ⟨a, ha, _, ie_homL_scale s s' h1 h2 hA₀, ?_⟩
    rw [smul_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem ie_embV_nsmul (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (k : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E) :
    k • embV D (tor0 D cc δ) A = embV D (tor0 D cc δ) (((k : ℕ) : D.host.E) • A) := by
  funext τ i j
  show k • embT D τ (A i j) = embT D τ ((k : D.host.E) * A i j)
  rw [map_mul, map_natCast, nsmul_eq_mul]

theorem ie_La_scale (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {M₁ M₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {M₁' M₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (s s' : ℕ)
    (h1 : ∀ x ∈ M₂, (s : D.host.E) • x ∈ M₁) (h2 : ∀ y ∈ M₁', (s' : D.host.E) • y ∈ M₂') :
    La D (tor0 D cc δ) M₁ M₁' ≤
      (La D (tor0 D cc δ) M₂ M₂').comap (DistribMulAction.toAddMonoidHom (VC D N N') (s * s')) := by
  unfold La
  rw [AddSubgroup.closure_le]
  rintro z ⟨w, hw, A, hA, rfl⟩
  simp only [SetLike.mem_coe, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply]
  rw [smul_comm, ie_embV_nsmul]
  exact AddSubgroup.subset_closure ⟨w, hw, _, ie_yy_scale s s' h1 h2 hA, rfl⟩

end Pair

theorem pairing_fact : PairFact := by
  intro D cc δ p _ N N' L L₁ L' L₁' ⟨s, hs, hs1, hs2⟩ ⟨s', hs', hs1', hs2'⟩
  have hss : Nat.Coprime (s * s') p := Nat.Coprime.mul hs hs'
  refine ⟨fun r b ⟨hli, hb1, hb2⟩ => ⟨hli, fun i => ?_, fun y hy => ?_⟩, fun t ⟨n, hn, hc, hm⟩ => ?_⟩
  · obtain ⟨s0, hc0, hm0⟩ := hb1 i
    refine ⟨(s * s') * s0, Nat.Coprime.mul hss hc0, ?_⟩
    rw [Nat.cast_mul, mul_smul]
    exact ie_yy_scale s s' hs2 hs1' hm0
  · obtain ⟨s1, hc1, c, hcs⟩ := hb2 _ (ie_yy_scale s s' hs1 hs2' hy)
    refine ⟨s1 * (s * s'), Nat.Coprime.mul hc1 hss, c, ?_⟩
    rw [Nat.cast_mul, mul_smul]
    exact hcs
  · have hp : p ≠ 1 := (Fact.out : p.Prime).one_lt.ne'
    have hs0 : 0 < s := Nat.pos_of_ne_zero fun h => hp (Nat.coprime_zero_left p |>.1 (h ▸ hs))
    have hs0' : 0 < s' := Nat.pos_of_ne_zero fun h => hp (Nat.coprime_zero_left p |>.1 (h ▸ hs'))
    refine ⟨(s * s') * n, Nat.mul_pos (Nat.mul_pos hs0 hs0') hn, Nat.Coprime.mul hss hc, ?_⟩
    have h := ie_La_scale cc δ s s' hs2 hs1' hm
    rw [AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply, ← mul_smul] at h
    exact h

end Formalism.L2.KerInert

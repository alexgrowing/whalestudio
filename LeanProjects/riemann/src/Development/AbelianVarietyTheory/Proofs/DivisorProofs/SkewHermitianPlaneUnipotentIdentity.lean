import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

noncomputable section

namespace GlobalTheory.UnipCocptHerm
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.UnipCocptForm
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_swap_h (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hherm : ∀ i j, σ (J j i) = J i j)
    (hσ : ∀ x, σ (σ x) = x) (a b : Fin n → E) : form σ J a b = σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hherm, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem decomp_h (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E)
    (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E) (hherm : ∀ i j, σ (J j i) = J i j) (hσ : ∀ x, σ (σ x) = x)
    (hn : n = n₁ + 2) (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (hg : ιᵀ * J * ι.map σ = J₁) (hJ₁ : J₁.det ≠ 0)
    (v : Fin n → E) : ∃ (α β : E) (z : Fin n₁ → E), v = α • x + β • y + ι *ᵥ z := by
  let b : Fin 2 ⊕ Fin n₁ → Fin n → E := Sum.elim ![x, y] fun j => ι *ᵥ Pi.single j 1
  have hyx : form σ J y x = 1 := by rw [form_swap_h σ J hherm hσ, hxy, map_one]
  have hxι : ∀ l, form σ J x (ι *ᵥ Pi.single l 1) = 0 := fun l => by
    rw [form_swap_h σ J hherm hσ, (horth _).1, map_zero]
  have hyι : ∀ l, form σ J y (ι *ᵥ Pi.single l 1) = 0 := fun l => by
    rw [form_swap_h σ J hherm hσ, (horth _).2, map_zero]
  have hli : LinearIndependent E b := by
    rw [Fintype.linearIndependent_iff]
    intro g hs
    have pair : ∀ u, ∑ k, g k * form σ J (b k) u = 0 := fun u => by
      rw [← form_sum, hs]; simp [form]
    have h1 := pair y
    have h2 := pair x
    simp only [Fintype.sum_sum_type, Fin.sum_univ_two, b, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
      Matrix.cons_val_one, hxy, hyy, hxx, hyx, (horth _).1, (horth _).2, mul_zero, mul_one, Finset.sum_const_zero,
      add_zero, zero_add] at h1 h2
    have h0 : g (Sum.inl 0) = 0 := h1
    have h1' : g (Sum.inl 1) = 0 := by simpa using h2
    have h3 : (fun j => g (Sum.inr j)) ᵥ* J₁ = 0 := by
      funext l
      have := pair (ι *ᵥ Pi.single l 1)
      simp only [Fintype.sum_sum_type, Fin.sum_univ_two, b, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, hxι, hyι, h0, h1', zero_mul, zero_add, form_col, hg] at this
      simpa [Matrix.vecMul, dotProduct] using this
    have h4 : (fun j => g (Sum.inr j)) = 0 := by
      by_contra hne
      exact hJ₁ (Matrix.exists_vecMul_eq_zero_iff.1 ⟨_, hne, h3⟩)
    rintro (k | k)
    · fin_cases k
      · exact h0
      · exact h1'
    · exact congrFun h4 k
  have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [hn]; omega)
  have hv : v ∈ Submodule.span E (Set.range b) := hsp ▸ Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
  refine ⟨g (Sum.inl 0), g (Sum.inl 1), fun j => g (Sum.inr j), ?_⟩
  rw [← hg, Fintype.sum_sum_type, Fin.sum_univ_two]
  simp only [b, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Matrix.mulVec_single_one, mul_comm]

theorem key_h (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (J₁ : Matrix (Fin n₁) (Fin n₁) E) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E)
    (hherm : ∀ i j, σ (J j i) = J i j) (hn : n = n₁ + 2) (hxx : form σ J x x = 0) (hyy : form σ J y y = 0)
    (hxy : form σ J x y = 1) (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0)
    (hg : ιᵀ * J * ι.map σ = J₁) (hJ₁ : J₁.det ≠ 0) (c : E) (hc : c ≠ 0)
    (M : Matrix (Fin n) (Fin n) (AE F E)) (hU : Mᵀ * incM F J * M.map (cA σ) = incM F J) :
    ((M - 1) * adMat F (Matrix.of fun i (_ : Fin 1) => x i) = 0 ∧
      adMat F (Formalism.UG.cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => x i) * (c • J.map σ)) * (M - 1) = 0 ∧
      ∀ v : Fin n → E, (Formalism.UG.cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => x i) * (c • J.map σ)) *ᵥ v = 0 →
        ∃ a : Fin 1 → AF F ⊗[F] E, (M - 1) *ᵥ (fun i => inclR (F := F) (AF F) (v i)) =
          adMat F (Matrix.of fun i (_ : Fin 1) => x i) *ᵥ a) ↔
    (M *ᵥ incV F x = incV F x ∧ ∀ z, ∃ a : AE F E, M *ᵥ (incM F ι *ᵥ z) = incM F ι *ᵥ z + a • incV F x) := by
  set C : Matrix (Fin n) (Fin 1) E := Matrix.of fun i (_ : Fin 1) => x i with hCdef
  set X : Fin n → AE F E := incV F x with hXdef
  set w : Fin n → E := J *ᵥ fun i => σ (x i) with hwdef
  have hC : ∀ a : Fin 1 → AE F E, adMat F C *ᵥ a = a 0 • X := by
    intro a; ext i
    simp [hCdef, hXdef, adMat, Matrix.mulVec, dotProduct, incV, mul_comm]
  have hMC : (M - 1) * adMat F C = 0 ↔ M *ᵥ X = X := by
    constructor
    · intro h
      have h2 := congrArg (· *ᵥ (fun _ : Fin 1 => (1 : AE F E))) h
      simp only [← Matrix.mulVec_mulVec, hC, one_smul, Matrix.zero_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] at h2
      exact sub_eq_zero.1 h2
    · intro h
      have hX0 : (M - 1) *ᵥ X = 0 := by rw [Matrix.sub_mulVec, Matrix.one_mulVec, h, sub_self]
      ext i j
      have := congrFun hX0 i
      simpa [Matrix.mul_apply, hCdef, hXdef, adMat, Matrix.mulVec, dotProduct, incV] using this
  have hrow : Formalism.UG.cT (σ : E →+* E) C * (c • J.map σ) = Matrix.of fun (_ : Fin 1) j => c * w j := by
    ext o j
    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      hCdef, Matrix.of_apply, hwdef, Matrix.mulVec, dotProduct, AlgHom.coe_toRingHom, hherm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hrowv : ∀ v : Fin n → E, (Matrix.of fun (_ : Fin 1) j => c * w j) *ᵥ v = fun _ => c * form σ J v x := by
    intro v; ext o
    change (fun j => c * w j) ⬝ᵥ v = c * (v ⬝ᵥ w)
    simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hrow, hMC]
  have hX0 : ∀ h : M *ᵥ X = X, (M - 1) *ᵥ X = 0 := fun h => by rw [Matrix.sub_mulVec, Matrix.one_mulVec, h, sub_self]
  constructor
  · rintro ⟨hx, -, h3⟩
    refine ⟨hx, ?_⟩
    have hj : ∀ j : Fin n₁, ∃ a : Fin 1 → AE F E,
        (M - 1) *ᵥ (fun i => inclR (F := F) (AF F) ((ι *ᵥ Pi.single j 1) i)) = adMat F C *ᵥ a :=
      fun j => h3 _ (by rw [hrowv, (horth _).1]; ext; simp)
    choose a ha using hj
    have hcol : (M - 1) * incM F ι = Matrix.of fun i j => a j 0 * X i := by
      ext i j
      have := congrFun (ha j) i
      rw [hC] at this
      simp only [Matrix.mulVec_single_one] at this
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, incM, Matrix.transpose_apply, mul_comm] using this
    intro z
    refine ⟨∑ j, a j 0 * z j, ?_⟩
    have h4 : (M - 1) *ᵥ (incM F ι *ᵥ z) = (∑ j, a j 0 * z j) • X := by
      rw [Matrix.mulVec_mulVec, hcol]
      ext i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    calc M *ᵥ (incM F ι *ᵥ z) = incM F ι *ᵥ z + (M - 1) *ᵥ (incM F ι *ᵥ z) := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
      _ = _ := by rw [h4]
  · rintro ⟨hx, hz⟩
    refine ⟨hx, ?_, ?_⟩
    · have hMσ : M.map (cA σ) *ᵥ incV F (fun i => σ (x i)) = incV F (fun i => σ (x i)) := by
        ext i
        have := RingHom.map_mulVec (cA σ).toRingHom M X i
        rw [hx] at this
        simp only [Function.comp_def, hXdef, incV, cA_inclR, AlgHom.coe_toRingHom] at this ⊢
        exact this.symm
      have hW : incM F J *ᵥ incV F (fun i => σ (x i)) = incV F w := by rw [hwdef, incV_mulVec]
      have hMW : Mᵀ *ᵥ incV F w = incV F w := by
        rw [← hW]
        conv_lhs => rw [← hMσ]
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        first | rw [hU] | rw [← Matrix.mul_assoc, hU]
      have hW0 : (M - 1)ᵀ *ᵥ incV F w = 0 := by
        rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mulVec, Matrix.one_mulVec, hMW, sub_self]
      ext o k
      have := congrFun hW0 k
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, incV, Pi.zero_apply] at this
      simp only [Matrix.mul_apply, adMat, Matrix.map_apply, Matrix.of_apply, map_mul, Matrix.zero_apply]
      calc ∑ j, inclR (F := F) (AF F) c * inclR (F := F) (AF F) (w j) * (M - 1) j k
          = inclR (F := F) (AF F) c * ∑ j, (M - 1) j k * inclR (F := F) (AF F) (w j) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [this, mul_zero]
    · intro v hv
      rw [hrowv] at hv
      have hvx : form σ J v x = 0 := by
        have := congrFun hv 0
        simpa [hc] using this
      obtain ⟨α, β, z, rfl⟩ := decomp_h σ J J₁ x y ι hherm hσ hn hxx hyy hxy horth hg hJ₁ v
      have hyx : form σ J y x = 1 := by rw [form_swap_h σ J hherm hσ, hxy, map_one]
      have hβ : β = 0 := by
        rw [form_add, form_add, form_smul, form_smul, hxx, hyx, (horth z).1] at hvx
        simpa using hvx
      subst hβ
      obtain ⟨a, ha⟩ := hz (incV F z)
      refine ⟨fun _ => a, ?_⟩
      rw [hC]
      have e1 : (fun i => inclR (F := F) (AF F) ((α • x + (0 : E) • y + ι *ᵥ z) i)) =
          inclR (F := F) (AF F) α • X + incM F ι *ᵥ incV F z := by
        rw [← incV_mulVec]; ext i; simp [hXdef, incV]
      rw [e1, Matrix.mulVec_add, Matrix.mulVec_smul, hX0 hx, smul_zero, zero_add, Matrix.sub_mulVec, Matrix.one_mulVec, ha]
      simp

theorem mem_unip_iff_h (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} (Y : Spc F E n)
    (J₁ : Matrix (Fin n₁) (Fin n₁) E) (H : Plane E n n₁)
    (hherm : ∀ i j, σ (Y.J j i) = Y.J i j) (hn : n = n₁ + 2) (hxx : form σ Y.J H.x H.x = 0)
    (hyy : form σ Y.J H.y H.y = 0) (hxy : form σ Y.J H.x H.y = 1)
    (horth : ∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0)
    (hg : H.ιᵀ * Y.J * H.ι.map σ = J₁) (hJ₁ : J₁.det ≠ 0) (c : E) (hc : c ≠ 0) (g : UA σ Y.J) :
    g ∈ unip σ Y H ↔ toGAd hσ Y.J hc g ∈ unipRad σ (c • Y.J.map σ) (Matrix.of fun i (_ : Fin 1) => H.x i) := by
  have hU : ∀ g : UA σ Y.J, (mat g)ᵀ * incM F Y.J * (mat g).map (cA σ) = incM F Y.J := fun g => g.2
  rw [GlobalTheory.UnipCT.unip_eq]
  constructor
  · intro hm
    apply Subgroup.subset_closure
    exact (key_h σ hσ Y.J J₁ H.x H.y H.ι hherm hn hxx hyy hxy horth hg hJ₁ c hc (mat g) (hU g)).2 hm
  · intro hm
    have hle : unipRad σ (c • Y.J.map σ) (Matrix.of fun i (_ : Fin 1) => H.x i) ≤
        (GlobalTheory.UnipCT.unipSet σ Y H).map (toGAd hσ Y.J hc).toMonoidHom := by
      refine (Subgroup.closure_le _).2 fun h hh => ?_
      rw [SetLike.mem_coe, Subgroup.mem_map_equiv]
      exact (key_h σ hσ Y.J J₁ H.x H.y H.ι hherm hn hxx hyy hxy horth hg hJ₁ c hc
        (mat ((toGAd hσ Y.J hc).symm h)) (hU _)).1 hh
    have := hle hm
    rwa [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at this

theorem isHermND_one (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hherm : ∀ i j, σ (J j i) = J i j)
    (hJ : J.det ≠ 0) (hσ : ∀ x, σ (σ x) = x) : IsHermND σ ((1 : E) • J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, one_mul, hσ]
    exact (hherm j i).symm
  · have e : (J.map σ).det = (σ : E →+* E) J.det := by rw [RingHom.map_det]; rfl
    rw [one_smul, e]
    exact (map_ne_zero _).2 hJ

theorem eps_sq (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E)
    (hxy : form σ J x y = 1) (ε : F) (hε : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) : ε * ε = 1 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, J i j ≠ 0 := by
    by_contra h
    push_neg at h
    have : J = 0 := Matrix.ext h
    rw [this] at hxy
    simp [form] at hxy
  have h1 : J i j = algebraMap F E ε * (algebraMap F E ε * J i j) := by
    conv_lhs => rw [← hσ (J i j), hε j i, map_mul, AlgHom.commutes, hε i j]
  have h2 : algebraMap F E (ε * ε) = algebraMap F E 1 := by
    rw [map_mul, map_one]
    have : (algebraMap F E ε * algebraMap F E ε - 1) * J i j = 0 := by linear_combination -h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hij)
  exact (algebraMap F E).injective h2

end GlobalTheory.UnipCocptHerm

theorem GlobalTheory.UnipCocptHerm.cocompact_unip_eps : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), n = n₁ + 2 → form σ W.J H.x H.x = 0 →
    form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
    (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
    ∀ ε : F, (∀ i j, σ (W.J j i) = algebraMap F E ε * W.J i j) → W.J.det ≠ 0 → W₁.J.det ≠ 0 →
    ∃ K : Set (unip σ W H), IsCompact K ∧ ∀ u : unip σ W H, ∃ γ ∈ (ratU σ W.J).subgroupOf (unip σ W H), γ * u ∈ K := by
  intro F E _ _ _ _ _ σ hcm n n₁ W W₁ H hn hxx hyy hxy horth hg ε hε hJ hJ₁
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  rcases mul_self_eq_one_iff.1 (GlobalTheory.UnipCocptHerm.eps_sq σ hσ W.J H.x H.y hxy ε hε) with h | h
  · subst h
    have hherm : ∀ i j, σ (W.J j i) = W.J i j := fun i j => by rw [hε, map_one, one_mul]
    exact GlobalTheory.UnipCocptForm.cocompact_of_mem σ hcm W H 1 one_ne_zero
      (GlobalTheory.UnipCocptHerm.isHermND_one σ W.J hherm hJ hσ)
      (GlobalTheory.UnipCocptForm.isIsoCols_smul_map_of_isotropic_pair σ W.J H.x H.y hxx hxy hσ 1)
      (GlobalTheory.UnipCocptHerm.mem_unip_iff_h σ hσ W W₁.J H hherm hn hxx hyy hxy horth hg hJ₁ 1 one_ne_zero)
  · subst h
    have hskew : ∀ i j, σ (W.J j i) = -W.J i j := fun i j => by rw [hε, map_neg, map_one, neg_one_mul]
    exact GlobalTheory.UnipCocptForm.cocompact_unip_form W W₁ H hcm hskew hn hxx hyy hxy horth hg hJ hJ₁

end

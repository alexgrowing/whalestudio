import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitScalar

open scoped ComplexOrder

theorem notMem_span_of_commute {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (hc : ∀ a ∈ G, ∀ b ∈ G, Commute a b) (s : Set V) (hs : ∀ x ∈ s, ∃ g ∈ G, g x = 0) (f : V)
    (hf : ∀ B ∈ Submonoid.closure G, B f ≠ 0) : f ∉ Submodule.span ℂ s := by
  have h1 : ∀ a ∈ G, ∀ B ∈ Submonoid.closure G, Commute a B := by
    intro a ha B hB
    induction hB using Submonoid.closure_induction with
    | mem b hb => exact hc a ha b hb
    | one => exact Commute.one_right _
    | mul x y _ _ hx hy => exact hx.mul_right hy
  have h2 : ∀ A ∈ Submonoid.closure G, ∀ B ∈ Submonoid.closure G, Commute A B := by
    intro A hA B hB
    induction hA using Submonoid.closure_induction with
    | mem a ha => exact h1 a ha B hB
    | one => exact Commute.one_left _
    | mul x y _ _ hx hy => exact hx.mul_left hy
  have key : ∀ x ∈ Submodule.span ℂ s, ∃ B ∈ Submonoid.closure G, B x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, h⟩ := hs x hx
      exact ⟨g, Submonoid.subset_closure hg, h⟩
    | zero => exact ⟨1, one_mem _, rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨A, hA, ha⟩ := hx
      obtain ⟨B, hB, hb⟩ := hy
      refine ⟨A * B, mul_mem hA hB, ?_⟩
      rw [map_add]
      nth_rewrite 1 [(h2 A hA B hB).eq]
      rw [Module.End.mul_apply, Module.End.mul_apply, ha, hb, map_zero, map_zero, add_zero]
    | smul c x _ hx =>
      obtain ⟨A, hA, ha⟩ := hx
      exact ⟨A, hA, by rw [map_smul, ha, smul_zero]⟩
  intro h
  obtain ⟨B, hB, hb⟩ := key f h
  exact hf B hB hb

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem isHalf_smul {m n : ℕ} {e : AE D} (he : e * e = e) (u : Mx D m n) : IsHalf e (e • u) := by
  rw [isHalf_iff, smul_smul, he]

theorem isHalf_add {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u + v) := by
  rw [isHalf_iff] at *
  rw [smul_add, hu, hv]

theorem isHalf_sub {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u - v) := by
  rw [isHalf_iff] at *
  rw [smul_sub, hu, hv]

theorem isHalf_nsmul {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (k : ℕ) : IsHalf e (k • u) := by
  rw [isHalf_iff] at *
  rw [smul_comm, hu]

theorem isHalf_zero {m n : ℕ} (e : AE D) : IsHalf e (0 : Mx D m n) := by
  rw [isHalf_iff, smul_zero]

theorem half_orth {e : AE D} (he : IsSplitIdem D e) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    symplO S T x y = 0 :=
  symplO_eq_zero S T (by rw [mul_comm, he.2.1]) hx hy

theorem heisL_add_half {e : AE D} (he : IsSplitIdem D e) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    heisL ψ S T (x + y) = heisL ψ S T x * heisL ψ S T y :=
  LinearMap.ext fun f => heisO_add_of_orth ψ S T (half_orth he hx hy) f

theorem heisL_commute_half {e : AE D} (he : IsSplitIdem D e) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    Commute (heisL ψ S T x) (heisL ψ S T y) := by
  rw [Commute, SemiconjBy, ← heisL_add_half he hx hy, ← heisL_add_half he hy hx, add_comm]

theorem psi_skew_ne {x y : WO S T} (h : ψ (symplO S T x y) ≠ 1) : ψ (symplO S T y x) ≠ 1 := by
  intro h'
  apply h
  have : ψ (symplO S T x y + symplO S T y x) = 1 := by
    rw [symplO_skew S T x y, add_neg_cancel, AddChar.map_zero_eq_one]
  rwa [AddChar.map_add_eq_mul, h', mul_one] at this

theorem exists_dual_half {Λ : AddSubgroup (WO S T)} {e : AE D} (he : IsSplitIdem D e)
    (hd : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hst : ∀ u ∈ Λ, cA D e • u ∈ Λ) {y : WO S T} (hy : IsHalf e y) (hyΛ : y ∉ Λ) :
    ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1 := by
  rw [hd y (half_fin he hy)] at hyΛ
  push Not at hyΛ
  obtain ⟨u, hu, h⟩ := hyΛ
  refine ⟨cA D e • u, hst u hu, isHalf_smul (isSplitIdem_conj he).1 u, psi_skew_ne ?_⟩
  rwa [← symplO_smul, (isHalf_iff _ _).1 hy]

theorem exists_count_form {Λ : AddSubgroup (WO S T)} {e : AE D} (he : IsSplitIdem D e)
    (hd : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hst : ∀ u ∈ Λ, cA D e • u ∈ Λ) {f : WO S T → ℂ} (hf0 : f ≠ 0) (hf : IsLatVac (heisO ψ S T) Λ f) :
    ∃ κ : (WO S T → ℂ) →ₗ[ℂ] ℂ, κ f = 1 ∧ ∀ y, IsHalf e y → 0 ≤ κ (heisO ψ S T y f) := by
  have he' := isSplitIdem_conj he
  have h : f ∉ Submodule.span ℂ {x | ∃ y, IsHalf e y ∧ y ∉ Λ ∧ x = heisO ψ S T y f} := by
    refine notMem_span_of_commute
      {g | ∃ l ∈ Λ, ∃ z : ℂ, IsHalf (cA D e) l ∧ z ≠ 1 ∧ g = heisL ψ S T l - z • 1} ?_ _ ?_ f ?_
    · rintro _ ⟨l, -, z, hl, -, rfl⟩ _ ⟨l', -, z', hl', -, rfl⟩
      exact ((heisL_commute_half he' hl hl').sub_right ((Commute.one_right _).smul_right _)).sub_left
        ((Commute.one_left _).smul_left _)
    · rintro _ ⟨y, hy, hyΛ, rfl⟩
      obtain ⟨l, hl, hl', hne⟩ := exists_dual_half he hd hst hy hyΛ
      refine ⟨_, ⟨l, hl, _, hl', hne, rfl⟩, ?_⟩
      rw [LinearMap.sub_apply, heisL_apply, heisO_comm, hf.2 _ he' l hl hl']
      exact sub_self _
    · have : ∀ B ∈ Submonoid.closure
          {g | ∃ l ∈ Λ, ∃ z : ℂ, IsHalf (cA D e) l ∧ z ≠ 1 ∧ g = heisL ψ S T l - z • 1},
          ∃ c : ℂ, c ≠ 0 ∧ B f = c • f := by
        intro B hB
        induction hB using Submonoid.closure_induction with
        | mem b hb =>
          obtain ⟨l, hl, z, hl', hz, rfl⟩ := hb
          refine ⟨1 - z, sub_ne_zero.2 hz.symm, ?_⟩
          rw [LinearMap.sub_apply, heisL_apply, hf.2 _ he' l hl hl', sub_smul, one_smul]
          rfl
        | one => exact ⟨1, one_ne_zero, (one_smul _ _).symm⟩
        | mul x y _ _ hx hy =>
          obtain ⟨c, hc, hx⟩ := hx
          obtain ⟨d, hd, hy⟩ := hy
          exact ⟨d * c, mul_ne_zero hd hc, by rw [Module.End.mul_apply, hy, map_smul, hx, smul_smul]⟩
      intro B hB
      obtain ⟨c, hc, h⟩ := this B hB
      rw [h]
      exact smul_ne_zero hc hf0
  obtain ⟨κ, hκ, hκ'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  refine ⟨(κ f)⁻¹ • κ, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hκ], fun y hy => ?_⟩
  by_cases hyΛ : y ∈ Λ
  · rw [hf.2 e he y hyΛ hy, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hκ]
    exact zero_le_one
  · have : κ (heisO ψ S T y f) = 0 := by
      rw [← Submodule.mem_bot ℂ, ← hκ']
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨y, hy, hyΛ, rfl⟩)
    rw [LinearMap.smul_apply, this, smul_zero]

theorem exists_invariant_form {Λ : AddSubgroup (WO S T)} {e : AE D} (he : IsSplitIdem D e)
    (hd : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hst : ∀ u ∈ Λ, cA D e • u ∈ Λ) {f : WO S T → ℂ} (hf0 : f ≠ 0) (hf : IsLatVac (heisO ψ S T) Λ f) :
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, ℓ f ≠ 0 ∧
      ∀ y, IsHalf e y → ∀ φ, IsThetaFunO ψ S T φ → ℓ (heisO ψ S T y φ) = ℓ φ := by
  obtain ⟨κ, hκ1, hκ⟩ := exists_count_form he hd hst hf0 hf
  have h : f ∉ Submodule.span ℂ
      {x | ∃ y φ, IsHalf e y ∧ IsThetaFunO ψ S T φ ∧ x = heisO ψ S T y φ - φ} := by
    refine notMem_span_of_commute
      {g | ∃ (y : WO S T) (N : ℕ), IsHalf e y ∧ g = ∑ k ∈ Finset.range (N + 1), heisL ψ S T (k • y)} ?_ _ ?_ f ?_
    · rintro _ ⟨y, N, hy, rfl⟩ _ ⟨y', N', hy', rfl⟩
      exact Commute.sum_left _ _ _ fun k _ => Commute.sum_right _ _ _ fun k' _ =>
        heisL_commute_half he (isHalf_nsmul hy k) (isHalf_nsmul hy' k')
    · rintro _ ⟨y, φ, hy, hφ, rfl⟩
      obtain ⟨U, hU, hUφ⟩ := hφ.level
      obtain ⟨N, hN, hNU⟩ := exists_nsmul_mem U hU (half_fin he hy)
      obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
      refine ⟨_, ⟨y, N, hy, rfl⟩, ?_⟩
      have e1 : ∀ k : ℕ, heisL ψ S T (k • y) (heisO ψ S T y φ - φ) =
          heisO ψ S T ((k + 1) • y) φ - heisO ψ S T (k • y) φ := by
        intro k
        rw [map_sub, succ_nsmul, heisO_add_of_orth ψ S T (half_orth he (isHalf_nsmul hy k) hy)]
        rfl
      rw [LinearMap.sum_apply, Finset.sum_congr rfl fun k _ => e1 k,
        Finset.sum_range_sub (fun k => heisO ψ S T (k • y) φ), zero_smul, heisO_zero,
        hUφ _ hNU (half_fin he (isHalf_nsmul hy _)), sub_self]
    · have : ∀ B ∈ Submonoid.closure
          {g | ∃ (y : WO S T) (N : ℕ), IsHalf e y ∧ g = ∑ k ∈ Finset.range (N + 1), heisL ψ S T (k • y)},
          (∀ y, IsHalf e y → 0 ≤ κ (B (heisO ψ S T y f))) ∧ 0 < κ (B f) := by
        intro B hB
        induction hB using Submonoid.closure_induction_right with
        | one => exact ⟨hκ, by rw [Module.End.one_apply, hκ1]; exact zero_lt_one⟩
        | mul_right B _ g hg ih =>
          obtain ⟨y', N, hy', rfl⟩ := hg
          refine ⟨fun y hy => ?_, ?_⟩
          · rw [Module.End.mul_apply, LinearMap.sum_apply, map_sum, map_sum]
            refine Finset.sum_nonneg fun k _ => ?_
            rw [heisL_apply, ← heisO_add_of_orth ψ S T (half_orth he (isHalf_nsmul hy' k) hy)]
            exact ih.1 _ (isHalf_add (isHalf_nsmul hy' k) hy)
          · rw [Module.End.mul_apply, LinearMap.sum_apply, map_sum, map_sum]
            refine Finset.sum_pos' (fun k _ => ih.1 _ (isHalf_nsmul hy' k)) ⟨0, Finset.mem_range.2 N.succ_pos, ?_⟩
            rw [heisL_apply, zero_smul, heisO_zero]
            exact ih.2
      intro B hB h0
      have := (this B hB).2
      rw [h0, map_zero] at this
      exact lt_irrefl _ this
  obtain ⟨ℓ, hℓ, hℓ'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  refine ⟨ℓ, hℓ, fun y hy φ hφ => ?_⟩
  rw [← sub_eq_zero, ← map_sub, ← Submodule.mem_bot ℂ, ← hℓ']
  exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨y, φ, hy, hφ, rfl⟩)

theorem sum_reps_invariant {Λ Λ' : AddSubgroup (WO S T)} {e : AE D} (he : IsSplitIdem D e) {R : Finset (WO S T)}
    (hR : ∀ u ∈ R, u ∈ Λ' ∧ IsHalf e u) (hR' : ∀ u ∈ Λ', IsHalf e u → ∃! v, v ∈ R ∧ u - v ∈ Λ)
    {G : WO S T → ℂ} (hG : ∀ d ∈ Λ, d ∈ Λ' → IsHalf e d → heisO ψ S T d G = G) {a : WO S T} (ha : a ∈ Λ')
    (hae : IsHalf e a) :
    heisO ψ S T a (∑ u ∈ R, heisO ψ S T u G) = ∑ u ∈ R, heisO ψ S T u G := by
  have ex : ∀ u ∈ R, ∃! v, v ∈ R ∧ a + u - v ∈ Λ := fun u hu =>
    hR' _ (add_mem ha (hR u hu).1) (isHalf_add hae (hR u hu).2)
  choose σ hσ hσu using ex
  rw [heisO_sum]
  have hinj : ∀ u₁ h₁ u₂ h₂, σ u₁ h₁ = σ u₂ h₂ → u₁ = u₂ := by
    intro u₁ h₁ u₂ h₂ h
    refine (hR' u₁ (hR u₁ h₁).1 (hR u₁ h₁).2).unique ⟨h₁, by rw [sub_self]; exact zero_mem _⟩ ⟨h₂, ?_⟩
    have := sub_mem (hσ u₁ h₁).2 (hσ u₂ h₂).2
    rwa [h, sub_sub_sub_cancel_right, add_sub_add_left_eq_sub] at this
  refine Finset.sum_bij σ (fun u hu => (hσ u hu).1) hinj
    (fun v hv => ?_) fun u hu => ?_
  · obtain ⟨u, hu, h⟩ := Finset.surj_on_of_inj_on_of_card_le σ (fun u hu => (hσ u hu).1)
      (fun u₁ u₂ h₁ h₂ => hinj u₁ h₁ u₂ h₂) le_rfl v hv
    exact ⟨u, hu, h.symm⟩
  · have hv := hR _ (hσ u hu).1
    have hd : IsHalf e (a + u - σ u hu) := isHalf_sub (isHalf_add hae (hR u hu).2) hv.2
    rw [← heisO_add_of_orth ψ S T (half_orth he hae (hR u hu).2)]
    conv_rhs => rw [← hG _ (hσ u hu).2 (sub_mem (add_mem ha (hR u hu).1) hv.1) hd]
    rw [← heisO_add_of_orth ψ S T (half_orth he hv.2 hd), add_sub_cancel]

theorem isLatVac_sum {Λ Λ' : AddSubgroup (WO S T)} {e : AE D} (he : IsSplitIdem D e)
    (hd : ∀ u ∈ Λ', ∀ u' ∈ Λ', ψ (symplO S T u u') = 1)
    (hst : ∀ u ∈ Λ', e • u ∈ Λ') (hst' : ∀ u ∈ Λ', cA D e • u ∈ Λ')
    (hoff : ∀ u ∈ Λ', (1 - (e + cA D e)) • u ∈ Λ) {R R' : Finset (WO S T)}
    (hR : ∀ u ∈ R, u ∈ Λ' ∧ IsHalf e u) (hRu : ∀ u ∈ Λ', IsHalf e u → ∃! v, v ∈ R ∧ u - v ∈ Λ)
    (hR' : ∀ u ∈ R', u ∈ Λ' ∧ IsHalf (cA D e) u) (hRu' : ∀ u ∈ Λ', IsHalf (cA D e) u → ∃! v, v ∈ R' ∧ u - v ∈ Λ)
    {f : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) Λ f) :
    IsLatVac (heisO ψ S T) Λ' (∑ u ∈ R, ∑ u' ∈ R', heisO ψ S T u (heisO ψ S T u' f)) := by
  have he' := isSplitIdem_conj he
  have hF : (∑ u ∈ R, ∑ u' ∈ R', heisO ψ S T u (heisO ψ S T u' f)) =
      ∑ u ∈ R, heisO ψ S T u (∑ u' ∈ R', heisO ψ S T u' f) :=
    Finset.sum_congr rfl fun u _ => (heisO_sum ψ S T u R' _).symm
  rw [hF]

  have pass : ∀ (Q : Finset (WO S T)) (G : WO S T → ℂ), (∀ u ∈ Q, u ∈ Λ') → ∀ d ∈ Λ', heisO ψ S T d G = G →
      heisO ψ S T d (∑ u ∈ Q, heisO ψ S T u G) = ∑ u ∈ Q, heisO ψ S T u G := by
    intro Q G hQ d hdΛ hG
    rw [heisO_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [heisO_comm, hd d hdΛ u (hQ u hu), one_smul, hG]
  set G := ∑ u' ∈ R', heisO ψ S T u' f with hGdef
  set F := ∑ u ∈ R, heisO ψ S T u G with hFdef
  have hA : ∀ a ∈ Λ', IsHalf e a → heisO ψ S T a F = F := fun a ha hae =>
    sum_reps_invariant he hR hRu
      (fun d hdΛ hdΛ' hde => pass R' f (fun u hu => (hR' u hu).1) d hdΛ' (hf.2 e he d hdΛ hde)) ha hae
  have hB : ∀ b ∈ Λ', IsHalf (cA D e) b → heisO ψ S T b F = F := fun b hb hbe =>
    pass R G (fun u hu => (hR u hu).1) b hb
      (sum_reps_invariant he' hR' hRu' (fun d hdΛ _ hde => hf.2 _ he' d hdΛ hde) hb hbe)
  have hC : ∀ d ∈ Λ', heisO ψ S T d f = f → heisO ψ S T d F = F := fun d hdΛ hdf =>
    pass R G (fun u hu => (hR u hu).1) d hdΛ (pass R' f (fun u hu => (hR' u hu).1) d hdΛ hdf)
  have hdec : ∀ u : WO S T, u = e • u + (cA D e • u + (1 - (e + cA D e)) • u) := by
    intro u
    rw [← add_smul, ← add_smul, ← add_assoc, add_sub_cancel, one_smul]
  have hoff' : ∀ u ∈ Λ', (1 - (e + cA D e)) • u ∈ Λ' := by
    intro u hu
    rw [sub_smul, add_smul, one_smul]
    exact sub_mem hu (add_mem (hst u hu) (hst' u hu))
  have key : ∀ u ∈ Λ', heisO ψ S T ((1 - (e + cA D e)) • u) f = f →
      ψ (symplOH S T (e • u) (cA D e • u + (1 - (e + cA D e)) • u)) = 1 →
      ψ (symplOH S T (cA D e • u) ((1 - (e + cA D e)) • u)) = 1 → heisO ψ S T u F = F := by
    intro u hu h0 h1 h2
    have e1 := heisO_heisO ψ S T (cA D e • u) ((1 - (e + cA D e)) • u) F
    rw [h2, one_smul, hC _ (hoff' u hu) h0, hB _ (hst' u hu) (isHalf_smul he'.1 u)] at e1
    have e2 := heisO_heisO ψ S T (e • u) (cA D e • u + (1 - (e + cA D e)) • u) F
    rw [h1, one_smul, ← e1, hA _ (hst u hu) (isHalf_smul he.1 u), ← hdec u] at e2
    exact e2.symm
  have two : ∀ x ∈ Λ', ∀ y ∈ Λ', ψ (symplOH S T (2 • x) y) = 1 := by
    intro x hx y hy
    rw [two_nsmul, symplOH_add_left, symplOH_add_self, hd x hx y hy]
  refine ⟨fun u hu => key _ (nsmul_mem hu 2) ?_ ?_ ?_, fun e₁ he₁ u hu hue => ?_⟩
  · rw [smul_comm]
    exact hf.1 _ (hoff u hu)
  · rw [smul_comm e]
    exact two _ (hst u hu) _ (add_mem (hst' _ (nsmul_mem hu 2)) (hoff' _ (nsmul_mem hu 2)))
  · rw [smul_comm (cA D e)]
    exact two _ (hst' u hu) _ (hoff' _ (nsmul_mem hu 2))
  · have hh : ∀ a : AE D, IsHalf e₁ (a • u) := by
      intro a
      rw [isHalf_iff, smul_comm, (isHalf_iff _ _).1 hue]
    refine key u hu (hf.2 e₁ he₁ _ (hoff u hu) (hh _)) ?_ ?_
    · rw [symplOH, half_orth he₁ (hh _) (isHalf_add (hh _) (hh _)), mul_zero, AddChar.map_zero_eq_one]
    · rw [symplOH, half_orth he₁ (hh _) (hh _), mul_zero, AddChar.map_zero_eq_one]

end GlobalTheory.SplitScalar

end

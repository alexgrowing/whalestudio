import Development.WeilBound.ThetaLifts.LocalTheory.AdmissiblePureTensorSchwartz

noncomputable section

namespace PositivityTheory.ThKG.Loc

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKF
open scoped Classical

variable {n d n₁ d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d} {Y₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}
  {M : Model σ Y W} {om : Rep σ Y W} {M₁ : Model σ Y₁ W₁} {om₁ : Rep σ Y₁ W₁} {H' : Plane E d d₁} {χ : Chr F E} {r : ℝ}
  {S : ∀ v : Pl F, Submodule ℂ (Fl F v n d)} {S₁ : ∀ v : Pl F, Submodule ℂ (Fl F v n₁ d₁)} {Ev : Fn F n d → Fn F n₁ d₁}
  {L : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)} {Λ : ∀ v : Pl F, Fl F v n d →ₗ[ℂ] Fl F v n₁ d₁}

theorem mem_polData {f} (hf : f ∈ M.Pol B.ψ B.emb) {φ} (le : ∀ v, S v ≤ SB _) (a : admitted M S φ) : pure f φ ∈ PolData B M :=
  Submodule.subset_span ⟨f, hf, φ, fun v => le v (a.1 v), a.2, rfl⟩

theorem br_of (ex : ∀ h₁ : UA σ W₁.J, ∃ m : UA σ W.J, IsLevi H' 1 h₁ m) (pol : ∀ f ∈ M.Pol B.ψ B.emb, L f ∈ M₁.Pol B.ψ B.emb)
    (mapS : ∀ v, ∀ x ∈ S v, Λ v x ∈ S₁ v)
    (fac : ∀ φ, admitted M S φ → ∀ v₀, ∃ (c : ℂ) (ψ : ∀ v, Fl F v n₁ d₁), c ≠ 0 ∧ admitted M₁ S₁ ψ ∧ (∀ v, ∃ a : ℂ, Λ v (φ v) = a • ψ v) ∧
      ∀ (f : SInf F _), ∀ x ∈ S v₀, Ev (pure f (Function.update φ v₀ x)) = c • pure (L f) (Function.update ψ v₀ (Λ v₀ x)))
    {C : ℂ} (hC : C ≠ 0)
    (comp : ∀ f ∈ M.Pol B.ψ B.emb, ∀ φ, admitted M S φ → ∃ T : UA σ W.J → ℂ, HasLaw W₁ H' χ r T ∧
      (∀ u ∈ unip σ W H', ∀ h, T (u * h) = T h) ∧ (M.I om (pure f φ) = 0 → T = 0) ∧
      ∀ h₁ m, IsLevi H' 1 h₁ m → ∀ h, T (m * h) = C * M₁.I om₁ (Ev (om (1, h) (pure f φ))) h₁) :
    Br B M om M₁ om₁ H' χ r S S₁ Ev L Λ := by
  have one : ∀ Φ, om (1, 1) Φ = Φ := fun Φ => by rw [Prod.mk_one_one, map_one]; rfl
  refine ⟨pol, mapS, fac, fun f hf φ a h0 => funext fun h₁ => ?_, fun f hf φ a t h₁ m hl u hu h' => ?_⟩
  · obtain ⟨T, -, -, h3, h4⟩ := comp f hf φ a
    obtain ⟨m, hm⟩ := ex h₁
    have := h4 h₁ m hm 1
    rw [h3 h0, one] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hC
  · obtain ⟨T, h1, h2, -, h4⟩ := comp f hf φ a
    obtain ⟨m', hm'⟩ := ex h'
    obtain ⟨l, hl'⟩ := ex (h' * h₁)
    have k := law_par h1 h2 hl hu hm' hl'
    have k2 := h4 _ l hl' 1
    rw [mul_one, one] at k2
    rw [h4 h' m' hm', k2] at k
    apply mul_left_cancel₀ hC
    rw [k]; ring

theorem fac_ev {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (h : IsEvLoc M M₁ e L Λ) (le : ∀ v, S v ≤ SB _) (mapS : ∀ v, ∀ x ∈ S v, Λ v x ∈ S₁ v) :
    ∀ φ, admitted M S φ → ∀ v₀, ∃ (c : ℂ) (ψ : ∀ v, Fl F v n₁ d₁), c ≠ 0 ∧ admitted M₁ S₁ ψ ∧ (∀ v, ∃ a : ℂ, Λ v (φ v) = a • ψ v) ∧
      ∀ (f : SInf F _), ∀ x ∈ S v₀, e (pure f (Function.update φ v₀ x)) = c • pure (L f) (Function.update ψ v₀ (Λ v₀ x)) := by
  intro φ a v₀
  refine ⟨1, fun v => Λ v (φ v), one_ne_zero, ⟨fun v => mapS v _ (a.1 v), a.2.mono fun v hv => by beta_reduce; rw [hv, (h.vac v).1]⟩,
    fun v => ⟨1, (one_smul _ _).symm⟩, fun f x hx => ?_⟩
  have b := a.upd hx
  rw [h.pure f _ (fun v => le v (b.1 v)) b.2, one_smul]
  congr 1
  funext v
  exact Function.apply_update (fun v => Λ v) φ v₀ x v

theorem fac_cone {T₀ : Finset (Pl F)} {u : Pl F → ℂ} {k : ℂ} (hk : k ≠ 0) (hu : ∀ v ∉ T₀, u v ≠ 0 ∧ Λ v (M.vac v) = u v • M₁.vac v)
    (le : ∀ v, S v ≤ SB _) (mapS : ∀ v, ∀ x ∈ S v, Λ v x ∈ S₁ v) (hv : ∀ v, M.vac v ∈ S v → M₁.vac v ∈ S₁ v)
    (h : ∀ T : Finset (Pl F), T₀ ⊆ T → ∀ (f : SInf F _) φ, (∀ v, φ v ∈ SB _) → (∀ v ∉ T, φ v = M.vac v) →
      (∏ v ∈ T \ T₀, u v) • Ev (pure f φ) = k • pure (L f) fun v => if v ∈ T then Λ v (φ v) else M₁.vac v) :
    ∀ φ, admitted M S φ → ∀ v₀, ∃ (c : ℂ) (ψ : ∀ v, Fl F v n₁ d₁), c ≠ 0 ∧ admitted M₁ S₁ ψ ∧ (∀ v, ∃ a : ℂ, Λ v (φ v) = a • ψ v) ∧
      ∀ (f : SInf F _), ∀ x ∈ S v₀, Ev (pure f (Function.update φ v₀ x)) = c • pure (L f) (Function.update ψ v₀ (Λ v₀ x)) := by
  intro φ a v₀
  let T : Finset (Pl F) := insert v₀ (T₀ ∪ (Filter.eventually_cofinite.1 a.2).toFinset)
  have sub : T₀ ⊆ T := Finset.subset_union_left.trans (Finset.subset_insert _ _)
  have off : ∀ v ∉ T, φ v = M.vac v := fun v hv => by_contra fun hn =>
    hv (Finset.mem_insert_of_mem (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 hn)))
  have pne : (∏ v ∈ T \ T₀, u v) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v hv => (hu v (Finset.mem_sdiff.1 hv).2).1
  refine ⟨(∏ v ∈ T \ T₀, u v)⁻¹ * k, fun v => if v ∈ T then Λ v (φ v) else M₁.vac v, mul_ne_zero (inv_ne_zero pne) hk,
    ⟨fun v => ?_, T.eventually_cofinite_notMem.mono fun v hv => if_neg hv⟩, fun v => ?_, fun f x hx => ?_⟩
  · beta_reduce
    split_ifs with hT
    exacts [mapS v _ (a.1 v), hv v (off v hT ▸ a.1 v)]
  · by_cases hT : v ∈ T
    · exact ⟨1, by beta_reduce; rw [if_pos hT, one_smul]⟩
    · exact ⟨u v, by beta_reduce; rw [if_neg hT, off v hT, (hu v fun h => hT (sub h)).2]⟩
  · have b := a.upd hx
    have := h T sub f _ (fun v => le v (b.1 v)) fun v hv => by
      rw [Function.update_of_ne (fun e : v = v₀ => hv (by rw [e]; exact Finset.mem_insert_self _ _)), off v hv]
    rw [mul_smul, ← (inv_smul_smul₀ pne (Ev _)), this]
    congr 3
    funext v
    by_cases e : v = v₀
    · subst e; rw [Function.update_self, Function.update_self, if_pos (Finset.mem_insert_self _ _)]
    · rw [Function.update_of_ne e, Function.update_of_ne e]

theorem ev_pol {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (h : IsEvLoc M M₁ e L Λ) (g : M.IsGood B.ψ) (g₁ : M₁.IsGood B.ψ)
    (hm : (PolData B M).map e = PolData B M₁) :
    (∀ f ∈ M.Pol B.ψ B.emb, L f ∈ M₁.Pol B.ψ B.emb) ∧ ∀ f₁ ∈ M₁.Pol B.ψ B.emb, ∃ f ∈ M.Pol B.ψ B.emb, L f = f₁ := by
  refine ⟨fun f hf => arch_slice (vac_ne g₁) g₁.std _ ?_, fun f₁ hf₁ => ?_⟩
  · have : e (pure f M.vac) ∈ PolData B M₁ := hm ▸ Submodule.mem_map_of_mem
      (Submodule.subset_span ⟨f, hf, M.vac, vac_sb g, Eventually.of_forall fun _ => rfl, rfl⟩)
    rw [h.pure f _ (vac_sb g) (Eventually.of_forall fun _ => rfl)] at this
    simp only [(h.vac _).1] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨f, hf, ψ, -, -, rfl⟩
    exact ⟨f, hf, ψ, rfl⟩
  · refine Submodule.mem_map.1 (arch_slice (vac_ne g₁) g₁.std ((M.Pol B.ψ B.emb).map (L : _ →ₗ[ℂ] _)) ?_)
    have : pure f₁ M₁.vac ∈ (PolData B M).map e := hm ▸
      Submodule.subset_span ⟨f₁, hf₁, M₁.vac, vac_sb g₁, Eventually.of_forall fun _ => rfl, rfl⟩
    rw [PolData, Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨f, hf, ψ, h1, h2, rfl⟩, rfl⟩
    exact ⟨L f, Submodule.mem_map_of_mem hf, _, h.pure f ψ h1 h2⟩

section Pt

variable {P₁ : Type} [AddCommGroup P₁] [Module ℂ P₁] {Q₁ : Pl F → Type} [∀ v, AddCommGroup (Q₁ v)] [∀ v, Module ℂ (Q₁ v)]
  {pi₁ : SInf F (Fin n₁ × Fin d₁) →ₗ[ℂ] P₁} {p₁ : ∀ v, Fl F v n₁ d₁ →ₗ[ℂ] Q₁ v}

theorem pt_of (hi : ∃ f ∈ M.Pol B.ψ B.emb, pi₁ (L f) ≠ 0) (T : Finset (Pl F)) (h1 : ∀ v ∈ T, ∃ x ∈ S v, p₁ v (Λ v x) ≠ 0)
    (h2 : ∀ v ∉ T, M.vac v ∈ S v ∧ p₁ v (Λ v (M.vac v)) ≠ 0) : Pt B M S pi₁ p₁ L Λ := by
  obtain ⟨f, hf, h0⟩ := hi
  choose x hx hx' using h1
  refine ⟨f, hf, fun v => if h : v ∈ T then x v h else M.vac v, ⟨fun v => ?_, T.eventually_cofinite_notMem.mono fun v hv => dif_neg hv⟩,
    h0, fun v => ?_⟩ <;> dsimp only <;> split_ifs with h
  exacts [hx v h, (h2 v h).1, hx' v h, (h2 v h).2]

theorem bump_pt {χX χW : Chr F E} {r s r' s' : ℕ} (H : Hyp) (hp : IsPair B M₁ χX χW om₁ r s r' s') (s₁ : Side B M₁ om₁ pi₁ p₁ S₁)
    (dn : Dense (M.Pol B.ψ B.emb : Set (SInf F (Fin n × Fin d)))) (pol : ∀ f ∈ M.Pol B.ψ B.emb, L f ∈ M₁.Pol B.ψ B.emb)
    (nz : ∃ (f : SInf F _) (φ : _), admitted M₁ S₁ φ ∧ M₁.I om₁ (pure f φ) ≠ 0)
    (bump : ∀ l : SInf F _ →L[ℂ] ℂ, l ≠ 0 →
      (∀ g ∈ UAt σ Y₁ (evI F), ∀ f f₁ : SInf F _, Acts (evI F) (om₁ (g, 1)) f f₁ → l f₁ = l f) → ∃ f, l (L f) ≠ 0) :
    ∃ f ∈ M.Pol B.ψ B.emb, pi₁ (L f) ≠ 0 := by
  obtain ⟨f₀, φ, a, h0⟩ := nz
  obtain ⟨h, hh⟩ := Function.ne_iff.1 h0
  obtain ⟨l, hl⟩ := s₁.clm a h
  obtain ⟨f, hf⟩ := bump l (fun e => hh (by rw [← hl, e]; rfl)) fun g hg f f₁ ac => by
    obtain ⟨T, hT, -⟩ := H.op F E σ B _ _ _ _ M₁ _ _ om₁ _ _ _ _ hp g hg 1 uat_one
    rw [(s₁.uniq f f₁ (T f)).1 _ ac (hT.2 f), hl, hl, ← s₁.arch a hT,
      H.unim F E σ B _ _ _ _ M₁ _ _ om₁ _ _ _ _ hp _ (admissible_pure_tensor_schwartz hp.good f ⟨fun v => s₁.le v (a.1 v), a.2⟩)]
  by_contra hn
  push_neg at hn
  have : (l.comp L : _ → ℂ) = fun _ => 0 := (l.comp L).continuous.ext_on dn continuous_const fun g hg => by
    show l (L g) = 0
    rw [hl, s₁.kill _ (pol g hg) φ a (Or.inl (hn g hg))]; rfl
  exact hf (congrFun this f)

theorem nz_pure (s₁ : Side B M₁ om₁ pi₁ p₁ S₁) (𝓖 : Set (Fn F n₁ d₁)) (h : ∀ Φ ∈ 𝓖, ∃ (f : SInf F _) (φ : _), admitted M₁ S₁ φ ∧ Φ = pure f φ)
    {Φ} (hΦ : Φ ∈ Submodule.span ℂ 𝓖) (h0 : M₁.I om₁ Φ ≠ 0) : ∃ (f : SInf F _) (φ : _), admitted M₁ S₁ φ ∧ M₁.I om₁ (pure f φ) ≠ 0 := by
  by_contra hn
  push_neg at hn
  obtain ⟨𝓒, h1, h2⟩ := s₁.cls
  have : Φ ∈ 𝓒 ∧ M₁.I om₁ Φ = 0 := by
    clear h0
    induction hΦ using Submodule.span_induction with
    | mem Φ hΦ => obtain ⟨f, φ, a, rfl⟩ := h Φ hΦ; exact ⟨h1 f φ a, hn f φ a⟩
    | zero => exact ⟨zero_mem _, I_zero _ _⟩
    | add x y _ _ hx hy => exact ⟨add_mem hx.1 hy.1, funext fun g => by rw [h2 _ hx.1 _ hy.1, hx.2, hy.2]; simp⟩
    | smul c x _ hx => exact ⟨𝓒.smul_mem _ hx.1, funext fun g => by rw [I_smul, hx.2]; simp⟩
  exact h0 this.2

end Pt

theorem coneI_eq {om' : Rep σ Y W} {K : Subgroup (UA σ Y.J)} {m : LocMeas K} {ei L' : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)}
    {u ν ν' z} (pres : ∀ g ∈ UAt σ Y (evI F), ∀ Φ ∈ schA F _, om (g, 1) Φ = om' (g, 1) Φ)
    (hν : ∀ l : (AE F E)ˣ, At (evI F) ((l : AE F E) - 1) → ν l = ν' l)
    (a : IsConeI B M om m ei u ν z L) (b : IsConeI B M om' m ei u ν' z L') : L = L' := by
  ext f y
  rw [a, b]
  congr 1; funext k; congr 1; funext l
  have hl : At (evI F) ((l.1 : AE F E) - 1) := by
    have := l.2
    generalize l.1 = x at this
    induction this using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => intro u _; simp
    | mul x y _ _ hx hy =>
      intro u hu
      have e : ((x * y : (AE F E)ˣ) : AE F E) - 1 = ((x : AE F E) - 1) * y + ((y : AE F E) - 1) := by push_cast; ring
      rw [e, smul_add, ← smul_mul_assoc, hx u hu, hy u hu]; simp
    | inv x _ hx =>
      intro u hu
      have e : ((x⁻¹ : (AE F E)ˣ) : AE F E) - 1 = -(((x : AE F E) - 1) * (x⁻¹ : (AE F E)ˣ)) := by
        rw [sub_mul, Units.mul_inv]; ring
      rw [e, smul_neg, ← smul_mul_assoc, hx u hu]; simp
  have e : ∀ w (f₁ : SInf F _), Acts (evI F) (fun Φ => M.co.rho B.ψ w (om (k.1, 1) Φ)) f f₁ ↔
      Acts (evI F) (fun Φ => M.co.rho B.ψ w (om' (k.1, 1) Φ)) f f₁ := fun w f₁ =>
    forall₂_congr fun r hr => by beta_reduce; rw [pres _ (uat_closure k.2.2) _ hr.2]
  rw [hν _ hl]
  simp only [opI, e]

theorem tens_step {T : Finset (Pl F)} {P P₁ : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁] {Q Q₁ : Pl F → Type}
    [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] [∀ v, AddCommGroup (Q₁ v)] [∀ v, Module ℂ (Q₁ v)] (li : P →ₗ[ℂ] P₁)
    (lf : ∀ v, Q v →ₗ[ℂ] Q₁ v) (c : ℂ) (w : Pl F → ℂ) {ι ι' : Type} [Fintype ι] [Fintype ι'] (x : ι → P) (y : ι → ∀ v, Q v)
    (x' : ι' → P) (y' : ι' → ∀ v, Q v)
    (h : ∑ i, x i ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => y i v) = ∑ j, x' j ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => y' j v))
    (k : ℂ) : ∑ i, ((k * c * ∏ v ∈ T, w v) • li (x i)) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => lf v (y i v)) =
      ∑ j, (k • c • li (x' j)) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => w v • lf v (y' j v)) := by
  have := congrArg (fun z => (k * c * ∏ v ∈ T, w v) • TensorProduct.map li (PiTensorProduct.map fun v : T => lf v) z) h
  simp only [map_sum, TensorProduct.map_tmul, PiTensorProduct.map_tprod, Finset.smul_sum] at this
  simp only [← TensorProduct.smul_tmul', this, MultilinearMap.map_smul_univ, TensorProduct.tmul_smul, smul_smul,
    Finset.prod_coe_sort T w]
  exact Finset.sum_congr rfl fun j _ => by congr 1; ring

end PositivityTheory.ThKG.Loc

end

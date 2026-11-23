import Development.WeilBound.ThetaLifts.SmallCones.KerPol

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT.Ker

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.Mix
open Matrix (vecMulVec)

theorem split_triv {A I J : Type} {e : I → A → ℂ} {c : I → ℂ} {j : J → I} (hj : Function.Injective j) (h1 : ∀ k a, e (j k) a = 1)
    {a : A} {S : ℂ} (h : HasSum (fun i => c i * e i a) S) :
    HasSum (fun i : ↥(Set.range j)ᶜ => c i * e i a) (S - ∑' k, c (j k)) := by
  have h2 := h.summable.tsum_subtype_add_tsum_subtype_compl (Set.range j)
  rw [tsum_range (fun i => c i * e i a) hj, h.tsum_eq] at h2
  simp only [h1, mul_one] at h2
  rw [← h2, add_sub_cancel_left]
  exact (h.summable.subtype _).hasSum

theorem triv_part {A I₁ I₂ J₁ J₂ : Type} [AddCommGroup A] {e₁ : I₁ → A → ℂ} {e₂ : I₂ → A → ℂ} {c₁ : I₁ → ℂ} {c₂ : I₂ → ℂ}
    {j₁ : J₁ → I₁} {j₂ : J₂ → I₂} (i₁ : Function.Injective j₁) (i₂ : Function.Injective j₂)
    (m₁ : ∀ i a b, e₁ i (a + b) = e₁ i a * e₁ i b) (m₂ : ∀ i a b, e₂ i (a + b) = e₂ i a * e₂ i b)
    (l₁ : ∀ i a, ‖e₁ i a‖ ≤ 1) (l₂ : ∀ i a, ‖e₂ i a‖ ≤ 1) (t₁ : ∀ k a, e₁ (j₁ k) a = 1) (t₂ : ∀ k a, e₂ (j₂ k) a = 1)
    (n₁ : ∀ i ∉ Set.range j₁, ∃ a, e₁ i a ≠ 1) (n₂ : ∀ i ∉ Set.range j₂, ∃ a, e₂ i a ≠ 1) (s₁ : Summable c₁) (s₂ : Summable c₂)
    {S : A → ℂ} (h₁ : ∀ a, HasSum (fun i => c₁ i * e₁ i a) (S a)) (h₂ : ∀ a, HasSum (fun i => c₂ i * e₂ i a) (S a)) :
    ∑' k, c₁ (j₁ k) = ∑' k, c₂ (j₂ k) := by
  refine sub_eq_zero.1 (GlobalTheory.CompanionTheory.ThetaInj.charSeries_coeff_eq_zero (A := A) (I := Unit ⊕ (↥(Set.range j₁)ᶜ ⊕ ↥(Set.range j₂)ᶜ))
    (Sum.elim (fun _ _ => 1) (Sum.elim (fun i => e₁ i) fun i => e₂ i))
    (Sum.elim (fun _ => ∑' k, c₁ (j₁ k) - ∑' k, c₂ (j₂ k)) (Sum.elim (fun i => c₁ i) fun i => -c₂ i)) (Sum.inl ())
    ?_ ?_ (fun _ => rfl) ?_ (Summable.norm ?_) fun a => ?_)
  · rintro (_ | i | i) a b
    exacts [(one_mul _).symm, m₁ i a b, m₂ i a b]
  · rintro (_ | i | i) a
    exacts [norm_one.le, l₁ i a, l₂ i a]
  · rintro (_ | i | i) h
    exacts [absurd rfl h, n₁ i i.2, n₂ i i.2]
  · exact Summable.sum _ Summable.of_finite (Summable.sum _ (s₁.subtype _) (s₂.subtype _).neg)
  · refine HasSum.tsum_eq ?_
    have k₂ : HasSum (fun i : ↥(Set.range j₂)ᶜ => -c₂ i * e₂ i a) (-(S a - ∑' k, c₂ (j₂ k))) := by
      simpa only [neg_mul] using (split_triv i₂ t₂ (h₂ a)).neg
    rw [show (0 : ℂ) = (∑' k, c₁ (j₁ k) - ∑' k, c₂ (j₂ k)) * 1 + ((S a - ∑' k, c₁ (j₁ k)) + -(S a - ∑' k, c₂ (j₂ k))) by ring]
    refine HasSum.sum (hasSum_unique _) (HasSum.sum ?_ ?_)
    · exact split_triv i₁ t₁ (h₁ a)
    · exact k₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {H : Plane E n n₁} {H' : Plane E d d₁} {ε ε' : ℤ}

theorem PG.eps_ne (h : PG σ X X₁ H ε) : (ε : E) ≠ 0 := left_ne_zero_of_mul_eq_one h.rat.ee

theorem PG.nd_low' (h : PG σ X X₁ H ε) (u) (hu : ∀ z, bf σ.toRingHom X.J (H.ι *ᵥ u) (H.ι *ᵥ z) = 0) : u = 0 :=
  h.nd_low u fun z => by rw [h.rat.symm, hu, map_zero, mul_zero]

theorem PG.line (h : PG σ X X₁ H ε) (a) (h1 : bf σ.toRingHom X.J a H.x = 0) (h2 : ∀ z, bf σ.toRingHom X.J a (H.ι *ᵥ z) = 0) :
    ∃ ξ : E, ξ • H.x = a := by
  obtain ⟨s, t, z, rfl⟩ := h.rat.span a
  simp only [bf_add_l, bf_smul_l, h.rat.xx, h.rat.ix, h.rat.yx, h.rat.xi, h.rat.yi, mul_zero, zero_add, add_zero] at h1 h2
  refine ⟨s, ?_⟩
  rw [h.nd_low' z h2, (mul_eq_zero.1 h1).resolve_right h.eps_ne]
  simp

theorem PG.x_ne (h : PG σ X X₁ H ε) : H.x ≠ 0 := fun h0 => by
  have := h.rat.xy
  rw [h0] at this
  simp [bf] at this

variable (H H') in

def capAB : Submodule (AE F E) (Ten F E n d) where
  carrier := sumA H H' ∩ sumB H H'
  zero_mem' := ⟨⟨0, 0, by simp [vv0]⟩, ⟨0, 0, by simp [vv0]⟩⟩
  add_mem' := by
    rintro a b ⟨⟨y, z, e⟩, ⟨z', y', e'⟩⟩ ⟨⟨y₁, z₁, e₁⟩, ⟨z₁', y₁', e₁'⟩⟩
    refine ⟨⟨y + y₁, z + z₁, ?_⟩, ⟨z' + z₁', y' + y₁', ?_⟩⟩
    · rw [e, e₁, Matrix.add_vecMulVec, Matrix.mulVec_add, Matrix.vecMulVec_add]; abel
    · rw [e', e₁', Matrix.mulVec_add, Matrix.add_vecMulVec, Matrix.vecMulVec_add]; abel
  smul_mem' := by
    rintro c a ⟨⟨y, z, e⟩, ⟨z', y', e'⟩⟩
    refine ⟨⟨c • y, c • z, ?_⟩, ⟨c • z', c • y', ?_⟩⟩
    · rw [e, Matrix.smul_vecMulVec, Matrix.mulVec_smul, Matrix.vecMulVec_smul, smul_add]
    · rw [e', Matrix.mulVec_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_add]

theorem cap_xx : incM F (vecMulVec H.x H'.x) ∈ capAB (F := F) H H' := by
  rw [incM_vv]
  exact ⟨⟨incV F H.x, 0, by simp [vv0]⟩, ⟨incV F H'.x, 0, by simp [vv0]⟩⟩

theorem cap_ix (u) : incM F (vecMulVec (H.ι *ᵥ u) H'.x) ∈ capAB (F := F) H H' := by
  rw [incM_vv, ← inc_mulVec]
  exact ⟨⟨incM F H.ι *ᵥ incV F u, 0, by simp [vv0]⟩, ⟨0, incV F u, by simp [vv0]⟩⟩

theorem cap_xi (u) : incM F (vecMulVec H.x (H'.ι *ᵥ u)) ∈ capAB (F := F) H H' := by
  rw [incM_vv, ← inc_mulVec]
  exact ⟨⟨0, incV F u, by simp [vv0]⟩, ⟨incM F H'.ι *ᵥ incV F u, 0, by simp [vv0]⟩⟩

theorem incM_smul (l : E) (v : Matrix (Fin n) (Fin d) E) : incM F (l • v) = inclR (F := F) (AF F) l • incM F v := by
  ext i j
  simp [incM]

theorem exists_ne (M : Model σ X W) (hψ : IsStd B.ψ) (cc : ∀ a, σ (σ a) = a) {x v : Matrix (Fin n) (Fin d) E}
    (hv : incM F v ∈ capAB (F := F) H H') (h : hTens σ X.J W.J x v ≠ 0) :
    ∃ a : capAB (F := F) H H', B.ψ (sy σ X W (incM F x) a.1) ≠ 1 := by
  obtain ⟨l, hl⟩ : ∃ l, Algebra.trace F E (-hTens σ X.J W.J x v * l) ≠ 0 := by
    by_contra h0
    push Not at h0
    exact h (neg_eq_zero.1 ((traceForm_nondegenerate F E).1 _ fun a => h0 a))
  obtain ⟨b, hb⟩ := DFunLike.ne_iff.1 (std_ne_one hψ)
  refine ⟨⟨(b * algebraMap F (AF F) (Algebra.trace F E (-hTens σ X.J W.J x v * l))⁻¹) • incM F (σ l • v), ?_⟩, ?_⟩
  · rw [← algebraMap_smul (AE F E), incM_smul]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hv)
  · have e := sy_inc (σ := σ) (X := X) (W := W) x (σ l • v)
    rw [hT_smul_r, cc, mul_comm, ← neg_mul] at e
    change B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) _ _) ≠ 1
    rw [form_eq M.co, map_smul, ← form_eq M.co, show symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) _ _ = _ from e,
      smul_eq_mul, mul_assoc, ← map_mul, inv_mul_cancel₀ hl, map_one, mul_one]
    simpa using hb

theorem twoExp_of (hE : ThetaExp) : TwoExp := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' hB hX hW hM hM₀ eA eB hA hBv
  have hψ := hB.std
  have p := pg_herm hB hH hX
  have p' := pg_skew hB hH' hW
  have hA' := isEv_sumA hψ p' hA
  have hB' := isEv_sumB hψ p hBv
  obtain ⟨C, hC, h1⟩ := (polA p p').exp hE hB hM hM₀ hA'
  obtain ⟨C', hC', h2⟩ := (polB p p').exp hE hB hM hM₀ hB'
  have eA' : ∀ ξ : E, vA H.y H'.y H'.ι (ξ • H.x, 0) = ξ • vecMulVec H.x H'.y := fun ξ => by
    simp [vv0, vA_apply, Matrix.smul_vecMulVec]
  have eB' : ∀ ξ : E, vB H.y H'.y H.ι (ξ • H'.x, 0) = ξ • vecMulVec H.y H'.x := fun ξ => by
    simp [vB_apply, Matrix.vecMulVec_smul]
  have iA : Function.Injective fun ξ : E => ((ξ • H.x, 0) : (Fin n → E) × (Fin d₁ → E)) := fun a b e =>
    smul_left_injective E p.x_ne (congrArg Prod.fst e)
  have iB : Function.Injective fun ξ : E => ((ξ • H'.x, 0) : (Fin d → E) × (Fin n₁ → E)) := fun a b e =>
    smul_left_injective E p'.x_ne (congrArg Prod.fst e)
  have hm : ∀ x a b, B.ψ (sy σ X W x (a + b)) = B.ψ (sy σ X W x a) * B.ψ (sy σ X W x b) := fun x a b => by
    rw [← AddChar.map_add_eq_mul]
    exact congrArg B.ψ ((formL M.co x).map_add a b)
  refine ⟨C⁻¹ * C', mul_ne_zero (inv_ne_zero hC) hC', fun Ψ hΨ => ⟨?_, ?_, ?_⟩⟩
  · simpa only [Function.comp_def, eA'] using ((summable_mul_left_iff hC).1 (h1 Ψ hΨ).summable).comp_injective iA
  · simpa only [Function.comp_def, eB'] using ((summable_mul_left_iff hC').1 (h2 Ψ hΨ).summable).comp_injective iB
  have key := triv_part (A := capAB (F := F) H H') (e₁ := fun t a => B.ψ (sy σ X W (incM F (vA H.y H'.y H'.ι t)) a.1))
    (e₂ := fun t a => B.ψ (sy σ X W (incM F (vB H.y H'.y H.ι t)) a.1)) iA iB (fun t a b => hm _ _ _) (fun t a b => hm _ _ _)
    (fun _ _ => (std_norm hψ _).le) (fun _ _ => (std_norm hψ _).le) ?_ ?_ ?_ ?_ (h1 Ψ hΨ).summable (h2 Ψ hΨ).summable
    (S := fun a => thetaSum F (M.co.rho B.ψ a.1 Ψ)) (fun a => ?_) (fun a => ?_)
  · simp only [eA', eB', tsum_mul_left] at key
    rw [mul_assoc, ← key, inv_mul_cancel_left₀ hC]
  · rintro ξ ⟨_, -, y, z, rfl⟩
    rw [eA', sy_of_hT, AddChar.map_zero_eq_one]
    rw [incM_smul, incM_vv, hT_smul_l, hT_add_r, hT_vv, hT_vv, p.ad.xx, p.ad.xi]
    simp
  · rintro ξ ⟨_, ⟨y, z, rfl⟩, -⟩
    rw [eB', sy_of_hT, AddChar.map_zero_eq_one]
    rw [incM_smul, incM_vv, hT_smul_l, hT_add_r, hT_vv, hT_vv, p'.ad.xx, p'.ad.xi]
    simp
  · rintro ⟨a, b⟩ hn
    by_contra h0
    have k : ∀ v, incM F v ∈ capAB (F := F) H H' → hTens σ X.J W.J (vA H.y H'.y H'.ι (a, b)) v = 0 := fun v hv => by
      by_contra h3
      exact h0 (exists_ne M hψ p.rat.cc hv h3)
    have k1 := k _ cap_xx
    have k2 := fun u => k _ (cap_ix u)
    have k3 := fun u => k _ (cap_xi u)
    simp only [vA_apply, hT_add_l, hT_vv, p'.rat.yx, p'.rat.ix, p'.rat.yi, p.rat.yx, p.rat.yi, mul_zero, add_zero, zero_add,
      mul_eq_zero, p.eps_ne, p'.eps_ne, or_false, false_or] at k1 k2 k3
    obtain ⟨ξ, rfl⟩ := p.line a k1 k2
    exact hn ⟨ξ, by rw [p'.nd_low' b k3]⟩
  · rintro ⟨a, b⟩ hn
    by_contra h0
    have k : ∀ v, incM F v ∈ capAB (F := F) H H' → hTens σ X.J W.J (vB H.y H'.y H.ι (a, b)) v = 0 := fun v hv => by
      by_contra h3
      exact h0 (exists_ne M hψ p.rat.cc hv h3)
    have k1 := k _ cap_xx
    have k2 := fun u => k _ (cap_xi u)
    have k3 := fun u => k _ (cap_ix u)
    simp only [vB_apply, hT_add_l, hT_vv, p'.rat.yx, p.rat.ix, p'.rat.yi, p.rat.yx, p.rat.yi, zero_mul, add_zero, zero_add,
      mul_eq_zero, p.eps_ne, p'.eps_ne, or_false, false_or] at k1 k2 k3
    obtain ⟨ξ, rfl⟩ := p'.line a k1 k2
    exact hn ⟨ξ, by rw [p.nd_low' b k3]⟩
  · convert h1 _ (rho_mem M hψ a.1 hΨ) using 2 with t
    rw [rho_comm, map_smul, hA'.inv _ a.2.1 _ (rho_mem M hψ _ hΨ), thetaSum_smul]
    ring
  · convert h2 _ (rho_mem M hψ a.1 hΨ) using 2 with t
    rw [rho_comm, map_smul, hB'.inv _ a.2.2 _ (rho_mem M hψ _ hΨ), thetaSum_smul]
    ring

end PositivityTheory.ThKCT.Ker

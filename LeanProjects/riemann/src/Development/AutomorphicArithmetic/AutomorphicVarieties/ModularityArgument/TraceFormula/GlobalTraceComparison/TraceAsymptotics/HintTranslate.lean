import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedOpenSubgroupGLw

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.BCT Formalism.UG
open PositivityTheory.Rg.BcB.G8 (K2)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section Generic

variable {G : Type} [Group G]

private theorem hint_of_rinv (K : Subgroup G) (u : G → ℂ) (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) :
    hint K u = ∑ᶠ q : G ⧸ K, u q.out := by
  have h : rStab u ⊓ K = K := inf_eq_right.2 fun k hk => hu k hk
  unfold hint
  rw [h, Subgroup.relIndex_self]
  simp

private theorem out_mk_eq (K : Subgroup G) (u : G → ℂ) (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) (x : G) :
    u ((x : G ⧸ K).out) = u x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hh]
  exact hu h h.2 x

private theorem hint_translate (K : Subgroup G) (u : G → ℂ) (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) (k : G) :
    hint K (fun z => u (k * z)) = hint K u := by
  rw [hint_of_rinv K u hu, hint_of_rinv K _ fun c hc x => by
    show u (k * (x * c)) = u (k * x)
    rw [← mul_assoc]
    exact hu c hc _]
  calc ∑ᶠ q : G ⧸ K, u (k * q.out)
      = ∑ᶠ q : G ⧸ K, (fun q' : G ⧸ K => u q'.out) ((MulAction.toPerm k : Equiv.Perm (G ⧸ K)) q) := by
        refine finsum_congr fun q => ?_
        have hq : (MulAction.toPerm k : Equiv.Perm (G ⧸ K)) q = ((k * q.out : G) : G ⧸ K) := by
          conv_lhs => rw [← QuotientGroup.out_eq' q]
          rfl
        show _ = u (((MulAction.toPerm k : Equiv.Perm (G ⧸ K)) q).out)
        rw [hq, out_mk_eq K u hu]
    _ = ∑ᶠ q : G ⧸ K, u q.out := finsum_comp_equiv (f := fun q' : G ⧸ K => u q'.out) (MulAction.toPerm k : Equiv.Perm (G ⧸ K))

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem isHecke_conv (K : Subgroup G) {A B : G → ℂ} (hA : IsHecke K A) (hB : IsHecke K B) :
    IsHecke K fun y => hint K fun z => A z * B (z⁻¹ * y) := by
  refine ⟨?_, fun k hk x => ⟨?_, ?_⟩⟩
  · refine HasCompactSupport.of_support_subset_isCompact (hA.1.isCompact.mul hB.1.isCompact) fun y hy => ?_
    have hy' : hint K (fun z => A z * B (z⁻¹ * y)) ≠ 0 := hy
    obtain ⟨z, hz⟩ : ∃ z, A z * B (z⁻¹ * y) ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hy' (by simp [hint, hc])
    exact Set.mem_mul.2 ⟨z, subset_tsupport _ (left_ne_zero_of_mul hz), z⁻¹ * y,
      subset_tsupport _ (right_ne_zero_of_mul hz), by group⟩
  · have hu : ∀ c ∈ K, ∀ z, (fun z => A z * B (z⁻¹ * x)) (z * c) = (fun z => A z * B (z⁻¹ * x)) z := by
      intro c hc z
      show A (z * c) * B ((z * c)⁻¹ * x) = A z * B (z⁻¹ * x)
      rw [(hA.2 c hc z).2, _root_.mul_inv_rev, mul_assoc, (hB.2 c⁻¹ (K.inv_mem hc) _).1]
    show hint K (fun z => A z * B (z⁻¹ * (k * x))) = hint K (fun z => A z * B (z⁻¹ * x))
    rw [← hint_translate K (fun z => A z * B (z⁻¹ * x)) hu k⁻¹]
    congr 1
    funext z
    show A z * B (z⁻¹ * (k * x)) = A (k⁻¹ * z) * B ((k⁻¹ * z)⁻¹ * x)
    rw [(hA.2 k⁻¹ (K.inv_mem hk) z).1]
    congr 2
    group
  · have h : (fun z => A z * B (z⁻¹ * (x * k))) = fun z => A z * B (z⁻¹ * x) := by
      funext z
      rw [← mul_assoc, (hB.2 k hk _).2]
    show hint K (fun z => A z * B (z⁻¹ * (x * k))) = hint K (fun z => A z * B (z⁻¹ * x))
    rw [h]

private theorem isHecke_ind (K : Subgroup G) (hK : IsCompact (K : Set G)) (S : Set G)
    (hl : ∀ k ∈ K, ∀ x ∈ S, k * x ∈ S) (hr : ∀ k ∈ K, ∀ x ∈ S, x * k ∈ S)
    (ht : ∀ x ∈ S, ∀ y ∈ S, ∃ a ∈ K, ∃ b ∈ K, y = a * x * b) :
    IsHecke K (S.indicator (1 : G → ℂ)) := by
  refine ⟨?_, fun k hk x => ⟨?_, ?_⟩⟩
  · rcases S.eq_empty_or_nonempty with rfl | ⟨d, hd⟩
    · exact HasCompactSupport.of_support_subset_isCompact isCompact_empty (by simp)
    · refine HasCompactSupport.of_support_subset_isCompact
        (IsCompact.mul (IsCompact.mul hK (isCompact_singleton (x := d))) hK) fun y hy => ?_
      have hyS : y ∈ S := by
        by_contra h
        exact hy (Set.indicator_of_notMem h _)
      obtain ⟨a, ha, b, hb, rfl⟩ := ht d hd y hyS
      exact Set.mul_mem_mul (Set.mul_mem_mul ha rfl) hb
  · have : k * x ∈ S ↔ x ∈ S := ⟨fun h => by simpa using hl k⁻¹ (K.inv_mem hk) _ h, hl k hk x⟩
    by_cases hx : x ∈ S
    · simp [hx, this]
    · simp [hx, this]
  · have : x * k ∈ S ↔ x ∈ S := ⟨fun h => by simpa using hr k⁻¹ (K.inv_mem hk) _ h, hr k hk x⟩
    by_cases hx : x ∈ S
    · simp [hx, this]
    · simp [hx, this]

private theorem isHecke_fn {ι : Type} (K : Subgroup G) (hK : IsCompact (K : Set G)) (g : ι → G → ℂ)
    (hg : ∀ i, IsHecke K (g i)) (e : Ex ι) : IsHecke K (e.fn K g) := by
  induction e with
  | one =>
    exact isHecke_ind K hK _ (fun k hk x hx => K.mul_mem hk hx) (fun k hk x hx => K.mul_mem hx hk)
      fun x hx y hy => ⟨y * x⁻¹, K.mul_mem hy (K.inv_mem hx), 1, K.one_mem, by group⟩
  | gen i => exact hg i
  | smul c a ih =>
    refine ⟨HasCompactSupport.of_support_subset_isCompact ih.1.isCompact fun y hy => ?_, fun k hk x => ?_⟩
    · exact subset_tsupport _ (right_ne_zero_of_mul hy)
    · show c * a.fn K g (k * x) = c * a.fn K g x ∧ c * a.fn K g (x * k) = c * a.fn K g x
      rw [(ih.2 k hk x).1, (ih.2 k hk x).2]
      exact ⟨rfl, rfl⟩
  | add a b iha ihb =>
    refine ⟨iha.1.add ihb.1, fun k hk x => ?_⟩
    show a.fn K g (k * x) + b.fn K g (k * x) = a.fn K g x + b.fn K g x ∧
      a.fn K g (x * k) + b.fn K g (x * k) = a.fn K g x + b.fn K g x
    rw [(iha.2 k hk x).1, (iha.2 k hk x).2, (ihb.2 k hk x).1, (ihb.2 k hk x).2]
    exact ⟨rfl, rfl⟩
  | mul a b iha ihb => exact isHecke_conv K iha ihb

end Generic

private theorem isHecke_pair {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] (K₁ : Subgroup G) (K₂ : Subgroup H) {f : G → ℂ} {g : H → ℂ}
    (hf : IsHecke K₁ f) (hg : IsHecke K₂ g) : IsHecke (K₁.prod K₂) fun y : G × H => f y.1 * g y.2 := by
  refine ⟨HasCompactSupport.of_support_subset_isCompact (hf.1.isCompact.prod hg.1.isCompact) fun y hy =>
    ⟨subset_tsupport _ (left_ne_zero_of_mul hy), subset_tsupport _ (right_ne_zero_of_mul hy)⟩, fun k hk x => ?_⟩
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hk
  show f (k.1 * x.1) * g (k.2 * x.2) = _ ∧ f (x.1 * k.1) * g (x.2 * k.2) = _
  rw [(hf.2 _ h1 _).1, (hf.2 _ h1 _).2, (hg.2 _ h2 _).1, (hg.2 _ h2 _).2]
  exact ⟨rfl, rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem isHecke_Tj (n : ℕ) (w : Pl E) (ϖ : w.adicCompletion E) (j : ℕ) :
    IsHecke (GlobalTheory.LFun.KGL w n) (Tj ℂ n (Ov E w) ϖ j) := by
  have hKe : GlobalTheory.LFun.KGL w n = GLint (Fin n) (Ov E w) := rfl
  have hc := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2
  unfold Tj
  refine isHecke_ind _ hc _ ?_ ?_ ?_
  · rintro k hk x ⟨a, ha, b, hb, hx⟩
    refine ⟨k * a, (GLint (Fin n) (Ov E w)).mul_mem (hKe ▸ hk) ha, b, hb, ?_⟩
    rw [Units.val_mul, Units.val_mul, hx]
    simp only [mul_assoc]
  · rintro k hk x ⟨a, ha, b, hb, hx⟩
    refine ⟨a, ha, b * k, (GLint (Fin n) (Ov E w)).mul_mem hb (hKe ▸ hk), ?_⟩
    rw [Units.val_mul, Units.val_mul, hx]
    simp only [mul_assoc]
  · rintro x ⟨a, ha, b, hb, hx⟩ y ⟨c, hc', d, hd, hy⟩
    refine ⟨c * a⁻¹, hKe ▸ (GLint (Fin n) (Ov E w)).mul_mem hc' ((GLint (Fin n) (Ov E w)).inv_mem ha),
      b⁻¹ * d, hKe ▸ (GLint (Fin n) (Ov E w)).mul_mem ((GLint (Fin n) (Ov E w)).inv_mem hb) hd, ?_⟩
    apply Units.ext
    have h1 : (a⁻¹).val * a.val = 1 := Units.inv_mul a
    have h2 : b.val * (b⁻¹).val = 1 := Units.mul_inv b
    simp only [Units.val_mul]
    rw [hx, hy]
    calc c.val * diagJ n ϖ j * d.val
        = c.val * 1 * diagJ n ϖ j * 1 * d.val := by simp
      _ = c.val * ((a⁻¹).val * a.val) * diagJ n ϖ j * (b.val * (b⁻¹).val) * d.val := by rw [h1, h2]
      _ = _ := by simp only [mul_assoc]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open UpperTheory.V.Z.Tf.GlobalTraceComparison in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.ExHecke2 := by
  intro E _ _ _ a b w e
  exact UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.isHecke_fn (K2 a b w)
    ((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2) _
    (fun p => UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.isHecke_pair _ _ (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.isHecke_Tj a w _ _)
      (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.isHecke_Tj b w _ _)) e

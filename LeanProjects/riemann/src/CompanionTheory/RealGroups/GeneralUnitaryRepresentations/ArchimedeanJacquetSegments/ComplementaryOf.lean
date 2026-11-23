import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Complementary
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermApply

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace CompanionTheory.RgGu.NR

namespace Compl

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem irr_sub {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) (W : Submodule ℂ V)
    (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) : W = ⊥ ∨ W = ⊤ :=
  (eq_bot_or_eq_top (⟨W, hW⟩ : Subrepresentation ρ)).imp (congrArg Subrepresentation.toSubmodule)
    (congrArg Subrepresentation.toSubmodule)

theorem irr_nontrivial {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
  exact bot_ne_top this

def starF {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ) :
    M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => starRingEnd ℂ (B w v))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)

@[simp] theorem starF_apply {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ)
    (v w : M) : starF B v w = starRingEnd ℂ (B w v) := rfl

def resF {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ) (W : Submodule ℂ M) :
    W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => B v w)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)

@[simp] theorem resF_apply {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ)
    (W : Submodule ℂ M) (v w : W) : resF B W v w = B v w := rfl

theorem exists_herm {ρ : Representation ℂ G V} (h : HasSesq ρ) :
    ∃ B : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ, B ≠ 0 ∧ (∀ v w, B w v = starRingEnd ℂ (B v w)) ∧
      ∀ g v w, B (ρ g v) (ρ g w) = B v w :=
  _root_.UpperTheory.Reformulated.B.Yoa6.main h

def stabG (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem nondeg {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ) (hC0 : C ≠ 0)
    (hCi : ∀ g v w, C (ρ g v) (ρ g w) = C v w) (v : V) (hv : v ≠ 0) : ∃ x, C v x ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  let R : Submodule ℂ V :=
    { carrier := {v | ∀ x, C v x = 0}
      add_mem' := fun {a b} ha hb x => by simp [ha x, hb x]
      zero_mem' := fun x => by simp
      smul_mem' := fun c a ha x => by simp [ha x] }
  have hR : ∀ g, ∀ y ∈ R, ρ g y ∈ R := by
    intro g y hy x
    have := hCi g y (ρ g⁻¹ x)
    rw [← Module.End.mul_apply (ρ g), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    rw [this]; exact hy _
  rcases irr_sub hi R hR with h1 | h1
  · have : v ∈ R := hcon
    rw [h1, Submodule.mem_bot] at this
    exact hv this
  · apply hC0
    ext a b
    have : a ∈ R := h1 ▸ Submodule.mem_top
    simpa using this b

end Compl

open _root_.CompanionTheory.RgGu.NR.Compl in
theorem complementary_of (h : Signature) : Complementary := by
  intro G V _ _ _ _ _ K₀ hK₀o hK₀c F hF hall h0 s hs
  have hsm : IsSmooth (F 0) := (hall 0 le_rfl).2.1
  have hirr : (F s).IsIrreducible := (hall s hs).2.2.1
  haveI := irr_nontrivial hirr
  obtain ⟨H, hH0, hHh, hHi⟩ := exists_herm (hall s hs).2.2.2
  obtain ⟨B₀, hB₀h, hB₀p, hB₀i⟩ := h0
  have key : ∀ K : Subgroup G, IsOpen (K : Set G) → K ≤ K₀ → fixed (F 0) K ≠ ⊥ →
      (∀ w ∈ fixed (F 0) K, w ≠ 0 → 0 < (H w w).re) ∨ (∀ w ∈ fixed (F 0) K, w ≠ 0 → (H w w).re < 0) := by
    intro K hKo hKle hW
    have hKc : IsCompact (K : Set G) := hK₀c.of_isClosed_subset (Subgroup.isClosed_of_isOpen K hKo) hKle
    set W := fixed (F 0) K with hWdef
    haveI : FiniteDimensional ℂ W := (hall 0 le_rfl).1.2 K hKo hKc
    set e := idem hsm hKc with he
    have hconst : ∀ t, ∀ x ∈ K, F t x = F 0 x := fun t x hx => hF.const t x (hKle hx)
    have hker : ∀ t (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ), (∀ g v w, C (F t g v) (F t g w) = C v w) →
        ∀ y ∈ twKer (F 0) K 1, ∀ w ∈ W, C y w = 0 ∧ C w y = 0 := by
      intro t C hC y hy w hw
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨n, u, rfl⟩ := hx
        have hn : (F 0) (n : G) w = w := GlobalTheory.Parabolic.mem_fixed.1 hw _ n.2
        have hn' : F t (n : G) = F 0 (n : G) := hconst t _ n.2
        simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, LinearMap.sub_apply]
        constructor
        · rw [← hn, ← hn', hC, hn', hn, sub_self]
        · rw [← hn, ← hn', hC, hn', hn, sub_self]
      | zero => simp
      | add x y _ _ hx hy => simp [hx.1, hy.1, hx.2, hy.2]
      | smul c x _ hx => simp [hx.1, hx.2]
    have hsub : ∀ x : V, x - e x ∈ twKer (F 0) K 1 := fun x => by
      rw [← idem_eq_zero_iff hsm hKc, map_sub, idem_of_mem hsm hKc (idem_mem hsm hKc x), sub_self]
    have hleft : ∀ t (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ), (∀ g v w, C (F t g v) (F t g w) = C v w) →
        ∀ x, ∀ w ∈ W, C (e x) w = C x w ∧ C w (e x) = C w x := by
      intro t C hC x w hw
      obtain ⟨h1, h2⟩ := hker t C hC _ (hsub x) w hw
      rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h1
      rw [map_sub, sub_eq_zero] at h2
      exact ⟨h1.symm, h2.symm⟩
    let T : ℝ → G → Module.End ℂ W := fun t g =>
      (e ∘ₗ (F t g) ∘ₗ W.subtype).codRestrict W (fun v => idem_mem hsm hKc _)
    have hT : ∀ t g (v : W), ((T t g v : W) : V) = e (F t g v) := fun _ _ _ => rfl
    have hinvW : ∀ t (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ), (∀ g v w, C (F t g v) (F t g w) = C v w) →
        ∀ (g : G) (v w : W), resF C W (T t g v) w = resF C W v (T t g⁻¹ w) := by
      intro t C hC g v w
      simp only [resF_apply, hT]
      rw [(hleft t C hC _ w w.2).1, (hleft t C hC _ v v.2).2]
      conv_lhs => rw [← hC g⁻¹]
      rw [← Module.End.mul_apply (F t g⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have hcont : ∀ (g : G) (w : W) (l : Module.Dual ℂ W), Continuous fun t => l (T t g w) := by
      intro g w l
      obtain ⟨m, r, u, hu⟩ := hF.expo g w
      have e1 : ∀ t, T t g w = ∑ i, ((Real.exp (r i * t) : ℝ) : ℂ) • (⟨e (u i), idem_mem hsm hKc _⟩ : W) := by
        intro t
        apply Subtype.ext
        rw [hT, hu t, map_sum, Submodule.coe_sum]
        simp only [map_smul, Submodule.coe_smul]
      simp_rw [e1, map_sum, map_smul, smul_eq_mul]
      refine continuous_finset_sum _ fun i _ => Continuous.mul ?_ continuous_const
      exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hsimple : ∀ t, 0 ≤ t → ∀ U : Submodule ℂ W, (∀ g, ∀ w ∈ U, T t g w ∈ U) → U = ⊥ ∨ U = ⊤ := by
      intro t ht U hU
      by_cases hU0 : U = ⊥
      · exact Or.inl hU0
      right
      obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      let S : Submodule ℂ V := Submodule.span ℂ (Set.range fun g => F t g u)
      have hS : ∀ g, ∀ x ∈ S, F t g x ∈ S := by
        intro g x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨g', rfl⟩ := hy
          exact Submodule.subset_span ⟨g * g', by simp only [map_mul, Module.End.mul_apply]⟩
        | zero => simp
        | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
        | smul c x _ hx => rw [map_smul]; exact S.smul_mem c hx
      have hSt : S = ⊤ := by
        rcases irr_sub (hall t ht).2.2.1 S hS with h1 | h1
        · exfalso
          apply hu0
          apply Subtype.ext
          have : ((u : W) : V) ∈ S := Submodule.subset_span ⟨1, by simp⟩
          rw [h1, Submodule.mem_bot] at this
          simpa using this
        · exact h1
      have hmem : ∀ x ∈ S, (⟨e x, idem_mem hsm hKc x⟩ : W) ∈ U := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨g, rfl⟩ := hy
          exact hU g u huU
        | zero =>
          convert U.zero_mem using 1
          exact Subtype.ext (by simp)
        | add x y _ _ hx hy =>
          have : (⟨e (x + y), idem_mem hsm hKc _⟩ : W) = ⟨e x, idem_mem hsm hKc _⟩ + ⟨e y, idem_mem hsm hKc _⟩ :=
            Subtype.ext (by simp)
          rw [this]; exact U.add_mem hx hy
        | smul c x _ hx =>
          have : (⟨e (c • x), idem_mem hsm hKc _⟩ : W) = c • ⟨e x, idem_mem hsm hKc _⟩ := Subtype.ext (by simp)
          rw [this]; exact U.smul_mem c hx
      refine eq_top_iff.2 fun w _ => ?_
      have hw : (⟨e w, idem_mem hsm hKc _⟩ : W) = w := Subtype.ext (idem_of_mem hsm hKc w.2)
      rw [← hw]
      exact hmem w (hSt ▸ Submodule.mem_top)
    haveI : Nontrivial W := (Submodule.nontrivial_iff_ne_bot).2 hW
    have hresne : ∀ t (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ), (∀ g v w, C (F t g v) (F t g w) = C v w) →
        (F t).IsIrreducible → C ≠ 0 → resF C W ≠ 0 := by
      intro t C hCi hi hC0 h0'
      obtain ⟨w, hw0⟩ := exists_ne (0 : W)
      obtain ⟨x, hx⟩ := nondeg hi C hC0 hCi w (fun e0 => hw0 (Subtype.ext e0))
      apply hx
      rw [← (hleft t C hCi x w w.2).2]
      have := congrArg (fun f => f w ⟨e x, idem_mem hsm hKc x⟩) h0'
      simpa using this
    have hforms : ∀ t, 0 ≤ t → ∃ C : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ, C ≠ 0 ∧
        (∀ v w, C w v = starRingEnd ℂ (C v w)) ∧ ∀ g v w, C (T t g v) w = C v (T t g⁻¹ w) := by
      intro t ht
      obtain ⟨C, hC0, hCh, hCi⟩ := exists_herm (hall t ht).2.2.2
      exact ⟨resF C W, hresne t C hCi (hall t ht).2.2.1 hC0, fun v w => hCh v w, hinvW t C hCi⟩
    have hpos0 : ∃ C : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ, (∀ v w, C w v = starRingEnd ℂ (C v w)) ∧
        (∀ v, v ≠ 0 → 0 < (C v v).re) ∧ ∀ g v w, C (T 0 g v) w = C v (T 0 g⁻¹ w) :=
      ⟨resF B₀ W, fun v w => hB₀h v w, fun v hv => hB₀p v (fun e0 => hv (Subtype.ext e0)), hinvW 0 B₀ hB₀i⟩
    rcases h G W (fun g => g⁻¹) T (fun i w l => hcont i w l) hsimple hforms hpos0 inv_surjective s hs (resF H W)
        (hresne s H hHi hirr hH0) (fun v w => hHh v w) (hinvW s H hHi) with h1 | h1
    · exact Or.inl fun w hw hw0 => h1 ⟨w, hw⟩ (fun e0 => hw0 (congrArg Subtype.val e0))
    · exact Or.inr fun w hw hw0 => h1 ⟨w, hw⟩ (fun e0 => hw0 (congrArg Subtype.val e0))
  obtain ⟨v₁, hv₁⟩ := exists_ne (0 : V)
  have hopen : ∀ v : V, IsOpen ((stabG (F 0) v : Subgroup G) : Set G) := fun v => hsm v
  let K₁ : Subgroup G := K₀ ⊓ stabG (F 0) v₁
  have hK₁o : IsOpen (K₁ : Set G) := hK₀o.inter (hopen v₁)
  have hv₁K : ∀ K : Subgroup G, K ≤ K₁ → v₁ ∈ fixed (F 0) K :=
    fun K hK => GlobalTheory.Parabolic.mem_fixed.2 fun g hg => (hK hg).2
  have hne : ∀ K : Subgroup G, K ≤ K₁ → fixed (F 0) K ≠ ⊥ := fun K hK h' => by
    have := hv₁K K hK
    rw [h', Submodule.mem_bot] at this
    exact hv₁ this
  have hloc : ∀ v : V, v ≠ 0 → ((0 < (H v₁ v₁).re → 0 < (H v v).re) ∧ ((H v₁ v₁).re < 0 → (H v v).re < 0)) := by
    intro v hv
    let Kv : Subgroup G := K₁ ⊓ stabG (F 0) v
    have hKvo : IsOpen (Kv : Set G) := hK₁o.inter (hopen v)
    have hvK : v ∈ fixed (F 0) Kv := GlobalTheory.Parabolic.mem_fixed.2 fun g hg => hg.2
    rcases key Kv hKvo (inf_le_left.trans inf_le_left) (hne Kv inf_le_left) with h1 | h1
    · have a := h1 v hvK hv
      have b := h1 v₁ (hv₁K Kv inf_le_left) hv₁
      exact ⟨fun _ => a, fun hb => absurd b (not_lt.2 hb.le)⟩
    · have a := h1 v hvK hv
      have b := h1 v₁ (hv₁K Kv inf_le_left) hv₁
      exact ⟨fun hb => absurd b (not_lt.2 hb.le), fun _ => a⟩
  rcases key K₁ hK₁o inf_le_left (hne K₁ le_rfl) with h1 | h1
  · have hp := h1 v₁ (hv₁K K₁ le_rfl) hv₁
    exact ⟨H, fun v w => hHh v w, fun v hv => (hloc v hv).1 hp, hHi⟩
  · have hn := h1 v₁ (hv₁K K₁ le_rfl) hv₁
    refine ⟨-H, fun v w => ?_, fun v hv => ?_, fun g v w => ?_⟩
    · simp [hHh v w]
    · have := (hloc v hv).2 hn
      simp only [LinearMap.neg_apply, Complex.neg_re]
      linarith
    · simp [hHi]

end CompanionTheory.RgGu.NR

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.CompletionTower

open AdicCompletion

variable {B : Type} [CommRing B] (I : Ideal B) {N : Type} [AddCommGroup N] [Module B N]

theorem exists_eval_smul (r : AdicCompletion I B) (x : AdicCompletion I N) (n : ℕ) :
    ∃ b : B, eval I N n (r • x) = b • eval I N n x := by
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (r.val n)
  exact ⟨b, by show (r • x).val n = b • x.val n; rw [smul_eval, ← hb]; rfl⟩

theorem finite_adicCompletion [Module.Finite B N] :
    Module.Finite (AdicCompletion I B) (AdicCompletion I N) :=
  Module.Finite.of_surjective (ofTensorProduct I N) (ofTensorProduct_surjective_of_finite I N)

theorem span_range_of [Module.Finite B N] :
    Submodule.span (AdicCompletion I B) (Set.range (of I N)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  obtain ⟨t, rfl⟩ := ofTensorProduct_surjective_of_finite I N x
  induction t with
  | zero => simp
  | tmul a e =>
    rw [ofTensorProduct_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

variable {I} (T : ℕ → Submodule B N) (hT : ∀ n, I ^ (n + 1) • (⊤ : Submodule B N) ≤ T n)

noncomputable def toQuot (n : ℕ) : AdicCompletion I N →ₗ[B] N ⧸ T n :=
  Submodule.factor (hT n) ∘ₗ eval I N (n + 1)

theorem toQuot_of (n : ℕ) (e : N) : toQuot T hT n (of I N e) = (T n).mkQ e := by
  simp [toQuot, eval_of, Submodule.factor_mk]

theorem toQuot_mk (n : ℕ) (f : AdicCauchySequence I N) :
    toQuot T hT n (AdicCompletion.mk I N f) = (T n).mkQ (f (n + 1)) := by
  show Submodule.factor (hT n) ((AdicCompletion.mk I N f).val (n + 1)) = _
  rw [mk_apply_coe, Submodule.factor_mk]

noncomputable def Tb (n : ℕ) : Submodule (AdicCompletion I B) (AdicCompletion I N) where
  carrier := {x | toQuot T hT n x = 0}
  add_mem' {x y} hx hy := by simp_all
  zero_mem' := by simp
  smul_mem' r x hx := by
    obtain ⟨b, hb⟩ := exists_eval_smul I r x (n + 1)
    have : toQuot T hT n (r • x) = b • toQuot T hT n x := by
      simp only [toQuot, LinearMap.comp_apply, hb, map_smul]
    simp_all

theorem mem_Tb (n : ℕ) (x : AdicCompletion I N) : x ∈ Tb T hT n ↔ toQuot T hT n x = 0 := Iff.rfl

theorem antitone_of_eq_sup_pow_smul_whole_module (hT' : ∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) : Antitone T :=
  antitone_nat_of_succ_le fun n ↦ (hT' n).symm ▸ le_sup_left

theorem exists_lift (hT' : ∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) (n : ℕ) (e : N)
    (he : e ∈ T n) : ∃ l ∈ ⨅ m, Tb T hT m, eval I N (n + 1) l = eval I N (n + 1) (of I N e) := by
  have step : ∀ j (x : T (n + j)), ∃ y : T (n + j + 1),
      (x : N) - y ∈ I ^ (n + j + 1) • (⊤ : Submodule B N) := by
    intro j x
    have hx : (x : N) ∈ T (n + j + 1) ⊔ I ^ (n + j + 1) • (⊤ : Submodule B N) := by
      rw [← hT']; exact x.2
    obtain ⟨a, ha, c, hc, hxe⟩ := Submodule.mem_sup.1 hx
    exact ⟨⟨a, ha⟩, by rw [← hxe]; simpa using hc⟩
  choose f hf using step
  let u : (j : ℕ) → T (n + j) := fun j ↦ Nat.rec ⟨e, he⟩ (fun j x ↦ f j x) j
  have huj : ∀ j, (u (j + 1)).1 = (f j (u j)).1 := fun j ↦ rfl
  have hu : ∀ j, ((u j).1 - (u (j + 1)).1) ∈ I ^ (n + j + 1) • (⊤ : Submodule B N) := fun j ↦ by
    rw [huj]; exact hf j (u j)
  let s : ℕ → N := fun k ↦ (u (k - (n + 1))).1
  have huc : ∀ a b, a = b → (u a).1 = (u b).1 := by rintro a b rfl; rfl
  have hs0 : ∀ k, k ≤ n + 1 → s k = e := fun k hk ↦ huc _ 0 (Nat.sub_eq_zero_of_le hk)
  have hs1 : ∀ j, s (n + 1 + j) = (u j).1 := fun j ↦ huc _ _ (by omega)
  have hcau : ∀ k, s k ≡ s (k + 1) [SMOD (I ^ k • ⊤ : Submodule B N)] := by
    intro k
    rw [SModEq.sub_mem]
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · rw [hs0 k hk.le, hs0 (k + 1) hk, sub_self]; exact zero_mem _
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [hs1, show n + 1 + j + 1 = n + 1 + (j + 1) by omega, hs1]
      simpa [show n + 1 + j = n + j + 1 by omega] using hu j
  let F : AdicCauchySequence I N := AdicCauchySequence.mk I N s hcau
  have hF : ∀ k, F k = s k := fun k ↦ rfl
  refine ⟨AdicCompletion.mk I N F, Submodule.mem_iInf _ |>.2 fun m ↦ ?_, ?_⟩
  · rw [mem_Tb, toQuot_mk, hF, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rcases Nat.lt_or_ge m n with hm | hm
    · rw [hs0 _ (by omega)]; exact antitone_of_eq_sup_pow_smul_whole_module T hT' hm.le he
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
      rw [show n + j + 1 = n + 1 + j by omega, hs1]; exact (u j).2
  · show (AdicCompletion.mk I N F).val (n + 1) = _
    rw [mk_apply_coe, eval_of, hF, hs0 _ le_rfl]

end GlobalTheory.CompanionTheory.GE.CompletionTower

namespace GlobalTheory.CompanionTheory.GE.CompletionTower

open AdicCompletion

theorem exists_completion_tower : ∀ {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {N : Type} [AddCommGroup N] [Module B N] [Module.Finite B N] (T : ℕ → Submodule B N),
    (∀ n, I ^ (n + 1) • (⊤ : Submodule B N) ≤ T n) →
    (∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) →
    ∃ (R : Type) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : Algebra B R) (M : Type)
      (_ : AddCommGroup M) (_ : Module R M) (_ : Module B M) (_ : IsScalarTower B R M)
      (_ : Module.Finite R M) (μ : N →ₗ[B] M), I.map (algebraMap B R) ≤ Ideal.jacobson ⊥ ∧
      Submodule.span R (Set.range μ) = ⊤ ∧
      ∀ n e, e ∈ T n ↔ μ e ∈ (I ^ (n + 1) • ⊤ : Submodule B M) := by
  intro B _ _ I N _ _ _ T hT hT'
  haveI := finite_adicCompletion I (N := N)
  haveI := AdicCompletion.isAdicComplete_self I I.fg_of_isNoetherianRing
  let L : Submodule (AdicCompletion I B) (AdicCompletion I N) := ⨅ m, Tb T hT m
  let μ : N →ₗ[B] AdicCompletion I N ⧸ L := (L.mkQ.restrictScalars B) ∘ₗ of I N
  refine ⟨AdicCompletion I B, inferInstance, GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion B I,
    inferInstance, AdicCompletion I N ⧸ L, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, μ, IsAdicComplete.le_jacobson_bot _, ?_, ?_⟩
  · have : Set.range μ = L.mkQ '' Set.range (of I N) := by
      ext y; simp [μ]
    rw [this, ← Submodule.map_span, span_range_of, Submodule.map_top, Submodule.range_mkQ]
  · intro n e
    constructor
    · intro he
      obtain ⟨l, hl, hle⟩ := exists_lift T hT hT' n e he
      have hmem : of I N e - l ∈ (I ^ (n + 1) • ⊤ : Submodule B (AdicCompletion I N)) := by
        rw [AdicCompletion.pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing, LinearMap.mem_ker,
          map_sub, hle, sub_self]
      have hl0 : L.mkQ l = 0 := (Submodule.Quotient.mk_eq_zero L).2 hl
      have hμ : μ e = (L.mkQ.restrictScalars B) (of I N e - l) := by
        simp only [μ, LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_sub, hl0, sub_zero]
      have h2 := Submodule.mem_map_of_mem (f := L.mkQ.restrictScalars B) hmem
      rw [Submodule.map_smul''] at h2
      rw [hμ]
      exact Submodule.smul_mono le_rfl le_top h2
    · intro hμ
      have key : (I ^ (n + 1) • ⊤ : Submodule B (AdicCompletion I N ⧸ L)) ≤
          (LinearMap.ker (toQuot T hT n)).map (L.mkQ.restrictScalars B) := by
        rw [Submodule.smul_le]
        intro i hi m _
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective L m
        refine ⟨i • x, ?_, by simp⟩
        show toQuot T hT n (i • x) = 0
        rw [map_smul]
        obtain ⟨y, hy⟩ := Submodule.mkQ_surjective (T n) (toQuot T hT n x)
        rw [← hy, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hT n (Submodule.smul_mem_smul hi Submodule.mem_top)
      obtain ⟨x, hx, hxe⟩ := key hμ
      have hd : x - of I N e ∈ L := (Submodule.Quotient.eq L).1 hxe
      have hd' := (Submodule.mem_iInf _).1 hd n
      rw [mem_Tb, map_sub, LinearMap.mem_ker.1 hx, zero_sub, neg_eq_zero, toQuot_of,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hd'
      exact hd'

end GlobalTheory.CompanionTheory.GE.CompletionTower

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubRepApply
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrreducibleConstituentRanksUniqueOfCharpoly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsSemisimplificationOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfSemisimplification
open Polynomial

noncomputable section

namespace GlobalTheory.CharFlag

variable {k Γ V : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V]

theorem HasCharFlag.perm {π : Representation k Γ V} {t : ℕ} (ψ : Fin t → Γ →* kˣ) (e : Fin t ≃ Fin t)
    (h : HasCharFlag π (ψ ∘ e)) : HasCharFlag π ψ := by
  obtain ⟨R, W, rs, h0, h1, hm, hst, hinj, hstep⟩ := h
  refine ⟨R, W, rs ∘ e.symm, h0, h1, hm, hst, hinj.comp e.symm.injective, fun s => ?_⟩
  have := hstep (e.symm s)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at this ⊢
  exact this

theorem hasCharFlag_zero (π : Representation k Γ V) (ψ : Fin 0 → Γ →* kˣ) : HasCharFlag π ψ := by
  refine ⟨1, fun j => if (j : ℕ) = 0 then ⊥ else ⊤, Fin.elim0, by simp, by simp, ?_, ?_,
    fun a => a.elim0, fun s => s.elim0⟩
  · intro i j hij
    by_cases hi : (i : ℕ) = 0
    · simp [hi]
    · have hj : (j : ℕ) ≠ 0 := fun h => hi (by have : (i : ℕ) ≤ j := hij; omega)
      simp [hi, hj]
  · intro g j x hx
    by_cases hj : (j : ℕ) = 0
    · simp only [hj, if_true, Submodule.mem_bot] at hx ⊢; simp [hx]
    · simp [hj]

theorem stab_span (π : Representation k Γ V) (x : V) (c : Γ → k) (hx : ∀ g, π g x = c g • x) :
    Stab π (Submodule.span k {x}) := by
  intro g y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rw [map_smul, hx]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x))

theorem charpoly_line (π : Representation k Γ V) (x : V) (hx : x ≠ 0) (c : k) (g : Γ) (hxg : π g x = c • x)
    (hS : Stab π (Submodule.span k {x})) : LinearMap.charpoly (subRep π _ hS g) = X - C c := by
  have hf : subRep π _ hS g = c • LinearMap.id := by
    ext ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
    simp [subRep_apply, map_smul, hxg, smul_comm c a]
  have hd : Module.finrank k (Submodule.span k {x}) = 1 := finrank_span_singleton hx
  let b : Module.Basis (Fin 1) k (Submodule.span k {x}) := Module.finBasisOfFinrankEq k _ hd
  rw [← LinearMap.charpoly_toMatrix _ b, hf, Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]
  simp

theorem charpoly_split [FiniteDimensional k V] (π : Representation k Γ V) (S : Submodule k V) (hS : Stab π S)
    (g : Γ) : LinearMap.charpoly (π g) =
      LinearMap.charpoly (subRep π S hS g) * LinearMap.charpoly (quotRep π S hS g) :=
  GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ S (π g) (hS g)

theorem lift_core (π : Representation k Γ V) (S : Submodule k V) (hS : Stab π S) {t : ℕ} (ψ : Fin t → Γ →* kˣ)
    (h : HasCharFlag (quotRep π S hS) ψ) :
    ∃ (R : ℕ) (W : Fin (R + 1 + 1) → Submodule k V) (rs : Fin t → Fin R), W 0 = ⊥ ∧ W (Fin.succ 0) = S ∧
      W (Fin.last (R + 1)) = ⊤ ∧ Monotone W ∧ (∀ g j x, x ∈ W j → π g x ∈ W j) ∧ Function.Injective rs ∧
      ∀ s, ∃ x ∈ W (rs s).succ.succ, x ∉ W (rs s).succ.castSucc ∧
        W (rs s).succ.succ = W (rs s).succ.castSucc ⊔ Submodule.span k {x} ∧
        ∀ g, π g x - ((ψ s g : kˣ) : k) • x ∈ W (rs s).succ.castSucc := by
  obtain ⟨R, W, rs, h0, h1, hm, hst, hinj, hstep⟩ := h
  refine ⟨R, Fin.cons ⊥ fun j => (W j).comap S.mkQ, rs, rfl, ?_, ?_, ?_, ?_, hinj, fun s => ?_⟩
  · rw [Fin.cons_succ, h0, Submodule.comap_bot, Submodule.ker_mkQ]
  · rw [← Fin.succ_last, Fin.cons_succ, h1, Submodule.comap_top]
  · intro i j hij
    induction i using Fin.cases with
    | zero => exact bot_le
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd hij (not_le.2 (Fin.succ_pos i))
      | succ j => exact Submodule.comap_mono (hm (Fin.succ_le_succ_iff.1 hij))
  · intro g j x hx
    induction j using Fin.cases with
    | zero =>
      have hx0 : x = 0 := hx
      rw [hx0, map_zero]
      exact Submodule.zero_mem _
    | succ j => exact hst g j (S.mkQ x) hx
  · obtain ⟨y, hy1, hy2, hy3, hy4⟩ := hstep s
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
    refine ⟨x, hy1, hy2, le_antisymm (fun z hz => ?_) (sup_le (Submodule.comap_mono
      (hm (Fin.castSucc_lt_succ).le)) ((Submodule.span_singleton_le_iff_mem _ _).2 hy1)), fun g => ?_⟩
    · rw [Submodule.mem_comap, hy3] at hz
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
      refine Submodule.mem_sup.2 ⟨z - c • x, ?_, c • x,
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x), sub_add_cancel _ _⟩
      rw [Submodule.mem_comap, map_sub, map_smul, ← hab, add_sub_cancel_right]
      exact ha
    · rw [Submodule.mem_comap, map_sub, map_smul]
      exact hy4 g

theorem lift_quot (π : Representation k Γ V) (S : Submodule k V) (hS : Stab π S) {t : ℕ} (ψ : Fin t → Γ →* kˣ)
    (h : HasCharFlag (quotRep π S hS) ψ) : HasCharFlag π ψ := by
  obtain ⟨R, W, rs, h0, -, h1, hm, hst, hinj, hstep⟩ := lift_core π S hS ψ h
  exact ⟨R + 1, W, fun s => (rs s).succ, h0, h1, hm, hst, (Fin.succ_injective _).comp hinj, hstep⟩

theorem lift_line (π : Representation k Γ V) (x : V) (ψ₀ : Γ →* kˣ) (hx0 : x ≠ 0)
    (hx : ∀ g, π g x = ((ψ₀ g : kˣ) : k) • x) (hS : Stab π (Submodule.span k {x})) {t : ℕ}
    (ψ : Fin t → Γ →* kˣ) (h : HasCharFlag (quotRep π _ hS) ψ) :
    HasCharFlag π (Fin.cons ψ₀ ψ : Fin (t + 1) → Γ →* kˣ) := by
  obtain ⟨R, W, rs, h0, hS1, h1, hm, hst, hinj, hstep⟩ := lift_core π _ hS ψ h
  refine ⟨R + 1, W, Fin.cons 0 fun s => (rs s).succ, h0, h1, hm, hst, ?_, fun s => ?_⟩
  · rw [Fin.cons_injective_iff]
    refine ⟨?_, (Fin.succ_injective _).comp hinj⟩
    rintro ⟨s, hs⟩
    exact Fin.succ_ne_zero _ hs
  · induction s using Fin.cases with
    | zero =>
      rw [Fin.cons_zero, Fin.cons_zero, Fin.castSucc_zero, h0, hS1]
      exact ⟨x, Submodule.mem_span_singleton_self x, hx0, (bot_sup_eq _).symm,
        fun g => by rw [hx, sub_self]; exact Submodule.zero_mem _⟩
    | succ s => exact hstep s

theorem ss_of_compl (σ : Representation k Γ V)
    (h : ∀ W, Stab σ W → ∃ W', Stab σ W' ∧ IsCompl W W') :
    IsSemisimpleModule (MonoidAlgebra k Γ) σ.asModule := by
  rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine ⟨fun P => ?_⟩
  obtain ⟨W', h1, h2⟩ := h P.toSubmodule fun g v hv => P.apply_mem_toSubmodule g hv
  refine ⟨⟨W', fun g v hv => h1 g v hv⟩, ?_⟩
  rw [isCompl_iff, disjoint_iff, codisjoint_iff,
    ← Subrepresentation.toSubmodule_injective.eq_iff, ← Subrepresentation.toSubmodule_injective.eq_iff]
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at h2
  exact h2

theorem ss_of_min (σ : Representation k Γ V) (h : ∀ W, Stab σ W → W = ⊥ ∨ W = ⊤) :
    IsSemisimpleModule (MonoidAlgebra k Γ) σ.asModule := by
  refine ss_of_compl σ fun W hW => ?_
  rcases h W hW with rfl | rfl
  · exact ⟨⊤, fun _ _ _ => trivial, isCompl_bot_top⟩
  · exact ⟨⊥, fun g x hx => by rw [(Submodule.mem_bot k).1 hx, map_zero]; exact Submodule.zero_mem _,
      isCompl_top_bot⟩

theorem ss_prod' {U : Type} [AddCommGroup U] [Module k U] (σ : Representation k Γ V) (τ : Representation k Γ U)
    (hσ : IsSemisimpleModule (MonoidAlgebra k Γ) σ.asModule)
    (hτ : IsSemisimpleModule (MonoidAlgebra k Γ) τ.asModule) :
    IsSemisimpleModule (MonoidAlgebra k Γ) (σ.prod τ).asModule := by
  have := GlobalTheory.SSRank.ss_prod (R := MonoidAlgebra k Γ) (M := σ.asModule) (N := τ.asModule)
  exact IsSemisimpleModule.congr (GlobalTheory.SSRank.prodEquiv σ τ)

theorem exists_ss [FiniteDimensional k V] (π : Representation k Γ V) :
    ∃ σ : Representation k Γ V, IsSemisimpleModule (MonoidAlgebra k Γ) σ.asModule ∧
      ∀ g, LinearMap.charpoly (σ g) = LinearMap.charpoly (π g) := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.Proof.exists_semisimplification'.exists_isSemisimplificationOf π
  exact ⟨σ, ss_of_compl σ fun W hW => hσ.1 W hW, GlobalTheory.SemisimplificationCharpoly.charpoly_eq σ π hσ⟩

def charRep (χ : Γ →* kˣ) : Representation k Γ k where
  toFun g := ((χ g : kˣ) : k) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_comm]

theorem charpoly_charRep (χ : Γ →* kˣ) (g : Γ) :
    LinearMap.charpoly (charRep χ g) = X - C ((χ g : kˣ) : k) := by
  rw [← LinearMap.charpoly_toMatrix _ (Module.Basis.singleton (Fin 1) k), Matrix.charpoly, Matrix.det_fin_one,
    Matrix.charmatrix_apply_eq]
  simp [charRep, Module.Basis.toMatrix_apply]

theorem exists_sum_chars : ∀ (t : ℕ) (ψ : Fin t → Γ →* kˣ),
    ∃ (B : Type) (_ : AddCommGroup B) (_ : Module k B) (_ : FiniteDimensional k B) (δ : Representation k Γ B),
      IsSemisimpleModule (MonoidAlgebra k Γ) δ.asModule ∧
      (∀ g, LinearMap.charpoly (δ g) = ∏ s, (X - C ((ψ s g : kˣ) : k))) ∧
      ∀ (σ : Representation k Γ V) (f : V →ₗ[k] B), (∀ g x, f (σ g x) = δ g (f x)) →
        (∀ s (φ : V →ₗ[k] k), (∀ g x, φ (σ g x) = ((ψ s g : kˣ) : k) • φ x) → φ = 0) → f = 0
  | 0, ψ => ⟨Fin 0 → k, inferInstance, inferInstance, inferInstance, 1,
      ss_of_min _ fun W _ => Or.inl (Subsingleton.elim _ _),
      fun g => by rw [GlobalTheory.SSRank.charpoly_fin_zero]; simp,
      fun _ _ _ _ => LinearMap.ext fun _ => Subsingleton.elim _ _⟩
  | t + 1, ψ => by
    obtain ⟨B, _, _, _, δ, h1, h2, h3⟩ := exists_sum_chars t fun s => ψ s.succ
    refine ⟨k × B, inferInstance, inferInstance, inferInstance, (charRep (ψ 0)).prod δ,
      ss_prod' _ _ (ss_of_min _ fun W _ => eq_bot_or_eq_top W) h1, fun g => ?_, fun σ f hf hφ => ?_⟩
    · rw [Fin.prod_univ_succ, ← h2, ← charpoly_charRep, ← LinearMap.charpoly_prodMap]
      rfl
    · have e1 := hφ 0 (LinearMap.fst k k B ∘ₗ f) fun g x => congrArg Prod.fst (hf g x)
      have e2 := h3 σ (LinearMap.snd k k B ∘ₗ f) (fun g x => congrArg Prod.snd (hf g x)) fun s => hφ s.succ
      exact LinearMap.ext fun x => Prod.ext (LinearMap.congr_fun e1 x) (LinearMap.congr_fun e2 x)

theorem bn_step [FiniteDimensional k V] {A : Type} [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    (π : Representation k Γ V) (α : Representation k Γ A) {t : ℕ} (ψ : Fin t → Γ →* kˣ) (S : Submodule k V)
    (hS : Stab π S) (hS0 : S ≠ ⊥) (hmin : ∀ S' : Submodule k V, S' ≤ S → Stab π S' → S' = ⊥ ∨ S' = S)
    (hno : ∀ s, ∀ x ∈ S, (∀ g, π g x = ((ψ s g : kˣ) : k) • x) → x = 0)
    (h : ∀ g, LinearMap.charpoly (π g) = LinearMap.charpoly (α g) * ∏ s, (X - C ((ψ s g : kˣ) : k))) :
    ∃ (B : Type) (_ : AddCommGroup B) (_ : Module k B) (_ : FiniteDimensional k B) (β : Representation k Γ B),
      ∀ g, LinearMap.charpoly (α g) = LinearMap.charpoly (subRep π S hS g) * LinearMap.charpoly (β g) := by
  have hsimple : ∀ W : Submodule k S, Stab (subRep π S hS) W → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hinj := Submodule.map_injective_of_injective S.subtype_injective
    rcases hmin (W.map S.subtype) (Submodule.map_subtype_le S W) (by
      rintro g _ ⟨x, hx, rfl⟩
      exact ⟨_, hW g x hx, rfl⟩) with h0 | h0
    · exact Or.inl (hinj (by rw [h0, Submodule.map_bot]))
    · exact Or.inr (hinj (by rw [h0, Submodule.map_top, Submodule.range_subtype]))
  obtain ⟨sQ, hQ1, hQ2⟩ := exists_ss (quotRep π S hS)
  obtain ⟨sA, hA1, hA2⟩ := exists_ss α
  obtain ⟨B, _, _, _, δ, hδ1, hδ2, hδ3⟩ := exists_sum_chars (V := S) t ψ
  obtain ⟨e, he⟩ := GlobalTheory.SSRank.bn_gen ((subRep π S hS).prod sQ) (sA.prod δ)
    (ss_prod' _ _ (ss_of_min _ hsimple) hQ1) (ss_prod' _ _ hA1 hδ1) fun g => by
      change LinearMap.charpoly ((subRep π S hS g).prodMap (sQ g)) = LinearMap.charpoly ((sA g).prodMap (δ g))
      rw [LinearMap.charpoly_prodMap, LinearMap.charpoly_prodMap, hQ2, hA2, hδ2, ← h, ← charpoly_split]
  let j : S →ₗ[k] A × B := e.toLinearMap ∘ₗ LinearMap.inl k S (V ⧸ S)
  have hj : ∀ g x, j (subRep π S hS g x) = (sA g (j x).1, δ g (j x).2) := fun g x => by
    have := LinearMap.congr_fun (he g) (x, 0)
    have h0 : ((subRep π S hS).prod sQ) g (x, 0) = (subRep π S hS g x, 0) :=
      Prod.ext rfl (map_zero (sQ g))
    rw [LinearMap.comp_apply, h0] at this
    exact this
  have h2 : LinearMap.snd k A B ∘ₗ j = 0 := by
    refine hδ3 (subRep π S hS) _ (fun g x => congrArg Prod.snd (hj g x)) fun s φ hφ => ?_
    rcases hsimple (LinearMap.ker φ) (fun g x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hφ, hx, smul_zero]) with h0 | h0
    · exfalso
      obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff S).1 hS0
      refine hx0 (hno s x hx fun g => ?_)
      have : subRep π S hS g ⟨x, hx⟩ = ((ψ s g : kˣ) : k) • ⟨x, hx⟩ :=
        LinearMap.ker_eq_bot.1 h0 (by rw [hφ, map_smul])
      exact congrArg Subtype.val this
    · exact LinearMap.ker_eq_top.1 h0
  let f : S →ₗ[k] A := LinearMap.fst k A B ∘ₗ j
  have hf : ∀ g x, f (subRep π S hS g x) = sA g (f x) := fun g x => congrArg Prod.fst (hj g x)
  have hfi : Function.Injective f := fun x y hxy =>
    LinearMap.inl_injective (e.injective (Prod.ext hxy
      ((LinearMap.congr_fun h2 x).trans (LinearMap.congr_fun h2 y).symm)))
  have hR : Stab sA (LinearMap.range f) := by
    rintro g _ ⟨x, rfl⟩
    exact ⟨_, hf g x⟩
  refine ⟨A ⧸ LinearMap.range f, inferInstance, inferInstance, inferInstance, quotRep sA _ hR, fun g => ?_⟩
  rw [← hA2, charpoly_split sA _ hR, ← LinearEquiv.charpoly_conj (LinearEquiv.ofInjective f hfi) (subRep π S hS g)]
  congr 2
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (LinearEquiv.ofInjective f hfi).surjective y
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  exact Subtype.ext (hf g x).symm

theorem main_gen : ∀ (d : ℕ) {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V],
    Module.finrank k V = d → ∀ (π : Representation k Γ V) {t : ℕ} (ψ : Fin t → Γ →* kˣ) {A : Type}
    [AddCommGroup A] [Module k A] [FiniteDimensional k A] (α : Representation k Γ A),
    (∀ g, LinearMap.charpoly (π g) = LinearMap.charpoly (α g) * ∏ s, (X - C ((ψ s g : kˣ) : k))) →
    HasCharFlag π ψ := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V _ _ _ hd π t ψ A _ _ _ α h
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact hasCharFlag_zero π ψ
  have hdeg := congrArg natDegree (h 1)
  rw [LinearMap.charpoly_natDegree, (LinearMap.charpoly_monic _).natDegree_mul
    (monic_prod_of_monic _ _ fun s _ => monic_X_sub_C _), LinearMap.charpoly_natDegree,
    natDegree_prod_of_monic _ _ (fun s _ => monic_X_sub_C _)] at hdeg
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one] at hdeg
  by_cases hev : ∃ s, ∃ x : V, x ≠ 0 ∧ ∀ g, π g x = ((ψ s g : kˣ) : k) • x
  · obtain ⟨s, x, hx0, hx⟩ := hev
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have hS := stab_span π x (fun g => ((ψ s g : kˣ) : k)) hx
    let e : Fin (t' + 1) ≃ Fin (t' + 1) := Equiv.swap 0 s
    refine HasCharFlag.perm ψ e ?_
    rw [← Fin.cons_self_tail (ψ ∘ e)]
    have he0 : (ψ ∘ e) 0 = ψ s := by simp [e]
    rw [he0]
    refine lift_line π x (ψ s) hx0 hx hS _ ?_
    have hfr : Module.finrank k (V ⧸ Submodule.span k {x}) < d := by
      have h1 := Submodule.finrank_quotient_add_finrank (Submodule.span k {x})
      rw [finrank_span_singleton hx0] at h1
      omega
    refine ih _ hfr rfl _ _ α fun g => ?_
    apply mul_left_cancel₀ (X_sub_C_ne_zero ((ψ s g : kˣ) : k))
    have h1 := charpoly_split π _ hS g
    rw [charpoly_line π x hx0 _ g (hx g) hS] at h1
    rw [← h1, h g,
      ← Equiv.prod_comp e (fun s' => (X - C ((ψ s' g : kˣ) : k))), Fin.prod_univ_succ]
    simp only [Fin.tail, Function.comp_apply]
    have : e 0 = s := by simp [e]
    rw [this]
    ring
  · have hV : (⊥ : Submodule k V) ≠ ⊤ := by
      intro hb
      have : Module.finrank k V = 0 := by
        rw [← finrank_top k V, ← hb, finrank_bot]
      omega
    obtain ⟨S, ⟨hS0, hS⟩, hmin⟩ := (wellFounded_lt (α := Submodule k V)).has_min
      {S | S ≠ ⊥ ∧ Stab π S} ⟨⊤, hV.symm, fun _ _ _ => trivial⟩
    have hmin' : ∀ S' : Submodule k V, S' ≤ S → Stab π S' → S' = ⊥ ∨ S' = S := by
      intro S' hle hst
      by_cases hb : S' = ⊥
      · exact Or.inl hb
      · exact Or.inr (by
          by_contra hne
          exact hmin S' ⟨hb, hst⟩ (lt_of_le_of_ne hle hne))
    obtain ⟨B, _, _, _, β, hβ⟩ := bn_step π α ψ S hS hS0 hmin'
      (fun s x _ hx => by
        by_contra hx0
        exact hev ⟨s, x, hx0, hx⟩) h
    refine lift_quot π S hS ψ ?_
    have hfr : Module.finrank k (V ⧸ S) < d := by
      have h1 := Submodule.finrank_quotient_add_finrank S
      have h2 : 0 < Module.finrank k S := Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 hS0)
      omega
    refine ih _ hfr rfl _ _ β fun g => ?_
    apply mul_left_cancel₀ (LinearMap.charpoly_monic (subRep π S hS g)).ne_zero
    rw [← charpoly_split, h g, hβ g, mul_assoc]

theorem main : ∀ (k Γ : Type) [Field k] [Group Γ] (n a t : ℕ) (r : Γ →* GL (Fin n) k) (ρ : Γ →* GL (Fin a) k) (ψ : Fin t → Γ →* kˣ), a + t = n → (∀ g, (r g : Matrix (Fin n) (Fin n) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly * ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : kˣ) : k))) → ∃ (R : ℕ) (V : Fin (R + 1) → Submodule k (Fin n → k)) (rs : Fin t → Fin R), V 0 = ⊥ ∧ V (Fin.last R) = ⊤ ∧ Monotone V ∧ (∀ g j x, x ∈ V j → (r g : Matrix (Fin n) (Fin n) k).mulVec x ∈ V j) ∧ Function.Injective rs ∧ ∀ s, ∃ x ∈ V (rs s).succ, x ∉ V (rs s).castSucc ∧ V (rs s).succ = V (rs s).castSucc ⊔ Submodule.span k {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) k).mulVec x - ((ψ s g : kˣ) : k) • x ∈ V (rs s).castSucc := by
  intro k Γ _ _ n a t r ρ ψ _ hc
  let π : Representation k Γ (Fin n → k) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toAlgHom.toRingHom.toMonoidHom.comp
      ((Units.coeHom _).comp r)
  let α : Representation k Γ (Fin a → k) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) k ≃ₐ[k] Module.End k (Fin a → k)).toAlgHom.toRingHom.toMonoidHom.comp
      ((Units.coeHom _).comp ρ)
  have hπ : ∀ g, π g = Matrix.toLin' (r g : Matrix (Fin n) (Fin n) k) := fun g => rfl
  have hα : ∀ g, α g = Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k) := fun g => rfl
  obtain ⟨R, W, rs, h0, h1, hm, hst, hinj, hstep⟩ := main_gen _ rfl π ψ α fun g => by
    rw [hπ, hα, Matrix.charpoly_toLin', Matrix.charpoly_toLin']
    exact hc g
  refine ⟨R, W, rs, h0, h1, hm, fun g j x hx => ?_, hinj, fun s => ?_⟩
  · have := hst g j x hx
    rwa [hπ, Matrix.toLin'_apply] at this
  · obtain ⟨x, hx1, hx2, hx3, hx4⟩ := hstep s
    refine ⟨x, hx1, hx2, hx3, fun g => ?_⟩
    have := hx4 g
    rwa [hπ, Matrix.toLin'_apply] at this

end GlobalTheory.CharFlag

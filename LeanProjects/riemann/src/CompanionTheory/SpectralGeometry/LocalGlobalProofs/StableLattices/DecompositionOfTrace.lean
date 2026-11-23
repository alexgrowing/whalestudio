import Mathlib
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckDecOfTrace

universe u

variable {O : Type u} {N : O → Type} [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]
  {Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop}

def homSub (hc : IsLinCat N Hom) (a b : O) : Submodule ℂ (N a →ₗ[ℂ] N b) where
  carrier := {f | Hom a b f}
  add_mem' := fun {f g} hf hg => hc.add a b f g hf hg
  zero_mem' := hc.zero a b
  smul_mem' := fun c f hf => hc.smul a b c f hf

def post (hc : IsLinCat N Hom) (a : O) {b c : O} (f : N b →ₗ[ℂ] N c) (hf : Hom b c f) :
    homSub hc a b →ₗ[ℂ] homSub hc a c where
  toFun w := ⟨f ∘ₗ w.1, hc.comp _ _ _ _ _ w.2 hf⟩
  map_add' v w := Subtype.ext (by simp [LinearMap.comp_add])
  map_smul' c w := Subtype.ext (by simp [LinearMap.comp_smul])

theorem exists_iso_of_eq (hc : IsLinCat N Hom) {a b : O} (h : a = b) :
    ∃ (θ : N a →ₗ[ℂ] N b) (θ' : N b →ₗ[ℂ] N a), Hom a b θ ∧ Hom b a θ' ∧ θ ∘ₗ θ' = LinearMap.id ∧
      θ' ∘ₗ θ = LinearMap.id := by
  subst h
  exact ⟨LinearMap.id, LinearMap.id, hc.id a, hc.id a, rfl, rfl⟩

theorem exists_basis (hc : IsLinCat N Hom) {P : Type} [DecidableEq P] {T : P → O} (hT : IsSimpleFam Hom T)
    {κ : Type} [Fintype κ] {par : κ → P} {X : O} {io : ∀ k, N (T (par k)) →ₗ[ℂ] N X}
    {pr : ∀ k, N X →ₗ[ℂ] N (T (par k))} (hd : IsDec Hom X (fun k => T (par k)) io pr) (ν : P) :
    ∃ b : Module.Basis {k // par k = ν} ℂ (homSub hc (T ν) X),
      ∀ k, ∃ θ : N (T ν) →ₗ[ℂ] N (T (par k.1)), (b k).1 = io k.1 ∘ₗ θ := by
  classical
  have hex := fun k : {k // par k = ν} => exists_iso_of_eq hc (congrArg T k.2.symm)
  choose θ θ' hθ hθ' h1 h2 using hex
  let v : {k // par k = ν} → homSub hc (T ν) X := fun k =>
    ⟨io k.1 ∘ₗ θ k, hc.comp _ _ _ _ _ (hθ k) (hd.io_hom k.1)⟩
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := hT.1 ν
    obtain ⟨x, hx⟩ := exists_ne (0 : N (T ν))
    have h3 := congrArg (fun w : homSub hc (T ν) X => θ' i (pr i.1 (w.1 x))) hg
    simp only [v, Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      map_sum, map_smul, Submodule.coe_zero, LinearMap.zero_apply, map_zero, LinearMap.comp_apply] at h3
    rw [Finset.sum_eq_single i] at h3
    · have e1 : pr i.1 (io i.1 (θ i x)) = θ i x := LinearMap.congr_fun (hd.pr_io i.1) _
      have e2 : θ' i (θ i x) = x := LinearMap.congr_fun (h2 i) _
      rw [e1, e2] at h3
      exact (smul_eq_zero.1 h3).resolve_right hx
    · intro k _ hk
      have e1 : pr i.1 (io k.1 (θ k x)) = 0 :=
        LinearMap.congr_fun (hd.pr_io_ne i.1 k.1 fun h => hk (Subtype.ext h.symm)) _
      rw [e1]; simp
    · simp
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    intro w _
    have hw : w = ∑ k, (⟨io k ∘ₗ (pr k ∘ₗ w.1), hc.comp _ _ _ _ _ (hc.comp _ _ _ _ _ w.2 (hd.pr_hom k))
        (hd.io_hom k)⟩ : homSub hc (T ν) X) := by
      apply Subtype.ext
      ext x
      have := LinearMap.congr_fun hd.sum (w.1 x)
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at this
      simp only [Submodule.coe_sum, LinearMap.sum_apply, LinearMap.comp_apply, this]
    rw [hw]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : par k = ν
    · obtain ⟨c, hc'⟩ := hT.2.1 ν (θ' ⟨k, hk⟩ ∘ₗ (pr k ∘ₗ w.1))
        (hc.comp _ _ _ _ _ (hc.comp _ _ _ _ _ w.2 (hd.pr_hom k)) (hθ' ⟨k, hk⟩))
      have : (⟨io k ∘ₗ (pr k ∘ₗ w.1), hc.comp _ _ _ _ _ (hc.comp _ _ _ _ _ w.2 (hd.pr_hom k))
        (hd.io_hom k)⟩ : homSub hc (T ν) X) = c • v ⟨k, hk⟩ := by
        apply Subtype.ext
        ext x
        have e1 : θ' ⟨k, hk⟩ (pr k (w.1 x)) = c • x := LinearMap.congr_fun hc' x
        have e2 : θ ⟨k, hk⟩ (θ' ⟨k, hk⟩ (pr k (w.1 x))) = pr k (w.1 x) := LinearMap.congr_fun (h1 _) _
        rw [e1] at e2
        show io k (pr k (w.1 x)) = c • io k (θ ⟨k, hk⟩ x)
        rw [← e2, map_smul, map_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · have h0 := hT.2.2 ν (par k) (Ne.symm hk) (pr k ∘ₗ w.1) (hc.comp _ _ _ _ _ w.2 (hd.pr_hom k))
      have : (⟨io k ∘ₗ (pr k ∘ₗ w.1), hc.comp _ _ _ _ _ (hc.comp _ _ _ _ _ w.2 (hd.pr_hom k))
        (hd.io_hom k)⟩ : homSub hc (T ν) X) = 0 := by
        apply Subtype.ext
        simp [h0]
      rw [this]
      exact Submodule.zero_mem _
  exact ⟨Module.Basis.mk hli hsp, fun k => ⟨θ k, by rw [Module.Basis.mk_apply]⟩⟩

theorem exists_trace (hc : IsLinCat N Hom) {P : Type} [DecidableEq P] {T : P → O} (hT : IsSimpleFam Hom T)
    {κ : Type} [Fintype κ] {par : κ → P} {X : O} {io : ∀ k, N (T (par k)) →ₗ[ℂ] N X}
    {pr : ∀ k, N X →ₗ[ℂ] N (T (par k))} (hd : IsDec Hom X (fun k => T (par k)) io pr) (ν : P)
    (Φ : Module.End ℂ (N X)) (a : κ → ℂ) (h : ∀ k, Φ ∘ₗ io k = a k • io k) :
    ∃ F : Module.End ℂ (homSub hc (T ν) X), (∀ w, (F w).1 = Φ ∘ₗ w.1) ∧
      LinearMap.trace ℂ _ F = ∑ k ∈ univ.filter (fun k => par k = ν), a k := by
  classical
  obtain ⟨b, hb⟩ := exists_basis hc hT hd ν
  refine ⟨b.constr ℂ fun k => a k.1 • b k, ?_, ?_⟩
  · have : (homSub hc (T ν) X).subtype ∘ₗ (b.constr ℂ fun k => a k.1 • b k) =
        (LinearMap.llcomp ℂ _ _ _ Φ) ∘ₗ (homSub hc (T ν) X).subtype := by
      refine b.ext fun k => ?_
      obtain ⟨θ, hθ⟩ := hb k
      simp only [LinearMap.comp_apply, Module.Basis.constr_basis, Submodule.subtype_apply,
        Submodule.coe_smul, LinearMap.llcomp_apply', hθ]
      rw [← LinearMap.comp_assoc, h, LinearMap.smul_comp]
    intro w
    exact LinearMap.congr_fun this w
  · rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace,
      Finset.sum_subtype (univ.filter fun k => par k = ν) (p := fun k => par k = ν) (by simp)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [LinearMap.toMatrix_apply]

theorem dec_of_gen (hc : IsLinCat N Hom) {P : Type} {T : P → O} (hT : IsSimpleFam Hom T)
    {κ : Type} [Fintype κ] {par : κ → P} {X Z : O} {io : ∀ k, N (T (par k)) →ₗ[ℂ] N X}
    {pr : ∀ k, N X →ₗ[ℂ] N (T (par k))} (hd : IsDec Hom X (fun k => T (par k)) io pr)
    {j : N Z →ₗ[ℂ] N X} {q : N X →ₗ[ℂ] N Z} (hj : Hom Z X j) (hq : Hom X Z q) (hqj : q ∘ₗ j = LinearMap.id)
    {I : Type} [Fintype I] {e : I → P} (he : Function.Injective e)
    (g : ∀ i, homSub hc (T (e i)) Z) (hg0 : ∀ i, g i ≠ 0) (hg : ∀ i w, ∃ c : ℂ, c • g i = w)
    (h0 : ∀ ν, (∀ i, e i ≠ ν) → ∀ w : homSub hc (T ν) Z, w = 0) :
    ∃ io pr, IsDec Hom Z (fun i => T (e i)) io pr := by
  classical
  let S : (N Z →ₗ[ℂ] N Z) → Prop := fun f =>
    ∃ r : ∀ i, homSub hc Z (T (e i)), ∑ i, (g i).1 ∘ₗ (r i).1 = f
  have S0 : S 0 := ⟨0, by simp⟩
  have Sadd : ∀ f f', S f → S f' → S (f + f') := by
    rintro _ _ ⟨r, rfl⟩ ⟨r', rfl⟩
    exact ⟨r + r', by simp [LinearMap.comp_add, Finset.sum_add_distrib]⟩
  have Sterm : ∀ ν (f : N (T ν) →ₗ[ℂ] N Z) (h : N Z →ₗ[ℂ] N (T ν)), Hom _ _ f → Hom _ _ h → S (f ∘ₗ h) := by
    intro ν f h hf hh
    by_cases hν : ∃ i, e i = ν
    · obtain ⟨i, rfl⟩ := hν
      obtain ⟨c, hc'⟩ := hg i ⟨f, hf⟩
      have hc'' : c • (g i).1 = f := congrArg Subtype.val hc'
      refine ⟨Pi.single i (c • ⟨h, hh⟩), ?_⟩
      rw [Finset.sum_eq_single i]
      · simp [← hc'', LinearMap.comp_smul, LinearMap.smul_comp]
      · intro i' _ hi'
        simp [Pi.single_eq_of_ne hi']
      · simp
    · push Not at hν
      have : f = 0 := congrArg Subtype.val (h0 ν hν ⟨f, hf⟩)
      rw [this, LinearMap.zero_comp]
      exact S0
  have Sid : S LinearMap.id := by
    have : (LinearMap.id : N Z →ₗ[ℂ] N Z) = ∑ k, (q ∘ₗ io k) ∘ₗ (pr k ∘ₗ j) := by
      ext x
      have e1 := LinearMap.congr_fun hd.sum (j x)
      have e2 : q (j x) = x := LinearMap.congr_fun hqj x
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at e1 ⊢
      rw [← map_sum, e1, e2]
    rw [this]
    exact Finset.sum_induction _ S Sadd S0 fun k _ =>
      Sterm _ _ _ (hc.comp _ _ _ _ _ (hd.io_hom k) hq) (hc.comp _ _ _ _ _ hj (hd.pr_hom k))
  obtain ⟨r, hr⟩ := Sid
  have hne : ∀ i i', i ≠ i' → (r i).1 ∘ₗ (g i').1 = 0 := fun i i' h =>
    hT.2.2 (e i') (e i) (fun h' => h (he h').symm) _ (hc.comp _ _ _ _ _ (g i').2 (r i).2)
  refine ⟨fun i => (g i).1, fun i => (r i).1, fun i => (g i).2, fun i => (r i).2, hr, fun i => ?_, hne⟩
  obtain ⟨c, hc'⟩ := hT.2.1 (e i) _ (hc.comp _ _ _ _ _ (g i).2 (r i).2)
  have h1 : (∑ i', (g i').1 ∘ₗ (r i').1) ∘ₗ (g i).1 = (g i).1 := by rw [hr, LinearMap.id_comp]
  have h2 : (∑ i', (g i').1 ∘ₗ (r i').1) ∘ₗ (g i).1 = c • (g i).1 := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    rw [Finset.sum_eq_single i]
    · have : (r i).1 ((g i).1 x) = c • x := LinearMap.congr_fun hc' x
      rw [this, map_smul]; rfl
    · intro i' _ hi'
      have : (r i').1 ((g i).1 x) = 0 := LinearMap.congr_fun (hne i' i hi') x
      rw [this, map_zero]
    · simp
  have h3 : (c - 1) • (g i).1 = 0 := by rw [sub_smul, one_smul, ← h2, h1, sub_self]
  have h4 : (g i).1 ≠ 0 := fun h => hg0 i (Subtype.ext h)
  have h5 : c = 1 := sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right h4)
  rw [hc', h5, one_smul]

theorem decOfTrace : DecOfTrace := by
  intro O N _ _ Hom hc P _ T hT κ _ par X Z io₁ io₂ pr₁ pr₂ hd₁ hd₂ Φ Φ₁ Φ₂ a b cs α β h₁ h₂ hΦ j q hj hq
    hqj hβ hrel I _ e he hone hzero
  have key : ∀ ν, Module.Finite ℂ (homSub hc (T ν) Z) ∧
      β * (Module.finrank ℂ (homSub hc (T ν) Z) : ℂ) =
        ∑ k ∈ univ.filter (fun k => par k = ν), (a k + b k + α - cs ν) := by
    intro ν
    obtain ⟨bs, -⟩ := exists_basis hc hT hd₁ ν
    haveI : Module.Finite ℂ (homSub hc (T ν) X) := Module.Finite.of_basis bs
    have hid : post hc (T ν) q hq ∘ₗ post hc (T ν) j hj = LinearMap.id := by
      ext w x
      exact LinearMap.congr_fun hqj (w.1 x)
    haveI hfin : Module.Finite ℂ (homSub hc (T ν) Z) :=
      Module.Finite.of_surjective (post hc (T ν) q hq) fun w =>
        ⟨post hc (T ν) j hj w, LinearMap.congr_fun hid w⟩
    refine ⟨hfin, ?_⟩
    obtain ⟨F₁, hF₁, t₁⟩ := exists_trace hc hT hd₁ ν Φ₁ a h₁
    obtain ⟨F₂, hF₂, t₂⟩ := exists_trace hc hT hd₂ ν Φ₂ b h₂
    obtain ⟨F₃, hF₃, t₃⟩ := exists_trace hc hT hd₁ ν ((α - cs ν) • LinearMap.id) (fun _ => α - cs ν)
      (fun k => by ext x; simp)
    have hA : β • (post hc (T ν) j hj ∘ₗ post hc (T ν) q hq) = F₁ + F₂ + F₃ := by
      ext w x
      have e1 : Φ (w.1 x) = cs ν • w.1 x := LinearMap.congr_fun (hΦ ν w.1 w.2) x
      rw [hrel] at e1
      simp only [LinearMap.add_apply, Submodule.coe_add, hF₁, hF₂, hF₃, LinearMap.comp_apply,
        LinearMap.smul_apply, LinearMap.id_apply, LinearMap.sub_apply] at e1 ⊢
      show β • j (q (w.1 x)) = _
      rw [sub_smul, ← e1]
      abel
    have ht := congrArg (LinearMap.trace ℂ _) hA
    rw [map_smul, LinearMap.trace_comp_comm', hid, LinearMap.trace_id, map_add, map_add, t₁, t₂, t₃,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, smul_eq_mul] at ht
    rw [ht]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hgen : ∀ i, ∃ g : homSub hc (T (e i)) Z, g ≠ 0 ∧ ∀ w, ∃ c : ℂ, c • g = w := by
    intro i
    have h := (key (e i)).2
    rw [hone i] at h
    have h' : (Module.finrank ℂ (homSub hc (T (e i)) Z) : ℂ) = 1 :=
      mul_left_cancel₀ hβ (by rw [h, mul_one])
    exact finrank_eq_one_iff'.1 (by exact_mod_cast h')
  choose g hg0 hg using hgen
  refine dec_of_gen hc hT hd₁ hj hq hqj he g hg0 hg fun ν hν w => ?_
  obtain ⟨hfin, h⟩ := key ν
  rw [hzero ν hν] at h
  have h' : Module.finrank ℂ (homSub hc (T ν) Z) = 0 := by
    exact_mod_cast (mul_eq_zero.1 h).resolve_left hβ
  exact finrank_zero_iff_forall_zero.1 h' w

end GlobalTheory.CompanionTheory.ZuckDecOfTrace

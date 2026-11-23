import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.TwoFactorUnique
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff

noncomputable section

open GlobalTheory.PRep GroundTheory.Automorphic.RestrictedTensor Module
open scoped TensorProduct

namespace GlobalTheory.BCT.DimFac

variable {Γ V W M : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup M] [Module ℂ M]

theorem mem_fix {ρ : Representation ℂ Γ V} {L : Subgroup Γ} {v : V} : v ∈ fixed ρ L ↔ ∀ g ∈ L, ρ g v = v := by
  change (∀ h : L, _) ↔ _
  simp

theorem rep_mul (ρ : Representation ℂ Γ V) (a b : Γ) (v : V) : ρ a (ρ b v) = ρ (a * b) v := by
  rw [map_mul, Module.End.mul_apply]

theorem schur_of_fixed {σ : Representation ℂ Γ W} (hσ : σ.IsIrreducible) (U : Subgroup Γ) (h0 : fixed σ U ≠ ⊥)
    [FiniteDimensional ℂ (fixed σ U)] (T : End ℂ W) (hT : ∀ g, T * σ g = σ g * T) : ∃ c : ℂ, T = c • 1 := by
  have hT' : ∀ g x, T (σ g x) = σ g (T x) := fun g x => LinearMap.congr_fun (hT g) x
  have hm : ∀ x ∈ fixed σ U, T x ∈ fixed σ U := fun x hx => mem_fix.2 fun g hg => by
    rw [← hT', mem_fix.1 hx g hg]
  haveI : Nontrivial (fixed σ U) := Submodule.nontrivial_iff_ne_bot.2 h0
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T.restrict hm)
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hx1 : T x.1 = c • x.1 := congrArg Subtype.val hx.apply_eq_smul
  refine ⟨c, ?_⟩
  rcases ((GlobalTheory.CuspRep.isIrreducible_iff σ).1 hσ).2 (LinearMap.ker (T - c • 1)) (fun g v hv => by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hv ⊢
    rw [hT', hv, map_smul]) with h | h
  · have : x.1 ∈ LinearMap.ker (T - c • 1) := by simp [hx1]
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hx.2
  · exact sub_eq_zero.1 (LinearMap.ker_eq_top.1 h)

def cut (e : Γ →* Γ) (hc : ∀ g y, Commute ((e g)⁻¹ * g) (e y)) : Γ →* Γ where
  toFun g := (e g)⁻¹ * g
  map_one' := by simp
  map_mul' a b := by
    have h := (hc a b).inv_right.eq
    rw [map_mul, mul_inv_rev]
    calc (e b)⁻¹ * (e a)⁻¹ * (a * b) = (e b)⁻¹ * ((e a)⁻¹ * a) * b := by group
      _ = _ := by rw [← h]; group

def homSp (σ : Representation ℂ Γ W) (ρ : Representation ℂ Γ V) (e : Γ →* Γ) : Submodule ℂ (W →ₗ[ℂ] V) where
  carrier := {f | ∀ g x, f (σ g x) = ρ (e g) (f x)}
  add_mem' := fun {a b} ha hb g x => by simp [ha g x, hb g x]
  zero_mem' := fun g x => by simp
  smul_mem' := fun c f hf g x => by simp [hf g x]

def homRep (σ : Representation ℂ Γ W) (ρ : Representation ℂ Γ V) (e : Γ →* Γ)
    (hc : ∀ g y, Commute ((e g)⁻¹ * g) (e y)) : Representation ℂ Γ (homSp σ ρ e) where
  toFun g :=
    { toFun := fun f => ⟨ρ (cut e hc g) ∘ₗ f.1, fun y x => by
        simp only [LinearMap.comp_apply]
        rw [f.2 y x, rep_mul, rep_mul]
        exact congrArg (fun z => ρ z (f.1 x)) (hc g y).eq⟩
      map_add' := fun a b => Subtype.ext (LinearMap.comp_add _ _ _)
      map_smul' := fun c a => Subtype.ext (LinearMap.comp_smul _ _ _) }
  map_one' := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun x => by simp)
  map_mul' a b := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun x => by simp)

theorem contractLeft_map {W' M' : Type} [AddCommGroup W'] [Module ℂ W'] [AddCommGroup M'] [Module ℂ M']
    (l : Dual ℂ W') (A : W →ₗ[ℂ] W') (B : M →ₗ[ℂ] M') (t : W ⊗[ℂ] M) :
    contractLeft l (TensorProduct.map A B t) = B (contractLeft (l ∘ₗ A) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [contractLeft_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem contractRight_map {W' M' : Type} [AddCommGroup W'] [Module ℂ W'] [AddCommGroup M'] [Module ℂ M']
    (l : Dual ℂ M') (A : W →ₗ[ℂ] W') (B : M →ₗ[ℂ] M') (t : W ⊗[ℂ] M) :
    contractRight l (TensorProduct.map A B t) = A (contractRight (l ∘ₗ B) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [contractRight_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_smulRight (l : Dual ℂ W) (y : W) (t : W ⊗[ℂ] M) :
    TensorProduct.map (l.smulRight y) LinearMap.id t = y ⊗ₜ contractLeft l t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x m => simp [contractLeft_tmul, TensorProduct.smul_tmul]
  | add x y hx hy => simp only [map_add, hx, hy, TensorProduct.tmul_add]

theorem exists_split {ρ : Representation ℂ Γ V} (hρ : ρ.IsIrreducible) {σ : Representation ℂ Γ W}
    (hσ : σ.IsIrreducible) (hs : ∀ T : End ℂ W, (∀ g, T * σ g = σ g * T) → ∃ c : ℂ, T = c • 1) {e : Γ →* Γ}
    (he : ∀ g, e (e g) = e g) (hc : ∀ g y, Commute ((e g)⁻¹ * g) (e y))
    {f : W →ₗ[ℂ] V} (hf0 : f ≠ 0) (hf : ∀ g x, f (σ g x) = ρ (e g) (f x)) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M) (τ : Representation ℂ Γ M) (Φ : W ⊗[ℂ] M ≃ₗ[ℂ] V),
      (∀ g, τ (e g) = 1) ∧ ∀ g t, Φ (TensorProduct.map (σ g) (τ g) t) = ρ g (Φ t) := by
  classical
  let ev : W ⊗[ℂ] homSp σ ρ e →ₗ[ℂ] V := TensorProduct.lift (homSp σ ρ e).subtype.flip
  have hev : ∀ x (u : homSp σ ρ e), ev (x ⊗ₜ u) = u.1 x := fun x u => rfl
  have heq : ∀ g t, ev (TensorProduct.map (σ g) (homRep σ ρ e hc g) t) = ρ g (ev t) := by
    intro g t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x u =>
      rw [TensorProduct.map_tmul, hev, hev]
      change ρ ((e g)⁻¹ * g) (u.1 (σ g x)) = _
      rw [u.2 g x, rep_mul, (hc g g).eq, mul_inv_cancel_left]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hsurj : Function.Surjective ev := by
    rcases ((GlobalTheory.CuspRep.isIrreducible_iff ρ).1 hρ).2 (LinearMap.range ev) (by
      rintro g _ ⟨t, rfl⟩
      exact ⟨_, heq g t⟩) with h | h
    · refine absurd (LinearMap.ext fun x => ?_) hf0
      have : ev (x ⊗ₜ ⟨f, hf⟩) ∈ LinearMap.range ev := ⟨_, rfl⟩
      rw [h] at this
      exact this
    · exact LinearMap.range_eq_top.1 h
  have hinj : Function.Injective ev := by
    refine (injective_iff_map_eq_zero ev).2 fun t ht => ?_
    by_contra h0
    obtain ⟨l, hl⟩ := exists_contractLeft_ne_zero h0
    refine hl (Subtype.ext (LinearMap.ext fun y => ?_))
    obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
    obtain ⟨r, hr⟩ := exists_asAlgebraHom_eq hσ hs (l.smulRight y) (s.image Prod.fst)
    have key : ∀ (r : MonoidAlgebra ℂ Γ) (u : homSp σ ρ e) x,
        u.1 (σ.asAlgebraHom r x) = Representation.asAlgebraHom (ρ.comp e) r (u.1 x) := by
      intro r u x
      induction r using MonoidAlgebra.induction_on with
      | of g => simpa using u.2 g x
      | add a b ha hb => simp [ha, hb]
      | smul c a ha => simp [ha]
    have h1 : ev (TensorProduct.map (l.smulRight y) LinearMap.id (∑ i ∈ s, i.1 ⊗ₜ[ℂ] i.2)) =
        Representation.asAlgebraHom (ρ.comp e) r (ev (∑ i ∈ s, i.1 ⊗ₜ[ℂ] i.2)) := by
      simp only [map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [TensorProduct.map_tmul, hev, hev, ← key, hr _ (Finset.mem_image_of_mem _ hi)]
      rfl
    rw [ht, map_zero, map_smulRight, hev] at h1
    exact h1
  refine ⟨homSp σ ρ e, inferInstance, inferInstance, homRep σ ρ e hc, LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩,
    fun g => LinearMap.ext fun u => Subtype.ext (LinearMap.ext fun x => ?_), heq⟩
  change ρ ((e (e g))⁻¹ * e g) (u.1 x) = u.1 x
  rw [he, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_dual_one {x : W} (hx : x ≠ 0) : ∃ l : Dual ℂ W, l x = 1 := by
  obtain ⟨l, hl⟩ : ∃ l : Dual ℂ W, l x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff ℂ x).1 h)
  exact ⟨(l x)⁻¹ • l, by simp [hl]⟩

theorem irred_right {ρ : Representation ℂ Γ V} (hρ : ρ.IsIrreducible) {σ : Representation ℂ Γ W}
    {τ : Representation ℂ Γ M} (Φ : W ⊗[ℂ] M ≃ₗ[ℂ] V) (hΦ : ∀ g t, Φ (TensorProduct.map (σ g) (τ g) t) = ρ g (Φ t)) :
    τ.IsIrreducible := by
  obtain ⟨hV, hV'⟩ := (GlobalTheory.CuspRep.isIrreducible_iff ρ).1 hρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have ht : Φ.symm v ≠ 0 := by simpa using hv
  obtain ⟨l₀, hl₀⟩ := exists_contractLeft_ne_zero ht
  obtain ⟨l₁, hl₁⟩ := exists_contractRight_ne_zero ht
  obtain ⟨l, hl⟩ := exists_dual_one hl₁
  set x := contractRight l₁ (Φ.symm v)
  refine (GlobalTheory.CuspRep.isIrreducible_iff τ).2 ⟨⟨_, _, hl₀⟩, fun N hN => ?_⟩
  let X : Submodule ℂ V := ⨅ l : Dual ℂ W, N.comap (contractLeft l ∘ₗ Φ.symm.toLinearMap)
  have hX : ∀ t, Φ t ∈ X ↔ ∀ l : Dual ℂ W, contractLeft l t ∈ N := fun t => by simp [X]
  rcases hV' X (fun g v hv => by
    obtain ⟨t, rfl⟩ := Φ.surjective v
    rw [← hΦ, hX]
    intro l
    rw [contractLeft_map]
    exact hN g _ ((hX t).1 hv _)) with h | h
  · refine Or.inl ((Submodule.eq_bot_iff _).2 fun m hm => ?_)
    have h1 : Φ (x ⊗ₜ m) ∈ X := (hX _).2 fun l => by
      rw [contractLeft_tmul]
      exact N.smul_mem _ hm
    rw [h, Submodule.mem_bot, map_eq_zero_iff _ Φ.injective] at h1
    have h2 := congrArg (contractLeft l) h1
    rwa [contractLeft_tmul, hl, one_smul, map_zero] at h2
  · refine Or.inr (Submodule.eq_top_iff'.2 fun m => ?_)
    have h2 := (hX (x ⊗ₜ m)).1 (h ▸ Submodule.mem_top) l
    rwa [contractLeft_tmul, hl, one_smul] at h2

theorem map_left_of_fixed {σ : Representation ℂ Γ W} {L : Subgroup Γ} {t : W ⊗[ℂ] M}
    (ht : ∀ g ∈ L, TensorProduct.map (σ g) LinearMap.id t = t) (p : W →ₗ[ℂ] W) (hp : ∀ x ∈ fixed σ L, p x = x) :
    TensorProduct.map p LinearMap.id t = t := by
  by_contra h
  obtain ⟨l, hl⟩ := exists_contractRight_ne_zero (sub_ne_zero.2 h)
  apply hl
  rw [map_sub, contractRight_map, LinearMap.comp_id, hp, sub_self]
  refine mem_fix.2 fun g hg => ?_
  conv_rhs => rw [← ht g hg, contractRight_map, LinearMap.comp_id]

theorem map_right_of_fixed {τ : Representation ℂ Γ M} {L : Subgroup Γ} {t : W ⊗[ℂ] M}
    (ht : ∀ g ∈ L, TensorProduct.map LinearMap.id (τ g) t = t) (p : M →ₗ[ℂ] M) (hp : ∀ x ∈ fixed τ L, p x = x) :
    TensorProduct.map LinearMap.id p t = t := by
  by_contra h
  obtain ⟨l, hl⟩ := exists_contractLeft_ne_zero (sub_ne_zero.2 h)
  apply hl
  rw [map_sub, contractLeft_map, LinearMap.comp_id, hp, sub_self]
  refine mem_fix.2 fun g hg => ?_
  conv_rhs => rw [← ht g hg, contractLeft_map, LinearMap.comp_id]

theorem finrank_fixed_split {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {τ : Representation ℂ Γ M}
    (Φ : W ⊗[ℂ] M ≃ₗ[ℂ] V) (hΦ : ∀ g t, Φ (TensorProduct.map (σ g) (τ g) t) = ρ g (Φ t)) {e : Γ →* Γ}
    (hσ : ∀ g, σ (e g) = σ g) (hτ : ∀ g, τ (e g) = 1) {L : Subgroup Γ} (hL : ∀ g ∈ L, e g ∈ L) :
    finrank ℂ (fixed ρ L) = finrank ℂ (fixed σ L) * finrank ℂ (fixed τ L) := by
  let j := TensorProduct.map (fixed σ L).subtype (fixed τ L).subtype
  have hj : Function.Injective j :=
    TensorProduct.map_injective_of_flat_flat _ _ (Submodule.injective_subtype _) (Submodule.injective_subtype _)
  have hr : fixed ρ L = (LinearMap.range j).map Φ.toLinearMap := by
    refine le_antisymm (fun v hv => ?_) ?_
    · obtain ⟨t, rfl⟩ := Φ.surjective v
      have h0 : ∀ g ∈ L, TensorProduct.map (σ g) (τ g) t = t := fun g hg =>
        Φ.injective ((hΦ g t).trans (mem_fix.1 hv g hg))
      have h1 : ∀ g ∈ L, TensorProduct.map (σ g) LinearMap.id t = t := fun g hg => by
        have := h0 _ (hL g hg)
        rwa [hσ, hτ] at this
      have h2 : ∀ g ∈ L, TensorProduct.map LinearMap.id (τ g) t = t := fun g hg => by
        have := h0 _ (L.mul_mem (L.inv_mem (hL g hg)) hg)
        rwa [map_mul, map_mul, ← map_inv e, hσ, hτ, one_mul, ← map_mul, inv_mul_cancel, map_one] at this
      obtain ⟨p, hp⟩ := (fixed σ L).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
      obtain ⟨q, hq⟩ := (fixed τ L).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
      have h3 := map_left_of_fixed h1 ((fixed σ L).subtype ∘ₗ p) fun x hx =>
        congrArg Subtype.val (LinearMap.congr_fun hp ⟨x, hx⟩)
      have h4 := map_right_of_fixed h2 ((fixed τ L).subtype ∘ₗ q) fun x hx =>
        congrArg Subtype.val (LinearMap.congr_fun hq ⟨x, hx⟩)
      refine ⟨t, ⟨TensorProduct.map p q t, ?_⟩, rfl⟩
      conv_rhs => rw [← h3, ← h4]
      simp only [j, TensorProduct.map_map, LinearMap.comp_id, LinearMap.id_comp]
    · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
      refine mem_fix.2 fun g hg => ?_
      change ρ g (Φ (j t)) = Φ (j t)
      rw [← hΦ]
      congr 1
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [j, mem_fix.1 x.2 g hg, mem_fix.1 y.2 g hg]
      | add x y hx hy => simp only [map_add, hx, hy]
  rw [hr, LinearEquiv.finrank_map_eq, LinearMap.finrank_range_of_inj hj, Module.finrank_tensorProduct]

def HasComp (ρ : Representation ℂ Γ V) (e : Γ →* Γ) (L : Subgroup Γ) (d : ℕ) : Prop :=
  ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ Γ W), σ.IsIrreducible ∧
    (∀ T : End ℂ W, (∀ g, T * σ g = σ g * T) → ∃ c : ℂ, T = c • 1) ∧ (∀ g, σ (e g) = σ g) ∧
    (∃ f : W →ₗ[ℂ] V, f ≠ 0 ∧ ∀ g x, f (σ g x) = ρ (e g) (f x)) ∧ finrank ℂ (fixed σ L) = d

theorem hasComp_of_surjective {H : Type} [Group H] (ρ : Representation ℂ Γ V) (e : Γ →* Γ) (L : Subgroup Γ)
    (q : Γ →* H) (hq : Function.Surjective q) (hqe : ∀ g, q (e g) = q g) (σ : Representation ℂ H W)
    (hσ : σ.IsIrreducible) (U : Subgroup H) (hU : fixed σ U ≠ ⊥) [FiniteDimensional ℂ (fixed σ U)]
    (f : W →ₗ[ℂ] V) (hf0 : f ≠ 0) (hf : ∀ g x, f (σ (q g) x) = ρ (e g) (f x)) (K : Subgroup H)
    (h1 : ∀ g ∈ L, q g ∈ K) (h2 : ∀ k ∈ K, ∃ g ∈ L, q g = k) : HasComp ρ e L (finrank ℂ (fixed σ K)) := by
  obtain ⟨h0, h3⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσ
  refine ⟨W, _, _, σ.comp q, (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun N hN => h3 N fun k v hv => ?_⟩,
    fun T hT => schur_of_fixed hσ U hU T fun k => ?_, fun g => congrArg σ (hqe g), ⟨f, hf0, hf⟩, ?_⟩
  · obtain ⟨g, rfl⟩ := hq k
    exact hN g v hv
  · obtain ⟨g, rfl⟩ := hq k
    exact hT g
  · have : fixed (σ.comp q) L = fixed σ K := by
      ext x
      rw [mem_fix, mem_fix]
      refine ⟨fun h k hk => ?_, fun h g hg => h _ (h1 g hg)⟩
      obtain ⟨g, hg, rfl⟩ := h2 k hk
      exact h g hg
    rw [this]

theorem hasComp_of_trivial {τ : Representation ℂ Γ M} (h : τ.IsIrreducible) {e : Γ →* Γ} (hτ : ∀ g, τ (e g) = 1)
    (L : Subgroup Γ) : HasComp τ e L 1 := by
  haveI := ((GlobalTheory.CuspRep.isIrreducible_iff τ).1 h).1
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  refine ⟨ℂ, inferInstance, inferInstance, 1, (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨inferInstance, fun N _ =>
    eq_bot_or_eq_top N⟩, fun T _ => ⟨T 1, LinearMap.ext_ring (by simp)⟩, fun _ => rfl,
    ⟨LinearMap.toSpanSingleton ℂ M m, fun h => hm (by simpa using LinearMap.congr_fun h 1), fun g x => by simp [hτ]⟩, ?_⟩
  have : fixed (1 : Representation ℂ Γ ℂ) L = ⊤ := Submodule.eq_top_iff'.2 fun x => mem_fix.2 fun _ _ => rfl
  rw [this, finrank_top, finrank_self]

theorem HasComp.right {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {τ : Representation ℂ Γ M}
    (Φ : W ⊗[ℂ] M ≃ₗ[ℂ] V) (hΦ : ∀ g t, Φ (TensorProduct.map (σ g) (τ g) t) = ρ g (Φ t)) {e : Γ →* Γ}
    (hσ : ∀ g, σ (e g) = 1) {L : Subgroup Γ} {d : ℕ} (h : HasComp ρ e L d) : HasComp τ e L d := by
  obtain ⟨W', _, _, σ', h1, h2, h3, ⟨f, hf0, hf⟩, h4⟩ := h
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (LinearMap.ext h)
  obtain ⟨l, hl⟩ := exists_contractLeft_ne_zero (z := Φ.symm (f x)) (by simpa using hx)
  refine ⟨W', _, _, σ', h1, h2, h3, ⟨contractLeft l ∘ₗ Φ.symm.toLinearMap ∘ₗ f, fun h => hl (LinearMap.congr_fun h x),
    fun g y => ?_⟩, h4⟩
  obtain ⟨t, ht⟩ := Φ.surjective (f y)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hf, ← ht, ← hΦ, Φ.symm_apply_apply, Φ.symm_apply_apply, contractLeft_map, hσ]
  rfl

theorem HasComp.exists_op {ρ : Representation ℂ Γ V} (hρ : ρ.IsIrreducible) {e : Γ →* Γ}
    (he : ∀ g, e (e g) = e g) (hc : ∀ g y, Commute ((e g)⁻¹ * g) (e y)) {L : Subgroup Γ} (h : HasComp ρ e L 1) :
    ∃ P : V →ₗ[ℂ] V, (∀ g, e g = 1 → ∀ v, P (ρ g v) = ρ g (P v)) ∧
      ∀ v, (∀ g ∈ L, ρ (e g) v = v) → P v = v ∧ ∀ y, ∃ c : ℂ, P (ρ (e y) v) = c • v := by
  obtain ⟨W, _, _, σ, h1, h2, h3, ⟨f, hf0, hf⟩, h4⟩ := h
  obtain ⟨M, _, _, τ, Φ, hτ, hΦ⟩ := exists_split hρ h1 h2 he hc hf0 hf
  obtain ⟨x, hx0, hx⟩ := finrank_eq_one_iff'.1 h4
  obtain ⟨l, hl⟩ := exists_dual_one (x := x.1) fun h => hx0 (Subtype.ext h)
  refine ⟨Φ.toLinearMap ∘ₗ TensorProduct.map (l.smulRight x.1) LinearMap.id ∘ₗ Φ.symm.toLinearMap,
    fun g hg v => ?_, fun v hv => ?_⟩
  · obtain ⟨t, rfl⟩ := Φ.surjective v
    have : σ g = LinearMap.id := by rw [← h3, hg, map_one]; rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← hΦ, ← hΦ, Φ.symm_apply_apply, Φ.symm_apply_apply, this]
    simp only [TensorProduct.map_map, LinearMap.comp_id, LinearMap.id_comp]
  · obtain ⟨t, rfl⟩ := Φ.surjective v
    have h5 : ∀ g ∈ L, TensorProduct.map (σ g) LinearMap.id t = t := fun g hg => by
      have := Φ.injective ((hΦ (e g) t).trans (hv g hg))
      rwa [h3, hτ] at this
    have h6 := map_left_of_fixed h5 (l.smulRight x.1) fun y hy => by
      obtain ⟨c, hc⟩ := hx ⟨y, hy⟩
      have : y = c • x.1 := (congrArg Subtype.val hc).symm
      simp [this, hl]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    refine ⟨by rw [Φ.symm_apply_apply, h6], fun y => ⟨l (σ y x.1), ?_⟩⟩
    have h7 : t = x.1 ⊗ₜ contractLeft l t := by rw [← map_smulRight, h6]
    rw [← hΦ, Φ.symm_apply_apply, h3, hτ, ← map_smul, h7]
    simp [TensorProduct.smul_tmul']

section Family

variable {ι : Type} {e : ι → Γ →* Γ} {L : Subgroup Γ}

theorem finrank_fixed_eq_one (he : ∀ i g, e i (e i g) = e i g) (hne : ∀ i j, i ≠ j → ∀ g, e i (e j g) = 1)
    (hc : ∀ i g y, Commute ((e i g)⁻¹ * g) (e i y)) (hL : ∀ g, g ∈ L ↔ ∀ i, e i g ∈ L)
    (hfin : ∀ g, {i | e i g ∉ L}.Finite) {ρ : Representation ℂ Γ V} (hρ : ρ.IsIrreducible)
    (h : ∀ i, HasComp ρ (e i) L 1) {m : V} (hm0 : m ≠ 0) (hm : m ∈ fixed ρ L) : finrank ℂ (fixed ρ L) = 1 := by
  classical
  let N : Finset ι → Submodule ℂ V := fun U => Submodule.span ℂ {v | ∃ g, (∀ i ∉ U, e i g ∈ L) ∧ ρ g m = v}
  have hmono : Monotone N := fun U U' hU => Submodule.span_mono fun v ⟨g, hg, hv⟩ =>
    ⟨g, fun i hi => hg i fun h => hi (hU h), hv⟩
  have htop : ∀ v, ∃ U, v ∈ N U := by
    have h1 : Submodule.span ℂ (Set.range fun g => ρ g m) = ⊤ := by
      refine (((GlobalTheory.CuspRep.isIrreducible_iff ρ).1 hρ).2 _ fun g v hv => ?_).resolve_left fun h0 => hm0 ?_
      · refine (Submodule.span_le (p := (Submodule.span ℂ (Set.range fun g => ρ g m)).comap (ρ g))).2 ?_ hv
        rintro _ ⟨a, rfl⟩
        exact Submodule.subset_span ⟨g * a, (rep_mul ρ g a m).symm⟩
      · have : m ∈ Submodule.span ℂ (Set.range fun g => ρ g m) := Submodule.subset_span ⟨1, by simp⟩
        rwa [h0] at this
    have h2 : Submodule.span ℂ (Set.range fun g => ρ g m) ≤ ⨆ U, N U := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      exact Submodule.mem_iSup_of_mem (hfin g).toFinset (Submodule.subset_span ⟨g, fun i hi => by simpa using hi, rfl⟩)
    exact fun v => (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 (h2 (h1 ▸ Submodule.mem_top))
  have hdown : ∀ v ∈ fixed ρ L, ∀ U, v ∈ N U → v ∈ N ∅ := by
    intro v hv U
    induction U using Finset.induction_on with
    | empty => exact id
    | insert i U hi ih =>
      intro hU
      obtain ⟨P, hP1, hP2⟩ := (h i).exists_op hρ (he i) (hc i)
      have hfx : ∀ u ∈ fixed ρ L, ∀ g ∈ L, ρ (e i g) u = u := fun u hu g hg => mem_fix.1 hu _ ((hL g).1 hg i)
      refine ih ?_
      rw [← (hP2 v (hfx v hv)).1]
      refine (Submodule.span_le (p := (N U).comap P)).2 ?_ hU
      rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, hc'⟩ := (hP2 m (hfx m hm)).2 g
      have h1 : e i ((e i g)⁻¹ * g) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
      have h2 : ρ g m = ρ ((e i g)⁻¹ * g) (ρ (e i g) m) := by rw [rep_mul, (hc i g g).eq, mul_inv_cancel_left]
      change P (ρ g m) ∈ N U
      rw [h2, hP1 _ h1, hc', map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun j hj => ?_, rfl⟩)
      by_cases hji : j = i
      · rw [hji, h1]; exact L.one_mem
      · rw [map_mul, map_inv, hne j i hji, inv_one, one_mul]
        exact hg j (by simp [hji, hj])
  refine finrank_eq_one_iff'.2 ⟨⟨m, hm⟩, fun h => hm0 (congrArg Subtype.val h), fun v => ?_⟩
  obtain ⟨U, hU⟩ := htop v.1
  have h3 : N ∅ ≤ Submodule.span ℂ {m} := Submodule.span_mono (by
    rintro _ ⟨g, hg, rfl⟩
    exact mem_fix.1 hm g ((hL g).2 fun i => hg i (by simp)))
  obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.1 (h3 (hdown v.1 v.2 U hU))
  exact ⟨c, Subtype.ext hc'⟩

theorem finrank_fixed_eq_prod (he : ∀ i g, e i (e i g) = e i g) (hne : ∀ i j, i ≠ j → ∀ g, e i (e j g) = 1)
    (hc : ∀ i g y, Commute ((e i g)⁻¹ * g) (e i y)) (hL : ∀ g, g ∈ L ↔ ∀ i, e i g ∈ L)
    (hfin : ∀ g, {i | e i g ∉ L}.Finite) (T : Finset ι) :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V), ρ.IsIrreducible → ∀ d : ι → ℕ,
      (∀ i, HasComp ρ (e i) L (d i)) → (∀ i ∉ T, d i = 1) →
      (∃ m : V, m ≠ 0 ∧ ∀ g ∈ L, (∀ i ∈ T, e i g = 1) → ρ g m = m) → finrank ℂ (fixed ρ L) = ∏ i ∈ T, d i := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rintro V _ _ ρ hρ d h hd ⟨m, hm0, hm⟩
    exact finrank_fixed_eq_one he hne hc hL hfin hρ (fun i => hd i (by simp) ▸ h i) hm0
      (mem_fix.2 fun g hg => hm g hg (by simp))
  | insert i T hi ih =>
    rintro V _ _ ρ hρ d h hd ⟨m, hm0, hm⟩
    obtain ⟨W, _, _, σ, h1, h2, h3, ⟨f, hf0, hf⟩, h4⟩ := h i
    obtain ⟨M, _, _, τ, Φ, hτ, hΦ⟩ := exists_split hρ h1 h2 (he i) (hc i) hf0 hf
    have hirr := irred_right hρ Φ hΦ
    rw [finrank_fixed_split Φ hΦ h3 hτ fun g hg => (hL g).1 hg i, Finset.prod_insert hi, h4,
      ih M τ hirr (Function.update d i 1) ?_ ?_ ?_]
    · congr 1
      exact Finset.prod_congr rfl fun j hj => Function.update_of_ne (fun (h : j = i) => hi (h ▸ hj)) _ _
    · intro j
      by_cases hji : j = i
      · rw [hji, Function.update_self]
        exact hasComp_of_trivial hirr hτ L
      · rw [Function.update_of_ne hji]
        exact (h j).right Φ hΦ fun g => by rw [← h3, hne i j (Ne.symm hji), map_one]
    · intro j hj
      by_cases hji : j = i
      · rw [hji, Function.update_self]
      · rw [Function.update_of_ne hji]
        exact hd j (by simp [hji, hj])
    · obtain ⟨t, rfl⟩ := Φ.surjective m
      obtain ⟨l, hl⟩ := exists_contractLeft_ne_zero (z := t) (by simpa using hm0)
      refine ⟨_, hl, fun g hg hT => ?_⟩
      have h5 : e i ((e i g)⁻¹ * g) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
      have h6 := Φ.injective ((hΦ _ t).trans (hm ((e i g)⁻¹ * g) (L.mul_mem (L.inv_mem ((hL g).1 hg i)) hg)
        fun j hj => by
          rcases Finset.mem_insert.1 hj with rfl | hj
          · exact h5
          · rw [map_mul, map_inv, hne j i (fun h => hi (h ▸ hj)), hT j hj, inv_one, one_mul]))
      rw [← h3, h5, map_one, map_mul, ← map_inv (e i), hτ, one_mul] at h6
      conv_rhs => rw [← h6, contractLeft_map]
      rfl

end Family

end GlobalTheory.BCT.DimFac

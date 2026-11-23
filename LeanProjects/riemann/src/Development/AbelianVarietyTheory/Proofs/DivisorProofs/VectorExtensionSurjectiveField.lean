import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneRanksFieldCharPStatement

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv CategoryTheory

namespace GlobalTheory

namespace PDiv

theorem exists_retraction_of_pow_prime {p : ℕ} [hp : Fact p.Prime] {M N : Type} [CommMonoid M]
    [CommMonoid N] (hM : ∀ x : M, x ^ p = 1) (hN : ∀ x : N, x ^ p = 1) (i : M →* N)
    (hi : Function.Injective i) : ∃ r : N →* M, ∀ x, r (i x) = x := by
  letI : CommGroup M := commGroupOfIsUnit fun x => IsUnit.of_pow_eq_one (hM x) hp.out.ne_zero
  letI : CommGroup N := commGroupOfIsUnit fun x => IsUnit.of_pow_eq_one (hN x) hp.out.ne_zero
  letI : Module (ZMod p) (Additive M) := AddCommGroup.zmodModule fun x => hM x.toMul
  letI : Module (ZMod p) (Additive N) := AddCommGroup.zmodModule fun x => hN x.toMul
  obtain ⟨r, hr⟩ := ((MonoidHom.toAdditive i).toZModLinearMap p).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hi)
  exact ⟨MonoidHom.toAdditive.symm r.toAddMonoidHom, fun x => LinearMap.congr_fun hr (Additive.ofMul x)⟩

section Points

variable {k : Type} [Field k]

theorem exists_eval_eq (B : Type) [CommRing B] [Algebra k B] [Module.Finite k B]
    (g : (B →ₐ[k] k) → k) : ∃ c : B, ∀ x : B →ₐ[k] k, x c = g x := by
  have hv := linearIndependent_algHom_toLinearMap k B k
  obtain ⟨l, hl⟩ := (Finsupp.linearCombination k g ∘ₗ hv.repr).exists_extend
  refine ⟨(Module.evalEquiv k B).symm l, fun x => ?_⟩
  have h := LinearMap.congr_fun hl ⟨x.toLinearMap, Submodule.subset_span ⟨x, rfl⟩⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hv.repr_eq_single x _ rfl] at h
  refine (Module.apply_evalEquiv_symm_apply k B x.toLinearMap l).trans (h.trans ?_)
  simp

theorem exists_pow_eq_zero_of_eval [IsAlgClosed k] (A : Type) [CommRing A] [Algebra k A]
    [Module.Finite k A] : ∃ m : ℕ, ∀ a : A, (∀ x : A →ₐ[k] k, x a = 0) → a ^ m = 0 := by
  haveI : IsNoetherianRing A := isNoetherian_of_tower k inferInstance
  obtain ⟨m, hm⟩ := IsNoetherianRing.isNilpotent_nilradical A
  refine ⟨m, fun a ha => ?_⟩
  have h : a ∈ nilradical A := nilpotent_iff_mem_prime.2 fun P hP => by
    let e := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ P))
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    have := ha (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k P))
    exact Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff _ e.symm.injective).1 this)
  have := Ideal.pow_mem_pow h m
  rwa [hm, Ideal.zero_eq_bot, Ideal.mem_bot] at this

variable {p : ℕ} [hp : Fact p.Prime] {A B : Type} [CommRing A] [Bialgebra k A] [CommRing B]
  [Bialgebra k B]

theorem cobOne_pow_prime_pow (h : (p : k) = 0) (n : ℕ) (b : A) :
    cobOne k A (b ^ p ^ n) = cobOne k A b ^ p ^ n := by
  have h0 := natCast_eq_zero_of_algebra h (A ⊗[k] A)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_mul, pow_mul, ← ih, ← frobRing_apply h0]
    simp only [cobOne_apply, map_sub, frobRing_apply, comul_pow,
      Algebra.TensorProduct.tmul_pow, one_pow]

theorem eval_cobOne (x y : WithConv (A →ₐ[k] k)) (b : A) :
    Algebra.TensorProduct.lift x.ofConv y.ofConv (fun _ _ => .all _ _) (cobOne k A b) =
      (x * y).ofConv b - x.ofConv b - y.ofConv b := by
  rw [AlgHom.convMul_apply]
  simp [cobOne_apply]

theorem exists_prim_pow_of_isAlgClosed [IsAlgClosed k] (h : (p : k) = 0) [IsCocomm k A]
    [IsCocomm k B] [Module.Finite k A] [Module.Finite k B]
    (hA : ∀ x : WithConv (A →ₐ[k] k), x ^ p = 1) (hB : ∀ x : WithConv (B →ₐ[k] k), x ^ p = 1)
    (φ : B →ₐc[k] A) (hφ : Function.Surjective φ) :
    ∃ n : ℕ, ∀ b : A, cobOne k A b = 0 → ∃ c : B, cobOne k B c = 0 ∧ φ c = b ^ p ^ n := by
  obtain ⟨m₁, h₁⟩ := exists_pow_eq_zero_of_eval (k := k) A
  obtain ⟨m₂, h₂⟩ := exists_pow_eq_zero_of_eval (k := k) (B ⊗[k] B)
  let i := (SemiBialgHom.ofBialgHom φ).pts k fun _ => rfl
  obtain ⟨r, hr⟩ := exists_retraction_of_pow_prime hA hB i fun x y e =>
    ofConv_injective (AlgHom.ext fun a => by
      obtain ⟨a, rfl⟩ := hφ a
      exact DFunLike.congr_fun (congrArg ofConv e) a)
  have hm : m₁ + m₂ ≤ p ^ (m₁ + m₂) := (Nat.lt_pow_self hp.out.one_lt).le
  refine ⟨m₁ + m₂, fun b hb => ?_⟩
  obtain ⟨c, hc⟩ := exists_eval_eq B fun x => (r (toConv x)).ofConv b
  refine ⟨c ^ p ^ (m₁ + m₂), ?_, ?_⟩
  · rw [cobOne_pow_prime_pow h]
    refine pow_eq_zero_of_le (by omega) (h₂ _ fun z => ?_)
    let x := toConv (z.comp Algebra.TensorProduct.includeLeft)
    let y := toConv (z.comp Algebra.TensorProduct.includeRight)
    have hz : z = Algebra.TensorProduct.lift x.ofConv y.ofConv (fun _ _ => .all _ _) := by
      ext <;> simp [x, y]
    rw [hz, eval_cobOne, hc, hc, hc, toConv_ofConv, toConv_ofConv, toConv_ofConv, map_mul,
      ← eval_cobOne, hb, map_zero]
  · have h0 := natCast_eq_zero_of_algebra h A
    have h3 : (φ c - b) ^ p ^ (m₁ + m₂) = 0 :=
      pow_eq_zero_of_le (by omega) (h₁ _ fun x => by
        have := hc (i (toConv x)).ofConv
        rw [toConv_ofConv, hr] at this
        rw [map_sub, sub_eq_zero]
        exact this)
    have h4 : ∀ (n : ℕ) (u v : A), (u - v) ^ p ^ n = u ^ p ^ n - v ^ p ^ n := fun n u v => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, pow_mul, pow_mul, pow_mul, ih, ← frobRing_apply h0, map_sub, frobRing_apply,
          frobRing_apply]
    rwa [h4, sub_eq_zero, ← map_pow] at h3

end Points

end PDiv

namespace PDivGroup

open PDiv

variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [Field K] (h : (p : K) = 0) {G H : PDivGroup p K}
  (f : G ⟶ H)

include h

theorem exists_prim_pow (hf : Function.Surjective (f.app 1)) :
    ∃ n : ℕ, ∀ b : G.A 1, cobOne K _ b = 0 →
      ∃ c : H.A 1, cobOne K _ c = 0 ∧ f.app 1 c = b ^ p ^ n := by
  let k := AlgebraicClosure K
  obtain ⟨n, hn⟩ := exists_prim_pow_of_isAlgClosed (k := k) (natCast_eq_zero_of_algebra h k)
    (fun x => by simpa using (G.baseChange k).pts_pow_self 1 x)
    (fun x => by simpa using (H.baseChange k).pts_pow_self 1 x) (bcMap k (f.app 1))
    (LinearMap.lTensor_surjective k (g := (f.app 1 : H.A 1 →ₗ[K] G.A 1)) hf)
  refine ⟨n, fun b hb => ?_⟩
  obtain ⟨c, hc, e⟩ := hn _ ((toBaseChange K k (G.A 1)).prim ⟨b, hb⟩).2
  obtain ⟨z, hz⟩ := (T.additiveFunctions_flatBaseChange_bijective (R := K) (A := H.A 1) k).2 ⟨c, hc⟩
  obtain ⟨l, hl⟩ := (Algebra.linearMap K k).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap K k).injective)
  have hl1 : l 1 = 1 := by simpa using LinearMap.congr_fun hl 1
  have key : ∀ z : k ⊗[K] LinearMap.ker (cobOne K (H.A 1)),
      f.app 1 (TensorProduct.lid K _ (l.rTensor _ z)).1 = TensorProduct.lid K _ (l.rTensor _
        (bcMap k (f.app 1) (liftSemi (toBaseChange K k (H.A 1)).prim z).1)) := fun z => by
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
    | tmul r x => simp [smul_tmul']
  refine ⟨_, (TensorProduct.lid K _ (l.rTensor _ z)).2, ?_⟩
  rw [key, hz, e]
  simp [Algebra.TensorProduct.tmul_pow, hl1]

theorem omegaMap_baseChangeMap_surjective (R' : Type) [CommRing R'] [Algebra K R']
    (hf : Function.Surjective (omegaMap G H f)) :
    Function.Surjective (omegaMap _ _ (baseChangeMap R' f)) := fun w => by
  obtain ⟨z, rfl⟩ := (T.omega_baseChange_bijective_of_p_eq_zero G R' h).2 w
  change _ ∈ LinearMap.range _
  induction z with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | tmul r x =>
    obtain ⟨x, rfl⟩ := hf x
    rw [liftSemi_tmul, (G.toBase R').omega_naturality (H.toBase R') f (baseChangeMap R' f)
      fun _ _ => rfl]
    exact Submodule.smul_mem _ _ ⟨_, rfl⟩

theorem omegaMap_frobTwistMap_surjective (hf : Function.Surjective (omegaMap G H f)) :
    Function.Surjective (omegaMap _ _ (frobTwistMap h f)) :=
  letI := (frobRing h).toAlgebra
  omegaMap_baseChangeMap_surjective h f K hf

theorem exists_sub_mem_span_absFrob (hW : Published.BarsottiTateDieudonne.WittModule)
    (hf : Function.Surjective (omegaMap G H f)) (x : G.RigExt) :
    ∃ y, x - rigExtMap f y ∈ Submodule.span K (Set.range (absFrob h G).rig) := by
  obtain ⟨-, -, -, -, -, g₁, g₂⟩ := T.dieudonne_ranks_field_char_p hW p K h G
  obtain ⟨-, -, -, h₁, -⟩ := T.dieudonne_ranks_field_char_p hW p K h H
  obtain ⟨w, hw⟩ := range_rigExtMap_verschiebung_le h G ⟨x, rfl⟩
  obtain ⟨w, rfl⟩ := omegaMap_frobTwistMap_surjective h f hf w
  obtain ⟨y, hy⟩ := h₁.ge (LinearMap.mem_range_self _ w)
  refine ⟨y, (g₁.trans g₂).le (LinearMap.mem_ker.2 ((map_sub _ _ _).trans (sub_eq_zero.2 ?_)))⟩
  have e₁ := LinearMap.congr_fun (rigExtMap_comp (frobTwistMap h f) (verschiebung h H)) y
  have e₂ := LinearMap.congr_fun (rigExtMap_comp (verschiebung h G) f) y
  rw [verschiebung_naturality] at e₁
  exact hw.symm.trans ((rigExtMap_rigOfOmega _ w).symm.trans
    ((congrArg (rigExtMap (frobTwistMap h f)) hy.symm).trans (e₁.symm.trans e₂)))

theorem mem_sup_span_pow (hW : Published.BarsottiTateDieudonne.WittModule)
    (hf : Function.Surjective (omegaMap G H f)) (n : ℕ) (b : G.A 1) (hb : cobOne K _ b = 0) :
    b ∈ (LinearMap.ker (cobOne K (H.A 1))).map (f.app 1 : H.A 1 →ₗ[K] G.A 1) ⊔
      Submodule.span K {a | ∃ b : G.A 1, cobOne K _ b = 0 ∧ a = b ^ p ^ n} := by
  set U := (LinearMap.ker (cobOne K (H.A 1))).map (f.app 1 : H.A 1 →ₗ[K] G.A 1) with hU
  have h0 := natCast_eq_zero_of_algebra h (G.A 1)
  induction n generalizing b with
  | zero => exact Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, by simp⟩)
  | succ n ih =>
    set S := U ⊔ Submodule.span K {a | ∃ b : G.A 1, cobOne K _ b = 0 ∧ a = b ^ p ^ (n + 1)}
    have k₁ : ∀ a : G.A 1, cobOne K _ a = 0 → a ^ p ∈ S := fun a ha => by
      obtain ⟨u, ⟨c, hc, rfl⟩, v, hv, rfl⟩ := Submodule.mem_sup.1 (ih a ha)
      rw [← frobRing_apply h0, map_add]
      refine Submodule.add_mem_sup ⟨c ^ p, ?_, by simp⟩ ?_
      · have := cobOne_pow_prime_pow h 1 c
        rwa [pow_one, show cobOne K _ c = 0 from hc, zero_pow hp.out.ne_zero] at this
      · clear ha
        induction hv using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨b, hb, rfl⟩ := hx
          exact Submodule.subset_span ⟨b, hb, by rw [frobRing_apply, pow_succ, pow_mul]⟩
        | zero => rw [map_zero]; exact zero_mem _
        | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
        | smul r x _ hx =>
          rw [frobRing_apply, smul_pow, ← frobRing_apply h0]
          exact Submodule.smul_mem _ _ hx
    let t : G.RigExt →ₗ[K] G.A 1 := Submodule.subtype _ ∘ₗ G.extChar h ∘ₗ G.rigToExt
    obtain ⟨x, hx⟩ := ((G.extChar_bijective h).2.comp G.rigToExt_surjective) ⟨b, hb⟩
    obtain ⟨y, hy⟩ := exists_sub_mem_span_absFrob h f hW hf x
    have k₂ : Submodule.span K (Set.range (absFrob h G).rig) ≤ S.comap t := by
      rw [Submodule.span_le]
      rintro _ ⟨z, rfl⟩
      change (G.extChar h (G.rigToExt ((absFrob h G).rig z))).1 ∈ S
      rw [SemiHom.rigToExt_rig, SemiHom.extChar_vecExt _ h, SemiBialgHom.prim_val, absFrob_app]
      exact k₁ _ (G.extChar h _).2
    have k₃ : t (rigExtMap f y) ∈ S := Submodule.mem_sup_left
      ⟨_, (H.extChar h (H.rigToExt y)).2, by
        change _ = (G.extChar h (G.rigToExt (rigExtMap f y))).1
        rw [rigToExt_rigExtMap, extChar_vecExtMap h]
        rfl⟩
    have k₄ : t x = b := congrArg Subtype.val hx
    have k₅ := add_mem (Submodule.mem_comap.1 (k₂ hy)) k₃
    rwa [map_sub, sub_add_cancel, k₄] at k₅

omit h hp in

theorem vecExtMap_surjective_of_omegaMap_bijective (hW : Published.BarsottiTateDieudonne.WittModule)
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G H : PDivGroup p K) (f : G ⟶ H)
    (h₁ : Function.Surjective (f.app 1)) (h₂ : Function.Bijective (omegaMap G H f)) :
    Function.Surjective (vecExtMap f) := fun x => by
  obtain ⟨n, hn⟩ := exists_prim_pow h f h₁
  have k := mem_sup_span_pow h f hW h₂.2 n _ (G.extChar h x).2
  rw [sup_eq_left.2 (Submodule.span_le.2 (by
    rintro _ ⟨b, hb, rfl⟩
    exact hn b hb))] at k
  obtain ⟨c, hc, e⟩ := k
  obtain ⟨y, hy⟩ := (H.extChar_bijective h).2 ⟨c, hc⟩
  exact ⟨y, (G.extChar_bijective h).1 (Subtype.ext (by rw [extChar_vecExtMap h, hy]; exact e))⟩

end PDivGroup

end GlobalTheory

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrOnMapOfInjective

noncomputable section

open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.BCT.Peel

section Linear

variable {X V : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]

theorem trOn_map (j : X →ₗ[ℂ] V) (hj : Function.Injective j) (M : Submodule ℂ X) (L' : X →ₗ[ℂ] X) (L : V →ₗ[ℂ] V)
    (h : ∀ x ∈ M, L (j x) = j (L' x)) : trOn (M.map j) L = trOn M L' :=
  _root_.GlobalTheory.TraceOnInjectiveMap.trOn_map_of_injective j hj M L' L h

theorem trOn_of_not_finite (M : Submodule ℂ V) (L : V →ₗ[ℂ] V) (h : ¬ Module.Finite ℂ M) : trOn M L = 0 := by
  unfold trOn
  split_ifs with hL
  · rw [LinearMap.trace, dif_neg]
    · rfl
    · rintro ⟨s, ⟨b⟩⟩
      exact h (Module.Finite.of_basis b)
  · rfl

theorem trOn_bot (L : V →ₗ[ℂ] V) : trOn ⊥ L = 0 := by
  unfold trOn
  split_ifs with hL
  · rw [Subsingleton.elim (L.restrict hL) 0, map_zero]
  · rfl

end Linear

section Iso

variable {H X V W : Type} [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

theorem map_fixed {σ : Representation ℂ H W} {τ : Representation ℂ H X} (f : σ.IntertwiningMap τ) (K : Subgroup H)
    {v : W} (hv : v ∈ fixed σ K) : f.toLinearMap v ∈ fixed τ K := by
  rw [GlobalTheory.TwTrLin.mem_fixed_iff] at hv ⊢
  intro k hk
  have := LinearMap.congr_fun (f.isIntertwining' k) v
  simp only [LinearMap.comp_apply] at this
  rw [← this, hv k hk]

theorem schur (σ : Representation ℂ H W) [σ.IsIrreducible] (K : Subgroup H) [Module.Finite ℂ (fixed σ K)]
    (h0 : fixed σ K ≠ ⊥) (φ : σ.IntertwiningMap σ) : ∃ c : ℂ, ∀ w, φ.toLinearMap w = c • w := by
  haveI : Nontrivial (fixed σ K) := Submodule.nontrivial_iff_ne_bot.2 h0
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue
    (φ.toLinearMap.restrict (p := fixed σ K) (q := fixed σ K) fun v hv => map_fixed φ K hv)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hv1 : φ.toLinearMap v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, ?_⟩
  rcases ((isIrreducible_iff σ).1 inferInstance).2 (LinearMap.ker (φ.toLinearMap - c • LinearMap.id))
    (fun g u hu => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hu ⊢
      have := LinearMap.congr_fun (φ.isIntertwining' g) u
      simp only [LinearMap.comp_apply] at this
      rw [this, hu]
      simp) with h | h
  · exfalso
    have : v.1 ∈ LinearMap.ker (φ.toLinearMap - c • LinearMap.id) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      exact hv1
    rw [h] at this
    exact hv.2 (Subtype.ext this)
  · intro w
    have : w ∈ LinearMap.ker (φ.toLinearMap - c • LinearMap.id) := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this

theorem exists_decomp (σ : Representation ℂ H W) [σ.IsIrreducible] (τ : Representation ℂ H X) (ρ : Representation ℂ H V)
    (j : τ.IntertwiningMap ρ) (hj : Function.Injective j.toLinearMap)
    (h : ∀ x, j.toLinearMap x ∈ LocUniq.isoPart σ ρ) :
    ∃ (ι : Type) (s : ι → σ.IntertwiningMap τ) (p : ι → τ.IntertwiningMap σ),
      (∀ i i' w, (p i).toLinearMap ((s i').toLinearMap w) = if i' = i then w else 0) ∧
      ∀ x, (∀ i, (p i).toLinearMap x = 0) → x = 0 := by
  let R := MonoidAlgebra ℂ H
  let J : τ.asModule →ₗ[R] ρ.asModule := Representation.IntertwiningMap.equivLinearMapAsModule τ ρ j
  have hle : LocUniq.isoPart σ ρ ≤ ((isotypicComponent R ρ.asModule σ.asModule).restrictScalars ℂ).comap
      ρ.asModuleEquiv.symm.toLinearMap := by
    refine iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    let F : σ.asModule →ₗ[R] ρ.asModule := Representation.IntertwiningMap.equivLinearMapAsModule σ ρ f
    have h1 : LinearMap.range F ≤ isotypicComponent R ρ.asModule σ.asModule := by
      rcases LinearMap.injective_or_eq_zero F with hf | hf
      · exact le_sSup ⟨(LinearEquiv.ofInjective F hf).symm⟩
      · simp [hf]
    exact h1 ⟨σ.asModuleEquiv.symm v, rfl⟩
  let J' : τ.asModule →ₗ[R] isotypicComponent R ρ.asModule σ.asModule :=
    J.codRestrict _ fun x => hle (h (τ.asModuleEquiv x))
  have hJ' : Function.Injective J' := fun a b e => hj (congrArg Subtype.val e)
  haveI : IsSemisimpleModule R τ.asModule := IsSemisimpleModule.of_injective J' hJ'
  obtain ⟨ι, ⟨e⟩⟩ := ((IsIsotypicOfType.isotypicComponent R ρ.asModule σ.asModule).of_injective J' hJ').linearEquiv_finsupp
  refine ⟨ι, fun i => (Representation.IntertwiningMap.equivLinearMapAsModule σ τ).symm
      (e.symm.toLinearMap ∘ₗ Finsupp.lsingle i),
    fun i => (Representation.IntertwiningMap.equivLinearMapAsModule τ σ).symm (Finsupp.lapply i ∘ₗ e.toLinearMap),
    fun i i' w => ?_, fun x hx => ?_⟩
  · change e (e.symm (Finsupp.single i' (σ.asModuleEquiv.symm w))) i = _
    rw [e.apply_symm_apply, Finsupp.single_apply]
    rfl
  · have : e (τ.asModuleEquiv.symm x) = 0 := Finsupp.ext fun i => hx i
    exact e.injective (this.trans (map_zero e).symm)

end Iso

section Trace

variable {H X W : Type} [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup W] [Module ℂ W]

theorem exists_factor (σ : Representation ℂ H W) [σ.IsIrreducible] (τ : Representation ℂ H X) {ι : Type} [Fintype ι]
    (s : ι → σ.IntertwiningMap τ) (p : ι → τ.IntertwiningMap σ)
    (hps : ∀ i i' w, (p i).toLinearMap ((s i').toLinearMap w) = if i' = i then w else 0)
    (hp : ∀ x, (∀ i, (p i).toLinearMap x = 0) → x = 0) (K : Subgroup H) [Module.Finite ℂ (fixed σ K)]
    [Module.Finite ℂ (fixed τ K)] (h0 : fixed σ K ≠ ⊥) (B : τ.IntertwiningMap τ) :
    ∃ t : ℂ, ∀ (A : X →ₗ[ℂ] X) (a : W →ₗ[ℂ] W), (∀ v ∈ fixed σ K, a v ∈ fixed σ K) →
      (∀ i w, A ((s i).toLinearMap w) = (s i).toLinearMap (a w)) →
      trOn (fixed τ K) (A ∘ₗ B.toLinearMap) = t * trOn (fixed σ K) a := by
  have hsum : ∀ x, x = ∑ i, (s i).toLinearMap ((p i).toLinearMap x) := fun x => by
    rw [← sub_eq_zero]
    refine hp _ fun i => ?_
    simp only [map_sub, map_sum, hps]
    simp
  choose b hb using fun i j => schur σ K h0 ((p j).comp (B.comp (s i)))
  have hb' : ∀ i j w, (p j).toLinearMap (B.toLinearMap ((s i).toLinearMap w)) = b i j • w := hb
  refine ⟨∑ i, b i i, fun A a ha hA => ?_⟩
  have hform : ∀ y, A (B.toLinearMap y) = ∑ i, ∑ j, b i j • (s j).toLinearMap (a ((p i).toLinearMap y)) := fun y => by
    conv_lhs => rw [hsum y]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsum (B.toLinearMap _), map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb', map_smul, map_smul, hA]
  have hY : ∀ y ∈ fixed τ K, (A ∘ₗ B.toLinearMap) y ∈ fixed τ K := fun y hy => by
    rw [LinearMap.comp_apply, hform]
    exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (map_fixed _ K (ha _ (map_fixed _ K hy)))
  let sU : ι → (fixed σ K →ₗ[ℂ] fixed τ K) := fun i => (s i).toLinearMap.restrict fun v hv => map_fixed _ K hv
  let pU : ι → (fixed τ K →ₗ[ℂ] fixed σ K) := fun i => (p i).toLinearMap.restrict fun v hv => map_fixed _ K hv
  unfold trOn
  rw [dif_pos hY, dif_pos ha]
  have h1 : (A ∘ₗ B.toLinearMap).restrict hY = ∑ i, ∑ j, b i j • (sU j ∘ₗ (a.restrict ha ∘ₗ pU i)) := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    change A (B.toLinearMap y.1) = _
    rw [hform]
    simp only [LinearMap.sum_apply, Submodule.coe_sum]
    rfl
  have h2 : ∀ i j, (a.restrict ha ∘ₗ pU i) ∘ₗ sU j = if j = i then a.restrict ha else 0 := fun i j => by
    refine LinearMap.ext fun v => Subtype.ext ?_
    change a ((p i).toLinearMap ((s j).toLinearMap v.1)) = _
    rw [hps]
    split_ifs
    · rfl
    · exact map_zero a
  rw [h1, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Finset.sum_eq_single i]
  · rw [map_smul, LinearMap.trace_comp_comm', h2, if_pos rfl, smul_eq_mul]
  · intro j _ hj
    rw [map_smul, LinearMap.trace_comp_comm', h2, if_neg hj, map_zero, smul_zero]
  · simp

theorem trOn_cross {V : Type} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H W) [σ.IsIrreducible]
    (τ : Representation ℂ H X) (ρ : Representation ℂ H V) (j : τ.IntertwiningMap ρ)
    (hj : Function.Injective j.toLinearMap) (h : ∀ x, j.toLinearMap x ∈ LocUniq.isoPart σ ρ) (K : Subgroup H)
    (B : τ.IntertwiningMap τ) (A A' : X →ₗ[ℂ] X) (a a' : W →ₗ[ℂ] W) (ha : ∀ v ∈ fixed σ K, a v ∈ fixed σ K)
    (ha' : ∀ v ∈ fixed σ K, a' v ∈ fixed σ K)
    (hA : ∀ (s : σ.IntertwiningMap τ) w, A (s.toLinearMap w) = s.toLinearMap (a w))
    (hA' : ∀ (s : σ.IntertwiningMap τ) w, A' (s.toLinearMap w) = s.toLinearMap (a' w)) :
    trOn (fixed τ K) (A ∘ₗ B.toLinearMap) * trOn (fixed σ K) a' =
      trOn (fixed σ K) a * trOn (fixed τ K) (A' ∘ₗ B.toLinearMap) := by
  by_cases hU : Module.Finite ℂ (fixed σ K)
  swap
  · rw [trOn_of_not_finite _ a hU, trOn_of_not_finite _ a' hU, mul_zero, zero_mul]
  by_cases h0 : fixed σ K = ⊥
  · rw [h0, trOn_bot, trOn_bot, mul_zero, zero_mul]
  by_cases hY : Module.Finite ℂ (fixed τ K)
  swap
  · rw [trOn_of_not_finite _ _ hY, trOn_of_not_finite _ _ hY, mul_zero, zero_mul]
  obtain ⟨ι, s, p, hps, hp⟩ := exists_decomp σ τ ρ j hj h
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hli : LinearIndependent ℂ fun i => (⟨(s i).toLinearMap u, map_fixed _ K hu⟩ : fixed τ K) := by
    refine LinearIndependent.of_comp (fixed τ K).subtype (linearIndependent_iff'.2 fun T g hg i hi => ?_)
    have := congrArg (p i).toLinearMap hg
    simp only [Function.comp_apply, Submodule.subtype_apply, map_sum, map_smul, hps, map_zero] at this
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg hj, smul_zero]) (fun h => absurd hi h), if_pos rfl] at this
    exact (smul_eq_zero.1 this).resolve_right hu0
  haveI : Finite ι := hli.finite
  haveI := Fintype.ofFinite ι
  obtain ⟨t, ht⟩ := exists_factor σ τ s p hps hp K h0 B
  rw [ht A a ha fun i => hA (s i), ht A' a' ha' fun i => hA' (s i)]
  ring

end Trace

section Split

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem levOp_nat {X : Type} [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ H W) (τ : Representation ℂ H X)
    (s : W →ₗ[ℂ] X) (hs : ∀ h w, s (σ h w) = τ h (s w)) (K₀ K : Subgroup H) (a : H → ℂ)
    (ha : {q : H ⧸ K | a q.out ≠ 0}.Finite) (w : W) :
    levOp τ K₀ K a LinearMap.id (s w) = s (levOp σ K₀ K a LinearMap.id w) := by
  rw [LevOpTmul.levOp_apply τ K₀ K a _ ha.toFinset (fun q hq => by simpa using hq),
    LevOpTmul.levOp_apply σ K₀ K a _ ha.toFinset (fun q hq => by simpa using hq)]
  simp only [map_smul, map_sum, hs, LinearMap.id_apply]

variable (ι : H →* G) (r : G →* H) (hr : ∀ h, r (ι h) = h) (hc : ∀ x ∈ r.ker, ∀ h, Commute x (ι h))
  {U : Subgroup G} {K : Subgroup H} (hK1 : ∀ k ∈ K, ι k ∈ U) (hK2 : ∀ k ∈ U, r k ∈ K)

include hr in

theorem exists_split (g : G) : ∃ x : r.ker, g = ι (r g) * x :=
  ⟨⟨(ι (r g))⁻¹ * g, by rw [MonoidHom.mem_ker, map_mul, map_inv, hr, inv_mul_cancel]⟩, by simp⟩

include hr hc hK1 hK2 in

theorem mk_eq_iff (h h' : H) (x x' : r.ker) :
    ((ι h * x : G) : G ⧸ U) = (ι h' * x' : G) ↔
      (h : H ⧸ K) = h' ∧ (x : r.ker ⧸ U.subgroupOf r.ker) = x' := by
  simp only [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have e : (ι h * x : G)⁻¹ * (ι h' * x') = ι (h⁻¹ * h') * ((x⁻¹ * x' : r.ker) : G) := by
    have := (hc _ (x⁻¹).2 (h⁻¹ * h')).eq
    simp only [Subgroup.coe_inv, Subgroup.coe_mul, map_mul, map_inv] at this ⊢
    rw [mul_inv_rev, ← mul_assoc _ (x : G)⁻¹, ← this]
    group
  rw [e]
  constructor
  · intro hm
    have h1 : h⁻¹ * h' ∈ K := by
      have := hK2 _ hm
      rwa [map_mul, hr, (x⁻¹ * x').2, mul_one] at this
    exact ⟨h1, (U.mul_mem_cancel_left (hK1 _ h1)).1 hm⟩
  · rintro ⟨h1, h2⟩
    exact U.mul_mem (hK1 _ h1) h2

include hr hc hK1 hK2 in

theorem levOp_split (ρ : Representation ℂ G V) (U₀ : Subgroup G) (K₀ : Subgroup H) (h0 : K.relIndex K₀ ≠ 0)
    (F : G → ℂ) (a : H → ℂ) (b : r.ker → ℂ) (hF : ∀ h (x : r.ker), F (ι h * x) = a h * b x)
    (hFr : ∀ k ∈ U, ∀ x, F (x * k) = F x) (har : ∀ k ∈ K, ∀ x, a (x * k) = a x)
    (hbr : ∀ k ∈ U.subgroupOf r.ker, ∀ x, b (x * k) = b x)
    (ha : {q : H ⧸ K | a q.out ≠ 0}.Finite) (hb : {q : r.ker ⧸ U.subgroupOf r.ker | b q.out ≠ 0}.Finite)
    (v : V) (hv : v ∈ fixed ρ U) :
    levOp ρ U₀ U F LinearMap.id v = levOp (ρ.comp ι) K₀ K a LinearMap.id
      ((((U.relIndex U₀ : ℕ) : ℂ)⁻¹ * (K.relIndex K₀ : ℕ)) •
        levOp (ρ.comp r.ker.subtype) (U.subgroupOf r.ker) (U.subgroupOf r.ker) b LinearMap.id v) := by
  have hv' := (GlobalTheory.TwTrLin.mem_fixed_iff ρ U v).1 hv
  have t3 := LevOpTmul.term_mk ρ U F hFr v hv'
  have t1 : ∀ g : H, a (g : H ⧸ K).out = a g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk, har _ k.2]
  have t2 : ∀ g : r.ker, b (g : r.ker ⧸ U.subgroupOf r.ker).out = b g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf r.ker) g
    rw [hk, hbr _ k.2]
  let e : (H ⧸ K) × (r.ker ⧸ U.subgroupOf r.ker) → G ⧸ U := fun p => ((ι p.1.out * (p.2.out : r.ker) : G) : G ⧸ U)
  have he : Function.Injective e := by
    intro p q h
    have := (mk_eq_iff ι r hr hc hK1 hK2 _ _ _ _).1 h
    simp only [QuotientGroup.out_eq'] at this
    exact Prod.ext this.1 this.2
  have h0' : ((K.relIndex K₀ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h0
  rw [LevOpTmul.levOp_apply _ K₀ K a _ ha.toFinset (fun q hq => by simpa using hq),
    LevOpTmul.levOp_apply _ _ _ b _ hb.toFinset (fun q hq => by simpa using hq),
    LevOpTmul.levOp_apply ρ _ _ _ _ ((ha.toFinset ×ˢ hb.toFinset).image e) ?_,
    Finset.sum_image (fun p _ q _ h => he h), Finset.sum_product]
  · simp only [LinearMap.id_apply, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul, map_smul, map_sum,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    simp only [e]
    rw [(t3 _).1, (t3 _).2, hF, map_mul]
    simp only [smul_smul]
    congr 1
    field_simp
  · intro q hq
    obtain ⟨x, hx⟩ := exists_split ι r hr q.out
    refine Finset.mem_image.2 ⟨((r q.out : H ⧸ K), (x : r.ker ⧸ U.subgroupOf r.ker)), ?_, ?_⟩
    · simp only [Finset.mem_product, Set.Finite.mem_toFinset, Set.mem_setOf_eq, t1, t2]
      rw [hx, hF] at hq
      exact mul_ne_zero_iff.1 hq
    · conv_rhs => rw [← QuotientGroup.out_eq' q, hx]
      exact (mk_eq_iff ι r hr hc hK1 hK2 _ _ _ _).2 ⟨QuotientGroup.out_eq' _, QuotientGroup.out_eq' _⟩

include hr hc hK1 hK2 in

theorem trOn_levOp_cross (ρ : Representation ℂ G V) (X : Submodule ℂ V) (hX : ∀ g, ∀ v ∈ X, ρ g v ∈ X)
    (σ : Representation ℂ H W) [σ.IsIrreducible] (hiso : X ≤ LocUniq.isoPart σ (ρ.comp ι))
    (U₀ : Subgroup G) (K₀ : Subgroup H) (h0 : K.relIndex K₀ ≠ 0)
    (F F' : G → ℂ) (a a' : H → ℂ) (b : r.ker → ℂ) (hF : ∀ h (x : r.ker), F (ι h * x) = a h * b x)
    (hF' : ∀ h (x : r.ker), F' (ι h * x) = a' h * b x)
    (hFr : ∀ k ∈ U, ∀ x, F (x * k) = F x) (hFr' : ∀ k ∈ U, ∀ x, F' (x * k) = F' x)
    (hai : ∀ k ∈ K, ∀ x, a (k * x) = a x ∧ a (x * k) = a x) (hai' : ∀ k ∈ K, ∀ x, a' (k * x) = a' x ∧ a' (x * k) = a' x)
    (hbi : ∀ k ∈ U.subgroupOf r.ker, ∀ x, b (k * x) = b x ∧ b (x * k) = b x)
    (ha : {q : H ⧸ K | a q.out ≠ 0}.Finite) (ha' : {q : H ⧸ K | a' q.out ≠ 0}.Finite)
    (hb : {q : r.ker ⧸ U.subgroupOf r.ker | b q.out ≠ 0}.Finite) :
    trOn (X ⊓ fixed ρ U) (levOp ρ U₀ U F LinearMap.id) * twTr σ K₀ K a' LinearMap.id =
      twTr σ K₀ K a LinearMap.id * trOn (X ⊓ fixed ρ U) (levOp ρ U₀ U F' LinearMap.id) := by
  let L := U.subgroupOf r.ker
  let ρR : Representation ℂ r.ker V := ρ.comp r.ker.subtype
  let ρH : Representation ℂ H V := ρ.comp ι
  have hcomm : ∀ (h : H) (x : r.ker) v, ρH h (ρR x v) = ρR x (ρH h v) := fun h x v => by
    change (ρ (ι h) * ρ x) v = (ρ x * ρ (ι h)) v
    rw [← map_mul, ← map_mul, (hc _ x.2 h).eq]
  let X' : Submodule ℂ V := X ⊓ fixed ρR L
  have hX' : ∀ h, X' ≤ X'.comap (ρH h) := fun h v hv => by
    refine ⟨hX _ _ hv.1, (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).2 fun k hk => ?_⟩
    rw [← hcomm, (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).1 hv.2 k hk]
  let τ : Representation ℂ H X' := ρH.subrepresentation X' hX'
  let j : τ.IntertwiningMap ρH := ⟨X'.subtype, fun _ => rfl⟩
  let c : ℂ := ((U.relIndex U₀ : ℕ) : ℂ)⁻¹ * (K.relIndex K₀ : ℕ)
  let B₀ : V →ₗ[ℂ] V := c • levOp ρR L L b LinearMap.id
  have hB₀ : ∀ v ∈ X', B₀ v ∈ X' := fun v hv => by
    refine X'.smul_mem c ⟨?_, GlobalTheory.TwTrLin.levOp_mapsTo ρR L L _ b hb (fun k hk x => (hbi k hk x).1)
      (fun k hk x => (hbi k hk x).2) (fun _ h => h) v hv.2⟩
    rw [LevOpTmul.levOp_apply _ _ _ b _ hb.toFinset (fun q hq => by simpa using hq)]
    exact X.smul_mem _ (X.sum_mem fun q _ => X.smul_mem _ (hX _ _ hv.1))
  let B : τ.IntertwiningMap τ := ⟨B₀.restrict hB₀, fun h => LinearMap.ext fun v => Subtype.ext (by
    change c • levOp ρR L L b LinearMap.id (ρH h v.1) = ρH h (c • levOp ρR L L b LinearMap.id v.1)
    rw [map_smul, levOp_nat ρR ρR (ρH h) (hcomm h) L L b hb])⟩
  have hY : X ⊓ fixed ρ U = (fixed τ K).map X'.subtype := by
    ext v
    constructor
    · rintro ⟨h1, h2⟩
      have h3 := (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).1 h2
      exact ⟨⟨v, h1, (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).2 fun k hk => h3 _ hk⟩,
        (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).2 fun k hk => Subtype.ext (h3 _ (hK1 k hk)), rfl⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.2.1, (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).2 fun k hk => ?_⟩
      obtain ⟨x, hx⟩ := exists_split ι r hr k
      have hxU : x ∈ L := by
        have : ι (r k) * x ∈ U := hx ▸ hk
        exact (U.mul_mem_cancel_left (hK1 _ (hK2 k hk))).1 this
      have h1 : ρ x v.1 = v.1 := (GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).1 v.2.2 x hxU
      have h2 : ρ (ι (r k)) v.1 = v.1 :=
        congrArg Subtype.val ((GlobalTheory.TwTrLin.mem_fixed_iff _ _ _).1 hv _ (hK2 k hk))
      change ρ k v.1 = v.1
      rw [hx, map_mul, Module.End.mul_apply, h1, h2]
  have key : ∀ (F : G → ℂ) (a : H → ℂ), (∀ h (x : r.ker), F (ι h * x) = a h * b x) → (∀ k ∈ U, ∀ x, F (x * k) = F x) →
      (∀ k ∈ K, ∀ x, a (x * k) = a x) → {q : H ⧸ K | a q.out ≠ 0}.Finite →
      trOn (X ⊓ fixed ρ U) (levOp ρ U₀ U F LinearMap.id) =
        trOn (fixed τ K) (levOp τ K₀ K a LinearMap.id ∘ₗ B.toLinearMap) := fun F a hF hFr har ha => by
    rw [hY]
    refine trOn_map _ X'.injective_subtype _ _ _ fun v hv => ?_
    have hv' : X'.subtype v ∈ X ⊓ fixed ρ U := hY ▸ ⟨v, hv, rfl⟩
    rw [levOp_split ι r hr hc hK1 hK2 ρ U₀ K₀ h0 F a b hF hFr har (fun k hk x => (hbi k hk x).2) ha hb _ hv'.2,
      LinearMap.comp_apply, ← levOp_nat τ ρH X'.subtype (fun _ _ => rfl) K₀ K a ha]
    rfl
  rw [key F a hF hFr (fun k hk x => (hai k hk x).2) ha, key F' a' hF' hFr' (fun k hk x => (hai' k hk x).2) ha']
  exact trOn_cross σ τ ρH j X'.injective_subtype (fun x => hiso x.2.1) K B _ _ _ _
    (GlobalTheory.TwTrLin.levOp_mapsTo σ K₀ K _ a ha (fun k hk x => (hai k hk x).1) (fun k hk x => (hai k hk x).2) fun _ h => h)
    (GlobalTheory.TwTrLin.levOp_mapsTo σ K₀ K _ a' ha' (fun k hk x => (hai' k hk x).1) (fun k hk x => (hai' k hk x).2)
      fun _ h => h)
    (fun s w => levOp_nat σ τ s.toLinearMap (fun h w => LinearMap.congr_fun (s.isIntertwining' h) w) K₀ K a ha w)
    (fun s w => levOp_nat σ τ s.toLinearMap (fun h w => LinearMap.congr_fun (s.isIntertwining' h) w) K₀ K a' ha' w)

end Split

end GlobalTheory.BCT.Peel

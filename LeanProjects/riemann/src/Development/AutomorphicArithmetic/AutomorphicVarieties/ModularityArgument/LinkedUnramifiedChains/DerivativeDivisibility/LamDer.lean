import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.AbsGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSqz
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteOfApprox

set_option linter.overlappingInstances false

open Polynomial IsLocalRing UpperTheory.V.Alg

namespace UpperTheory.V.J

private theorem smod_pow {O : Type} [CommRing O] (π a b : O) (n : ℕ)
    (h : a ≡ b [SMOD ((Ideal.span {π}) ^ n • ⊤ : Submodule O O)]) : ∃ e, a - b = π ^ n * e := by
  have h1 := SModEq.sub_mem.1 h
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h1
  obtain ⟨e, he⟩ := h1
  exact ⟨e, by rw [← he, mul_comm]⟩

private theorem eq_top_of_mod {O M : Type} [CommRing O] (π : O) [IsPrecomplete (Ideal.span {π}) O] [AddCommGroup M]
    [Module O M] (hsep : ∀ x : M, (∀ n : ℕ, ∃ y : M, x = π ^ n • y) → x = 0) (S : Submodule O M) (hS : S.FG)
    (h : ∀ x : M, ∃ s ∈ S, ∃ y : M, x = s + π • y) : S = ⊤ := by
  obtain ⟨s, t, ht⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hS
  have h' : ∀ x : M, ∃ (c : Fin s → O) (y : M), x = ∑ j, c j • t j + π • y := fun x => by
    obtain ⟨a, ha, y, rfl⟩ := h x
    rw [← ht] at ha
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 ha
    exact ⟨c, y, rfl⟩
  choose C Y hCY using h'
  refine eq_top_iff.2 fun x _ => ?_
  let r : ℕ → M := fun k => Y^[k] x
  have hr : ∀ k, r (k + 1) = Y (r k) := fun k => Function.iterate_succ_apply' Y k x
  let P : ℕ → Fin s → O := fun N j => ∑ k ∈ Finset.range N, π ^ k * C (r k) j
  have hP : ∀ N j, P (N + 1) j = P N j + π ^ N * C (r N) j := fun N j => Finset.sum_range_succ _ _
  have hx : ∀ N, x = ∑ j, P N j • t j + π ^ N • r N := fun N => by
    induction N with
    | zero =>
      simp only [P, Finset.range_zero, Finset.sum_empty, zero_smul, Finset.sum_const_zero, pow_zero, one_smul, zero_add]
      rfl
    | succ N ih =>
      have e := hCY (r N)
      rw [← hr] at e
      have e2 : ∑ j, P (N + 1) j • t j = ∑ j, P N j • t j + π ^ N • ∑ j, C (r N) j • t j := by
        rw [Finset.smul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hP, add_smul, mul_smul]
      calc x = ∑ j, P N j • t j + π ^ N • (∑ j, C (r N) j • t j + π • r (N + 1)) := by rw [← e]; exact ih
        _ = _ := by rw [e2, smul_add, smul_smul, ← pow_succ, add_assoc]
  have hstep : ∀ j m n, m ≤ n → ∃ b, P n j - P m j = π ^ m * b := fun j m n hmn => by
    induction n, hmn using Nat.le_induction with
    | base => exact ⟨0, by simp⟩
    | succ n hmn ih =>
      obtain ⟨b, hb⟩ := ih
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      refine ⟨b + π ^ k * C (r (m + k)) j, ?_⟩
      rw [hP, add_sub_right_comm, hb, pow_add]
      ring
  have hL : ∀ j, ∃ L, ∀ n, P n j ≡ L [SMOD ((Ideal.span {π}) ^ n • ⊤ : Submodule O O)] := fun j =>
    IsPrecomplete.prec' (fun n => P n j) fun {m n} hmn => by
      obtain ⟨b, hb⟩ := hstep j m n hmn
      refine SModEq.sub_mem.2 ?_
      rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
      exact ⟨-b, by rw [show P m j - P n j = -(P n j - P m j) by ring, hb]; ring⟩
  choose L hL using hL
  have h0 : x - ∑ j, L j • t j = 0 := hsep _ fun n => by
    choose e he using fun j => smod_pow π _ _ n (hL j n)
    refine ⟨∑ j, e j • t j + r n, ?_⟩
    have e3 : ∀ j, P n j • t j = L j • t j + π ^ n • e j • t j := fun j => by
      rw [smul_smul, ← he j, ← add_smul]
      congr 1
      ring
    rw [smul_add, Finset.smul_sum]
    conv_lhs => rw [hx n]
    simp only [e3, Finset.sum_add_distrib]
    abel
  rw [← ht, sub_eq_zero.1 h0]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

private theorem aeval_split {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (a : R) (Q : O[X]) :
    aeval a Q = algebraMap O R (Q.coeff 0) + a * aeval a Q.divX := by
  have h := congrArg (aeval a) (Polynomial.divX_mul_X_add Q)
  simp only [map_add, map_mul, aeval_X, aeval_C] at h
  linear_combination (-1 : R) * h

private theorem pow_mem_of_poly {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] (π : O) (a : R)
    (ha : a ∈ maximalIdeal R) (j : ℕ) : ∀ (Q : O[X]) (e : ℕ), (∀ i < j, π ∣ Q.coeff i) → IsUnit (algebraMap O R (Q.coeff j)) →
      a ^ e * aeval a Q ∈ Ideal.span {algebraMap O R π} → a ^ (e + j) ∈ Ideal.span {algebraMap O R π} := by
  induction j with
  | zero =>
    intro Q e _ hu hQ
    have hsplit := aeval_split (O := O) a Q
    have hw : IsUnit (aeval a Q) := by
      by_contra hn
      have h1 : aeval a Q ∈ maximalIdeal R := (mem_maximalIdeal _).2 hn
      rw [hsplit] at h1
      have h2 := (Ideal.add_mem_iff_left _ (Ideal.mul_mem_right _ _ ha)).1 h1
      exact (mem_maximalIdeal _).1 h2 hu
    obtain ⟨w, hw⟩ := hw
    have := Ideal.mul_mem_right ((w⁻¹ : Rˣ) : R) _ hQ
    rw [← hw, mul_assoc, Units.mul_inv, mul_one] at this
    simpa using this
  | succ j ih =>
    intro Q e hd hu hQ
    have hsplit := aeval_split (O := O) a Q
    obtain ⟨b, hb⟩ := hd 0 (Nat.succ_pos j)
    have h1 : a ^ (e + 1) * aeval a Q.divX ∈ Ideal.span {algebraMap O R π} := by
      have h2 : a ^ (e + 1) * aeval a Q.divX = a ^ e * aeval a Q - algebraMap O R π * (a ^ e * algebraMap O R b) := by
        rw [hsplit, hb, map_mul]
        ring
      rw [h2]
      exact Ideal.sub_mem _ hQ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    have := ih Q.divX (e + 1) (fun i hi => by
      rw [Polynomial.coeff_divX]
      exact hd (i + 1) (Nat.succ_lt_succ hi)) (by rwa [Polynomial.coeff_divX]) h1
    rwa [show e + 1 + j = e + (j + 1) by ring] at this

private theorem finite_of_alg {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing R] [IsDomain R] [Algebra O R] [IsCO O R] (hinj : Function.Injective (algebraMap O R))
    (hal : ∀ a : R, ∃ P : O[X], P ≠ 0 ∧ aeval a P = 0) : Module.Finite O R :=
  _root_.UpperTheory.Reformulated.B.Ra2.finite_of_alg hinj hal

private theorem exists_sqz {O Λ A N : Type} [CommRing O] [IsLocalRing O] [CommRing Λ] [Algebra O Λ] [CommRing A] [Algebra O A]
    [IsCO O A] [AddCommGroup N] [Module A N] [Module O N] [IsScalarTower O A N] [Module.Finite A N] (p : Λ →ₐ[O] A)
    (d : Λ →ₗ[O] N) (hd : ∀ f g, d (f * g) = p f • d g + p g • d f) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra O T) (_ : IsCO O T) (f₀ f₁ : Λ →ₐ[O] T), ∀ a, f₀ a = f₁ a ↔ d a = 0 := by
  letI : Module Aᵐᵒᵖ N := Module.compHom N ((RingHom.id A).fromOpposite fun x y => Commute.all x y)
  haveI : IsCentralScalar A N := ⟨fun _ _ => rfl⟩
  haveI : SMulCommClass A Aᵐᵒᵖ N := ⟨fun a b n => smul_comm a (MulOpposite.unop b) n⟩
  haveI : IsScalarTower O Aᵐᵒᵖ N := ⟨fun c b n => by
    change (c • MulOpposite.unop b) • n = c • (MulOpposite.unop b • n)
    exact smul_assoc c _ n⟩
  letI : Algebra O (TrivSqZeroExt A N) := TrivSqZeroExt.algebra' O A N
  have h1 : d 1 = 0 := by
    have := hd 1 1
    simp only [mul_one, map_one, one_smul] at this
    exact left_eq_add.1 this
  let f₁ : Λ →ₐ[O] TrivSqZeroExt A N :=
    { toFun := fun a => TrivSqZeroExt.inl (p a) + TrivSqZeroExt.inr (d a)
      map_one' := TrivSqZeroExt.ext (by simp) (by simp [h1])
      map_zero' := TrivSqZeroExt.ext (by simp) (by simp)
      map_add' := fun a b => TrivSqZeroExt.ext (by simp) (by simp)
      map_mul' := fun a b => by
        refine TrivSqZeroExt.ext (by simp) ?_
        rw [TrivSqZeroExt.snd_mul]
        simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, TrivSqZeroExt.snd_add,
          TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
        rw [hd, op_smul_eq_smul]
      commutes' := fun c => by
        refine TrivSqZeroExt.ext ?_ ?_
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
          exact p.commutes c
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
          rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]
          rfl }
  refine ⟨TrivSqZeroExt A N, inferInstance, inferInstance, co_sqz O A N fun _ => rfl,
    (TrivSqZeroExt.inlAlgHom O A N).comp p, f₁, fun a => ⟨fun h => ?_, fun h => ?_⟩⟩
  · simpa [f₁] using (congrArg TrivSqZeroExt.snd h).symm
  · exact TrivSqZeroExt.ext (by simp [f₁]) (by simp [f₁, h])

private theorem exists_pair_of_der {O Λ K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing Λ] [Algebra O Λ] [IsCO O Λ] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) (hal : ∀ a : K, ∃ P : O[X], P ≠ 0 ∧ aeval a P = 0) (p : Λ →ₐ[O] K)
    (d : Λ →ₗ[O] K) (hd : ∀ f g, d (f * g) = p f * d g + p g * d f) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra O T) (_ : IsCO O T) (f₀ f₁ : Λ →ₐ[O] T), ∀ a, f₀ a = f₁ a ↔ d a = 0 := by
  classical
  have hsurj : Function.Surjective p.rangeRestrict := p.rangeRestrict_surjective
  haveI : IsCO O p.range := co_quot O Λ p.range p.rangeRestrict hsurj
  have hfin : Module.Finite O p.range := finite_of_alg
    (fun a b h => hinj (congrArg Subtype.val h))
    fun a => by
      obtain ⟨P, hP, h0⟩ := hal a
      exact ⟨P, hP, Subtype.ext (by rw [← Subalgebra.aeval_coe]; simpa using h0)⟩
  obtain ⟨G, hG⟩ := hfin.fg_top
  choose ℓ hℓ using hsurj
  obtain ⟨Q, hQ⟩ : (RingHom.ker p).FG := IsNoetherian.noetherian _
  let N : Submodule p.range K := Submodule.span p.range (d '' ((G.image ℓ : Finset Λ) ∪ Q : Finset Λ))
  have hsub : ∀ f ∈ (G.image ℓ : Finset Λ) ∪ Q, d f ∈ N := fun f hf =>
    Submodule.subset_span ⟨f, by exact_mod_cast hf, rfl⟩
  have hq : ∀ z ∈ Submodule.span Λ (Q : Set Λ), p z = 0 ∧ d z ∈ N := fun z hz => by
    induction hz using Submodule.span_induction with
    | mem g hg =>
      refine ⟨?_, hsub g (Finset.mem_union_right _ hg)⟩
      have : g ∈ RingHom.ker p := hQ ▸ Submodule.subset_span hg
      exact this
    | zero => exact ⟨map_zero p, by rw [map_zero]; exact zero_mem _⟩
    | add x y _ _ hx hy =>
      exact ⟨by rw [map_add, hx.1, hy.1, add_zero], by rw [map_add]; exact add_mem hx.2 hy.2⟩
    | smul b y _ hy =>
      refine ⟨by rw [smul_eq_mul, map_mul, hy.1, mul_zero], ?_⟩
      rw [smul_eq_mul, hd, hy.1, zero_mul, add_zero]
      exact N.smul_mem (p.rangeRestrict b) hy.2
  have hl : ∀ y ∈ Submodule.span O (G : Set p.range), ∃ g, p.rangeRestrict g = y ∧ d g ∈ N := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      exact ⟨ℓ y, hℓ y, hsub _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy))⟩
    | zero => exact ⟨0, map_zero _, by rw [map_zero]; exact zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨g, rfl, hg⟩ := hx
      obtain ⟨g', rfl, hg'⟩ := hy
      exact ⟨g + g', map_add _ _ _, by rw [map_add]; exact add_mem hg hg'⟩
    | smul c y _ hy =>
      obtain ⟨g, rfl, hg⟩ := hy
      refine ⟨c • g, map_smul _ _ _, ?_⟩
      rw [map_smul, ← algebraMap_smul p.range c (d g)]
      exact N.smul_mem _ hg
  have key : ∀ f, d f ∈ N := fun f => by
    obtain ⟨g, hg, hgN⟩ := hl (p.rangeRestrict f) (by rw [hG]; trivial)
    have h1 : f - g ∈ Submodule.span Λ (Q : Set Λ) := by
      have h2 : p (f - g) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.2 (congrArg Subtype.val hg).symm
      have : f - g ∈ RingHom.ker p := RingHom.mem_ker.2 h2
      rw [← hQ] at this
      exact this
    have := add_mem hgN (hq _ h1).2
    rwa [← map_add, add_sub_cancel] at this
  let d' : Λ →ₗ[O] N :=
    { toFun := fun f => ⟨d f, key f⟩
      map_add' := fun a b => Subtype.ext (map_add d a b)
      map_smul' := fun c a => Subtype.ext (map_smul d c a) }
  haveI : Module.Finite p.range N := Module.Finite.iff_fg.2 (Submodule.fg_span (Set.Finite.image _ (Finset.finite_toSet _)))
  obtain ⟨T, i1, i2, i3, f₀, f₁, hf⟩ := exists_sqz p.rangeRestrict d' fun f g => Subtype.ext (hd f g)
  exact ⟨T, i1, i2, i3, f₀, f₁, fun a => (hf a).trans ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩⟩

private theorem map_mem_max {O Λ T : Type} [CommRing O] [IsLocalRing O] [CommRing Λ] [Algebra O Λ] [IsCO O Λ] [CommRing T]
    [Algebra O T] [IsCO O T] (f : Λ →ₐ[O] T) {x : Λ} (hx : x ∈ maximalIdeal Λ) : f x ∈ maximalIdeal T := by
  by_contra hn
  obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) (f x)
  have hbu : IsUnit (algebraMap O T b) := by
    by_contra h
    have h2 := add_mem hb ((mem_maximalIdeal _).2 h)
    rw [sub_add_cancel] at h2
    exact hn h2
  have hb' : IsUnit (algebraMap O Λ b) := (isUnit_of_map_unit (algebraMap O T) b hbu).map _
  have hu : IsUnit (x - algebraMap O Λ b) := by
    by_contra h
    have h2 := (mem_maximalIdeal _).2 h
    have h3 := sub_mem hx h2
    rw [sub_sub_cancel] at h3
    exact (mem_maximalIdeal _).1 h3 hb'
  have h3 := hu.map f
  rw [map_sub, f.commutes] at h3
  exact (mem_maximalIdeal _).1 hb h3

private theorem adic_push {O Λ T Γ : Type} [CommRing O] [IsLocalRing O] [CommRing Λ] [Algebra O Λ] [IsCO O Λ] [CommRing T]
    [Algebra O T] [IsCO O T] [TopologicalSpace Γ] (f : Λ →ₐ[O] T) {u : Γ → Λ} (h : AdicCont (maximalIdeal Λ) u) :
    AdicCont (maximalIdeal T) fun g => f (u g) := fun N => by
  have hm : Ideal.map (f : Λ →+* T) (maximalIdeal Λ ^ N) ≤ maximalIdeal T ^ N := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 (map_mem_max f hx)) N
  let φ : Λ ⧸ maximalIdeal Λ ^ N →+* T ⧸ maximalIdeal T ^ N :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (f : Λ →+* T)) fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.2 (hm (Ideal.mem_map_of_mem _ ha))
  exact (h N).comp φ

private theorem inert_push {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    {n : ℕ} (r : W.Resid F O n) (Λ : W.LamObj r) {T : Type} [CommRing T] [Algebra O T] [IsCO O T] (f : Λ.Λ →ₐ[O] T) :
    W.IsInert r fun v i => W.pushCh (f : Λ.Λ →+* T) (Λ.κ v i) := fun v i => by
  obtain ⟨ψ, h, hk⟩ := Λ.inert v i
  refine ⟨W.pushCh (f : Λ.Λ →+* T) ψ, ⟨adic_push f h.cont, fun g => ?_, fun g => ?_⟩, ?_⟩
  · exact (res_map f _).trans (h.red g)
  · exact (congrArg f (h.mu g)).trans (f.commutes _)
  · change W.pushCh _ (Λ.κ v i) = _
    rw [hk]
    rfl

end UpperTheory.V.J

open UpperTheory.V.J UpperTheory.V.W UpperTheory.V.HV Formalism.ConjugateSelfDual ReciprocityTheory.Gal in
theorem UpperTheory.V.J.lamDer :
    UpperTheory.V.J.LamDer := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B Λ x m _ δ hδ hk a
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.abelian₂.dvr_finite l c.O).1
  have hinj : Function.Injective (algebraMap c.O (Qbar l)) := Subtype.val_injective
  have hal : ∀ a : Qbar l, ∃ P : c.O[X], P ≠ 0 ∧ aeval a P = 0 := fun a => by
    have h1 : IsAlgebraic ℚ_[l] a := Algebra.IsAlgebraic.isAlgebraic a
    have h2 : IsAlgebraic ℤ_[l] a := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] (Qbar l)).2 h1
    have h3 : IsAlgebraic c.O a := h2.extendScalars (UpperTheory.V.abelian₂.dvr_finite l c.O).2.2.2.1
    exact h3
  let t := Λ.toPair B.u
  let d : Λ.Λ →ₗ[c.O] Qbar l := δ.comp t.toLinearMap
  obtain ⟨T, _, _, _, f₀, f₁, hf⟩ := exists_pair_of_der hinj hal (x.comp t) d fun f g => by
    have := hδ (t f) (t g)
    simpa [d, map_mul] using this
  have hκ : ∀ v i (g : V.frame.Iv v), d ((Λ.κ v i g : Λ.Λˣ) : Λ.Λ) = 0 := fun v i g => by
    have h1 := congrArg Units.val (DFunLike.congr_fun (W.LamObj.toPair_spec r Λ B.u v i) g)
    have h2 : t ((Λ.κ v i g : Λ.Λˣ) : Λ.Λ) = (B.u.ψ v i g : B.Bˣ) := h1
    change δ (t _) = 0
    rw [h2]
    exact hk v i g g.2
  obtain ⟨u, -, hu⟩ := Λ.univ T _ (inert_push r Λ f₀)
  have e0 := hu f₀ fun _ _ => rfl
  have e1 := hu f₁ fun v i => MonoidHom.ext fun g => Units.ext ((hf _).2 (hκ v i g)).symm
  exact (hf a).1 (by rw [e0, ← e1])

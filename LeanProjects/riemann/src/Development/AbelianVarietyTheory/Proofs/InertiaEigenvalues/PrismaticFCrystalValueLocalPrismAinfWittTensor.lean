import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism

namespace GlobalTheory.Prism.LocalValue

theorem exists_basis {A B M N ι : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [Fintype ι] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u)
    (b : Module.Basis ι A M) : ∃ c : Module.Basis ι B N, ∀ i, c i = u (b i) := by
  classical
  let v : M →ₛₗ[f] (ι → B) :=
    { toFun := fun x i => f (b.equivFun x i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp }
  obtain ⟨S, hS, -⟩ := h _ v
  let Q : (ι → B) →ₗ[B] N := Fintype.linearCombination B fun i => u (b i)
  have hQ : Q.comp S = LinearMap.id := h.hom_ext fun x => by
    rw [LinearMap.comp_apply, hS, LinearMap.id_apply, Fintype.linearCombination_apply]
    conv_rhs => rw [← b.sum_equivFun x, map_sum]
    exact Finset.sum_congr rfl fun i _ => (u.map_smulₛₗ _ _).symm
  have hQ1 : ∀ i, Q (Pi.single i 1) = u (b i) := fun i => by
    simp [Q]
  have hS' : S.comp Q = LinearMap.id := by
    refine (Pi.basisFun B ι).ext fun i => ?_
    rw [LinearMap.comp_apply, Pi.basisFun_apply, hQ1, hS, LinearMap.id_apply]
    ext k
    change f (b.equivFun (b i) k) = _
    rw [b.equivFun_self, Pi.single_apply]
    by_cases hik : i = k
    · simp [hik]
    · simp [hik, Ne.symm hik]
  refine ⟨(Pi.basisFun B ι).map (LinearEquiv.ofLinear Q S hQ hS'), fun i => ?_⟩
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  exact hQ1 i

theorem exists_pow_smul_eq_sum {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι]
    {d : A} {f : A →+* Localization.Away d} {Φ : M →ₛₗ[f] LocalizedModule (Submonoid.powers d) M}
    (h : SemiBC Φ) (b : Module.Basis ι A M) (m : ι → M) (k : ι → ℕ)
    (hm : ∀ i, IsFrac d (Φ (b i)) (m i) (k i)) (x : M) :
    ∃ (r : ℕ) (s : ι → A), d ^ r • x = ∑ i, s i • m i := by
  obtain ⟨c, hc⟩ := exists_basis h b
  have h1 : (LocalizedModule.mk x 1 : LocalizedModule (Submonoid.powers d) M) ∈
      Submodule.span (Localization.Away d)
        (Set.range fun i => (LocalizedModule.mk (m i) 1 : LocalizedModule (Submonoid.powers d) M)) := by
    refine (?_ : (⊤ : Submodule (Localization.Away d) _) ≤ _) Submodule.mem_top
    rw [← c.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h2 : c i = (Localization.mk 1 ⟨d ^ k i, (Submonoid.mem_powers_iff _ _).2 ⟨k i, rfl⟩⟩ :
        Localization.Away d) • (LocalizedModule.mk (m i) 1 : LocalizedModule (Submonoid.powers d) M) := by
      rw [hc, hm i, LocalizedModule.mk_smul_mk, one_smul, mul_one]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨⟨_, t, rfl⟩, ht⟩ := multiple_mem_span_of_mem_localization_span (Submonoid.powers d)
    (Localization.Away d) _ _ h1
  obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 ht
  have h3 : LocalizedModule.mkLinearMap (Submonoid.powers d) M (∑ i, s i • m i) =
      LocalizedModule.mkLinearMap (Submonoid.powers d) M (d ^ t • x) := by
    rw [map_sum, map_smul]
    simp only [map_smul]
    exact hs
  rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_eq] at h3
  obtain ⟨⟨_, a, rfl⟩, ha⟩ := h3
  simp only [one_smul, Submonoid.smul_def] at ha
  refine ⟨a + t, fun i => d ^ a * s i, ?_⟩
  rw [pow_add, mul_smul, ← ha, Finset.smul_sum]
  simp only [mul_smul]

theorem exists_eq_smul {A B M N ι : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [Fintype ι] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u)
    (b : Module.Basis ι A M) {π : A} (hπ : RingHom.ker f = Ideal.span {π}) (x : M) (hx : u x = 0) :
    ∃ y, x = π • y := by
  obtain ⟨c, hc⟩ := exists_basis h b
  have h1 : ∑ i, f (b.equivFun x i) • c i = 0 := by
    rw [← hx]
    conv_rhs => rw [← b.sum_equivFun x, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hc, u.map_smulₛₗ]
  have h2 := Fintype.linearIndependent_iff.1 c.linearIndependent _ h1
  have h3 : ∀ i, ∃ a, a * π = b.equivFun x i := fun i =>
    Ideal.mem_span_singleton'.1 (hπ ▸ (RingHom.mem_ker).2 (h2 i))
  choose a ha using h3
  refine ⟨∑ i, a i • b i, ?_⟩
  conv_lhs => rw [← b.sum_equivFun x]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [← ha, smul_smul, mul_comm]

theorem ennreal_volume_ratio_step_cancel {A B M N : Type} [CommRing A] [CommRing B] [IsDomain B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [Module.Free B N] {f : A →+* B} (u : M →ₛₗ[f] N) {e : A}
    (he : f e ≠ 0) {m n : M} {k i r : ℕ} (h : (e * e) ^ r • (e ^ i • m - e ^ k • n) = 0) {y : N}
    (hy : f e ^ i • y = u n) : f e ^ k • y = u m := by
  have h2 := congrArg u h
  rw [u.map_smulₛₗ, map_sub, u.map_smulₛₗ, u.map_smulₛₗ, map_zero, map_pow, map_pow, map_pow, map_mul,
    ← hy, smul_comm (f e ^ k), ← smul_sub, smul_eq_zero, smul_eq_zero] at h2
  rcases h2 with h2 | h2 | h2
  · exact absurd h2 (pow_ne_zero _ (mul_ne_zero he he))
  · exact absurd h2 (pow_ne_zero _ he)
  · exact (sub_eq_zero.1 h2).symm

theorem general {l : ℕ} {R : Type} [CommRing R] {PS PA : Obj l R} [IsLocalRing PS.A] (io : Hom PS PA)
    {B N : Type} [CommRing B] [IsDomain B] [AddCommGroup N] [Module B N] {f : PA.A →+* B}
    (E : FCrys l R) {j : E.M PA →ₛₗ[f] N} (hj : SemiBC j) (F : N → N)
    (hF : ∀ (d : ↥PA.I), (d : PA.A) ≠ 0 → ∀ (x m : E.M PA) (k : ℕ), IsFrac (d : PA.A) (E.Φ PA d x) m k →
      f d ^ k • F (j x) = j m)
    {Q : PS.A} (hQ : Q ∈ PS.I) (ψ : PS.A →+* B) (hψ : ∀ x, ψ x = f (io.f x)) (hQ0 : ψ Q ≠ 0) :
    ∃ (q : ℕ) (b : Module.Basis (Fin q) PS.A (E.M PS)) (c : Module.Basis (Fin q) B N),
      (∀ i, c i = j (E.tr io (b i))) ∧
      (∀ x, ∃ (k : ℕ) (m : E.M PS), ψ Q ^ k • F (j (E.tr io x)) = j (E.tr io m)) ∧
      (∀ x, ∃ (k : ℕ) (s : Fin q → PS.A), ψ Q ^ k • j (E.tr io x) = ∑ i, ψ (s i) • F (c i)) := by
  have := E.fin PS
  have := E.proj PS
  have : Module.Free PS.A (E.M PS) := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis PS.A (E.M PS)
  obtain ⟨c', hc'⟩ := exists_basis (E.tr_bc io) b
  obtain ⟨c, hc⟩ := exists_basis hj c'
  have hcb : ∀ i, c i = j (E.tr io (b i)) := fun i => by rw [hc, hc']
  have : Module.Free B N := Module.Free.of_basis c
  have hsm : ∀ (s : PS.A) (x : E.M PS), j (E.tr io (s • x)) = ψ s • j (E.tr io x) := fun s x => by
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hψ]
  have key : ∀ (x m : E.M PS) (k : ℕ), IsFrac Q (E.Φ PS ⟨Q, hQ⟩ x) m k →
      ψ Q ^ k • F (j (E.tr io x)) = j (E.tr io m) := by
    intro x m k h
    have h0 : io.f Q ≠ 0 := fun h0 => hQ0 (by rw [hψ, h0, map_zero])
    obtain ⟨n, i, hn⟩ := exists_isFrac (io.f Q) (E.Φ PA ⟨io.f Q, io.f_I Q hQ⟩ (E.tr io x))
    obtain ⟨r, hr⟩ := E.Φ_nat io ⟨Q, hQ⟩ ⟨io.f Q, io.f_I Q hQ⟩ x m k n i h hn
    have h1 := hF ⟨io.f Q, io.f_I Q hQ⟩ h0 _ n i hn
    rw [hψ] at hQ0 ⊢
    exact ennreal_volume_ratio_step_cancel j hQ0 hr h1
  refine ⟨_, b, c, hcb, fun x => ?_, fun x => ?_⟩
  · obtain ⟨m, k, h⟩ := exists_isFrac Q (E.Φ PS ⟨Q, hQ⟩ x)
    exact ⟨k, m, key x m k h⟩
  · choose m k hm using fun i => exists_isFrac Q (E.Φ PS ⟨Q, hQ⟩ (b i))
    obtain ⟨r, s, hs⟩ := exists_pow_smul_eq_sum (E.Φ_bc PS ⟨Q, hQ⟩) b m k hm x
    refine ⟨r, fun i => s i * Q ^ k i, ?_⟩
    have hs' : Q ^ r • x = ∑ i, s i • m i := hs
    rw [← map_pow, ← hsm, hs', map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsm, ← key _ _ _ (hm i), hcb, smul_smul, map_mul, map_pow]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (PS PW : Obj l ↥(OL K)) (ev : Hom PS PW) (ioH : Hom PS (ainfObj K)) (gH : ↥(GK K) → Hom PS PS) (π Q : PS.A) (ψ : PS.A →+* WCb l), (∀ x, ψ x = inclW l (ainfId K (ioH.f x))) → (∀ g, ioH.comp (gH g) = (ainfHom K g).comp ioH) → (∀ g, ev.comp (gH g) = ev) → RingHom.ker ev.f = Ideal.span {π} → Q ∈ PS.I → IsLocalRing PS.A → ψ Q ≠ 0 → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (E : FCrys l ↥(OL K)) (j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K E (ainfObj K) (ainfId K) T ρ j → ∃ (q : ℕ) (b : Module.Basis (Fin q) PS.A (E.M PS)) (c : Module.Basis (Fin q) (WCb l) (WCb l ⊗[ℤ_[l]] T)), (∀ i, c i = j (E.tr ioH (b i))) ∧ (∀ x, ∃ (k : ℕ) (m : E.M PS), ψ Q ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (E.tr ioH x)) = j (E.tr ioH m)) ∧ (∀ x, ∃ (k : ℕ) (s : Fin q → PS.A), ψ Q ^ k • j (E.tr ioH x) = ∑ i, ψ (s i) • TensorProduct.map (frobW l).toLinearMap LinearMap.id (c i)) ∧ (∀ (g : ↥(GK K)) x, TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ g) (j (E.tr ioH x)) = j (E.tr ioH (E.tr (gH g) x))) ∧ (∀ g x, ∃ y, E.tr (gH g) x - x = π • y) := by
  intro l _ K PS PW ev ioH gH π Q ψ hψ hg hev hker hQ hloc hQ0 T _ _ ρ E j H
  obtain ⟨q, b, c, h1, h2, h3⟩ := general ioH E H.bc
    (fun y => TensorProduct.map (frobW l).toLinearMap LinearMap.id y) H.j_φ hQ ψ hψ hQ0
  refine ⟨q, b, c, h1, h2, h3, fun g x => ?_, fun g x => ?_⟩
  · have h4 : E.tr ioH (E.tr (gH g) x) = E.tr (ainfHom K g) (E.tr ioH x) :=
      ((E.tr_comp ioH (gH g) x).symm.trans (congrArg (fun f => E.tr f x) (hg g))).trans
        (E.tr_comp (ainfHom K g) ioH x)
    exact (H.j_act g (E.tr ioH x)).symm.trans (congrArg j h4.symm)
  · refine exists_eq_smul (E.tr_bc ev) b hker _ ?_
    rw [map_sub, ← E.tr_comp, hev, sub_self]

end GlobalTheory.Prism.LocalValue

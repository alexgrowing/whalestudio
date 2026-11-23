import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEvWIsUnitInjectiveDvdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTwoHomsERegularAssociatedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdIffDvdCoeffBreuilKisinStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EnvPush

theorem c_mem_of_mem_map {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (TB : TopBasis s I ι) (L : Ideal S) (i : ι) {x : A} (hx : x ∈ L.map s) : TB.c i x ∈ L := by
  have key : ∀ a : A, TB.c i (a * x) ∈ L := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      intro a
      rw [mul_comm, TB.c_mul]
      exact L.mul_mem_right _ hj
    | zero => intro a; rw [mul_zero, map_zero]; exact L.zero_mem
    | add y z _ _ hy hz => intro a; rw [mul_add, map_add]; exact L.add_mem (hy a) (hz a)
    | smul b y _ hy => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b)
  simpa using key 1

theorem coeff_map {S A S' A' ι : Type} [CommRing S] [CommRing A] [CommRing S'] [CommRing A'] {s : S →+* A}
    {s' : S' →+* A'} {I : Ideal S} {I' : Ideal S'} (TB : TopBasis s I ι) (TB' : TopBasis s' I' ι) (g : S →+* S')
    (qf : A →+* A') (hq : ∀ y, qf (s y) = s' (g y)) (hb : ∀ i, qf (TB.b i) = TB'.b i) (hI : I.map g ≤ I')
    (hH : IsHausdorff I' S') (x : A) (α : ι) : TB'.c α (qf x) = g (TB.c α x) := by
  classical
  refine sub_eq_zero.1 (hH.haus _ fun n => SModEq.zero.2 ((Ideal.mul_top _).ge ?_))
  have hF : ∀ i, i ∉ (TB.fin x n).toFinset ∪ {α} → TB.c i x ∈ I ^ n := fun i hi => by
    by_contra h
    exact hi (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).2 h))
  have hm : qf (x - ∑ i ∈ (TB.fin x n).toFinset ∪ {α}, s (TB.c i x) * TB.b i) ∈ (I' ^ n).map s' := by
    have h1 := Ideal.mem_map_of_mem qf (TB.approx x n _ hF)
    rw [Ideal.map_map, show qf.comp s = s'.comp g from RingHom.ext hq, ← Ideal.map_map, Ideal.map_pow] at h1
    exact Ideal.map_mono (Ideal.pow_right_mono hI n) h1
  have hc := c_mem_of_mem_map TB' _ α hm
  have e : TB'.c α (qf (x - ∑ i ∈ (TB.fin x n).toFinset ∪ {α}, s (TB.c i x) * TB.b i)) =
      TB'.c α (qf x) - g (TB.c α x) := by
    rw [map_sub, map_sub, map_sum, map_sum, Finset.sum_eq_single α]
    · rw [map_mul, hq, hb, TB'.c_mul, TB'.c_self, mul_one]
    · intro i _ hi
      rw [map_mul, hq, hb, TB'.c_mul, TB'.c_ne α i (Ne.symm hi), mul_zero]
    · intro h
      exact absurd (Finset.mem_union_right _ (Finset.mem_singleton_self α)) h
  rwa [e] at hc

end GlobalTheory.BSP.EnvPush

open GlobalTheory.BSP.EnvPush in

theorem GlobalTheory.BSP.envPush_dvd_l : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (An : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (q : Hom En.Q An.Q), q.comp En.inl = An.inl.comp bk.ι → q.comp En.inr = An.inr → ∀ x : En.Q.A, ((l : ℕ) : An.Q.A) ∣ q.f x → ((l : ℕ) : En.Q.A) ∣ x := by
  intro l _ K bk En An q hl hr x hx
  have hql : ∀ y : bk.prism.A, q.f (En.inl.f y) = An.inl.f (bk.ι.f y) := fun y =>
    congrArg (fun h : Hom bk.prism An.Q => h.f y) hl
  have hqr : ∀ y : bk.prism.A, q.f (En.inr.f y) = An.inr.f y := fun y =>
    congrArg (fun h : Hom bk.prism An.Q => h.f y) hr

  have hw : q.f En.w = An.w := by
    have e1 : q.f (En.inr.f (bk.toP X)) = An.inr.f (bk.toP X) := hqr _
    have e2 : En.inr.f (bk.toP X) = En.inl.f (bk.toP X) + En.inl.f (bk.toP bk.E) * En.w := En.w_eq
    have e3 : An.inr.f (bk.toP X) = An.inl.f (bk.ι.f (bk.toP X)) + An.inl.f (bk.ι.f (bk.toP bk.E)) * An.w :=
      An.w_eq
    have e4 : q.f (En.inl.f (bk.toP X) + En.inl.f (bk.toP bk.E) * En.w) =
        An.inl.f (bk.ι.f (bk.toP X)) + An.inl.f (bk.ι.f (bk.toP bk.E)) * q.f En.w :=
      (q.f.map_add _ _).trans (congrArg₂ (· + ·) (hql _) ((q.f.map_mul _ _).trans (congrArg (· * q.f En.w) (hql _))))
    have e5 := add_left_cancel (e4.symm.trans ((congrArg q.f e2).symm.trans (e1.trans e3)))
    have key : ∀ (b u v : An.Q.A), b ∈ nonZeroDivisors An.Q.A → b * u = b * v → u = v := fun b u v hb h =>
      sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff hb).1 (by rw [mul_sub, h, sub_self]))
    have hnz : An.inl.f (bk.ι.f (bk.toP bk.E)) ∈ nonZeroDivisors An.Q.A :=
      (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk An.Q (An.inl.comp bk.ι) (An.inl.comp bk.ι)).1
    exact key _ _ _ hnz e5

  have hδ : ∀ (n : ℕ) (y : En.Q.A), q.f (En.Q.D.δ^[n] y) = An.Q.D.δ^[n] (q.f y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      exact (congrArg q.f (Function.iterate_succ_apply' _ n y)).trans ((q.f_δ _).trans
        ((congrArg An.Q.D.δ (ih y)).trans (Function.iterate_succ_apply' _ n _).symm))
  have hb : ∀ α, q.f (En.tb.b α) = An.tb.b α := by
    intro α
    refine (congrArg q.f (En.tb_b α)).trans ((map_finsuppProd q.f _ _).trans (Eq.trans ?_ (An.tb_b α).symm))
    exact Finsupp.prod_congr fun i _ =>
      (map_pow q.f _ _).trans (congrArg (· ^ α.1 i) ((hδ i En.w).trans (congrArg _ hw)))

  have hJ : (Ideal.span {((l : ℕ) : bk.prism.A)} ⊔ bk.prism.I).map bk.ι.f ≤
      Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I := by
    refine Ideal.map_le_iff_le_comap.2 (sup_le (Ideal.span_le.2 (Set.singleton_subset_iff.2 ?_))
      fun y hy => Ideal.mem_sup_right (bk.ι.f_I y hy))
    show bk.ι.f ((l : ℕ) : bk.prism.A) ∈ Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I
    rw [map_natCast]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have hH : IsHausdorff (Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I) (ainfObj K).A :=
    (ainfObj K).complete.toIsHausdorff

  have key : ∀ α, An.tb.c α (q.f x) = bk.ι.f (En.tb.c α x) := fun α =>
    coeff_map En.tb An.tb bk.ι.f q.f hql hb hJ hH x α

  obtain ⟨y, hy⟩ := hx
  have hl' : ∀ α, ((l : ℕ) : bk.S) ∣ En.tb.c α x := fun α => by
    apply (GlobalTheory.T.breuilKisin_evW_isUnit_injective_dvd l K bk).2.2
    refine ⟨An.tb.c α y, ?_⟩
    calc bk.ι.f (En.tb.c α x) = An.tb.c α (q.f x) := (key α).symm
      _ = An.tb.c α (An.inl.f ((l : ℕ) : (ainfObj K).A) * y) := by rw [hy, map_natCast]
      _ = ((l : ℕ) : (ainfObj K).A) * An.tb.c α y := An.tb.c_mul α _ y
  have h := (GlobalTheory.T.dvd_iff_dvd_coeff_breuilKisin l K bk En.Q.A (En.inl.f : bk.S →+* En.Q.A) (Digits l) En.tb ((l : ℕ) : bk.S) x).2 hl'
  have hg : ∀ {R A : Type} [CommRing R] [CommRing A] (s : R →+* A) (y : A) (n : ℕ), s n ∣ y → (n : A) ∣ y :=
    fun s y n h => (map_natCast s n) ▸ h
  exact hg _ _ _ h

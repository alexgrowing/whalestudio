import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrLenRestrictSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionLocal
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationRestrict
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace RestrLenRestrict

section CechH

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type w}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {M : Type w} [AddCommGroup M] [Module R M]

def cochainOf (σ : ∀ I : Cell U, M →ₗ[R] G I) : M →ₗ[R] Cech.Cochain G 0 :=
  LinearMap.pi fun I : Cech.Idx U 0 => σ I.1

def toH0OfCocycle (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0) : M →ₗ[R] Cech.H G ρ 0 :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (LinearMap.ker (Cech.d G ρ 0)) φ
    (fun m => LinearMap.mem_ker.mpr (hφ m))

theorem toH0OfCocycle_eq_zero_iff (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0) (m : M) :
    toH0OfCocycle φ hφ m = 0 ↔ φ m = 0 := by
  have e : toH0OfCocycle φ hφ m = (Submodule.Quotient.mk (⟨φ m, LinearMap.mem_ker.mpr (hφ m)⟩ :
      LinearMap.ker (Cech.d G ρ 0)) : Cech.H G ρ 0) := rfl
  rw [e]
  exact (Submodule.Quotient.mk_eq_zero _).trans (Submodule.mem_comap.trans (Submodule.mem_bot R))

theorem toH0OfCocycle_surjective (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0)
    (h : ∀ z : Cech.Cochain G 0, Cech.d G ρ 0 z = 0 → ∃ m, φ m = z) : Function.Surjective (toH0OfCocycle φ hφ) := by
  intro ξ
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  obtain ⟨m, hm⟩ := h z (LinearMap.mem_ker.mp z.2)
  refine ⟨m, ?_⟩
  have e : toH0OfCocycle φ hφ m = (Submodule.Quotient.mk (⟨φ m, LinearMap.mem_ker.mpr (hφ m)⟩ :
      LinearMap.ker (Cech.d G ρ 0)) : Cech.H G ρ 0) := rfl
  rw [e]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hm)

theorem length_quotient_eq_length_H0 (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0)
    (h : ∀ z : Cech.Cochain G 0, Cech.d G ρ 0 z = 0 → ∃ m, φ m = z) (K : Submodule R M)
    (hK : ∀ m, φ m = 0 ↔ m ∈ K) : Module.length R (M ⧸ K) = Module.length R (Cech.H G ρ 0) := by
  have hker : LinearMap.ker (toH0OfCocycle φ hφ) = K := by
    ext m
    rw [LinearMap.mem_ker, toH0OfCocycle_eq_zero_iff, hK]
  rw [← hker]
  exact (LinearMap.quotKerEquivOfSurjective _ (toH0OfCocycle_surjective φ hφ h)).length_eq

theorem sgn_mul_self' (L : Finset (Fin n)) (j : Fin n) : Cech.sgn L j * Cech.sgn L j = 1 := by
  rw [Cech.sgn, ← mul_pow]
  norm_num

end CechH

section Quot

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type w} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem mem_sub_of_mem_secs {F : SubSystem S x E} {t : E} (ht : t ∈ F.secs) (I : Chart x) :
    t ∈ F.sub I :=
  (Submodule.mem_iInf _).mp ht I

def secsTo (F₁ F₂ : SubSystem S x E) (I : Chart x) :
    F₁.secs →ₗ[S] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) :=
  (SubSystem.quotSub F₁ F₂ I).mkQ ∘ₗ
    { toFun := fun t => ⟨t.1, mem_sub_of_mem_secs t.2 I⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def qres (F₁ F₂ : SubSystem S x E) (I J : Chart x) (h : I.1 ⊆ J.1) :
    (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) →ₗ[S] (F₁.sub J ⧸ SubSystem.quotSub F₁ F₂ J) :=
  SubSystem.quotRes F₁ F₂ I J h

def toCochain (F₁ F₂ : SubSystem S x E) :=
  cochainOf (R := S) (G := fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (fun I => secsTo F₁ F₂ I)

theorem d_toCochain (F₁ F₂ : SubSystem S x E) (t : F₁.secs) :
    Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (qres F₁ F₂) 0
      (toCochain F₁ F₂ t) = 0 := by
  have hv : ∀ (I J : Chart x) (h : I.1 ⊆ J.1),
      qres F₁ F₂ I J h (secsTo F₁ F₂ I t) = secsTo F₁ F₂ J t := fun _ _ _ => rfl
  exact Cech.d_zero_of_compat (fun I => secsTo F₁ F₂ I t) hv

def sing {a : Fin (N + 1)} (ha : a ∈ support x) : Cech.Idx (support x) 0 :=
  ⟨⟨{a}, Finset.singleton_nonempty a, Finset.singleton_subset_iff.mpr ha⟩, Finset.card_singleton a⟩

theorem eq_sing (I : Cech.Idx (support x) 0) : ∃ (a : Fin (N + 1)) (ha : a ∈ support x), I = sing ha := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.2
  have hmem : a ∈ support x := I.1.2.2 (by rw [ha]; exact Finset.mem_singleton_self a)
  exact ⟨a, hmem, Subtype.ext (Subtype.ext ha)⟩

theorem toCochain_eq_zero_iff (F₁ F₂ : SubSystem S x E) (t : F₁.secs) :
    toCochain F₁ F₂ t = 0 ↔ t ∈ F₂.secs.comap F₁.secs.subtype := by
  rw [Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · intro h
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro T
    obtain ⟨a, haT⟩ := T.2.1
    have ha : a ∈ support x := T.2.2 haT
    have h1 : (Submodule.Quotient.mk (⟨(t : E), mem_sub_of_mem_secs t.2 _⟩ : F₁.sub (sing ha).1) :
        F₁.sub (sing ha).1 ⧸ SubSystem.quotSub F₁ F₂ (sing ha).1) = 0 := congrFun h (sing ha)
    have h2 : (t : E) ∈ F₂.sub (sing ha).1 :=
      (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ (sing ha).1)).mp h1
    exact F₂.mono _ T (Finset.singleton_subset_iff.mpr haT) _ h2
  · intro h
    funext I
    show (Submodule.Quotient.mk (⟨(t : E), mem_sub_of_mem_secs t.2 _⟩ : F₁.sub I.1) :
        F₁.sub I.1 ⧸ SubSystem.quotSub F₁ F₂ I.1) = 0
    exact (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I.1)).mpr (mem_sub_of_mem_secs h I.1)

theorem d_mk (F₁ F₂ : SubSystem S x E) (u : Cech.Idx (support x) 0 → E) (hu : ∀ I, u I ∈ F₁.sub I.1)
    (J : Cech.Idx (support x) 1) :
    Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (qres F₁ F₂) 0
        (fun I => Submodule.Quotient.mk ⟨u I, hu I⟩) J =
      Submodule.Quotient.mk ⟨∑ j : J.1.1, Cech.sgn J.1.1 j • u (Cech.face J j),
        Submodule.sum_mem _ fun j _ =>
          zsmul_mem (F₁.mono _ _ (Cech.face_subset J j) _ (hu (Cech.face J j))) _⟩ := by
  rw [Cech.d_apply]
  have : (⟨∑ j : J.1.1, Cech.sgn J.1.1 j • u (Cech.face J j),
        Submodule.sum_mem _ fun j _ =>
          zsmul_mem (F₁.mono _ _ (Cech.face_subset J j) _ (hu (Cech.face J j))) _⟩ : F₁.sub J.1) =
      ∑ j : J.1.1, Cech.sgn J.1.1 j • F₁.res _ J.1 (Cech.face_subset J j) ⟨u (Cech.face J j), hu _⟩ := by
    apply Subtype.ext
    simp [SubSystem.res]
  rw [this, ← Submodule.mkQ_apply, map_sum]
  simp only [map_zsmul]
  rfl

set_option maxHeartbeats 1000000 in

theorem exists_toCochain_eq (F₁ F₂ : SubSystem S x E)
    (hlift : ∀ s : Chart x → E, (∀ I, s I ∈ F₁.sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ F₂.sub I₂) →
      ∃ t ∈ F₁.secs, ∀ I, t - s I ∈ F₂.sub I)
    (z : Cech.Cochain (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) 0)
    (hz : Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (qres F₁ F₂) 0 z = 0) :
    ∃ t : F₁.secs, toCochain F₁ F₂ t = z := by
  classical
  have hrep : ∀ I : Cech.Idx (support x) 0, ∃ v : E, ∃ hv : v ∈ F₁.sub I.1,
      (Submodule.Quotient.mk ⟨v, hv⟩ : F₁.sub I.1 ⧸ SubSystem.quotSub F₁ F₂ I.1) = z I := by
    intro I
    obtain ⟨⟨v, hv⟩, h⟩ := Submodule.Quotient.mk_surjective _ (z I)
    exact ⟨v, hv, h⟩
  choose v hv hvz using hrep
  have hz' : z = fun I => Submodule.Quotient.mk ⟨v I, hv I⟩ := funext fun I => (hvz I).symm
  have hpair : ∀ J : Cech.Idx (support x) 1,
      ∑ j : J.1.1, Cech.sgn J.1.1 j • v (Cech.face J j) ∈ F₂.sub J.1 := by
    intro J
    have e := congrFun hz J
    rw [hz', d_mk] at e
    exact (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ J.1)).mp e
  let V : Finset (Fin (N + 1)) → E := fun T =>
    if h : (T.Nonempty ∧ T ⊆ support x) ∧ T.card = 0 + 1 then v ⟨⟨T, h.1⟩, h.2⟩ else 0
  have hV : ∀ I : Cech.Idx (support x) 0, V I.1.1 = v I := fun I => by
    simp only [V]
    rw [dif_pos ⟨I.1.2, I.2⟩]
  have hVpair : ∀ (a b : Fin (N + 1)) (ha : a ∈ support x) (hb : b ∈ support x) (T : Chart x),
      a ∈ T.1 → b ∈ T.1 → V {a} - V {b} ∈ F₂.sub T := by
    intro a b ha hb T haT hbT
    by_cases hab : a = b
    · subst hab
      rw [sub_self]
      exact Submodule.zero_mem _
    have hsupp : ({a, b} : Finset (Fin (N + 1))) ⊆ support x := by
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨ha, hb⟩
    let J : Cech.Idx (support x) 1 :=
      ⟨⟨{a, b}, Finset.insert_nonempty _ _, hsupp⟩, Finset.card_pair hab⟩
    have e := hpair J
    have hj : ∀ j : J.1.1, v (Cech.face J j) = V (J.1.1.erase j) := fun j => (hV (Cech.face J j)).symm
    simp only [hj] at e
    have e2 := Cech.sum_sgn_of_card_two (J := ({a, b} : Finset (Fin (N + 1)))) (Finset.card_pair hab)
    rw [Finset.sum_coe_sort ({a, b} : Finset (Fin (N + 1)))
      (fun j => Cech.sgn {a, b} j • V (({a, b} : Finset (Fin (N + 1))).erase j))] at e
    rw [Finset.sum_pair hab] at e e2
    have ea : ({a, b} : Finset (Fin (N + 1))).erase a = {b} :=
      Finset.erase_insert (by simpa using hab)
    have eb : ({a, b} : Finset (Fin (N + 1))).erase b = {a} := by
      rw [Finset.pair_comm]
      exact Finset.erase_insert (by simpa using Ne.symm hab)
    rw [ea, eb, eq_neg_of_add_eq_zero_right e2, neg_smul, ← sub_eq_add_neg, ← smul_sub] at e
    have e3 := zsmul_mem e (Cech.sgn {a, b} a)
    rw [smul_smul, sgn_mul_self', one_smul] at e3
    have e4 : V {a} - V {b} ∈ F₂.sub J.1 := by
      rw [← neg_sub]
      exact neg_mem e3
    refine F₂.mono J.1 T ?_ _ e4
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨haT, hbT⟩
  let s : Chart x → E := fun I => V {I.1.min' I.2.1}
  have hs : ∀ I, s I ∈ F₁.sub I := by
    intro I
    have hm := I.1.min'_mem I.2.1
    have h1 : V {I.1.min' I.2.1} ∈ F₁.sub (sing (I.2.2 hm)).1 := by
      rw [show V {I.1.min' I.2.1} = v (sing (I.2.2 hm)) from hV (sing (I.2.2 hm))]
      exact hv _
    exact F₁.mono _ I (Finset.singleton_subset_iff.mpr hm) _ h1
  have hcomp : ∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ F₂.sub I₂ := by
    intro I₁ I₂ h
    exact hVpair _ _ (I₁.2.2 (I₁.1.min'_mem I₁.2.1)) (I₂.2.2 (I₂.1.min'_mem I₂.2.1)) I₂
      (h (I₁.1.min'_mem I₁.2.1)) (I₂.1.min'_mem I₂.2.1)
  obtain ⟨t, ht, hts⟩ := hlift s hs hcomp
  refine ⟨⟨t, ht⟩, ?_⟩
  rw [hz']
  funext I
  obtain ⟨a, ha, rfl⟩ := eq_sing I
  change (Submodule.Quotient.mk (⟨t, mem_sub_of_mem_secs ht _⟩ : F₁.sub (sing ha).1) :
      F₁.sub (sing ha).1 ⧸ SubSystem.quotSub F₁ F₂ (sing ha).1) = Submodule.Quotient.mk ⟨v (sing ha), hv _⟩
  rw [Submodule.Quotient.eq]
  change t - v (sing ha) ∈ F₂.sub (sing ha).1
  have hsa : s (sing ha).1 = v (sing ha) := by
    have hmin : ({a} : Finset (Fin (N + 1))).min' (Finset.singleton_nonempty a) = a :=
      Finset.min'_singleton a
    change V {({a} : Finset (Fin (N + 1))).min' _} = v (sing ha)
    rw [hmin]
    exact hV (sing ha)
  rw [← hsa]
  exact hts _

set_option maxHeartbeats 1000000 in

theorem length_secs_eq (F₁ F₂ : SubSystem S x E)
    (hlift : ∀ s : Chart x → E, (∀ I, s I ∈ F₁.sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ F₂.sub I₂) →
      ∃ t ∈ F₁.secs, ∀ I, t - s I ∈ F₂.sub I) :
    Module.length S (F₁.secs ⧸ F₂.secs.comap F₁.secs.subtype) =
      Module.length S (SubSystem.quotH F₁ F₂ 0) := by
  have h := length_quotient_eq_length_H0 (R := S) (G := fun I => ↥(F₁.sub I) ⧸ SubSystem.quotSub F₁ F₂ I)
    (ρ := qres F₁ F₂) (M := F₁.secs) (toCochain F₁ F₂)
    (fun t => by exact d_toCochain F₁ F₂ t)
    (fun z hz => by exact exists_toCochain_eq F₁ F₂ hlift z hz)
    (F₂.secs.comap F₁.secs.subtype)
    (fun t => by exact toCochain_eq_zero_iff F₁ F₂ t)
  exact h

end Quot

section Compose

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {K' K'' : Type w}
  [Field K'] [Algebra S K'] [Field K''] [Algebra S K''] {N : ℕ}
  {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} {z : Fin (N + 1) → K''}

theorem restrictData_comp {hxy : ∀ i, y i ≠ 0 → x i ≠ 0} {hyz : ∀ i, z i ≠ 0 → y i ≠ 0}
    {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {Q'' : SubSystem S z K''} {r : Ω → K'}
    {r' : K' → K''} (h1 : RestrictData Q hxy Q' r) (h2 : RestrictData Q' hyz Q'' r') :
    RestrictData Q (fun i hi => hxy i (hyz i hi)) Q'' (r' ∘ r) where
  mem I q hq := h2.mem I _ (h1.mem (liftChart hyz I) q hq)
  add I q hq q' hq' := by
    simp only [Function.comp_apply]
    rw [h1.add (liftChart hyz I) q hq q' hq',
      h2.add I _ (h1.mem (liftChart hyz I) q hq) _ (h1.mem (liftChart hyz I) q' hq')]
  smul I q hq f s e hs hf hse := by
    simp only [Function.comp_apply]
    rw [h1.smul (liftChart hyz I) q hq f s e hs hf hse,
      h2.smul I (r q) (h1.mem (liftChart hyz I) q hq) f s e hs hf hse]
  span I := by
    rw [← h2.span I]
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨q, hq, rfl⟩
      exact Submodule.subset_span ⟨r q, h1.mem (liftChart hyz I) q hq, rfl⟩
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨q', hq', rfl⟩
      have hle := (h1.span (liftChart hyz I)).le
      have hq'' : q' ∈ Submodule.span (chartRing S y (liftChart hyz I))
          (r '' Q.sub (liftChart hxy (liftChart hyz I))) := by
        rw [h1.span (liftChart hyz I)]
        exact hq'
      have h0 : r' 0 = 0 := by
        have := h2.add I 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
        rw [add_zero] at this
        simpa using this
      refine Submodule.span_induction (p := fun q' _ => r' q' ∈ Submodule.span (chartRing S z I)
        ((r' ∘ r) '' Q.sub (liftChart (fun i hi => hxy i (hyz i hi)) I))) ?_ ?_ ?_ ?_ hq''
      · rintro _ ⟨q, hq, rfl⟩
        exact Submodule.subset_span ⟨q, hq, rfl⟩
      · rw [h0]
        exact Submodule.zero_mem _
      · intro a b ha hb iha ihb
        rw [h2.add I a (hle ha) b (hle hb)]
        exact Submodule.add_mem _ iha ihb
      · intro c a ha iha
        obtain ⟨f, s, e, hs, hf, hse, hc⟩ := c.2
        have key : r' (c • a) =
            (⟨aeval z f / aeval z s, f, s, e, hs, hf, hse, rfl⟩ : chartRing S z I) • r' a := by
          rw [Subalgebra.smul_def, smul_eq_mul, hc, h2.smul I a (hle ha) f s e hs hf hse]
          rfl
        rw [key]
        exact Submodule.smul_mem _ _ iha

end Compose

section Red

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

def redHom (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    {j : Fin (N + 1)} (hyj : y j ≠ 0) :
    chartRing k x (singleChart (hxy j hyj)) →ₐ[k] chartRing k y (singleChart hyj) where
  toFun a := ⟨redAt k x y a, (chartRing_sub_locAt hsp hxy (singleChart hyj) a.2).2⟩
  map_one' := Subtype.ext (locAt_one hsp).2
  map_mul' a b := Subtype.ext (locAt_mul hsp (chartRing_sub_locAt hsp hxy (singleChart hyj) a.2).1
    (chartRing_sub_locAt hsp hxy (singleChart hyj) b.2).1).2
  map_zero' := Subtype.ext (locAt_zero hsp).2
  map_add' a b := Subtype.ext (locAt_add hsp (chartRing_sub_locAt hsp hxy (singleChart hyj) a.2).1
    (chartRing_sub_locAt hsp hxy (singleChart hyj) b.2).1).2
  commutes' c := Subtype.ext (locAt_algebraMap hsp c).2

theorem redHom_ratio (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    {j : Fin (N + 1)} (hyj : y j ≠ 0) (i : Fin (N + 1)) :
    redHom hsp hxy hyj (ratio (hxy j hyj) i) = ratio hyj i := by
  apply Subtype.ext
  show redAt k x y (x i / x j) = y i / y j
  have h := redAt_eq hsp (isHomogeneous_X k i) (isHomogeneous_X k j)
    (show aeval y (X j : Poly k N) ≠ 0 by rw [aeval_X]; exact hyj)
  simpa only [aeval_X] using h

theorem ker_comp_redHom (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    {j : Fin (N + 1)} (hyj : y j ≠ 0) (pp : Ideal (Poly k N)) [pp.IsPrime]
    (hle : primeOf (S := k) y ≤ pp) (hX : (X j : Poly k N) ∉ pp) {K'' : Type w} [Field K'']
    [Algebra k K''] (ψ : chartRing k y (singleChart hyj) →ₐ[k] K'')
    (hker : RingHom.ker ψ = chartPrime pp hyj) :
    RingHom.ker (ψ.comp (redHom hsp hxy hyj)) = chartPrime pp (hxy j hyj) := by
  ext a
  obtain ⟨f, s, e, hs, hf, hse, ha⟩ := a.2
  have hsy : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hyj) hs
  have hred : ((redHom hsp hxy hyj a : chartRing k y (singleChart hyj)) : K') =
      aeval y f / aeval y s := by
    show redAt k x y (a : Ω) = _
    rw [ha]
    exact redAt_eq hsp hf hse hsy
  rw [RingHom.mem_ker, AlgHom.comp_apply, ← RingHom.mem_ker (f := ψ), hker,
    mem_chartPrime_iff hyj hle hX hf hs hse hred,
    mem_chartPrime_iff (hxy j hyj) (hsp.trans hle) hX hf hs hse ha]

end Red

theorem exists_residue {k : Type u} [Field k] {R : Type w} [CommRing R] [Algebra k R] (P : Ideal R)
    [P.IsPrime] : ∃ (K : Type w) (_ : Field K) (_ : Algebra k K) (ψ : R →ₐ[k] K), RingHom.ker ψ = P := by
  refine ⟨FractionRing (R ⧸ P), inferInstance, inferInstance,
    (IsScalarTower.toAlgHom k (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mkₐ k P), ?_⟩
  ext a
  rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, IsScalarTower.coe_toAlgHom',
    ← map_zero (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))),
    (IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P))).eq_iff, Ideal.Quotient.eq_zero_iff_mem]

set_option maxHeartbeats 1000000 in

theorem proof (hSC : SurjectiveClosed.Statement.{u, w})
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) : RestrLenRestrict.Statement.{u, w} := by
  intro k _ Ω _ _ N x K' _ _ y hxy hsp pp e hW Q Q' r hr
  have := hW.isPrime
  obtain ⟨j, hjX⟩ := hW.relevant
  have hyj : y j ≠ 0 := fun h0 => hjX (hW.le
    ((mem_primeOf_of_isHomogeneous y (isHomogeneous_X k j)).mpr (by rw [aeval_X, h0])))
  have hxj : x j ≠ 0 := hxy j hyj
  have hle : primeOf (S := k) x ≤ pp := hsp.trans hW.le
  have : (chartPrime pp hyj).IsPrime :=
    (PrimeFiltration.Point.proof k K' N y pp hW.isPrime hW.homog hW.le j hyj hjX).1
  obtain ⟨K'', _, _, ψ, hker⟩ := exists_residue (k := k) (chartPrime pp hyj)
  have hyz : ∀ i, ψ (ratio hyj i) ≠ 0 → y i ≠ 0 := by
    intro i hi h0
    apply hi
    have : ratio (S := k) hyj i = 0 := Subtype.ext (show y i / y j = 0 by rw [h0, zero_div])
    rw [this, map_zero]

  obtain ⟨QW, rW, hQW⟩ :=
    PrimeFiltration.Restrict.proof k K' N y pp hW.isPrime hW.homog hW.le j hyj hjX K'' ψ hker hyz Q'
  have hRW : RestrictData Q'.toSubSystem hyz QW.toSubSystem rW :=
    ⟨fun I => (hQW I).1, fun I => (hQW I).2.1, fun I => (hQW I).2.2.1, fun I => (hQW I).2.2.2⟩
  have hRxW := restrictData_comp hr hRW

  have hkerx := ker_comp_redHom hsp hxy hyj pp hW.le hjX ψ hker
  have hpt : (fun i => (ψ.comp (redHom hsp hxy hyj)) (ratio hxj i)) = fun i => ψ (ratio hyj i) := by
    funext i
    rw [AlgHom.comp_apply, redHom_ratio]
  have key : ∀ (zz : Fin (N + 1) → K''),
      (fun i => (ψ.comp (redHom hsp hxy hyj)) (ratio hxj i)) = zz →
      ∀ (hxz : ∀ i, zz i ≠ 0 → x i ≠ 0) (QW' : LineBundle k zz) (rr : Ω → K''),
      RestrictData Q.toSubSystem hxz QW'.toSubSystem rr → ∀ c : ℤ,
      Nonempty (SubSystem.quotH (Q.twist (twistSys k x c))
        ((Q.twist (twistSys k x c)).twist (idealSys x pp)) 0 ≃ₗ[k] (QW'.twist (twistSys k zz c)).H 0) := by
    rintro zz rfl hxz QW' rr hR c
    exact hRQ k Ω N x pp hW.isPrime hW.homog hle j hxj hjX K'' (ψ.comp (redHom hsp hxy hyj)) hkerx hxz
      Q QW' rr hR c 0
  obtain ⟨c₁, hc₁⟩ := hSC k Ω N x Q pp hW.homog
  obtain ⟨c₂, hc₂⟩ := hSC k K' N y Q' pp hW.homog
  refine Filter.eventually_atTop.mpr ⟨max c₁.toNat c₂.toNat, fun c hc => ?_⟩
  have h1 : c₁ ≤ (c : ℤ) :=
    (Int.self_le_toNat c₁).trans (by exact_mod_cast (le_max_left _ _).trans hc)
  have h2 : c₂ ≤ (c : ℤ) :=
    (Int.self_le_toNat c₂).trans (by exact_mod_cast (le_max_right _ _).trans hc)
  obtain ⟨ex⟩ := key _ hpt _ QW (rW ∘ r) hRxW c
  obtain ⟨ey⟩ := hRQ k K' N y pp hW.isPrime hW.homog hW.le j hyj hjX K'' ψ hker hyz Q' QW rW hRW c 0
  rw [restrLen, restrLen, length_secs_eq _ _ (hc₂ c h2), length_secs_eq _ _ (hc₁ c h1), ey.length_eq,
    ex.length_eq]

end RestrLenRestrict

end

end GroundTheory.Heights₂.Heights.Kleiman

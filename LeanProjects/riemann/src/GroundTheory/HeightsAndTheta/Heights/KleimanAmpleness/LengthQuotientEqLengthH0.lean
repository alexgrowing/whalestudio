import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace QuotientH0Length

section CechH

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type w}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {M : Type w} [AddCommGroup M] [Module R M]

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
  {x : Fin (N + 1) → Ω}

theorem mem_sub_of_mem_secs {F : SubSystem S x Ω} {t : Ω} (ht : t ∈ F.secs) (I : Chart x) :
    t ∈ F.sub I :=
  (Submodule.mem_iInf _).mp ht I

def secsTo (F₁ F₂ : SubSystem S x Ω) (I : Chart x) :
    F₁.secs →ₗ[S] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) :=
  (SubSystem.quotSub F₁ F₂ I).mkQ ∘ₗ
    { toFun := fun t => ⟨t.1, mem_sub_of_mem_secs t.2 I⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def toCochain (F₁ F₂ : SubSystem S x Ω) :
    F₁.secs →ₗ[S] Cech.Cochain (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) 0 :=
  LinearMap.pi fun I : Cech.Idx (support x) 0 => secsTo F₁ F₂ I.1

theorem d_toCochain (F₁ F₂ : SubSystem S x Ω) (t : F₁.secs) :
    Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (SubSystem.quotRes F₁ F₂) 0
      (toCochain F₁ F₂ t) = 0 := by
  have hv : ∀ (I J : Chart x) (h : I.1 ⊆ J.1),
      SubSystem.quotRes F₁ F₂ I J h (secsTo F₁ F₂ I t) = secsTo F₁ F₂ J t := fun _ _ _ => rfl
  exact Cech.d_zero_of_compat (fun I => secsTo F₁ F₂ I t) hv

def sing {a : Fin (N + 1)} (ha : a ∈ support x) : Cech.Idx (support x) 0 :=
  ⟨⟨{a}, Finset.singleton_nonempty a, Finset.singleton_subset_iff.mpr ha⟩, Finset.card_singleton a⟩

theorem eq_sing (I : Cech.Idx (support x) 0) : ∃ (a : Fin (N + 1)) (ha : a ∈ support x), I = sing ha := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.2
  have hmem : a ∈ support x := I.1.2.2 (by rw [ha]; exact Finset.mem_singleton_self a)
  exact ⟨a, hmem, Subtype.ext (Subtype.ext ha)⟩

theorem toCochain_eq_zero_iff (F₁ F₂ : SubSystem S x Ω) (t : F₁.secs) :
    toCochain F₁ F₂ t = 0 ↔ t ∈ F₂.secs.comap F₁.secs.subtype := by
  rw [Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · intro h
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro T
    obtain ⟨a, haT⟩ := T.2.1
    have ha : a ∈ support x := T.2.2 haT
    have h1 : (Submodule.Quotient.mk (⟨(t : Ω), mem_sub_of_mem_secs t.2 _⟩ : F₁.sub (sing ha).1) :
        F₁.sub (sing ha).1 ⧸ SubSystem.quotSub F₁ F₂ (sing ha).1) = 0 := congrFun h (sing ha)
    have h2 : (t : Ω) ∈ F₂.sub (sing ha).1 :=
      (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ (sing ha).1)).mp h1
    exact F₂.mono _ T (Finset.singleton_subset_iff.mpr haT) _ h2
  · intro h
    funext I
    show (Submodule.Quotient.mk (⟨(t : Ω), mem_sub_of_mem_secs t.2 _⟩ : F₁.sub I.1) :
        F₁.sub I.1 ⧸ SubSystem.quotSub F₁ F₂ I.1) = 0
    exact (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I.1)).mpr (mem_sub_of_mem_secs h I.1)

theorem d_mk (F₁ F₂ : SubSystem S x Ω) (u : Cech.Idx (support x) 0 → Ω) (hu : ∀ I, u I ∈ F₁.sub I.1)
    (J : Cech.Idx (support x) 1) :
    Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (SubSystem.quotRes F₁ F₂) 0
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

theorem exists_toCochain_eq (F₁ F₂ : SubSystem S x Ω)
    (hlift : ∀ s : Chart x → Ω, (∀ I, s I ∈ F₁.sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ F₂.sub I₂) →
      ∃ t ∈ F₁.secs, ∀ I, t - s I ∈ F₂.sub I)
    (z : Cech.Cochain (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) 0)
    (hz : Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (SubSystem.quotRes F₁ F₂) 0 z = 0) :
    ∃ t : F₁.secs, toCochain F₁ F₂ t = z := by
  classical
  have hrep : ∀ I : Cech.Idx (support x) 0, ∃ v : Ω, ∃ hv : v ∈ F₁.sub I.1,
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
  let V : Finset (Fin (N + 1)) → Ω := fun T =>
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
  let s : Chart x → Ω := fun I => V {I.1.min' I.2.1}
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

set_option maxHeartbeats 400000 in

theorem length_secs_eq (F₁ F₂ : SubSystem S x Ω)
    (hlift : ∀ s : Chart x → Ω, (∀ I, s I ∈ F₁.sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ F₂.sub I₂) →
      ∃ t ∈ F₁.secs, ∀ I, t - s I ∈ F₂.sub I) :
    Module.length S (F₁.secs ⧸ F₂.secs.comap F₁.secs.subtype) =
      Module.length S (SubSystem.quotH F₁ F₂ 0) := by
  have hφ := d_toCochain F₁ F₂
  have hh := exists_toCochain_eq F₁ F₂ hlift
  have hK := toCochain_eq_zero_iff F₁ F₂
  have e : Module.length S (F₁.secs ⧸ F₂.secs.comap F₁.secs.subtype) =
      Module.length S (Cech.H (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I)
        (SubSystem.quotRes F₁ F₂) 0) :=
    length_quotient_eq_length_H0 (toCochain F₁ F₂) hφ hh _ hK
  rw [e]
  rfl

end Quot

end QuotientH0Length

end

end GroundTheory.Heights₂.Heights.Kleiman

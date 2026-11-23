import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.ConnNatHolds
import ReciprocityTheory.GroupCohomology.PairHomFCoeOfId
import ReciprocityTheory.GroupCohomology.Shapiro

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

namespace KernelCokernelKilling

section Disc

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem contAction_of_disc {V : Type u} [AddCommGroup V] [Module R V] [TopologicalSpace V]
    [DiscreteTopology V] (rho : Representation R G V) (h : ∀ v, Continuous fun g => rho g v) :
    ContAction rho :=
  continuous_prod_of_discrete_right.2 h

theorem orbit_cont (B : TRep R G) (v : B.V) : Continuous fun g => B.rho g v :=
  B.cont.comp (f := fun g : G => (g, v)) (continuous_id.prodMk continuous_const)

def subRep (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V)
    (hS : ∀ g, S ≤ S.comap (B.rho g)) : TRep R G where
  V := S
  ccs := ⟨fun _ => continuous_of_discreteTopology⟩
  rho := B.rho.subrepresentation S hS
  cont := contAction_of_disc _ fun v => (orbit_cont B v.1).subtype_mk _

instance (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V) (hS) :
    DiscreteTopology (subRep B S hS).V := inferInstanceAs (DiscreteTopology S)

theorem disc_quot {V : Type u} [AddCommGroup V] [Module R V] [TopologicalSpace V] [DiscreteTopology V]
    (S : Submodule R V) : DiscreteTopology (V ⧸ S) :=
  discreteTopology_iff_forall_isOpen.2 fun _ =>
    (Submodule.isQuotientMap_mkQ S).isOpen_preimage.1 (isOpen_discrete _)

def quotRep (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V)
    (hS : ∀ g, S ≤ S.comap (B.rho g)) : TRep R G where
  V := B.V ⧸ S
  ccs := ⟨fun _ => by have := disc_quot S; exact continuous_of_discreteTopology⟩
  rho := B.rho.quotient S hS
  cont := by
    have := disc_quot S
    refine contAction_of_disc _ fun v => ?_
    induction v using Submodule.Quotient.induction_on with
    | H v => exact (continuous_of_discreteTopology (f := S.mkQ)).comp (orbit_cont B v)

instance (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V) (hS) :
    DiscreteTopology (quotRep B S hS).V := disc_quot S

def subIncl (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V) (hS) : Pair (subRep B S hS) B :=
  Pair.ofMap S.subtype continuous_of_discreteTopology fun _ _ => rfl

def quotMk (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V) (hS) : Pair B (quotRep B S hS) :=
  Pair.ofMap (M' := quotRep B S hS) S.mkQ continuous_of_discreteTopology fun _ _ => rfl

theorem admissible_of_discrete_topology {A B C : TRep R G} [DiscreteTopology A.V] [DiscreteTopology B.V]
    [DiscreteTopology C.V] (i : Pair A B) (p : Pair B C) (hi : i.φ = MonoidHom.id G)
    (hp : p.φ = MonoidHom.id G) (hinj : Injective i.u) (hex : Exact i.u p.u) (hsurj : Surjective p.u) :
    admitted i p :=
  ⟨hi, hp, ⟨⟨by
      rw [DiscreteTopology.eq_bot (α := A.V)]
      symm
      apply eq_bot_of_singletons_open
      intro a
      refine ⟨{i.u a}, isOpen_discrete _, ?_⟩
      ext x
      simp [hinj.eq_iff]⟩, hinj⟩, hex,
    ⟨surjInv hsurj, continuous_of_discreteTopology, surjInv_eq hsurj⟩⟩

end Disc

section Triv

variable {R : Type u} [CommRing R] {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Subsingleton H]

theorem alt_sum_range (m : ℕ) :
    (1 + ∑ j ∈ Finset.range (2 * m + 1), (-1 : R) ^ (j + 1)) = 0 ∧
      (1 + ∑ j ∈ Finset.range (2 * m + 2), (-1 : R) ^ (j + 1)) = 1 := by
  have key : ∀ n : ℕ, ∑ j ∈ Finset.range n, (-1 : R) ^ (j + 1) = if Even n then 0 else -1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rcases Nat.even_or_odd n with h | h
      · have h' : ¬ Even (n + 1) := by
          rw [Nat.even_add_one]
          exact not_not.mpr h
        rw [if_pos h, if_neg h', pow_succ, h.neg_one_pow]
        ring
      · have h' : Even (n + 1) := by
          rw [Nat.even_add_one]
          exact Nat.not_even_iff_odd.mpr h
        rw [if_neg (Nat.not_even_iff_odd.mpr h), if_pos h', pow_succ, h.neg_one_pow]
        ring
  refine ⟨?_, ?_⟩
  · rw [key, if_neg (by rw [Nat.not_even_iff_odd]; exact ⟨m, rfl⟩)]
    ring
  · rw [key, if_pos ⟨m + 1, by ring⟩]
    ring

theorem alt_sum_odd (m : ℕ) : (1 + ∑ j : Fin (2 * m + 1 + 1), (-1 : R) ^ ((j : ℕ) + 1)) = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (-1 : R) ^ (j + 1)) (2 * m + 1 + 1)]
  exact (alt_sum_range m).2

theorem dn_triv {V : Type u} [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul R V] (rho : Representation R H V) (n : ℕ) (f : (Fin n → H) → V)
    (g : Fin (n + 1) → H) (a : Fin n → H) :
    dn rho n f g = (1 + ∑ j : Fin (n + 1), (-1 : R) ^ ((j : ℕ) + 1)) • f a := by
  rw [dn_apply, Subsingleton.elim (g 0) 1, map_one, Module.End.one_apply,
    Subsingleton.elim (fun i => g i.succ) a, add_smul, one_smul, Finset.sum_smul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Subsingleton.elim (Fin.contractNth j (· * ·) g) a]

theorem triv_odd (T : TRep R H) (m : ℕ) : Subsingleton (T.H (2 * m + 1)) := by
  refine subsingleton_of_forall_eq 0 fun c => ?_
  induction c using Cx.H_ind with
  | h x hx =>
    rw [Cx.cls_eq_zero_iff]
    have h0 : ∀ g, x.1 g = 0 := fun g => by
      have := congrFun (congrArg Subtype.val hx) (fun _ => 1)
      change dn T.rho (2 * m + 1) x.1 (fun _ => 1) = 0 at this
      rw [dn_triv T.rho (2 * m + 1) _ _ g, alt_sum_odd, one_smul] at this
      exact this
    have : x = 0 := Subtype.ext (funext h0)
    rw [this]
    exact zero_mem _

theorem triv_even (T : TRep R H) (m : ℕ) : Subsingleton (T.H (2 * m + 1 + 1)) := by
  refine subsingleton_of_forall_eq 0 fun c => ?_
  induction c using Cx.H_ind with
  | h x hx =>
    rw [Cx.cls_eq_zero_iff]
    refine ⟨⟨fun _ => x.1 fun _ => 1, continuous_const⟩, Subtype.ext (funext fun g => ?_)⟩
    show dn T.rho (2 * m + 1) (fun _ => x.1 fun _ => 1) g = x.1 g
    rw [dn_triv T.rho (2 * m + 1) _ g (fun _ => 1), alt_sum_odd, one_smul,
      Subsingleton.elim g (fun _ => 1)]

theorem triv_H_sub (T : TRep R H) (k : ℕ) (hk : 1 ≤ k) : Subsingleton (T.H k) := by
  obtain ⟨m, hm | hm⟩ : ∃ m, k = 2 * m + 1 ∨ k = 2 * m + 1 + 1 := by
    rcases Nat.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t - 1, Or.inr (by omega)⟩
    · exact ⟨t, Or.inl ht⟩
  · subst hm
    exact triv_odd T m
  · subst hm
    exact triv_even T m

end Triv

section ShiftSec

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem disc_CM {X Y : Type u} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [DiscreteTopology Y] : DiscreteTopology C(X, Y) := by
  refine discreteTopology_iff_isOpen_singleton.2 fun f => ?_
  have hfin : (Set.range f).Finite := (isCompact_range f.continuous).finite_of_discrete
  have he : ({f} : Set C(X, Y)) =
      ⋂ y ∈ Set.range f, {g : C(X, Y) | Set.MapsTo g (f ⁻¹' {y}) {y}} := by
    ext g
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro rfl y _ x hx; exact hx
    · intro h; ext x; exact h (f x) ⟨x, rfl⟩ rfl
  rw [he]
  exact hfin.isOpen_biInter fun y _ => ContinuousMap.isOpen_setOfPred_mapsTo
    ((isClosed_discrete _).preimage f.continuous).isCompact (isOpen_discrete _)

variable [CompactSpace G]

end ShiftSec

section ShiftC

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V]

instance disc_resBot : DiscreteTopology (M.resSub (⊥ : Subgroup G)).V :=
  inferInstanceAs (DiscreteTopology M.V)

abbrev shC : TRep R G := coindRep (⊥ : Subgroup G) (M.resSub ⊥)

instance disc_shC : DiscreteTopology (shC M).V := by
  have := disc_CM (X := G) (Y := (M.resSub (⊥ : Subgroup G)).V)
  exact inferInstanceAs (DiscreteTopology (coindSub (⊥ : Subgroup G) (M.resSub ⊥)))

def shI : M.V →ₗ[R] (shC M).V where
  toFun m := ⟨⟨fun g => M.rho g m, orbit_cont M m⟩, fun x g => by
    have hx : (x : G) = 1 := Subgroup.mem_bot.1 x.2
    show M.rho ((x : G) * g) m = M.rho (x : G) (M.rho g m)
    rw [hx, one_mul, map_one, Module.End.one_apply]⟩
  map_add' m m' := Subtype.ext (ContinuousMap.ext fun g => map_add (M.rho g) m m')
  map_smul' r m := Subtype.ext (ContinuousMap.ext fun g => map_smul (M.rho g) r m)

theorem shI_equiv (g : G) (m : M.V) : shI M (M.rho g m) = (shC M).rho g (shI M m) :=
  Subtype.ext (ContinuousMap.ext fun h => by
    show M.rho h (M.rho g m) = M.rho (h * g) m
    rw [map_mul]; rfl)

theorem shI_inj : Injective (shI M) := fun m m' h => by
  have := congrArg (fun f : (shC M).V => f.1 1) h
  change M.rho 1 m = M.rho 1 m' at this
  simpa only [map_one, Module.End.one_apply] using this

theorem shI_stable (g : G) : LinearMap.range (shI M) ≤ (LinearMap.range (shI M)).comap ((shC M).rho g) := by
  rintro v ⟨m, rfl⟩
  exact ⟨M.rho g m, shI_equiv M g m⟩

def shIP : Pair M (shC M) := Pair.ofMap (shI M) continuous_of_discreteTopology (shI_equiv M)

abbrev shQ : TRep R G := quotRep (shC M) (LinearMap.range (shI M)) (shI_stable M)

theorem shAdm : admitted (shIP M) (quotMk (shC M) _ (shI_stable M)) :=
  admissible_of_discrete_topology _ _ rfl rfl (shI_inj M)
    (LinearMap.exact_iff.2 (Submodule.ker_mkQ _)) (Submodule.mkQ_surjective _)

theorem shC_tors (hM : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) :
    ∀ f : (shC M).V, ∃ k : ℕ, 0 < k ∧ k • f = 0 := by
  intro f
  choose k hk using hM
  have hfin : (Set.range f.1).Finite := (isCompact_range f.1.continuous).finite_of_discrete
  obtain ⟨s, hs⟩ : ∃ s : Finset M.V, ∀ g, f.1 g ∈ s :=
    ⟨hfin.toFinset, fun g => hfin.mem_toFinset.2 ⟨g, rfl⟩⟩
  refine ⟨∏ m ∈ s, k m, Finset.prod_pos fun m _ => (hk m).1, ?_⟩
  have key : ∀ v ∈ s, (∏ m ∈ s, k m) • v = 0 := by
    intro v hv
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem k hv
    rw [hd, mul_comm, mul_smul, (hk v).2, smul_zero]
  exact Subtype.ext (ContinuousMap.ext fun g => key _ (hs g))

theorem shQ_tors (hM : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) :
    ∀ q : (shQ M).V, ∃ k : ℕ, 0 < k ∧ k • q = 0 := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H f =>
    obtain ⟨k, hk, hf⟩ := shC_tors M hM f
    refine ⟨k, hk, ?_⟩
    have := map_nsmul (LinearMap.range (shI M)).mkQ k f
    rw [hf, map_zero] at this
    exact this.symm

theorem shC_acyc (k : ℕ) (hk : 1 ≤ k) : Subsingleton ((shC M).H k) := by
  have hq := shapiro_holds R G (⊥ : Subgroup G) (M.resSub ⊥) (shC M) (coindEv _ _)
    (coindEv_isCoind _ _) ⟨fun _ => 1, continuous_const, fun x g => Subsingleton.elim _ _⟩
  have := triv_H_sub (M.resSub (⊥ : Subgroup G)) k hk
  exact (hq k).1.subsingleton

theorem shift_step (n : ℕ) (hQ : Subsingleton ((shQ M).H n)) : Subsingleton (M.H (n + 1)) := by
  obtain ⟨δ, -, hL⟩ := (lES_holds R _ _ _ _ _ (admissibility_holds R G _ _ _ _ _ (shAdm M))).1
  refine subsingleton_of_forall_eq 0 fun x => ?_
  have hC := shC_acyc M (n + 1) (by omega)
  have h0 : (shIP M).hom.H (n + 1) x = 0 := Subsingleton.elim _ _
  obtain ⟨q, rfl⟩ := (hL.exA n x).1 h0
  rw [Subsingleton.elim q 0, map_zero]

end ShiftC

end KernelCokernelKilling

end

end ReciprocityTheory.Coh

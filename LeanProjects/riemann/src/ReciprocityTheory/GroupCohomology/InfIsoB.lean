import ReciprocityTheory.GroupCohomology.InfIsoA

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function Topology

noncomputable section

universe u

namespace InflationIsomorphism

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Inv

variable {N : Subgroup G} [N.Normal]

theorem inv_disc {A : TRep R G} [DiscreteTopology A.V] {Q : TRep R (G ⧸ N)} {P : Pair Q A}
    (hP : IsInvRep A N Q P) : DiscreteTopology Q.V := hP.2.1.discreteTopology

theorem inv_mem {A : TRep R G} {Q : TRep R (G ⧸ N)} {P : Pair Q A} (hP : IsInvRep A N Q P) (q : Q.V) :
    ∀ g ∈ N, A.rho g (P.u q) = P.u q := (hP.2.2 _).1 ⟨q, rfl⟩

theorem inv_equiv {A : TRep R G} {Q : TRep R (G ⧸ N)} {P : Pair Q A} (hP : IsInvRep A N Q P) (g : G)
    (q : Q.V) : P.u (Q.rho (g : G ⧸ N) q) = A.rho g (P.u q) := by
  have h := P.equiv g q
  rw [hP.1] at h
  exact h

def invLin {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)} {PB : Pair QB B}
    (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB) (a : A.V →ₗ[R] B.V)
    (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) : QA.V →ₗ[R] QB.V :=
  (LinearEquiv.ofInjective PB.u hB.2.1.injective).symm.toLinearMap.comp
    ((a.comp PA.u).codRestrict (LinearMap.range PB.u) fun q => (hB.2.2 _).2 fun g hg => by
      rw [LinearMap.comp_apply, ← ha, inv_mem hA q g hg])

theorem invLin_spec {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)}
    {PB : Pair QB B} (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB) (a : A.V →ₗ[R] B.V)
    (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) (q : QA.V) : PB.u (invLin hA hB a ha q) = a (PA.u q) := by
  unfold invLin
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofInjective_symm_apply]
  rfl

def invPair {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)} {PB : Pair QB B}
    [DiscreteTopology A.V] (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB) (a : A.V →ₗ[R] B.V)
    (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) : Pair QA QB :=
  have := inv_disc hA
  Pair.ofMap (invLin hA hB a ha) continuous_of_discreteTopology fun y q => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    apply hB.2.1.injective
    rw [inv_equiv hB, invLin_spec, invLin_spec, inv_equiv hA, ha]

theorem invPair_u {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)}
    {PB : Pair QB B} [DiscreteTopology A.V] (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB)
    (a : A.V →ₗ[R] B.V) (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) (q : QA.V) :
    PB.u ((invPair hA hB a ha).u q) = a (PA.u q) := invLin_spec hA hB a ha q

theorem invPair_comm {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)}
    {PB : Pair QB B} [DiscreteTopology A.V] (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB)
    (a : A.V →ₗ[R] B.V) (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) (hac : Continuous a) (n : ℕ)
    (x : QA.coch.X n) :
    PB.hom.f n ((invPair hA hB a ha).hom.f n x) = (Pair.ofMap a hac ha).hom.f n (PA.hom.f n x) := by
  refine Subtype.ext (funext fun g => ?_)
  show PB.u ((invPair hA hB a ha).u (x.1 fun i => (invPair hA hB a ha).φ (PB.φ (g i)))) =
    a (PA.u (x.1 fun i => PA.φ (g i)))
  rw [invPair_u, hA.1, hB.1]
  rfl

theorem deg0 (A : TRep R G) (Q : TRep R (G ⧸ N)) (P : Pair Q A) (hP : IsInvRep A N Q P) :
    Bijective (P.hom.H 0) := by
  have hsub : ∀ {X : Type u} (f f' : Fin 0 → X), f = f' := fun f f' => Subsingleton.elim _ _
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [InflationRestrictionInvariants.H_mk, InflationRestrictionInvariants.mk_eq_zero_iff] at hz
    have h0 : P.hom.f 0 x = 0 := hz
    have hx0 : x = 0 := by
      refine Subtype.ext (funext fun f => ?_)
      have : P.u (x.1 fun i => P.φ (![] i)) = 0 := congrArg (fun y : A.coch.X 0 => y.1 ![]) h0
      apply hP.2.1.injective
      refine (show P.u (x.1 f) = P.u 0 from ?_)
      rw [map_zero, hsub f (fun i => P.φ (![] i))]
      exact this
    rw [InflationRestrictionInvariants.mk_eq_zero_iff]
    subst hx0
    exact Submodule.zero_mem _
  · intro z
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hy' : A.coch.d 0 y = 0 := hy
    have hinvG : ∀ a, A.rho a (y.1 ![]) = y.1 ![] := fun a => by
      have := congrArg (fun w : A.coch.X 1 => w.1 (InflationRestrictionInvariants.e1 a)) hy'
      simp only [InflationRestrictionInvariants.zeroDifferential_val] at this
      exact sub_eq_zero.1 this
    obtain ⟨q, hq⟩ := (hP.2.2 (y.1 ![])).2 fun g _ => hinvG g
    have hdq : Q.coch.d 0 (InflationRestrictionInvariants.const0 Q q) = 0 := by
      refine Subtype.ext (funext fun g => ?_)
      rw [InflationRestrictionInvariants.oneCochain_apply_fin_one, InflationRestrictionInvariants.zeroDifferential_val]
      show Q.rho (g 0) q - q = 0
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (g 0)
      rw [← ha, sub_eq_zero]
      apply hP.2.1.injective
      rw [inv_equiv hP, hq, hinvG]
    refine ⟨Submodule.Quotient.mk ⟨InflationRestrictionInvariants.const0 Q q, hdq⟩, ?_⟩
    rw [InflationRestrictionInvariants.H_mk]
    congr 1
    refine Subtype.ext (Subtype.ext (funext fun f => ?_))
    show P.u q = y.1 f
    rw [hq, hsub f ![]]

end Inv

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [LocallyCompactSpace G] {N : Subgroup G} [N.Normal]

abbrev Mbot (M : TRep R G) : TRep R (⊥ : Subgroup (G ⧸ N)) := M.res 1 continuous_const

def evC (M : TRep R G) [DiscreteTopology M.V] {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)}
    (hC : IsInvRep (CG M) N QC PC) : Pair QC (Mbot (N := N) M) :=
  have := inv_disc hC
  { φ := (⊥ : Subgroup (G ⧸ N)).subtype
    u := (coindEv (⊥ : Subgroup G) (M.resSub ⊥)).u.comp PC.u
    φ_cont := continuous_subtype_val
    u_cont := continuous_of_discreteTopology
    equiv := fun g m => by
      have hg : g = 1 := Subtype.ext (Subgroup.mem_bot.1 g.2)
      subst hg
      show _ = M.rho 1 _
      rw [map_one, map_one, map_one]
      rfl }

theorem evC_rho (M : TRep R G) [DiscreteTopology M.V] {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)}
    (hC : IsInvRep (CG M) N QC PC) (q : QC.V) (g : G) :
    (evC M hC).u (QC.rho (g : G ⧸ N) q) = (PC.u q).1 g := by
  show (PC.u (QC.rho (g : G ⧸ N) q)).1 1 = _
  rw [inv_equiv hC]
  show (PC.u q).1 (1 * g) = _
  rw [one_mul]

theorem QC_coind (M : TRep R G) [DiscreteTopology M.V] {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)}
    (hC : IsInvRep (CG M) N QC PC) : IsCoind (⊥ : Subgroup (G ⧸ N)) (Mbot M) QC (evC M hC) := by
  have := inv_disc hC
  have : DiscreteTopology (Mbot (N := N) M).V := ‹DiscreteTopology M.V›
  have := cmap_disc (G ⧸ N) (Mbot (N := N) M).V
  let j : QC.V → C(G ⧸ N, (Mbot (N := N) M).V) := fun q =>
    ⟨fun y => (evC M hC).u (QC.rho y q),
      (evC M hC).u_cont.comp (QC.cont.comp (f := fun y => (y, q)) (continuous_id.prodMk continuous_const))⟩
  have hj : ∀ q (g : G), j q (g : G ⧸ N) = (PC.u q).1 g := evC_rho M hC
  refine ⟨rfl, j, emb_disc _ fun q q' h => ?_, fun c g => rfl, fun f _ => ?_⟩
  · apply hC.2.1.injective
    refine Subtype.ext (ContinuousMap.ext fun g => ?_)
    rw [← hj, ← hj, h]
  · let F : (CG M).V := ⟨f.comp ⟨QuotientGroup.mk, continuous_quot_mk⟩, fun x g => by
      have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.1 x.2)
      subst hx
      show f ((((1 : (⊥ : Subgroup G)) : G) * g : G) : G ⧸ N) = M.rho 1 (f (g : G ⧸ N))
      rw [map_one, Subgroup.coe_one, one_mul]
      rfl⟩
    obtain ⟨q, hq⟩ := (hC.2.2 F).2 fun n hn => Subtype.ext (ContinuousMap.ext fun h => by
      show f ((h * n : G) : G ⧸ N) = f (h : G ⧸ N)
      rw [QuotientGroup.mk_mul_of_mem h hn])
    refine ⟨q, ContinuousMap.ext fun y => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hj, hq]
    rfl

theorem QC_acyc (M : TRep R G) [DiscreteTopology M.V] {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)}
    (hC : IsInvRep (CG M) N QC PC) (m : ℕ) (z : QC.H (m + 1)) : z = 0 := by
  have hq := shapiro_holds R (G ⧸ N) (⊥ : Subgroup (G ⧸ N)) (Mbot M) QC (evC M hC) (QC_coind M hC)
    ⟨fun _ => 1, continuous_const, fun x g => by
      have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.1 x.2)
      rw [hx, one_mul]⟩
  have : Subsingleton (⊥ : Subgroup (G ⧸ N)) :=
    ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)⟩
  refine (hq (m + 1)).1 ?_
  rw [map_zero]
  exact FiniteLevelCohomology.H_succ_trivial _ m _

end InflationIsomorphism

end

end ReciprocityTheory.Coh

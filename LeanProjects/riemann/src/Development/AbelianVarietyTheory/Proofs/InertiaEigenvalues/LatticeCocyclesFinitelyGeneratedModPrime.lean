import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1H2LocalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingSubgroupEquivBicontinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenOfFgOfSpanEqTop
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.LatRed

section Red

variable {O V : Type} [CommRing O] [AddCommGroup V] [Module O V]

def Red (T : Submodule O V) (ϖ : O) : Type :=
  ↥T ⧸ LinearMap.range (ϖ • LinearMap.id : ↥T →ₗ[O] ↥T)

variable (T : Submodule O V) (ϖ : O)

instance : AddCommGroup (Red T ϖ) :=
  inferInstanceAs (AddCommGroup (↥T ⧸ LinearMap.range (ϖ • LinearMap.id : ↥T →ₗ[O] ↥T)))

instance : Module O (Red T ϖ) :=
  inferInstanceAs (Module O (↥T ⧸ LinearMap.range (ϖ • LinearMap.id : ↥T →ₗ[O] ↥T)))

instance : TopologicalSpace (Red T ϖ) := ⊥

instance : DiscreteTopology (Red T ϖ) := ⟨rfl⟩

def mk : ↥T →ₗ[O] Red T ϖ := Submodule.mkQ _

variable {T ϖ}

theorem mk_surjective : Function.Surjective (mk T ϖ) := Submodule.mkQ_surjective _

theorem mk_eq_zero_iff (t : ↥T) : mk T ϖ t = 0 ↔ ∃ u : ↥T, ϖ • u = t := by
  change Submodule.Quotient.mk t = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  rfl

def act (ϖ : O) (σ : V →ₗ[O] V) (hσ : ∀ x ∈ T, σ x ∈ T) : Red T ϖ →ₗ[O] Red T ϖ :=
  Submodule.mapQ _ _ (σ.restrict hσ) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨σ.restrict hσ u, by simp⟩)

theorem act_mk (σ : V →ₗ[O] V) (hσ : ∀ x ∈ T, σ x ∈ T) (t : ↥T) :
    act ϖ σ hσ (mk T ϖ t) = mk T ϖ (σ.restrict hσ t) := rfl

end Red

section Top

variable {O V LL : Type} [CommRing O] [AddCommGroup V] [Module O V] [Field LL] [Algebra O LL]
  [Module LL V] [IsScalarTower O LL V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousConstSMul LL V] {T : Submodule O V} {ϖ : O}

theorem isOpen_smul (hT : IsOpen (T : Set V)) (hϖ : algebraMap O LL ϖ ≠ 0) :
    IsOpen {v : V | ∃ u : ↥T, ϖ • (u : V) = v} := by
  have : {v : V | ∃ u : ↥T, ϖ • (u : V) = v} =
      (fun v => (algebraMap O LL ϖ)⁻¹ • v) ⁻¹' (T : Set V) := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨u, rfl⟩
      rw [← algebraMap_smul LL ϖ (u : V), smul_smul, inv_mul_cancel₀ hϖ, one_smul]
      exact u.2
    · intro h
      refine ⟨⟨_, h⟩, ?_⟩
      change ϖ • ((algebraMap O LL ϖ)⁻¹ • v) = v
      rw [← algebraMap_smul LL ϖ, smul_smul, mul_inv_cancel₀ hϖ, one_smul]
  rw [this]
  exact hT.preimage (continuous_const_smul _)

omit [Field LL] [Algebra O LL] [Module LL V] [IsScalarTower O LL V] [ContinuousConstSMul LL V] in

theorem isLocallyConstant_mk {X : Type} [TopologicalSpace X]
    (hS : IsOpen {v : V | ∃ u : ↥T, ϖ • (u : V) = v}) (f : X → V) (hf : Continuous f)
    (hfT : ∀ x, f x ∈ T) : IsLocallyConstant fun x => mk T ϖ ⟨f x, hfT x⟩ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hU : IsOpen ((fun y => f y + -f x) ⁻¹' {v : V | ∃ u : ↥T, ϖ • (u : V) = v}) :=
    hS.preimage (hf.add continuous_const)
  have hx : x ∈ (fun y => f y + -f x) ⁻¹' {v : V | ∃ u : ↥T, ϖ • (u : V) = v} :=
    ⟨0, by simp⟩
  filter_upwards [hU.mem_nhds hx] with y hy
  obtain ⟨u, hu⟩ := hy
  rw [← sub_eq_zero, ← map_sub (mk T ϖ), mk_eq_zero_iff]
  refine ⟨u, Subtype.ext ?_⟩
  simp [hu, sub_eq_add_neg]

end Top

end GlobalTheory.LatRed

namespace GlobalTheory.LatRed

def ofAction (N : ℕ) {G M : Type} [Monoid G] [AddCommGroup M] [Module (ZMod N) M]
    (a : G → M →+ M) (h1 : ∀ m, a 1 m = m) (hmul : ∀ g h m, a (g * h) m = a g (a h m)) :
    Representation (ZMod N) G M where
  toFun g := AddMonoidHom.toZModLinearMap N (a g)
  map_one' := LinearMap.ext h1
  map_mul' g h := LinearMap.ext (hmul g h)

section Lift

variable {G : Type} [Group G] [TopologicalSpace G] {LL O V : Type} [Field LL] [CommRing O]
  [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] {ρ : Representation LL G V}

omit [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] in
theorem cob_apply (x : V) (g : G) : Formalism.WeaklyAdmissibleFiltrations.cob ρ x g = ρ g x - x := rfl

theorem representationCoboundary_mem_continuousCocycles (hcont : ∀ x, Continuous fun g => ρ g x) (x : V) :
    Formalism.WeaklyAdmissibleFiltrations.cob ρ x ∈ Formalism.WeaklyAdmissibleFiltrations.continuousCocycles ρ := by
  refine ⟨?_, fun g h => ?_⟩
  · have : Formalism.WeaklyAdmissibleFiltrations.cob ρ x = fun g => ρ g x + -x :=
      funext fun g => by rw [cob_apply, sub_eq_add_neg]
    rw [this]
    exact (hcont x).add continuous_const
  · simp only [cob_apply, map_mul, Module.End.mul_apply, map_sub]
    abel

theorem lift_of_mod (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (hcont : ∀ x, Continuous fun g => ρ g x)
    (ϖ : O) (hϖ : algebraMap O LL ϖ ≠ 0) (d : ↥(Formalism.WeaklyAdmissibleFiltrations.latticeCocycles L)) (x : V) (hx : x ∈ L.T)
    (hd : ∀ g, ∃ u : ↥L.T, ϖ • (u : V) = (d : G → V) g - (ρ g x - x)) :
    ∃ c' : ↥(Formalism.WeaklyAdmissibleFiltrations.latticeCocycles L), ((d : G → V) - ϖ • (c' : G → V)) ∈ Formalism.WeaklyAdmissibleFiltrations.latticeCoboundaries L := by
  have hdZ : (d : G → V) ∈ Formalism.WeaklyAdmissibleFiltrations.continuousCocycles ρ := (Submodule.mem_inf.1 d.2).1
  let f : G → V := (algebraMap O LL ϖ)⁻¹ • ((d : G → V) - Formalism.WeaklyAdmissibleFiltrations.cob ρ x)
  have hf : ∀ g, f g = (algebraMap O LL ϖ)⁻¹ • ((d : G → V) g - (ρ g x - x)) := fun g => rfl
  have hfZ : f ∈ Formalism.WeaklyAdmissibleFiltrations.continuousCocycles ρ :=
    (Formalism.WeaklyAdmissibleFiltrations.continuousCocycles ρ).smul_mem _ ((Formalism.WeaklyAdmissibleFiltrations.continuousCocycles ρ).sub_mem hdZ (representationCoboundary_mem_continuousCocycles hcont x))
  have hfT : ∀ g, f g ∈ L.T := by
    intro g
    obtain ⟨u, hu⟩ := hd g
    rw [hf, ← hu, ← algebraMap_smul LL ϖ (u : V), smul_smul, inv_mul_cancel₀ hϖ, one_smul]
    exact u.2
  refine ⟨⟨f, Submodule.mem_inf.2 ⟨hfZ, Submodule.mem_pi.2 fun g _ => hfT g⟩⟩, ?_⟩
  refine Submodule.mem_map.2 ⟨x, hx, funext fun g => ?_⟩
  change Formalism.WeaklyAdmissibleFiltrations.cob ρ x g = (d : G → V) g - ϖ • f g
  rw [hf, ← algebraMap_smul LL ϖ, smul_smul, mul_inv_cancel₀ hϖ, one_smul, cob_apply]
  abel

end Lift

end GlobalTheory.LatRed

namespace GlobalTheory.LatRed

theorem cocycles_fg_mod_l : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∃ s : Finset ↥(latticeCocycles LA), ∀ c : ↥(latticeCocycles LA), ∃ (a : ↥(latticeCocycles LA) → O) (c' : ↥(latticeCocycles LA)), ((c : ↥(GK K) → A.V) - ∑ i ∈ s, a i • (i : ↥(GK K) → A.V) - ((l : ℕ) : O) • (c' : ↥(GK K) → A.V)) ∈ latticeCoboundaries LA := by
  intro hT l _ K LL _ _ _ O _ _ hO A LA
  classical
  haveI : IsTopologicalRing LL := hO.2.2.2.1
  haveI hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  set ϖ : O := ((l : ℕ) : O) with hϖdef
  have hϖ : algebraMap O LL ϖ ≠ 0 := by
    rw [hϖdef, map_natCast, ← map_natCast (algebraMap ℚ_[l] LL) l]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hTo : IsOpen (LA.T : Set A.V) :=
    GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hO.2.2.2.2 LA.T LA.fg LA.span
  have hS := isOpen_smul (LL := LL) (ϖ := ϖ) hTo hϖ
  have hl1 : ∀ m : Red LA.T ϖ, (l ^ 1) • m = 0 := by
    intro m
    obtain ⟨t, rfl⟩ := mk_surjective m
    rw [pow_one, ← map_nsmul, mk_eq_zero_iff]
    exact ⟨t, by rw [hϖdef, Nat.cast_smul_eq_nsmul]⟩
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  letI : Module (ZMod (l ^ 1)) (Red LA.T ϖ) := AddCommGroup.zmodModule hl1
  haveI hfin : Finite (Red LA.T ϖ) := by
    haveI : Module.Finite O ↥LA.T := Module.Finite.iff_fg.2 LA.fg
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O ↥LA.T
    haveI : Finite (O ⧸ Ideal.span {ϖ}) := by
      have := (GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hO).2.2.1 1
      simpa [pow_one] using this
    have hqs : Function.Surjective (Ideal.Quotient.mk (Ideal.span {ϖ})) :=
      Ideal.Quotient.mk_surjective
    refine Finite.of_surjective
      (fun v : Fin n → O ⧸ Ideal.span {ϖ} => mk LA.T ϖ (f (fun k => Function.surjInv hqs (v k)))) ?_
    intro m
    obtain ⟨t, rfl⟩ := mk_surjective m
    obtain ⟨c, rfl⟩ := hf t
    refine ⟨fun k => Ideal.Quotient.mk (Ideal.span {ϖ}) (c k), ?_⟩
    show mk LA.T ϖ (f _) = mk LA.T ϖ (f c)
    rw [← sub_eq_zero, ← map_sub (mk LA.T ϖ), ← map_sub f, mk_eq_zero_iff]
    have he : ∀ k, ∃ e, Function.surjInv hqs (Ideal.Quotient.mk (Ideal.span {ϖ}) (c k)) - c k = ϖ * e := by
      intro k
      have h0 : Ideal.Quotient.mk (Ideal.span {ϖ})
          (Function.surjInv hqs (Ideal.Quotient.mk (Ideal.span {ϖ}) (c k)) - c k) = 0 := by
        rw [map_sub, Function.surjInv_eq hqs, sub_self]
      obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
      exact ⟨e, by rw [← he, mul_comm]⟩
    choose e he using he
    refine ⟨f e, ?_⟩
    rw [← map_smul]
    congr 1
    funext k
    simp [he]
  let Φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hΦ : Continuous Φ ∧ Continuous Φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let ρT : ↥(GK K) → A.V →ₗ[O] A.V := fun g => (A.ρ g).restrictScalars O
  have hρT : ∀ g, ∀ x ∈ LA.T, ρT g x ∈ LA.T := LA.stable
  let a : Formalism.GaloisCohomology.GK l K.1 → Red LA.T ϖ →+ Red LA.T ϖ :=
    fun g' => (act ϖ (ρT (Φ.symm g')) (hρT _)).toAddMonoidHom
  have ha1 : ∀ m, a 1 m = m := by
    intro m
    obtain ⟨t, rfl⟩ := mk_surjective m
    change act ϖ (ρT (Φ.symm 1)) (hρT _) (mk LA.T ϖ t) = mk LA.T ϖ t
    rw [act_mk]
    congr 1
    apply Subtype.ext
    simp [ρT]
  have hamul : ∀ g h m, a (g * h) m = a g (a h m) := by
    intro g h m
    obtain ⟨t, rfl⟩ := mk_surjective m
    change act ϖ (ρT (Φ.symm (g * h))) (hρT _) (mk LA.T ϖ t) =
      act ϖ (ρT (Φ.symm g)) (hρT _) (act ϖ (ρT (Φ.symm h)) (hρT _) (mk LA.T ϖ t))
    rw [act_mk, act_mk, act_mk]
    congr 1
    apply Subtype.ext
    simp [ρT, map_mul]
  let ρb : Representation (ZMod (l ^ 1)) (Formalism.GaloisCohomology.GK l K.1) (Red LA.T ϖ) :=
    ofAction (l ^ 1) a ha1 hamul
  have hρb : ReciprocityTheory.Gal.ContAction ρb := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    obtain ⟨t, rfl⟩ := mk_surjective m
    exact (isLocallyConstant_mk hS (fun g => A.ρ g t) (A.cont _)
      (fun g => hρT g t t.2)).continuous.comp hΦ.2
  have hH1 : Finite (ReciprocityTheory.Gal.H1 ρb) :=
    (GlobalTheory.T.finite_H1_H2_local hT l K.1 K.2 1 (Red LA.T ϖ) ρb one_pos hρb).1
  have hcT : ∀ (c : ↥(latticeCocycles LA)) (g : ↥(GK K)), (c : ↥(GK K) → A.V) g ∈ LA.T :=
    fun c g => Submodule.mem_pi.1 (Submodule.mem_inf.1 c.2).2 g (Set.mem_univ g)
  let ev : ↥(latticeCocycles LA) → ↥(GK K) → ↥LA.T := fun c g => ⟨(c : ↥(GK K) → A.V) g, hcT c g⟩
  have hred : ∀ c : ↥(latticeCocycles LA), (fun g' => mk LA.T ϖ (ev c (Φ.symm g'))) ∈ ReciprocityTheory.Gal.Z1 ρb := by
    intro c
    have hcZ : (c : ↥(GK K) → A.V) ∈ continuousCocycles A.ρ := (Submodule.mem_inf.1 c.2).1
    refine ⟨(isLocallyConstant_mk hS _ hcZ.1 (hcT c)).continuous.comp hΦ.2, fun g h => ?_⟩
    change mk LA.T ϖ (ev c (Φ.symm (g * h))) = mk LA.T ϖ (ev c (Φ.symm g)) +
      act ϖ (ρT (Φ.symm g)) (hρT _) (mk LA.T ϖ (ev c (Φ.symm h)))
    rw [act_mk, ← map_add]
    congr 1
    apply Subtype.ext
    simp [ev, ρT, map_mul, hcZ.2]
  let F : ↥(latticeCocycles LA) → ReciprocityTheory.Gal.H1 ρb := fun c => Submodule.Quotient.mk ⟨_, hred c⟩
  haveI : Nonempty ↥(latticeCocycles LA) := ⟨0⟩
  have hfr : (Set.range F).Finite := Set.toFinite _
  refine ⟨hfr.toFinset.image (Function.invFun F), fun c => ?_⟩
  set i := Function.invFun F (F c) with hi
  have hFi : F i = F c := Function.invFun_eq ⟨c, rfl⟩
  have hmem : i ∈ hfr.toFinset.image (Function.invFun F) :=
    Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset _).2 ⟨c, rfl⟩)
  have hB := (Submodule.Quotient.eq _).1 hFi.symm
  have hB' : (((⟨_, hred c⟩ : ReciprocityTheory.Gal.Z1 ρb) - ⟨_, hred i⟩ : ReciprocityTheory.Gal.Z1 ρb) :
      Formalism.GaloisCohomology.GK l K.1 → Red LA.T ϖ) ∈ ReciprocityTheory.Gal.B1 ρb := hB
  obtain ⟨m, hm⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 ρb _).1 hB'
  obtain ⟨t, rfl⟩ := mk_surjective m
  have hd : ∀ g, ∃ u : ↥LA.T, ϖ • (u : A.V) =
      ((c - i : ↥(latticeCocycles LA)) : ↥(GK K) → A.V) g - (A.ρ g t - t) := by
    intro g
    have h1 := hm (Φ g)
    change mk LA.T ϖ (ev c (Φ.symm (Φ g))) - mk LA.T ϖ (ev i (Φ.symm (Φ g))) =
      act ϖ (ρT (Φ.symm (Φ g))) (hρT _) (mk LA.T ϖ t) - mk LA.T ϖ t at h1
    rw [MulEquiv.symm_apply_apply, act_mk, ← map_sub (mk LA.T ϖ), ← map_sub (mk LA.T ϖ),
      ← sub_eq_zero, ← map_sub (mk LA.T ϖ), mk_eq_zero_iff] at h1
    obtain ⟨u, hu⟩ := h1
    refine ⟨u, ?_⟩
    have := congrArg Subtype.val hu
    simpa [ev, ρT] using this
  obtain ⟨c', hc'⟩ := lift_of_mod LA A.cont ϖ hϖ (c - i) t t.2 hd
  refine ⟨fun j => if j = i then 1 else 0, c', ?_⟩
  have hsum : ∑ j ∈ hfr.toFinset.image (Function.invFun F),
      (if j = i then (1 : O) else 0) • (j : ↥(GK K) → A.V) = (i : ↥(GK K) → A.V) := by
    rw [Finset.sum_eq_single_of_mem i hmem (fun j _ hj => by rw [if_neg hj, zero_smul]), if_pos rfl,
      one_smul]
  rw [hsum]
  simpa using hc'

end GlobalTheory.LatRed

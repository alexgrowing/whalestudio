import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResSel.BaseChange

theorem finrank_eq_of_coord {k K V W : Type} [Field k] [Field K] [Algebra k K] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module K W] (S : Submodule k V) (T : Submodule K W) (J : V →+ W) (L : (K →ₗ[k] k) → W →+ V)
    (hJ : ∀ (c : k) v, J (c • v) = algebraMap k K c • J v) (hL : ∀ lam a v, L lam (a • J v) = lam a • v)
    (hW : ∀ w, ∃ (n : Type) (s : Finset n) (e : n → K) (lam : n → K →ₗ[k] k), w = ∑ j ∈ s, e j • J (L (lam j) w))
    (hS : ∀ v ∈ S, J v ∈ T) (hT : ∀ lam, ∀ w ∈ T, L lam w ∈ S) [Module.Finite k S] :
    Module.Finite K T ∧ Module.finrank K T = Module.finrank k S := by
  let b := Module.finBasis k S
  let w : Fin (Module.finrank k S) → T := fun i => ⟨J (b i), hS _ (b i).2⟩
  have hli : LinearIndependent K w := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    rw [← Module.forall_dual_apply_eq_zero_iff k]
    intro lam
    have h1 : ∑ i, a i • J (b i) = 0 := by
      have := congrArg Subtype.val ha
      simpa [w] using this
    have h2 : ∑ i, lam (a i) • b i = 0 := by
      apply Subtype.ext
      have := congrArg (L lam) h1
      simpa [map_sum, hL] using this
    exact Fintype.linearIndependent_iff.1 b.linearIndependent _ h2 i
  have hJs : ∀ v : S, (⟨J v, hS _ v.2⟩ : T) ∈ Submodule.span K (Set.range w) := by
    intro v
    have : (⟨J v, hS _ v.2⟩ : T) = ∑ i, algebraMap k K (b.repr v i) • w i := by
      apply Subtype.ext
      have e := congrArg (fun x : S => J x) (b.sum_repr v)
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, map_sum, hJ] at e
      simp [w, e]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsp : ⊤ ≤ Submodule.span K (Set.range w) := by
    intro x _
    obtain ⟨n, s, e, lam, h⟩ := hW x.1
    have : x = ∑ j ∈ s, e j • (⟨J (L (lam j) x.1), hS _ (hT _ _ x.2)⟩ : T) := by
      apply Subtype.ext
      simpa using h
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hJs ⟨_, hT _ _ x.2⟩)
  let B := Module.Basis.mk hli hsp
  exact ⟨Module.Finite.of_basis B, by rw [Module.finrank_eq_card_basis B, Fintype.card_fin]⟩

section General

variable {R R' : Type} [CommRing R] [CommRing R'] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R' M']
  (rho : Representation R Γ M) (rho' : Representation R' Γ M') (u : M →+ M') (hu : Continuous u)
  (he : ∀ g m, u (rho g m) = rho' g (u m))

def cocycleMapOfEquivariant : Z1 rho →+ Z1 rho' where
  toFun z := ⟨fun g => u (z.1 g), hu.comp z.2.1, fun g h => by
    beta_reduce
    rw [z.2.2, map_add, he]⟩
  map_add' z w := Subtype.ext (funext fun g => map_add u _ _)
  map_zero' := Subtype.ext (funext fun g => map_zero u)

def h1MapOfAdditive : H1 rho →+ H1 rho' :=
  QuotientAddGroup.map ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup ((B1 rho').comap (Z1 rho').subtype).toAddSubgroup
    (cocycleMapOfEquivariant rho rho' u hu he) fun z hz => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 rho _).1 hz
    refine (mem_coboundaries1 _ _).2 ⟨u m, fun g => ?_⟩
    change u (z.1 g) = _
    rw [show z.1 g = _ from hm g, map_sub, he]

theorem h1MapOfAdditive_mk (z : Z1 rho) :
    h1MapOfAdditive rho rho' u hu he (Submodule.Quotient.mk z) = Submodule.Quotient.mk (cocycleMapOfEquivariant rho rho' u hu he z) := rfl

theorem res_addH1 {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (h1MapOfAdditive rho rho' u hu he x) =
      h1MapOfAdditive (rho.comp phi) (rho'.comp phi) u hu (fun g m => he (phi g) m) (resH1 rho phi hphi x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem addH1_ur (J : Subgroup Γ) (x : H1 rho) (hx : x ∈ H1ur rho J) :
    h1MapOfAdditive rho rho' u hu he x ∈ H1ur rho' J := by
  have h0 : resH1 rho J.subtype continuous_subtype_val x = 0 := hx
  exact (res_addH1 rho rho' u hu he J.subtype continuous_subtype_val x).trans
    ((congrArg _ h0).trans (map_zero _))

end General

section Coef

variable {O K K' : Type} [CommRing O] [CommRing K] [CommRing K'] [Algebra O K] [Algebra O K'] (f : K →ₗ[O] K') (r : ℕ)

def vecAdd : (Fin r → K) →+ (Fin r → K') where
  toFun m a := f (m a)
  map_add' m m' := funext fun a => map_add f _ _
  map_zero' := funext fun a => map_zero f

theorem vecAdd_repOn {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (g : Γ) (m : Fin r → K) :
    vecAdd f r (repOn ρ (1 : Γ →* Kˣ) K g m) = repOn ρ (1 : Γ →* K'ˣ) K' g (vecAdd f r m) := by
  funext a
  simp [vecAdd, repOn, matAct, map_sum, ← Algebra.smul_def]

end Coef

section Sel

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i))
  {K K' : Type} [CommRing K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]
  [CommRing K'] [Algebra (X.O0 i) K'] [TopologicalSpace K'] [DiscreteTopology K'] (f : K →ₗ[X.O0 i] K')

theorem addH1_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ (1 : GE N →* Kˣ) K).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v) :
    h1MapOfAdditive ((repOn ρ (1 : GE N →* Kˣ) K).comp (DecV N v).subtype) ((repOn ρ (1 : GE N →* K'ˣ) K').comp (DecV N v).subtype)
      (vecAdd f r) continuous_of_discreteTopology (fun g m => vecAdd_repOn f ρ g.1 m) x ∈
      bkOn bkP i ρ (1 : GE N →* K'ˣ) K' v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · rw [← one_smul K x]
    generalize (1 : K) = t
    induction hx using Submodule.span_induction generalizing t with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨cocycleMapOfEquivariant _ _ (vecAdd f r) continuous_of_discreteTopology
        (fun g m => vecAdd_repOn f ρ g.1 m) (t • z), c, y, f (t * b), hc, hy, fun g a => ?_, rfl⟩
      change f (t * (z : ↥(DecV N v) → Fin r → K) g a) = _
      rw [hz, algebraMap_smul, algebraMap_smul, mul_smul_comm, map_smul]
    | zero => rw [smul_zero, map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [smul_add, map_add]; exact Submodule.add_mem _ (hx t) (hy t)
    | smul a x _ hx => rw [smul_smul]; exact hx _
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

def coefH1 : H1 (repOn ρ (1 : GE N →* Kˣ) K) →+ H1 (repOn ρ (1 : GE N →* K'ˣ) K') :=
  h1MapOfAdditive (repOn ρ (1 : GE N →* Kˣ) K) (repOn ρ (1 : GE N →* K'ˣ) K') (vecAdd f r) continuous_of_discreteTopology
    (vecAdd_repOn f ρ)

theorem coefH1_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ (1 : GE N →* Kˣ) K))
    (hx : x ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K Q) : coefH1 i ρ f x ∈ selOn bkP i ρ (1 : GE N →* K'ˣ) K' Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_addH1 (repOn ρ (1 : GE N →* Kˣ) K) (repOn ρ (1 : GE N →* K'ˣ) K') (vecAdd f r) continuous_of_discreteTopology
    (vecAdd_repOn f ρ) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact addH1_mem_bkOn bkP i ρ f v _ hv
  · exact Submodule.mem_top
  · exact addH1_ur _ _ _ _ _ _ _ hv

end Sel

theorem selOn_baseChange (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (k : Type) [Field k] [Algebra (X.O0 i) k] [TopologicalSpace k]
    [DiscreteTopology k] (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]
    (hk : IsRes i k) (hs : Function.Surjective (algebraMap (X.O0 i) k)) (hK : IsRes i K) (Q : Finset (PlE D.host))
    (hfin : Module.Finite k (selOn bkP i ρ (1 : GE N →* kˣ) k Q)) :
    Module.Finite K (selOn bkP i ρ (1 : GE N →* Kˣ) K Q) ∧
      Module.finrank K (selOn bkP i ρ (1 : GE N →* Kˣ) K Q) = Module.finrank k (selOn bkP i ρ (1 : GE N →* kˣ) k Q) := by
  classical
  have hker : RingHom.ker (algebraMap (X.O0 i) k) ≤ RingHom.ker (algebraMap (X.O0 i) K) := fun x hx =>
    hK x (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _) hx)
  let ι : k →+* K := (algebraMap (X.O0 i) k).liftOfSurjective hs ⟨algebraMap (X.O0 i) K, hker⟩
  letI : Algebra k K := ι.toAlgebra
  haveI : IsScalarTower (X.O0 i) k K := IsScalarTower.of_algebraMap_eq fun x =>
    ((algebraMap (X.O0 i) k).liftOfRightInverse_comp_apply _ _ ⟨algebraMap (X.O0 i) K, hker⟩ x).symm
  haveI : CompactSpace (GE N) := inferInstance
  refine finrank_eq_of_coord _ _ (coefH1 i ρ ((Algebra.linearMap k K).restrictScalars (X.O0 i)))
    (fun lam => coefH1 i ρ (lam.restrictScalars (X.O0 i))) ?_ ?_ ?_
    (fun v hv => coefH1_mem_selOn bkP i ρ _ Q v hv) (fun lam v hv => coefH1_mem_selOn bkP i ρ _ Q v hv)
  · intro c v
    induction v using Submodule.Quotient.induction_on with
    | H z =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => funext fun a => ?_))
      exact map_mul (algebraMap k K) c (z.1 g a)
  · intro lam t v
    induction v using Submodule.Quotient.induction_on with
    | H z =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => funext fun a => ?_))
      change lam (t * algebraMap k K (z.1 g a)) = lam t * z.1 g a
      rw [mul_comm t, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  · intro w
    induction w using Submodule.Quotient.induction_on with
    | H z =>
      let b := Module.Basis.ofVectorSpace k K
      have hf : (Set.range z.1).Finite := (isCompact_range z.2.1).finite_of_discrete
      let s := hf.toFinset.biUnion fun m => Finset.univ.biUnion fun a => (b.repr (m a)).support
      refine ⟨_, s, b, b.coord, ?_⟩
      have key : z = ∑ j ∈ s, b j • cocycleMapOfEquivariant _ _ (vecAdd ((Algebra.linearMap k K).restrictScalars (X.O0 i)) _)
          continuous_of_discreteTopology (vecAdd_repOn _ ρ) (cocycleMapOfEquivariant _ _ (vecAdd ((b.coord j).restrictScalars (X.O0 i)) _)
          continuous_of_discreteTopology (vecAdd_repOn _ ρ) z) := by
        refine Subtype.ext (funext fun g => funext fun a => ?_)
        rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, Finset.sum_apply]
        change _ = ∑ j ∈ s, b j * algebraMap k K (b.repr (z.1 g a) j)
        have hsub : (b.repr (z.1 g a)).support ⊆ s := fun j hj =>
          Finset.mem_biUnion.2 ⟨z.1 g, by simp, Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hj⟩⟩
        conv_lhs => rw [← b.linearCombination_repr (z.1 g a), Finsupp.linearCombination_apply,
          Finsupp.sum_of_support_subset _ hsub (fun j c => c • b j) (fun j _ => zero_smul _ _)]
        exact Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def, mul_comm]
      refine (congrArg (Submodule.mkQ _) key).trans ?_
      rw [map_sum]
      rfl

end GlobalTheory.ResSel.BaseChange

end

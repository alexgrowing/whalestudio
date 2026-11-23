import ReciprocityTheory.GroupCohomology.CardLenStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.ConnNatHolds
import ReciprocityTheory.GroupCohomology.PairHomFCoeOfId
import ReciprocityTheory.GroupCohomology.InfRes
import ReciprocityTheory.GroupCohomology.Shapiro
import ReciprocityTheory.GroupCohomology.FiniteLevel

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function Topology

noncomputable section

universe u

namespace InflationIsomorphism

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def stabN (A : TRep R G) (N : Subgroup G) (a : A.V) : Subgroup N where
  carrier := {n | A.rho (n : G) a = a}
  mul_mem' {x y} hx hy := by
    show A.rho ((x * y : N) : G) a = a
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, show A.rho (y : G) a = a from hy]
    exact hx
  one_mem' := by show A.rho ((1 : N) : G) a = a; simp
  inv_mem' {x} hx := by
    show A.rho ((x⁻¹ : N) : G) a = a
    have hx' : A.rho (x : G) a = a := hx
    conv_lhs => rw [← hx']
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one,
      Module.End.one_apply]

theorem stabN_open (A : TRep R G) [DiscreteTopology A.V] (N : Subgroup G) (a : A.V) :
    IsOpen (stabN A N a : Set N) := by
  have hc : Continuous fun n : N => A.rho (n : G) a :=
    A.cont.comp (f := fun n : N => ((n : G), a)) (continuous_subtype_val.prodMk continuous_const)
  exact (isOpen_discrete {a}).preimage hc

theorem finite_quot_of_open {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] (W : Subgroup K) (hW : IsOpen (W : Set K)) : Finite (K ⧸ W) := by
  have := QuotientGroup.discreteTopology hW
  exact finite_of_compact_of_discrete

theorem inv_lift [CompactSpace G] (N : Subgroup G) (hN : IsClosed (N : Set G))
    (hW : ∀ W : Subgroup N, IsOpen (W : Set N) → IsUnit (W.index : R))
    (A B : TRep R G) [DiscreteTopology A.V] (p : A.V →ₗ[R] B.V)
    (hp : ∀ g a, p (A.rho g a) = B.rho g (p a)) (hs : Surjective p) (b : B.V)
    (hb : ∀ g ∈ N, B.rho g b = b) : ∃ a, (∀ g ∈ N, A.rho g a = a) ∧ p a = b := by
  have : CompactSpace N := isCompact_iff_compactSpace.1 hN.isCompact
  obtain ⟨a₀, rfl⟩ := hs b
  set W := stabN A N a₀
  have hWo := stabN_open A N a₀
  have : Finite (N ⧸ W) := finite_quot_of_open W hWo
  have : Fintype (N ⧸ W) := Fintype.ofFinite _
  obtain ⟨v, hv⟩ := hW W hWo
  set s : A.V := ∑ c : N ⧸ W, A.rho ((c.out : N) : G) a₀ with hs_def
  have key : ∀ (x : N), A.rho ((x : N) : G) a₀ = A.rho (((QuotientGroup.mk x : N ⧸ W).out : N) : G) a₀ := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul W x
    rw [hh, Subgroup.coe_mul, map_mul, Module.End.mul_apply, show A.rho ((h : N) : G) a₀ = a₀ from h.2]
  have hinv : ∀ g ∈ N, A.rho g s = s := by
    intro g hg
    rw [hs_def, map_sum]
    have e : ∀ c : N ⧸ W, A.rho g (A.rho ((c.out : N) : G) a₀) =
        A.rho ((((⟨g, hg⟩ : N) • c).out : N) : G) a₀ := by
      intro c
      rw [← Module.End.mul_apply, ← map_mul]
      have := key (⟨g, hg⟩ * c.out)
      rw [Subgroup.coe_mul] at this
      rw [this]
      congr 4
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rfl
    simp only [e]
    exact Fintype.sum_equiv (MulAction.toPerm (⟨g, hg⟩ : N)) _ _ (fun _ => rfl)
  refine ⟨((v⁻¹ : Rˣ) : R) • s, fun g hg => by rw [map_smul, hinv g hg], ?_⟩
  rw [map_smul, hs_def, map_sum]
  simp only [hp, fun c : N ⧸ W => hb _ c.out.2]
  have hcard : (Finset.univ : Finset (N ⧸ W)).card = W.index := by
    rw [Subgroup.index, Nat.card_eq_fintype_card, Finset.card_univ]
  rw [Finset.sum_const, hcard, ← Nat.cast_smul_eq_nsmul R, ← hv, smul_smul, Units.inv_mul, one_smul]

theorem emb_disc {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [DiscreteTopology X]
    [DiscreteTopology Y] (f : X → Y) (hf : Injective f) : IsEmbedding f := by
  refine ⟨⟨(DiscreteTopology.eq_bot).trans (eq_bot_of_singletons_open fun x => ?_).symm⟩, hf⟩
  refine isOpen_induced_iff.2 ⟨{f x}, isOpen_discrete _, ?_⟩
  ext y; simp [hf.eq_iff]

theorem cmap_disc (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    [DiscreteTopology Y] : DiscreteTopology C(X, Y) := by
  refine discreteTopology_iff_isOpen_singleton.2 fun f => ?_
  have hfin : (Set.range f).Finite := (isCompact_range f.continuous).finite_of_discrete
  have hset : ({f} : Set C(X, Y)) = ⋂ y ∈ Set.range f, {g : C(X, Y) | Set.MapsTo g (f ⁻¹' {y}) {y}} := by
    ext g
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro rfl y _ x hx; exact hx
    · intro h
      ext x
      exact h (f x) ⟨x, rfl⟩ (show x ∈ f ⁻¹' {f x} from rfl)
  rw [hset]
  exact hfin.isOpen_biInter fun y _ => ContinuousMap.isOpen_setOfPred_mapsTo
    ((isClosed_discrete {y}).preimage f.continuous).isCompact (isOpen_discrete _)

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

abbrev CG (M : TRep R G) : TRep R G := coindRep (⊥ : Subgroup G) (M.resSub ⊥)

instance CG_disc [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] : DiscreteTopology (CG M).V := by
  have : DiscreteTopology (M.resSub (⊥ : Subgroup G)).V := ‹DiscreteTopology M.V›
  have := cmap_disc G (M.resSub (⊥ : Subgroup G)).V
  exact (IsEmbedding.subtypeVal (p := fun f => f ∈ coindSub (⊥ : Subgroup G) (M.resSub ⊥))).discreteTopology

def iCG (M : TRep R G) : M.V →ₗ[R] (CG M).V where
  toFun m := ⟨⟨fun x => M.rho x m, M.cont.comp (f := fun x : G => (x, m)) (continuous_id.prodMk continuous_const)⟩,
    fun x g => by
      show M.rho ((x : G) * g) m = M.rho (x : G) (M.rho g m)
      rw [map_mul, Module.End.mul_apply]⟩
  map_add' a b := Subtype.ext (ContinuousMap.ext fun x => by
    show M.rho x (a + b) = M.rho x a + M.rho x b; simp)
  map_smul' r a := Subtype.ext (ContinuousMap.ext fun x => by
    show M.rho x (r • a) = r • M.rho x a; simp)

@[simp] theorem iCG_apply (M : TRep R G) (m : M.V) (x : G) : (iCG M m).1 x = M.rho x m := rfl

theorem iCG_equiv (M : TRep R G) (g : G) (m : M.V) : iCG M (M.rho g m) = (CG M).rho g (iCG M m) := by
  refine Subtype.ext (ContinuousMap.ext fun x => ?_)
  show M.rho x (M.rho g m) = M.rho (x * g) m
  rw [map_mul, Module.End.mul_apply]

theorem iCG_inj (M : TRep R G) : Injective (iCG M) := fun a b h => by
  have h1 : M.rho 1 a = M.rho 1 b := congrArg (fun f : (CG M).V => f.1 1) h
  simpa using h1

def iP (M : TRep R G) [DiscreteTopology M.V] : Pair M (CG M) :=
  Pair.ofMap (iCG M) continuous_of_discreteTopology (iCG_equiv M)

def QG (M : TRep R G) : TRep R G where
  V := (CG M).V ⧸ LinearMap.range (iCG M)
  rho := (CG M).rho.quotient (LinearMap.range (iCG M)) (fun g x hx => by
    obtain ⟨m, rfl⟩ := hx
    exact ⟨M.rho g m, iCG_equiv M g m⟩)
  cont := by
    have hq : IsQuotientMap (fun p : G × (CG M).V => (p.1, (LinearMap.range (iCG M)).mkQ p.2)) :=
      (IsOpenQuotientMap.id.prodMap (Submodule.isOpenQuotientMap_mkQ _)).isQuotientMap
    unfold Gal.ContAction
    rw [hq.continuous_iff]
    exact (Submodule.isQuotientMap_mkQ _).continuous.comp (CG M).cont

instance QG_disc [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] : DiscreteTopology (QG M).V := by
  refine discreteTopology_iff_isOpen_singleton.2 fun x => ?_
  exact (Submodule.isQuotientMap_mkQ (LinearMap.range (iCG M))).isOpen_preimage.1 (isOpen_discrete _)

def pLin (M : TRep R G) : (CG M).V →ₗ[R] (QG M).V := (LinearMap.range (iCG M)).mkQ

theorem pLin_cont (M : TRep R G) : Continuous (pLin M) := (Submodule.isQuotientMap_mkQ _).continuous

theorem pLin_equiv (M : TRep R G) (g : G) (c : (CG M).V) : pLin M ((CG M).rho g c) = (QG M).rho g (pLin M c) := rfl

theorem pLin_eq_zero (M : TRep R G) (c : (CG M).V) : pLin M c = 0 ↔ c ∈ LinearMap.range (iCG M) :=
  Submodule.Quotient.mk_eq_zero _

theorem pLin_surj (M : TRep R G) : Surjective (pLin M) := Submodule.mkQ_surjective _

def pP (M : TRep R G) : Pair (CG M) (QG M) := Pair.ofMap (pLin M) (pLin_cont M) (pLin_equiv M)

theorem admissible_compact_discrete [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] : admitted (iP M) (pP M) where
  i_id := rfl
  p_id := rfl
  emb := emb_disc _ (iCG_inj M)
  exact := LinearMap.exact_map_mkQ_range _
  sec := ⟨surjInv (pLin_surj M), continuous_of_discreteTopology,
    surjInv_eq _⟩

theorem CG_acyc (M : TRep R G) (m : ℕ) (z : (CG M).H (m + 1)) : z = 0 := by
  have hq := shapiro_holds R G (⊥ : Subgroup G) (M.resSub ⊥) (CG M) (coindEv _ _) (coindEv_isCoind _ _)
    ⟨fun _ => 1, continuous_const, fun x g => by
      have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.1 x.2)
      rw [hx, one_mul]⟩
  have : Subsingleton (⊥ : Subgroup G) :=
    ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)⟩
  refine (hq (m + 1)).1 ?_
  rw [map_zero]
  exact FiniteLevelCohomology.H_succ_trivial _ m _

end InflationIsomorphism

end

end ReciprocityTheory.Coh

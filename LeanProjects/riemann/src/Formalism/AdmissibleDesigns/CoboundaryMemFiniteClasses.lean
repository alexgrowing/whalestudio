import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
import Formalism.AdmissibleDesigns.SelfGood

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KBKa

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N.KHf ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]
  [ContinuousSMul O (FractionRing O)]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {VT VT' : Type}
  [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
  [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
  [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  (Dat : LatData O Γ VT VT')
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] (e : FractionRing O ≃+* LL)
  {Qp : Type} [Field Qp] [Algebra Qp LL]
  {OL : Type} [CommRing OL] [Algebra OL LL]
  {G : Type} [Group G] [TopologicalSpace G] (ι : G →* Γ)
  {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR)

instance instModOL (V : Type) [AddCommGroup V] [Module (FractionRing O) V] : Module OL (TrV e V) :=
  Module.compHom V (e.symm.toRingHom.comp (algebraMap OL LL))

instance instTowOL (V : Type) [AddCommGroup V] [Module (FractionRing O) V] :
    IsScalarTower OL LL (TrV e V) :=
  ⟨fun c a v => by
    show (e.symm (c • a)) • (show V from v) = (e.symm (algebraMap OL LL c)) • ((e.symm a) • (show V from v))
    rw [Algebra.smul_def, map_mul, mul_smul]⟩

def IotaHomeo : Prop := ∃ h : G ≃ₜ Γ, ∀ g, h g = ι g

def HomeoK : Prop := Continuous e ∧ Continuous e.symm

def TopMatch (V : Type) [AddCommGroup V] [Module (FractionRing O) V] [t : TopologicalSpace V] : Prop :=
  (instTop (V := V) e : TopologicalSpace (TrV e V)) = t

def CycMatch : Prop :=
  ∀ g, e (algebraMap O (FractionRing O) ((Dat.ε (ι g) : Oˣ) : O)) = ((cycLL PD LL g : LLˣ) : LL)

def toV {V : Type} (x : TrV e V) : V := x

theorem toV_add {V : Type} [AddCommGroup V] [Module (FractionRing O) V] (x y : TrV e V) :
    toV e (x + y) = toV e x + toV e y := rfl

theorem toV_smul {V : Type} [AddCommGroup V] [Module (FractionRing O) V] (c : LL) (x : TrV e V) :
    toV e (c • x) = e.symm c • toV e x := rfl

theorem bT_smulK_left (k : FractionRing O) (v : VT) (w : VT') : Dat.bT (k • v) w = k • Dat.bT v w :=
  smulK (Dat.bT.flip w) k v

theorem bT_smulK_right (k : FractionRing O) (v : VT) (w : VT') : Dat.bT v (k • w) = k • Dat.bT v w :=
  smulK (Dat.bT v) k w

def pairLL : TrV e VT →ₗ[LL] TrV e VT' →ₗ[LL] LL :=
  LinearMap.mk₂ LL (fun x y => e (Dat.bT (toV e x) (toV e y)))
    (fun x x' y => by rw [toV_add, map_add, LinearMap.add_apply, map_add])
    (fun c x y => by
      rw [toV_smul, bT_smulK_left, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply, smul_eq_mul])
    (fun x y y' => by rw [toV_add, map_add, map_add])
    (fun c x y => by
      rw [toV_smul, bT_smulK_right, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply, smul_eq_mul])

theorem pairLL_apply (x : TrV e VT) (y : TrV e VT') :
    pairLL Dat e x y = e (Dat.bT (toV e x) (toV e y)) := rfl

def repA (hfin : FiniteDimensional LL (TrV e VT))
    (hc : ∀ x, Continuous fun g => repL e Dat.ρT ι g x) : Formalism.MainNotions.N.GRep G Qp LL OL where
  V := TrV e VT
  fd := hfin
  ρ := repL e Dat.ρT ι
  cont := hc

def repA' (hfin : FiniteDimensional LL (TrV e VT'))
    (hc : ∀ x, Continuous fun g => repL e Dat.ρT' ι g x) : Formalism.MainNotions.N.GRep G Qp LL OL where
  V := TrV e VT'
  fd := hfin
  ρ := repL e Dat.ρT' ι
  cont := hc

end Gen

section GenP

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]
  [ContinuousSMul O (FractionRing O)]
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] (e : FractionRing O ≃+* LL)

theorem cont_iff {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [t : TopologicalSpace V]
    (h : TopMatch e V) {X : Type} [TopologicalSpace X] (f : X → V) :
    @Continuous X (TrV e V) _ (instTop e) f ↔ Continuous f := by
  unfold TopMatch at h
  rw [h]
  exact Iff.rfl

def ofV {V : Type} (x : V) : TrV e V := x

theorem ofV_smulK {V : Type} [AddCommGroup V] [Module (FractionRing O) V] (k : FractionRing O) (x : V) :
    ofV e (V := V) (k • x) = e k • ofV e x := by
  show k • x = e.symm (e k) • x
  rw [RingEquiv.symm_apply_apply]

theorem fd_of_finK {V : Type} [AddCommGroup V] [Module (FractionRing O) V]
    [hV : Module.Finite (FractionRing O) V] : FiniteDimensional LL (TrV e V) := by
  obtain ⟨S, hS⟩ := hV.fg_top
  refine ⟨⟨S.image (ofV e), ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  intro v _
  have hv : toV e v ∈ Submodule.span (FractionRing O) (S : Set V) := by rw [hS]; exact Submodule.mem_top
  have key : ∀ x ∈ Submodule.span (FractionRing O) (S : Set V),
      ofV e x ∈ Submodule.span LL (ofV e '' (S : Set V)) := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => ofV e x ∈ Submodule.span LL (ofV e '' (S : Set V)))
      (fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩) (Submodule.zero_mem _)
      (fun y z _ _ hy hz => Submodule.add_mem _ hy hz) (fun k y _ hy => ?_) hx
    rw [ofV_smulK]
    exact Submodule.smul_mem _ _ hy
  exact key _ hv

theorem finK_of_lat {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] {T : Submodule O V} (h : IsLatticeIn T) :
    Module.Finite (FractionRing O) V := by
  obtain ⟨S, hS⟩ := h.1
  refine ⟨⟨S, ?_⟩⟩
  rw [eq_top_iff, ← h.2, Submodule.span_le]
  intro x hx
  rw [← hS] at hx
  exact Submodule.span_le_restrictScalars O (FractionRing O) _ hx

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {V : Type} [AddCommGroup V] [Module O V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]

theorem sub_mem_of_mk_eq (ρ : Representation O Γ V) (Z : Submodule (FractionRing O) (Γ → V))
    (hB : ∀ x, d0 ρ x ∈ Z) (c c' : Z1 ρ)
    (h : Submodule.mkQ ((B1 ρ).comap (Z1 ρ).subtype) c = Submodule.mkQ _ c') :
    (c : Γ → V) - c' ∈ Z := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨m, hm⟩ := h
  have : (c : Γ → V) - c' = d0 ρ m := by rw [hm]; rfl
  rw [this]
  exact hB m

theorem mk_smul (ρ : Representation O Γ V) [ContinuousConstSMul (FractionRing O) V]
    [Module (FractionRing O) (H1 ρ)] [IsScalarTower O (FractionRing O) (H1 ρ)]
    (k : FractionRing O) (c : Z1 ρ) :
    ∃ kc : Z1 ρ, (kc : Γ → V) = k • (c : Γ → V) ∧
      Submodule.mkQ ((B1 ρ).comap (Z1 ρ).subtype) kc = k • Submodule.mkQ _ c := by
  have hc : Continuous (c : Γ → V) ∧ ∀ g h, c.1 (g * h) = c.1 g + ρ g (c.1 h) := c.2
  refine ⟨⟨k • (c : Γ → V), hc.1.const_smul k, fun g h => ?_⟩, rfl, ?_⟩
  · show k • c.1 (g * h) = k • c.1 g + ρ g (k • c.1 h)
    rw [hc.2 g h, smul_add, smulK (ρ g) k]
  · obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (nonZeroDivisors O) k
    have hs : algebraMap O (FractionRing O) (s : O) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    dsimp only at hxs
    apply smul_right_injective (H1 ρ) hs
    dsimp only
    rw [smul_smul, mul_comm, hxs, algebraMap_smul, algebraMap_smul, ← map_smul, ← map_smul]
    congr 1
    apply Subtype.ext
    funext g
    show (s : O) • (k • c.1 g) = x • c.1 g
    rw [← algebraMap_smul (FractionRing O) (s : O) (k • c.1 g), smul_smul, mul_comm, hxs, algebraMap_smul]

def clsSet (ρ : Representation O Γ V) (Z : Submodule (FractionRing O) (Γ → V)) : Submodule O (H1 ρ) :=
  (((Z.restrictScalars O).comap (LinearMap.compLeft LinearMap.id Γ)).comap (Z1 ρ).subtype).map
    (Submodule.mkQ _)

theorem mem_span_iff (ρ : Representation O Γ V) [ContinuousConstSMul (FractionRing O) V]
    [Module (FractionRing O) (H1 ρ)] [IsScalarTower O (FractionRing O) (H1 ρ)]
    (Z : Submodule (FractionRing O) (Γ → V)) (hB : ∀ x, d0 ρ x ∈ Z) (c : Z1 ρ) :
    Submodule.mkQ ((B1 ρ).comap (Z1 ρ).subtype) c ∈
      Submodule.span (FractionRing O) (clsSet ρ Z : Set (H1 ρ)) ↔ (c : Γ → V) ∈ Z := by
  let S : Submodule (FractionRing O) (H1 ρ) :=
    { carrier := {a | ∀ c : Z1 ρ, Submodule.mkQ ((B1 ρ).comap (Z1 ρ).subtype) c = a → (c : Γ → V) ∈ Z}
      zero_mem' := fun c hc => by
        have h := sub_mem_of_mk_eq ρ Z hB c 0 (by rw [hc, map_zero])
        simpa using h
      add_mem' := fun {a b} ha hb c hc => by
        obtain ⟨ca, rfl⟩ := Submodule.mkQ_surjective _ a
        obtain ⟨cb, rfl⟩ := Submodule.mkQ_surjective _ b
        have h := sub_mem_of_mk_eq ρ Z hB c (ca + cb) (by rw [hc, map_add])
        have e1 : (c : Γ → V) = ((c : Γ → V) - ((ca + cb : Z1 ρ) : Γ → V)) + ((ca : Γ → V) + cb) := by
          simp
        rw [e1]
        exact Z.add_mem h (Z.add_mem (ha ca rfl) (hb cb rfl))
      smul_mem' := fun k a ha c hc => by
        obtain ⟨ca, rfl⟩ := Submodule.mkQ_surjective _ a
        obtain ⟨kc, hkc, hmk⟩ := mk_smul ρ k ca
        have h := sub_mem_of_mk_eq ρ Z hB c kc (by rw [hc, hmk])
        have e1 : (c : Γ → V) = ((c : Γ → V) - kc) + k • (ca : Γ → V) := by rw [← hkc]; abel
        rw [e1]
        exact Z.add_mem h (Z.smul_mem k (ha ca rfl)) }
  constructor
  · intro h
    have hle : Submodule.span (FractionRing O) (clsSet ρ Z : Set (H1 ρ)) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨c0, hc0, rfl⟩ c hc
      have h1 := sub_mem_of_mk_eq ρ Z hB c c0 hc
      have e1 : (c : Γ → V) = ((c : Γ → V) - c0) + c0 := by abel
      rw [e1]
      exact Z.add_mem h1 hc0
    exact hle h c rfl
  · intro h
    exact Submodule.subset_span ⟨c, h, rfl⟩

end GenP

section GenQ

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]
  [ContinuousSMul O (FractionRing O)]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {VT VT' : Type}
  [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
  [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
  [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  (Dat : LatData O Γ VT VT')
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] (e : FractionRing O ≃+* LL)
  {Qp : Type} [Field Qp] [Algebra Qp LL]
  {OL : Type} [CommRing OL] [Algebra OL LL]
  {G : Type} [Group G] [TopologicalSpace G] (ι : G →* Γ)
  {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR)

def dualMap : VT' →ₗ[FractionRing O] (VT →ₗ[FractionRing O] FractionRing O) where
  toFun f :=
    { toFun := fun x => Dat.bT x f
      map_add' := fun x y => by rw [map_add, LinearMap.add_apply]
      map_smul' := fun k x => bT_smulK_left Dat k x f }
  map_add' f f' := LinearMap.ext fun x => map_add (Dat.bT x) f f'
  map_smul' k f := LinearMap.ext fun x => bT_smulK_right Dat k x f

theorem dualMap_bij (hP : PerfectRight Dat.bT) : Function.Bijective (dualMap Dat) := by
  constructor
  · intro f f' h
    obtain ⟨g, _, hg⟩ := hP (dualMap Dat f)
    have h1 := hg f (fun x => rfl)
    have h2 := hg f' (fun x => by rw [h]; rfl)
    rw [h1, h2]
  · intro ψ
    obtain ⟨f, hf, _⟩ := hP ψ
    exact ⟨f, LinearMap.ext hf⟩

theorem finK' [Module.Finite (FractionRing O) VT] (hP : PerfectRight Dat.bT) :
    Module.Finite (FractionRing O) VT' :=
  Module.Finite.equiv (LinearEquiv.ofBijective (dualMap Dat) (dualMap_bij Dat hP)).symm

theorem nondeg_left (hP : PerfectRight Dat.bT) (x : VT) (hx : ∀ y, Dat.bT x y = 0) : x = 0 := by
  by_contra hne
  obtain ⟨ψ, hψ⟩ : ∃ ψ : VT →ₗ[FractionRing O] FractionRing O, ψ x ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne ((Module.forall_dual_apply_eq_zero_iff (FractionRing O) x).1 hall)
  obtain ⟨f, hf, _⟩ := hP ψ
  exact hψ ((hf x).symm.trans (hx f))

theorem nondeg_right (hP : PerfectRight Dat.bT) (y : VT') (hy : ∀ x, Dat.bT x y = 0) : y = 0 := by
  obtain ⟨f, _, hu⟩ := hP 0
  rw [hu y (fun x => hy x), hu 0 (fun x => by simp)]

theorem isDual1 (hreal : Formalism.RepresentationBoundsCohomology.FIN.RealLat Dat) (hcyc : CycMatch Dat e ι PD) :
    IsDual1 PD (repL e Dat.ρT ι) (repL e Dat.ρT' ι) (pairLL Dat e) := by
  haveI : Module.Finite (FractionRing O) VT := finK_of_lat hreal.lat
  haveI : Module.Finite (FractionRing O) VT' := finK' Dat hreal.perf
  haveI := fd_of_finK e (V := VT)
  haveI := fd_of_finK e (V := VT')
  have hl : ∀ x : TrV e VT, (∀ y, pairLL Dat e x y = 0) → x = 0 := fun x hx =>
    nondeg_left Dat hreal.perf (toV e x) fun y => (map_eq_zero_iff e e.injective).1 (hx y)
  have hr : ∀ y : TrV e VT', (∀ x, pairLL Dat e x y = 0) → y = 0 := fun y hy =>
    nondeg_right Dat hreal.perf (toV e y) fun x => (map_eq_zero_iff e e.injective).1 (hy x)
  refine ⟨fun g x y => ?_, hl, hr, ?_⟩
  · rw [pairLL_apply, pairLL_apply]
    show e (Dat.bT (Dat.ρT (ι g) (toV e x)) (Dat.ρT' (ι g) (toV e y))) = _
    rw [Dat.eqT, Algebra.smul_def, map_mul, hcyc g]
  · apply le_antisymm
    · have hinj : Function.Injective (pairLL Dat e) := fun x x' h => by
        have := hl (x - x') (fun y => by rw [map_sub, LinearMap.sub_apply, h, sub_self])
        exact sub_eq_zero.1 this
      exact (LinearMap.finrank_le_finrank_of_injective hinj).trans (Subspace.dual_finrank_eq).le
    · have hinj : Function.Injective (pairLL Dat e).flip := fun y y' h => by
        have := hr (y - y') (fun x => by
          have h' := congrArg (fun F => F x) h
          simp only [LinearMap.flip_apply] at h'
          rw [map_sub, h', sub_self])
        exact sub_eq_zero.1 this
      exact (LinearMap.finrank_le_finrank_of_injective hinj).trans (Subspace.dual_finrank_eq).le

theorem coboundary_mem_finite_classes {V : Type} [AddCommGroup V] [Module O V] [t : TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
    (ρ : Representation O Γ V) (htop : TopMatch e V) (hι : Continuous ι) (hc : ContAction ρ) (x : V) :
    d0 ρ x ∈ finZ e PD ρ ι := by
  rw [mem_finZ]
  refine ⟨⟨?_, fun g h => ?_⟩, (ofV e x : TrV e V) ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · exact (cont_iff e htop _).2 ((hc.comp ((hι).prodMk continuous_const)).sub continuous_const)
  · show ρ (ι (g * h)) x - x = (ρ (ι g) x - x) + ρ (ι g) (ρ (ι h) x - x)
    rw [map_mul, map_mul, Module.End.mul_apply, map_sub]
    abel
  · show (ofV e (ρ (ι g) x - x) : TrV e V) ⊗ₜ[Qp] (1 : B) = actVB PD (repL e ρ ι) g (ofV e x ⊗ₜ[Qp] (1 : B)) - ofV e x ⊗ₜ[Qp] (1 : B)
    rw [actVB, TensorProduct.AlgebraTensorModule.map_tmul]
    simp only [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, AlgEquiv.toAlgHom_eq_coe,
      AlgEquiv.coe_algHom, map_one]
    rw [← TensorProduct.sub_tmul]
    rfl

end GenQ

section GenR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]
  [ContinuousSMul O (FractionRing O)]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] (e : FractionRing O ≃+* LL)
  {G : Type} [Group G] [TopologicalSpace G] (ι : G →* Γ)
  {V : Type} [AddCommGroup V] [Module O V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]

theorem continuous_cocycle_transport (ρ : Representation O Γ V) (htop : TopMatch e V) (hι : Continuous ι) (c : Z1 ρ) :
    (fun g => ofV e (c.1 (ι g))) ∈ continuousCocycles (repL e ρ ι) := by
  have hc : Continuous (c : Γ → V) ∧ ∀ g h, c.1 (g * h) = c.1 g + ρ g (c.1 h) := c.2
  refine ⟨(cont_iff e htop _).2 (hc.1.comp hι), fun g h => ?_⟩
  show c.1 (ι (g * h)) = c.1 (ι g) + ρ (ι g) (c.1 (ι h))
  rw [map_mul, hc.2]

theorem symm_iota (h : G ≃ₜ Γ) (hh : ∀ g, h g = ι g) (γ : Γ) : ι (h.symm γ) = γ := by
  rw [← hh, h.apply_symm_apply]

theorem symm_iota' (h : G ≃ₜ Γ) (hh : ∀ g, h g = ι g) (g : G) : h.symm (ι g) = g := by
  rw [← hh, h.symm_apply_apply]

theorem exists_cocycle_of_continuous (ρ : Representation O Γ V) (htop : TopMatch e V) (h : G ≃ₜ Γ)
    (hh : ∀ g, h g = ι g) (b : G → TrV e V) (hb : b ∈ continuousCocycles (repL e ρ ι)) :
    ∃ d : Z1 ρ, ∀ g, ofV e (d.1 (ι g)) = b g := by
  have hb' : Continuous b ∧ ∀ g g', b (g * g') = b g + repL e ρ ι g (b g') := hb
  refine ⟨⟨fun γ => toV e (b (h.symm γ)), (cont_iff e htop _).1 (hb'.1.comp h.symm.continuous),
    fun γ δ => ?_⟩, fun g => ?_⟩
  · have hm : h.symm (γ * δ) = h.symm γ * h.symm δ := by
      apply h.injective
      rw [h.apply_symm_apply, hh, map_mul, symm_iota ι h hh, symm_iota ι h hh]
    show toV e (b (h.symm (γ * δ))) = toV e (b (h.symm γ)) + ρ γ (toV e (b (h.symm δ)))
    rw [hm, hb'.2]
    show toV e (b (h.symm γ)) + ρ (ι (h.symm γ)) (toV e (b (h.symm δ))) = _
    rw [symm_iota ι h hh]
  · show b (h.symm (ι g)) = b g
    rw [symm_iota' ι h hh]

end GenR

section GenS

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]
  [ContinuousSMul O (FractionRing O)]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {VT VT' : Type}
  [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
  [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
  [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  (Dat : LatData O Γ VT VT')
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] (e : FractionRing O ≃+* LL)
  {Qp : Type} [Field Qp] [Algebra Qp LL]
  {OL : Type} [CommRing OL] [Algebra OL LL]
  {G : Type} [Group G] [TopologicalSpace G] (ι : G →* Γ)
  {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR)

theorem cup_iff (hι : Continuous ι) (hK : HomeoK e) (hcyc : CycMatch Dat e ι PD) (h : G ≃ₜ Γ)
    (hh : ∀ g, h g = ι g) (c : Z1 Dat.ρT) (d : Z1 Dat.ρT') :
    ReciprocityTheory.ChartRestriction.T2.cupFG Dat (Submodule.mkQ _ c) (Submodule.mkQ _ d) = 0 ↔
      CobL PD (cupL (repL e Dat.ρT' ι) (pairLL Dat e) (fun g => ofV e (c.1 (ι g)))
        (fun g => ofV e (d.1 (ι g)))) := by
  show Submodule.mkQ _ (cupCocycleZ1Z1 Dat.ρT Dat.ρT' (twist Dat.ε (FractionRing O)) Dat.bT Dat.contbT Dat.eqT
    Dat.contT' c d) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    separated_dvr_second_cohomology_mem]
  constructor
  · rintro ⟨f, hf, hfe⟩
    refine ⟨fun g => e (f (ι g)), hK.1.comp (hf.comp hι), ?_⟩
    funext ⟨g, g'⟩
    have h1 := congrFun hfe (ι g, ι g')
    simp only [d1_apply, cupCocycleZ1Z1_apply, twist_apply, Algebra.smul_def] at h1
    show ((cycLL PD LL g : LLˣ) : LL) * e (f (ι g')) - e (f (ι (g * g'))) + e (f (ι g)) =
      e (Dat.bT (c.1 (ι g)) (Dat.ρT' (ι g) (d.1 (ι g'))))
    rw [← hcyc g, ← map_mul, ← map_sub, ← map_add, map_mul ι]
    exact congrArg e h1
  · rintro ⟨f', hf', hfe'⟩
    refine ⟨fun γ => e.symm (f' (h.symm γ)), hK.2.comp (hf'.comp h.symm.continuous), ?_⟩
    funext ⟨γ, δ⟩
    obtain ⟨g1, rfl⟩ : ∃ g1, ι g1 = γ := ⟨h.symm γ, symm_iota ι h hh γ⟩
    obtain ⟨g2, rfl⟩ : ∃ g2, ι g2 = δ := ⟨h.symm δ, symm_iota ι h hh δ⟩
    have h1 := congrFun hfe' (g1, g2)
    change ((cycLL PD LL g1 : LLˣ) : LL) * f' g2 - f' (g1 * g2) + f' g1 =
      e (Dat.bT (c.1 (ι g1)) (Dat.ρT' (ι g1) (d.1 (ι g2)))) at h1
    show ((Dat.ε (ι g1) : Oˣ) : O) • e.symm (f' (h.symm (ι g2))) - e.symm (f' (h.symm (ι g1 * ι g2))) +
      e.symm (f' (h.symm (ι g1))) = Dat.bT (c.1 (ι g1)) (Dat.ρT' (ι g1) (d.1 (ι g2)))
    rw [← map_mul ι, symm_iota' ι h hh, symm_iota' ι h hh, symm_iota' ι h hh]
    apply e.injective
    rw [map_add, map_sub, Algebra.smul_def, map_mul, hcyc g1, e.apply_symm_apply, e.apply_symm_apply,
      e.apply_symm_apply]
    exact h1

theorem bka_gen [Module (FractionRing O) (H1 Dat.ρT)] [IsScalarTower O (FractionRing O) (H1 Dat.ρT)]
    [Module (FractionRing O) (H1 Dat.ρT')] [IsScalarTower O (FractionRing O) (H1 Dat.ρT')]
    (hbk : Formalism.MainNotions.LargeLevelLemmas.bkAAt PD LL OL) (hreal : Formalism.RepresentationBoundsCohomology.FIN.RealLat Dat) (hι : IotaHomeo ι)
    (hK : HomeoK e) (ht : TopMatch e VT) (ht' : TopMatch e VT') (hcyc : CycMatch Dat e ι PD)
    (hdr : IsDR PD (repL e Dat.ρT ι))
    (Z : Submodule (FractionRing O) (Γ → VT)) (Z' : Submodule (FractionRing O) (Γ → VT'))
    (hZ : Z = finZ e PD Dat.ρT ι) (hZ' : Z' = finZ e PD Dat.ρT' ι) (a : H1 Dat.ρT) :
    a ∈ Submodule.span (FractionRing O) (clsSet Dat.ρT Z : Set (H1 Dat.ρT)) ↔
      ∀ b ∈ Submodule.span (FractionRing O) (clsSet Dat.ρT' Z' : Set (H1 Dat.ρT')),
        ReciprocityTheory.ChartRestriction.T2.cupFG Dat a b = 0 := by
  subst hZ hZ'
  obtain ⟨h, hh⟩ := hι
  have hιc : Continuous ι := by
    rw [show (ι : G → Γ) = h from funext fun g => (hh g).symm]
    exact h.continuous
  haveI : Module.Finite (FractionRing O) VT := finK_of_lat hreal.lat
  haveI : Module.Finite (FractionRing O) VT' := finK' Dat hreal.perf
  haveI : ContinuousConstSMul (FractionRing O) VT := hreal.cs
  haveI : ContinuousConstSMul (FractionRing O) VT' := hreal.cs'
  have fdV := fd_of_finK e (V := VT)
  have fdV' := fd_of_finK e (V := VT')
  have hcA : ∀ x, Continuous fun g => repL e Dat.ρT ι g x := fun x =>
    (cont_iff e ht _).2 (hreal.contT.comp (hιc.prodMk continuous_const))
  have hcA' : ∀ x, Continuous fun g => repL e Dat.ρT' ι g x := fun x =>
    (cont_iff e ht' _).2 (Dat.contT'.comp (hιc.prodMk continuous_const))
  let A := repA (Qp := Qp) (OL := OL) Dat e ι fdV hcA
  let A' := repA' (Qp := Qp) (OL := OL) Dat e ι fdV' hcA'
  have hB : ∀ x, d0 Dat.ρT x ∈ finZ e PD Dat.ρT ι := coboundary_mem_finite_classes e ι PD Dat.ρT ht hιc hreal.contT
  have hB' : ∀ x, d0 Dat.ρT' x ∈ finZ e PD Dat.ρT' ι := coboundary_mem_finite_classes e ι PD Dat.ρT' ht' hιc Dat.contT'
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ a
  rw [mem_span_iff Dat.ρT _ hB c, mem_finZ]
  have hcZ := continuous_cocycle_transport e ι Dat.ρT ht hιc c
  have hdual := isDual1 Dat e ι PD hreal hcyc
  refine ((hbk A A' (pairLL Dat e) hdr hdual).1 _ hcZ).trans ?_
  constructor
  · intro H b hb
    obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ b
    have hd := (mem_span_iff Dat.ρT' _ hB' d).1 hb
    exact (cup_iff Dat e ι PD hιc hK hcyc h hh c d).2 (H _ hd)
  · intro H b hb
    obtain ⟨d, hd⟩ := exists_cocycle_of_continuous e ι Dat.ρT' ht' h hh b hb.1
    have hbd : b = fun g => ofV e (d.1 (ι g)) := funext fun g => (hd g).symm
    subst hbd
    have hdZ : d.1 ∈ finZ e PD Dat.ρT' ι := hb
    exact (cup_iff Dat e ι PD hιc hK hcyc h hh c d).1 (H _ ((mem_span_iff Dat.ρT' _ hB' d).2 hdZ))

end GenS

section Rec

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.BasicNotions.Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem over_of_row {w : ℕ} (hw : w ∈ K.rowsN i dc) : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i) := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
  have hp : v ∈ K.plSet i dc := Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  rw [K.plOf_idx i dc hp]
  exact (dc.cover v).1 (Or.inl hv)

theorem iotaHomeo_rec {w : ℕ} (hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i)) :
    IotaHomeo (Br.iota D.nbr i _ hn) :=
  ⟨Br.ιHomeo (D.nbr i _ hn), fun _ => rfl⟩

variable [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]

def RowIn (w : ℕ) : Prop :=
  ∀ hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i),
    HomeoK (eK (D.nbr i _ hn)) ∧
    TopMatch (eK (D.nbr i _ hn)) (VT w) ∧ TopMatch (eK (D.nbr i _ hn)) (VT' w) ∧
    CycMatch (Dat w) (eK (D.nbr i _ hn)) (Br.iota D.nbr i _ hn) (Br.PD D.loc D.nbr i _ hn) ∧
    IsDR (Br.PD D.loc D.nbr i _ hn) (repL (eK (D.nbr i _ hn)) (Dat w).ρT (Br.iota D.nbr i _ hn))

theorem bk_a_of_admitted_bk_a (hBK : LargeLevelLemmas.BlochKatoAnnihilators i) (hG : K.SelfGood i) {w : ℕ} (hw : w ∈ K.rowsN i dc)
    (hreal : Formalism.RepresentationBoundsCohomology.FIN.RealLat (Dat w)) (hin : RowIn i dc VT VT' Dat w) :
    Formalism.MainNotions.N.KHf.BKa i dc VT VT' Dat w := by
  have hn := over_of_row i dc hw
  obtain ⟨hK, ht, ht', hcyc, hdr⟩ := hin hn
  have hbk : LargeLevelLemmas.bkAAt (Br.PD D.loc D.nbr i _ hn) (Br.LLw (D.nbr i _ hn)) ↥(OL (D.nbr i _ hn).LL) :=
    hBK _ hn (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (hG _ hn)
  intro a
  exact bka_gen (Dat w) (eK (D.nbr i _ hn)) (Br.iota D.nbr i _ hn) (Br.PD D.loc D.nbr i _ hn) hbk hreal (iotaHomeo_rec i dc hn) hK
    ht ht' hcyc hdr (fZ i dc w (Dat w).ρT) (fZ i dc w (Dat w).ρT') (fZ_pos i dc (Dat w).ρT hn)
    (fZ_pos i dc (Dat w).ρT' hn) a

end Rec

end Formalism.MainNotions.N.KBKa

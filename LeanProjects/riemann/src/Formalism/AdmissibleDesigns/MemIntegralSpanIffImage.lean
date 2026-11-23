import Formalism.AdmissibleDesigns.MemImageOfTensorSum
import Formalism.AdmissibleDesigns.CohomZeroEquivContinuous
import Formalism.SharpRestriction.LevelLetterCocycles.IsobaricMultiplicityOne
import Formalism.AdmissibleDesigns.EKSymmCont

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.NG

namespace Formalism.MainNotions.N.KTate

open Formalism.MainNotions.N.KHf

section Gen

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) (OL : Type) [CommRing OL] [Algebra OL LL] {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G]
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  [FiniteDimensional (FractionRing O) V]

abbrev modOL : Module OL (TrV e V) := Module.compHom _ (algebraMap OL LL)

theorem towOL : @IsScalarTower OL LL (TrV e V) _ _ (modOL e OL).toSMul := by
  letI := modOL (V := V) e OL
  exact ⟨fun a b v => by
    show (a • b) • v = (algebraMap OL LL a) • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩

def grepV (ρ : Representation O Γ V) (ι : G →* Γ) (hc : ∀ v : TrV e V, Continuous fun g => repL e ρ ι g v) :
    GRep G Qp LL OL :=
  { V := TrV e V
    modO := modOL (V := V) e OL
    towO := towOL (V := V) e OL
    fd := KDim.finDim_TrV (V := V) e
    ρ := repL e ρ ι
    cont := hc }

variable {OL} (σ : O ≃+* OL) (hσ : ∀ c : O, algebraMap OL LL (σ c) = e (algebraMap O (FractionRing O) c))

include hσ in

theorem smul_OL (c : O) (v : V) :
    @HSMul.hSMul OL (TrV e V) (TrV e V) (@instHSMul _ _ (modOL (V := V) e OL).toSMul) (σ c) (show TrV e V from v) =
      (c • v : V) := by
  show e.symm (algebraMap OL LL (σ c)) • v = c • v
  rw [hσ, RingEquiv.symm_apply_apply, algebraMap_smul]

variable {n : Type} [Fintype n] (bV : Basis n (FractionRing O) V)

def latT : @Submodule OL (TrV e V) _ _ (modOL (V := V) e OL) :=
  letI := modOL (V := V) e OL
  Submodule.span OL (Set.range fun j => (show TrV e V from bV j))

end Gen

abbrev tr {O : Type} [CommRing O] {LL : Type} [Field LL] (e : FractionRing O ≃+* LL) {V : Type} (v : V) : TrV e V := v

section Lat

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {OL : Type} [CommRing OL] [Algebra OL LL] {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G]
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  [FiniteDimensional (FractionRing O) V]
  (σ : O ≃+* OL) (hσ : ∀ c : O, algebraMap OL LL (σ c) = e (algebraMap O (FractionRing O) c))
  {n : Type} [Fintype n] (bV : Basis n (FractionRing O) V)
  {L : Type} [AddCommGroup L] [Module O L] (bL : Basis n O L) (iL : L →ₗ[O] V) (hb : ∀ j, iL (bL j) = bV j)

include hσ hb in
theorem iL_mem_latT (m : L) : letI := modOL (V := V) e OL
    tr e (iL m) ∈ latT e (OL := OL) bV := by
  letI := modOL (V := V) e OL
  have hm : tr e (iL m) = ∑ j, σ (bL.repr m j) • tr e (bV j) := by
    show iL m = ∑ j, e.symm (algebraMap OL LL (σ (bL.repr m j))) • bV j
    conv_lhs => rw [← bL.sum_repr m]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hb, hσ, RingEquiv.symm_apply_apply, algebraMap_smul]
  rw [hm]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

include hσ hb in
theorem exists_of_mem_latT (x : TrV e V) (hx : letI := modOL (V := V) e OL; x ∈ latT e (OL := OL) bV) :
    ∃ m : L, tr e (iL m) = x := by
  letI := modOL (V := V) e OL
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨bL j, hb j⟩
  | zero => exact ⟨0, map_zero iL⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add iL a b⟩
  | smul o x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    refine ⟨σ.symm o • a, ?_⟩
    show iL (σ.symm o • a) = e.symm (algebraMap OL LL o) • iL a
    rw [map_smul]
    conv_rhs => rw [← RingEquiv.apply_symm_apply σ o]
    rw [hσ, RingEquiv.symm_apply_apply, algebraMap_smul]

include hσ in
theorem linInd_latT : letI := modOL (V := V) e OL
    LinearIndependent OL (fun j => tr e (bV j)) := by
  letI := modOL (V := V) e OL
  rw [Fintype.linearIndependent_iff]
  intro o ho j
  have h2 : ∑ k, (e.symm (algebraMap OL LL (o k))) • bV k = 0 := ho
  have h3 := (Fintype.linearIndependent_iff.mp bV.linearIndependent) _ h2 j
  obtain ⟨c, hc⟩ := σ.surjective (o j)
  rw [← hc, hσ, RingEquiv.symm_apply_apply] at h3
  have : c = 0 := IsFractionRing.injective O (FractionRing O) (h3.trans (map_zero _).symm)
  rw [← hc, this, map_zero]

theorem span_latT : letI := modOL (V := V) e OL
    Submodule.span LL ((latT e (OL := OL) bV : Set (TrV e V))) = ⊤ := by
  letI := modOL (V := V) e OL
  rw [eq_top_iff]
  intro v _
  have hv := bV.sum_repr (show V from v)
  have h : v = ∑ j, e (bV.repr v j) • tr e (bV j) := by
    show (v : V) = ∑ j, e.symm (e (bV.repr v j)) • bV j
    simp only [RingEquiv.symm_apply_apply]
    exact hv.symm
  rw [h]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Submodule.subset_span ⟨j, rfl⟩))

include hσ in
theorem free_latT : letI := modOL (V := V) e OL
    Module.Free OL ↥(latT e (OL := OL) bV) := by
  letI := modOL (V := V) e OL
  exact Module.Free.of_basis (Basis.span (linInd_latT e σ hσ bV))

def latV (ρ : Representation O Γ V) (ι : G →* Γ) (hc : ∀ v : TrV e V, Continuous fun g => repL e ρ ι g v)
    (ρL : Representation O Γ L) (hiL : ∀ γ m, iL (ρL γ m) = ρ γ (iL m)) :
    Lattice (O := OL) (grepV e OL (Qp := Qp) ρ ι hc).ρ where
  T := latT e (OL := OL) (V := V) bV
  stable g x hx := by
    obtain ⟨m, hm⟩ := exists_of_mem_latT e σ hσ bV bL iL hb (show TrV e V from x) hx
    have h : (grepV e OL (Qp := Qp) ρ ι hc).ρ g x = tr e (iL (ρL (ι g) m)) := by
      rw [← hm, hiL]
      rfl
    rw [h]
    exact iL_mem_latT e σ hσ bV bL iL hb _
  fg := Submodule.fg_span (Set.finite_range _)
  free := free_latT e (V := V) σ hσ bV
  span := span_latT e (V := V) bV

end Lat

theorem finite_compHom {R S M : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module S M] (σ : R ≃+* S)
    [hM : Module.Finite S M] : @Module.Finite R M _ _ (Module.compHom M σ.toRingHom) := by
  letI : Module R M := Module.compHom M σ.toRingHom
  obtain ⟨s, hs⟩ := hM.fg_top
  refine ⟨⟨s, eq_top_iff.2 fun x hx0 => ?_⟩⟩
  clear hx0
  have hx : x ∈ Submodule.span S (s : Set M) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have h : c • y = σ.symm c • y := by
      show c • y = σ (σ.symm c) • y
      rw [RingEquiv.apply_symm_apply]
    rw [h]
    exact Submodule.smul_mem _ _ hy

section FinFf

variable {O : Type} [CommRing O] [IsDomain O] [IsNoetherianRing O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {OL : Type} [CommRing OL] [Algebra OL LL] {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G]
  {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR)
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  [FiniteDimensional (FractionRing O) V]
  (σ : O ≃+* OL) (hσ : ∀ c : O, algebraMap OL LL (σ c) = e (algebraMap O (FractionRing O) c))
  {n : Type} [Fintype n] (bV : Basis n (FractionRing O) V)
  {L : Type} [AddCommGroup L] [Module O L] (bL : Basis n O L) (iL : L →ₗ[O] V) (hb : ∀ j, iL (bL j) = bV j)
  (ρ : Representation O Γ V) (ι : G →* Γ) (hc : ∀ v : TrV e V, Continuous fun g => repL e ρ ι g v)
  (ρL : Representation O Γ L) (hiL : ∀ γ m, iL (ρL γ m) = ρ γ (iL m))

theorem transp_mem (p : ↥((KFin.finPreG iL (finZ e PD ρ ι)).comap (coZ1s ρL).subtype)) :
    (fun g => tr e (iL (((p : coZ1s ρL) : Γ → L) (ι g)))) ∈
      latticeCocycles (latV e σ hσ bV bL iL hb (Qp := Qp) ρ ι hc ρL hiL) := by
  have hp : (fun g => tr e (iL (((p : coZ1s ρL) : Γ → L) (ι g)))) ∈ finiteCocycles PD (repL e ρ ι) := p.2
  exact ⟨hp.1, fun g _ => iL_mem_latT e σ hσ bV bL iL hb _⟩

def transportToH1Lattice :
    letI := Module.compHom (LatticeCohomology (latV e σ hσ bV bL iL hb (Qp := Qp) ρ ι hc ρL hiL)) σ.toRingHom
    ↥((KFin.finPreG iL (finZ e PD ρ ι)).comap (coZ1s ρL).subtype) →ₗ[O]
      LatticeCohomology (latV e σ hσ bV bL iL hb (Qp := Qp) ρ ι hc ρL hiL) :=
  letI := Module.compHom (LatticeCohomology (latV e σ hσ bV bL iL hb (Qp := Qp) ρ ι hc ρL hiL)) σ.toRingHom
  { toFun := fun p => Submodule.Quotient.mk ⟨_, transp_mem e PD σ hσ bV bL iL hb ρ ι hc ρL hiL p⟩
    map_add' := fun p q => by
      rw [← Submodule.Quotient.mk_add]
      congr 1
      exact Subtype.ext (funext fun g => map_add iL _ _)
    map_smul' := fun c p => by
      show _ = (σ c : OL) • (Submodule.Quotient.mk _ : LatticeCohomology (latV e σ hσ bV bL iL hb (Qp := Qp) ρ ι hc ρL hiL))
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      refine Subtype.ext (funext fun g => ?_)
      show iL (c • ((p : coZ1s ρL) : Γ → L) (ι g)) = e.symm (algebraMap OL LL (σ c)) • iL (((p : coZ1s ρL) : Γ → L) (ι g))
      rw [hσ, RingEquiv.symm_apply_apply, algebraMap_smul, map_smul] }

include hσ hb hiL in

theorem finite_FfG (hι : Function.Surjective ι) (hinj : Function.Injective iL)
    (hfin : Module.Finite OL (LatticeCohomology (latV e σ hσ bV bL iL hb (Qp := Qp) ρ ι hc ρL hiL))) :
    Module.Finite O ↥(KFin.FfG ρL iL (finZ e PD ρ ι)) := by
  set LA := latV e σ hσ bV bL iL hb (Qp := Qp) ρ ι hc ρL hiL with hLA
  letI : Module O (LatticeCohomology LA) := Module.compHom (LatticeCohomology LA) σ.toRingHom
  haveI : Module.Finite O (LatticeCohomology LA) := finite_compHom σ
  haveI : IsNoetherian O (LatticeCohomology LA) := isNoetherian_of_isNoetherianRing_of_finite O _
  set P := (KFin.finPreG iL (finZ e PD ρ ι)).comap (coZ1s ρL).subtype with hP
  set Φ := transportToH1Lattice e PD σ hσ bV bL iL hb ρ ι hc ρL hiL (Qp := Qp) with hΦ
  have hker : LinearMap.ker Φ ≤ LinearMap.ker ((Submodule.mkQ ((coB1 ρL).comap (coZ1s ρL).subtype)).comp P.subtype) := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    have hp' := (Submodule.Quotient.mk_eq_zero _).mp hp
    obtain ⟨x, hxT, hx⟩ := hp'
    obtain ⟨m, rfl⟩ := exists_of_mem_latT e σ hσ bV bL iL hb x hxT
    show Submodule.Quotient.mk (p : coZ1s ρL) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨m, funext fun γ => ?_⟩
    obtain ⟨g, rfl⟩ := hι γ
    have h := congrFun hx g
    apply hinj
    show iL (ρL (ι g) m - m) = iL (((p : coZ1s ρL) : Γ → L) (ι g))
    rw [map_sub, hiL]
    exact h
  haveI : Module.Finite O (↥P ⧸ LinearMap.ker Φ) := Module.Finite.equiv (Φ.quotKerEquivRange).symm
  have hF : KFin.FfG ρL iL (finZ e PD ρ ι) =
      LinearMap.range ((LinearMap.ker Φ).liftQ ((Submodule.mkQ ((coB1 ρL).comap (coZ1s ρL).subtype)).comp P.subtype) hker) := by
    rw [Submodule.range_liftQ, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  rw [hF]
  infer_instance

end FinFf

section Cpt

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL OL : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing OL] [IsDomain OL] [Algebra OL LL] [TopologicalSpace LL] (A : GRep G Qp LL OL)

def DivT (T : Submodule OL A.V) : Prop := ∀ v : A.V, ∃ a : OL, a ≠ 0 ∧ a • v ∈ T

theorem cont_smulOL (a : OL) : Continuous fun w : A.V => a • w := by
  have h : (fun w : A.V => a • w) = fun w => (algebraMap OL LL a) • w := funext fun w => (algebraMap_smul LL a w).symm
  rw [h]
  exact continuous_const_smul _

theorem bound_compact (T : Submodule OL A.V) (hopen : IsOpen (T : Set A.V)) (hdiv : DivT A T) (S : Set A.V)
    (hS : IsCompact S) : ∃ a : OL, a ≠ 0 ∧ ∀ v ∈ S, a • v ∈ T := by
  choose f hf0 hfT using hdiv
  have hU : ∀ v, IsOpen {w : A.V | f v • w ∈ T} := fun v => hopen.preimage (cont_smulOL A (f v))
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun v => {w : A.V | f v • w ∈ T}) hU
    (fun w _ => Set.mem_iUnion.2 ⟨w, hfT w⟩)
  refine ⟨∏ v ∈ t, f v, Finset.prod_ne_zero_iff.2 fun v _ => hf0 v, fun w hw => ?_⟩
  obtain ⟨v, hv, hwv⟩ := Set.mem_iUnion₂.1 (ht hw)
  rw [← Finset.mul_prod_erase t f hv, mul_comm, mul_smul]
  exact T.smul_mem _ hwv

variable [CompactSpace G]

theorem bound_cont (T : Submodule OL A.V) (hopen : IsOpen (T : Set A.V)) (hdiv : DivT A T) (c : G → A.V)
    (hc : Continuous c) : ∃ a : OL, a ≠ 0 ∧ ∀ g, a • c g ∈ T := by
  obtain ⟨a, ha, h⟩ := bound_compact A T hopen hdiv _ (isCompact_range hc)
  exact ⟨a, ha, fun g => h _ ⟨g, rfl⟩⟩

def incT (LA : Lattice (O := OL) A.ρ) : ↥(latticeCocycles LA) →ₗ[OL] ↥(continuousCocycles A.ρ) where
  toFun c := ⟨c.1, c.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def h1TV (LA : Lattice (O := OL) A.ρ) :
    letI := Module.compHom (H1V A.ρ) (algebraMap OL LL)
    LatticeCohomology LA →ₗ[OL] H1V A.ρ :=
  letI := Module.compHom (H1V A.ρ) (algebraMap OL LL)
  Submodule.liftQ _
    { toFun := fun c => Submodule.Quotient.mk (incT A LA c)
      map_add' := fun _ _ => rfl
      map_smul' := fun a c => by
        show (Submodule.Quotient.mk (incT A LA (a • c)) : H1V A.ρ) =
          (algebraMap OL LL a) • (Submodule.Quotient.mk (incT A LA c) : H1V A.ρ)
        rw [← Submodule.Quotient.mk_smul]
        congr 1
        exact Subtype.ext (funext fun g => (algebraMap_smul LL a _).symm) }
    (by
      rintro c hc
      obtain ⟨x, _, hx⟩ := hc
      rw [LinearMap.mem_ker]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, hx⟩)

theorem h1_lattice_to_vector_mk (LA : Lattice (O := OL) A.ρ) (c : ↥(latticeCocycles LA)) :
    h1TV A LA (Submodule.Quotient.mk c) = Submodule.Quotient.mk (incT A LA c) := rfl

theorem finite_H1V (LA : Lattice (O := OL) A.ρ) (hopen : IsOpen (LA.T : Set A.V)) (hdiv : DivT A LA.T)
    (hinj : Function.Injective (algebraMap OL LL)) [hfin : Module.Finite OL (LatticeCohomology LA)] :
    Module.Finite LL (H1V A.ρ) := by
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨⟨s.image (h1TV A LA), eq_top_iff.2 fun x _ => ?_⟩⟩
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨a, ha, hac⟩ := bound_cont A LA.T hopen hdiv c.1 c.2.1
  have hT : a • c.1 ∈ latticeCocycles LA := ⟨(continuousCocycles A.ρ).restrictScalars OL |>.smul_mem a c.2, fun g _ => hac g⟩
  letI := Module.compHom (H1V A.ρ) (algebraMap OL LL)
  have hrange : h1TV A LA (Submodule.Quotient.mk ⟨_, hT⟩) ∈
      Submodule.span OL ((s.image (h1TV A LA) : Finset (H1V A.ρ)) : Set (H1V A.ρ)) := by
    have h1 : (Submodule.Quotient.mk ⟨_, hT⟩ : LatticeCohomology LA) ∈ Submodule.span OL (s : Set (LatticeCohomology LA)) := by
      rw [hs]; trivial
    have h2 := Submodule.mem_map_of_mem (f := h1TV A LA) h1
    rw [Submodule.map_span] at h2
    simpa [Finset.coe_image] using h2
  have hle : ∀ y ∈ (letI := Module.compHom (H1V A.ρ) (algebraMap OL LL)
      Submodule.span OL ((s.image (h1TV A LA) : Finset (H1V A.ρ)) : Set (H1V A.ρ))),
      y ∈ Submodule.span LL ((s.image (h1TV A LA) : Finset (H1V A.ρ)) : Set (H1V A.ρ)) := by
    letI := Module.compHom (H1V A.ρ) (algebraMap OL LL)
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy => exact Submodule.smul_mem _ (algebraMap OL LL a) hy
  have hmem := hle _ hrange
  have heq : h1TV A LA (Submodule.Quotient.mk ⟨_, hT⟩) = (algebraMap OL LL a) • Submodule.Quotient.mk c := by
    rw [h1_lattice_to_vector_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (funext fun g => (algebraMap_smul LL a (c.1 g)).symm)
  rw [heq] at hmem
  have ha' : algebraMap OL LL a ≠ 0 := fun h0 => ha (hinj (h0.trans (map_zero _).symm))
  have := Submodule.smul_mem _ (algebraMap OL LL a)⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ ha', one_smul] at this

omit [CompactSpace G] in

theorem finDim_H1fV {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) [Module.Finite LL (H1V A.ρ)] :
    FiniteDimensional LL (FiniteCohomology PD A.ρ) := by
  let f : FiniteCohomology PD A.ρ →ₗ[LL] H1V A.ρ :=
    Submodule.mapQ _ _ (Submodule.inclusion (fun c hc => hc.1 : finiteCocycles PD A.ρ ≤ continuousCocycles A.ρ)) (fun c hc => hc)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    have h := (Submodule.Quotient.mk_eq_zero _).mp hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact h
  exact Module.Finite.of_injective f hf

end Cpt

section Stab

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL OL : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing OL] [IsDomain OL] [Algebra OL LL] [TopologicalSpace LL] (A : GRep G Qp LL OL)
  {n : Type} [Fintype n] (b : Basis n LL A.V)

def T0 : Submodule OL A.V where
  carrier := {x | ∀ j, b.equivFun x j ∈ Set.range (algebraMap OL LL)}
  zero_mem' j := ⟨0, by simp⟩
  add_mem' {x y} hx hy j := by
    obtain ⟨a, ha⟩ := hx j
    obtain ⟨c, hc⟩ := hy j
    exact ⟨a + c, by simp [ha, hc]⟩
  smul_mem' o x hx j := by
    obtain ⟨a, ha⟩ := hx j
    refine ⟨o * a, ?_⟩
    show _ = b.equivFun (o • x) j
    rw [← algebraMap_smul LL o x, map_smul, Pi.smul_apply, ← ha, smul_eq_mul, map_mul]

theorem mem_integral_span (x : A.V) : x ∈ T0 A b ↔ ∀ j, b.equivFun x j ∈ Set.range (algebraMap OL LL) := Iff.rfl

theorem integral_span_open [IsTopologicalRing LL] (hO : IsOpen (Set.range (algebraMap OL LL))) :
    IsOpen ((T0 A b : Submodule OL A.V) : Set A.V) := by
  have hc : Continuous b.equivFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  have h : ((T0 A b : Submodule OL A.V) : Set A.V) =
      b.equivFun ⁻¹' (Set.univ.pi fun _ => Set.range (algebraMap OL LL)) := by
    ext x
    simp [mem_integral_span]
  rw [h]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => hO).preimage hc

theorem integral_span_divisible [IsFractionRing OL LL] : DivT A (T0 A b) := by
  intro v
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors OL) Finset.univ
    (fun j => b.equivFun v j)
  refine ⟨a, nonZeroDivisors.ne_zero a.2, fun j => ?_⟩
  obtain ⟨c, hc⟩ := ha j (Finset.mem_univ j)
  refine ⟨c, ?_⟩
  rw [hc, ← algebraMap_smul LL (a : OL) v, map_smul, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]

theorem basis_mem_integral_span (j : n) : b j ∈ T0 A b := by
  intro k
  rw [Basis.equivFun_self]
  by_cases h : j = k
  · exact ⟨1, by simp [h]⟩
  · exact ⟨0, by rw [map_zero, if_neg h]⟩

theorem integral_span_coordinates (x : A.V) (hx : x ∈ T0 A b) : ∃ o : n → OL, x = ∑ j, o j • b j := by
  choose o ho using hx
  refine ⟨o, ?_⟩
  conv_lhs => rw [← b.sum_equivFun x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← ho j, algebraMap_smul]

def Tst : Submodule OL A.V := Submodule.span OL (⋃ g : G, A.ρ g '' (T0 A b : Set A.V))

theorem integral_span_le_stable : T0 A b ≤ Tst A b := fun x hx =>
  Submodule.subset_span (Set.mem_iUnion.2 ⟨1, x, hx, by simp⟩)

theorem Tst_stable (g : G) (x : A.V) (hx : x ∈ Tst A b) : A.ρ g x ∈ Tst A b := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
    refine Submodule.subset_span (Set.mem_iUnion.2 ⟨g * h, y, hy, ?_⟩)
    rw [map_mul]
    rfl
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hx

theorem Tst_bound [CompactSpace G] (hopen : IsOpen ((T0 A b : Submodule OL A.V) : Set A.V))
    (hdiv : DivT A (T0 A b)) : ∃ a : OL, a ≠ 0 ∧ ∀ x ∈ Tst A b, a • x ∈ T0 A b := by
  have hS : IsCompact (⋃ j, Set.range fun g => A.ρ g (b j)) :=
    isCompact_iUnion fun j => isCompact_range (A.cont (b j))
  obtain ⟨a, ha, hb⟩ := bound_compact A (T0 A b) hopen hdiv _ hS
  refine ⟨a, ha, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
    obtain ⟨o, rfl⟩ := integral_span_coordinates A b y hy
    rw [map_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [LinearMap.map_smul_of_tower, smul_comm]
    exact Submodule.smul_mem _ _ (hb _ (Set.mem_iUnion.2 ⟨j, g, rfl⟩))
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem noZero (hinj : Function.Injective (algebraMap OL LL)) : NoZeroSMulDivisors OL A.V :=
  ⟨fun {c x} h => by
    rw [← algebraMap_smul LL c x] at h
    rcases smul_eq_zero.1 h with h | h
    · exact Or.inl (hinj (h.trans (map_zero _).symm))
    · exact Or.inr h⟩

def latSt [CompactSpace G] [IsNoetherianRing OL] [IsPrincipalIdealRing OL] [IsTopologicalRing LL]
    (hO : IsOpen (Set.range (algebraMap OL LL))) [IsFractionRing OL LL] : Lattice (O := OL) A.ρ where
  T := Tst A b
  stable := Tst_stable A b
  fg := by
    have hinj : Function.Injective (algebraMap OL LL) := IsFractionRing.injective OL LL
    obtain ⟨a, ha, hab⟩ := Tst_bound A b (integral_span_open A b hO) (integral_span_divisible A b)
    haveI : Module.Finite OL ↥(Submodule.span OL (Set.range b)) :=
      Module.Finite.span_of_finite OL (Set.finite_range b)
    haveI := noZero A hinj
    let f : ↥(Tst A b) →ₗ[OL] ↥(Submodule.span OL (Set.range b)) :=
      { toFun := fun x => ⟨a • x.1, by
          obtain ⟨o, ho⟩ := integral_span_coordinates A b _ (hab x.1 x.2)
          rw [ho]
          exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)⟩
        map_add' := fun x y => Subtype.ext (smul_add a x.1 y.1)
        map_smul' := fun o x => Subtype.ext (smul_comm a o x.1) }
    have hf : Function.Injective f := fun x y h => by
      have h' : a • (x.1 - y.1) = 0 := by
        rw [smul_sub]
        exact sub_eq_zero.2 (congrArg Subtype.val h)
      rcases smul_eq_zero.1 h' with h0 | h0
      · exact absurd h0 ha
      · exact Subtype.ext (sub_eq_zero.1 h0)
    haveI : Module.Finite OL ↥(Tst A b) := Module.Finite.of_injective f hf
    exact Module.Finite.iff_fg.1 inferInstance
  free := by
    haveI := noZero A (IsFractionRing.injective OL LL)
    haveI : Module.Finite OL ↥(Tst A b) := by
      have hinj : Function.Injective (algebraMap OL LL) := IsFractionRing.injective OL LL
      obtain ⟨a, ha, hab⟩ := Tst_bound A b (integral_span_open A b hO) (integral_span_divisible A b)
      haveI : Module.Finite OL ↥(Submodule.span OL (Set.range b)) :=
        Module.Finite.span_of_finite OL (Set.finite_range b)
      let f : ↥(Tst A b) →ₗ[OL] ↥(Submodule.span OL (Set.range b)) :=
        { toFun := fun x => ⟨a • x.1, by
            obtain ⟨o, ho⟩ := integral_span_coordinates A b _ (hab x.1 x.2)
            rw [ho]
            exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)⟩
          map_add' := fun x y => Subtype.ext (smul_add a x.1 y.1)
          map_smul' := fun o x => Subtype.ext (smul_comm a o x.1) }
      have hf : Function.Injective f := fun x y h => by
        have h' : a • (x.1 - y.1) = 0 := by
          rw [smul_sub]
          exact sub_eq_zero.2 (congrArg Subtype.val h)
        rcases smul_eq_zero.1 h' with h0 | h0
        · exact absurd h0 ha
        · exact Subtype.ext (sub_eq_zero.1 h0)
      exact Module.Finite.of_injective f hf
    exact Module.free_of_finite_type_torsion_free'
  span := by
    rw [eq_top_iff, ← b.span_eq]
    exact Submodule.span_le.2 fun x ⟨j, hj⟩ => hj ▸ Submodule.subset_span (integral_span_le_stable A b (basis_mem_integral_span A b j))

theorem latSt_open [CompactSpace G] [IsNoetherianRing OL] [IsPrincipalIdealRing OL] [IsTopologicalRing LL]
    (hO : IsOpen (Set.range (algebraMap OL LL))) [IsFractionRing OL LL] :
    IsOpen (((latSt A b hO).T : Submodule OL A.V) : Set A.V) := by
  haveI : ContinuousNeg A.V := ⟨by
    have h : (fun v : A.V => -v) = fun v => (-1 : LL) • v := funext fun v => (neg_one_smul LL v).symm
    rw [h]
    exact continuous_const_smul _⟩
  haveI : IsTopologicalAddGroup A.V := {}
  exact Submodule.isOpen_mono (integral_span_le_stable A b) (integral_span_open A b hO)

theorem latSt_div [CompactSpace G] [IsNoetherianRing OL] [IsPrincipalIdealRing OL] [IsTopologicalRing LL]
    (hO : IsOpen (Set.range (algebraMap OL LL))) [IsFractionRing OL LL] : DivT A (latSt A b hO).T := fun v => by
  obtain ⟨a, ha, h⟩ := integral_span_divisible A b v
  exact ⟨a, ha, integral_span_le_stable A b h⟩

theorem finDim_of_tate [CompactSpace G] [IsNoetherianRing OL] [IsPrincipalIdealRing OL] [IsTopologicalRing LL]
    (hO : IsOpen (Set.range (algebraMap OL LL))) [IsFractionRing OL LL]
    (hT : ∀ LA : Lattice (O := OL) A.ρ, Module.Finite OL (LatticeCohomology LA))
    {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) : FiniteDimensional LL (FiniteCohomology PD A.ρ) := by
  let b₀ := Module.finBasis LL A.V
  haveI := hT (latSt A b₀ hO)
  haveI := finite_H1V A (latSt A b₀ hO) (latSt_open A b₀ hO) (latSt_div A b₀ hO) (IsFractionRing.injective OL LL)
  exact finDim_H1fV A PD

end Stab

section Rank

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {OL : Type} [CommRing OL] [IsDomain OL] [Algebra OL LL] {Qp : Type} [Field Qp]
  [Algebra Qp LL]
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G]
  {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR)
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  [FiniteDimensional (FractionRing O) V]
  (σ : O ≃+* OL) (hσ : ∀ c : O, algebraMap OL LL (σ c) = e (algebraMap O (FractionRing O) c))
  {n : Type} [Fintype n] (bV : Basis n (FractionRing O) V)
  {L : Type} [AddCommGroup L] [Module O L] (bL : Basis n O L) (iL : L →ₗ[O] V) (hb : ∀ j, iL (bL j) = bV j)
  (ρ : Representation O Γ V) (ι : G →* Γ) (hc : ∀ v : TrV e V, Continuous fun g => repL e ρ ι g v)
  (ρL : Representation O Γ L) (hiL : ∀ γ m, iL (ρL γ m) = ρ γ (iL m))

abbrev QF := ↥(finZ e PD ρ ι) ⧸ (LinearMap.range (KDim.cobK ρ)).comap (finZ e PD ρ ι).subtype

abbrev PF := (KFin.finPreG iL (finZ e PD ρ ι)).comap (coZ1s ρL).subtype

def thet0 : ↥(PF e PD iL ρ ι ρL) →ₗ[O] QF e PD ρ ι where
  toFun p := Submodule.Quotient.mk ⟨fun γ => iL (((p : coZ1s ρL) : Γ → L) γ), p.2⟩
  map_add' p q := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    exact Subtype.ext (funext fun γ => map_add iL _ _)
  map_smul' c p := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (funext fun γ => map_smul iL c _)

abbrev hF : ↥(PF e PD iL ρ ι ρL) →ₗ[O] H1z ρL :=
  (Submodule.mkQ ((coB1 ρL).comap (coZ1s ρL).subtype)).comp (PF e PD iL ρ ι ρL).subtype

include hiL in
theorem ker_le : LinearMap.ker (hF e PD iL ρ ι ρL) ≤ LinearMap.ker (thet0 e PD iL ρ ι ρL) := by
  intro p hp
  rw [LinearMap.mem_ker] at hp ⊢
  have h := (Submodule.Quotient.mk_eq_zero _).mp hp
  obtain ⟨m, hm⟩ := h
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨iL m, funext fun γ => ?_⟩
  have h2 : ((p : coZ1s ρL) : Γ → L) γ = ρL γ m - m := (congrFun hm γ).symm
  show ρ γ (iL m) - iL m = iL (((p : coZ1s ρL) : Γ → L) γ)
  rw [h2, map_sub, hiL]

theorem F_eq : KFin.FfG ρL iL (finZ e PD ρ ι) = LinearMap.range (hF e PD iL ρ ι ρL) := by
  rw [LinearMap.range_comp, Submodule.range_subtype]
  rfl

def thet : ↥(KFin.FfG ρL iL (finZ e PD ρ ι)) →ₗ[O] QF e PD ρ ι :=
  ((LinearMap.ker (hF e PD iL ρ ι ρL)).liftQ (thet0 e PD iL ρ ι ρL) (ker_le e PD iL ρ ι ρL hiL)).comp
    (((hF e PD iL ρ ι ρL).quotKerEquivRange).symm.toLinearMap.comp
      (LinearEquiv.ofEq _ _ (F_eq e PD iL ρ ι ρL)).toLinearMap)

theorem thet_mk (p : ↥(PF e PD iL ρ ι ρL)) :
    thet e PD iL ρ ι ρL hiL ⟨hF e PD iL ρ ι ρL p, (F_eq e PD iL ρ ι ρL).symm ▸ LinearMap.mem_range_self _ p⟩ =
      thet0 e PD iL ρ ι ρL p := by
  have h1 : LinearEquiv.ofEq _ _ (F_eq e PD iL ρ ι ρL)
      ⟨hF e PD iL ρ ι ρL p, (F_eq e PD iL ρ ι ρL).symm ▸ LinearMap.mem_range_self _ p⟩ =
      ⟨hF e PD iL ρ ι ρL p, LinearMap.mem_range_self _ p⟩ := Subtype.ext rfl
  show ((LinearMap.ker (hF e PD iL ρ ι ρL)).liftQ (thet0 e PD iL ρ ι ρL) (ker_le e PD iL ρ ι ρL hiL))
      ((hF e PD iL ρ ι ρL).quotKerEquivRange.symm (LinearEquiv.ofEq _ _ (F_eq e PD iL ρ ι ρL)
        ⟨hF e PD iL ρ ι ρL p, (F_eq e PD iL ρ ι ρL).symm ▸ LinearMap.mem_range_self _ p⟩)) = _
  rw [h1, LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

end Rank

section RankLoc

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {OL : Type} [CommRing OL] [IsDomain OL] [Algebra OL LL] {Qp : Type} [Field Qp]
  [Algebra Qp LL]
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G]
  {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR)
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  [FiniteDimensional (FractionRing O) V]
  (σ : O ≃+* OL) (hσ : ∀ c : O, algebraMap OL LL (σ c) = e (algebraMap O (FractionRing O) c))
  {n : Type} [Fintype n] (bV : Basis n (FractionRing O) V)
  {L : Type} [AddCommGroup L] [Module O L] (bL : Basis n O L) (iL : L →ₗ[O] V) (hb : ∀ j, iL (bL j) = bV j)
  (ρ : Representation O Γ V) (ι : G →* Γ) (hc : ∀ v : TrV e V, Continuous fun g => repL e ρ ι g v)
  (ρL : Representation O Γ L) (hiL : ∀ γ m, iL (ρL γ m) = ρ γ (iL m))

def bA : Basis n LL (grepV e OL (Qp := Qp) ρ ι hc).V :=
  Basis.ofEquivFun
    { toFun := fun v j => e (bV.equivFun (show V from v) j)
      invFun := fun f => (bV.equivFun.symm fun j => e.symm (f j) : V)
      map_add' := fun u v => funext fun j => by
        have h : bV.equivFun ((show V from u) + (show V from v)) j =
            bV.equivFun (show V from u) j + bV.equivFun (show V from v) j := by
          rw [map_add]
          rfl
        exact (congrArg e h).trans (map_add e _ _)
      map_smul' := fun c v => funext fun j => by
        have h : bV.equivFun (e.symm c • (show V from v)) j = e.symm c * bV.equivFun (show V from v) j := by
          rw [map_smul]
          rfl
        show e (bV.equivFun (e.symm c • (show V from v)) j) = c * e (bV.equivFun (show V from v) j)
        rw [h, map_mul, RingEquiv.apply_symm_apply]
      left_inv := fun v => by
        show bV.equivFun.symm (fun j => e.symm (e (bV.equivFun (show V from v) j))) = (show V from v)
        simp only [RingEquiv.symm_apply_apply]
        exact bV.equivFun.symm_apply_apply _
      right_inv := fun f => funext fun j => by
        show e (bV.equivFun (bV.equivFun.symm fun j => e.symm (f j)) j) = f j
        rw [LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] }

theorem bA_coord (x : (grepV e OL (Qp := Qp) ρ ι hc).V) (j : n) :
    (bA e (OL := OL) (Qp := Qp) bV ρ ι hc).equivFun x j = e (bV.equivFun (show V from x) j) := by
  unfold bA
  rw [Basis.equivFun_ofEquivFun]
  rfl

include hσ hb in
theorem coord_iL (m : L) (j : n) : bV.equivFun (iL m) j = algebraMap O (FractionRing O) (bL.equivFun m j) := by
  have h : iL m = bV.equivFun.symm (fun j => algebraMap O (FractionRing O) (bL.equivFun m j)) := by
    rw [Basis.equivFun_symm_apply]
    conv_lhs => rw [← bL.sum_equivFun m]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hb, algebraMap_smul]
  rw [h, LinearEquiv.apply_symm_apply]

include hσ hb in

theorem mem_integral_span_iff_image (x : TrV e V) :
    x ∈ T0 (grepV e OL (Qp := Qp) ρ ι hc) (bA e (OL := OL) (Qp := Qp) bV ρ ι hc) ↔ ∃ m : L, tr e (iL m) = x := by
  constructor
  · intro hx
    choose o ho using hx
    refine ⟨∑ j, σ.symm (o j) • bL j, ?_⟩
    show iL (∑ j, σ.symm (o j) • bL j) = (x : V)
    conv_rhs => rw [← bV.sum_equivFun (x : V)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hb, ← algebraMap_smul (FractionRing O) (σ.symm (o j)) (bV j)]
    congr 1
    apply e.injective
    have h1 : algebraMap OL LL (o j) = e (bV.equivFun (show V from x) j) :=
      (ho j).trans (bA_coord e (OL := OL) (Qp := Qp) bV ρ ι hc x j)
    rw [← hσ, RingEquiv.apply_symm_apply, h1]
  · rintro ⟨m, rfl⟩ j
    refine ⟨σ (bL.equivFun m j), ?_⟩
    rw [hσ, ← coord_iL e σ hσ bV bL iL hb]
    exact (bA_coord e (OL := OL) (Qp := Qp) bV ρ ι hc _ j).symm

variable [IsTopologicalRing LL] [IsFractionRing OL LL]

include hb in

theorem div_L (v : V) : ∃ s : O, s ≠ 0 ∧ ∃ m : L, iL m = s • v := by
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ
    (fun j => bV.equivFun v j)
  choose c hc using fun j => hs j (Finset.mem_univ j)
  refine ⟨s, nonZeroDivisors.ne_zero s.2, ∑ j, c j • bL j, ?_⟩
  rw [map_sum]
  conv_rhs => rw [← bV.sum_equivFun v, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hb, ← algebraMap_smul (FractionRing O) (c j), hc j, smul_assoc]

variable [CompactSpace G]

include hσ hb hc hiL in

theorem bound_fin (hι : Function.Surjective ι) (hO : IsOpen (Set.range (algebraMap OL LL))) (c : ↥(finZ e PD ρ ι)) :
    ∃ s : O, s ≠ 0 ∧ ∃ p : Γ → L, ∀ γ, iL (p γ) = s • (c : Γ → V) γ := by
  have hcont : Continuous fun g => tr e ((c : Γ → V) (ι g)) := c.2.1.1
  obtain ⟨a, ha, h⟩ := bound_cont (grepV e OL (Qp := Qp) ρ ι hc) _ (integral_span_open _ (bA e (OL := OL) (Qp := Qp) bV ρ ι hc) hO)
    (integral_span_divisible _ (bA e (OL := OL) (Qp := Qp) bV ρ ι hc)) _ hcont
  have hs : σ.symm a ≠ 0 := fun h0 => ha (by rw [← σ.apply_symm_apply a, h0, map_zero])
  have hγ : ∀ γ, ∃ m : L, iL m = σ.symm a • (c : Γ → V) γ := by
    intro γ
    obtain ⟨g, rfl⟩ := hι γ
    obtain ⟨m, hm⟩ := (mem_integral_span_iff_image e σ hσ bV bL iL hb ρ ι hc (Qp := Qp) _).1 (h g)
    refine ⟨m, ?_⟩
    have h2 := smul_OL e σ hσ (σ.symm a) ((c : Γ → V) (ι g))
    rw [RingEquiv.apply_symm_apply] at h2
    rw [← h2]
    exact hm
  choose p hp using hγ
  exact ⟨σ.symm a, hs, p, hp⟩

end RankLoc

section RankThm

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {OL : Type} [CommRing OL] [IsDomain OL] [Algebra OL LL] {Qp : Type} [Field Qp]
  [Algebra Qp LL]
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G]
  {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR)
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  [FiniteDimensional (FractionRing O) V]
  (σ : O ≃+* OL) (hσ : ∀ c : O, algebraMap OL LL (σ c) = e (algebraMap O (FractionRing O) c))
  {n : Type} [Fintype n] (bV : Basis n (FractionRing O) V)
  {L : Type} [AddCommGroup L] [Module O L] (bL : Basis n O L) (iL : L →ₗ[O] V) (hb : ∀ j, iL (bL j) = bV j)
  (ρ : Representation O Γ V) (ι : G →* Γ) (hc : ∀ v : TrV e V, Continuous fun g => repL e ρ ι g v)
  (ρL : Representation O Γ L) (hiL : ∀ γ m, iL (ρL γ m) = ρ γ (iL m))
  [IsTopologicalRing LL] [IsFractionRing OL LL] [CompactSpace G]

include hσ hb hc in

theorem thet_loc (hι : Function.Bijective ι) (hO : IsOpen (Set.range (algebraMap OL LL)))
    (hinj : Function.Injective iL) :
    IsLocalizedModule (nonZeroDivisors O) (thet e PD iL ρ ι ρL hiL) where
  map_units s := by
    rw [Module.End.isUnit_iff]
    have hs : algebraMap O (FractionRing O) (s : O) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    constructor
    · intro q1 q2 h
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
        ← algebraMap_smul (FractionRing O) (s : O) q1, ← algebraMap_smul (FractionRing O) (s : O) q2] at h
      exact smul_right_injective _ hs h
    · intro q
      refine ⟨(algebraMap O (FractionRing O) (s : O))⁻¹ • q, ?_⟩
      rw [Module.algebraMap_end_apply, ← algebraMap_smul (FractionRing O) (s : O), smul_smul,
        mul_inv_cancel₀ hs, one_smul]
  surj q := by
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨s, hs, p, hp⟩ := bound_fin e PD σ hσ bV bL iL hb ρ ι hc ρL hiL (Qp := Qp) hι.2 hO c
    have hcoc : ∀ γ δ, (c : Γ → V) (γ * δ) = (c : Γ → V) γ + ρ γ ((c : Γ → V) δ) := by
      intro γ δ
      obtain ⟨g, rfl⟩ := hι.2 γ
      obtain ⟨h, rfl⟩ := hι.2 δ
      have h1 := c.2.1.2 g h
      rw [← map_mul]
      exact h1
    have hpz : p ∈ coZ1s ρL := fun γ δ => hinj (by rw [map_add, hiL, hp, hp, hp, hcoc, smul_add, map_smul])
    have hpf : p ∈ KFin.finPreG iL (finZ e PD ρ ι) := by
      show (fun γ => iL (p γ)) ∈ finZ e PD ρ ι
      have h1 : (fun γ => iL (p γ)) = s • (c : Γ → V) := funext hp
      rw [h1]
      exact ((finZ e PD ρ ι).restrictScalars O).smul_mem s c.2
    let z : ↥(PF e PD iL ρ ι ρL) := ⟨⟨p, hpz⟩, hpf⟩
    refine ⟨(⟨hF e PD iL ρ ι ρL z, (F_eq e PD iL ρ ι ρL).symm ▸ LinearMap.mem_range_self _ z⟩,
      ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩), ?_⟩
    show (s : O) • (Submodule.Quotient.mk c : QF e PD ρ ι) = _
    rw [thet_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (funext fun γ => (hp γ).symm)
  exists_of_eq {z1 z2} h := by
    have hz : ((z1 - z2 : ↥(KFin.FfG ρL iL (finZ e PD ρ ι))) : H1z ρL) ∈ LinearMap.range (hF e PD iL ρ ι ρL) := by
      rw [← F_eq e PD iL ρ ι ρL]
      exact (z1 - z2).2
    obtain ⟨p, hp⟩ := hz
    have h1 : thet e PD iL ρ ι ρL hiL (z1 - z2) = thet0 e PD iL ρ ι ρL p := by
      have h2 : z1 - z2 = ⟨hF e PD iL ρ ι ρL p, (F_eq e PD iL ρ ι ρL).symm ▸ LinearMap.mem_range_self _ p⟩ :=
        Subtype.ext hp.symm
      rw [h2, thet_mk]
    have h0 : thet0 e PD iL ρ ι ρL p = 0 := by rw [← h1, map_sub, h, sub_self]
    obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_eq_zero _).mp h0
    obtain ⟨s, hs, m, hm⟩ := div_L bV bL iL hb v
    refine ⟨⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩, ?_⟩
    rw [← sub_eq_zero, ← smul_sub]
    show (s : O) • (z1 - z2) = 0
    apply Subtype.ext
    show (s : O) • ((z1 - z2 : ↥(KFin.FfG ρL iL (finZ e PD ρ ι))) : H1z ρL) = 0
    rw [← hp]
    show (s : O) • (Submodule.Quotient.mk (p : coZ1s ρL) : H1z ρL) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine ⟨m, funext fun γ => hinj ?_⟩
    show iL (ρL γ m - m) = iL ((s : O) • ((p : coZ1s ρL) : Γ → L) γ)
    rw [map_sub, hiL, hm, map_smul, map_smul, ← smul_sub]
    congr 1
    exact congrFun hv γ

include hσ hb hc hiL in

theorem finrank_Ff (hι : Function.Bijective ι) (hO : IsOpen (Set.range (algebraMap OL LL)))
    (hinj : Function.Injective iL) :
    Module.finrank O (↥(KFin.FfG ρL iL (finZ e PD ρ ι)) ⧸ Submodule.torsion O ↥(KFin.FfG ρL iL (finZ e PD ρ ι))) =
      Module.finrank LL (FiniteCohomology PD (repL e ρ ι)) := by
  haveI := thet_loc e PD σ hσ bV bL iL hb ρ ι hc ρL hiL (Qp := Qp) hι hO hinj
  have h1 : Module.finrank O (↥(KFin.FfG ρL iL (finZ e PD ρ ι)) ⧸ Submodule.torsion O ↥(KFin.FfG ρL iL (finZ e PD ρ ι))) =
      Module.finrank O ↥(KFin.FfG ρL iL (finZ e PD ρ ι)) := by
    unfold Module.finrank
    rw [rank_quotient_eq_of_le_torsion le_rfl]
  have h2 := IsLocalizedModule.finrank_eq (p := nonZeroDivisors O) (f := thet e PD iL ρ ι ρL hiL) le_rfl
  have h3 := IsLocalization.finrank_eq (S := FractionRing O) (p := nonZeroDivisors O) (N := QF e PD ρ ι) le_rfl
  have h4 : Module.finrank (FractionRing O) (QF e PD ρ ι) = Module.finrank LL (FiniteCohomology PD (repL e ρ ι)) := by
    unfold Module.finrank
    rw [KDim.rank_finQuot (e := e) (PD := PD) (ρ := ρ) (hι := hι)]
  rw [h1, ← h2, ← h3, h4]

include hσ hb hc hiL in

theorem finrank_Ff' (hι : Function.Bijective ι) (hO : IsOpen (Set.range (algebraMap OL LL)))
    (hinj : Function.Injective iL) (Zf : Submodule (FractionRing O) (Γ → V)) (hZ : Zf = finZ e PD ρ ι) :
    Module.finrank O (↥(KFin.FfG ρL iL Zf) ⧸ Submodule.torsion O ↥(KFin.FfG ρL iL Zf)) =
      Module.finrank LL (FiniteCohomology PD (repL e ρ ι)) := by
  subst hZ
  exact finrank_Ff e PD σ hσ bV bL iL hb ρ ι hc ρL hiL (Qp := Qp) hι hO hinj

end RankThm

section Rec

open Formalism.MainNotions Formalism.MainNotions.N Formalism.RepresentationBoundsCohomology.SF NumberField IsDedekindDomain
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

abbrev bVr : Basis {a // RepresentationBoundsCohomology.blk D.R a = 0} (FractionRing (D.nd.O i)) (KFin.Vr i Dd) :=
  Pi.basisFun (FractionRing (D.nd.O i)) {a // RepresentationBoundsCohomology.blk D.R a = 0}

abbrev bLr : Basis {a // RepresentationBoundsCohomology.blk D.R a = 0} (D.nd.O i) (KFin.Lr i Dd) :=
  Pi.basisFun (D.nd.O i) {a // RepresentationBoundsCohomology.blk D.R a = 0}

theorem iLr_basis (j : {a // RepresentationBoundsCohomology.blk D.R a = 0}) : KFin.iLr i Dd (bLr i Dd j) = bVr i Dd j := by
  funext k
  have h1 : (bLr i Dd j : {a // RepresentationBoundsCohomology.blk D.R a = 0} → D.nd.O i) k = (Pi.single j (1 : D.nd.O i) : _ → D.nd.O i) k :=
    congrFun (Pi.basisFun_apply (D.nd.O i) {a // RepresentationBoundsCohomology.blk D.R a = 0} j) k
  have h2 : (bVr i Dd j : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) k =
      (Pi.single j (1 : FractionRing (D.nd.O i)) : _ → FractionRing (D.nd.O i)) k :=
    congrFun (Pi.basisFun_apply (FractionRing (D.nd.O i)) {a // RepresentationBoundsCohomology.blk D.R a = 0} j) k
  show algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((bLr i Dd j : {a // RepresentationBoundsCohomology.blk D.R a = 0} → D.nd.O i) k) =
    (bVr i Dd j : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) k
  rw [h1, h2]
  rcases eq_or_ne k j with rfl | h
  · simp
  · simp [h]

theorem iLr_inj : Function.Injective (KFin.iLr i Dd) := fun _ _ h =>
  funext fun k => IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)) (congrFun h k)

instance finDimVr : FiniteDimensional (FractionRing (D.nd.O i)) (KFin.Vr i Dd) :=
  inferInstanceAs (FiniteDimensional (FractionRing (D.nd.O i)) ({a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)))

theorem finFf_of (hFin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) (l : K.Col i dc) (hO : KHf.OrbC i dc (KFin.ρV i dc Dd l)) :
    KFin.FinFf i dc Dd l := by
  have hn := KDim.col_over i dc l
  show Module.Finite (D.nd.O i) ↥(KFin.FfG (KFin.ρL i dc Dd l) (KFin.iLr i Dd)
    (KHf.fZ i dc (K.colIdx i dc l) (KFin.ρV i dc Dd l)))
  rw [KHf.fZ_pos i dc _ hn]
  exact finite_FfG (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (D.nbr i _ hn).eO
    (fun c => (Br.toLLK_alg (D.nbr i _ hn) c).symm) (bVr i Dd) (bLr i Dd) (KFin.iLr i Dd) (iLr_basis i Dd)
    (KFin.ρV i dc Dd l) (Br.iota D.nbr i _ hn) (hO hn) (KFin.ρL i dc Dd l) (KFin.iL_equiv i dc Dd l)
    (Br.ι_bijective (D.nbr i _ hn)).2 (iLr_inj i Dd)
    (hFin _ hn (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) _ _)

end Rec

section RecRank

open Formalism.MainNotions Formalism.MainNotions.N Formalism.RepresentationBoundsCohomology.SF NumberField IsDedekindDomain
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem compact_G {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    CompactSpace (Br.G D.nbr i w hw) :=
  isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed _).isCompact

theorem jr_eq (l : K.Col i dc) :
    KFin.jr i dc ρ π (K.colIdx i dc l) =
      Module.finrank (Br.LL D.nbr i _ (KDim.col_over i dc l))
        (FiniteCohomology (Br.PD D.loc D.nbr i _ (KDim.col_over i dc l))
          (KDim.repW i dc ρ π (K.colIdx i dc l) (KDim.col_over i dc l))) := by
  show KHf.jK i dc ρ π (K.colIdx i dc l) = _
  unfold KHf.jK
  rw [dif_pos (KDim.col_over i dc l)]
  rfl

def DimV (l : K.Col i dc) : Prop :=
  Module.finrank (Br.LL D.nbr i _ (KDim.col_over i dc l))
      (FiniteCohomology (Br.PD D.loc D.nbr i _ (KDim.col_over i dc l))
        (repL (eK (D.nbr i _ (KDim.col_over i dc l))) (KFin.ρV i dc Dd l) (Br.iota D.nbr i _ (KDim.col_over i dc l)))) =
    Module.finrank (Br.LL D.nbr i _ (KDim.col_over i dc l))
      (FiniteCohomology (Br.PD D.loc D.nbr i _ (KDim.col_over i dc l))
        (KDim.repW i dc ρ π (K.colIdx i dc l) (KDim.col_over i dc l)))

set_option maxHeartbeats 1000000 in

theorem rankFf_of (hO : Formalism.MainNotions.N.LitGoodO) (l : K.Col i dc) (hOrb : KHf.OrbC i dc (KFin.ρV i dc Dd l))
    (hdim : DimV i dc Dd ρ π l) : KFin.RankFf i dc Dd ρ π l := by
  have hn := KDim.col_over i dc l
  obtain ⟨⟨_, hdvr, hfr⟩, -, -, htop, hopen⟩ := hO (D.nd.l i) (D.nbr i _ hn).LL
  haveI := hfr
  haveI := htop
  haveI := compact_G i hn
  have hZ : KFin.Zf i dc Dd l = finZ (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (KFin.ρV i dc Dd l)
      (Br.iota D.nbr i _ hn) := KHf.fZ_pos i dc _ hn
  have h1 := finrank_Ff' (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (D.nbr i _ hn).eO
    (fun c => (Br.toLLK_alg (D.nbr i _ hn) c).symm) (bVr i Dd) (bLr i Dd) (KFin.iLr i Dd) (iLr_basis i Dd)
    (KFin.ρV i dc Dd l) (Br.iota D.nbr i _ hn) (hOrb hn) (KFin.ρL i dc Dd l) (KFin.iL_equiv i dc Dd l)
    (Br.ι_bijective (D.nbr i _ hn)) hopen (iLr_inj i Dd) _ hZ
  exact h1.trans (hdim.trans (jr_eq i dc ρ π l).symm)

end RecRank

section RecX

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

theorem finX_of (hFin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) (hO : Formalism.MainNotions.N.LitGoodO) (x' : X') (l : K.Col i dc)
    (hc : KDim.ContX i dc r χ x' l) : KDim.FinX i dc r χ x' l := by
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  have hn := KDim.col_over i dc l
  obtain ⟨⟨_, hdvr, hfr⟩, -, -, htop, hopen⟩ := hO (D.nd.l i) (D.nbr i _ hn).LL
  haveI := hdvr
  haveI := hfr
  haveI := htop
  haveI := compact_G i hn
  exact finDim_of_tate (KDim.grepX i dc r χ x' l hc) hopen
    (fun LA => hFin _ hn (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) _ LA) (Br.PD D.loc D.nbr i _ hn)

end RecX

section Final

open Formalism.MainNotions Formalism.MainNotions.N Formalism.RepresentationBoundsCohomology.SF NumberField IsDedekindDomain
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem rankFf (l : K.Col i dc) (hOrb : KHf.OrbC i dc (KFin.ρV i dc Dd l)) (hdim : DimV i dc Dd ρ π l) :
    KFin.RankFf i dc Dd ρ π l :=
  rankFf_of i dc Dd ρ π Formalism.MainNotions.N.T2.litGoodO l hOrb hdim

end Final

section FinalX

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

theorem finX (hFin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) (x' : X') (l : K.Col i dc) (hc : KDim.ContX i dc r χ x' l) :
    KDim.FinX i dc r χ x' l :=
  finX_of i dc r χ hFin Formalism.MainNotions.N.T2.litGoodO x' l hc

end FinalX

section RecOrb

open Formalism.MainNotions Formalism.MainNotions.N Formalism.RepresentationBoundsCohomology.SF NumberField IsDedekindDomain
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

theorem orbC_V
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (l : K.Col i dc) : KHf.OrbC i dc (KFin.ρV i dc Dd l) :=
  KOrb.orbC_uRep i dc r π g0 eB e₁ s Dd hD hc (V := KFin.Vr i Dd)
    (fun c v => KOrb.latM_alg (i := i) (Dd := Dd) (Dd.ρk 0) c v) (K.colIdx i dc l)

theorem finFf_rec (hFin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (l : K.Col i dc) : KFin.FinFf i dc Dd l :=
  finFf_of i dc Dd hFin l (orbC_V i dc r π g0 eB e₁ s Dd hD hc l)

theorem rankFf_rec
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (l : K.Col i dc) (hdim : DimV i dc Dd ρ π l) : KFin.RankFf i dc Dd ρ π l :=
  rankFf i dc Dd ρ π l (orbC_V i dc r π g0 eB e₁ s Dd hD hc l) hdim

theorem finX_rec (hFin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (x' : Dd.X') (l : K.Col i dc) : KDim.FinX i dc Dd.r Dd.χ x' l :=
  finX i dc Dd.r Dd.χ hFin x' l
    (KDim.contX_of_orbC i dc Dd.r Dd.χ x' l (KOrb.orbC_repE i dc r π g0 eB e₁ s Dd hD hc x' (K.colIdx i dc l)))

end RecOrb

section IsoH1f

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ Kk : Type} [Field Qp] [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V W : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    [TopologicalSpace W] [ContinuousAdd W] [ContinuousConstSMul LL W]
    (ρ : Representation LL G V) (ρ' : Representation LL G W)

theorem finrank_H1fV_congr (f : V ≃ₗ[LL] W) (hf : Continuous f) (hf' : Continuous f.symm)
    (heq : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    Module.finrank LL (FiniteCohomology PD ρ) = Module.finrank LL (FiniteCohomology PD ρ') := by
  have heq' : ∀ g w, f.symm (ρ' g w) = ρ g (f.symm w) := fun g w => f.injective (by
    rw [heq, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
  let φ : ↥(finiteCocycles PD ρ) →ₗ[LL] ↥(finiteCocycles PD ρ') :=
    { toFun := fun c => ⟨f ∘ c.1, (cocyclesFunctorial_holds G Qp K₀ Kk B BdR PD LL V W ρ ρ' f.toLinearMap hf heq c.1).2 c.2⟩
      map_add' := fun a b => Subtype.ext (funext fun g => map_add f _ _)
      map_smul' := fun a b => Subtype.ext (funext fun g => map_smul f _ _) }
  let ψ : ↥(finiteCocycles PD ρ') →ₗ[LL] ↥(finiteCocycles PD ρ) :=
    { toFun := fun c => ⟨f.symm ∘ c.1,
        (cocyclesFunctorial_holds G Qp K₀ Kk B BdR PD LL W V ρ' ρ f.symm.toLinearMap hf' heq' c.1).2 c.2⟩
      map_add' := fun a b => Subtype.ext (funext fun g => map_add f.symm _ _)
      map_smul' := fun a b => Subtype.ext (funext fun g => map_smul f.symm _ _) }
  let E : ↥(finiteCocycles PD ρ) ≃ₗ[LL] ↥(finiteCocycles PD ρ') := LinearEquiv.ofLinear φ ψ
    (LinearMap.ext fun c => Subtype.ext (funext fun g => f.apply_symm_apply _))
    (LinearMap.ext fun c => Subtype.ext (funext fun g => f.symm_apply_apply _))
  have hpq : ((B1 ρ).comap (finiteCocycles PD ρ).subtype).map E.toLinearMap = (B1 ρ').comap (finiteCocycles PD ρ').subtype := by
    ext c
    constructor
    · rintro ⟨c₀, ⟨x, hx⟩, rfl⟩
      refine ⟨f x, funext fun g => ?_⟩
      have h : (c₀ : G → V) g = ρ g x - x := (congrFun hx g).symm
      show ρ' g (f x) - f x = f ((c₀ : G → V) g)
      rw [h, map_sub, heq]
    · rintro ⟨y, hy⟩
      refine ⟨E.symm c, ⟨f.symm y, funext fun g => ?_⟩, E.apply_symm_apply c⟩
      have h : (c : G → W) g = ρ' g y - y := (congrFun hy g).symm
      show ρ g (f.symm y) - f.symm y = f.symm ((c : G → W) g)
      rw [h, map_sub, heq']
  exact (Submodule.Quotient.equiv _ _ E hpq).finrank_eq

end IsoH1f

section RecIso

open Formalism.MainNotions Formalism.MainNotions.N Formalism.RepresentationBoundsCohomology.SF NumberField IsDedekindDomain
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

def IsoV (l : K.Col i dc) : Prop :=
  ∃ f : TrV (eK (D.nbr i _ (KDim.col_over i dc l))) (KFin.Vr i Dd) ≃ₗ[Br.LL D.nbr i _ (KDim.col_over i dc l)]
      (Fin D.R.r → Br.LL D.nbr i _ (KDim.col_over i dc l)),
    ∀ g v, f (repL (eK (D.nbr i _ (KDim.col_over i dc l))) (KFin.ρV i dc Dd l)
        (Br.iota D.nbr i _ (KDim.col_over i dc l)) g v) =
      KDim.repW i dc ρ π (K.colIdx i dc l) (KDim.col_over i dc l) g (f v)

theorem dimV_of_iso (l : K.Col i dc) (h : IsoV i dc Dd ρ π l) : DimV i dc Dd ρ π l := by
  obtain ⟨f, hf⟩ := h
  have hn := KDim.col_over i dc l
  obtain ⟨-, -, -, htop, -⟩ := Formalism.MainNotions.N.T2.litGoodO (D.nd.l i) (D.nbr i _ hn).LL
  haveI := htop
  exact finrank_H1fV_congr (Br.PD D.loc D.nbr i _ hn) _ _ f
    (IsModuleTopology.continuous_of_linearMap f.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap f.symm.toLinearMap) hf

theorem rankFf_iso (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (g0 : GE D.nd)
    (eB e₁ s : D.nd.X i → MatN D.nd i)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (l : K.Col i dc) (hiso : IsoV i dc Dd ρ π l) : KFin.RankFf i dc Dd ρ π l :=
  rankFf_rec i dc r π g0 eB e₁ s Dd ρ hD hc l (dimV_of_iso i dc Dd ρ π l hiso)

end RecIso

end Formalism.MainNotions.N.KTate

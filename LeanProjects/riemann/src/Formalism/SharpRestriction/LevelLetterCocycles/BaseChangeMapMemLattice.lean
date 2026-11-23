import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.BCW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

section Rep

variable {G : Type} [Group G] {LL LL' : Type} [Field LL] [Field LL'] [Algebra LL LL']

variable (LL') in

def bρ {V : Type} [AddCommGroup V] [Module LL V] (ρ : Representation LL G V) :
    Representation LL' G (LL' ⊗[LL] V) where
  toFun g := (ρ g).baseChange LL'
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one _ _
  map_mul' g h := by rw [map_mul, LinearMap.baseChange_mul]

theorem bρ_tmul {V : Type} [AddCommGroup V] [Module LL V] (ρ : Representation LL G V) (g : G) (a : LL')
    (v : V) : bρ LL' ρ g (a ⊗ₜ[LL] v) = a ⊗ₜ[LL] ρ g v := rfl

end Rep

section Top

variable {LL LL' : Type} [Field LL] [Field LL'] [Algebra LL LL'] [TopologicalSpace LL]
  [TopologicalSpace LL'] [IsTopologicalRing LL']

set_option warn.classDefReducibility false in

def bTop (V : Type) [AddCommGroup V] [Module LL V] : TopologicalSpace (LL' ⊗[LL] V) :=
  moduleTopology LL' (LL' ⊗[LL] V)

theorem bIsMod (V : Type) [AddCommGroup V] [Module LL V] :
    @IsModuleTopology LL' _ (LL' ⊗[LL] V) _ _ (bTop (LL := LL) (LL' := LL') V) :=
  @IsModuleTopology.mk LL' _ (LL' ⊗[LL] V) _ _ (bTop (LL := LL) (LL' := LL') V) rfl

end Top

section Lin

theorem linInd_frac {O LL V ι : Type} [CommRing O] [IsDomain O] [Field LL] [Algebra O LL]
    [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    [Fintype ι] (b : ι → V) (hb : LinearIndependent O b) : LinearIndependent LL b := by
  refine Fintype.linearIndependent_iff.2 fun x hx i => ?_
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
    (Finset.univ.image x)
  have ha : ∀ j, ∃ a : O, algebraMap O LL a = (s : O) • x j := fun j =>
    hs (x j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  choose a ha using ha
  have h0 : ∑ j, a j • b j = 0 := by
    have : ∑ j, ((s : O) • x j) • b j = (s : O) • ∑ j, x j • b j := by
      rw [Finset.smul_sum]; simp only [smul_assoc]
    rw [hx, smul_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ha j, algebraMap_smul]
  have h1 := Fintype.linearIndependent_iff.1 hb a h0 i
  have h2 := ha i
  rw [h1, map_zero] at h2
  have hs0 : (algebraMap O LL (s : O)) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  rw [Algebra.smul_def] at h2
  exact (mul_eq_zero.1 h2.symm).resolve_left hs0

end Lin

section Lat

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL LL' O O' : Type} [Field Qp] [Field LL]
  [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
  [TopologicalSpace LL] [TopologicalSpace LL'] [IsTopologicalRing LL'] [CommRing O] [Algebra O LL]
  [CommRing O'] [Algebra O' LL']

theorem contSMul_of (hc : Continuous (algebraMap LL LL')) (M : Type) [AddCommGroup M] [Module LL M]
    [Module LL' M] [IsScalarTower LL LL' M] [TopologicalSpace M] [ContinuousSMul LL' M] :
    ContinuousSMul LL M := by
  refine ⟨?_⟩
  have e : (fun p : LL × M => p.1 • p.2) = fun p : LL × M => (algebraMap LL LL' p.1) • p.2 := by
    funext p; rw [algebraMap_smul]
  rw [e]
  exact (hc.comp continuous_fst).smul continuous_snd

example (V : Type) [AddCommGroup V] [Module LL V] : Module O' (LL' ⊗[LL] V) := inferInstance
example (V : Type) [AddCommGroup V] [Module LL V] : IsScalarTower O' LL' (LL' ⊗[LL] V) := inferInstance
example (V : Type) [AddCommGroup V] [Module LL V] : IsScalarTower Qp LL' (LL' ⊗[LL] V) := inferInstance
example (V : Type) [AddCommGroup V] [Module LL V] [FiniteDimensional LL V] :
    FiniteDimensional LL' (LL' ⊗[LL] V) := inferInstance

end Lat

section LatT

variable {Qp LL LL' O O' : Type} [Field LL] [Field LL'] [Algebra LL LL'] [CommRing O] [Algebra O LL]
  [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL'] [IsScalarTower O O' LL']
  [IsScalarTower O LL LL']

def bT {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (T : Submodule O V) : Submodule O' (LL' ⊗[LL] V) :=
  Submodule.span O' (Set.range fun t : T => (1 : LL') ⊗ₜ[LL] (t : V))

theorem one_tmul_smul {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (c : O) (v : V) :
    (1 : LL') ⊗ₜ[LL] (c • v) = (algebraMap O O' c) • ((1 : LL') ⊗ₜ[LL] v) := by
  rw [← algebraMap_smul LL c v, TensorProduct.tmul_smul, algebraMap_smul]
  exact (algebraMap_smul O' c _).symm

end LatT

section LatP

variable {LL LL' O O' : Type} [Field LL] [Field LL'] [Algebra LL LL'] [CommRing O] [IsDomain O]
  [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
  [IsScalarTower O O' LL'] [IsScalarTower O LL LL']
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]

def basisV {ι : Type} [Fintype ι] (T : Submodule O V) (b : Module.Basis ι O T)
    (hspan : Submodule.span LL (T : Set V) = ⊤) : Module.Basis ι LL V :=
  Module.Basis.mk (v := fun i => (b i : V))
    (linInd_frac (O := O) _ (b.linearIndependent.map' T.subtype (Submodule.ker_subtype T)))
    (by
      rw [← hspan]
      refine Submodule.span_le.2 fun x hx => ?_
      have : (⟨x, hx⟩ : T) ∈ Submodule.span O (Set.range b) := by rw [b.span_eq]; trivial
      have h2 := Submodule.mem_span_range_iff_exists_fun O |>.1 this
      obtain ⟨c, hc⟩ := h2
      have hx' : x = ∑ i, c i • (b i : V) := by
        have := congrArg Subtype.val hc
        simpa using this.symm
      rw [hx']
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← algebraMap_smul LL (c i)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem basisV_apply {ι : Type} [Fintype ι] (T : Submodule O V) (b : Module.Basis ι O T)
    (hspan : Submodule.span LL (T : Set V) = ⊤) (i : ι) : basisV T b hspan i = (b i : V) := by
  simp [basisV]

end LatP

section LatQ

variable {LL LL' O O' : Type} [Field LL] [Field LL'] [Algebra LL LL'] [CommRing O] [IsDomain O]
  [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
  [IsScalarTower O O' LL'] [IsScalarTower O LL LL']
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]

def basisV' {ι : Type} [Fintype ι] (T : Submodule O V) (b : Module.Basis ι O T)
    (hspan : Submodule.span LL (T : Set V) = ⊤) : Module.Basis ι LL' (LL' ⊗[LL] V) :=
  (basisV T b hspan).baseChange LL'

theorem basisV'_apply {ι : Type} [Fintype ι] (T : Submodule O V) (b : Module.Basis ι O T)
    (hspan : Submodule.span LL (T : Set V) = ⊤) (i : ι) :
    basisV' (LL' := LL') T b hspan i = (1 : LL') ⊗ₜ[LL] (b i : V) := by
  simp [basisV', Module.Basis.baseChange_apply, basisV_apply]

theorem bT_eq {ι : Type} [Fintype ι] (T : Submodule O V) (b : Module.Basis ι O T) :
    bT (LL' := LL') (O' := O') T = Submodule.span O' (Set.range fun i => (1 : LL') ⊗ₜ[LL] (b i : V)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨t, rfl⟩
    have : t ∈ Submodule.span O (Set.range b) := by rw [b.span_eq]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 this
    have ht : (t : V) = ∑ i, c i • (b i : V) := by
      have := congrArg Subtype.val hc
      simpa using this.symm
    show (1 : LL') ⊗ₜ[LL] (t : V) ∈ _
    rw [ht, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [one_tmul_smul (O' := O')]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨b i, rfl⟩

end LatQ

section LatR

variable {G : Type} [Group G] {Qp LL LL' O O' : Type} [Field Qp] [Field LL] [Field LL']
  [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL'] [CommRing O] [IsDomain O]
  [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
  [IsScalarTower O O' LL'] [IsScalarTower O LL LL']
  {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V]
  [IsScalarTower O LL V]

def bLattice (hO' : Function.Injective (algebraMap O' LL')) {ρ : Representation LL G V}
    (L : Lattice (O := O) ρ) : Lattice (O := O') (bρ LL' ρ) where
  T := bT (LL' := LL') (O' := O') L.T
  stable g x hx := by
    refine Submodule.span_induction (fun y hy => ?_) (by simp) (fun a b _ _ ha hb => ?_)
      (fun c a _ ha => ?_) hx
    · obtain ⟨t, rfl⟩ := hy
      exact Submodule.subset_span ⟨⟨ρ g t, L.stable g t t.2⟩, rfl⟩
    · rw [map_add]; exact Submodule.add_mem _ ha hb
    · rw [← algebraMap_smul LL' c a, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ _ ha
  fg := by
    haveI := L.free
    haveI : Module.Finite O L.T := Module.Finite.iff_fg.2 L.fg
    let b := Module.Free.chooseBasis O L.T
    rw [bT_eq L.T b]
    exact Submodule.fg_span (Set.finite_range _)
  free := by
    haveI := L.free
    haveI : Module.Finite O L.T := Module.Finite.iff_fg.2 L.fg
    let b := Module.Free.chooseBasis O L.T
    rw [bT_eq L.T b]
    have hli : LinearIndependent O' (fun i => (1 : LL') ⊗ₜ[LL] (b i : V)) := by
      refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
      have h1 : ∑ j, (algebraMap O' LL' (c j)) • basisV' (LL' := LL') L.T b L.span j = 0 := by
        simp only [basisV'_apply, algebraMap_smul]; exact hc
      have h2 := Fintype.linearIndependent_iff.1 (basisV' (LL' := LL') L.T b L.span).linearIndependent _ h1 i
      exact hO' (by rw [h2, map_zero])
    exact Module.Free.of_basis (Module.Basis.span hli)
  span := by
    haveI := L.free
    haveI : Module.Finite O L.T := Module.Finite.iff_fg.2 L.fg
    let b := Module.Free.chooseBasis O L.T
    rw [eq_top_iff, ← (basisV' (LL' := LL') L.T b L.span).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [basisV'_apply]
    exact Submodule.subset_span (Submodule.subset_span ⟨b i, rfl⟩)

end LatR

section HomB

variable {G : Type} [Group G] {Qp LL LL' O O' : Type} [Field Qp] [Field LL] [Field LL']
  [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL'] [CommRing O] [IsDomain O]
  [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
  [IsScalarTower O O' LL'] [IsScalarTower O LL LL']
  {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V]
  [IsScalarTower O LL V]
  {V₂ : Type} [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂] [Module O V₂]
  [IsScalarTower O LL V₂]

abbrev bf (f : V →ₗ[LL] V₂) : (LL' ⊗[LL] V) →ₗ[LL'] (LL' ⊗[LL] V₂) := f.baseChange LL'

theorem bf_equiv {ρ : Representation LL G V} {ρ₂ : Representation LL G V₂} (f : V →ₗ[LL] V₂)
    (hf : ∀ g x, f (ρ g x) = ρ₂ g (f x)) (g : G) (x : LL' ⊗[LL] V) :
    bf (LL' := LL') f (bρ LL' ρ g x) = bρ LL' ρ₂ g (bf (LL' := LL') f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp [bf, bρ, hf]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem baseChange_map_mem_lattice {f : V →ₗ[LL] V₂} {T : Submodule O V} {T₂ : Submodule O V₂} (hf : ∀ x ∈ T, f x ∈ T₂)
    (x : LL' ⊗[LL] V) (hx : x ∈ bT (LL' := LL') (O' := O') T) :
    bf (LL' := LL') f x ∈ bT (LL' := LL') (O' := O') T₂ := by
  refine Submodule.span_induction (fun y hy => ?_) (by simp) (fun a b _ _ ha hb => ?_)
    (fun c a _ ha => ?_) hx
  · obtain ⟨t, rfl⟩ := hy
    exact Submodule.subset_span ⟨⟨f t, hf t t.2⟩, by simp [bf]⟩
  · rw [map_add]; exact Submodule.add_mem _ ha hb
  · rw [← algebraMap_smul LL' c a, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ _ ha

theorem bf_onto {f : V →ₗ[LL] V₂} {T : Submodule O V} {T₂ : Submodule O V₂}
    (hon : ∀ y ∈ T₂, ∃ x ∈ T, f x = y) (y : LL' ⊗[LL] V₂) (hy : y ∈ bT (LL' := LL') (O' := O') T₂) :
    ∃ x ∈ bT (LL' := LL') (O' := O') T, bf (LL' := LL') f x = y := by
  refine Submodule.span_induction (fun z hz => ?_) ⟨0, Submodule.zero_mem _, by simp⟩
    (fun a b _ _ ⟨xa, ha, ea⟩ ⟨xb, hb, eb⟩ => ⟨xa + xb, Submodule.add_mem _ ha hb, by rw [map_add, ea, eb]⟩)
    (fun c a _ ⟨xa, ha, ea⟩ => ⟨c • xa, Submodule.smul_mem _ _ ha, by
      rw [← algebraMap_smul LL' c xa, map_smul, ea, algebraMap_smul]⟩) hy
  obtain ⟨t, rfl⟩ := hz
  obtain ⟨x, hx, e⟩ := hon t t.2
  exact ⟨(1 : LL') ⊗ₜ[LL] x, Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩, by simp [bf, e]⟩

end HomB

section Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL LL' O O' : Type} [Field Qp] [Field LL]
  [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
  [TopologicalSpace LL] [TopologicalSpace LL'] [IsTopologicalRing LL'] [CommRing O] [IsDomain O]
  [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
  [IsScalarTower O O' LL'] [IsScalarTower O LL LL']

def bLoc (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    (T : LocLat G Qp LL O) : LocLat G Qp LL' O' :=
  letI : TopologicalSpace (LL' ⊗[LL] T.V) := bTop (LL := LL) (LL' := LL') T.V
  haveI hM : IsModuleTopology LL' (LL' ⊗[LL] T.V) := bIsMod (LL := LL) (LL' := LL') T.V
  haveI : ContinuousAdd (LL' ⊗[LL] T.V) := IsModuleTopology.toContinuousAdd LL' _
  haveI : ContinuousSMul LL' (LL' ⊗[LL] T.V) := IsModuleTopology.toContinuousSMul LL' _
  haveI : ContinuousSMul LL (LL' ⊗[LL] T.V) := contSMul_of hc _
  { V := LL' ⊗[LL] T.V
    ρ := bρ LL' T.ρ
    cont := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simpa using continuous_const
      | tmul a v =>
        have hl : Continuous (TensorProduct.mk LL LL' T.V 1) :=
          IsModuleTopology.continuous_of_linearMap _
        have e : (fun g => bρ LL' T.ρ g (a ⊗ₜ[LL] v)) = fun g => a • (TensorProduct.mk LL LL' T.V 1) (T.ρ g v) := by
          funext g
          simp [bρ_tmul, TensorProduct.smul_tmul']
        rw [e]
        exact (hl.comp (T.cont v)).const_smul a
      | add x y hx hy =>
        have e : (fun g => bρ LL' T.ρ g (x + y)) = fun g => bρ LL' T.ρ g x + bρ LL' T.ρ g y := by
          funext g; rw [map_add]
        rw [e]; exact hx.add hy
    L := bLattice (LL' := LL') (O' := O') hO' T.L }

end Loc

section HomL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL LL' O O' : Type} [Field Qp] [Field LL]
  [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
  [TopologicalSpace LL] [TopologicalSpace LL'] [IsTopologicalRing LL'] [CommRing O] [IsDomain O]
  [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
  [IsScalarTower O O' LL'] [IsScalarTower O LL LL']

def bfL (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    {T₁ T₂ : LocLat G Qp LL O} (f : T₁.V →ₗ[LL] T₂.V) :
    (bLoc (O' := O') hc hO' T₁).V →ₗ[LL'] (bLoc (O' := O') hc hO' T₂).V :=
  bf (LL' := LL') f

def bHom (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) :
    LatHom (bLoc (O' := O') hc hO' T₁).L (bLoc (O' := O') hc hO' T₂).L :=
  { f := bfL (O' := O') hc hO' F.f
    equiv := fun g x => bf_equiv F.f F.equiv g x
    cont := IsModuleTopology.continuous_of_linearMap (R := LL') _
    T_le := fun x hx => baseChange_map_mem_lattice (O' := O') F.T_le x hx }

theorem bHom_onto (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hF : F.Onto) : (bHom (O' := O') hc hO' F).Onto :=
  fun y hy => bf_onto (O' := O') hF y hy

end HomL

end Formalism.MainNotions.UnusedSlot80.BCW

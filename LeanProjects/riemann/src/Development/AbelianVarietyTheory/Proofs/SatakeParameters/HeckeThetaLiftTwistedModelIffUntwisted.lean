import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOpsIffHeckeLiftsAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open Formalism.L2.Col
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.HeckeLifts₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3}

abbrev SysL (A3 : FamIn3 K G Pl0 I0 Ty T m) (j : Fin m) (p : A3.fam3.base3.Ix) :
    ((A3.liftI j A3.A.fam.μ0).OpIx → ℂ) → Prop :=
  cxSys A3.fam3.base3.v0.embedding ((A3.liftI j A3.A.fam.μ0).HasRes3 (A3.fam3.tr3 j p.1))

end Abstract

section TwEig

variable {s : Bool} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem tw_map_mul (a b : Module.End ℂ E) : (Tw.map s (a * b) : Module.End ℂ (Tw s E)) = Tw.map s a * Tw.map s b :=
  LinearMap.ext fun _ => rfl

theorem tw_map_pow (a : Module.End ℂ E) (k : ℕ) : (Tw.map s (a ^ k) : Module.End ℂ (Tw s E)) = Tw.map s a ^ k := by
  induction k with
  | zero => exact LinearMap.ext fun _ => rfl
  | succ k ih => rw [pow_succ, tw_map_mul, ih, pow_succ]

theorem tw_map_sub_smul (a : Module.End ℂ E) (μ : ℂ) :
    (Tw.map s a - μ • 1 : Module.End ℂ (Tw s E)) = Tw.map s (a - cj s μ • 1) :=
  LinearMap.ext fun _ => rfl

theorem mem_maxGen_tw (a : Module.End ℂ E) (μ : ℂ) (v : Tw s E) :
    v ∈ Module.End.maxGenEigenspace (Tw.map s a : Module.End ℂ (Tw s E)) μ ↔ Tw.out v ∈ a.maxGenEigenspace (cj s μ) := by
  simp only [Module.End.mem_maxGenEigenspace]
  rw [tw_map_sub_smul]
  refine exists_congr fun k => ?_
  rw [← tw_map_pow]
  exact Iff.rfl

theorem eigAt_tw {I : Type} (h : I → Module.End ℂ E) (y : I → ℂ) :
    eigAt (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) y = Tw.sub s (eigAt h fun i => cj s (y i)) := by
  refine SetLike.ext fun v => ?_
  rw [show v ∈ Tw.sub s (eigAt h fun i => cj s (y i)) ↔ Tw.out v ∈ eigAt h (fun i => cj s (y i)) from Iff.rfl]
  simp only [eigAt, Submodule.mem_iInf]
  exact forall_congr' fun i => mem_maxGen_tw (h i) (y i) v

theorem sub_iSup {ι : Type} (V : ι → Submodule ℂ E) : Tw.sub s (⨆ c, V c) = ⨆ c, Tw.sub s (V c) := by
  refine le_antisymm (fun x hx => ?_) (iSup_le fun c v hv => (le_iSup V c) hv)
  exact Submodule.iSup_induction V (motive := fun y => (Tw.mk s y : Tw s E) ∈ ⨆ c, Tw.sub s (V c)) hx
    (fun c y hy => Submodule.mem_iSup_of_mem c hy) (zero_mem _) (fun a b ha hb => add_mem ha hb)

theorem sub_iSup_prop {P : Prop} (V : P → Submodule ℂ E) : Tw.sub s (⨆ c, V c) = ⨆ c, Tw.sub s (V c) := by
  by_cases hP : P
  · rw [iSup_pos hP, iSup_pos hP]
  · rw [iSup_neg hP, iSup_neg hP]
    rfl

theorem eigSum_tw {I : Type} (h : I → Module.End ℂ E) (Q : (I → ℂ) → Prop) :
    eigSum (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) Q = Tw.sub s (eigSum h fun x => Q fun i => cj s (x i)) := by
  unfold eigSum
  rw [sub_iSup]
  simp only [sub_iSup_prop, eigAt_tw]
  have hcc : ∀ y : I → ℂ, (fun i => cj s (cj s (y i))) = y := fun y => funext fun i => cj_cj s (y i)
  refine le_antisymm (iSup₂_le fun y hy => le_iSup₂_of_le (fun i => cj s (y i)) (by rw [hcc]; exact hy) le_rfl)
    (iSup₂_le fun x hx => le_iSup₂_of_le (fun i => cj s (x i)) hx ?_)
  rw [hcc]

end TwEig

section Concrete

open HeckeLiftsCompare

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}

def twE (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : Fin D.R.m) (H : Module.End ℂ (R.HW j (sg0 D A3.A)).H) :
    Module.End ℂ ((R.toCx3 F).W j) :=
  (Tw.map (twAt D.what₂.embLL A3.A.v0) H : Module.End ℂ (Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H))

theorem theta_jL (j : Fin D.R.m) (t : T) (y : (A3.A.fam.L j t).S.Forms) :
    (R.toCx3 F).θ' j t ((R.toCx3 F).jL j t y) =
      (R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (R.jV j t y)) :
        Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H) := rfl

theorem twE_smul (j : Fin D.R.m) (H : Module.End ℂ (R.HW j (sg0 D A3.A)).H) (c : ℂ) (v : (R.HW j (sg0 D A3.A)).H) :
    twE R F j H (c • Tw.mk (twAt D.what₂.embLL A3.A.v0) v : Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H) =
      (c • Tw.mk (twAt D.what₂.embLL A3.A.v0) (H v) : Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H) :=
  (Tw.map (twAt D.what₂.embLL A3.A.v0) H).map_smul c _

theorem intw_of_rat (hM : R.toRealDat.IsModels) (j : Fin D.R.m) (t : T) (i : (A3.liftI j t).OpIx)
    (H : Module.End ℂ (R.HW j (sg0 D A3.A)).H)
    (h : ∀ f, R.thG j t (R.jV j t ((A3.liftI j t).opAll i f)) = H (R.thG j t (R.jV j t f)))
    (u : (R.toCx3 F).FLC j t) :
    (R.toCx3 F).θ' j t ((R.toCx3 F).opLC j t (Sum.inl i) u) = twE R F j H ((R.toCx3 F).θ' j t u) := by
  have hK := RealDat3.kFormL_of (F := F) hM
  have key : ((R.toCx3 F).θ' j t) ∘ₗ ((R.toCx3 F).opLC j t (Sum.inl i)) = (twE R F j H) ∘ₗ ((R.toCx3 F).θ' j t) := by
    refine LinearMap.ext_on (hK j t).2 ?_
    rintro _ ⟨k, rfl⟩
    have e1 := CxData.jL_opL (R.toCx3 F) hK j t (Sum.inl i) (CxData.bL (A := A3.fam3.amb3) j t k)
    simp only [LinearMap.comp_apply]
    refine (congrArg ((R.toCx3 F).θ' j t) e1.symm).trans ?_
    refine (theta_jL j t _).trans ?_
    refine Eq.trans ?_ (congrArg (twE R F j H) (theta_jL j t _).symm)
    refine Eq.trans ?_ (twE_smul j H _ _).symm
    exact congrArg (fun v => (R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) v :
      Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H)) (h _)
  exact LinearMap.congr_fun key u

open Classical in

def spOf (hW' : IndefiniteRowSideFullHecke.LocalHeckeLifts.OpW R.toRealDat) (j : Fin D.R.m) (t : T) (i : A3.A.ok t × ℕ) : Module.End ℂ (R.HW j (sg0 D A3.A)).H :=
  if i.2 ≤ (Vc D j).rank then hW' j t (Sum.inl i) else 0

abbrev SysC (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (j : Fin D.R.m) (p : A3.fam3.base3.Ix) :
    ((A3.liftI j A3.A.fam.μ0).OpIx → ℂ) → Prop :=
  cxSys D.what₂.embLL ((A3.liftI j A3.A.fam.μ0).HasRes3 (A3.fam3.tr3 j p.1))

theorem sysL_cj (R : RealDat3 D A3 Ks) (j : Fin D.R.m) (p : A3.fam3.base3.Ix) (x : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) :
    SysL A3 j p (fun i => cj (twAt D.what₂.embLL A3.A.v0) (x i)) ↔ SysC A3 j p x := by
  constructor
  · refine fun h => Exists.elim h fun y hy => ⟨y, hy.1, funext fun i => ?_⟩
    have e : cj (twAt D.what₂.embLL A3.A.v0) (x i) = A3.A.v0.embedding (y i) := congrFun hy.2 i
    rw [R.toRealDat.emb0] at e
    rw [← cj_cj (twAt D.what₂.embLL A3.A.v0) (x i), e, cj_cj]
  · refine fun h => Exists.elim h fun y hy => ⟨y, hy.1, funext fun i => ?_⟩
    have e : x i = D.what₂.embLL (y i) := congrFun hy.2 i
    show cj (twAt D.what₂.embLL A3.A.v0) (x i) = A3.A.v0.embedding (y i)
    rw [R.toRealDat.emb0, e]

def unE (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (h : Module.End ℂ (Tw s E)) : Module.End ℂ E where
  toFun v := Tw.out (h (Tw.mk s v))
  map_add' x y := (congrArg Tw.out (h.map_add (Tw.mk s x) (Tw.mk s y)))
  map_smul' c v := by
    have e : (Tw.mk s (c • v) : Tw s E) = cj s c • Tw.mk s v := by
      show c • v = cj s (cj s c) • v
      rw [cj_cj]
    show Tw.out (h (Tw.mk s (c • v))) = c • Tw.out (h (Tw.mk s v))
    rw [e, map_smul, Tw.out_smul, cj_cj]

theorem twE_commute (j : Fin D.R.m) (a b : Module.End ℂ (R.HW j (sg0 D A3.A)).H) :
    Commute (twE R F j a) (twE R F j b) ↔ Commute a b :=
  ⟨fun h => LinearMap.ext fun v => LinearMap.congr_fun h.eq v, fun h => LinearMap.ext fun v => LinearMap.congr_fun h.eq v⟩

theorem rat_of_intw (hM : R.toRealDat.IsModels) (j : Fin D.R.m) (hph : R.phs j ≠ 0) (t : T) (i : (A3.liftI j t).OpIx)
    (H : Module.End ℂ (R.HW j (sg0 D A3.A)).H)
    (h : ∀ u, (R.toCx3 F).θ' j t ((R.toCx3 F).opLC j t (Sum.inl i) u) = twE R F j H ((R.toCx3 F).θ' j t u))
    (f : (A3.A.fam.L j t).S.Forms) :
    R.thG j t (R.jV j t ((A3.liftI j t).opAll i f)) = H (R.thG j t (R.jV j t f)) := by
  have hK := RealDat3.kFormL_of (F := F) hM
  have e1 := CxData.jL_opL (R.toCx3 F) hK j t (Sum.inl i) f
  have e2 := (congrArg ((R.toCx3 F).θ' j t) e1).trans (h _)
  have e3 := ((theta_jL (R := R) (F := F) j t _).symm.trans e2).trans
    ((congrArg (twE R F j H) (theta_jL j t f)).trans (twE_smul j H _ _))
  exact smul_right_injective (Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H) hph e3

structure UntwL (g : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (R.HW j (sg0 D A3.A)).H) : Prop where
  rat : ∀ j t i f, R.thG j t (R.jV j t ((A3.liftI j t).opAll i f)) = g j t i (R.thG j t (R.jV j t f))
  comm : ∀ j, PairComm (g j A3.A.fam.μ0)
  parts : ∀ j p, R.Wp3 j p = eigSum (g j A3.A.fam.μ0) (SysC A3 j p)

theorem sub_inj (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {A B : Submodule ℂ E}
    (h : Tw.sub s A = Tw.sub s B) : A = B :=
  SetLike.ext fun x => SetLike.ext_iff.1 h (Tw.mk s x)

theorem hecke_theta_lift_twisted_model_iff_untwisted (hM : R.toRealDat.IsModels) (hph : ∀ j, R.phs j ≠ 0)
    (g : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (R.HW j (sg0 D A3.A)).H) :
    HeckeIntertwiningLifts A3 (R.toCx3 F) (fun j t i => twE R F j (g j t i)) ↔ UntwL (R := R) g := by
  have hp : ∀ j p, eigSum (fun i => twE R F j (g j A3.A.fam.μ0 i)) (SysL A3 j p) =
      Tw.sub (twAt D.what₂.embLL A3.A.v0) (eigSum (g j A3.A.fam.μ0) (SysC A3 j p)) := fun j p => by
    have e := eigSum_tw (s := twAt D.what₂.embLL A3.A.v0) (g j A3.A.fam.μ0) (SysL A3 j p)
    have e' : (fun x : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ => SysL A3 j p fun i => cj (twAt D.what₂.embLL A3.A.v0) (x i)) =
        SysC A3 j p := funext fun x => propext (sysL_cj R j p x)
    rw [e'] at e
    exact e
  constructor
  · intro h
    refine ⟨fun j t i f => rat_of_intw hM j (hph j) t i _ (h.intw j t i) f, fun j i i' => (twE_commute j _ _).1 (h.comm j i i'), fun j p => ?_⟩
    refine sub_inj (twAt D.what₂.embLL A3.A.v0) ?_
    exact (h.parts j p).trans (hp j p)
  · intro h
    refine ⟨fun j t i u => intw_of_rat hM j t i _ (h.rat j t i) u, fun j i i' => (twE_commute j _ _).2 (h.comm j i i'), fun j p => ?_⟩
    refine Eq.trans ?_ (hp j p).symm
    exact congrArg (Tw.sub (twAt D.what₂.embLL A3.A.v0)) (h.parts j p)

theorem phs_ne_zero (hC : R.WeakCharacterisation F) (j : Fin D.R.m) : R.phs j ≠ 0 :=
  norm_ne_zero_iff.1 (by rw [(hC.phase j).1]; exact one_ne_zero)

def unW (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : Fin D.R.m) (h : Module.End ℂ ((R.toCx3 F).W j)) :
    Module.End ℂ (R.HW j (sg0 D A3.A)).H :=
  unE (E := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) h

theorem untw_of_hH (hC : R.WeakCharacterisation F) {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ ((R.toCx3 F).W j)}
    (hH : HeckeIntertwiningLifts A3 (R.toCx3 F) hW) : UntwL (R := R) fun j t i => unW R F j (hW j t i) :=
  (hecke_theta_lift_twisted_model_iff_untwisted (F := F) hC.base.models (phs_ne_zero hC) fun j t i => unW R F j (hW j t i)).1 hH

end Concrete

end GlobalTheory.HeckeLifts₂

end

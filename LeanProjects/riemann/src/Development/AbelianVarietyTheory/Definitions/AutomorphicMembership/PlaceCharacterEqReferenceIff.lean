import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open scoped InnerProductSpace

namespace GlobalTheory.Mem

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def lvlForms {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (r : Representation K G S.Forms)
    (P : Subgroup G) (ψ : P →* Kˣ) : Set S.Forms := {f | ∀ h : P, r (h : G) f = ((ψ h : Kˣ) : K) • f}

def intForms {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) : Set S.Forms :=
  {f | ∀ c, (f : S.Cl → S.V) c ∈ S.Nab c}

def intSpan (D : D7) {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V) : AddSubgroup V :=
  AddSubgroup.closure {y | ∃ a : 𝓞 D.what₂.LL, ∃ x ∈ s, y = D.what₂.embLL (a : D.what₂.LL) • x}

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure SideTie (R : RealDat D A Ks) (F : Face D A) (tup : T → D.what₂.Tup) (b : Bool) {EE : Type} [NormedAddCommGroup EE]
    [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) where

  eE : EE →ₗ[ℂ] R.HE.H

  eE_range : LinearMap.range eE = (R.EEat (R.levR F b)).comap R.HE.e

  eE_norm : ∀ x, ‖eE x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2

  eA : ∀ t, S.Amb (tup t) →ₗ[ℂ] (R.HX t).H

  eA_range : ∀ t, LinearMap.range (eA t) =
    Submodule.span ℂ (R.jX t '' lvlForms (A.MtildeCSD t) (A.leftGroupActionRight t) (F.lvl b).P (F.lvl b).ψ)

  eA_norm : ∀ t x, ‖eA t x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2

  eOp_tie : ∀ t x (f : (A.MtildeCSD t).Forms), eA t x = R.jX t f →
    eA t (S.eOp (tup t) x) = R.jX t ((A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (idemOf A.X) f)

  iota_tie : ∀ t x, eE (S.iota (tup t) x) = R.Th t (eA t x)

  lat_tie : ∀ t, eA t '' (S.Mtilde (tup t)).carrier =
    R.jX t '' (lvlForms (A.MtildeCSD t) (A.leftGroupActionRight t) (F.lvl b).P (F.lvl b).ψ ∩ intForms (A.MtildeCSD t))

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure RowsTieSum (R : RealDat D A Ks) (F : Face D A) (X0 : BaseLevelRowSide D) where

  tup : T → D.what₂.Tup

  tup_inj : Function.Injective tup

  tup_zero : tup A.μ0 = D.what₂.mu0

  muAt_tie : ∀ w, D.what₂.muAt w = tup (R.mu (D.plEq w))

  sharp : SideTie R F tup true (RowSide.sharp D)

  base : SideTie R F tup false X0.s

  ty : D.what₂.FT → A.fam.base.Ix

  ft_tie : ∀ σ, sharp.eE (D.what₂.onb σ) ∈ R.EEp (ty (D.what₂.ft σ))

  framedRowBaseTie : ∀ σ, base.eE (D.what₂.onb0 σ) ∈ R.EEp (ty (D.what₂.ft0 σ))

  eV : ∀ (i : Fin D.R.m) t, D.what₂.Mt (tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.HV i t).H

  eV_range : ∀ i t, LinearMap.range (eV i t) =
    Submodule.span ℂ (R.jV i t '' lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹)

  eV_norm : ∀ i t x, ‖eV i t x‖ ^ 2 = RealDat.nP F false * ‖x‖ ^ 2

  eV_rat : ∀ i t, Set.range (fun x => eV i t (D.what₂.jMt (tup t) ((i : ℕ) + 1) x)) =
    R.jV i t '' lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹

  eV_lat : ∀ i t, intSpan D (eV i t '' (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier) =
    intSpan D (R.jV i t '' (lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹ ∩ intForms (A.MtCSD i t)))

  eMt_tie : ∀ i t x (f : (A.MtCSD i t).Forms), eV i t x = R.jV i t f →
    eV i t (D.what₂.eMt (tup t) ((i : ℕ) + 1) x) = R.jV i t ((A.MtCSD i t).gaOp (A.leftGroupActionLift i t) (idemOf A.X) f)

  eW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H

  eW_range : ∀ i, LinearMap.range (eW i) = (R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).comap (R.HW i (sg0 D A)).e

  eW_norm : ∀ i x, ‖eW i x‖ ^ 2 = RealDat.nP F false * ‖x‖ ^ 2

  eW_lat : ∀ i, intSpan D (eW i '' (D.what₂.MjLat ((i : ℕ) + 1)).carrier) =
    intSpan D ((R.FW i).j (sg0 D A) '' ((R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A.X).coeff g) : Set _))

  theta_tie : ∀ i t x, eW i (D.what₂.thetaP (tup t) ((i : ℕ) + 1) x) = R.thG i t (eV i t x)

  isot_sum : ∀ (i : Fin D.R.m) π,
    (⨆ π', ⨆ (_ : ty π' = ty π), D.what₂.isot ((i : ℕ) + 1) π') = (R.Wp i (ty π)).comap (eW i)

  lam_tie : ∀ (i : Fin D.R.m) t π, D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ →
    D.what₂.lamP (tup t) ((i : ℕ) + 1) π = R.lam i t (ty π) A.v0

  etaJ_tie : ∀ (i : Fin D.R.m) w, D.what₂.muAt w ≠ D.what₂.mu0 → D.what₂.etaJ ((i : ℕ) + 1) w =
    A.fam.etaJ F.P0 F.ψ0 (R.toCx F).zs i (R.mu (D.plEq w)) (D.plEq w)

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure RowsTie (R : RealDat D A Ks) (F : Face D A) (X0 : BaseLevelRowSide D) where

  tup : T → D.what₂.Tup

  tup_inj : Function.Injective tup

  tup_zero : tup A.μ0 = D.what₂.mu0

  muAt_tie : ∀ w, D.what₂.muAt w = tup (R.mu (D.plEq w))

  sharp : SideTie R F tup true (RowSide.sharp D)

  base : SideTie R F tup false X0.s

  ty : D.what₂.FT → A.fam.base.Ix

  ty_inj : Function.Injective ty

  ft_tie : ∀ σ, sharp.eE (D.what₂.onb σ) ∈ R.EEp (ty (D.what₂.ft σ))

  framedRowBaseTie : ∀ σ, base.eE (D.what₂.onb0 σ) ∈ R.EEp (ty (D.what₂.ft0 σ))

  eV : ∀ (i : Fin D.R.m) t, D.what₂.Mt (tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.HV i t).H

  eV_range : ∀ i t, LinearMap.range (eV i t) =
    Submodule.span ℂ (R.jV i t '' lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹)

  eV_norm : ∀ i t x, ‖eV i t x‖ ^ 2 = RealDat.nP F false * ‖x‖ ^ 2

  eV_rat : ∀ i t, Set.range (fun x => eV i t (D.what₂.jMt (tup t) ((i : ℕ) + 1) x)) =
    R.jV i t '' lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹

  eV_lat : ∀ i t, intSpan D (eV i t '' (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier) =
    intSpan D (R.jV i t '' (lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹ ∩ intForms (A.MtCSD i t)))

  eMt_tie : ∀ i t x (f : (A.MtCSD i t).Forms), eV i t x = R.jV i t f →
    eV i t (D.what₂.eMt (tup t) ((i : ℕ) + 1) x) = R.jV i t ((A.MtCSD i t).gaOp (A.leftGroupActionLift i t) (idemOf A.X) f)

  eW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H

  eW_range : ∀ i, LinearMap.range (eW i) = (R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).comap (R.HW i (sg0 D A)).e

  eW_norm : ∀ i x, ‖eW i x‖ ^ 2 = RealDat.nP F false * ‖x‖ ^ 2

  eW_lat : ∀ i, intSpan D (eW i '' (D.what₂.MjLat ((i : ℕ) + 1)).carrier) =
    intSpan D ((R.FW i).j (sg0 D A) '' ((R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A.X).coeff g) : Set _))

  theta_tie : ∀ i t x, eW i (D.what₂.thetaP (tup t) ((i : ℕ) + 1) x) = R.thG i t (eV i t x)

  isot_tie : ∀ (i : Fin D.R.m) π, D.what₂.isot ((i : ℕ) + 1) π = (R.Wp i (ty π)).comap (eW i)

  lam_tie : ∀ (i : Fin D.R.m) t π, D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ →
    D.what₂.lamP (tup t) ((i : ℕ) + 1) π = R.lam i t (ty π) A.v0

  etaJ_tie : ∀ (i : Fin D.R.m) w, D.what₂.muAt w ≠ D.what₂.mu0 → D.what₂.etaJ ((i : ℕ) + 1) w =
    A.fam.etaJ F.P0 F.ψ0 (R.toCx F).zs i (R.mu (D.plEq w)) (D.plEq w)

section Basic

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (r : Representation K G S.Forms)

def lvlSub (P : Subgroup G) (ψ : P →* Kˣ) : Submodule K S.Forms where
  carrier := lvlForms S r P ψ
  zero_mem' := fun h => by simp
  add_mem' := fun {f g} hf hg h => by rw [map_add, hf h, hg h, smul_add]
  smul_mem' := fun a f hf h => by rw [map_smul, hf h, smul_comm]

example : lvlForms S r ⊥ 1 = Set.univ := by
  refine Set.eq_univ_of_forall fun f h => ?_
  rw [Subgroup.mem_bot.1 h.2, map_one]; simp

example (P : Subgroup G) (h : P) (hr : r (h : G) = -1) (f : S.Forms) (hf : f ∈ lvlForms S r P 1) : f = 0 := by
  have h1 := hf h
  rw [hr] at h1
  have h2 : (2 : K) • f = 0 := by
    rw [two_smul]; nth_rewrite 1 [← neg_neg f]
    rw [neg_add_eq_zero]; simpa using h1
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

example {V : Type} [AddCommGroup V] [Module ℂ V] : intSpan D (∅ : Set V) = ⊥ := by simp [intSpan]

end Basic

theorem injective_of_norm_sq {F : Face D A} {b : Bool} {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (e : V →ₗ[ℂ] W) (h : ∀ x, ‖e x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2) :
    Function.Injective e := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 := h x
  rw [hx, norm_zero, zero_pow two_ne_zero] at h1
  have h2 := (mul_eq_zero.1 h1.symm).resolve_left (RealDat.nP_pos (F := F) b).ne'
  simpa using h2

theorem inner_of_norm_sq {F : Face D A} {b : Bool} {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (e : V →ₗ[ℂ] W) (h : ∀ x, ‖e x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2) (x y : V) :
    ⟪e x, e y⟫_ℂ = ((RealDat.nP F b : ℝ) : ℂ) * ⟪x, y⟫_ℂ := by
  have h' : ∀ x, ((‖e x‖ : ℝ) : ℂ) ^ 2 = ((RealDat.nP F b : ℝ) : ℂ) * ((‖x‖ : ℝ) : ℂ) ^ 2 := fun x => by exact_mod_cast h x
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, ← map_add, ← map_sub, ← map_smul, ← map_sub, ← map_add]
  simp only [Complex.coe_algebraMap, h']
  ring

namespace SideTie

variable {R : RealDat D A Ks} {F : Face D A} {tup : T → D.what₂.Tup} {b : Bool} {EE : Type} [NormedAddCommGroup EE]
  [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {S : RowSide D EE} (Y : SideTie R F tup b S)

theorem eE_injective : Function.Injective Y.eE := injective_of_norm_sq _ Y.eE_norm

end SideTie

section Fibre

variable {V H I J : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup H] [Module ℂ H]

example : (⨆ π : Bool, ⨆ (_ : (fun _ => ()) π = ()),
      (if π then LinearMap.range (LinearMap.inl ℂ ℂ ℂ) else LinearMap.range (LinearMap.inr ℂ ℂ ℂ))) = ⊤ ∧
    LinearMap.range (LinearMap.inl ℂ ℂ ℂ) ≠ ⊤ := by
  refine ⟨?_, fun h => ?_⟩
  · simp only [iSup_pos, iSup_bool_eq, if_true, Bool.false_eq_true, if_false]
    exact LinearMap.sup_range_inl_inr
  · obtain ⟨x, hx⟩ : ((0, 1) : ℂ × ℂ) ∈ LinearMap.range (LinearMap.inl ℂ ℂ ℂ) := h ▸ Submodule.mem_top
    simpa using congrArg Prod.snd hx

end Fibre

namespace RowsTieSum

variable {R : RealDat D A Ks} {F : Face D A} {X0 : BaseLevelRowSide D} (Y : RowsTieSum R F X0)

theorem eW_injective (i : Fin D.R.m) : Function.Injective (Y.eW i) := injective_of_norm_sq _ (Y.eW_norm i)

def Separated : Prop := Function.Injective Y.ty

theorem isot_eq_of_separated (h : Y.Separated) (i : Fin D.R.m) (π : D.what₂.FT) :
    D.what₂.isot ((i : ℕ) + 1) π = (R.Wp i (Y.ty π)).comap (Y.eW i) := by
  rw [← Y.isot_sum i π]
  simp only [(show Function.Injective Y.ty from h).eq_iff, iSup_iSup_eq_left]

def toRowsTie (h : Y.Separated) : RowsTie R F X0 where
  tup := Y.tup
  tup_inj := Y.tup_inj
  tup_zero := Y.tup_zero
  muAt_tie := Y.muAt_tie
  sharp := Y.sharp
  base := Y.base
  ty := Y.ty
  ft_tie := Y.ft_tie
  framedRowBaseTie := Y.framedRowBaseTie
  eV := Y.eV
  eV_range := Y.eV_range
  eV_norm := Y.eV_norm
  eV_rat := Y.eV_rat
  eV_lat := Y.eV_lat
  eMt_tie := Y.eMt_tie
  eW := Y.eW
  eW_range := Y.eW_range
  eW_norm := Y.eW_norm
  eW_lat := Y.eW_lat
  theta_tie := Y.theta_tie
  lam_tie := Y.lam_tie
  etaJ_tie := Y.etaJ_tie
  ty_inj := h
  isot_tie := Y.isot_eq_of_separated h

end RowsTieSum

namespace RowsTie

variable {R : RealDat D A Ks} {F : Face D A} {X0 : BaseLevelRowSide D} (Y : RowsTie R F X0)

theorem eW_injective (i : Fin D.R.m) : Function.Injective (Y.eW i) := injective_of_norm_sq _ (Y.eW_norm i)

theorem iSup_isot (i : Fin D.R.m) (π : D.what₂.FT) :
    (⨆ π', ⨆ (_ : Y.ty π' = Y.ty π), D.what₂.isot ((i : ℕ) + 1) π') = (R.Wp i (Y.ty π)).comap (Y.eW i) := by
  simp only [Y.ty_inj.eq_iff, iSup_iSup_eq_left, Y.isot_tie]

def toSum : RowsTieSum R F X0 where
  tup := Y.tup
  tup_inj := Y.tup_inj
  tup_zero := Y.tup_zero
  muAt_tie := Y.muAt_tie
  sharp := Y.sharp
  base := Y.base
  ty := Y.ty
  ft_tie := Y.ft_tie
  framedRowBaseTie := Y.framedRowBaseTie
  eV := Y.eV
  eV_range := Y.eV_range
  eV_norm := Y.eV_norm
  eV_rat := Y.eV_rat
  eV_lat := Y.eV_lat
  eMt_tie := Y.eMt_tie
  eW := Y.eW
  eW_range := Y.eW_range
  eW_norm := Y.eW_norm
  eW_lat := Y.eW_lat
  theta_tie := Y.theta_tie
  lam_tie := Y.lam_tie
  etaJ_tie := Y.etaJ_tie
  isot_sum := Y.iSup_isot

end RowsTie

end GlobalTheory.Mem

end

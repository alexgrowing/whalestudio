import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StabCnt
open Formalism.L2.SG.Pf

variable {D : D7}

theorem mem_orth_iff {U : Submodule D.host.E (VS D).V} {v : (VS D).V} :
    v ∈ orth (VS D) U ↔ ∀ x ∈ U, (VS D).hT x v = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem sup_span_add {P : Submodule D.host.E (VS D).V} {x d : (VS D).V} (hd : d ∈ P) :
    P ⊔ Submodule.span D.host.E {x + d} = P ⊔ Submodule.span D.host.E {x} := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
      (Submodule.mem_sup_left hd)
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_singleton_le_iff_mem]
    have h2 : x + d ∈ P ⊔ Submodule.span D.host.E {x + d} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self (x + d))
    have h3 : d ∈ P ⊔ Submodule.span D.host.E {x + d} := Submodule.mem_sup_left hd
    have h1 := Submodule.sub_mem _ h2 h3
    simpa using h1

variable {T : D.host.E}

theorem xflag_succ (A : LFlag (VS D) D.R.rS T) (j : ℕ) (hj : j < D.R.rS) :
    Xflag A (j + 1) = Xflag A j ⊔ Submodule.span D.host.E {A.fl.e ⟨j, hj⟩} := by
  show Submodule.span _ (A.fl.e '' {i | i.1 < j + 1}) = Submodule.span _ (A.fl.e '' {i | i.1 < j}) ⊔ _
  rw [← Set.image_singleton, ← Submodule.span_union, ← Set.image_union]
  congr 2
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
  omega

theorem xflag_ge (A : LFlag (VS D) D.R.rS T) (j : ℕ) (hj : D.R.rS ≤ j) : Xflag A j = Xflag A D.R.rS := by
  show Submodule.span _ (A.fl.e '' {i | i.1 < j}) = Submodule.span _ (A.fl.e '' {i | i.1 < D.R.rS})
  congr 2
  ext i
  simp only [Set.mem_setOf_eq]
  omega

theorem frame_castSucc (A : LFlag (VS D) D.R.rS T) (i : Fin D.R.rS) : frame A i.castSucc = A.fl.e i := by
  simp [frame, FlagG.fvec]

theorem frame_last (A : LFlag (VS D) D.R.rS T) : frame A (Fin.last _) = A.fl.z := by
  simp [frame, FlagG.fvec]

theorem adapt_xflag {A B : LFlag (VS D) D.R.rS T} {a : GV D} (h : Adapt a A B) (j : ℕ) :
    (Xflag A j).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag B j := by
  induction j with
  | zero => rw [xflag_zero, xflag_zero, Submodule.map_bot]
  | succ j ih =>
    by_cases hj : j < D.R.rS
    · rw [xflag_succ A j hj, xflag_succ B j hj, Submodule.map_sup, ih, Submodule.map_span, Set.image_singleton]
      have hd := h.2 (Fin.castSucc ⟨j, hj⟩)
      rw [frame_castSucc, frame_castSucc, Fin.coe_castSucc] at hd
      have e : (a : (VS D).V →ₗ[D.host.E] (VS D).V) (A.fl.e ⟨j, hj⟩) = B.fl.e ⟨j, hj⟩ + (a (A.fl.e ⟨j, hj⟩) - B.fl.e ⟨j, hj⟩) := by
        simp
      rw [e, sup_span_add hd]
    · rw [xflag_ge A (j + 1) (by omega), xflag_ge B (j + 1) (by omega), ← xflag_ge A j (by omega),
        ← xflag_ge B j (by omega), ih]

theorem adapt_xsp {A B : LFlag (VS D) D.R.rS T} {a : GV D} (h : Adapt a A B) :
    (Xsp A).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B := by
  rw [xsp_eq, xsp_eq, adapt_xflag h]

theorem orth_map_isom {a : GV D} (ha : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {U U' : Submodule D.host.E (VS D).V}
    (hU : U.map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = U') :
    (orth (VS D) U).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = orth (VS D) U' := by
  ext w
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, mem_orth_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩ x' hx'
    rw [← hU] at hx'
    obtain ⟨x, hx, rfl⟩ := hx'
    simp only [LinearEquiv.coe_coe]
    rw [ha]; exact hv x hx
  · intro hw
    refine ⟨a.symm w, fun x hx => ?_, by simp⟩
    have := hw (a x) (hU ▸ Submodule.mem_map_of_mem hx)
    have e : (VS D).hT (a x) (a (a.symm w)) = (VS D).hT x (a.symm w) := ha _ _
    simp only [LinearEquiv.apply_symm_apply] at e
    rw [← e]; exact this

theorem adapt_orth {A B : LFlag (VS D) D.R.rS T} {a : GV D} (h : Adapt a A B) :
    (orth (VS D) (Xsp A)).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = orth (VS D) (Xsp B) :=
  orth_map_isom h.1 (adapt_xsp h)

theorem mem_of_map_eq {a : GV D} {U U' : Submodule D.host.E (VS D).V}
    (hU : U.map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = U') {x : (VS D).V} (hx : x ∈ U) : a x ∈ U' := by
  rw [← hU]; exact Submodule.mem_map_of_mem hx

theorem symm_mem_of_map_eq {a : GV D} {U U' : Submodule D.host.E (VS D).V}
    (hU : U.map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = U') {y : (VS D).V} (hy : y ∈ U') : a.symm y ∈ U := by
  rw [← hU] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  simpa using hx

theorem adapt_mul {A B C : LFlag (VS D) D.R.rS T} {a b : GV D} (ha : Adapt a A B) (hb : Adapt b B C) :
    Adapt (b * a) A C := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hb.1 ha.1, fun k => ?_⟩
  have e : (b * a) (frame A k) - frame C k = b (a (frame A k) - frame B k) + (b (frame B k) - frame C k) := by
    rw [le_mul_app, map_sub]; abel
  rw [e]
  exact add_mem (mem_of_map_eq (adapt_xflag hb _) (ha.2 k)) (hb.2 k)

theorem adapt_inv {A B : LFlag (VS D) D.R.rS T} {a : GV D} (ha : Adapt a A B) : Adapt a⁻¹ B A := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem ha.1, fun k => ?_⟩
  have e : a⁻¹ (frame B k) - frame A k = -(a.symm (a (frame A k) - frame B k)) := by
    rw [le_inv_app, map_sub]; simp
  rw [e]
  exact neg_mem (symm_mem_of_map_eq (adapt_xflag ha _) (ha.2 k))

theorem z_mem_orth (A : LFlag (VS D) D.R.rS T) : A.fl.z ∈ orth (VS D) (Xsp A) := by
  rw [mem_orth_iff]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact A.fl.z_orth i
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem adapt_nrat {A : LFlag (VS D) D.R.rS T} {n : GV D} (hn : n ∈ NRat A) : Adapt n A A := by
  refine ⟨hn.1, fun k => ?_⟩
  induction k using Fin.lastCases with
  | last =>
    rw [frame_last, Fin.val_last, ← xsp_eq]
    exact hn.2.2 _ (z_mem_orth A)
  | cast i =>
    rw [frame_castSucc, Fin.coe_castSucc]
    apply hn.2.1 i.1
    show A.fl.e i ∈ Submodule.span _ (A.fl.e '' {k | k.1 < i.1 + 1})
    exact Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩

theorem frameAdaptedIsometry_of_fixing_both_frames {T' : D.host.E} {A : LFlag (VS D) D.R.rS T} {A' : LFlag (VS D) D.R.rS T'} {h : GV D}
    (hh : h ∈ H0 A A') : Adapt h A A ∧ Adapt h A' A' :=
  ⟨⟨hh.1, fun k => by rw [hh.2.1 k, sub_self]; exact zero_mem _⟩,
   ⟨hh.1, fun k => by rw [hh.2.2 k, sub_self]; exact zero_mem _⟩⟩

theorem adapt_mapLF {A : LFlag (VS D) D.R.rS T} {γ : GV D} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    Adapt γ A (mapLF γ A) := by
  refine ⟨hγ, fun k => ?_⟩
  have : frame (mapLF γ A) k = γ (frame A k) := by
    simp only [mapLF, dif_pos hγ, frame]
    rw [fvec_mapFlag]
  rw [this, sub_self]; exact zero_mem _

theorem nrat_conj {A B : LFlag (VS D) D.R.rS T} {a n : GV D} (ha : Adapt a A B) (hn : n ∈ NRat A) :
    a * n * a⁻¹ ∈ NRat B := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ha.1 hn.1)
    ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem ha.1), fun j x hx => ?_, fun x hx => ?_⟩
  · have e : (a * n * a⁻¹) x - x = a (n (a.symm x) - a.symm x) := by
      rw [le_mul_app, le_mul_app, le_inv_app, map_sub]; simp
    rw [e]
    exact mem_of_map_eq (adapt_xflag ha j) (hn.2.1 j _ (symm_mem_of_map_eq (adapt_xflag ha _) hx))
  · have e : (a * n * a⁻¹) x - x = a (n (a.symm x) - a.symm x) := by
      rw [le_mul_app, le_mul_app, le_inv_app, map_sub]; simp
    rw [e]
    exact mem_of_map_eq (adapt_xsp ha) (hn.2.2 _ (symm_mem_of_map_eq (adapt_orth ha) hx))

theorem nrat_eq_nlam (A : LFlag (VS D) D.R.rS T) : NRat A = NLam ⊤ A := by
  ext n
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, ?_⟩, h2, h3⟩
    rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_top, LinearMap.range_eq_top]
    exact n.surjective
  · rintro ⟨⟨h1, _⟩, h2, h3⟩
    exact ⟨h1, h2, h3⟩

def NRatSub (A : LFlag (VS D) D.R.rS T) : Subgroup (GV D) := NLamSub ⊤ A

theorem mem_nratSub {A : LFlag (VS D) D.R.rS T} {n : GV D} : n ∈ NRatSub A ↔ n ∈ NRat A := by
  rw [nrat_eq_nlam]; rfl

theorem nrat_mul {A : LFlag (VS D) D.R.rS T} {a b : GV D} (ha : a ∈ NRat A) (hb : b ∈ NRat A) : a * b ∈ NRat A :=
  mem_nratSub.1 ((NRatSub A).mul_mem (mem_nratSub.2 ha) (mem_nratSub.2 hb))

theorem nrat_inv {A : LFlag (VS D) D.R.rS T} {a : GV D} (ha : a ∈ NRat A) : a⁻¹ ∈ NRat A :=
  mem_nratSub.1 ((NRatSub A).inv_mem (mem_nratSub.2 ha))

theorem nrat_one (A : LFlag (VS D) D.R.rS T) : (1 : GV D) ∈ NRat A :=
  mem_nratSub.1 (NRatSub A).one_mem

section Defs

variable {T T' : D.host.E}

def InB (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T') (lam lam' : LV D) (γ : GV D)
    (b : GV D × GV D) : Prop :=
  b.1 ∈ Aut0 F0 lam ∧ b.2 ∈ Aut0 F0' lam' ∧ KeyEq F0 F0' lam γ (b.1 * γ * b.2⁻¹)

def Corr (F0 F : LFlag (VS D) D.R.rS T) (F0' F' : LFlag (VS D) D.R.rS T') (γ g : GV D) (b : GV D × GV D)
    (h : GV D) : Prop :=
  h ∈ H0 F F' ∧ ∃ n ∈ NRat F0, ∃ n' ∈ NRat F0', b.1 * γ * b.2⁻¹ = n * γ * n' ∧
    h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) ∈ NRat F ∧ h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) ∈ NRat F'

end Defs

end GlobalTheory.StabCnt

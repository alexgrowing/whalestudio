import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwistBaseCoefficientRingResidueFieldFinite

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial

theorem exists_basis_coord_lattice {O V : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
    (B : Submodule O V) (hfg : B.FG)
    (hsp : Submodule.span (FractionRing O) (B : Set V) = ⊤) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) (FractionRing O) V),
      ∀ f : V, f ∈ B ↔ ∀ t, e.repr f t ∈ (algebraMap O (FractionRing O)).range := by
  classical
  have hfin : Module.Finite O B := Module.Finite.iff_fg.2 hfg
  have htf : Module.IsTorsionFree O V := Module.IsTorsionFree.trans_faithfulSMul O (FractionRing O) V
  have hfree : Module.Free O B := inferInstance
  let bO := Module.finBasis O B
  let v : Fin (Module.finrank O B) → V := fun t => (bO t : V)
  have hliO : LinearIndependent O v := bO.linearIndependent.map' B.subtype (Submodule.ker_subtype B)
  have hliK : LinearIndependent (FractionRing O) v :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).1 hliO
  have hBspan : B = Submodule.span O (Set.range v) := by
    have h1 : Submodule.map B.subtype (Submodule.span O (Set.range bO)) = B := by
      rw [bO.span_eq, Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_span, ← Set.range_comp] at h1
    exact h1.symm
  have hle : (⊤ : Submodule (FractionRing O) V) ≤ Submodule.span (FractionRing O) (Set.range v) := by
    rw [← hsp, Submodule.span_le]
    intro x hx
    have hx' : x ∈ Submodule.span O (Set.range v) := hBspan ▸ hx
    exact Submodule.span_subset_span O (FractionRing O) (Set.range v) hx'
  let e := Module.Basis.mk hliK hle
  have he : ∀ t, e t = v t := fun t => by simp [e]
  refine ⟨_, e, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
  · rw [hBspan] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      intro s
      rw [← he, e.repr_self]
      by_cases h : t = s
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [h]⟩
    | zero => intro s; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro s
      rw [map_add, Finsupp.add_apply]
      exact add_mem (hx s) (hy s)
    | smul a x _ hx =>
      intro s
      rw [← algebraMap_smul (FractionRing O) a x, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_mem ⟨a, rfl⟩ (hx s)
  · choose c hc using hf
    rw [← e.sum_repr f]
    refine sum_mem fun t _ => ?_
    rw [← hc t, algebraMap_smul, he]
    exact B.smul_mem _ (hBspan ▸ Submodule.subset_span ⟨t, rfl⟩)

section SideCoord

variable {K C : Type} [Field K] [Field C] (iC : K →+* C) {V : Bool → Type}
  [∀ b, AddCommGroup (V b)] [∀ b, Module K (V b)] {n : Bool → ℕ}
  (e : ∀ b, Module.Basis (Fin (n b)) K (V b))

def sideEv (b : Bool) : V b →+ ((Σ b', Fin (n b')) → C) where
  toFun f y := if h : y.1 = b then iC ((e b).repr f (h ▸ y.2)) else 0
  map_zero' := by
    funext y
    by_cases h : y.1 = b <;> simp [h]
  map_add' f g := by
    funext y
    by_cases h : y.1 = b <;> simp [h]

@[simp] theorem sideEv_same (b : Bool) (f : V b) (t : Fin (n b)) :
    sideEv iC e b f ⟨b, t⟩ = iC ((e b).repr f t) := by
  simp [sideEv]

theorem sideEv_other {b b' : Bool} (h : b' ≠ b) (f : V b) (t : Fin (n b')) :
    sideEv iC e b f ⟨b', t⟩ = 0 := by
  simp [sideEv, h]

theorem sideEv_smul (b : Bool) (a : K) (f : V b) (y : Σ b', Fin (n b')) :
    sideEv iC e b (a • f) y = iC a * sideEv iC e b f y := by
  obtain ⟨b', t⟩ := y
  by_cases h : b' = b
  · subst h; simp
  · simp [sideEv_other iC e h]

theorem sideEv_inj (b : Bool) : Function.Injective (sideEv iC e b) := by
  intro f g hfg
  apply (e b).repr.injective
  ext t
  have := congrFun hfg ⟨b, t⟩
  exact iC.injective (by simpa using this)

def sideU (b : Bool) (T : Module.End K (V b)) (c y : Σ b', Fin (n b')) : C :=
  if h : c.1 = b then sideEv iC e b (T (e b (h ▸ c.2))) y else 0

theorem sideEv_end (b : Bool) (T : Module.End K (V b)) (f : V b) (y : Σ b', Fin (n b')) :
    sideEv iC e b (T f) y = ∑ c, sideU iC e b T c y * sideEv iC e b f c := by
  classical
  have h0 : T f = ∑ t, (e b).repr f t • T (e b t) := by
    conv_lhs => rw [← (e b).sum_repr f]
    simp only [map_sum, map_smul]
  have h1 : sideEv iC e b (T f) y =
      ∑ t, iC ((e b).repr f t) * sideEv iC e b (T (e b t)) y := by
    rw [h0, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun t _ => sideEv_smul iC e b _ _ y
  rw [h1, Fintype.sum_sigma, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp [sideU, mul_comm]
  · intro b' _ hb
    refine Finset.sum_eq_zero fun t _ => ?_
    simp [sideEv_other iC e hb]
  · simp

end SideCoord

theorem exists_nth_of_fg_full : ∀ (D : D7) (tw : NTw D.R D.host D.what₂ D.LL0 D.nd)
    (ex : NExp D.R D.host D.what₂ D.LL0 D.nd tw),
    (∀ i : tw.Tw, ∃ iC : FractionRing (tw.O i) →+* ℂ_[tw.l i], ∀ x, ‖iC x‖ ≤ 1 ↔
      x ∈ (algebraMap (tw.O i) (FractionRing (tw.O i))).range) →
    (∀ i j b, (ex.Bsup i j b).FG ∧
      Submodule.span (FractionRing (tw.O i)) (ex.Bsup i j b : Set (ex.Fm i j b)) = ⊤) →
    Nonempty (NTh D.R D.host D.what₂ D.LL0 D.nd tw ex) := by
  classical
  intro D tw ex hi hB
  choose iC hiC using hi
  have hex := fun i j b =>
    exists_basis_coord_lattice (ex.Bsup i j b) (hB i j b).1 (hB i j b).2
  choose n e he using hex
  have hsup : ∀ i j b, {f : ex.Fm i j b | f ∈ (⊤ : AddSubgroup (ex.Fm i j b)) ∧
      ∀ y, ‖sideEv (iC i) (e i j) b f y‖ ≤ 1} = (ex.Bsup i j b : Set (ex.Fm i j b)) := by
    intro i j b
    ext f
    simp only [Set.mem_ofPred_eq, AddSubgroup.mem_top, true_and, SetLike.mem_coe]
    rw [he i j b f]
    constructor
    · intro h t
      have := h ⟨b, t⟩
      rw [sideEv_same] at this
      exact (hiC i _).1 this
    · intro h y
      obtain ⟨b', t⟩ := y
      by_cases hb : b' = b
      · subst hb
        rw [sideEv_same]
        exact (hiC i _).2 (h t)
      · rw [sideEv_other _ _ hb]
        simp
  exact ⟨{
    iC := iC
    iC_int := hiC
    aL := fun i => if ∃ k, tw.l i = D.host.g k then 1 else 0
    aL_g := fun i k h => if_pos ⟨k, h⟩
    aL_off := fun i h => if_neg (not_exists.2 h)
    Pt := fun i j => Σ b, Fin (n i j b)
    ev := fun i j b => sideEv (iC i) (e i j) b
    ev_smul := fun i j b a f y => sideEv_smul _ _ b a f y
    ev_inj := fun i j b => sideEv_inj _ _ b
    Lt := fun _ _ => PUnit
    acgLt := fun _ _ => inferInstance
    modLt := fun _ _ => inferInstance
    freeLt := fun _ _ => inferInstance
    finLt := fun _ _ => inferInstance
    Let := fun _ _ => PEmpty
    finLet := fun _ _ => inferInstance
    Harm := fun _ _ => Set.univ
    Ctr := fun _ _ => PEmpty
    ctrC := fun _ _ κ => κ.elim
    Harm_def := fun i j P => ⟨fun _ κ => κ.elim, fun _ => Set.mem_univ _⟩
    thV := fun _ _ _ _ _ => 0
    thV_add := fun _ _ _ _ _ _ => by simp
    thV_smul := fun _ _ _ _ _ _ => by simp
    thV_addP := fun _ _ _ _ _ _ => by simp
    thV_smulP := fun _ _ _ _ _ _ => by simp
    datPhi := fun _ _ _ _ => 0
    datP := fun _ _ _ _ => 0
    recDet := fun _ _ _ => 1
    Kq := fun _ _ _ => PUnit
    grpKq := fun _ _ _ => inferInstance
    actK := fun _ _ _ _ y => y
    actK_one := fun _ _ _ _ => rfl
    actK_mul := fun _ _ _ _ _ _ => rfl
    recDetq := fun _ _ _ _ => 1
    recDetq_mem := fun _ _ _ _ => one_mem _
    recDet_act := fun _ _ _ _ _ _ _ _ _ _ => rfl
    recDetq_act := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    hkIdx := fun i j _ _ => Σ b, Fin (n i j b)
    finHk := fun _ _ _ _ => inferInstance
    hkMove := fun _ _ _ _ c _ => c
    hkU := fun i j b k P c y => sideU (iC i) (e i j) b (ex.hkF i j b k P) c y
    hk_ev := fun i j b k P _ _ _ _ f y => sideEv_end _ _ b _ f y
    MaximalUnramifiedExtension := fun _ => ⊤
    FmUr := fun _ _ _ => ⊤
    FmUr_smul := fun _ _ _ _ _ _ _ => AddSubgroup.mem_top _
    FmUr_span := fun i j b => by
      rw [AddSubgroup.coe_top, Submodule.span_univ]
    Bsup_def := fun i j b => by
      rw [hsup i j b, Submodule.span_eq] }⟩

end GlobalTheory.HeightCounting

end

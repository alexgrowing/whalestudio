import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.AlgIdentity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelevantCarrierNonempty.InSCarrierNonempty
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.FourParts

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.FourParts

namespace PI.UnitaryGroupMassFormula.IdCellInSW

section Flag

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem coef_expand (G : FlagG S r T) (x : S.V) (hx : x ∈ G.X) : x = ∑ a, G.coefX x a • G.e a := by
  have hx' : x ∈ Submodule.span E (Set.range G.e) := hx
  simp only [FlagG.coefX, dif_pos hx']
  have := G.e_indep.linearCombination_repr ⟨x, hx'⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at this
  exact this.symm

theorem coef_add (G : FlagG S r T) (a : Fin r) (x : S.V) (hx : x ∈ G.X) (y : S.V) (hy : y ∈ G.X) :
    G.coefX (x + y) a = G.coefX x a + G.coefX y a := by
  have hx' : x ∈ Submodule.span E (Set.range G.e) := hx
  have hy' : y ∈ Submodule.span E (Set.range G.e) := hy
  have hxy : x + y ∈ Submodule.span E (Set.range G.e) := Submodule.add_mem _ hx' hy'
  simp only [FlagG.coefX, dif_pos hx', dif_pos hy', dif_pos hxy]
  have e : (⟨x + y, hxy⟩ : Submodule.span E (Set.range G.e)) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
  rw [e, map_add, Finsupp.add_apply]

theorem coef_smul (G : FlagG S r T) (a : Fin r) (t : E) (x : S.V) (hx : x ∈ G.X) :
    G.coefX (t • x) a = t * G.coefX x a := by
  have hx' : x ∈ Submodule.span E (Set.range G.e) := hx
  have htx : t • x ∈ Submodule.span E (Set.range G.e) := Submodule.smul_mem _ t hx'
  simp only [FlagG.coefX, dif_pos hx', dif_pos htx]
  have e : (⟨t • x, htx⟩ : Submodule.span E (Set.range G.e)) = t • ⟨x, hx'⟩ := rfl
  rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem coef_e (G : FlagG S r T) (a b : Fin r) : G.coefX (G.e b) a = if a = b then 1 else 0 := by
  have hb : G.e b ∈ Submodule.span E (Set.range G.e) := Submodule.subset_span ⟨b, rfl⟩
  simp only [FlagG.coefX, dif_pos hb]
  rw [G.e_indep.repr_eq_single b ⟨G.e b, hb⟩ rfl, Finsupp.single_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

theorem e_mem_X (G : FlagG S r T) (a : Fin r) : G.e a ∈ G.X := Submodule.subset_span ⟨a, rfl⟩

theorem X_iso (G : FlagG S r T) : ∀ x ∈ G.X, ∀ y ∈ G.X, S.hT x y = 0 := by
  have h1 : ∀ a, ∀ x ∈ G.X, S.hT x (G.e a) = 0 := by
    intro a x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact G.e_iso b a
    | zero => simp
    | add y w _ _ hy hw => simp [hy, hw]
    | smul t y _ hy => simp [hy]
  intro x hx y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, rfl⟩ := hz
    exact h1 b x hx
  | zero => simp
  | add y w _ _ hy hw => simp [hy, hw]
  | smul t y _ hy => simp [hy]

end Flag

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TraceOne (D : D7) : Prop := ∃ θ : 𝓞 D.host.E, (θ : D.host.E) + star (θ : D.host.E) = 1

def Jd (D : D7) (a : Fin D.R.rS) : Submodule (𝓞 D.host.E) D.host.E :=
  ((ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    Submodule (𝓞 D.host.E) D.host.E)

theorem XS_coef {D : D7} {T : D.host.E} (G : FlagG (VS D) D.R.rS T) (y : (VS D).V) (hy : y ∈ XS D G) :
    y ∈ G.X ∧ ∀ a, G.coefX y a ∈ Jd D a := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, t, ht, rfl⟩ := hz
    refine ⟨G.X.smul_mem _ (e_mem_X G b), fun a => ?_⟩
    rw [coef_smul G a t _ (e_mem_X G b), coef_e]
    by_cases hab : a = b
    · subst hab
      simp only [if_true, mul_one]
      exact (FractionalIdeal.mem_coe).2 ht
    · simp only [hab, if_false, mul_zero]
      exact Submodule.zero_mem _
  | zero =>
    refine ⟨G.X.zero_mem, fun a => ?_⟩
    have := coef_smul G a 0 0 G.X.zero_mem
    rw [zero_smul, zero_mul] at this
    rw [this]
    exact Submodule.zero_mem _
  | add y w _ _ hy hw =>
    exact ⟨G.X.add_mem hy.1 hw.1, fun a => by
      rw [coef_add G a y hy.1 w hw.1]
      exact Submodule.add_mem _ (hy.2 a) (hw.2 a)⟩
  | smul o y _ hy =>
    refine ⟨by rw [← algebraMap_smul D.host.E o y]; exact G.X.smul_mem _ hy.1, fun a => ?_⟩
    rw [← algebraMap_smul D.host.E o y, coef_smul G a _ y hy.1, ← Algebra.smul_def]
    exact Submodule.smul_mem _ o (hy.2 a)

theorem smul_e_mem_XS {D : D7} {T : D.host.E} (G : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS) (t : D.host.E)
    (ht : t ∈ Jd D a) : t • G.e a ∈ XS D G :=
  Submodule.subset_span ⟨a, t, (FractionalIdeal.mem_coe).1 ht, rfl⟩

theorem isIdF_of (D : D7) (hθ : TraceOne D) {u u' : D.what₂.Word}
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : IsRowLat D F0 Λ) (F' : LFlag (hS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (hP : PD D Λ (lf D F0) u' F') (hin : InSF (lf D F0) F') : IsIdF Λ (lf D F0) F' := by
  obtain ⟨θ, hθ⟩ := hθ
  obtain ⟨_, ⟨hlat, hU, _, _⟩, hXS⟩ := hΛ
  obtain ⟨_, _, _, hXS'⟩ := hP

  have hle : ∀ k, F0.Xa k ≤ F'.fl.Xa k := PI.UnitaryGroupMassFormula.InSRelevantW.xa_le_of hin.1
  have hin' : ∀ a : Fin D.R.rS, F0.e a - F'.fl.e a ∈ F'.fl.Xa a.val := fun a => by
    rw [← neg_sub]
    exact Submodule.neg_mem _ (hle _ (hin.1 a))
  have hle' : ∀ k, F'.fl.Xa k ≤ F0.Xa k := PI.UnitaryGroupMassFormula.InSRelevantW.xa_le_of hin'
  have hXX : F'.fl.X = F0.X := by
    rw [← PI.UnitaryGroupMassFormula.InSRelevantW.xa_r F'.fl, ← PI.UnitaryGroupMassFormula.InSRelevantW.xa_r F0]
    exact le_antisymm (hle' _) (hle _)
  have hXΛ : ∀ y ∈ Λ, y ∈ F0.X → y ∈ XS D F0 := fun y hy hyX => by
    rw [← hXS]
    exact ⟨hy, hyX⟩
  have hXΛ' : ∀ y ∈ Λ, y ∈ F0.X → y ∈ XS D F'.fl := fun y hy hyX => by
    rw [← hXS']
    refine ⟨hy, ?_⟩
    show y ∈ F'.fl.X
    rw [hXX]
    exact hyX
  have hXSΛ : ∀ y ∈ XS D F0, y ∈ Λ := fun y hy => by
    rw [← hXS] at hy
    exact hy.1
  have hXSΛ' : ∀ y ∈ XS D F'.fl, y ∈ Λ := fun y hy => by
    rw [← hXS'] at hy
    exact hy.1
  have he' : ∀ a, F'.fl.e a ∈ F0.X := fun a => hXX ▸ e_mem_X F'.fl a
  obtain ⟨n, hnisom, hngmap, hne, hnperp⟩ :=
    core (VS D).hT (VS D).herm (VS D).nondeg Λ hlat.fg hlat.span_eq_top hU F0.X (X_iso F0)
      F0.e F'.fl.e (e_mem_X F0) he'
      (fun a x => F0.coefX x a) (fun a x => F'.fl.coefX x a)
      (fun x hx => coef_expand F0 x hx) (fun x hx => coef_expand F'.fl x (hXX ▸ hx))
      (fun a x hx y hy => coef_add F0 a x hx y hy)
      (fun a x hx y hy => coef_add F'.fl a x (hXX ▸ hx) y (hXX ▸ hy))
      (fun a t x hx => coef_smul F0 a t x hx) (fun a t x hx => coef_smul F'.fl a t x (hXX ▸ hx))
      (fun a b => coef_e F0 a b) (fun a b => coef_e F'.fl a b)
      (Jd D)
      (fun a t ht => ⟨hXSΛ _ (smul_e_mem_XS F0 a t ht), hXSΛ' _ (smul_e_mem_XS F'.fl a t ht)⟩)
      (fun x hx hxX a => ⟨(XS_coef F0 x (hXΛ x hx hxX)).2 a, (XS_coef F'.fl x (hXΛ' x hx hxX)).2 a⟩)
      θ hθ
  have hperp : ∀ x ∈ orth (VS D) (Xsp (lf D F0)), n x - x ∈ Xsp (lf D F0) := by
    intro x hx
    refine hnperp x fun y hy => ?_
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    exact hx y hy
  refine ⟨n, ⟨⟨hnisom, hngmap⟩, ?_, hperp⟩, hne, ?_⟩
  · intro j x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      have hi' : i.val < j + 1 := hi
      show n (F0.e i) - F0.e i ∈ F0.Xa j
      rw [hne i]
      exact PI.UnitaryGroupMassFormula.InSRelevantW.xa_mono F0 (Nat.lt_succ_iff.1 hi') (hin.1 i)
    | zero => simp
    | add y w _ _ hy hw =>
      have e : n (y + w) - (y + w) = (n y - y) + (n w - w) := by rw [map_add]; abel
      rw [e]
      exact Submodule.add_mem _ hy hw
    | smul t y _ hy =>
      have e : n (t • y) - t • y = t • (n y - y) := by rw [map_smul, smul_sub]
      rw [e]
      exact Submodule.smul_mem _ t hy
  · have h1 := hperp _ (z_mem_orth (lf D F0))
    have e : n (lf D F0).fl.z - F'.fl.z = (n (lf D F0).fl.z - (lf D F0).fl.z) - (F'.fl.z - (lf D F0).fl.z) := by
      abel
    rw [e]
    exact Submodule.sub_mem _ h1 hin.2

theorem termIdIffInS_of (D : D7) (hθ : TraceOne D) (u u' : D.what₂.Word) : TermIdIffInS D u u' := by
  intro F0 Λ hΛ x _ hin
  exact isIdF_of D hθ F0 Λ hΛ x.1 x.2 hin

end PI.UnitaryGroupMassFormula.IdCellInSW

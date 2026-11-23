import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfC

noncomputable section

open ValuativeRel Matrix

namespace Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V}

theorem coef_zero {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v) {c : ι → E}
    (h0 : ∀ i, H.h (∑ j, c j • v j) (v i) = 0) : c = 0 := by
  obtain ⟨N, -, hNG⟩ := hN
  have hG : H.gram v *ᵥ c = 0 := by
    funext i
    have h := h0 i
    rw [← hL_apply, map_sum] at h
    simp only [map_smul, hL_apply, smul_eq_mul] at h
    simp only [Matrix.mulVec, dotProduct, HermSp.gram, Matrix.of_apply, Pi.zero_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h := congrArg (fun x => N *ᵥ x) hG
  simp only [Matrix.mulVec_mulVec, hNG, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  exact h

theorem linInd_of_gramInv {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v) :
    LinearIndependent E v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := coef_zero hN (c := g) (fun k => by rw [hg]; exact H.h_zero_left _)
  exact congrFun h i

theorem prim_of_gramInv {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v)
    {Λ : Submodule M.L.O V} (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (hv : ∀ i, v i ∈ Λ) : H.Prim Λ v := by
  refine ⟨hv, linInd_of_gramInv hN, fun x hx hxs => ?_⟩
  obtain ⟨c, hc, hw⟩ := decomp hN hI hv hx
  have hw0 : x - ∑ j, c j • v j = 0 := eq_zero_of_orth hN (Submodule.sub_mem _ hxs (comb_mem_span v c)) hw
  rw [sub_eq_zero.1 hw0]
  exact Submodule.sum_mem _ fun j _ =>
    (Submodule.span M.L.O (Set.range v)).smul_mem (⟨c j, hc j⟩ : M.L.O) (Submodule.subset_span ⟨j, rfl⟩)

theorem prim_inr {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] {a : ι₁ → V}
    {b : ι₂ → V} (hN : GramInv H (Sum.elim a b)) {Λ : Submodule M.L.O V}
    (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (hv : ∀ k, Sum.elim a b k ∈ Λ) : H.Prim Λ b := by
  refine ⟨fun j => hv (Sum.inr j), (linInd_of_gramInv hN).comp Sum.inr Sum.inr_injective, fun x hx hxs => ?_⟩
  obtain ⟨c, hc, hw⟩ := decomp hN hI hv hx
  have hsp : Submodule.span E (Set.range b) ≤ Submodule.span E (Set.range (Sum.elim a b)) :=
    Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨Sum.inr j, rfl⟩)
  have hw0 : x - ∑ k, c k • Sum.elim a b k = 0 :=
    eq_zero_of_orth hN (Submodule.sub_mem _ (hsp hxs) (comb_mem_span _ c)) hw
  have hx' : x = ∑ k, c k • Sum.elim a b k := sub_eq_zero.1 hw0
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxs
  have hsum : ∑ k, Sum.elim (0 : ι₁ → E) e k • Sum.elim a b k = x := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]
    exact he
  have hz : ∑ k, (c k - Sum.elim (0 : ι₁ → E) e k) • Sum.elim a b k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [hsum, ← hx', sub_self]
  have hce := Fintype.linearIndependent_iff.1 (linInd_of_gramInv hN) _ hz
  have hl : ∀ i, c (Sum.inl i) = 0 := fun i => by
    have h := hce (Sum.inl i)
    simpa using h
  have hx2 : x = ∑ j, c (Sum.inr j) • b j := by
    conv_lhs => rw [hx']
    rw [Fintype.sum_sum_type]
    simp [hl]
  rw [hx2]
  exact Submodule.sum_mem _ fun j _ =>
    (Submodule.span M.L.O (Set.range b)).smul_mem (⟨c (Sum.inr j), hc _⟩ : M.L.O) (Submodule.subset_span ⟨j, rfl⟩)

end Formalism.MainNotions.S.Loc.HermSp.CohU

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem vP_eq {p : PlF D} (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (hs : (Zd.M p).split = none) : vP Zd p γ F'₂ = Sum.elim (tLoc Zd p γ).f (locF' Zd p F'₂) := by
  unfold vP Formalism.MainNotions.S.Loc.HermSp.MMfam
  rw [hs]
  rfl

variable (u u' F0 what₂)

def CohInt : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ ∀ b, locF' Zd p F'₂ b ∈ lattice₂ D Zd.M p γ.lam}.Finite

def CohDG : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ (IsUnit ((locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1)) ∧
      (locH Zd p).Gdet (tLoc Zd p γ).f (locF' Zd p F'₂) (tLoc Zd p γ).T (tLoc Zd p γ).T' ≠ 0)}.Finite

variable {u u' F0 what₂}

theorem cohGen_of (hInt : CohInt Zd u u' F0 what₂) (hDG : CohDG Zd u u' F0 what₂) (hGood : CohGood Zd u u' F0 what₂) :
    CohGen Zd u u' F0 what₂ := by
  intro hP γ Z F'₂ φ' hH
  refine (((hInt hP γ Z F'₂ φ' hH).union (hDG hP γ Z F'₂ φ' hH)).union
    ((hGood hP γ Z F'₂ φ' hH).union (split_finite Zd))).subset ?_
  intro p hp
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
  obtain ⟨⟨hi, hdg⟩, hN, hs⟩ := hn
  have hsn : (Zd.M p).split = none := Option.not_isSome_iff_eq_none.1 hs
  apply hp
  have T1 := hH.2.2.2 p
  have sd := T1.1.1.1
  have frf := T1.1.1.2.1
  have frf' := T1.1.1.2.2.1
  have hI : ∀ x ∈ lattice₂ D Zd.M p γ.lam, ∀ y ∈ lattice₂ D Zd.M p γ.lam, (locH Zd p).h x y ∈ (Zd.M p).L.O :=
    fun x hx => (sd.2.2 x).1 hx
  have hv' : ∀ k, Sum.elim (tLoc Zd p γ).f (locF' Zd p F'₂) k ∈ lattice₂ D Zd.M p γ.lam := by
    intro k
    cases k with
    | inl a => exact frf.1.1 a
    | inr b => exact hi b
  have hN' := hN
  rw [vP_eq Zd γ F'₂ hsn] at hN'
  have hv : ∀ k, vP Zd p γ F'₂ k ∈ lattice₂ D Zd.M p γ.lam := by
    rw [vP_eq Zd γ F'₂ hsn]
    exact hv'
  have hfr2 : (locH Zd p).IsFrame (lattice₂ D Zd.M p γ.lam) D.R.rS (locF' Zd p F'₂) (tLoc Zd p γ).T' :=
    ⟨Formalism.MainNotions.S.Loc.HermSp.CohU.prim_inr hN' hI hv', T1.2.2.1.1, T1.2.2.1.2, frf'.2.2.2.1, frf'.2.2.2.2⟩
  refine ⟨⟨sd, frf, hfr2, hdg.1, hdg.2, fun g hg => ?_⟩, ?_⟩
  · rw [hsn] at hg
    cases hg
  · exact Formalism.MainNotions.S.Loc.HermSp.CohU.prim_of_gramInv hN hI hv

theorem star_coherence_of_four (hInt : CohInt Zd u u' F0 what₂) (hDG : CohDG Zd u u' F0 what₂) (hLp : CohLp Zd u u' F0 what₂)
    (hGood : CohGood Zd u u' F0 what₂) : CtxP u u' F0 what₂ → StarCoh Zd u u' F0 what₂ :=
  starCoh_of_P'' Zd (cohGen_of Zd hInt hDG hGood) hLp hGood

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

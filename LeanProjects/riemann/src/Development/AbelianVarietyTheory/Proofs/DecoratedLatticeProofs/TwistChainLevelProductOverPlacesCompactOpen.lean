import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocK
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeStabilizerTwistAndLevelAway
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QFinGrp

open GlobalTheory.FinPl

theorem map_ofFn_prod_eq {G M : Type*} [Group G] [Monoid M] (φ : G →* M) :
    ∀ {r : ℕ} (a : Fin r → G) (i : Fin r), (∀ j, j ≠ i → φ (a j) = 1) → φ (List.ofFn a).prod = φ (a i)
  | 0, _, i, _ => i.elim0
  | r + 1, a, i, h => by
    rw [List.ofFn_succ, List.prod_cons, map_mul]
    by_cases hi : i = 0
    · subst hi
      have h1 : φ (List.ofFn fun j : Fin r => a j.succ).prod = 1 := by
        rw [map_list_prod]
        refine List.prod_eq_one fun x hx => ?_
        rw [List.map_ofFn, List.mem_ofFn] at hx
        obtain ⟨j, rfl⟩ := hx
        exact h _ (Fin.succ_ne_zero j)
      rw [h1, mul_one]
    · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi
      rw [h 0 (Fin.succ_ne_zero i').symm, one_mul]
      exact map_ofFn_prod_eq φ (fun j => a j.succ) i' fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

variable {D : D7}

theorem loc_facts {c : Comm D} {v : VCom c} {t : Tup c} (F : QFam v t) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (i : Fin F.r) :
    GlobalTheory.QuotientFiniteLevel.locK F j σ h i ≤ grpAt (c.V (j + 1)) (· ∈ ({(F.Q i).q.v} : Finset (Pl D))) ∧
    IsCompact (GlobalTheory.QuotientFiniteLevel.locK F j σ h i : Set (GA D (c.V (j + 1)))) ∧
    IsOpen {x : grpAt (c.V (j + 1)) (· ∈ ({(F.Q i).q.v} : Finset (Pl D))) |
      (x : GA D (c.V (j + 1))) ∈ GlobalTheory.QuotientFiniteLevel.locK F j σ h i} := by
  have hd : j + 1 + ((F.Q i).s - j) = (F.Q i).s + 1 := by have := (F.Q i).hs; omega
  obtain ⟨hce, hrange, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (F.Q i).k (F.Q i).q (c.V (j + 1))
    ((F.Q i).X (j + 1) ⊕ Fin ((F.Q i).s - j)) ((F.Q i).FY (j + 1) ((F.Q i).s - j) hd)
    ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd) ((F.Q i).gl_loc _ _ hd)
  have hr : ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd).range =
      grpAt (c.V (j + 1)) (· ∈ ({(F.Q i).q.v} : Finset (Pl D))) := by
    rw [hrange]; congr 1; funext p; exact propext Finset.mem_singleton.symm
  obtain ⟨hJo, hJc, -⟩ := (F.Q i).reg.2.2 (j + 1) ((F.Q i).s - j) hd
  refine ⟨?_, ?_, ?_⟩
  · rw [← hr]; intro x hx; obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 hx; exact ⟨g, rfl⟩
  · rw [GlobalTheory.QuotientFiniteLevel.locK, Subgroup.coe_map]; exact hJc.image hce.continuous
  · obtain ⟨U, hU, hUe⟩ := hce.isInducing.isOpen_iff.1 hJo
    convert hU.preimage continuous_subtype_val using 1
    ext ⟨x, hx⟩
    rw [← hr] at hx
    obtain ⟨g, rfl⟩ := hx
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [GlobalTheory.QuotientFiniteLevel.locK, Subgroup.mem_map]
    constructor
    · rintro ⟨g', hg', e⟩
      have : g' ∈ ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd) ⁻¹' U := hUe.symm ▸ hg'
      rw [← e]; exact this
    · intro hU'
      have hg : g ∈ ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd) ⁻¹' U := hU'
      rw [hUe] at hg
      exact ⟨g, hg, rfl⟩

theorem qK_grp : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w →
    ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), GlobalTheory.QuotientFiniteLevel.qK F j σ h ≤ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q) ∧
      IsCompact (GlobalTheory.QuotientFiniteLevel.qK F j σ h : Set (GA D (c.V (j + 1)))) ∧
      IsOpen (((GlobalTheory.QuotientFiniteLevel.qK F j σ h).subgroupOf (GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) : Subgroup _) :
        Set (GlobalTheory.FinPl.grpAt (c.V (j + 1)) (· ∈ w.Q))) := by
  intro D c v t w F hF j σ h
  have hloc := loc_facts F j σ h
  have hv : ∀ i, (F.Q i).q.v ∈ w.Q := fun i => (hF.places _).2 ⟨i, rfl⟩
  have hle : ∀ i, GlobalTheory.QuotientFiniteLevel.locK F j σ h i ≤ grpAt (c.V (j + 1)) (· ∈ w.Q) := fun i => (hloc i).1.trans
    (GlobalTheory.CellLevels.grpAt_le_of_imp _ fun p hp => (Finset.mem_singleton.1 hp) ▸ hv i)
  have hoff : ∀ i i', i ≠ i' →
      GlobalTheory.QuotientFiniteLevel.locK F j σ h i' ≤ grpAt (c.V (j + 1)) (· ∉ ({(F.Q i).q.v} : Finset (Pl D))) := fun i i' hii' =>
    (hloc i').1.trans (GlobalTheory.CellLevels.grpAt_le_of_imp _ fun p hp hp' =>
      hii' (hF.inj ((Finset.mem_singleton.1 hp').symm.trans (Finset.mem_singleton.1 hp))))
  have hcomm : Pairwise fun i i' => ∀ x y : GA D (c.V (j + 1)),
      x ∈ GlobalTheory.QuotientFiniteLevel.locK F j σ h i → y ∈ GlobalTheory.QuotientFiniteLevel.locK F j σ h i' → Commute x y := by
    intro i i' hii' x y hx hy
    exact (GlobalTheory.FinPl.SetCut.grp_split D (c.V (j + 1)) {(F.Q i).q.v}).2.2.2.2.1 x ((hloc i).1 hx) y (hoff i i' hii' hy)
  have hqK : GlobalTheory.QuotientFiniteLevel.qK F j σ h = ⨆ i, GlobalTheory.QuotientFiniteLevel.locK F j σ h i := rfl
  have hQle : GlobalTheory.QuotientFiniteLevel.qK F j σ h ≤ grpAt (c.V (j + 1)) (· ∈ w.Q) := iSup_le hle
  refine ⟨hQle, ?_, ?_⟩
  · have hrange := Subgroup.noncommPiCoprod_range (hcomm := hcomm)
    have hcont : Continuous (Subgroup.noncommPiCoprod hcomm) := by
      have e : ⇑(Subgroup.noncommPiCoprod hcomm) = fun x =>
          ((List.finRange F.r).map fun i => ((x i : GlobalTheory.QuotientFiniteLevel.locK F j σ h i) : GA D (c.V (j + 1)))).prod := by
        funext x
        simp [Subgroup.noncommPiCoprod, MonoidHom.noncommPiCoprod, Finset.noncommProd, List.ofFn_eq_map]
      rw [e]
      exact continuous_list_prod _ fun i _ => continuous_subtype_val.comp (continuous_apply i)
    haveI : ∀ i, CompactSpace (GlobalTheory.QuotientFiniteLevel.locK F j σ h i) := fun i => isCompact_iff_compactSpace.1 (hloc i).2.1
    have : (GlobalTheory.QuotientFiniteLevel.qK F j σ h : Set (GA D (c.V (j + 1)))) = Set.range (Subgroup.noncommPiCoprod hcomm) := by
      rw [hqK, ← hrange, MonoidHom.coe_range]
    rw [this]; exact isCompact_range hcont
  · set V := c.V (j + 1) with hVdef
    set K := GlobalTheory.QuotientFiniteLevel.locK F j σ h with hKdef
    obtain ⟨-, -, hQf, -, -, ⟨eQ, heQ⟩, -⟩ := GlobalTheory.FinPl.SetCut.grp_split D V w.Q
    have hbot : ∀ a, a ∈ grpAt V (· ∈ w.Q) → a ∈ grpAt V (· ∉ w.Q) → a = 1 := by
      intro a h1 h2
      have : eQ (⟨a, h1⟩, 1) = eQ (1, ⟨a, h2⟩) := by
        apply Subtype.ext; rw [heQ, heQ]; simp
      exact congrArg (fun p => (p.1 : GA D V)) (eQ.injective this)
    choose e he using fun i => (GlobalTheory.FinPl.SetCut.grp_split D V {(F.Q i).q.v}).2.2.2.2.2.1
    have he' : ∀ i (z : GfC V), (z : GA D V) = (((e i).symm z).1 : GA D V) * (((e i).symm z).2 : GA D V) := by
      intro i z; rw [← he i, Homeomorph.apply_symm_apply]
    let ι : grpAt V (· ∈ w.Q) → GfC V := fun x => ⟨x.1, hQf x.2⟩
    have hι : Continuous ι := continuous_subtype_val.subtype_mk _
    let U : Set (grpAt V (· ∈ w.Q)) := ⋂ i, {x | ((((e i).symm (ι x)).1 : _) : GA D V) ∈ K i}
    have hUo : IsOpen U := isOpen_iInter_of_finite fun i =>
      (hloc i).2.2.preimage (continuous_fst.comp ((e i).symm.continuous.comp hι))
    have h1U : (1 : grpAt V (· ∈ w.Q)) ∈ U := by
      refine Set.mem_iInter.2 fun i => ?_
      have : (e i).symm (ι 1) = 1 := by
        rw [Homeomorph.symm_apply_eq]; apply Subtype.ext; rw [he]; simp [ι]
      show ((((e i).symm (ι 1)).1 : _) : GA D V) ∈ K i
      rw [this]; exact (K i).one_mem
    have hprj : ∀ i, ∀ b ∈ grpAt V (· ∉ ({(F.Q i).q.v} : Finset (Pl D))),
        GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v b = 1 := fun i b hb =>
      ((GlobalTheory.FinPl.KOpen.mem_grpAt_iff V _ b).1 hb).2 _ (by simp)
    have hUsub : U ⊆ (((GlobalTheory.QuotientFiniteLevel.qK F j σ h).subgroupOf (grpAt V (· ∈ w.Q)) : Subgroup _) : Set _) := by
      intro x hx
      have hx' := Set.mem_iInter.1 hx
      let a : Fin F.r → GA D V := fun i => (((e i).symm (ι x)).1 : GA D V)
      have ha : ∀ i, a i ∈ K i := fun i => hx' i
      have hp : (List.ofFn a).prod ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h := by
        refine Subgroup.list_prod_mem _ fun y hy => ?_
        rw [List.mem_ofFn] at hy
        obtain ⟨i, rfl⟩ := hy
        exact (le_iSup K i) (ha i)
      have hy1 : ∀ i, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v ((x : GA D V) * ((List.ofFn a).prod)⁻¹) = 1 := by
        intro i
        have hxi : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (x : GA D V) =
            GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (a i) := by
          have := he' i (ι x)
          change (x : GA D V) = a i * _ at this
          rw [this, map_mul, hprj i _ (((e i).symm (ι x)).2).2, mul_one]
        have hpi : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (List.ofFn a).prod =
            GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (a i) :=
          map_ofFn_prod_eq _ a i fun j' hj' => hprj i _ (hoff i j' (Ne.symm hj') (ha j'))
        rw [map_mul, map_inv, hxi, hpi, mul_inv_cancel]
      have hyQ : (x : GA D V) * ((List.ofFn a).prod)⁻¹ ∈ grpAt V (· ∈ w.Q) :=
        mul_mem x.2 (inv_mem (hQle hp))
      have hyN : (x : GA D V) * ((List.ofFn a).prod)⁻¹ ∈ grpAt V (· ∉ w.Q) := by
        refine (GlobalTheory.FinPl.KOpen.mem_grpAt_iff V _ _).2 ⟨hQf hyQ, fun p hp' => ?_⟩
        obtain ⟨i, rfl⟩ := (hF.places p).1 (not_not.1 hp')
        exact hy1 i
      have hxp : (x : GA D V) = (List.ofFn a).prod := mul_inv_eq_one.1 (hbot _ hyQ hyN)
      show (x : GA D V) ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h
      rw [hxp]; exact hp
    exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hUo.mem_nhds h1U) hUsub)

end GlobalTheory.QFinGrp
end

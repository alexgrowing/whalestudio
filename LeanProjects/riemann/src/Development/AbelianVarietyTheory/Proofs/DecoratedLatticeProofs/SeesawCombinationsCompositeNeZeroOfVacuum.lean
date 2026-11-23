import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorLocalHomLatticeMemSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedSplitPlaceOfIsHalfConjSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVecExistsUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.CombNonzero

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}

theorem comb_o_ne_zero (hψ : IsStdChar D ψ (-1)) (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') (L : LocPl ψ S T M M')
    {h : WO S T → ℂ} (hv : GlobalTheory.FinPl.Vac ψ S T M M' (· = L.q.v) h) (h0 : h ≠ 0) : comb ψ S T L.o h ≠ 0 := by
  classical
  set p : Place D L.k := ofSplit L.q with hp
  obtain ⟨ε, hε, hs⟩ := L.q.above
  obtain ⟨s1, s2, -⟩ := L.q.split
  have hsc := GlobalTheory.PlaceModelSum.isSplitIdem_cA L.q.split
  have c1 : cA D L.q.e * cA D L.q.e = cA D L.q.e := by rw [← map_mul, s1]
  have he1 : algebraMap (AF D.host.F) (AE D) ε * L.q.e = L.q.e := by
    rw [← hs]; linear_combination s1 + s2
  have he2 : algebraMap (AF D.host.F) (AE D) ε * cA D L.q.e = cA D L.q.e := by
    rw [← hs]; linear_combination c1 + s2

  have fix : ∀ a : AE D, IsSplitIdem D a → algebraMap (AF D.host.F) (AE D) ε * a = a →
      ∀ u ∈ (latO S T (M : Set _) (M' : Set _) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T a, heisO ψ S T u h = h := by
    intro a ha hea u hu
    have hm := GlobalTheory.PlaceModel.idem_smul_mem hε ha.1 hea (AddSubgroup.mem_inf.1 hu).1
    have hua : a • u = u := (GlobalTheory.PlaceModel.mem_half S T).1 (AddSubgroup.mem_inf.1 hu).2
    rw [hua] at hm
    exact hv.2.2 a ha u (AddSubgroup.mem_inf.1 hm).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).2 (AddSubgroup.mem_inf.1 hm).2)
  have hO : GlobalTheory.PlaceModelSum.IsOrthSum L.q.e :=
    ⟨Unit, {()}, fun _ => L.q.e, fun _ _ => L.q.split, fun _ _ _ _ hne => absurd rfl hne, by simp⟩
  obtain ⟨T', hT'⟩ := GlobalTheory.FlatVecExist.exists_model_of_fix hψ hM hM' hO s2 (fix _ L.q.split he1) (fix _ hsc he2)
  let Tm := T'.comp (GlobalTheory.LocMod.Witness.ext p L.FS L.FT)
  have hTm : p.IsModel ψ L.FS L.FT Tm := by
    refine ⟨fun Φ => ?_, fun x Φ Φ' e => ?_, fun y hy Φ Φ' e => ?_⟩
    · exact GlobalTheory.SchrTheta.isTheta_placeModel D ψ hψ S T M M' hM hM' L.q.e s1 (GlobalTheory.PlaceModelSum.infPart_split L.q.split)
        h hv.1 T' hT' _ (GlobalTheory.LocMod.Witness.ext_sb p L.FS L.FT hM hM' Φ)
    · refine Eq.trans (congrArg T' ?_) (hT'.trans _ (GlobalTheory.LocMod.Witness.ext_sb p L.FS L.FT hM hM' Φ) _
        (GlobalTheory.LocMod.Witness.up_half p L.FS L.FT x))
      funext t
      rw [GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.down_add,
        GlobalTheory.LocMod.Witness.down_up, e]
      exact if_congr (GlobalTheory.LocMod.Witness.half_add (GlobalTheory.LocMod.Witness.up_half p L.FS L.FT x)).symm rfl rfl
    · refine Eq.trans (congrArg T' ?_) (hT'.modul _ (GlobalTheory.LocMod.Witness.ext_sb p L.FS L.FT hM hM' Φ) _ hy)
      funext t
      rw [GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.ext_apply, e]
      split_ifs with ht
      · rw [GlobalTheory.LocMod.Witness.up_down p L.FS L.FT ht]
      · rw [mul_zero]
  let Φ₀ : SB (Matrix L.Y L.Y' L.k) := ⟨_, GlobalTheory.LatIndSB.indicator_latO_mem_SB D ψ S T M M' hM hM' L⟩
  have hΦ₀ : Tm Φ₀ = h := by
    have e1 : GlobalTheory.LocMod.Witness.ext p L.FS L.FT Φ₀ = (1 : ℂ) • halfInd L.q.e (latO S T (M : Set _) (M' : Set _) fun _ => True) := by
      funext t
      rw [one_smul, GlobalTheory.LocMod.Witness.ext_apply, halfInd]
      by_cases ht : IsHalf p.e t
      · rw [if_pos ht]
        show Set.indicator {x | p.up L.FS L.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = L.q.v)} (fun _ => (1 : ℂ)) (p.down L.FS L.FT t) = _
        rw [Set.indicator_apply]
        refine if_congr ?_ rfl rfl
        change p.up L.FS L.FT (p.down L.FS L.FT t) ∈ latO S T (M : Set _) (M' : Set _) (· = L.q.v) ↔ _
        rw [GlobalTheory.LocMod.Witness.up_down p L.FS L.FT ht, and_iff_left (show IsHalf L.q.e t from ht)]
        refine ⟨fun hm => GlobalTheory.PlaceModel.latO_le_top _ hm, fun hm => ?_⟩
        have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε s1 he1 hm).1
        have h3 : L.q.e • t = t := (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 ht)
        rw [h3] at h2
        exact h2
      · rw [if_neg ht, if_neg fun hh => ht hh.2]
    change T' (GlobalTheory.LocMod.Witness.ext p L.FS L.FT Φ₀) = h
    rw [e1]
    exact hT'.vac
  obtain ⟨O, hO, hO1⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := L.k) (Y := L.Y) (Y' := L.Y')
  have hOne : Tm O = comb ψ S T L.o (Tm Φ₀) := L.o_is Tm hTm Φ₀ O hO rfl
  intro hc
  rw [hΦ₀, hc] at hOne
  have hO0 : O ≠ 0 := by rintro rfl; simp at hO1
  have hz := (GlobalTheory.LocModU.localModel_uniq_transport_exist D L.k p L.Y L.Y' S T L.FS L.FT ψ hψ).1 Tm ((0 : ℂ) • Tm) hTm
    (GlobalTheory.LocMod.Witness.isModel_smul p hTm 0) O hO0 (by rw [hOne]; simp)
  apply h0
  rw [← hΦ₀, hz]
  simp

theorem vac_mono (hψ : IsStdChar D ψ (-1)) (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M')
    {P Q : GlobalTheory.FinPl.Pl D → Prop} (hQP : ∀ v, Q v → P v) {f : WO S T → ℂ}
    (hf : GlobalTheory.FinPl.Vac ψ S T M M' P f) : GlobalTheory.FinPl.Vac ψ S T M M' Q f := by
  have hiff := (GlobalTheory.DisjComb.main D ψ hψ S T Q (fun v => P v ∧ ¬ Q v) (fun v hq hp => hp.2 hq)).2.2.2.2 M M' f hM hM'
  have e : (fun v => Q v ∨ (P v ∧ ¬ Q v)) = P := by
    funext v
    apply propext
    constructor
    · rintro (hq | hq)
      · exact hQP v hq
      · exact hq.1
    · intro hp
      by_cases hq : Q v
      · exact Or.inl hq
      · exact Or.inr ⟨hp, hq⟩
  rw [e] at hiff
  exact (hiff.1 hf).1

theorem fold_vac (hψ : IsStdChar D ψ (-1)) {n : ℕ} (Lp : Fin n → LocPl ψ S T M M') (P : GlobalTheory.FinPl.Pl D → Prop)
    (l : List (Fin n)) (hl : ∀ i ∈ l, ¬ P (Lp i).q.v) (g : WO S T → ℂ) (hg : GlobalTheory.FinPl.Vac ψ S T M M' P g) :
    GlobalTheory.FinPl.Vac ψ S T M M' P (l.foldr (fun i g' => comb ψ S T (Lp i).o g') g) := by
  induction l with
  | nil => exact hg
  | cons i l ih =>
    rw [List.foldr_cons]
    have hc : GlobalTheory.FinPl.CombAt (· = (Lp i).q.v) (Lp i).o := fun u hu =>
      GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (Lp i).q u ((Lp i).o_at u hu)
    refine ((GlobalTheory.DisjComb.main D ψ hψ S T (· = (Lp i).q.v) P
      (fun v hv hp => hl i List.mem_cons_self (hv ▸ hp))).2.1 _ hc).2 M M' _ ?_
    exact ih fun j hj => hl j (List.mem_cons_of_mem _ hj)

theorem fold_ne_zero (hψ : IsStdChar D ψ (-1)) (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') {n : ℕ}
    (Lp : Fin n → LocPl ψ S T M M') (hinj : Function.Injective fun i => (Lp i).q.v) (l : List (Fin n)) (hnd : l.Nodup)
    (g : WO S T → ℂ) (hg : GlobalTheory.FinPl.Vac ψ S T M M' (fun v => ∃ i ∈ l, (Lp i).q.v = v) g) (g0 : g ≠ 0) :
    l.foldr (fun i g' => comb ψ S T (Lp i).o g') g ≠ 0 := by
  induction l with
  | nil => exact g0
  | cons i l ih =>
    rw [List.foldr_cons]
    obtain ⟨hi, hnd'⟩ := List.nodup_cons.1 hnd
    refine comb_o_ne_zero hψ hM hM' (Lp i) ?_ (ih hnd' (vac_mono hψ hM hM'
      (fun v ⟨j, hj, e⟩ => ⟨j, List.mem_cons_of_mem _ hj, e⟩) hg))
    refine fold_vac hψ Lp _ l (fun j hj e => hi ?_) g (vac_mono hψ hM hM' (fun v hv => ⟨i, List.mem_cons_self, hv.symm⟩) hg)
    have : j = i := hinj e
    exact this ▸ hj

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (Lp : Fin n → LocPl ψ S T M M'), (Function.Injective fun i => (Lp i).q.v) → ∀ g, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) g → g ≠ 0 → (List.finRange n).foldr (fun i g' => comb ψ S T (Lp i).o g') g ≠ 0 := by
  intro D ψ hψ S T M M' hM hM' n Lp hinj g hg g0
  exact fold_ne_zero hψ hM hM' Lp hinj _ (List.nodup_finRange n) g (vac_mono hψ hM hM' (fun _ _ => trivial) hg) g0

end GlobalTheory.CombNonzero

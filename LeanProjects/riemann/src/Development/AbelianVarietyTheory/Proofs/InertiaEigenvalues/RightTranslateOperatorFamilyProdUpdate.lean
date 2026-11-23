import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialLevelCosetRepresentativeMemLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eu

theorem prod_toList_insert_comm {ι M : Type} [Monoid M] [DecidableEq ι] (s : Finset ι) (v : ι) (hv : v ∉ s) (f : ι → M)
    (hc : ∀ a b, a ≠ b → Commute (f a) (f b)) :
    ((insert v s).toList.map f).prod = (s.toList.map f).prod * f v := by
  have hp : ((insert v s).toList.map f).Perm ((v :: s.toList).map f) := (Finset.toList_insert hv).map f
  have hpw : ((insert v s).toList.map f).Pairwise Commute := by
    rw [List.pairwise_map]
    exact (Finset.nodup_toList _).imp fun h => hc _ _ h
  rw [hp.prod_eq' hpw, List.map_cons, List.prod_cons]
  refine (Commute.list_prod_right _ _ fun y hy => ?_).eq
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
  refine hc _ _ ?_
  rintro rfl
  exact hv (Finset.mem_toList.1 hw)

theorem fid_orth (D : D7) {v w : HeightOneSpectrum (𝓞 D.host.F)} (h : v ≠ w) : fid D v * fid D w = 0 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  unfold fid
  split_ifs with h1 h2
  · obtain ⟨ε, hε, e⟩ := h1.choose_spec
    obtain ⟨ε', hε', e'⟩ := h2.choose_spec
    rw [e, e']
    exact GlobalTheory.IdemSupport.place_orth hΦ hε hε' h
  · exact mul_zero _
  · exact zero_mul _
  · exact zero_mul _

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem rep_mem_locSet {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) :
    rep x ∈ locSet R i v := (Quotient.out x).2

theorem rep_commute {R : RealDat D A Ks} {i : Fin D.R.m} {v w : HeightOneSpectrum (𝓞 D.host.F)} (h : v ≠ w)
    (x : LX R i v) (y : LX R i w) : Commute (rep x) (rep y) :=
  GlobalTheory.IdemSupport.commute_of_suppF _ (fid_orth D h) (rep_mem_locSet x).2 (rep_mem_locSet y).2

theorem famProd_mem_GfC (R : RealDat D A Ks) (i : Fin D.R.m) (F : ∀ v, LX R i v) :
    famProd R i F ∈ GfC (Wc D i) := by
  unfold famProd
  split_ifs with h
  · refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy
    exact (rep_mem_locSet _).1
  · exact Subgroup.one_mem _

theorem bop_congr (R : RealDat D A Ks) (i : Fin D.R.m) {γ γ' : GA D (Wc D i)}
    (h : trPair R i γ = trPair R i γ') : Bop R i γ = Bop R i γ' := by
  unfold Bop
  rw [h]

theorem famProd_update_of_ne (R : RealDat D A Ks) (i : Fin D.R.m) (F : ∀ v, LX R i v)
    (hF : {w | F w ≠ lx0 R i w}.Finite) (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : F v = lx0 R i v) (x : LX R i v)
    (hx : x ≠ lx0 R i v) : famProd R i (Function.update F v x) = famProd R i F * rep x := by
  have hs : {w | Function.update F v x w ≠ lx0 R i w} = insert v {w | F w ≠ lx0 R i w} := by
    ext w
    by_cases hw : w = v
    · subst hw
      simp [hx]
    · simp [hw]
  have hF' : {w | Function.update F v x w ≠ lx0 R i w}.Finite := by
    rw [hs]; exact hF.insert v
  have ht : hF'.toFinset = insert v hF.toFinset := by
    ext w
    rw [Set.Finite.mem_toFinset, hs, Finset.mem_insert, Set.Finite.mem_toFinset, Set.mem_insert_iff]
  have hnv : v ∉ hF.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact fun h => h hv
  unfold famProd
  rw [dif_pos hF, dif_pos hF', ht,
    prod_toList_insert_comm hF.toFinset v hnv (fun w => rep (Function.update F v x w))
      (fun a b h => rep_commute h _ _)]
  congr 1
  · congr 1
    refine List.map_congr_left fun w hw => ?_
    have : w ≠ v := by
      rintro rfl
      exact hnv (Finset.mem_toList.1 hw)
    rw [Function.update_of_ne this]
  · simp only [Function.update_self]

theorem bop_famProd_update : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i, TransLaws R i → ∀ (F : ∀ v, Eu.LX R i v), {w | F w ≠ Eu.lx0 R i w}.Finite → ∀ v, F v = Eu.lx0 R i v → Eu.famProd R i F ∈ GfC (Wc D i) ∧ ∀ x : Eu.LX R i v, Eu.Bop R i (Eu.famProd R i (Function.update F v x)) = Eu.Bop R i (Eu.famProd R i F * Eu.rep x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hTL F hF v hv
  refine ⟨famProd_mem_GfC R i F, fun x => ?_⟩
  by_cases hx : x = lx0 R i v
  · have hu : Function.update F v x = F := by
      rw [hx, ← hv]; exact Function.update_eq_self v F
    rw [hu]
    refine bop_congr R i (funext fun a => funext fun b => ?_)
    have := hTL.2.2.2.1 _ (famProd_mem_GfC R i F) 1 (Subgroup.one_mem _) (rep x) (hx ▸ trivial_level_coset_representative_mem_level R i v) a b
    rw [one_mul] at this
    exact this.symm
  · rw [famProd_update_of_ne R i F hF v hv x hx]

end GlobalTheory.RawLift.Eu

end

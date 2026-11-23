import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumSplitPlaceCombinationMulLocalStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocComb

open GlobalTheory.ExportSeries

theorem ratDatum_insert (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : PP ∉ P)
    (hs : SplitSet (insert PP P)) (c : WO S T →₀ ℂ) (Ξl : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ)
    (hloc : GlobalTheory.LocMod.IsLocFac D ψ S T PP c Ξl)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hSd : IsSelfDualC S ΛS) (hTd : IsSelfDualC T ΛT) (hSi : (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank)
    (hTi : (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank) (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ)
    (f₀ f : WO S T → ℂ) (h0 : IsThetaFunO ψ S T f₀) (h1 : IsLatVac (heisO ψ S T) (stdHom S T) f₀)
    (hf : IsRatDatum ψ S T (idem P) Ξ f₀ f) :
    IsRatDatum ψ S T (idem (insert PP P)) (fun γ => Ξ γ * Ξl γ) f₀ (comb ψ S T c f) := by
  obtain ⟨k, _, _, _, _, p, Y, Y', _, _, _, _, FS, FT, Ξk, hd, hat, hint, hSB, hcomb, hΞ⟩ := hloc
  have hP : SplitSet P := hs.mono (Finset.subset_insert _ _)
  have he : idem P + p.e = idem (insert PP P) := by
    rw [idem, idem, Finset.sum_insert hPP, idemAt_eq hat, add_comm]
  have hs' : IsIdemSum (idem P + p.e) (@insert _ _ (@Finset.instInsert _ (Classical.decEq _)) PP P) := by
    rw [he]
    convert hs.isIdemSum
  have key := GlobalTheory.T.rationalDatum_splitPlace_combination_mul_local D k p ψ hψ hd S T Y Y' FS FT P PP (idem P) hPP hat hP.isIdemSum hs' hint ΛS ΛT hSd hTd hSi hTi Ξ Ξk hSB c
    hcomb f₀ f h0 h1 hf
  rw [he] at key
  have hfun : (fun γ => Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) = fun γ => Ξ γ * Ξl γ :=
    funext fun γ => by rw [hΞ γ]
  rwa [hfun] at key

theorem ratDatum_list (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (P₀ Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ) (PPn : Fin n → Formalism.L2.DIV.Pl D.host.E)
    (hinj : Function.Injective PPn) (hQ : ∀ i, PPn i ∈ Q) (hdis : Disjoint P₀ Q) (hs : SplitSet (P₀ ∪ Q))
    (c : Fin n → WO S T →₀ ℂ) (Ξl : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ)
    (hloc : ∀ i, GlobalTheory.LocMod.IsLocFac D ψ S T (PPn i) (c i) (Ξl i))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hSd : IsSelfDualC S ΛS) (hTd : IsSelfDualC T ΛT) (hSi : (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank)
    (hTi : (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank)
    (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (f₀ f : WO S T → ℂ) (h0 : IsThetaFunO ψ S T f₀)
    (h1 : IsLatVac (heisO ψ S T) (stdHom S T) f₀) (hf : IsRatDatum ψ S T (idem P₀) Ξ f₀ f) :
    ∀ L : List (Fin n), L.Nodup →
      IsRatDatum ψ S T (idem (P₀ ∪ (L.map PPn).toFinset)) (fun γ => Ξ γ * (L.map fun i => Ξl i γ).prod) f₀
        (L.foldr (fun i g => comb ψ S T (c i) g) f) := by
  intro L
  induction L with
  | nil =>
    intro _
    have : (fun γ => Ξ γ * (([] : List (Fin n)).map fun i => Ξl i γ).prod) = Ξ := funext fun γ => by simp
    simpa [this] using hf
  | cons i L ih =>
    intro hnd
    rw [List.nodup_cons] at hnd
    have hsub : P₀ ∪ ((i :: L).map PPn).toFinset ⊆ P₀ ∪ Q := by
      intro x hx
      rcases Finset.mem_union.1 hx with h | h
      · exact Finset.mem_union_left _ h
      · obtain ⟨j, -, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact Finset.mem_union_right _ (hQ j)
    have hins : P₀ ∪ ((i :: L).map PPn).toFinset = insert (PPn i) (P₀ ∪ (L.map PPn).toFinset) := by
      rw [List.map_cons, List.toFinset_cons, Finset.union_insert]
    have hnot : PPn i ∉ P₀ ∪ (L.map PPn).toFinset := by
      intro h
      rcases Finset.mem_union.1 h with h | h
      · exact Finset.disjoint_left.1 hdis h (hQ i)
      · obtain ⟨j, hj, hji⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact hnd.1 (hinj hji ▸ hj)
    have step := ratDatum_insert D ψ hψ S T _ (PPn i) hnot (hins ▸ hs.mono hsub) (c i) (Ξl i) (hloc i) ΛS ΛT hSd hTd hSi hTi _ f₀ _ h0 h1
      (ih hnd.2)
    rw [← hins] at step
    have hfun : (fun γ => Ξ γ * (L.map fun i => Ξl i γ).prod * Ξl i γ) =
        fun γ => Ξ γ * ((i :: L).map fun i => Ξl i γ).prod := funext fun γ => by
      rw [List.map_cons, List.prod_cons]; ring
    rw [hfun] at step
    simpa only [List.foldr_cons] using step

theorem ratDatum_foldr_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (P₀ Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ) (PPn : Fin n → Formalism.L2.DIV.Pl D.host.E), Function.Injective PPn → (∀ PP, PP ∈ Q ↔ ∃ i, PPn i = PP) → Disjoint P₀ Q → ∀ (c : Fin n → WO S T →₀ ℂ) (Ξl : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ), (∀ i, GlobalTheory.LocMod.IsLocFac D ψ S T (PPn i) (c i) (Ξl i)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank → (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank → ∀ (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (f₀ f : WO S T → ℂ), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → (∀ e₀, IsIdemSum e₀ P₀ → IsRatDatum ψ S T e₀ Ξ f₀ f) → ∀ e, IsIdemSum e (P₀ ∪ Q) → IsRatDatum ψ S T e (fun γ => Ξ γ * ∏ i, Ξl i γ) f₀ ((List.finRange n).foldr (fun i g => comb ψ S T (c i) g) f) := by
  intro D ψ hψ S T P₀ Q n PPn hinj hQ hdis c Ξl hloc ΛS ΛT hSd hTd hSi hTi Ξ f₀ f h0 h1 hrat e he
  have hs : SplitSet (P₀ ∪ Q) := ⟨e, he⟩
  have hQ' : ∀ i, PPn i ∈ Q := fun i => (hQ _).2 ⟨i, rfl⟩
  have hP₀ : SplitSet P₀ := hs.mono Finset.subset_union_left
  have key := ratDatum_list D ψ hψ S T P₀ Q n PPn hinj hQ' hdis hs c Ξl hloc ΛS ΛT hSd hTd hSi hTi Ξ f₀ f h0 h1
    (hrat _ hP₀.isIdemSum) (List.finRange n) (List.nodup_finRange n)
  have hset : ((List.finRange n).map PPn).toFinset = Q := by
    ext x
    simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, true_and]
    exact ⟨fun ⟨i, hi⟩ => (hQ x).2 ⟨i, hi⟩, fun h => (hQ x).1 h⟩
  rw [hset, idem_eq he] at key
  have hfun : (fun γ => Ξ γ * ((List.finRange n).map fun i => Ξl i γ).prod) = fun γ => Ξ γ * ∏ i, Ξl i γ :=
    funext fun γ => by rw [Fin.prod_univ_def]
  rwa [hfun] at key

end GlobalTheory.LocComb
end

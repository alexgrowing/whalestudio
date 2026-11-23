import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergCombinationSplitPlaceDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBExtFunEqHalfInd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteOfPlaces

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocMod ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SeeSaw.LocPlInhab
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem exists_latInd (q : GlobalTheory.FinPl.SplitPt D k) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y)
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') :
    ∃ Φ₀ : SB (Matrix Y Y' k), Φ₀.1 0 = 1 ∧
      Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) := by
  obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem q
  have h1 : {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} =
      (((latO S T M M' fun _ => True).comap (Witness.upH (ofSplit q) FS FT) : AddSubgroup _) : Set (Matrix Y Y' k)) := by
    ext x
    refine ⟨fun h => GlobalTheory.PlaceModel.latO_le_top _ h, fun h => ?_⟩
    have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε q.split.1 heε h).1
    have h3 : q.e • (Witness.upH (ofSplit q) FS FT) x = (ofSplit q).up FS FT x :=
      (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (Witness.up_half (ofSplit q) FS FT x))
    rwa [h3] at h2
  rw [h1]
  have ho := Witness.lat_open (ofSplit q) FS FT hS hT
  have hk := Witness.lat_compact (ofSplit q) FS FT hS hT
  generalize ((latO S T _ _ fun _ => True).comap (Witness.upH (ofSplit q) FS FT) : AddSubgroup _) = A at ho hk
  have hcl : IsClopen (A : Set (Matrix Y Y' k)) := ⟨A.isClosed_of_isOpen ho, ho⟩
  exact ⟨⟨(A : Set (Matrix Y Y' k)).indicator 1, (LocallyConstant.charFn ℂ hcl).isLocallyConstant,
      HasCompactSupport.intro hk fun x hx => Set.indicator_of_notMem hx _⟩, Set.indicator_of_mem A.zero_mem _, rfl⟩

theorem exists_locPl {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (q : GlobalTheory.FinPl.SplitPt D k) (hq : q.UnitAA)
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (Φ : SB (Matrix Y Y' k))
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') :
    ∃ L : LocPl ψ S T M M', L.q.v = q.v ∧ L.q.e = q.e ∧
      ∀ x, prodDat (fun _ : Fin 1 => L) ((ofSplit q).up FS FT x) = Φ.1 x := by
  obtain ⟨O, hO, h0⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  obtain ⟨Φ₀, h1, h2⟩ := exists_latInd q FS FT hS hT
  obtain ⟨e, e1, e2⟩ := GlobalTheory.LocComb.exists_comb D k (ofSplit q) Y Y' S T FS FT ψ hψ O Φ (by rintro rfl; simp at h0)
  obtain ⟨o, o1, o2⟩ := GlobalTheory.LocComb.exists_comb D k (ofSplit q) Y Y' S T FS FT ψ hψ Φ₀ O (by rintro rfl; simp at h1)
  refine ⟨⟨k, q, hq, Y, Y', FS, FT, Φ, e, ⟨e1, fun Tm hT a b ha hb => ?_⟩, o, o1, fun Tm hT a b hb ha => ?_⟩, rfl, rfl, fun x => ?_⟩
  · obtain rfl : a = O := Subtype.ext (ha.trans hO.symm)
    obtain rfl : b = Φ := Subtype.ext hb
    exact e2 Tm hT
  · obtain rfl : b = O := Subtype.ext (hb.trans hO.symm)
    obtain rfl : a = Φ₀ := Subtype.ext (ha.trans h2.symm)
    exact o2 Tm hT
  · unfold prodDat
    rw [Fin.sum_univ_one, Fin.prod_univ_one]
    exact (if_pos (Witness.up_half (ofSplit q) FS FT x)).trans (congrArg Φ.1 (Witness.down_up (ofSplit q) FS FT x))

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem exists_locPl_off {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') (Z : Finset (GlobalTheory.FinPl.Pl D)) :
    ∃ L : LocPl ψ S T M M', L.q.v ∉ Z ∧ ∃ x, prodDat (fun _ : Fin 1 => L) x = 1 := by
  obtain ⟨v, p, hv, hP⟩ := GlobalTheory.FinPl.PlacesTest.exists_one_place D Z
  obtain ⟨O, -, h0⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Fv D.host.F v) (Y := Fin T.rank) (Y' := Fin S.rank)
  obtain ⟨L, h1, -, h2⟩ := exists_locPl hψ p (hP.unit ()) (Frame.ofGL 1) (Frame.ofGL 1) O hS hT
  have hpv : v = p.v := by obtain ⟨_, h⟩ := (hP.mem v).1 rfl; first | exact h | exact h.symm
  exact ⟨L, by rw [h1, ← hpv]; exact hv, _, (h2 0).trans h0⟩

end GlobalTheory.SeeSaw.LocPlInhab
end

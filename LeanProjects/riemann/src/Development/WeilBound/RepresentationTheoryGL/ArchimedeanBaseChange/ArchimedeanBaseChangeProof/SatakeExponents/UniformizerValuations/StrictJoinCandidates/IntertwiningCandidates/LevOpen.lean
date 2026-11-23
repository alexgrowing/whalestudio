import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.IwahoriPairLeMaximal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PPositions

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcB.G8
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.LevelOpenness

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Rd.LevOC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def LOk (d : LocData E n) : Prop :=
  ∀ a ≤ n, ∀ w ∈ d.S₀ ∪ d.Bad, IsOpen (d.L a w : Set (GLw a w × GLw (n - a) w))

theorem LOk_of_ok (d : LocData E n) (hd : d.Ok) : LOk d := fun a ha w hw => (L_open_le d hd a ha w hw).1

theorem lev_open (d : LocData E n) (hd : LOk d) (a : ℕ) (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev a w : Set (GLw a w × GLw (n - a) w)) := by
  unfold LocData.lev
  split_ifs with h1 h2
  · exact iwahori_pair_isOpen a (n - a) w
  · exact hd a ha w h2
  · exact maximal_pair_isOpen a (n - a) w

theorem lev₂_open (d : LocData E n) (hd : LOk d) (a : ℕ) (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev₂ a w : Set (GLw a w × GLw (n - a) w)) := by
  unfold LocData.lev₂
  split_ifs with h2
  · exact hd a ha w h2
  · exact maximal_pair_isOpen a (n - a) w

theorem C_open (d : LocData E n) (hd : LOk d) (a : ℕ) (ha : a ≤ n) {S : Set (Pl E)} (i : Slot S) :
    IsOpen (C d a i) := by
  rcases i with w | w
  · exact lev_open d hd a ha w.1
  · exact lev₂_open d hd a ha w.1

theorem gSet_open' (hSl : Slots) {Sec : Set (Pl E)} (hS : IsSection Sec) (d : LocData E n) (hd : LOk d) (a : ℕ)
    (ha : a ≤ n) : IsOpen (gSet Sec d a) := by
  have hSl' := hSl E a (n - a) Sec hS
  obtain ⟨hKo1, -⟩ := GlobalTheory.T.finite_kernel_compact_open E a
  obtain ⟨hKo2, -⟩ := GlobalTheory.T.finite_kernel_compact_open E (n - a)
  set U : Set (Hf E a (n - a)) := (((Kf E a).prod (Kf E (n - a)) : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a)))
    with hU
  have hUo : IsOpen U := by
    rw [hU, Subgroup.coe_prod]
    exact hKo1.prod hKo2
  have hF := (Filter.eventually_cofinite.1 (C_cof d a (S := Sec)))
  set V : Set (Hf E a (n - a)) := U ∩ ⋂ i ∈ {i : Slot Sec | ¬ C d a i = (K2 a (n - a) i.pl : Set _)},
    (i.cp a (n - a)) ⁻¹' C d a i with hV
  have hVo : IsOpen V :=
    hUo.inter (hF.isOpen_biInter fun i _ => (C_open d hd a ha i).preimage (hSl'.2.1 i))
  have h1V : (1 : Hf E a (n - a)) ∈ V := by
    refine ⟨one_mem _, Set.mem_iInter₂.2 fun i _ => ?_⟩
    have h1 : (1 : Hf E a (n - a)) ∈ gSet Sec d a := (levSub Sec d a).one_mem
    rw [gSet_eq] at h1
    exact h1 i
  have hVsub : V ⊆ gSet Sec d a := by
    intro x hx
    rw [gSet_eq]
    intro i
    by_cases hi : C d a i = (K2 a (n - a) i.pl : Set _)
    · rw [hi]
      exact (hSl'.2.2.2.2.2.1 x).1 hx.1 i
    · exact Set.mem_iInter₂.1 hx.2 i hi
  exact Subgroup.isOpen_of_mem_nhds (levSub Sec d a) (g := 1) (Filter.mem_of_superset (hVo.mem_nhds h1V) hVsub)

theorem g₁_open (hSl : Slots) {Sec : Set (Pl E)} (hS : IsSection Sec) (d : LocData E n) (hd : LOk d) (a : ℕ)
    (ha : a ≤ n) : IsOpen (g₁ Sec d a : Set (GL (Fin a) (Af E))) := by
  rw [g₁_coe]
  exact (gSet_open' hSl hS d hd a ha).preimage (continuous_id.prodMk continuous_const)

theorem g₂_open (hSl : Slots) {Sec : Set (Pl E)} (hS : IsSection Sec) (d : LocData E n) (hd : LOk d) (a : ℕ)
    (ha : a ≤ n) : IsOpen (g₂ Sec d a : Set (GL (Fin (n - a)) (Af E))) := by
  rw [g₂_coe]
  exact (gSet_open' hSl hS d hd a ha).preimage (continuous_const.prodMk continuous_id)

theorem loc_LOk {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S : Finset (Pl E)} (F₀ : Frame0 hR π S)
    (T' : Finset (Pl E)) c e b : LOk (F₀.loc T' c e b) :=
  fun a ha w hw => LOk_of_ok F₀.d₀ F₀.ok₀ a ha w hw

end PositivityTheory.Rg.BcB.F.FX.Bo.LevelOpenness

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F

theorem LevOpen_holds : LevOpen := by
  intro hR E _ _ _ n π S F₀ T' c e b a ha
  have hd := LevelOpenness.loc_LOk F₀ T' c e b
  exact ⟨LevelOpenness.g₁_open slots F₀.hSec _ hd a ha, LevelOpenness.g₂_open slots F₀.hSec _ hd a ha⟩

end PositivityTheory.Rg.BcB.F.FX.Bo

end

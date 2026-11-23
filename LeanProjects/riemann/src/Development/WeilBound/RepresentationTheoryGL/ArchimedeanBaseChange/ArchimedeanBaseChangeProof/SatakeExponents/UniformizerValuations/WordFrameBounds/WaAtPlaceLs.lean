import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.Lt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.UnitaryAdjointHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PuSphHecke
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingWordOf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace PositivityTheory.Rg.BcB.F.B3

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

namespace PWordId2

section Frame

variable {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T)
omit [IsCMField E] in
theorem wa_v_one {w : Pl E} (u : (w.adicCompletion E)ˣ)
    (h : ordL (u : w.adicCompletion E) = 0) : Valued.v (u : w.adicCompletion E) = 1 := by
  have h0 : Valued.v (u : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).2 u.ne_zero
  unfold ordL at h
  rw [dif_neg h0, neg_eq_zero] at h
  have h1 : WithZero.unzero h0 = 1 := by simpa using congrArg Multiplicative.ofAdd h
  rw [← WithZero.coe_unzero h0, h1]
  rfl

theorem wa_mu_loc (w : Pl E) : F.d.μ w = F₀.μ.loc w := by
  rw [F.same.2.2.1]; exact F₀.μloc w

theorem wa_mu_unit (w : Pl E) (u : (w.adicCompletion E)ˣ) : ‖((F.d.μ w u : ℂˣ) : ℂ)‖ = 1 := by
  rw [wa_mu_loc]; exact F₀.hμ.1 _

theorem wa_good (w : Pl E) (hw : w ∈ F₀.Sec) (hB : w ∉ F.d.B) (hs : IsSplitAt w) : F.d.Good w := by
  simp only [LocData.B, Finset.mem_union, not_or] at hB
  obtain ⟨⟨hT, hS0⟩, hBad⟩ := hB
  have hun := (F₀.good w hw (by rw [← F.same.1]; exact hS0) (by rw [← F.same.2.1]; exact hBad)).2
  exact ⟨hs, hT, hS0, hBad, fun u hu => by rw [wa_mu_loc]; exact hun u (wa_v_one u hu)⟩

theorem wa_notin_B {w : Pl E} (hw : F.d.Good w) : w ∉ F.d.B := by
  obtain ⟨-, hT, hS, hB, -⟩ := hw
  simp [LocData.B, hT, hS, hB]

theorem wa_ug_ok (x : F.Γ) : (F.ug x).Ok F₀.Sec F.d.B := by
  rcases x with _ | x | x
  · exact trivial
  · exact trivial
  · exact ⟨x.1.2.1, wa_notin_B F x.1.2.2, GlobalTheory.CompanionTheory.MatchWord.isHecke_hU F.d F.ok (if_pos x.1.2.2.1) x.2.1⟩

theorem wa_ul_ok (hE : GlobalTheory.BCT.Unr E) (ws : List (List (F.Γ × Bool))) : ∀ x ∈ lU F ws, x.Ok F₀.Sec F.d.B := by
  intro x hx
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  unfold ul
  split_ifs
  · exact (U.unitary_adjoint_holds E hE n F₀.Sec F₀.lam F.d.KU F.fam F.d.B (F.d.gU F.m) F.R F.levOff _ (wa_ug_ok F p.1)).1
  · exact wa_ug_ok F p.1

theorem wa_sph_map (L : List (F.Γ × Bool)) (w : Pl E) :
    U.UGen.sph (L.map (ul F)) w = MLM.wordUS F.d w (atPlace F.d w (L.map (lt F))) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨x, b⟩ := p
    rcases x with u | y | y
    · have hul : ul F (Sum.inl u, b) = Sum.inl (if b then starRingEnd ℂ 1 else 1) := by
        cases b <;> rfl
      rw [List.map_cons, hul, U.pu_sph_inl, ih]; rfl
    · have hul : ul F (Sum.inr (Sum.inl y), b) = Sum.inl (if b then starRingEnd ℂ (F.dval y) else F.dval y) := by
        cases b <;> rfl
      rw [List.map_cons, hul, U.pu_sph_inl, ih]; rfl
    · have hul : ul F (Sum.inr (Sum.inr y), b) =
          Sum.inr ⟨y.1.1, if b then lstar (F.d.hU y.1.1 y.2.1) else F.d.hU y.1.1 y.2.1⟩ := by
        cases b <;> rfl
      rw [List.map_cons, hul]
      by_cases hw : y.1.1 = w
      · subst hw
        rw [U.pu_sph_self, ih]
        have e : atPlace F.d y.1.1 (lt F (Sum.inr (Sum.inr y), b) :: L.map (lt F)) =
            (y.2.1, y.2.2, b) :: atPlace F.d y.1.1 (L.map (lt F)) := by simp [atPlace, lt]
        rw [List.map_cons, e]
        cases b <;> rfl
      · rw [U.pu_sph_ne _ _ _ _ hw, ih]
        have e : atPlace F.d w (lt F (Sum.inr (Sum.inr y), b) :: L.map (lt F)) = atPlace F.d w (L.map (lt F)) := by
          simp [atPlace, lt, hw]
        rw [List.map_cons, e]

theorem wa_atPlace_ls (ws : List (List (F.Γ × Bool))) (w : Pl E) :
    atPlace F.d w (ls F ws) = atPlace F.d w (ws.flatten.map (lt F)) := by
  induction ws with
  | nil => rfl
  | cons v ws ih =>
    have e1 : ls F (v :: ws) = List.replicate F.m (Sum.inl ()) ++ (v.map (lt F) ++ ls F ws) := by
      simp [ls]
    have e2 : atPlace F.d w (List.replicate F.m (Sum.inl () : LL F.d)) = [] := by
      induction F.m with
      | zero => rfl
      | succ k ihk => simp [List.replicate_succ, atPlace] at ihk ⊢
    rw [e1, List.flatten_cons, List.map_append]
    simp only [atPlace, List.filterMap_append] at ih e2 ⊢
    rw [e2, ih, List.nil_append]

theorem count_ls (ws : List (List (F.Γ × Bool))) : (ls F ws).countP Sum.isLeft = F.m * ws.length := by
  induction ws with
  | nil => simp [ls]
  | cons v ws ih =>
    have e1 : ls F (v :: ws) = List.replicate F.m (Sum.inl ()) ++ (v.map (lt F) ++ ls F ws) := by
      simp [ls]
    have h2 : (v.map (lt F)).countP Sum.isLeft = 0 := by
      rw [List.countP_eq_zero]
      intro a ha
      obtain ⟨⟨x, b⟩, -, rfl⟩ := List.mem_map.1 ha
      rcases x with _ | _ | _ <;> simp [lt]
    rw [e1, List.countP_append, List.countP_append, ih, h2, List.countP_replicate, List.length_cons]
    simp [Sum.isLeft]
    ring

theorem sph_eq (ws : List (List (F.Γ × Bool))) (w : Pl E) :
    U.UGen.sph (lU F ws) w = MLM.wordUS F.d w (atPlace F.d w (ls F ws)) := by
  rw [wa_atPlace_ls, lU, wa_sph_map]

theorem lm (hE : GlobalTheory.BCT.Unr E) (h' : LocMatch) (ws : List (List (F.Γ × Bool))) (hws : ws ≠ []) :
    (∀ w ∈ F.d.B, IsHecke (F.d.KU w) (F.d.gU F.m w)) ∧
    (∃ w ∈ F₀.Sec, ∀ y, U.fam F.d.B F.d.KU (F.d.gU F.m) ws.length (lU F ws) w y ≠ 0 → y.1.val.charpoly.Separable) ∧
    ∀ a ≤ n, (IsTestP ((prodL F.d (ls F ws) a).tr F.d.P F.d.one) ∧ IsTestP (prodL F.d (ls F ws) a).t ∧
      IsTestP (seen ((prodL F.d (ls F ws) a).tr F.d.P F.d.one) (prodL F.d (ls F ws) a).t) ∧
      ∀ w ∈ F₀.Sec, Match n a (n - a) w (F.d.μ w) (U.fam F.d.B F.d.KU (F.d.gU F.m) ws.length (lU F ws) w)
        (seen ((prodL F.d (ls F ws) a).tr F.d.P F.d.one) (prodL F.d (ls F ws) a).t w)) ∧
      ∃ w ∈ F₀.Sec, ¬ IsSplitAt w ∧ RegAt2 a (n - a) w ((prodL F.d (ls F ws) a).tr F.d.P F.d.one w) := by
  have hk1 : 1 ≤ ws.length := List.length_pos_iff.2 hws
  exact h' E hE n F.d F.ok F.mok F₀.Sec F₀.hSec F.levOff F.T_ne (wa_mu_unit F) (fun w hw hB hs => wa_good F w hw hB hs)
    (ls F ws) F.m ws.length F.m_pos hk1 (count_ls F ws) (lU F ws) (fun w _ => sph_eq F ws w)

theorem trace_eq (hE : GlobalTheory.BCT.Unr E) (h' : LocMatch) (ws : List (List (F.Γ × Bool))) (hws : ws ≠ []) :
    GlobalTheory.BCT.IsTest (KL n) F.d.KU (U.fam F.d.B F.d.KU (F.d.gU F.m) ws.length (lU F ws)) ∧
    LinearMap.trace ℂ _ ((F.R.u ^ ws.length * ((lU F ws).map F.R.op).prod :
      EuclideanSpace ℂ (Fin F.R.d) →L[ℂ] EuclideanSpace ℂ (Fin F.R.d)) :
      EuclideanSpace ℂ (Fin F.R.d) →ₗ[ℂ] EuclideanSpace ℂ (Fin F.R.d)) =
    U.UGen.sc (lU F ws) * geomU F₀.Sec F₀.lam (U.fam F.d.B F.d.KU (F.d.gU F.m) ws.length (lU F ws)) := by
  obtain ⟨hHk, hSep, -⟩ := lm F hE h' ws hws
  obtain ⟨hTest, htr⟩ := U.unitary_words_holds E hE n F₀.Sec F₀.lam F.d.KU F.fam F.d.B (F.d.gU F.m) F.R F.levOff hHk ws.length
    (lU F ws) (wa_ul_ok F hE ws)
  exact ⟨hTest, htr hSep⟩

end Frame

end PWordId2

end PositivityTheory.Rg.BcB.F.B3

end

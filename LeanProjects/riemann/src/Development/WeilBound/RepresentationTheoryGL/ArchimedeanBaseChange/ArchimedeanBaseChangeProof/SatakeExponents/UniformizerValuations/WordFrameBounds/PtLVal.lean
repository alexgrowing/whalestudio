import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.Lt

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

theorem wd_val {B : Block E} (w : List (BGen B)) (t₀ : PT B) (hw : ∀ g ∈ w, BGen.Ok g) (h0 : t₀.Ok)
    (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b) :
    (BGen.wd w t₀).Ok ∧ (BGen.wd w t₀).val χa χb = (w.map (Sum.elim (fun _ => 1) fun s => s.val χa χb)).prod * t₀.val χa χb := by
  induction w with
  | nil => simp [BGen.wd, h0]
  | cons g w ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun g hg => hw g (List.mem_cons_of_mem _ hg))
    rcases g with c | s
    · refine ⟨ih1, ?_⟩
      simp only [BGen.wd, List.foldr_cons, Sum.elim_inl, List.map_cons, List.prod_cons, one_mul] at ih2 ⊢
      exact ih2
    · have hs : s.Ok := hw (Sum.inr s) List.mem_cons_self
      have h := BlockFiniteConvolution.blkOp₀ E B s (BGen.wd w t₀) hs ih1
      refine ⟨h.2.2.1, ?_⟩
      have e : BGen.wd (Sum.inr s :: w) t₀ = s.mul (BGen.wd w t₀) := rfl
      rw [e, h.2.2.2.2.2.2.1, ih2, List.map_cons, List.prod_cons, Sum.elim_inr, mul_assoc]

variable {F} in
theorem pt_val (i : F₀.C.ι) (wa wb : InfinitePlace E → List (Bool × ℕ)) (ψ : Matrix F.κ F.κ (Hf E (F₀.C.a i) (n - F₀.C.a i) → ℂ)) (r : ℝ) :
    ((F₀.A i).pt wa wb ψ r).val (F₀.A i).χa (F₀.A i).χb =
      (∏ v, zVal (wa v) ((F₀.A i).χa v)) * ∏ v, zVal (wb v) ((F₀.A i).χb v) := by
  have h1 : (∏ v, coshT (F₀.A i).bump (cas ((F₀.A i).χa v))) * ∏ v, coshT (F₀.A i).bump (cas ((F₀.A i).χb v)) = 1 :=
    (F₀.A i).one
  simp only [PT.val, valA, Arch.pt, Arch.valW, Finset.prod_mul_distrib]
  rw [mul_mul_mul_comm, h1, mul_one]

theorem hermA (i : F₀.C.ι) (v : InfinitePlace E) : IsHerm ((F₀.A i).χa v) := FBL.hermInf_holds _ _
theorem hermB (i : F₀.C.ι) (v : InfinitePlace E) : IsHerm ((F₀.A i).χb v) := FBL.hermInf_holds _ _

theorem ptL_val (i : F₀.C.ι) (L : LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) :
    (F.ptL i L).val (F₀.A i).χa (F₀.A i).χb = 1 := by
  simp [RunFrame.ptL, pt_val, zVal]

theorem t₂_val (i : F₀.C.ι) : (F.t₂ i).val (F₀.A i).χa (F₀.A i).χb = 1 := by
  simp [RunFrame.t₂, pt_val, zVal]

theorem letter (i : F₀.C.ι) (x : F.Γ) :
    Sum.elim id (fun _ => 1) (F.g x i) * Sum.elim (fun _ => 1) (fun s : PT (F.B i) => s.val (F₀.A i).χa (F₀.A i).χb) (F.g x i) =
      Sum.elim id (fun _ => 1) (F.ug x) := by
  rcases x with u | x | x
  · simp [RunFrame.g, RunFrame.ug, RunFrame.t₀, ptL_val]
  · simp only [RunFrame.g, RunFrame.ug]
    split_ifs with h
    · subst h
      obtain ⟨j, v, s, m, side⟩ := x
      simp only [Sum.elim_inr, Sum.elim_inl, id, one_mul, RunFrame.tD, pt_val, RunFrame.dval]
      cases side <;> simp [zVal] <;>
        rw [Finset.prod_eq_single v (fun b _ hb => by simp [hb]) (by simp)] <;> simp
    · simp
  · simp [RunFrame.g, RunFrame.ug, ptL_val]

theorem val_eq (hF : F.Struct) (i : F₀.C.ι) (ws : List (List (F.Γ × Bool))) :
    BGen.sc (ws.map (bw F i)).flatten * (tw F i ws).val (F₀.A i).χa (F₀.A i).χb = U.UGen.sc (lU F ws) := by
  have hadj : ∀ g : BGen (F.B i), g.Ok → g.adj.Ok ∧
      Sum.elim id (fun _ => 1) g.adj * Sum.elim (fun _ => 1) (fun s : PT (F.B i) => s.val (F₀.A i).χa (F₀.A i).χb) g.adj =
        starRingEnd ℂ (Sum.elim id (fun _ => 1) g * Sum.elim (fun _ => 1) (fun s : PT (F.B i) => s.val (F₀.A i).χa (F₀.A i).χb) g) := by
    rintro (c | t) hg
    · exact ⟨trivial, by simp [BGen.adj]⟩
    · have h := BlockFiniteConvolution.blkOp₀ E (F.B i) t t hg hg
      refine ⟨h.2.2.2.2.1, ?_⟩
      simp only [BGen.adj, Sum.map_inr, Sum.elim_inr, one_mul]
      exact h.2.2.2.2.2.2.2 _ _ (hermA i) (hermB i)
  have hl : ∀ p : F.Γ × Bool, (gl F i p).Ok ∧
      Sum.elim id (fun _ => 1) (gl F i p) * Sum.elim (fun _ => 1) (fun s : PT (F.B i) => s.val (F₀.A i).χa (F₀.A i).χb) (gl F i p) =
        Sum.elim id (fun _ => 1) (ul F p) := by
    rintro ⟨x, b⟩
    have hx := letter F i x
    cases b
    · simp only [gl, ul, Bool.false_eq_true, if_false]; exact ⟨hF.ok x i, hx⟩
    · simp only [gl, ul, if_true]
      refine ⟨(hadj _ (hF.ok x i)).1, ?_⟩
      rw [(hadj _ (hF.ok x i)).2, hx]
      rcases F.ug x with c | u <;> simp [U.UGen.adj]
  have hok : ∀ g ∈ Sum.inr (F.t₁ i) :: (ws.map (bw F i)).flatten, BGen.Ok g := by
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact (hF.tok i).1
    · obtain ⟨l, hl', hg⟩ := List.mem_flatten.1 hg
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hl'
      rcases List.mem_append.1 hg with hg | hg
      · rw [List.eq_of_mem_replicate hg]; exact hF.βok i
      · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hg
        exact (hl p).1
  obtain ⟨-, hv⟩ := wd_val _ (F.t₂ i) hok (hF.tok i).2 (F₀.A i).χa (F₀.A i).χb
  rw [tw, hv, t₂_val, List.map_cons, List.prod_cons, Sum.elim_inr, RunFrame.t₁, ptL_val, one_mul, mul_one,
    BGen.sc, ← List.prod_map_mul, U.UGen.sc, lU, List.map_map]
  clear hok hv
  induction ws with
  | nil => simp
  | cons w ws ih =>
    rw [List.map_cons, List.flatten_cons, List.map_append, List.prod_append, ih, List.flatten_cons, List.map_append,
      List.prod_append]
    congr 1
    simp only [bw, List.map_append, List.prod_append, List.map_replicate, List.map_map]
    rw [List.prod_replicate, Sum.elim_inr, Sum.elim_inr, RunFrame.β, ptL_val]
    simp only [mul_one, one_pow, one_mul]
    congr 1
    exact List.map_congr_left fun p _ => (hl p).2

theorem lef_pt (i : F₀.C.ι) (t : PT (F.B i)) (ht : t.Ok) (v : InfinitePlace E) :
    LefAt (F₀.C.νC (F₀.C.a i)) (F₀.C.νC (n - F₀.C.a i)) (F₀.C.l₁ i v) (F₀.C.l₂ i v)
      (t.va v ((F₀.A i).χa v) * t.vb v ((F₀.A i).χb v)) (t.arch (F₀.A i).Ta (F₀.A i).Tb v) := by
  exact (F₀.A i).lef v _ _ _ _ t.T (ht.ka v) (ht.kb v)

end Frame

end PWordId2

end PositivityTheory.Rg.BcB.F.B3

end

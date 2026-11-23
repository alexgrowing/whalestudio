import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FlatLevel

variable {D : D7}

theorem prod_diagonal_block_dets_eq_lower_block_det {κ : Type} [CommRing κ] {r t j n : ℕ} (hn : n = r + j * t) {g : GL (Fin n) κ}
    (hg : g ∈ blockTri (blkOf r t)) :
    ∏ c ∈ Finset.range j, dBlk (blkOf r t) (c + 1) g = dBlk (blk2 r) 1 g := by
  classical
  have hg2 : g ∈ blockTri (blk2 r) := blockTri_blkOf_le r t hg
  set M : Matrix (Fin n) (Fin n) κ := (g : Matrix (Fin n) (Fin n) κ) with hM
  have sq : ∀ (b : Fin n → ℕ) (c : ℕ), g ∈ blockTri b → ((dBlk b c g : κˣ) : κ) = (M.toSquareBlock b c).det := by
    intro b c h; rw [diag_block_det_val c h]; rfl
  have emp : ∀ (b : Fin n → ℕ) (c : ℕ), c ∉ Finset.univ.image b → (M.toSquareBlock b c).det = 1 := by
    intro b c hc
    haveI : IsEmpty {a : Fin n // b a = c} := ⟨fun a => hc (Finset.mem_image.2 ⟨a.1, Finset.mem_univ _, a.2⟩)⟩
    exact Matrix.det_isEmpty
  have hdet : ∀ (b : Fin n → ℕ) (N : ℕ), (∀ a, b a < N) → M.BlockTriangular b →
      M.det = ∏ c ∈ Finset.range N, (M.toSquareBlock b c).det := by
    intro b N hb hB
    rw [hB.det]
    refine Finset.prod_subset (fun c hc => ?_) (fun c _ hc => emp b c hc)
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hc
    exact Finset.mem_range.2 (hb a)
  have h1 := hdet (blkOf r t) (j + 1) (fun a => by
      unfold blkOf
      split_ifs with h
      · omega
      · have ha : a.val - r < j * t := by have := a.2; omega
        have ht : 0 < t := by
          rcases Nat.eq_zero_or_pos t with h0 | h0
          · simp [h0] at ha
          · exact h0
        have : (a.val - r) / t < j := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact ha)
        omega) hg
  have h2 := hdet (blk2 r) 2 (fun a => by unfold blk2; split_ifs <;> omega) hg2
  rw [Finset.prod_range_succ'] at h1
  rw [Finset.prod_range_succ', Finset.prod_range_one] at h2
  have h0 : (M.toSquareBlock (blkOf r t) 0).det = (M.toSquareBlock (blk2 r) 0).det := by
    rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight (p := fun a : Fin n => blk2 r a = 0)
      (q := fun a : Fin n => blkOf r t a = 0) (fun a => by unfold blk2 blkOf; split_ifs <;> simp_all))]
    rfl
  have hu : IsUnit (M.toSquareBlock (blk2 r) 0).det := by rw [← sq _ 0 hg2]; exact Units.isUnit _
  apply Units.ext
  rw [Units.coe_prod, sq _ 1 hg2]
  rw [Finset.prod_congr rfl (fun c _ => sq _ (c + 1) hg)]
  rw [h0] at h1
  exact hu.mul_right_cancel (h1.symm.trans h2)

end GlobalTheory.FlatLevel

namespace GlobalTheory.FlatLevel

variable {D : D7}

theorem multT_le {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) {J J' : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) : MultT θ M J χ ≤ MultT θ M J' χ' :=
  Submodule.map_mono (Submodule.span_mono fun X hX =>
    ⟨hX.aut, hX.cusp, fun v k hk g => (h k hk).2 ▸ hX.lev v k (h k hk).1 g, hX.equiv, hX.cont⟩)

open Classical in

theorem lev_flat_le (c : Com D) (w : Twist D) (hw : w.Is c) (j : ℕ) {n : ℕ} (hn : n = D.R.r + j * D.R.t)
    (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (Lev.EAf D)) (hr hr' : D.R.r ≤ n)
    (x : GL (Fin n) (Lev.EAf D))
    (hx : x ∈ lev D.sp.cm J β (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B)) :
    x ∈ lev D.sp.cm J β (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B) ∧
      levFn β (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B) x =
        levFn β (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B) x := by
  obtain ⟨hp, hP⟩ := mem_lev.1 hx
  obtain ⟨hUA, hSt, h3, -⟩ := mem_parLev.1 hp
  have h3' : ∀ PP ∈ c.Pg, redFn β PP x ∈ blockTri (blkOf D.R.r D.R.t) := h3
  have hP' : (fun PP : c.Pg => upperLeftBlock hr (redFn β PP.1 x)) ∈ c.P.H := hP
  have hone := (hw.grp _).1 hP'
  have hPg : ∀ PP ∈ w.Pg, PP ∈ c.Pg := fun PP h => hw.union ▸ Finset.mem_union_left _ h
  have hQ : ∀ PP ∈ w.Q, PP ∈ c.Pg := fun PP h => hw.union ▸ Finset.mem_union_right _ h
  refine ⟨mem_lev.2 ⟨mem_parLev.2 ⟨hUA, hSt, fun PP h => h3' PP (hPg PP h),
    fun PP h => blockTri_blkOf_le _ _ (h3' PP (hQ PP h))⟩, ?_⟩, ?_⟩
  · show _ ∈ (⊥ : Subgroup (G0 w.Pg D.R.r))
    refine Subgroup.mem_bot.2 (funext fun PP => ?_)
    exact hone ⟨PP.1, hPg PP.1 PP.2⟩ PP.2
  · unfold levFn
    have e1 : ext1 (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B).P.H
        (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B).P.chi
        (rTup β (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B) x) = 1 := by
      show ext1 c.P.H c.P.chi _ = 1
      unfold ext1
      split_ifs
      · rw [hw.chr]; rfl
      · rfl
    have e2 : ext1 (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B).P.H
        (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B).P.chi
        (rTup β (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B) x) = 1 := by
      show ext1 (LevelP.triv w.Pg D.R.r ℂ).H (LevelP.triv w.Pg D.R.r ℂ).chi _ = 1
      unfold ext1
      split_ifs
      · rfl
      · rfl
    rw [e1, e2]
    show 1 * (∏ PP ∈ c.Pg, ∏ c' ∈ Finset.range j, c.chi (c' + 1) PP (dBlk (blkOf D.R.r D.R.t) (c' + 1) (redFn β PP x))) *
        ∏ PP ∈ (∅ : Finset (Pl D.host.E)), (w.ξ PP)⁻¹ (dBlk (blk2 D.R.r) 1 (redFn β PP x)) =
      1 * (∏ PP ∈ w.Pg, ∏ c' ∈ Finset.range j, w.chi (c' + 1) PP (dBlk (blkOf D.R.r D.R.t) (c' + 1) (redFn β PP x))) *
        ∏ PP ∈ w.Q, (w.ξ PP)⁻¹ (dBlk (blk2 D.R.r) 1 (redFn β PP x))
    rw [Finset.prod_empty, mul_one, one_mul, one_mul, hw.union, Finset.prod_union hw.disj]
    congr 1
    · refine Finset.prod_congr rfl fun PP hP => Finset.prod_congr rfl fun c' _ => ?_
      rw [hw.chiPg (c' + 1) PP hP]
    · refine Finset.prod_congr rfl fun PP hP => ?_
      simp_rw [hw.chiQ _ PP hP]
      rw [← map_prod, prod_diagonal_block_dets_eq_lower_block_det hn (h3' PP (hQ PP hP))]

open Classical in

theorem flatLe : ∀ D : D7, FlatLe D := by
  intro D c w hw j _ s hs hr
  obtain ⟨hr', hL, hflat⟩ := hs
  have hn : s.V.rank = D.R.r + j * D.R.t := hflat.rank
  show MultT c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) ≤
    MultT c.θ s.M (levS s.V s.β (Lev.datY s.V.rank D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B))
      (Lev.levChi s.V s.β (Lev.datY s.V.rank D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B))
  rw [hL]
  refine multT_le c.θ s.M fun k hk => ?_
  obtain ⟨h1, h2⟩ := lev_flat_le c w hw j hn s.V.gram s.β hr hr' _ hk.2
  exact ⟨⟨hk.1, h1⟩, (congrArg (fun u : ℂˣ => (u : ℂ)) h2).symm⟩

end GlobalTheory.FlatLevel

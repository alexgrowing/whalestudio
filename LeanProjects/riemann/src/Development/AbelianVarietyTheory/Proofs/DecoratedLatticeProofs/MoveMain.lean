import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBasePointCarryingLatticeAndFramesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelTestFunctionsAgreeRationalPoints
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionEqOfLocalAgreementStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeEqOfSplitPlaceFrameSpanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RLatMove

theorem card_eq_of_frame {k : Type} [Field k] {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k n Y) : Fintype.card Y = n := by
  apply le_antisymm
  · calc Fintype.card Y = (1 : Matrix Y Y k).rank := Matrix.rank_one.symm
      _ = (F.γ * F.β).rank := by rw [F.γβ]
      _ ≤ F.γ.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin n) := Matrix.rank_le_card_width _
      _ = n := Fintype.card_fin n
  · calc n = Fintype.card (Fin n) := (Fintype.card_fin n).symm
      _ = (1 : Matrix (Fin n) (Fin n) k).rank := Matrix.rank_one.symm
      _ = (F.β * F.γ).rank := by rw [F.βγ]
      _ ≤ F.β.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card Y := Matrix.rank_le_card_width _

def frameGL {k : Type} [Field k] {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k n Y) (B : GL Y k) (σ : Fin n ≃ Y) : GL (Fin n) k where
  val := (F.β * B.val).submatrix id σ
  inv := ((B⁻¹).val * F.γ).submatrix σ id
  val_inv := by
    rw [Matrix.submatrix_mul_equiv (F.β * B.val) ((B⁻¹).val * F.γ) id σ id]
    have : F.β * B.val * ((B⁻¹).val * F.γ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc B.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul, F.βγ]
    rw [this, Matrix.submatrix_id_id]
  inv_val := by
    have h := Matrix.submatrix_mul_equiv ((B⁻¹).val * F.γ) (F.β * B.val) σ (Equiv.refl (Fin n)) σ
    simp only [Equiv.coe_refl] at h
    rw [h]
    have : (B⁻¹).val * F.γ * (F.β * B.val) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one]
    rw [this, Matrix.submatrix_one_equiv]

theorem frameGL_val {k : Type} [Field k] {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k n Y) (B : GL Y k) (σ : Fin n ≃ Y) :
    (frameGL F B σ).val = (F.β * B.val).submatrix id σ := rfl

end GlobalTheory.RLatMove

namespace GlobalTheory.RLatMove

theorem finJ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (hW : PkHyp W) : Finite {PP // PP ∈ (pk W).Pg ∨ QAll W PP} := by
  haveI := hW.fin
  have : {PP | PP ∈ (pk W).Pg ∨ QAll W PP} = ((pk W).Pg : Set _) ∪ ⋃ t, ((pk W).Q t : Set _) := by
    ext PP; simp [QAll]
  have hf : Set.Finite {PP | PP ∈ (pk W).Pg ∨ QAll W PP} := by
    rw [this]; exact (Finset.finite_toSet _).union (Set.finite_iUnion fun t => Finset.finite_toSet _)
  exact hf.to_subtype

end GlobalTheory.RLatMove

namespace GlobalTheory.RLatMove

theorem move_main : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N j)) → ∃ b : ∀ j, GA D (Yc D j), (∀ j, b j ∈ GfC (Yc D j)) ∧ (∀ j, j < D.R.m → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((pk W).ΛY j) (N j) P) ∧ ∀ PP h j c (hc : j + c = (l PP h).s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin ((l PP h).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (l PP h).q) (Yc D j) (b j) ((pk W).βY j) (((FY PP h j c hc).β * (bas PP h j c hc).val).submatrix id fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hz hτ hNT hζ hLT hgP htP hdisj hPre hOrth hbas FY N hN hInt
  classical
  haveI : Finite {PP // PP ∈ (pk W).Pg ∨ QAll W PP} := finJ W hW
  letI : Fintype {PP // PP ∈ (pk W).Pg ∨ QAll W PP} := Fintype.ofFinite _
  have hinj : Function.Injective
      (fun i : {PP // PP ∈ (pk W).Pg ∨ QAll W PP} => (l i.1 i.2).q.v) := by
    intro i i' hii
    apply GlobalTheory.T.level_places_under_injective W hW
    simp only at hii
    rwa [(l i.1 i.2).under, (l i'.1 i'.2).under] at hii
  have key : ∀ j, j < D.R.m → ∃ t ∈ GfC (Yc D j),
      (∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) →
        GlobalTheory.FinPl.Moves (Yc D j) t ((pk W).ΛY j) (N j) P) ∧
      ∀ PP h c (hc : j + c = (l PP h).s + 1),
        ∃ e : Ix (Fin D.R.k ⊕ Fin ((l PP h).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank,
          GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧
          MovedTo (ofSplit (l PP h).q) (Yc D j) t ((pk W).βY j)
            (((FY PP h j c hc).β * (bas PP h j c hc).val).submatrix id
              fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i)) := by
    intro j hj
    have hsj : ∀ PP h, j + ((l PP h).s + 1 - j) = (l PP h).s + 1 := fun PP h => by
      have := (l PP h).hs; omega
    have hE : ∀ PP h, ∃ e : Ix (Fin D.R.k ⊕ Fin ((l PP h).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank,
        GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e := by
      intro PP h
      obtain ⟨eqv, heqv⟩ := GlobalTheory.SymBridge.PhiAgreeProof.zPos_equiv D.R.k ((l PP h).s + 1) D.R.t j
      have hcard := card_eq_of_frame (FY PP h j _ (hsj PP h))
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod] at hcard
      have hr : D.R.k + ((l PP h).s + 1) + j * D.R.t = (Yc D j).rank := by
        rw [← hcard]; have := hsj PP h; omega
      exact ⟨eqv.trans (finCongr hr), fun x => by simp [heqv]⟩
    choose E hEo using hE
    let σ : ∀ PP h, Fin (Yc D j).rank ≃ (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin ((l PP h).s + 1 - j)) :=
      fun PP h => (E PP h).symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) j _ (hsj PP h))
    let M : ∀ i : {PP // PP ∈ (pk W).Pg ∨ QAll W PP}, GL (Fin (Yc D j).rank) (l i.1 i.2).k :=
      fun i => frameGL (FY i.1 i.2 j _ (hsj i.1 i.2)) (bas i.1 i.2 j _ (hsj i.1 i.2)) (σ i.1 i.2)
    have hsd := GlobalTheory.T.self_dual_lattice_frame_chain W hW j hj
    obtain ⟨t, ht, Lt, hLt, hMv, hAgree, hMT⟩ := GlobalTheory.T.exists_base_point_carrying_lattice_and_frames D (Yc D j) ((pk W).ΛY j) (N j) ((pk W).βY j)
      hsd.1 (hN j hj) {PP // PP ∈ (pk W).Pg ∨ QAll W PP} (fun i => (l i.1 i.2).k)
      (fun i => (l i.1 i.2).q) hinj M
    refine ⟨t, ht, ?_, ?_⟩
    · intro P hP
      have hloc : ∀ w, P w → GlobalTheory.FinPl.latV (Yc D j) Lt (· = w) = GlobalTheory.FinPl.latV (Yc D j) (N j) (· = w) := by
        intro w hw
        by_cases hex : ∃ i : {PP // PP ∈ (pk W).Pg ∨ QAll W PP}, (l i.1 i.2).q.v = w
        · obtain ⟨⟨PP, h⟩, rfl⟩ := hex
          have hPg : PP ∉ (pk W).Pg := fun hPg => hP _ hw ((hgP _).2 ⟨PP, hPg, (l PP h).under⟩)
          have hb := hbas PP h hPg j _ (hsj PP h)
          have hm := hMT ⟨PP, h⟩
          have hval : (M ⟨PP, h⟩).val = (FY PP h j _ (hsj PP h)).β.submatrix id (σ PP h) := by
            simp only [M, frameGL_val, hb, Units.val_one, Matrix.mul_one]
          rw [hval] at hm
          exact GlobalTheory.T.selfDual_lattice_eq_of_splitPlace_frame_span (Yc D j) t ((pk W).ΛY j) Lt (N j) ((pk W).βY j) _ (l PP h).q _
            (FY PP h j _ (hsj PP h)) (σ PP h) ht hsd.1 hsd.2 hLt (hN j hj) (hMv _) hm
            (hInt PP h j _ (hsj PP h))
        · push_neg at hex
          exact hAgree w (fun i => (hex i).symm)
      have hEq := GlobalTheory.T.latticeCompletion_eq_of_local_agreement (Yc D j) Lt (N j) P hLt.1 (hN j hj).1 hloc
      have := hMv P
      unfold GlobalTheory.FinPl.Moves at this ⊢
      rwa [← hEq]
    · intro PP h c hc
      obtain rfl : c = (l PP h).s + 1 - j := by omega
      exact ⟨E PP h, hEo PP h, hMT ⟨PP, h⟩⟩
  choose T hT hMovesT hFrT using key
  refine ⟨fun j => if h : j < D.R.m then T j h else 1, ?_, ?_, ?_⟩
  · intro j
    by_cases h : j < D.R.m
    · simp only [dif_pos h]; exact hT j h
    · simp only [dif_neg h]; exact one_mem _
  · intro j hj P hP
    simp only [dif_pos hj]
    exact hMovesT j hj P hP
  · intro PP h j c hc
    have hj : j < D.R.m := by have := (l PP h).hs; omega
    simp only [dif_pos hj]
    exact hFrT j hj PP h c hc

end GlobalTheory.RLatMove

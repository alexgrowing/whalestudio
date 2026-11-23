import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqLatFrameOfIsSDFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointComponentMemSpanOfLatticeGenerators
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopReadOfTrueQ
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoeLatFrameOfEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_mem_latV_iff (q : SplitPt D k) (S : HSp D) (L : Lat S)
    (hL : (L : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank) (w : Fin S.rank → k) :
    (fun i => q.sec (w i)) ∈ latV S L (· = q.v) ↔ ∀ i, w i ∈ 𝒪[k] := by
  classical
  have hmem : ∀ x : Fin S.rank → D.host.E, x ∈ L ↔ ∀ i, IsIntegral ℤ (x i) := fun x => by
    rw [← SetLike.mem_coe, hL]; rfl
  have hsingle : ∀ i : Fin S.rank, (Pi.single i (1 : D.host.E) : Fin S.rank → D.host.E) ∈ L := fun i =>
    (hmem _).2 fun j => by
      by_cases h : j = i
      · subst h; simpa using isIntegral_one
      · simpa [Pi.single_apply, h] using isIntegral_zero
  let G : Finset (Fin S.rank → D.host.E) := Finset.univ.image fun i => Pi.single i 1
  have hGL : ∀ x ∈ (G : Set (Fin S.rank → D.host.E)), x ∈ L := by
    intro x hx
    simp only [G, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hsingle i
  have hG : Submodule.span (𝓞 D.host.E) (G : Set (Fin S.rank → D.host.E)) = L := by
    apply le_antisymm
    · rw [Submodule.span_le]; exact hGL
    · intro x hx
      have hi := (hmem x).1 hx
      have e : x = ∑ i, (⟨x i, hi i⟩ : 𝓞 D.host.E) • (Pi.single i 1 : Fin S.rank → D.host.E) := by
        funext j
        rw [Finset.sum_apply, Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
        simp [Algebra.smul_def]
      rw [e]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp [G]))
  constructor
  · intro h
    have h1 := FullLatFrame.pr_mem_span q G hG h
    simp only [q.pr_sec] at h1
    have h2 : ∀ z ∈ Submodule.span 𝒪[k] (FullLatFrame.aux₃ q '' (G : Set (Fin S.rank → D.host.E))), ∀ i, z i ∈ 𝒪[k] := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        intro i
        exact FullLatFrame.pr_int_mem q ⟨x i, (hmem x).1 (hGL x hx) i⟩
      | zero => intro i; exact zero_mem _
      | add x y _ _ hx hy => intro i; exact add_mem (hx i) (hy i)
      | smul a x _ hx => intro i; exact mul_mem a.2 (hx i)
    exact h2 _ h1
  · intro h
    have e : w = ∑ i, (⟨w i, h i⟩ : 𝒪[k]) • FullLatFrame.aux₃ q (S := S) (Pi.single i 1) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j (fun b _ hb => by simp [FullLatFrame.aux₃, Pi.single_apply, Ne.symm hb]) (by simp)]
      simp [FullLatFrame.aux₃]
      change _ = w j * 1
      rw [mul_one]
    rw [← FullLatFrame.mem_latW, e]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rw [FullLatFrame.mem_latW]
    exact GlobalTheory.FinPl.FrameLat.sec_inc_mem (hsingle i)

theorem intIn_stdFr (q : SplitPt D k) (S : HSp D) (L : Lat S)
    (hL : (L : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank) {Y : Type} [Fintype Y] [DecidableEq Y]
    (e : Y ≃ Fin S.rank) : IntIn q S (stdFr k e) L := by
  intro y
  rw [sec_mem_latV_iff q S L hL]
  have h : (stdFr k e).β *ᵥ y = y ∘ e.symm := by
    change (1 : Matrix (Fin S.rank) (Fin S.rank) k).submatrix id e *ᵥ y = _
    have := Matrix.submatrix_mulVec_equiv (1 : Matrix (Fin S.rank) (Fin S.rank) k) y id e
    simpa [Function.comp_def] using this
  rw [h]
  exact ⟨fun h i => h _, fun h a => by simpa using h (e a)⟩

end GlobalTheory.XGeoStd.Frames

namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def diagFr {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (e : Y ≃ Fin N) (d : Y → k) (hd : ∀ y, d y ≠ 0) :
    GlobalTheory.LocMod.Frame k N Y where
  β := (stdFr k e).β * Matrix.diagonal d
  γ := Matrix.diagonal (fun y => (d y)⁻¹) * (stdFr k e).γ
  βγ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal d), Matrix.diagonal_mul_diagonal,
      show (fun y => d y * (d y)⁻¹) = fun _ => (1 : k) from funext fun y => mul_inv_cancel₀ (hd y),
      Matrix.diagonal_one, Matrix.one_mul, (stdFr k e).βγ]
  γβ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (stdFr k e).γ, (stdFr k e).γβ, Matrix.one_mul, Matrix.diagonal_mul_diagonal,
      show (fun y => (d y)⁻¹ * d y) = fun _ => (1 : k) from funext fun y => inv_mul_cancel₀ (hd y), Matrix.diagonal_one]

theorem intIn_diagFr (q : SplitPt D k) (S : HSp D) (L : Lat S)
    (hL : (L : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank) {Y : Type} [Fintype Y] [DecidableEq Y]
    (e : Y ≃ Fin S.rank) (d : Y → k) (hd : ∀ y, d y ≠ 0) (hv : ∀ y, valuation k (d y) = 1) :
    IntIn q S (diagFr e d hd) L := by
  intro y
  have h1 := intIn_stdFr q S L hL e (fun a => d a * y a)
  have h2 : (diagFr e d hd).β *ᵥ y = (stdFr k e).β *ᵥ fun a => d a * y a := by
    change ((stdFr k e).β * Matrix.diagonal d) *ᵥ y = _
    rw [← Matrix.mulVec_mulVec]
    congr 1
    funext a
    exact Matrix.mulVec_diagonal _ _ _
  rw [h2, ← h1]
  refine forall_congr' fun a => ?_
  change valuation k (y a) ≤ 1 ↔ valuation k (d a * y a) ≤ 1
  rw [map_mul, hv, one_mul]

variable {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre}

theorem oTop_iA {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok) (n : ℕ) (h : n = (I.rec7 l Z).R.m) :
    ∀ b a, (oTop l Z hI n h).iA b a = if (a : ℕ) = (b : ℕ) then 1 else 0 := by
  subst h; intro b a; rfl

theorem oTop_iB {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok) (n : ℕ) (h : n = (I.rec7 l Z).R.m) :
    ∀ b a, (oTop l Z hI n h).iB b a = if (I.rec7 l Z).sp.X'.rank = (b : ℕ) then 1 else 0 := by
  subst h; intro b a; rfl

end GlobalTheory.XGeoStd.Frames

namespace GlobalTheory.XGeoStd.Frames

theorem entry_inl {E k : Type} [Field E] [Field k] (f : E → k) (hf0 : f 0 = 0) (hf1 : f 1 = 1) {n N : ℕ} {Y : Type} [Fintype Y]
    [DecidableEq Y] (eT : Y ≃ Fin n) (iA : Matrix (Fin N) (Fin n) E) (hA : ∀ b a, iA b a = if (a : ℕ) = (b : ℕ) then 1 else 0)
    (r : Fin N) (c : Y) (m : Fin N) (hm : (m : ℕ) = eT c) :
    (1 : Matrix (Fin N) (Fin N) k) r m = (iA.map f * (1 : Matrix (Fin n) (Fin n) k).submatrix id eT) r c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (eT c)
    (fun b _ hb => by rw [Matrix.submatrix_apply, id, Matrix.one_apply_ne hb, mul_zero]) (by simp)]
  rw [Matrix.submatrix_apply, id, Matrix.one_apply_eq, mul_one, Matrix.map_apply, hA, Matrix.one_apply]
  by_cases h : (eT c : ℕ) = r
  · rw [if_pos h, hf1, if_pos (Fin.ext (h.symm.trans hm.symm))]
  · rw [if_neg h, hf0, if_neg (fun h' => h (hm.symm.trans (congrArg Fin.val h'.symm)))]

theorem entry_inr {E k : Type} [Field E] [Field k] (f : E → k) (hf0 : f 0 = 0) (hf1 : f 1 = 1) {n N : ℕ}
    (iB : Matrix (Fin N) (Fin 1) E) (hB : ∀ b a, iB b a = if n = (b : ℕ) then 1 else 0) (z : Fin 1 → E) (x : E)
    (hz : ∀ i, z i = x) (r : Fin N) (m : Fin N) (hm : (m : ℕ) = n) :
    (1 : Matrix (Fin N) (Fin N) k) r m * f x = (iB.map f *ᵥ fun i => f (z i)) r := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.map_apply, hB, hz, Matrix.one_apply]
  by_cases h : n = (r : ℕ)
  · rw [if_pos h, hf1, if_pos (Fin.ext (h.symm.trans hm.symm))]
  · rw [if_neg h, hf0, if_neg (fun h' => h (hm.symm.trans (congrArg Fin.val h'.symm)))]

end GlobalTheory.XGeoStd.Frames

namespace GlobalTheory.XGeoStd.Frames

set_option maxHeartbeats 4000000 in

theorem exists_locX_std : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex) (hW : AllTrue W) (u : B.Word) (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (PP : Pl (I.rec7 l Z).host.E) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt q.e PP → q.v = PP.under (𝓞 (I.rec7 l Z).host.F) → q.UnitAA → valuation k ((GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u)) = 1 → ∃ s : LocX (GlobalTheory.XGeoStd.xgeo l Z hW.tr.ok vac u (pk W).ΛX) (pk W).βX PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (s.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos s.FT := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u vac PP k _ _ _ _ _ _ q hidem hunder hunit hval
  have hI := hW.tr.ok
  obtain ⟨hsI, hXsp, hX'sp, -⟩ := hI.spaces
  have hLX : ∀ j, ((GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X j)) : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) =
      GlobalTheory.AdForm.intVec _ _ := fun j => GlobalTheory.AdForm.PinInhab.lat_X hI j
  have hLT : (((pk W).ΛX : GlobalTheory.FinPl.Lat (I.rec7 l Z).sp.X') : Set (Fin (I.rec7 l Z).sp.X'.rank → (I.rec7 l Z).host.E)) =
      GlobalTheory.AdForm.intVec _ _ := by
    rw [GlobalTheory.XGeoStd.eq_latFrame_of_isSDFrame W.Q.charW.base.lev.βX]
    exact GlobalTheory.AdForm.VacStd.coe_latFrame_of_eq _ hsI _ hX'sp
  have hβ : (pk W).βX = 1 := hW.pk.bot.pins.betaStd.2
  have hm := (I.rec7 l Z).R.two_le_m
  obtain ⟨s, hs⟩ : ∃ s, s + 1 + 1 = (I.rec7 l Z).R.m := ⟨(I.rec7 l Z).R.m - 2, by omega⟩
  have rX : ∀ j, j ≤ s + 1 → (I.rec7 l Z).R.k + j + j * (I.rec7 l Z).R.t = ((I.rec7 l Z).sp.X j).rank := by
    intro j hj
    rw [Formalism.L2.Forms.rankN _ j (by omega)]
    show _ = (I.rec7 l Z).R.k + j * ((I.rec7 l Z).R.t + 1)
    ring
  have rT : (I.rec7 l Z).R.k + (s + 1) + (s + 2) * (I.rec7 l Z).R.t = (I.rec7 l Z).sp.X'.rank := by
    rw [Formalism.L2.Forms.rankP, show (I.rec7 l Z).R.N (I.rec7 l Z).R.m = (I.rec7 l Z).R.k + (I.rec7 l Z).R.m * ((I.rec7 l Z).R.t + 1) from rfl,
      ← hs]
    have e : (s + 1 + 1) * ((I.rec7 l Z).R.t + 1) = (s + 2) * (I.rec7 l Z).R.t + (s + 1) + 1 := by ring
    rw [e]
    omega
  have rM : (I.rec7 l Z).sp.X'.rank + 1 = ((I.rec7 l Z).sp.X (s + 1 + 1)).rank := by
    rw [hs]; exact GlobalTheory.AdForm.LiveModel.rk_top _

  set κ := (I.rec7 l Z).R.k
  set τ := (I.rec7 l Z).R.t
  let eX : ∀ j (hj : j ≤ s + 1), XIx (Fin κ) (Fin τ) j ≃ Fin ((I.rec7 l Z).sp.X j).rank := fun j hj =>
    (GlobalTheory.Fam.Inhab.blockOrd κ τ j j).trans (finCongr (rX j hj))
  have oX : ∀ j hj, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos (eX j hj) := fun j hj a => by
    simpa [eX] using GlobalTheory.Fam.Inhab.isOrd_xPos κ τ j a
  let eT : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ≃ Fin (I.rec7 l Z).sp.X'.rank :=
    (GlobalTheory.Fam.Inhab.blockOrd κ τ (s + 1) (s + 2)).trans (finCongr rT)
  have oT : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eT := fun a => by
    simpa [eT] using GlobalTheory.Fam.Inhab.isOrd_zPos κ τ (s + 1) (s + 2) a
  let eM : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ⊕ Unit ≃ Fin ((I.rec7 l Z).sp.X (s + 1 + 1)).rank :=
    ((Equiv.sumCongr eT (finOneEquiv.symm)).trans finSumFinEquiv).trans (finCongr rM)
  have eM_l : ∀ a, (eM (Sum.inl a) : ℕ) = eT a := fun a => by simp [eM]
  have eM_r : (eM (Sum.inr ()) : ℕ) = (I.rec7 l Z).sp.X'.rank := by simp [eM]
  set π := (GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u) with hπ
  have hπ0 : π ≠ 0 := fun h0 => by rw [h0, map_zero] at hval; exact zero_ne_one hval
  let dM : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ⊕ Unit → k := Sum.elim (fun _ => 1) fun _ => π
  have hd0 : ∀ y, dM y ≠ 0 := by rintro (a | a) <;> simp [dM, hπ0]
  have hdv : ∀ y, valuation k (dM y) = 1 := by rintro (a | a) <;> simp [dM, hval]
  refine ⟨{ k := k, q := q, idem := hidem, under := hunder, unit := hunit, s := s, hs := hs,
             FX := fun j hj => GlobalTheory.Fam.Inhab.stdFr k (eX j hj), FT := GlobalTheory.Fam.Inhab.stdFr k eT, FM := diagFr eM dM hd0,
             last := ?_, latX := ?_, latM := ?_, latT := ?_, frameTop := ?_ },
    fun j hj => GlobalTheory.Fam.Inhab.isStdFr_stdFr (oX j hj), GlobalTheory.Fam.Inhab.isStdFr_stdFr oT⟩
  · have hpr1 : (GlobalTheory.LocMod.ofSplit q).pr (1 : (I.rec7 l Z).host.E) = 1 := by simp [GlobalTheory.LocMod.Place.pr]
    have hpr0 : (GlobalTheory.LocMod.ofSplit q).pr (0 : (I.rec7 l Z).host.E) = 0 := by simp [GlobalTheory.LocMod.Place.pr]
    ext r c
    rcases c with c | c
    · rw [Matrix.fromCols_apply_inl]
      change ((GlobalTheory.Fam.Inhab.stdFr k eM).β * Matrix.diagonal dM) r (Sum.inl c) = _
      rw [Matrix.mul_diagonal]
      simp only [dM, Sum.elim_inl, mul_one]
      change (1 : Matrix _ _ k) r (eM (Sum.inl c)) =
        (((oTop l Z hI (s + 1 + 1) hs).iA.map (GlobalTheory.LocMod.ofSplit q).pr *
          (1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank) k).submatrix id eT :
            Matrix (Fin ((I.rec7 l Z).sp.X (s + 1 + 1)).rank) _ k) r c)
      exact entry_inl _ hpr0 hpr1 eT _ (oTop_iA l Z hI (s + 1 + 1) hs) r c _ (eM_l c)
    · rw [Matrix.fromCols_apply_inr]
      change ((GlobalTheory.Fam.Inhab.stdFr k eM).β * Matrix.diagonal dM) r (Sum.inr c) = _
      rw [Matrix.mul_diagonal]
      simp only [dM, Sum.elim_inr]
      change (1 : Matrix _ _ k) r (eM (Sum.inr c)) * π =
        ((oTop l Z hI (s + 1 + 1) hs).iB.map (GlobalTheory.LocMod.ofSplit q).pr *ᵥ fun i => (GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.zeta I l Z u i)) r
      exact entry_inr _ hpr0 hpr1 _ (oTop_iB l Z hI (s + 1 + 1) hs) _ (GlobalTheory.XGeoStd.piE I l Z u) (fun _ => rfl) r _ eM_r
  · intro j hj
    exact intIn_stdFr q _ _ (hLX j) (eX j hj)
  · exact intIn_diagFr q _ _ (hLX (s + 1 + 1)) eM dM hd0 hdv
  · exact intIn_stdFr q _ _ hLT eT
  · refine ⟨eT, oT, fun b hb => ?_⟩
    have h1 : b.map (GlobalTheory.LocMod.ofSplit q).π = 1 := by
      have h2 : b.map (toEAf (I.rec7 l Z)) = (1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank)
          (AE (I.rec7 l Z))).map (toEAf (I.rec7 l Z)) := by
        rw [hb, hβ, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [(GlobalTheory.LocMod.ofSplit q).map_pi_eq_of_toEAf h2, Matrix.map_one _ (map_zero _) (map_one _)]
    have h3 : (GlobalTheory.Fam.Inhab.stdFr k eT).β.submatrix id eT.symm = 1 := by
      change ((1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank) k).submatrix id eT).submatrix id eT.symm = 1
      rw [Matrix.submatrix_submatrix]
      simp
    rw [h3, show (GlobalTheory.XGeoStd.xgeo l Z hI vac u (pk W).ΛX).bT = 1 from rfl, GlobalTheory.LocMod.mt_one_gaMat, Matrix.one_mul, h1]

end GlobalTheory.XGeoStd.Frames

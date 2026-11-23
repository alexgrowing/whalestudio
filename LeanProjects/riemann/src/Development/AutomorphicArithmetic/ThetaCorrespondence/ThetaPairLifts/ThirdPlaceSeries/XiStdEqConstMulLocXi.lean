import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiStdEqConstMulLocXi
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EmbeddingAtLocalFactor

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section Loc
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.TopCongr GlobalTheory.LocMod
namespace GlobalTheory.Fam.TopFrames
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.Fam.TopFrames
end Loc
section Gen
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.DetSpec Matrix
open GlobalTheory.SeeSaw.BaseFrame GlobalTheory.TopStep
namespace GlobalTheory.Fam.TopFrames
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  [StarRing E] {hc : Formalism.BasicNotions.CMData F E}
end GlobalTheory.Fam.TopFrames
end Gen
section World
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel
namespace GlobalTheory.Fam.TopFrames
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}
section Tw
variable {u : B.Word} {a : I.ι} {Ch₀ : ℕ → Type} {A : TwDat I l Z u a Ch₀}
end Tw
variable {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
set_option maxHeartbeats 1000000 in
theorem valuation_frs_sub_kronecker_lt_one (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T} {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.Reads) (P : BadPr I (W.P.I.tup t))
    (hP : P.1 ∈ (B.primes X).vGs) {j : ℕ} (hj : j + 1 = B.R.m) (β : J.Ch₀ j) (r c) :
    HeightOneSpectrum.valuation B.fields.E P.1
      (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P (Pi.single c 1) r - if r.val = c.val then 1 else 0) < 1 := by
  letI := GlobalTheory.Mem.Col2.starE B
  have hm : j ≤ B.R.m := by omega
  obtain ⟨k₀, h, -, h1, h2, h3, -⟩ := hJ.pen j hj β
  have h4 : ¬ ∃ i, (J.G i).q.v = P.1.under (𝓞 B.host.F) := by
    rintro ⟨i, hi⟩
    rw [(GlobalTheory.LocMod.PinEx.place_facts _ (J.G i).idem).1] at hi
    have h5 := ((TwistPrimes.twist_primes_away I hW.tr.ok).2 u (W.P.I.tup t) (J.pl i) ((hW.tq.Q t _).1 (J.mem i))).1
    rcases (under_eq_iff B.host (J.pl i) P.1).1 hi.symm with h6 | h6
    · exact h5.2.1 (h6 ▸ hP)
    · exact h5.2.2.2.1 (h6 ▸ hP)
  have h5 := finM_map_prV _ (rankN (I.rec7 l Z) j hm) h3 h4
  have h6 := (TrueColsTest.kStd_spec X u (B.R.N j)).2.1 (P.1.under (𝓞 B.host.F))
    fun hT => Formalism.L2.Col.rls_T_notUnder l.pr u _ hT ⟨P.1, hP, rfl⟩
  have hk : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) (J.A.kb j β) = 1 := by
    refine Units.ext ?_
    have h7 := (hJ.is.kA j hm β).2.1
    rw [h2, GlobalTheory.AdForm.Model.finM_mul, h1] at h7
    have h8 : (J.A.kb j β).1.map (Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) = 1 := by
      rw [← h7]
      refine Matrix.map_mul.trans ?_
      have h6' : (TC.kStd X u (B.R.N j)).1.map (Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) = 1 := congrArg Units.val h6
      exact (congrArg₂ (fun x y : Matrix (Fin (B.R.N j)) (Fin (B.R.N j))
        (B.host.E ⊗[B.host.F] (P.1.under (𝓞 B.host.F)).adicCompletion B.host.F) => x * y) h6' h5).trans (one_mul _)
    exact h8
  have e : Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P = (J.A.p0 j β).1.1.deco.1.liftFr ⟨P.1, hP⟩ := dif_pos hP
  have h9 := (hJ.is.base j hm β).1
  rw [e]
  exact GlobalTheory.SeeSaw.BaseFrame.lift_near_one (y := 1) (by rw [one_mul]; exact h9) (by rw [one_mul]; exact h9) h9 (hJ.is.base j hm β).2
    ⟨P.1, hP⟩ hk (GlobalTheory.TopStep.liftFr_spec (J.A.p0 j β).1.1.deco.2 ⟨P.1, hP⟩) r c
set_option maxHeartbeats 1000000 in
theorem fm_beta_eq {a : _root_.GlobalTheory.Fam.GeometricFamily W u} (hIs : a.Is) (hTr : a.True) (hA : ∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0)
    (n : Fin a.n) (r) : (∀ c, (a.G n).FM.β r (Sum.inl c) = if r.val = GlobalTheory.SymBridge.zPos c then 1 else 0) ∧
      (a.G n).FM.β r (Sum.inr ()) = _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) := by
  letI := a.fld; letI := a.val; letI := a.top; letI := a.loc
  have hA' : ∀ j (h : j = (I.rec7 l Z).R.m) r s, (a.g.oT j h).iA r s = if r.val = s.val then 1 else 0 := by
    rintro _ rfl
    exact hA
  have hB' : ∀ j (h : j = (I.rec7 l Z).R.m) r, ((a.g.oT j h).iB *ᵥ a.o.ζ₀) r =
      if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0 := by
    rintro _ rfl r
    exact hTr.z0 r
  obtain ⟨-, ⟨e, he, hT⟩, hz⟩ := hIs.stdG n
  rw [(a.G n).last]
  refine ⟨fun c => ?_, ?_⟩
  · rw [fromCols_apply_inl, hT, Matrix.mul_apply, Finset.sum_eq_single (e c)]
    · rw [Matrix.submatrix_apply, id, Matrix.one_apply_eq, mul_one, Matrix.map_apply, ← he c]
      refine (congrArg (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) (hA' _ _ r (e c))).trans ?_
      split_ifs
      exacts [map_one _, map_zero _]
    · intro b _ hb
      rw [Matrix.submatrix_apply, id, Matrix.one_apply_ne hb, mul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  · rw [fromCols_apply_inr, hz]
    refine Eq.trans ?_ (congrArg (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) (hB' _ (a.G n).hs r))
    refine Eq.trans ?_ (map_sum (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) (fun b => (a.g.oT _ (a.G n).hs).iB r b * a.o.ζ₀ b) Finset.univ).symm
    show ∑ b, _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n ((a.g.oT _ (a.G n).hs).iB r b) * _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (a.o.ζ₀ b) = _
    exact Finset.sum_congr rfl fun b _ => (map_mul (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) _ _).symm
set_option maxHeartbeats 2000000 in
theorem xiStd_eq_const_mul_locXi_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (n : Fin a.n) (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch ((a.G n).s + 1)) (γ : J.Ch ((a.G n).s + 1 + 1)) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ C : ℂ,
  (∀ (e' : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1))) (e : GlobalTheory.StepData.Ix (Fin B.R.k ⊕ Fin ((a.G n).s + 1)) (Fin B.R.t) ((a.G n).s + 2) ⊕ Unit ≃ Fin (B.R.N B.R.m)),
     GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' → GlobalTheory.SymBridge.IsOrd (Sum.elim GlobalTheory.SymBridge.zPos fun _ => B.R.N B.R.m - 1) e →
     ∀ (y : Formalism.L2.Col.HomE B.fields.E (B.R.N ((a.G n).s + 1)) (B.R.N B.R.m)) (y' : Formalism.L2.Col.Sp B.fields.E (B.R.N ((a.G n).s + 1))),
       (∀ i, Formalism.L2.Col.IntAt P.1 ((Formalism.L2.Col.qOf P.1 : B.fields.E) * y' i)) →
       ((a.G n).S.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) (a.G n).S.ψ (a.G n).ν (-1)
           (Submodule.Quotient.mk fun r => _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (y' (e' r))) (GlobalTheory.SymBridge.toLoc (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) e e' y) =
         C * B.embLL (GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P y y')) →
  ∀ (hj : (a.G n).s + 1 + 1 ≤ B.R.m) z, _root_.GlobalTheory.Fam.TopLoc.standardXi a n z =
    C * B.embLL (GlobalTheory.QTw.locXi J.A ((a.G n).s + 1) (J.ι _ α) (J.ι _ γ) P (GlobalTheory.QTw.homOf I l Z ((a.G n).s + 1) hj z)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a hIs hTr hA n t J hJ α γ P hP C hC hj z
  have hint : ∀ x : B.fields.E, _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n x ∈ 𝒪[(a.G n).k] ↔ Formalism.L2.Col.IntAt P.1 x := by
    have hR := (hIs.tie (fun t => (TopLocFac.nonempty_rowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g hTr.pinX.std t).some)
      fun t => (TopLocFac.nonempty_colCh _ _).some).2
    rw [hP]
    exact (GlobalTheory.LocMod.PinEx.place_facts _ (hR.idem n).1).2.1
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  have hm : (a.G n).s + 1 ≤ B.R.m := Nat.le_of_succ_le hj
  have hPv : P.1 ∈ (B.primes X).vGs := hP ▸ (hW.lev.2.1 _).1 (a.pl n).2
  have hlt := GlobalTheory.SeeSaw.LevelData.val_lt_one_iff hint
  obtain ⟨e', he'⟩ := exists_xOrd B.R ((a.G n).s + 1)
  obtain ⟨e, he⟩ := exists_topOrd B.R (a.G n).s hs
  have hF := _root_.GlobalTheory.Fam.TopFrames.valuation_frs_sub_kronecker_lt_one hW hJ P hPv hs (J.ι _ α)
  have hF' := top_near hW.tr.ok hJ.is P hPv hs (J.ι _ γ)
  have hq := intAt_q_mul (A := J.A) P hPv hs (J.ι _ α)
  have hco := hJ.cosG n α e' he'
  have hx : locXi J.A ((a.G n).s + 1) (J.ι _ α) (J.ι _ γ) P (homOf I l Z ((a.G n).s + 1) hj z) =
      GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P
        (castSp B.fields.E (congrArg B.R.N hs) ∘ₗ Formalism.L2.Col.inFr
          (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.1 P)
          (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1 + 1) (J.ι _ γ)).1.1 P) (homOf I l Z ((a.G n).s + 1) hj z))
        ((Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.1 P).symm
          (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.2)) := by
    unfold locXi
    rw [dif_neg (by omega), dif_neg (by omega), dif_pos hs]
    rfl
  rw [hx]
  clear hx
  generalize Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.1 P = f at hF hq ⊢
  generalize Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1 + 1) (J.ι _ γ)).1.1 P = f' at hF' ⊢
  generalize Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ α)).1.2 = y at hq hco ⊢
  obtain ⟨-, -, -, -, -, -, -, -, -, -, g10⟩ := id (GlobalTheory.SeeSaw.LevelData.type_prime hPv)
  have hqv : HeightOneSpectrum.valuation B.fields.E P.1 (Formalism.L2.Col.qOf P.1 : B.fields.E) = WithZero.exp (-1 : ℤ) := by
    obtain ⟨i, g1, -, -, g4, -⟩ := GlobalTheory.SeeSaw.LevelData.type_prime hPv
    exact GlobalTheory.AtTypeExists.valuation_norm P.1 (g1 ▸ g4)
  have hy : (Submodule.Quotient.mk ((a.G n).S.y0 (Fin B.R.t)) : _ ⧸ box _ (1 : (a.G n).kˣ)) =
      Submodule.Quotient.mk fun r => _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (f.symm y (e' r)) := by
    refine GlobalTheory.SeeSaw.StdMatch.mk_eq_mk_of_int fun c => ?_
    have h1 := (hint _).2 (intAt_sub_of_near hqv hF hq (e' c))
    rw [LinearEquiv.apply_symm_apply, map_sub] at h1
    have h2 : _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (y (e' c)) - (a.G n).S.y0 (Fin B.R.t) c ∈ 𝒪[(a.G n).k] := hco c
    have h3 := sub_mem h2 h1
    rwa [sub_sub_sub_cancel_left] at h3
  refine Eq.trans ?_ (hC e' (e.trans (finCongr (congrArg B.R.N hs))) he' (fun r => he r) _ _ hq)
  refine Eq.trans ?_ (congrArg (fun w => ((a.G n).S.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) (a.G n).S.ψ (a.G n).ν (-1) w _) hy)
  have e1 := GlobalTheory.SeeSaw.StdMatch.mul_toLoc (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) (rankN (I.rec7 l Z) _ hm) (rankN (I.rec7 l Z) _ hj) f f' e' e
    (Matrix.of fun r c => _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (f (Pi.single (e' c) 1) (finCongr (rankN (I.rec7 l Z) _ hm) r)))
    (Matrix.of fun r c => _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (f' (Pi.single (e c) 1) (finCongr (rankN (I.rec7 l Z) _ hj) r)))
    (fun _ _ => rfl) (fun _ _ => rfl) z
  refine xiTop_frames (a.G n).unitVol (a.G n).S (Fin B.R.t) ((a.G n).FX _ le_rfl) (a.G n).FM
    (GlobalTheory.SeeSaw.StdMatch.gamma_int (a.G n).q _ (Set.ext (hTr.pinX.xs _ hm).2.2) ((a.G n).latX _ le_rfl))
    (GlobalTheory.SeeSaw.StdMatch.gamma_int (a.G n).q _ (Set.ext (hTr.pinX.xs _ hj).2.2) (a.G n).latM) (fun r c => ?_) (fun r c => ?_) _ e1
  · obtain ⟨e₁, h1, h2⟩ := (hIs.stdG n).1 ((a.G n).s + 1) le_rfl
    have h3 := (hlt _).2 (hF (finCongr (rankN (I.rec7 l Z) _ hm) r) (e' c))
    rw [map_sub, apply_ite (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n), map_one, map_zero, (he' c).trans (h1 c).symm] at h3
    have h4 : ((a.G n).FX ((a.G n).s + 1) le_rfl).β r c = if r.val = (e₁ c).val then 1 else 0 :=
      (congrFun (congrFun h2 r) c).trans (Matrix.one_apply.trans (if_congr Fin.ext_iff rfl rfl))
    exact (congrArg (fun w => valuation (a.G n).k (_ - w)) h4).trans_lt h3
  · have h3 := (hlt _).2 (hF' (finCongr (rankN (I.rec7 l Z) _ hj) r) (e c))
    rw [map_sub, apply_ite (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n), map_one, map_zero, he c] at h3
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.Fam.TopFrames.fm_beta_eq hIs hTr hA n r
    show valuation (a.G n).k (_ - (a.G n).FM.β r c) < 1
    rcases c with c | c
    · exact (congrArg (fun w => valuation (a.G n).k (_ - w)) (h1 c)).trans_lt h3
    · refine (congrArg (fun w => valuation (a.G n).k (_ - w)) h2).trans_lt ?_
      have h4 := (hlt ((X.piT u - 1 : 𝓞 B.host.E) : B.host.E)).2 ((P.1.valuation_lt_one_iff_mem _).2 (g10 u))
      have h5 : _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n ((X.piT u - 1 : 𝓞 B.host.E) : B.host.E) = _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n ((X.piT u : 𝓞 B.host.E) : B.host.E) - 1 :=
        ((_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n).map_sub ((X.piT u : 𝓞 B.host.E) : B.host.E) 1).trans (congrArg _ (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n).map_one)
      rw [h5] at h4
      replace h3 : valuation (a.G n).k (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (f' (Pi.single (e (Sum.inr c)) 1) (finCongr (rankN (I.rec7 l Z) _ hj) r)) -
          if (finCongr (rankN (I.rec7 l Z) _ hj) r).val = B.R.N B.R.m - 1 then 1 else 0) < 1 := h3
      have h6 : 0 < B.R.N B.R.m := by
        have := (e (Sum.inr c)).2
        rw [← hs]
        omega
      by_cases hr : r.val + 1 = B.R.N B.R.m
      · rw [if_pos (show (finCongr (rankN (I.rec7 l Z) _ hj) r).val = B.R.N B.R.m - 1 from Nat.eq_sub_of_add_eq hr)] at h3
        rw [if_pos hr]
        have h7 := Valuation.map_sub_lt _ h3 h4
        rwa [sub_sub_sub_cancel_right] at h7
      · rw [if_neg (show ¬ (finCongr (rankN (I.rec7 l Z) _ hj) r).val = B.R.N B.R.m - 1 from fun h => hr (by
          have h8 : r.val = B.R.N B.R.m - 1 := h
          omega))] at h3
        rw [if_neg hr, map_zero]
        exact h3
end GlobalTheory.Fam.TopFrames
end World
end
end

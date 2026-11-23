import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevOfMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelElementEqProdLocalParts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateCompactMemLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointHeckeComponentTameAndResidual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharacterClosedForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdLocalParts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSumOfNoConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.RowLevel

theorem rTrans_lev {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (G) (hG : G ∈ MultT θ M J χ) (w) {a b k : GA D V} (ha : a ∈ GinfC V)
    (hk : k ∈ GfC V) (hm : b⁻¹ * k * b ∈ J) :
    rTrans k (rTrans (a * b) (G w)) = χ (b⁻¹ * k * b) • rTrans (a * b) (G w) := by
  have h1 := (GlobalTheory.ValMoveProof.valMove D θ hθ V S M J χ).1 G hG w _ hm
  have hc : a * k = k * a := GlobalTheory.AdelicSplit.commute_GinfC_GfC V ha hk
  funext y
  have h2 := congrFun h1 (y * (a * b))
  simp only [rTrans, Pi.smul_apply, smul_eq_mul] at h2 ⊢
  rw [← h2]
  refine congrArg (G w) ?_
  calc y * k * (a * b) = y * (k * a) * b := by group
    _ = y * (a * k) * b := by rw [hc]
    _ = y * (a * b) * (b⁻¹ * k * b) := by group

theorem rightTranslate_level_conj_acts_by_character_finite {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (G) (hG : G ∈ MultT θ M J χ) (w) {b k : GA D V}
    (hk : k ∈ GfC V) (hm : b⁻¹ * k * b ∈ J) :
    rTrans k (rTrans b (G w)) = χ (b⁻¹ * k * b) • rTrans b (G w) := by
  have := rTrans_lev hθ M J χ G hG w (a := 1) (Subgroup.one_mem _) hk hm
  simpa only [one_mul] using this

theorem conj_mem_off {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ N : GlobalTheory.FinPl.Lat V} {M : ℕ}
    (hβ : IsSDFrame V β Λ M) (hN : IsSelfDualC V N) (L : LevDat D.host.E ℂ V.rank) {P : GlobalTheory.FinPl.Pl D → Prop}
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ¬ P (PP.under (𝓞 D.host.F))) {b κ : GA D V} (hb : b ∈ GfC V)
    (hmv : ∀ p, P p → GlobalTheory.FinPl.Moves V b Λ N (· = p)) (hκ : GlobalTheory.FinPl.InK V N P κ) :
    b⁻¹ * κ * b ∈ levS V β L ∧ levChi V β L (b⁻¹ * κ * b) = 1 := by
  have hΛ := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D V β Λ M hβ
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨hκf, hκS⟩ := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff V _ κ).1 hκ.1
  have h1 : ∀ p, ¬ P p → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram p (b⁻¹ * κ * b) = 1 := fun p hp => by
    rw [map_mul, map_mul, hκS p hp, mul_one, ← map_mul, inv_mul_cancel, map_one]
  have hSt : Lev.finE V (b⁻¹ * κ * b) ∈ St β := by
    refine (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hfr _).2 fun p => ?_
    by_cases hp : P p
    · rw [← GlobalTheory.StMoves.moves_iff_stabLoc V Λ hΛ.1.fg p, GlobalTheory.StMoves.moves_conj_iff κ (hmv p hp)]
      exact GlobalTheory.LevConj.moves_at_of_moves hN.1 hp hκ.2
    · rw [h1 p hp]; exact one_mem _
  have h' : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → redFn β PP (Lev.finE V (b⁻¹ * κ * b)) = 1 := fun PP h =>
    GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP hSt (h1 _ (hP PP h))
  refine ⟨⟨(GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem hb) hκf) hb,
    GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm V.gram β L _ (GlobalTheory.LevSplit.finE_mem_UA V _) hSt h'⟩, ?_⟩
  unfold Lev.levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one β L _ h', Units.val_one]

theorem off_lev : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GPin G → GRead f G pl → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), (f.t t).Is → F.Pins w → QLev f F → (∀ i, (G i).Chars (f.t t)) → ∀ j, j < D.R.m → ∀ κ, GlobalTheory.FinPl.InK _ (v.N j) (offP v w) κ → (f.g.b j)⁻¹ * κ * f.g.b j ∈ levS _ ((pk W).βY j) ((pk W).datYt t j (lvP W)) ∧ levChi _ ((pk W).βY j) ((pk W).datYt t j (lvP W)) ((f.g.b j)⁻¹ * κ * f.g.b j) = 1 := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch j hj κ hκ
  have hlev := W.Q.charW.base.lev
  refine conj_mem_off (hlev.βY j hj) (hv.sd j hj) _ ?_ (hV.b j ▸ hv.b j)
    (fun p hp => hV.moves j hj _ fun q hq => hq ▸ hp.1) hκ
  rintro PP (h | h) ho
  · exact ho.1 ((hV.gP _).2 ⟨PP, h, rfl⟩)
  · obtain ⟨e, he⟩ := hQL.places
    obtain ⟨i, hi⟩ := e.surjective ⟨PP, h⟩
    refine ho.2 ((hFP.places _).2 ⟨i, ?_⟩)
    rw [(he i).2, hi]

theorem top_lev : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GPin G → GRead f G pl → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), (f.t t).Is → F.Pins w → QLev f F → (∀ i, (G i).Chars (f.t t)) → ∀ κ, GlobalTheory.FinPl.InK f.c.T v.NT (· ∈ v.tP) κ → f.g.bT⁻¹ * κ * f.g.bT ∈ levS _ (pk W).βX (datXP (pk W) (lvP W) t) ∧ levChi _ (pk W).βX (datXP (pk W) (lvP W) t) (f.g.bT⁻¹ * κ * f.g.bT) = 1 := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch κ hκ
  have hlev := W.Q.charW.base.lev
  refine conj_mem_off hlev.βX hv.sdT _ ?_ (hV.bT.1 ▸ hv.bT) (fun p _ => hV.bT.2 ▸ hV.movesT _) hκ
  rintro PP (h | h) ho
  · exact Finset.disjoint_left.1 hv.disj ((hV.gP _).2 ⟨PP, h, rfl⟩) ho
  · have h1 := (hV.tP _).1 ho
    refine (hlev.Q_off t PP h).2 u ?_
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal := h1
    rwa [map_natCast] at h2

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem chi_eq_mu {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) (q : GlobalTheory.FinPl.SplitPt D k) {PP : Pl D.host.E}
    (hPP : PP ∈ L.Pg) (h : Formalism.L2.NTheta.IsIdemAt q.e PP) (π : Lev.EAf D →+* k) (h1 : ∀ a, π (toEAf D a) = q.pr a)
    (h3 : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, π s ∈ 𝒪[k])
    (h4 : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP s = 0 ↔ valuation k (π s) < 1)
    (c : ℕ) (hc : c < D.R.m) (μ : kˣ →* ℂˣ) (hμ : (ofSplit q).IsComp (Lift.chrStep L.mu0 L.eta (c + 1)).1⁻¹ μ) (ht : IsTame μ)
    (s : Formalism.L2.Herm.intAf D.host.F D.host.E) (y : (kP PP)ˣ) (x : kˣ) (hy : (y : kP PP) = resS D.host.F PP s)
    (hx : (x : k) = π s) : L.chi (c + 1) PP y = μ x := by
  haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (y : kP PP)
  have hzP : z ∉ PP.asIdeal := fun hm => y.ne_zero (hz.symm.trans (Ideal.Quotient.eq_zero_iff_mem.2 hm))
  have hz0 : (z : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 (by rintro rfl; exact hzP (zero_mem _))
  have hπ : π (oToS D.host.F D.host.E z) = q.pr (incA D (z : D.host.E)) := h1 (incA D (z : D.host.E))
  have hv : valuation k (q.pr (incA D (z : D.host.E))) = 1 :=
    le_antisymm (hπ ▸ h3 (oToS D.host.F D.host.E z)) (not_lt.1 fun hl => hzP ((GlobalTheory.LocMod.LevBack.pr_lt q h z).2 hl))
  have hne : q.pr (incA D (z : D.host.E)) ≠ 0 := fun h0 => by rw [h0, map_zero] at hv; exact zero_ne_one hv
  have hd : valuation k ((x : k) - q.pr (incA D (z : D.host.E))) < 1 := by
    have := (h4 (s - oToS D.host.F D.host.E z)).1 (by rw [map_sub, resS_oToS, hz, hy, sub_self])
    rwa [AddSubgroupClass.coe_sub, RingHom.map_sub, hπ, ← hx] at this
  have e1 : μ x = μ (Units.mk0 _ hne) := by
    have := ht (x * (Units.mk0 _ hne)⁻¹) (by
      have e : ((x * (Units.mk0 _ hne)⁻¹ : kˣ) : k) - 1 =
          ((x : k) - q.pr (incA D (z : D.host.E))) * (q.pr (incA D (z : D.host.E)))⁻¹ := by
        rw [sub_mul, mul_inv_cancel₀ hne]; simp
      rw [e, map_mul, map_inv₀, hv, inv_one, mul_one]
      exact hd)
    rwa [map_mul, map_inv, mul_inv_eq_one] at this
  have e2 := hμ (Units.mk0 _ hne) (GlobalTheory.LocMod.SplitHecke.idlU q (Units.mk0 _ hne)) rfl
  have e3 := GlobalTheory.LocMod.SplitHecke.chi_idlU_rat q h (hL.mu0 ⟨c, hc⟩) hz0 (Units.mk0 _ hne) rfl
  have e4 := GlobalTheory.LocMod.SplitHecke.chi_idlU_rat q h hL.eta hz0 (Units.mk0 _ hne) rfl
  rw [GlobalTheory.NormOneUnit.locK_unr (L.C.isEta.unr PP) (y := Units.mk0 _ hz0)
    ((PP.valuation_eq_one_iff_notMem (K := D.host.E)).2 hzP), Units.val_one] at e4
  have e5 := hL.chi ⟨c, hc⟩ PP hPP z (Units.mk0 _ hz0) y rfl hz.symm
  rw [← e5] at e3
  have e4' : L.eta (GlobalTheory.LocMod.SplitHecke.idlU q (Units.mk0 _ hne)) = 1 := Circle.coe_injective e4
  apply Units.ext
  rw [e1, e2]
  unfold Lift.chrStep
  split_ifs
  · simp only [MonoidHom.inv_apply, MonoidHom.mul_apply, e4', inv_one, mul_one, Circle.coe_inv]
    rw [e3]; simp
  · simp only [MonoidHom.inv_apply, Circle.coe_inv]
    rw [e3]; simp

theorem red_lam {s κ t j n r : ℕ} (S : GlobalTheory.SymChain.SymData k s κ) (hr0 : r = κ + (s + 1)) (hr : r ≤ n)
    {e : Ix (Fin κ ⊕ Fin (s + 1)) (Fin t) j ≃ Fin n} (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e) {O K : Type} [CommRing O]
    [CommRing K] [Nontrivial K] (φ : O →+* K) (ψ : O →+* k) (h1 : ∀ z, ψ z ∈ 𝒪[k]) (h2 : ∀ z, φ z = 0 ↔ valuation k (ψ z) < 1)
    (χ : ℕ → Kˣ →* ℂˣ) (hχ : ∀ c, c < j → ∀ (z : O) (y : Kˣ) (x : kˣ), (y : K) = φ z → (x : k) = ψ z → χ (c + 1) y = S.μ (c + 1) x)
    (Y : GL (Fin n) O) (g : (S.P.iter (Fin t) S.μ S.tame j).J)
    (hy : ∀ a b, ψ (Y.val (e a) (e b)) = (g : GL (Ix (Fin κ ⊕ Fin (s + 1)) (Fin t) j) k).val a b) :
    Formalism.UG.bc φ Y ∈ blockTri (blkOf r t) ∧ ∃ x : S.P.J, (∀ (a b : Fin κ ⊕ Fin (s + 1)) (a' b' : Fin r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : O,
        φ z = (upperLeftBlock hr (Formalism.UG.bc φ Y)).val a' b' → valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val a b - ψ z) < 1) ∧
      (S.P.iter (Fin t) S.μ S.tame j).lam g =
        S.P.lam x * ∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) (Formalism.UG.bc φ Y)) := by
  obtain ⟨-, hP⟩ := (GlobalTheory.SymChain.pattern_iter _ _ _ S (Fin t) j g.1).1 g.2
  have hb := (GlobalTheory.LocMod.LevBack.red_of_pattern S hr0 hr he φ ψ h1 h2 Y fun a b hab => by rw [hy]; exact hP a b hab).1
  obtain ⟨g₀, Dm, e0, hD, el⟩ := GlobalTheory.SymBridge.iter_lam_closed k _ (Fin t) S.P S.μ S.tame j g
  refine ⟨hb, g₀, fun a b a' b' ha hb' z hz => ?_, ?_⟩
  · have hc : ∀ a (a' : Fin r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → Fin.castLE hr a' = e (Sum.inl a) := fun a a' h =>
      Fin.ext (by rw [he]; rcases a with a | a <;> exact h)
    rw [upper_block_val_submatrix hr (blockTri_blkOf_le _ _ hb), submatrix_apply, hc a a' ha, hc b b' hb'] at hz
    rw [e0, submatrix_apply, ← hy, ← map_sub, ← h2, map_sub, hz]
    exact sub_self _
  · rw [el, Finset.prod_range]
    congr 1
    refine Finset.prod_congr rfl fun c _ => (hχ c c.2 (Ix.diagonalBlockOfMatrix (Y.val.submatrix e e) c).det _ _ ?_ ?_).symm
    · have hk := GlobalTheory.LocMod.LevBack.blkOf_zPos hr0 he
      have hbij : Function.Bijective fun i : Fin t =>
          (⟨e (.inr (c, i)), hk _⟩ : {i : Fin n // blkOf r t i = c.val + 1}) := by
        refine ⟨fun s s' h => by simpa using congrArg Subtype.val h, fun ⟨i, hi⟩ => ?_⟩
        obtain ⟨i | ⟨c', s⟩, rfl⟩ := e.surjective i
        · exact absurd ((hk _).symm.trans hi) (Nat.succ_ne_zero _).symm
        · obtain rfl : c' = c := Fin.ext (Nat.succ_injective ((hk _).symm.trans hi))
          exact ⟨s, rfl⟩
      rw [diag_block_det_val _ hb, ← det_submatrix_equiv_self (Equiv.ofBijective _ hbij), RingHom.map_det]
      rfl
    · rw [Matrix.GeneralLinearGroup.val_det_apply, (hD c).2, RingHom.map_det]
      congr 1
      ext a b
      exact (hy _ _).symm

end Loc

theorem mat_frame {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (π : Lev.EAf D →+* k) (h1 : ∀ a, π (toEAf D a) = q.pr a) {V : HSp D}
    {β : GL (Fin V.rank) (Lev.EAf D)} {b x : GA D V} {ι Y : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k V.rank Y) (L : LatFrame k ι Y) (e : ι ≃ Fin V.rank)
    (hmv : MovedTo (ofSplit q) V b β ((F.β * L.bas.val).submatrix id fun i => L.ord (e.symm i))) (xk : GL Y k)
    (hx : (mt V x).map q.pr = F.β * xk.val * F.γ) :
    GeneralLinearGroup.map π (β⁻¹ * Lev.finE V (b⁻¹ * x * b) * β) = reGL e (L.conj.symm xk) := by
  have hmap : ∀ M : Matrix (Fin V.rank) (Fin V.rank) (AE D), (M.map (toEAf D)).map π = M.map q.pr :=
    fun M => Matrix.ext fun _ _ => h1 _
  rw [← GlobalTheory.LocMod.LevBack.conj_frame F L e (GeneralLinearGroup.map π (Lev.finE V b * β))
    (GeneralLinearGroup.map π (Lev.finE V x)) (L.conj.symm xk) ?_ ?_]
  · rw [MonoidHom.map_mul (Lev.finE V), MonoidHom.map_mul (Lev.finE V), MonoidHom.map_inv, GlobalTheory.LocMod.LevBack.conj_conj,
      MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv]
  · have hb : (β.val.map (GlobalTheory.AdelicLatMove.finEmb D)).map (toEAf D) = β.val :=
      Matrix.ext fun _ _ => GlobalTheory.LocMod.LevBack.toEAf_finEmb _
    refine Eq.trans ?_ (hmv _ hb)
    refine Eq.trans ?_ (hmap _)
    rw [Matrix.map_mul, hb]
    rfl
  · rw [MulEquiv.apply_symm_apply]
    exact (hmap _).trans hx

theorem conj_list_prod {G ι : Type} [Group G] (b : G) (h : ι → G) (l : List ι) :
    b⁻¹ * (l.map h).prod * b = (l.map fun i => b⁻¹ * h i * b).prod := by
  induction l with
  | nil => simp
  | cons i l ih => rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ← ih]; group

set_option maxHeartbeats 1000000 in

theorem g_lev {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} {f : FamCh W u}
    {v : VCom f.c} (hv : v.Is) (hV : VTie f v) {n : ℕ} {G : Fin n → GLoc v} {pl : Fin n ≃ (pk W).Pg} (hGP : GPin G)
    (hGR : GRead f G pl) (t : W.P.T) (j : ℕ) (hj : j < D.R.m) (k : GA D (Yc D j)) (hk : k ∈ v.JG j) (a : ℂ) (ha : GLam G j k a) :
    (f.g.b j)⁻¹ * k * f.g.b j ∈ levS _ ((pk W).βY j) ((pk W).datYt t j (lvP W)) ∧
      levChi _ ((pk W).βY j) ((pk W).datYt t j (lvP W)) ((f.g.b j)⁻¹ * k * f.g.b j) = a := by
  have hlev := W.Q.charW.base.lev
  have hΛ := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hlev.βY j hj)
  obtain ⟨c0, hfr, -⟩ := hlev.βY j hj
  obtain ⟨hkg, hkJ⟩ := (hGP.lev j hj k).1 hk
  obtain ⟨hkf, hkS⟩ := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff _ _ k).1 hkg
  obtain ⟨c, hc, x, hxM, rfl⟩ := ha
  have hb : f.g.b j ∈ GfC (Yc D j) := hV.b j ▸ hv.b j
  choose e he hmv using fun i => hGR.frame i j (c i) (hc i)
  choose π h1 h2 h3 h4 using fun i => GlobalTheory.LocMod.LevBack.exists_chart (G i).q (hGR.idem i).1
  have hSt : Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j) ∈ St ((pk W).βY j) := by
    obtain ⟨h, hloc, hprod⟩ := GlobalTheory.LevelCut.prod_local_parts D f.c v n G hGP j k hkg
    rw [hprod, conj_list_prod, map_list_prod]
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    simp only [List.mem_map] at hy
    obtain ⟨_, ⟨i, -, rfl⟩, rfl⟩ := hy
    obtain ⟨xk, hM, hL⟩ := hloc i (c i) (hc i)
    have hJ := hkJ i _ _ _ hM
    have hγ := mat_frame (G i).q (π i) (h1 i) ((G i).FY j (c i) (hc i))
      (typeFrame (G i).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (c i) (hc i))) (e i) (hmv i) xk hL.2
    obtain ⟨hyK, -⟩ := (GlobalTheory.SymChain.pattern_iter _ _ _ (G i).S (Fin D.R.t) j
      ((typeFrame (G i).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (c i) (hc i))).conj.symm xk)).1 hJ
    obtain ⟨Y, hY, -⟩ := GlobalTheory.LocMod.LevBack.exists_int (G i).q (π i) (h2 i) (Yc D j) hΛ hfr (t := f.g.b j) hL.1 (by
      erw [hγ]
      rw [mem_KO, ← map_inv]
      rw [mem_KO] at hyK
      exact ⟨fun _ _ => hyK.1 _ _, fun _ _ => hyK.2 _ _⟩)
    exact ⟨Y, hY⟩
  have hQ : ∀ PP ∈ (pk W).Q t, redFn ((pk W).βY j) PP (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)) = 1 := fun PP hPP => by
    refine GlobalTheory.ChainOnto.RedOne.redFn_eq_one D _ _ _ PP hSt ?_
    have hn : PP.under (𝓞 D.host.F) ∉ v.gP := fun hm => by
      obtain ⟨PP', hP', e'⟩ := (hV.gP _).1 hm
      obtain ⟨i, hi⟩ := (hlev.Pg PP').1 hP'
      obtain ⟨⟨q, hq, hcard, -, hqg⟩, -⟩ := hlev.Q_pl t PP hPP
      have g1 := Formalism.IndefR.Fin.g_mem_of_div _ hi
      have g2 : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ (PP'.under (𝓞 D.host.F)).asIdeal := by
        change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP'.asIdeal
        rwa [map_natCast]
      rw [← e'] at g2
      have g3 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal := g2
      rw [map_natCast] at g3
      exact Formalism.IndefR.Fin.not_two_primes PP.isPrime.ne_top (D.host.g_prime i) hq (fun h => hqg i h.symm) g3
        (Formalism.IndefR.Fin.char_mem hq hcard)
    rw [map_mul, map_mul, hkS _ hn, mul_one, ← map_mul, inv_mul_cancel, map_one]
  obtain ⟨Y, hY⟩ := id hSt
  have hYv : Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype Y =
      ((pk W).βY j)⁻¹ * Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j) * (pk W).βY j := by
    rw [← hY]
    change _ = ((pk W).βY j)⁻¹ * ((pk W).βY j * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype Y * ((pk W).βY j)⁻¹) * (pk W).βY j
    group
  have hall := fun i => by
    haveI : Nontrivial (kP (pl i).1) := Ideal.Quotient.nontrivial_iff.2 (pl i).1.isPrime.ne_top
    have hs := (G i).hs
    have hγ := mat_frame (G i).q (π i) (h1 i) ((G i).FY j (c i) (hc i))
      (typeFrame (G i).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (c i) (hc i))) (e i) (hmv i) (x i).1 (hxM i)
    exact red_lam (G i).S (r := D.R.r) (by unfold Ranks.r; omega) (r_le_Y j) (he i) (resS D.host.F (pl i).1)
      ((π i).comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (h3 i) (h4 i) (fun c => (pk W).chi c (pl i).1)
      (fun c hc z y x' hy hx => chi_eq_mu (pk W).toLevCh hlev (G i).q (pl i).2 (hGR.idem i).1 (π i) (h1 i) (h3 i) (h4 i) c
        (by omega) _ (hGR.mu i (c + 1) (by omega) (by omega)) ((G i).S.tame _) z y x' hy hx) Y
      ⟨(typeFrame (G i).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (c i) (hc i))).conj.symm (x i).1, (x i).2⟩ (fun a b => by
        have e1 := congrArg (fun g : GL _ _ => g.val (e i a) (e i b)) hγ
        simp only [reGL_val, submatrix_apply, Equiv.symm_apply_apply] at e1
        refine Eq.trans ?_ e1
        exact congrArg (π i) (congrArg (fun g : GL _ _ => g.val (e i a) (e i b)) hYv))
  choose hbt x₀ hred hlam using hall
  have hr : ∀ PP, redFn ((pk W).βY j) PP (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)) = Formalism.UG.bc (resS D.host.F PP) Y :=
    fun PP => by rw [← hY, redFn_frGL]
  obtain ⟨g, hg⟩ : ∃ g : ∀ PP : (pk W).Pg, GL (Fin D.R.r) (kP PP.1),
    ∀ PP, g PP = upperLeftBlock (r_le_Y j) (Formalism.UG.bc (resS D.host.F PP.1) Y) := ⟨_, fun _ => rfl⟩
  have hrT : rTup ((pk W).βY j) ((pk W).datYt t j (lvP W)) (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)) = g := by
    funext PP
    exact (congrArg (upperLeftBlock (r_le_Y j)) (hr PP.1)).trans (hg PP).symm
  have hR : ∀ i (a b : Fin D.R.k ⊕ Fin ((G i).s + 1)) (a' b' : Fin D.R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E,
        Ideal.Quotient.mk (pl i).1.asIdeal z = (g (pl i)).val a' b' →
        valuation (G i).k ((x₀ i : GL (Fin D.R.k ⊕ Fin ((G i).s + 1)) (G i).k).val a b - (ofSplit (G i).q).pr (z : D.host.E)) < 1 := by
    intro i a b a' b' ha hb z hz
    rw [hg] at hz
    have := hred i a b a' b' ha hb (oToS D.host.F D.host.E z) ((resS_oToS (pl i).1 z).trans hz)
    rwa [show ((π i).comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (oToS D.host.F D.host.E z) =
      (ofSplit (G i).q).pr (z : D.host.E) from h1 i (incA D (z : D.host.E))] at this
  have hgH : g ∈ (lvP W).H := (hGR.lev g).1.2 fun i => ⟨x₀ i, hR i⟩
  have hchi := (hGR.lev g).2 hgH x₀ hR
  refine ⟨⟨(GfC _).mul_mem ((GfC _).mul_mem ((GfC _).inv_mem hb) hkf) hb, ?_⟩, ?_⟩
  · change Lev.finE (Yc D j) _ ∈ Formalism.L2.DIV.lev _ _ _ _
    refine ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hSt, fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
    · obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
      obtain rfl : (pl i).1 = PP := congrArg Subtype.val hi
      rw [hr]
      exact hbt i
    · rw [hQ PP hPP]; exact one_mem _
    · rw [hrT]; exact hgH
  · unfold Lev.levChi levFn
    rw [hrT]
    have e1 : ext1 ((pk W).datYt t j (lvP W)).P.H ((pk W).datYt t j (lvP W)).P.chi g = ∏ i, (G i).S.P.lam (x₀ i) :=
      (extendOne_of_mem (P := (lvP W).H) (lvP W).chi hgH).trans hchi
    have e2 : ∏ PP ∈ ((pk W).datYt t j (lvP W)).Q, ((pk W).datYt t j (lvP W)).xq PP (dBlk (blk2 ((pk W).datYt t j (lvP W)).r) 1
        (redFn ((pk W).βY j) PP (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)))) = 1 :=
      Finset.prod_eq_one fun PP hPP => by rw [hQ PP hPP, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
    have e3 : ∏ PP ∈ ((pk W).datYt t j (lvP W)).Pg, ∏ c ∈ Finset.range ((pk W).datYt t j (lvP W)).s,
        ((pk W).datYt t j (lvP W)).cg (c + 1) PP (dBlk (blkOf ((pk W).datYt t j (lvP W)).r ((pk W).datYt t j (lvP W)).t) (c + 1)
          (redFn ((pk W).βY j) PP (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)))) =
        ∏ i, ∏ c ∈ Finset.range j, (pk W).chi (c + 1) (pl i).1
          (dBlk (blkOf D.R.r D.R.t) (c + 1) (Formalism.UG.bc (resS D.host.F (pl i).1) Y)) := by
      simp only [hr]
      rw [← Finset.prod_coe_sort]
      exact (Fintype.prod_equiv pl _ _ fun i => rfl).symm
    rw [e1, e2, e3, mul_one, ← Finset.prod_mul_distrib, Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => congrArg Units.val (hlam i).symm

theorem main : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GPin G → GRead f G pl → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), (f.t t).Is → F.Pins w → QLev f F → (∀ i, (G i).Chars (f.t t)) → (∀ j, j < D.R.m → ∀ (X : (f.t t).CC j) x, ∀ a ∈ GinfC _, (∀ i, (F.Q i).Typed j (rTrans (a * v.b j) (X.1 x))) ∧ ∀ κ, GlobalTheory.FinPl.InK _ (v.N j) (offP v w) κ → rTrans κ (rTrans (a * v.b j) (X.1 x)) = rTrans (a * v.b j) (X.1 x)) ∧ (∀ j, j + 1 < D.R.m → ∀ k ∈ v.JG (j + 1), ∃ a : ℂ, a ≠ 0 ∧ (∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) g → (f.t t).om j (1, k) (comb f.c.ψ _ _ (v.eG j) g) = a⁻¹ • comb f.c.ψ _ _ (v.eG j) g) ∧ (j + 1 + 1 < D.R.m → ∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) g → (f.t t).om (j + 1) (k, 1) (comb f.c.ψ _ _ (v.eG (j + 1)) g) = a • comb f.c.ψ _ _ (v.eG (j + 1)) g) ∧ ∀ (X : (f.t t).CC (j + 1)) x, rTrans k (rTrans (v.b (j + 1)) (X.1 x)) = a • rTrans (v.b (j + 1)) (X.1 x)) ∧ TopSph (t := f.t t) v := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch
  have hθ : IsInfFam f.c.θ := W.Q.charW.base.models.inf
  have hc : IsStdChar D f.c.ψ (-1) := W.Q.stdChar
  have hGLv := fun j (hj : j + 1 < D.R.m) k hk a ha => g_lev hv hV hGP hGR t (j + 1) hj k hk a ha
  refine ⟨fun j hj X x a ha => ⟨fun i => ?_, fun κ hκ => ?_⟩, fun j hj k hk => ?_, fun X x κ hκ => ?_⟩
  · intro d h y
    have hKO := (F.Q i).le j d h y.2
    have hm := (hQL.mid i j d h hj y.1 hKO)
    have hgf : (F.Q i).gl j d h y.1 ∈ GfC _ :=
      GlobalTheory.WeilProduct.mem_GfC_of_suppAt (F.Q i).q.split ((F.Q i).gl_loc j d h y.1).1
    rw [hV.b j, rTrans_lev hθ _ _ _ _ X.2 x ha hgf ((hm.1).2 y.2), hm.2 y.2]
  · have hκf : κ ∈ GfC _ := GlobalTheory.LevelCut.mem_GfC_of_grpAt _ _ κ hκ.1
    have ho := off_lev D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch j hj κ hκ
    rw [hV.b j, rTrans_lev hθ _ _ _ _ X.2 x ha hκf ho.1, ho.2, one_smul]
  · obtain ⟨r, hr⟩ := D.R.m_even
    have third : ∀ (X : (f.t t).CC (j + 1)) x (a : ℂ), GLam G (j + 1) k a →
        rTrans k (rTrans (v.b (j + 1)) (X.1 x)) = a • rTrans (v.b (j + 1)) (X.1 x) := by
      intro X x a hga
      have hkf : k ∈ GfC _ := GlobalTheory.LevelCut.mem_GfC_of_grpAt _ _ k ((hv.JG (j + 1) hj).1 hk)
      have ho := hGLv j hj k hk a hga
      rw [hV.b (j + 1), rightTranslate_level_conj_acts_by_character_finite hθ _ _ _ _ X.2 x hkf ho.1, ho.2]
    have uniq : ∀ a a', GLam G (j + 1) k a → GLam G (j + 1) k a' → a = a' := fun a a' h h' =>
      (hGLv j hj k hk a h).2.symm.trans (hGLv j hj k hk a' h').2
    rcases Nat.even_or_odd j with ⟨q, hq⟩ | ⟨q, hq⟩
    · obtain ⟨σ, hσ⟩ : ∃ σ, j + 2 * σ + 2 = D.R.m := ⟨(D.R.m - j - 2) / 2, by omega⟩
      have LL := GlobalTheory.RowLevel.Std.lift_laws D f.c v n G hc hv hGP (f.t t) ht hch j σ hσ
      obtain ⟨a, ha0, hga, hlaw⟩ := LL.1 k hk
      refine ⟨a, ha0, hlaw, fun hj2 => ?_, fun X x => third X x a hga⟩
      obtain ⟨a', -, hga', hlaw'⟩ := (LL.2.2 (by omega)).2 k hk
      rw [uniq a a' hga hga']
      exact hlaw'
    · obtain ⟨j₀, rfl⟩ : ∃ j₀, j = j₀ + 1 := ⟨2 * q, by omega⟩
      obtain ⟨σ, hσ⟩ : ∃ σ, j₀ + 2 * (σ + 1) + 2 = D.R.m := ⟨(D.R.m - j₀ - 4) / 2, by omega⟩
      have LL := GlobalTheory.RowLevel.Std.lift_laws D f.c v n G hc hv hGP (f.t t) ht hch j₀ (σ + 1) hσ
      obtain ⟨a, ha0, hga, hlaw⟩ := (LL.2.2 (by omega)).1 k hk
      refine ⟨a, ha0, hlaw, fun hj2 => ?_, fun X x => third X x a hga⟩
      have LL' := GlobalTheory.RowLevel.Std.lift_laws D f.c v n G hc hv hGP (f.t t) ht hch (j₀ + 1 + 1) σ (by omega)
      obtain ⟨a', -, hga', hlaw'⟩ := LL'.2.1 k hk
      rw [uniq a a' hga hga']
      exact hlaw'
  · have hκf : κ ∈ GfC _ := GlobalTheory.LevelCut.mem_GfC_of_grpAt _ _ κ hκ.1
    have ho := top_lev D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch κ hκ
    rw [hV.bT.1, rightTranslate_level_conj_acts_by_character_finite hθ _ _ _ _ X.2 x hκf ho.1, ho.2, one_smul]

end GlobalTheory.RowLevel

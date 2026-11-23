import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuadraticFamilyLevelIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GVec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
namespace GlobalTheory.RowLevel
theorem off_lev_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), (f.t t).Is → F.Pins w → _root_.GlobalTheory.Fam.QLevAlt f F → (∀ i, (G i).Chars (f.t t)) → ∀ j, j < D.R.m → ∀ κ, GlobalTheory.FinPl.InK _ (v.N j) (offP v w) κ → (f.g.b j)⁻¹ * κ * f.g.b j ∈ levS _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ∧ levChi _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((f.g.b j)⁻¹ * κ * f.g.b j) = 1 := by
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
theorem top_lev_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), (f.t t).Is → F.Pins w → _root_.GlobalTheory.Fam.QLevAlt f F → (∀ i, (G i).Chars (f.t t)) → ∀ κ, GlobalTheory.FinPl.InK f.c.T v.NT (· ∈ v.tP) κ → f.g.bT⁻¹ * κ * f.g.bT ∈ levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) ∧ levChi _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) (f.g.bT⁻¹ * κ * f.g.bT) = 1 := by
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
end Loc
set_option maxHeartbeats 1000000 in
theorem g_lev_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} {f : _root_.GlobalTheory.Fam.FamilyCharacter W u}
    {v : VCom f.c} (hv : v.Is) (hV : _root_.GlobalTheory.Fam.CommutingVectorTie f v) {n : ℕ} {G : Fin n → GLoc v} {pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg} (hGP : GPin G)
    (hGR : _root_.GlobalTheory.Fam.LocalGroupReading f G pl) (t : W.P.T) (j : ℕ) (hj : j < D.R.m) (k : GA D (Yc D j)) (hk : k ∈ v.JG j) (a : ℂ) (ha : GLam G j k a) :
    (f.g.b j)⁻¹ * k * f.g.b j ∈ levS _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ∧
      levChi _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((f.g.b j)⁻¹ * k * f.g.b j) = a := by
  have hlev := W.Q.charW.base.lev
  have hΛ := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hlev.βY j hj)
  obtain ⟨c0, hfr, -⟩ := hlev.βY j hj
  obtain ⟨hkg, hkJ⟩ := (hGP.lev j hj k).1 hk
  obtain ⟨hkf, hkS⟩ := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff _ _ k).1 hkg
  obtain ⟨c, hc, x, hxM, rfl⟩ := ha
  have hb : f.g.b j ∈ GfC (Yc D j) := hV.b j ▸ hv.b j
  choose e he hmv using fun i => hGR.frame i j (c i) (hc i)
  choose π h1 h2 h3 h4 using fun i => GlobalTheory.LocMod.LevBack.exists_chart (G i).q (hGR.idem i).1
  have hSt : Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j) ∈ St ((_root_.GlobalTheory.Fam.pk_z W).βY j) := by
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
  have hQ : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, redFn ((_root_.GlobalTheory.Fam.pk_z W).βY j) PP (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)) = 1 := fun PP hPP => by
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
      ((_root_.GlobalTheory.Fam.pk_z W).βY j)⁻¹ * Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j) * (_root_.GlobalTheory.Fam.pk_z W).βY j := by
    rw [← hY]
    change _ = ((_root_.GlobalTheory.Fam.pk_z W).βY j)⁻¹ * ((_root_.GlobalTheory.Fam.pk_z W).βY j * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype Y * ((_root_.GlobalTheory.Fam.pk_z W).βY j)⁻¹) * (_root_.GlobalTheory.Fam.pk_z W).βY j
    group
  have hall := fun i => by
    haveI : Nontrivial (kP (pl i).1) := Ideal.Quotient.nontrivial_iff.2 (pl i).1.isPrime.ne_top
    have hs := (G i).hs
    have hγ := mat_frame (G i).q (π i) (h1 i) ((G i).FY j (c i) (hc i))
      (typeFrame (G i).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (c i) (hc i))) (e i) (hmv i) (x i).1 (hxM i)
    exact red_lam (G i).S (r := D.R.r) (by unfold Ranks.r; omega) (r_le_Y j) (he i) (resS D.host.F (pl i).1)
      ((π i).comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (h3 i) (h4 i) (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1)
      (fun c hc z y x' hy hx => chi_eq_mu (_root_.GlobalTheory.Fam.pk_z W).toLevCh hlev (G i).q (pl i).2 (hGR.idem i).1 (π i) (h1 i) (h3 i) (h4 i) c
        (by omega) _ (hGR.mu i (c + 1) (by omega) (by omega)) ((G i).S.tame _) z y x' hy hx) Y
      ⟨(typeFrame (G i).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (c i) (hc i))).conj.symm (x i).1, (x i).2⟩ (fun a b => by
        have e1 := congrArg (fun g : GL _ _ => g.val (e i a) (e i b)) hγ
        simp only [reGL_val, submatrix_apply, Equiv.symm_apply_apply] at e1
        refine Eq.trans ?_ e1
        exact congrArg (π i) (congrArg (fun g : GL _ _ => g.val (e i a) (e i b)) hYv))
  choose hbt x₀ hred hlam using hall
  have hr : ∀ PP, redFn ((_root_.GlobalTheory.Fam.pk_z W).βY j) PP (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)) = Formalism.UG.bc (resS D.host.F PP) Y :=
    fun PP => by rw [← hY, redFn_frGL]
  obtain ⟨g, hg⟩ : ∃ g : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, GL (Fin D.R.r) (kP PP.1),
    ∀ PP, g PP = upperLeftBlock (r_le_Y j) (Formalism.UG.bc (resS D.host.F PP.1) Y) := ⟨_, fun _ => rfl⟩
  have hrT : rTup ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)) = g := by
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
  have hgH : g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := (hGR.lev g).1.2 fun i => ⟨x₀ i, hR i⟩
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
    have e1 : ext1 ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).P.H ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).P.chi g = ∏ i, (G i).S.P.lam (x₀ i) :=
      (extendOne_of_mem (P := (_root_.GlobalTheory.Fam.complexLevelStructure W).H) (_root_.GlobalTheory.Fam.complexLevelStructure W).chi hgH).trans hchi
    have e2 : ∏ PP ∈ ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).Q, ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).xq PP (dBlk (blk2 ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).r) 1
        (redFn ((_root_.GlobalTheory.Fam.pk_z W).βY j) PP (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)))) = 1 :=
      Finset.prod_eq_one fun PP hPP => by rw [hQ PP hPP, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
    have e3 : ∏ PP ∈ ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).Pg, ∏ c ∈ Finset.range ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).s,
        ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).cg (c + 1) PP (dBlk (blkOf ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).r ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).t) (c + 1)
          (redFn ((_root_.GlobalTheory.Fam.pk_z W).βY j) PP (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)))) =
        ∏ i, ∏ c ∈ Finset.range j, (_root_.GlobalTheory.Fam.pk_z W).chi (c + 1) (pl i).1
          (dBlk (blkOf D.R.r D.R.t) (c + 1) (Formalism.UG.bc (resS D.host.F (pl i).1) Y)) := by
      simp only [hr]
      rw [← Finset.prod_coe_sort]
      exact (Fintype.prod_equiv pl _ _ fun i => rfl).symm
    rw [e1, e2, e3, mul_one, ← Finset.prod_mul_distrib, Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => congrArg Units.val (hlam i).symm
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), (f.t t).Is → F.Pins w → _root_.GlobalTheory.Fam.QLevAlt f F → (∀ i, (G i).Chars (f.t t)) → (∀ j, j < D.R.m → ∀ (X : (f.t t).CC j) x, ∀ a ∈ GinfC _, (∀ i, (F.Q i).Typed j (rTrans (a * v.b j) (X.1 x))) ∧ ∀ κ, GlobalTheory.FinPl.InK _ (v.N j) (offP v w) κ → rTrans κ (rTrans (a * v.b j) (X.1 x)) = rTrans (a * v.b j) (X.1 x)) ∧ (∀ j, j + 1 < D.R.m → ∀ k ∈ v.JG (j + 1), ∃ a : ℂ, a ≠ 0 ∧ (∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) g → (f.t t).om j (1, k) (comb f.c.ψ _ _ (v.eG j) g) = a⁻¹ • comb f.c.ψ _ _ (v.eG j) g) ∧ (j + 1 + 1 < D.R.m → ∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) g → (f.t t).om (j + 1) (k, 1) (comb f.c.ψ _ _ (v.eG (j + 1)) g) = a • comb f.c.ψ _ _ (v.eG (j + 1)) g) ∧ ∀ (X : (f.t t).CC (j + 1)) x, rTrans k (rTrans (v.b (j + 1)) (X.1 x)) = a • rTrans (v.b (j + 1)) (X.1 x)) ∧ TopSph (t := f.t t) v := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch
  have hθ : IsInfFam f.c.θ := W.Q.charW.base.models.inf
  have hc : IsStdChar D f.c.ψ (-1) := W.Q.stdChar
  have hGLv := fun j (hj : j + 1 < D.R.m) k hk a ha => _root_.GlobalTheory.RowLevel.g_lev_alt hv hV hGP hGR t (j + 1) hj k hk a ha
  refine ⟨fun j hj X x a ha => ⟨fun i => ?_, fun κ hκ => ?_⟩, fun j hj k hk => ?_, fun X x κ hκ => ?_⟩
  · intro d h y
    have hKO := (F.Q i).le j d h y.2
    have hm := (hQL.mid i j d h hj y.1 hKO)
    have hgf : (F.Q i).gl j d h y.1 ∈ GfC _ :=
      GlobalTheory.WeilProduct.mem_GfC_of_suppAt (F.Q i).q.split ((F.Q i).gl_loc j d h y.1).1
    rw [hV.b j, rTrans_lev hθ _ _ _ _ X.2 x ha hgf ((hm.1).2 y.2), hm.2 y.2]
  · have hκf : κ ∈ GfC _ := GlobalTheory.LevelCut.mem_GfC_of_grpAt _ _ κ hκ.1
    have ho := _root_.GlobalTheory.RowLevel.off_lev_alt D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch j hj κ hκ
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
    have ho := _root_.GlobalTheory.RowLevel.top_lev_alt D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch κ hκ
    rw [hV.bT.1, rightTranslate_level_conj_acts_by_character_finite hθ _ _ _ _ X.2 x hκf ho.1, ho.2, one_smul]
end GlobalTheory.RowLevel
end

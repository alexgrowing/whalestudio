import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepBeforeLastEqSSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelLeCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiStdEqConstMulLocXi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelLocalGroupEqOfAgreeOffPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesEqIffReductionEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotTopPtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
section Gen

open Formalism.L2.Col Formalism.L2.Ker Formalism.UG GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart

namespace GlobalTheory.PenLevTyp

theorem commute_of_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} {x k : GL (Fin n) (AfE F E)} (hx : ∀ w, w ≠ v → bc (prV (E := E) w) x = 1)
    (hk : bc (prV (E := E) v) k = 1) : x * k = k * x := by
  have key : ∀ w, bc (prV (E := E) w) (x * k) = bc (prV (E := E) w) (k * x) := fun w => by
    rw [map_mul, map_mul]
    by_cases hw : w = v
    · subst hw
      rw [hk, mul_one, one_mul]
    · rw [hx w hw, mul_one, one_mul]
  apply Units.ext
  ext r s
  refine sub_eq_zero.1 (Formalism.UG.P.afsplit_inj _ fun w => ?_)
  rw [map_sub, sub_eq_zero]
  exact congrArg (fun g : GL (Fin n) _ => g.1 r s) (key w)

theorem fr_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g g' : GL (Fin n) (AfE F E)}
    {p p' : DecoF E n ST SG Q} (h : IsPtOf hc g p) (h' : IsPtOf hc g' p') (P : Q)
    (e0 : ∀ i j, adAt F P.1 (g.1 i j) = adAt F P.1 (g'.1 i j)) : p.fr P = p'.fr P := by
  have e : ∀ i j, p.fr P (Pi.single j 1) i = p'.fr P (Pi.single j 1) i := fun i j =>
    (algebraMap E (P.1.adicCompletion E)).injective ((h.fr P i j).symm.trans ((e0 i j).trans (h'.fr P i j)))
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.pi_ext fun j x => ?_
  have hs : (Pi.single j x : Sp E n) = x • Pi.single j 1 := by
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  simp only [LinearEquiv.coe_coe]
  rw [hs, map_smul, map_smul]
  funext i
  simp only [Pi.smul_apply, e]

theorem exists_pt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g g' : GL (Fin n) (AfE F E)}
    {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (hg' : g' ∈ UAd hc n)
    (e0 : ∀ P ∈ Q, ∀ i j, adAt F P (g'.1 i j) = adAt F P (g.1 i j)) : ∃ p' : DecoF E n ST SG Q, IsPtOf hc g' p' := by
  refine GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat hc ST SG Q g' hg' fun P hP => ?_
  let f := p.fr ⟨P, hP⟩
  refine ⟨⟨LinearMap.toMatrix' f.toLinearMap, LinearMap.toMatrix' f.symm.toLinearMap, ?_, ?_⟩, fun r s => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]
  · rw [e0 P hP, h.fr ⟨P, hP⟩ r s]
    simp only [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
    rfl

section Pt

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S S' : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {mu' : Tup X.F X.E X.K S'} {cst' : LocCst X (rowSG Pr sel mu')}
  {u : Pr.Word} {j : ℕ}

theorem coset_at (q : PtAt R sel mu cst u j) (h : j + 1 = R.m) {y : Sp X.E (R.N j)} (hy0 : y ∈ q.1.2) (w : Pr.vGs) :
    cosetIn q ⟨w.1, Finset.mem_union_left _ w.2⟩ = {z | z - (q.1.1.deco.1.liftFr w).symm y ∈ stdAt X.E (R.N j) w.1} ∧
      ((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y ∈ stdAt X.E (R.N j) w.1 ∧
      bar q w = {redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y)} := by
  obtain ⟨y₀, hy₀, hY⟩ := q.mem_ybSet h
  have hd := q.1.1.deco.2
  have hf := GlobalTheory.TopStep.liftFr_spec hd w
  have h1 : ((qOf w.1 : ℕ) : X.E) • y₀ ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal q.1.1.deco.1.N := by
    have := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy₀ ⟨w.1, Finset.mem_union_left _ w.2⟩
    simpa [w.2] using this
  have h2 : ∀ z ∈ q.1.2, z - y₀ ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal q.1.1.deco.1.N := fun z hz => by
    rw [hY, Set.mem_setOf_eq, Formalism.L2.Col.mem_locLat] at hz
    simpa [w.2] using hz ⟨w.1, Finset.mem_union_left _ w.2⟩
  have h3 : ∀ z ∈ q.1.2, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal q.1.1.deco.1.N := fun z hz => by
    have := sub_mem (h2 z hz) (h2 y hy0)
    rwa [sub_sub_sub_cancel_right] at this
  have hq : ((qOf w.1 : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal q.1.1.deco.1.N := by
    have := add_mem h1 (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat (qOf w.1)) (h2 y hy0))
    rwa [← smul_add, add_sub_cancel] at this
  have hs : (q.1.1.deco.1.liftFr w).symm (((qOf w.1 : ℕ) : X.E) • y) ∈ stdAt X.E _ w.1 :=
    (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hq)
  refine ⟨?_, by rw [← map_smul]; exact hs, ?_⟩
  · have hfr : frsF sel mu q.1.1 ⟨w.1, Finset.mem_union_left _ w.2⟩ = q.1.1.deco.1.liftFr w := dif_pos w.2
    ext z
    simp only [cosetIn, Set.mem_setOf_eq, if_pos w.2, pow_zero, inv_one, one_smul, hfr]
    constructor
    · rintro ⟨y', hy', hz⟩
      have h1 : (q.1.1.deco.1.liftFr w).symm y' - (q.1.1.deco.1.liftFr w).symm y ∈ stdAt X.E (R.N j) w.1 := by
        rw [← map_sub]
        exact (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact h3 y' hy')
      have := add_mem hz h1
      rwa [sub_add_sub_cancel] at this
    · exact fun hz => ⟨y, hy0, hz⟩
  · have key : q.1.1.deco.1.be w (((qOf w.1 : ℕ) : X.E) • y) =
        redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y) := by
      rw [← map_smul, ← hf.2 _ hs, LinearEquiv.apply_symm_apply]
    ext v
    simp only [bar, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← key]
      have ht : z - y ∈ q.1.1.deco.1.at w.1 := h3 z hz
      have e : ((qOf w.1 : ℕ) : X.E) • z = ((qOf w.1 : ℕ) : X.E) • y + ((qOf w.1 : ℕ) : X.E) • (z - y) := by
        rw [← smul_add, add_sub_cancel]
      rw [e, hd.be_add w _ hq _ (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) ht),
        GlobalTheory.TopStep.be_smul_int hd w (GlobalTheory.TopStep.intAt_nat _) ht, GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul, add_zero]
    · rintro rfl
      exact ⟨y, hy0, key.symm⟩

theorem cos_iff_bar (h : j + 1 = R.m) (w : Pr.vGs) (hq : ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2) (q : PtAt R sel mu cst u j)
    (q' : PtAt R sel mu' cst' u j) :
    cosetIn q ⟨w.1, Finset.mem_union_left _ w.2⟩ = cosetIn q' ⟨w.1, Finset.mem_union_left _ w.2⟩ ↔ bar q w = bar q' w := by
  obtain ⟨h1, h2, h3⟩ := coset_at q h (q.repY_mem h) w
  obtain ⟨h1', h2', h3'⟩ := coset_at q' h (q'.repY_mem h) w
  rw [h1, h1', h3, h3', Set.singleton_eq_singleton_iff]
  exact coset_eq_iff_redV hq h2 h2'

end Pt

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)

theorem levGAt_eq (hTw : I.IsTw) (a : I.ι) (j : ℕ) (hj : j < B.R.m) (b : Idx I.sel (I.tup a) (I.idx a) j) :
    levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = colLevSym I.Ch j := by
  have h1 : levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = (I.idx a).levG j (b.get hj) := by
    unfold levGAt
    rw [← Idx.some_get b hj]
    rfl
  have h2 : ∀ b', (I.idx a).levG j b' = colLevSym I.Ch j := by
    rw [(hTw a).2]
    exact fun _ => rfl
  rw [h1, h2]

set_option maxHeartbeats 2000000 in

theorem mem_lev_iff (hI : I.Ok) (hTw : I.IsTw) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (j : ℕ) (hj : j + 1 = B.R.m)
    [NeZero (B.R.N j)] {Ch : Type} {chOf : (I.stp u a j).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N j) → B.host.E)} {U : Ch → Subgroup (TC.GA B (B.R.N j))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a j).Cl → TC.GA B (B.R.N j)} {st : ∀ c, (I.stp u a j).Stab c → GL (Fin (B.R.N j)) B.host.E}
    {k : Ch → TC.GA B (B.R.N j)} (hR : I.Reads u a j chOf Lb U chi y st k) (c : (I.stp u a j).Cl)
    (x : TC.GA B (B.R.N j)) (hx : x ∈ UAd B.sp.cm (B.R.N j)) (hc : x * k (chOf c) = k (chOf c) * x)
    (hc₀ : x * TC.kStd X u (B.R.N j) = TC.kStd X u (B.R.N j) * x)
    (h1 : ∀ P ∈ I.Q a, x.1.map (adAt B.host.F P) = 1) :
    x ∈ U (chOf c) ↔ x ∈ levU (F := B.host.F) B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs
      (chG (X := B.fields) (colLevSym I.Ch j) (bar (show PtAt B.R I.sel (I.tup a) (I.cst a) u j from (I.stp u a j).rep c))) := by
  have hy0 : IsPtOf B.sp.cm (y c * k (chOf c)) ((I.stp u a j).rep c).1.1 :=
    IsPtOf.of_extTo (I.Q_subset_SQ a)
      ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a)) (hR.pt c)
  obtain ⟨g, hgd⟩ : ∃ g, g * TC.kStd X u (B.R.N j) = y c * k (chOf c) := ⟨_, inv_mul_cancel_right _ _⟩
  have hgx : g * x * TC.kStd X u (B.R.N j) = y c * x * k (chOf c) := by
    rw [mul_assoc, hc₀, ← mul_assoc, hgd, mul_assoc, ← hc, mul_assoc]
  rw [← hgd] at hy0
  have hg := dia_of_pt hPr u hy0
  have hk : TC.kStd X u (B.R.N j) ∈ UAd B.sp.cm (B.R.N j) := (kStd_spec hPr u (B.R.N j)).1.choose_spec.1.uni
  have e0 : ∀ P ∈ I.Q a, ∀ r s, adAt B.host.F P ((g * x * TC.kStd X u (B.R.N j)).1 r s) =
      adAt B.host.F P ((g * TC.kStd X u (B.R.N j)).1 r s) := fun P hP r s => by
    have e' : (g * x * TC.kStd X u (B.R.N j)).1.map (adAt B.host.F P) = (g * TC.kStd X u (B.R.N j)).1.map (adAt B.host.F P) := by
      rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, h1 P hP, Matrix.mul_one]
    exact congrFun (congrFun e' r) s
  obtain ⟨q, hq⟩ := exists_pt hy0 (mul_mem (mul_mem hg.1 hx) hk) e0
  have hfr : ∀ P, q.fr P = ((I.stp u a j).rep c).1.1.fr P := fun P => fr_eq hq hy0 P (e0 P.1 P.2)
  have hxq := dia_of_pt hPr u hq
  have hΛ := levGAt_eq I hTw a j (by omega) c.1
  rw [hR.lev c x q (by rw [← hgx]; exact hq)]
  constructor
  · rintro ⟨κ, h1, h2, h3⟩
    have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N j) (h1.trans (map_one _).symm)
    obtain ⟨hJ, hr⟩ := red_of_act B.sp.cm (B.R.N j) (diaT (Pr := B.primes X) u) hg.1 hxq.1 κ.2.1.1 (by
      rw [hg.2, hxq.2, ← h2]
      show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N j) × GLG B.fields.E (B.R.N j) (B.primes X).vGs) • _ = _
      rw [e1]
      rfl)
    refine (mem_levU _ _ _ _ _).2 ⟨hJ, ?_⟩
    have key : ∀ (Λ' : LevFam B.fields.E B.fields.K (B.R.N j) (B.primes X).vGs), Λ' = colLevSym I.Ch j →
        ∀ g : Λ'.grp, g.1 ∈ (colLevSym I.Ch j).grp := by
      rintro _ rfl g
      exact g.2
    rw [hr]
    refine inv_mem (mem_chG.2 ⟨key _ hΛ κ.2.1, (bar_ya_eq_iff (X := B.fields) _ _ κ _).1 (funext fun w => ?_)⟩)
    exact (cos_iff_bar hj w (hqG hPr w.1 w.2) _ _).1 (congrFun h3 _)
  · intro hxU
    have h2 := act_of_mem B.sp.cm (B.R.N j) _ (diaT (Pr := B.primes X) u) hg.1 ⟨x, hxU⟩
    rw [hg.2, hxq.2] at h2
    have hm0 := mem_chG.1 ((levRed B.sp.cm (B.R.N j) _ _ _ ⟨x, hxU⟩)⁻¹).2
    have hm : ((levRed B.sp.cm (B.R.N j) _ _ _ ⟨x, hxU⟩)⁻¹).1 ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j c.1).grp := by
      rw [hΛ]
      exact hm0.1
    have h3 : ((I.stp u a j).act c.1 (1, ⟨_, hm⟩, 1) ((I.stp u a j).rep c)).1.1 = q := by
      refine Subtype.ext (Prod.ext h2.symm (funext fun P => ?_))
      show (1 : _ ≃ₗ[B.fields.E] _) * ((I.stp u a j).rep c).1.1.fr P * (1 : _ ≃ₗ[B.fields.E] _) = q.fr P
      rw [one_mul, mul_one, hfr]
    refine ⟨(1, ⟨_, hm⟩, 1), map_one (ufGL B.host.E (B.R.N j)), h3, funext fun P => ?_⟩
    by_cases hP : P.1 ∈ (B.primes X).vGs
    · exact (cos_iff_bar hj ⟨P.1, hP⟩ (hqG hPr P.1 hP) _ _).2 (congrFun
        ((bar_ya_eq_iff (X := B.fields) _ (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) j c.1) (1, ⟨_, hm⟩, 1) _).2 hm0.2) _)
    · have h4 : ((I.stp u a j).act c.1 (1, ⟨_, hm⟩, 1) ((I.stp u a j).rep c)).1.2 = ((I.stp u a j).rep c).1.2 := Set.image_id _
      unfold cosetIn
      rw [h3, h4]
      unfold frsF
      rw [dif_neg hP, dif_neg hP, hfr]

end GlobalTheory.PenLevTyp

end Gen
end

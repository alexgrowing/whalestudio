import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BuiltCols
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvLgCanonical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsRowValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivHermitianFrameNormAtComplexPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroColumnsClassSumFormPosDefStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsPrescribedUnitaryFormsStandInsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDivStageStandIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitsOrderOfEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCombOfMemClosureFinset
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Df

namespace GlobalTheory.Core.Rk.TrueModel

attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem map_mem_span_image {K : Type} [Field K] (σ : K →+* ℂ) {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[σ] W) (S : Set V) {x : V} (hx : x ∈ Submodule.span K S) :
    j x ∈ Submodule.span ℂ (j '' S) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul k y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem span_image_eq_top {K : Type} [Field K] (σ : K →+* ℂ) {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[σ] W) {ι : Type} (b : Module.Basis ι K V) (S : Set V)
    (hS : Submodule.span K S = ⊤) (hb : Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤) :
    Submodule.span ℂ (j '' S) = ⊤ := by
  rw [eq_top_iff, ← hb, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact map_mem_span_image σ j S (by rw [hS]; exact Submodule.mem_top)

theorem rowsDef_ex : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok), Nonempty (RowsDef I l hX) := by
  intro B X I hI hP l hX
  classical
  have hb := fun a => Df.mtHL_good_basis I hX a
  choose j hj using fun a => (hb a).2.1
  have hA := fun a => GlobalTheory.T.exists_equiv_hermitianFrameNorm_at_complexPlace B.LL B.embLL (MtHL I hX a) (MtCx I a) (j a) (hb a).1.1
    (by simpa only [hj] using (hb a).2.2.1) (by simpa only [hj] using (hb a).2.2.2)
  choose n gA hgA using hA
  have hme : ∀ u a, ∃ m : MtCx I a ≃ₗ[ℂ] (I.per l u a).Mt, ∀ F, SameForm I l u a F (m F) :=
    fun u a => ⟨PerQ.Model.mtE I l hI u a, fun _ _ => rfl⟩
  choose mq hmq using hme
  let jj : ∀ a, (MtHL I hX a).V →ₛₗ[B.embLL] EuclideanSpace ℂ (Fin (n a)) := fun a => (gA a).toLinearMap.comp (j a)
  letI : ∀ a, Module (𝓞 B.LL) (MtHL I hX a).V := fun a => (MtHL I hX a).modOV
  haveI : ∀ a, IsScalarTower (𝓞 B.LL) B.LL (MtHL I hX a).V := fun a => (MtHL I hX a).towV
  have hL := fun a => GlobalTheory.exists_oLat_of_fg_ringOfIntegers B.O B.LL B.OtoLL B.embLL (MtHL I hX a).V
    (EuclideanSpace ℂ (Fin (n a))) (jj a) (MtHL I hX a).L B.O_int (hb a).1.2.1
    (span_image_eq_top B.embLL (jj a) (MtHL I hX a).b _ (hb a).1.2.2 (by
      have h2 := (hb a).2.2.2
      simp only [← hj] at h2
      have : (Set.range fun i => jj a ((MtHL I hX a).b i)) = (gA a).toLinearMap '' (Set.range fun i => j a ((MtHL I hX a).b i)) := by
        rw [← Set.range_comp]; rfl
      rw [this, ← Submodule.map_span, h2, Submodule.map_top, LinearEquiv.range]))
  choose L hLc hLg hLy hLs using hL
  let mt : B.places.Pl → (I.cols l).Tup := fun w => if B.places.resChar w = B.host.pde then I.muStar' else I.muStar
  have hmt : ∀ w, mt (B.places.conj w) = mt w := fun w => by
    simp only [mt, GlobalTheory.Mem.Top.TwFin.resChar_conj]
  obtain ⟨W, g, hstd, hmuAt, hmuTw, he0, heT, hcar, hgen, heOp, hze⟩ :=
    GlobalTheory.T.exists_rows_prescribedUnitaryForms_standIns B (I.cols l) n (fun u => (mq u I.mu0).symm.trans (gA I.mu0))
      (fun u a => (mq u a).symm.trans (gA a)) L mt hmt (GlobalTheory.T.stepZeroColumns_classSumForm_posDef I hI hP l hX)
  letI := W.instAmb
  letI := W.instAmbi
  refine ⟨⟨W, fun a => (gA a).trans (g a).toLinearEquiv, ?_, hstd⟩⟩
  refine
    { muAt := hmuAt
      muTw := hmuTw
      eMt0 := ?_
      eMtTw := ?_
      norm := ?_
      lat := ?_
      gen := ?_
      eOp := heOp
      ze := hze }
  · intro u F
    have h : W.eMt0 u (mq u I.mu0 F) = g (I.cols l).mu0 (gA I.mu0 F) :=
      (he0 u _).trans (congrArg (g (I.cols l).mu0) (congrArg (gA I.mu0) ((mq u I.mu0).symm_apply_apply F)))
    have h' : (W.eMt0 u).symm (g (I.cols l).mu0 (gA I.mu0 F)) = mq u I.mu0 F := by
      rw [← h]; exact (W.eMt0 u).symm_apply_apply _
    have hs := hmq u I.mu0 F
    rw [← h'] at hs
    exact hs
  · intro u a F
    have h : W.eMtTw u a (mq u a F) = g a (gA a F) :=
      (heT u a _).trans (congrArg (g a) (congrArg (gA a) ((mq u a).symm_apply_apply F)))
    have h' : (W.eMtTw u a).symm (g a (gA a F)) = mq u a F := by
      rw [← h]; exact (W.eMtTw u a).symm_apply_apply _
    have hs := hmq u a F
    rw [← h'] at hs
    exact hs
  · intro a x
    have h := (g a).norm_map (gA a (toCx I hX a x))
    exact (hgA a x).trans ((congrArg (fun z => ‖gA a z‖) (hj a x)).trans h.symm)
  · intro a y
    constructor
    · intro hy
      have hy' : g a ((g a).symm y) ∈ (W.Mtilde a).carrier := by simpa using hy
      obtain ⟨x, hx, hxy⟩ := (Set.ext_iff.1 (hLc a) _).1 ((hcar a _).1 hy')
      refine ⟨x, hx, ?_⟩
      have h1 : gA a (toCx I hX a x) = (g a).symm y := (congrArg (gA a) (hj a x)).symm.trans hxy
      have h2 : g a (gA a (toCx I hX a x)) = y := by rw [h1]; simp
      exact h2
    · rintro ⟨x, hx, rfl⟩
      have h1 : jj a x = gA a (toCx I hX a x) := congrArg (gA a) (hj a x)
      have h2 : g a (jj a x) ∈ (W.Mtilde a).carrier := (hcar a _).2 ((Set.ext_iff.1 (hLc a) _).2 ⟨x, hx, rfl⟩)
      rw [h1] at h2
      exact h2
  · intro a y hy
    have hy' : g a ((g a).symm y) ∈ (W.Mtilde a).gen := by simpa using hy
    have h1 := hLg a _ ((hgen a _).1 hy')
    have h2 : g a ((g a).symm y) ∈ (W.Mtilde a).carrier := (hcar a _).2 ((Set.ext_iff.1 (hLc a) _).2 h1)
    simpa using h2

set_option maxHeartbeats 1600000 in

theorem ambTrue_ex : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok), ∀ (Z : TC.Later B (I.cols l)) (e : ∀ a : (I.cols l).Tup, MtCx I a ≃ₗ[ℂ] Z.W.Amb a), DefTrue I l hX Z.W e → ∃ A : AmbForm (I.rec7 l Z) (RowSide.sharp (I.rec7 l Z)), AmbTrue I l hX Z e A := by
  intro B X I _ _ l hX Z e hD
  classical
  let j : ∀ a : (I.cols l).Tup, (MtHL I hX a).V →ₛₗ[B.embLL] MtCx I a := fun a => (Df.mtHL_good_basis I hX a).2.1.choose
  have hj : ∀ a x, j a x = toCx I hX a x := fun a => (Df.mtHL_good_basis I hX a).2.1.choose_spec
  let jA : ∀ a : (I.cols l).Tup, (MtHL I hX a).V →ₛₗ[B.embLL] Z.W.Amb a := fun a => (e a).toLinearMap.comp (j a)
  have hjA : ∀ a x, jA a x = e a (toCx I hX a x) := fun a x => by
    show e a (j a x) = _
    rw [hj]
  have hli : ∀ a, LinearIndependent ℂ (fun i => jA a ((MtHL I hX a).b i)) := fun a => by
    have h1 := (Df.mtHL_good_basis I hX a).2.2.1
    have h2 := h1.map' (e a).toLinearMap (LinearEquiv.ker _)
    have hf : (fun i => jA a ((MtHL I hX a).b i)) = (e a).toLinearMap ∘ (fun i => toCx I hX a ((MtHL I hX a).b i)) := by
      funext i
      simp only [Function.comp_apply, LinearEquiv.coe_coe]
      exact hjA a _
    rw [hf]
    exact h2
  have hspan : ∀ a, Submodule.span ℂ (Set.range (fun i => jA a ((MtHL I hX a).b i))) = ⊤ := fun a => by
    have h1 := (Df.mtHL_good_basis I hX a).2.2.2
    have hr : Set.range (fun i => jA a ((MtHL I hX a).b i)) = (e a).toLinearMap '' Set.range (fun i => toCx I hX a ((MtHL I hX a).b i)) := by
      rw [← Set.range_comp]
      congr 1
      funext i
      simp only [Function.comp_apply, LinearEquiv.coe_coe]
      exact hjA a _
    rw [hr, Submodule.span_image, h1, Submodule.map_top]
    exact LinearEquiv.range _
  have hinj : ∀ a, Function.Injective (jA a) := fun a => by
    rw [injective_iff_map_eq_zero]
    intro z hz
    set b := (MtHL I hX a).b
    have hsum : jA a z = ∑ i, B.embLL (b.repr z i) • jA a (b i) := by
      conv_lhs => rw [← b.sum_repr z]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smulₛₗ]
    rw [hsum] at hz
    have h0 := Fintype.linearIndependent_iff.mp (hli a) (fun i => B.embLL (b.repr z i)) hz
    have : b.repr z = 0 := by
      ext i
      have := h0 i
      simpa using this
    simpa using this
  refine ⟨⟨fun a => MtHL I hX a, jA, ?_, ?_, ?_, ?_, ?_⟩, ⟨fun a => ?_⟩⟩
  · intro μ _; exact (Df.mtHL_good_basis I hX μ).1
  · intro μ _; exact ⟨hli μ, hspan μ⟩
  · intro μ _ x
    have hlat := hD.lat μ
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := (hlat (jA μ x)).2 ⟨x, hx, (hjA μ x).symm⟩
      refine ⟨fun v => ⟨B.OtoLL (c v), (I.rec7 l Z).O_int (c v)⟩, ?_⟩
      exact hc
    · rintro ⟨c, hc⟩
      letI := Z.W.instAmb μ
      letI := Z.W.instAmbi μ
      have hg : ∀ v ∈ (Z.W.Mtilde μ).gen, ∃ y ∈ (MtHL I hX μ).L, jA μ y = v := fun v hv => by
        obtain ⟨y, hy, h⟩ := (hlat v).1 (hD.gen μ v hv)
        exact ⟨y, hy, (hjA μ y).trans h⟩
      choose! xv hxvL hxv using hg
      let c' : Z.W.Amb μ → 𝓞 B.LL := c
      have hmem : (∑ v ∈ (Z.W.Mtilde μ).gen, c' v • xv v) ∈ (MtHL I hX μ).L :=
        Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ (hxvL v hv)
      have heq : jA μ (∑ v ∈ (Z.W.Mtilde μ).gen, c' v • xv v) = jA μ x := by
        rw [map_sum]
        refine Eq.trans (Finset.sum_congr rfl fun v hv => ?_) hc.symm
        have hs : ((c' v : B.LL)) • xv v = c' v • xv v := by
          letI := (MtHL I hX μ).modOV
          haveI := (MtHL I hX μ).towV
          exact algebraMap_smul B.LL (c' v) (xv v)
        rw [← hs, map_smulₛₗ, hxv v hv]
        rfl
      rw [← hinj μ heq]
      exact hmem
  · intro μ _ v hv
    obtain ⟨x, _, h⟩ := (hD.lat μ v).1 (hD.gen μ v hv)
    exact ⟨x, (hjA μ x).trans h⟩
  · intro μ _ x
    have h := hD.norm μ x
    have h2 := hjA μ x
    rw [← h2] at h
    exact h
  · show (⟨MtHL I hX a, fun x => jA a x⟩ : Σ H : HLat B.LL, (H.V → Z.W.Amb a)) = _
    exact congrArg (Sigma.mk (MtHL I hX a)) (funext (hjA a))

theorem exists_choices : ∃ (B : Base) (X : PreX B.toPre) (I : TC B X), StagesInhab.HasLetters B.toPre ∧ I.Ok ∧ TC.Pins B X ∧
    I.IsTw ∧ ColIn.JetsIn I := by
  classical
  obtain ⟨P, X, f, hL, hX, hsp, hdu, p1, p2⟩ := TrueColsTest.exists_pre
  obtain ⟨M, hM, -, -, m1, m2, -⟩ := FrameVal.frame_values P.R P.host _ f fun j τ => (P.hc τ).e_int j
  obtain ⟨α, hα, gα⟩ := @DatHecke.exists_gen M hM
  choose r hr using fun q : ℕ => IsAlgClosed.exists_pow_nat_eq (q : ℂ) (n := 2) two_pos
  obtain ⟨Y, hY, gY⟩ := InEx.exists_holds (2 * P.R.m) ({1, f.del, f.del'} : Set (Formalism.L2.Host.HChar P.host.E))
  obtain ⟨B, rfl, -, -, h2⟩ := BaseExt.exists_base P ∅ ∅
    (insert α (Y ∪ Finset.univ.image fun k => r (P.host.g k)) ∪ TwIdxEx.gens P f.chiPsi {1, f.del, f.del'}) (by simp) (by simp)
    (fun z hz => by
      rcases Finset.mem_union.1 hz with hz | hz
      swap
      · exact TwIdxEx.gens_algebraic _ _ _ z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hα
      rcases Finset.mem_union.1 hz with h | h
      · exact hY z h
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 h
        exact IsAlgebraic.of_pow two_pos (by rw [hr]; exact isAlgebraic_natCast _))
  have h3 := fun z hz => h2 z (Finset.mem_union_right _ hz)
  replace h2 := fun z hz => h2 z (Finset.mem_union_left _ hz)
  have i1 := gα B.LL B.embLL (h2 _ (Finset.mem_insert_self _ _))
  have hf : ({1, f.del, f.del'} : Set (Formalism.L2.Host.HChar B.host.E)).Finite := Set.toFinite _
  have ht : ∀ ξ ∈ ({1, f.del, f.del'} : Set (Formalism.L2.Host.HChar B.host.E)), Chr.IsTwist B.host (InEx.avoid B.toPre) ξ :=
    fun ξ hξ => InEx.isTwist_of_mem_set B f (Top.TwDat.untw B ∅) ξ (.inl hξ)
  obtain ⟨sel, hsel⟩ := Formalism.L2.Col.exists_sel B.fields
  obtain ⟨I, a1, a2, -, a4, -, a6, a7⟩ := InEx.exists_colIn B X f hX hsp hdu (InEx.avoid B.toPre)
    (fun u => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Exists.intro u rfl))))), B.T_ne_pde u⟩)
    (fun i => ⟨Or.inr (Or.inl (Exists.intro i rfl)), (B.host.pde_ne_g i).1.symm, (B.host.pde_ne_g i).2.symm⟩)
    (fun _ hp h => InEx.mem_avoid_of_dvd _ hp h)
    _ hf (.inl rfl) (.inr (.inl rfl)) (.inr (.inr rfl)) ht
    (fun ξ hξ => gY hf B.LL B.embLL
      (fun z hz => h2 z (Finset.mem_insert_of_mem (Finset.mem_union_left _ hz))) ξ hξ (ht ξ hξ).1)
    (fun j => InEx.valuesIn_of (m1 j) _ i1) (InEx.valuesIn_of m2 _ i1) (fun i => by
      obtain ⟨s, hs⟩ := h2 _ (Finset.mem_insert_of_mem
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
      exact ⟨s, B.embLL.injective (by rw [map_pow, hs, hr, map_natCast])⟩) sel hsel (JetEx.amb0 B.host)
    (exists_ambIn_ok B.host).choose_spec
  subst a2
  have hk : (canon I).Ok := canon_ok a1 fun a P hP => ((a7 a).2.2.2 P hP).ge
  exact ⟨B, X, canon I, hL, hk, ⟨p1, p2⟩, canon_isTw I,
    TwIdxEx.jetsIn_of_isTw hL hk (canon_isTw I) a6 (by rw [← a4] at h3; exact h3)⟩

theorem exists_builtCols : ∃ D : D7, BuiltCols D := by
  obtain ⟨B, X, I, hL, h, hP, hT, hJ⟩ := exists_choices
  obtain ⟨Z⟩ := TrueColsTest.later (TrueColsTest.laws h) hL
  exact ⟨_, B, X, I, _, Z, h, hP, hT, hJ, rfl⟩

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws)

def rowJ (h : I.Ok) (u : B.Word) : (MtTrue I).V →ₛₗ[B.embLL] (I.per l u I.mu0).Mt :=
  PeriodOnStep.rowEmb (Pr := B.primes X) B.wts I.Ch I.sel (I.tup I.mu0) I.Ps (I := I.chIn u I.mu0) (I.perIn u I.mu0).b0
    (I.perIn u I.mu0).til (I.perIn u I.mu0).ext (I.perIn u I.mu0).tz (I.perIn u I.mu0).H
    (Finset.disjoint_right.2 (Q_notMem_of_ok h I.mu0)) B.embLL

theorem isRowEmb_rowJ (h : I.Ok) (u : B.Word) : IsRowEmb I l u (rowJ I l h u) := fun _ _ => rfl

theorem isRowEmb_unique {u : B.Word} {j j'} (h : IsRowEmb I l u j) (h' : IsRowEmb I l u j') : j = j' :=
  LinearMap.ext fun z => Subtype.ext (funext fun _ => funext fun p => (h z p).trans (h' z p).symm)

theorem isRowEmb_injective {u : B.Word} {j} (h : IsRowEmb I l u j) : Function.Injective j := by
  intro z z' e
  refine Subtype.ext (funext fun d => Subtype.ext ?_)
  obtain ⟨p, rfl⟩ := toRow_surjective I.sel (I.tup I.mu0) d
  exact MvPolynomial.map_injective B.embLL B.embLL.injective
    ((h z (trivPt B.fields _ _ _ _ p)).symm.trans ((congrArg (fun F : (I.per l u I.mu0).Mt => F.1 () (trivPt B.fields _ _ _ _ p)) e).trans
      (h z' (trivPt B.fields _ _ _ _ p))))

theorem isPerTrue_unique {u : B.Word} {j e e'} (h : IsPerTrue I l u j e) (h' : IsPerTrue I l u j e') : e = e' :=
  LinearMap.ext fun x => LinearMap.ext fun z => B.embLL.injective ((h x z).trans (h' x z).symm)

theorem exists_isPerTrue (h : I.Ok) (u : B.Word) : ∃ e, IsPerTrue I l u (rowJ I l h u) e := by
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  obtain ⟨κ, ι, -, -, e⟩ := PeriodOnStep.isConcrete_forms (Pr := B.primes X) B.wts I.Ch I.sel (I.tup I.mu0) I.Ps
    (I := I.chIn u I.mu0) (I.perIn u I.mu0).b0
    (I.perIn u I.mu0).til (I.perIn u I.mu0).ext (I.perIn u I.mu0).tz (I.perIn u I.mu0).H
    (Finset.disjoint_right.2 (Q_notMem_of_ok h I.mu0)) B.embLL hX (B.hcW u) (I.atIn u I.mu0) (I.fmIn l.pr u I.mu0)
    (l.ch u _) (l.lev u _) (l.per u _) (l.atL u _) (l.fmL u _) (l.ovr u _)
    (PeriodOnStep.isFormsOf_MtildeH (Pr := B.primes X) B.wts I.Ch I.sel (I.tup I.mu0) I.Ps hX)
  exact ⟨((PeriodClassSum.classSum (Pr := B.primes X) B.wts I.Ch I.sel (I.tup I.mu0) I.Ps _).compl₁₂ κ.toLinearMap ι.toLinearMap),
    fun x z => (e x z).symm⟩

theorem ambIsTrue_of_ambTrue (Z : TC.Later B (I.cols l)) (e) (hD : Df.DefTrue I l (GlobalTheory.Mem.FieldsLaws.fields_ok B) Z.W e)
    (A : AmbForm (I.rec7 l Z) (RowSide.sharp (I.rec7 l Z))) (hA : Df.AmbTrue I l (GlobalTheory.Mem.FieldsLaws.fields_ok B) Z e A) :
    AmbIsTrue I l Z A := by
  have h0 := hA.mt (I.cols l).mu0
  have key : ∀ (H : HLat B.LL) (f : H.V → Z.W.Amb (I.cols l).mu0),
      (⟨H, f⟩ : Σ H : HLat B.LL, (H.V → Z.W.Amb (I.cols l).mu0)) =
        ⟨Df.MtHL I (GlobalTheory.Mem.FieldsLaws.fields_ok B) I.mu0, fun x => e (I.cols l).mu0 (Df.toCx I (GlobalTheory.Mem.FieldsLaws.fields_ok B) I.mu0 x)⟩ →
      ∃ s : (MtTrue I).V ≃ₗ[B.LL] H.V, (∀ z, s z ∈ H.L ↔ z ∈ (MtTrue I).L) ∧
        (∀ (v : InfinitePlace B.LL) z, Formalism.HermitianLatticesTheory.normAt H.b H.X v (s z) = Formalism.HermitianLatticesTheory.normAt (MtTrue I).b (MtTrue I).X v z) ∧
        ∀ z, f (s z) = e (I.cols l).mu0 (Df.toCx I (GlobalTheory.Mem.FieldsLaws.fields_ok B) I.mu0 z) := by
    intro H f h
    cases h
    exact ⟨LinearEquiv.refl _ _, fun _ => Iff.rfl, fun _ _ => rfl, fun _ => rfl⟩
  obtain ⟨s, s1, s2, s3⟩ := key _ _ h0
  refine ⟨s, s1, s2, fun w j hj z => ?_⟩
  refine (congrArg (Z.W.eMt0 w).symm (s3 z)).trans (Subtype.ext (funext fun _ => funext fun p => ?_))
  exact (hD.eMt0 w _ p).trans (hj z p).symm

theorem exists_ambIsTrue : ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (A : AmbForm (I.rec7 l Z) (RowSide.sharp (I.rec7 l Z))), I.Ok ∧ TC.Pins B X ∧ I.IsTw ∧ ColIn.JetsIn I ∧ BuiltCols (I.rec7 l Z) ∧
      AmbIsTrue I l Z A ∧ ∀ u, ∃ j e, IsRowEmb I l u j ∧ IsPerTrue I l u j e := by
  obtain ⟨B, X, I, hL, h, hP, hT, hJ⟩ := exists_choices
  have l := TrueColsTest.laws h
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  obtain ⟨R⟩ := rowsDef_ex I h hP l hX
  obtain ⟨Del, letter, hD, hinj, gap, hu⟩ := hL
  obtain ⟨V, -⟩ := exists_divStage_standIn B _ R.W R.std 0
  obtain ⟨N, -⟩ := GlobalTheory.MemN.exists_nStage_tameChi B _ R.W R.std
  obtain ⟨S⟩ := SStageInhab.nonempty_sStage B _ R.W Del hD gap letter hinj hu
    (fun u x _ y _ => TrueColsTest.ipC_herm l u x y) (fun u x hx h => TrueColsTest.ipC_pos l u x hx h)
    (by rw [R.std.drows]; exact Nat.zero_le _)
  obtain ⟨G⟩ := GJInhab.nonempty_stage B (I.cols l)
  obtain ⟨A, hA⟩ := ambTrue_ex I h hP l hX ⟨R.W, V, S, N, G⟩ R.e R.tru
  exact ⟨B, X, I, l, ⟨R.W, V, S, N, G⟩, A, h, hP, hT, hJ, ⟨B, X, I, l, _, h, hP, hT, hJ, rfl⟩,
    ambIsTrue_of_ambTrue I l _ R.e R.tru A hA, fun u => (exists_isPerTrue I l h u).elim fun e he =>
      ⟨_, e, isRowEmb_rowJ I l h u, he⟩⟩

theorem ambIsTrue_jAmb (h : I.Ok) (Z : TC.Later B (I.cols l)) (A : AmbForm (I.rec7 l Z) (RowSide.sharp (I.rec7 l Z)))
    (hA : AmbIsTrue I l Z A) (w w' : B.Word) (z : (MtTrue I).V) :
    (I.rec7 l Z).eMt w (rowJ I l h w z) = (I.rec7 l Z).eMt w' (rowJ I l h w' z) := by
  obtain ⟨s, -, -, h3⟩ := hA
  have e1 := h3 w _ (isRowEmb_rowJ I l h w) z
  have e2 := h3 w' _ (isRowEmb_rowJ I l h w') z
  exact ((LinearEquiv.symm_apply_eq _).1 e1).symm.trans ((LinearEquiv.symm_apply_eq _).1 e2)

theorem exists_isRowEmb (u : B.Word) : ∃ j, IsRowEmb I l u j := by
  have hd : Disjoint (B.primes X).vGs (QE I.sel (I.tup I.mu0 : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K)) := by
    rw [I.trueColumn_tuple_trivial_eq_one]
    exact (Formalism.L2.Col.twistPrimes_trivialTuple_empty (X := B.fields) I.sel I.S).symm ▸ Finset.disjoint_empty_right _
  exact ⟨PeriodOnStep.rowEmb (Pr := B.primes X) B.wts I.Ch I.sel (I.tup I.mu0) I.Ps (I := I.chIn u I.mu0) (I.perIn u I.mu0).b0
    (I.perIn u I.mu0).til (I.perIn u I.mu0).ext (I.perIn u I.mu0).tz (I.perIn u I.mu0).H hd B.embLL, fun _ _ => rfl⟩

end GlobalTheory.Core.Rk.TrueModel

end

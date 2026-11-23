import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondFieldStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CurveOverOfRayFieldAny
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrameLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JInjRdOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LinearIndependentOfIndepToC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivAtRecordOfEquivRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SecBCAndCuspBC
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ActLevAndActBC

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MovedUnifNe

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

theorem indepToC_sec {D : D7} (T : Core D) (hM : LawsM T) {j : ℕ} (hj : InR D j) {σ : T.Q.c.F →+* ℂ}
    (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    ReciprocityTheory.ChartRestriction.G.PullbackSections.IndepToC ((rdU (T.U j σ)).comp (sec (T.Q.Xo j) T.Q.c a n).subtype) := by
  have hL := GlobalTheory.abelianSchemeLaws_all.2
  have hA : BCEx (T.Q.Xo j) T.Q.c σ :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.bcEx_laws T.Q.c hL.secBaseChangeAny hL.secTwist σ
  have hF : WtField (T.Q.Xo j) T.Q.c :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.wtField_laws T.Q.c hL.secBaseChangeAny hL.secTwist (hM.evalWD j hj)
  intro m b hb
  have hU : IsUnf (T.U j σ) := hM.unf j hj σ hσ
  have hb' := hb.map' (sec (T.Q.Xo j) T.Q.c a n).subtype (Submodule.ker_subtype _)
  have hfs : ∀ i, (⇑(sec (T.Q.Xo j) T.Q.c a n).subtype ∘ b) i ∈ sec (T.Q.Xo j) T.Q.c a n :=
    fun i => (b i).2
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hrel : ∀ k (x : ((T.U j σ).X k).dom),
      ∑ i, g i * toC (evR (T.Q.Xo j) T.Q.c ((⇑(sec (T.Q.Xo j) T.Q.c a n).subtype ∘ b) i)
        ((T.U j σ).un k x)) = 0 := by
    intro k x
    have h := congrFun (congrFun hg k) x.1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.rdU_apply_dom (T.U j σ) _ k x]; rfl
  have hall := ReciprocityTheory.ChartRestriction.G.PullbackSections.rel_of_frames (T.U j σ) hU.2.2.1 (hM.unTest j hj σ hσ) hF _ hfs g hrel
  let _ : Algebra T.Q.c.F ℂ := σ.toAlgebra
  have hc := ReciprocityTheory.ChartRestriction.G.PullbackSections.indep_of_complex (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S)
    (fun φ y z => FrMap φ y z) (hM.evalWD j hj) (fun p φ y => hA p y φ)
    _ (fun i => (hfs i).1) hb' g (fun z hz => hall z hz)
  intro i
  exact congrFun hc i

theorem rel_of_dict {D : D7} (T : Core D) (hM : LawsM T) {j : ℕ} (hj : InR D j) {σ : T.Q.c.F →+* ℂ}
    (hσ : GoodEmb T.Q.c σ) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n m : ℕ} (fs : Fin m → T.R j)
    (hfs : ∀ i, fs i ∈ sec (T.Q.Xo j) T.Q.c a n) (g : Fin m → ℂ)
    (h : ∀ x : GA D (T.V j σ), ∃ γ ∈ GQ (T.V j σ),
      ∑ i, g i * rdU (T.U j σ) (fs i) (T.dict j σ (γ * x)).1 (T.dict j σ (γ * x)).2 = 0) :
    ∑ i, g i • rdU (T.U j σ) (fs i) = 0 := by
  classical
  have hL := GlobalTheory.abelianSchemeLaws_all.2
  have hF : WtField (T.Q.Xo j) T.Q.c :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.wtField_laws T.Q.c hL.secBaseChangeAny hL.secTwist (hM.evalWD j hj)
  have hU : IsUnf (T.U j σ) := hM.unf j hj σ hσ
  have hT := hM.unTest j hj σ hσ
  obtain ⟨th, hr, -, hD⟩ := hM.dictU j hj σ hσ
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  funext k x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  by_cases hx : x ∈ ((T.U j σ).X k).dom
  swap
  · refine Finset.sum_eq_zero fun i _ => ?_
    have e : rdU (T.U j σ) (fs i) k x = 0 := by
      show (if h : x ∈ ((T.U j σ).X k).dom then _ else 0) = 0
      rw [dif_neg hx]
    rw [e, mul_zero]
  obtain ⟨g0, γ, hγ, b, hb, hg0⟩ := hD.2.2.2.2.1 k x hx
  obtain ⟨γ0, hγ0, hrel⟩ := h g0
  obtain ⟨γ', hγ', hd⟩ := hD.1 γ0 hγ0 g0
  have hdom1 := hD.2.2.2.1 g0
  have hdom2 := hD.2.2.2.1 (γ0 * g0)
  rw [hd] at hrel hdom2
  generalize T.dict j σ g0 = p at hrel hdom1 hdom2 hγ' hg0
  subst hg0
  simp only at hrel hdom1 hdom2 hγ'
  obtain ⟨t1, h1⟩ := (hU.2.2.2.1 k k ⟨x, hx⟩ ⟨_, hdom1⟩).2 ⟨γ, hγ, b, hb, rfl⟩
  obtain ⟨t2, h2⟩ := (hU.2.2.2.1 k k ⟨_, hdom1⟩ ⟨_, hdom2⟩).2
    ⟨γ', hγ', ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF _, ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF_mem _,
      by rw [ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_oneF]⟩
  have hv : ∀ i, rdU (T.U j σ) (fs i) k (lact γ' (rmul (lact γ x) b)) =
      toC (wchar (ex (T.Q.Dw j) a n) t2) * (toC (wchar (ex (T.Q.Dw j) a n) t1) * rdU (T.U j σ) (fs i) k x) := by
    intro i
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.rdU_apply_dom (T.U j σ) (fs i) k ⟨_, hdom2⟩,
      ReciprocityTheory.ChartRestriction.G.PullbackSections.rdU_apply_dom (T.U j σ) (fs i) k ⟨x, hx⟩,
      hF a n (fs i) (hfs i) (CAt σ) t2 _ _ (hT k _) (hT k _) h2,
      hF a n (fs i) (hfs i) (CAt σ) t1 _ _ (hT k _) (hT k _) h1]
    rfl
  simp only [hv] at hrel
  have hw1 : toC (wchar (ex (T.Q.Dw j) a n) t1) ≠ 0 := wchar_ne_zero _ t1
  have hw2 : toC (wchar (ex (T.Q.Dw j) a n) t2) ≠ 0 := wchar_ne_zero _ t2
  have e : ∑ i, g i * (toC (wchar (ex (T.Q.Dw j) a n) t2) * (toC (wchar (ex (T.Q.Dw j) a n) t1) *
      rdU (T.U j σ) (fs i) k x)) = (toC (wchar (ex (T.Q.Dw j) a n) t2) * toC (wchar (ex (T.Q.Dw j) a n) t1)) *
      ∑ i, g i * rdU (T.U j σ) (fs i) k x := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e] at hrel
  exact (mul_eq_zero.1 hrel).resolve_left (mul_ne_zero hw2 hw1)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem eq_zero_of_rdU {D : D7} (T : Core D) (hM : LawsM T) {j : ℕ} (hj : InR D j) (c' : Coeff T.Q.l)
    (hle : T.Q.c.F ≤ c'.F) (σ' : c'.F →+* ℂ) (hσ : GoodEmb T.Q.c (σ'.comp (incF T.Q.c c' hle)))
    {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n m : ℕ} {f' : Rul (T.Q.Xo j) c'} (hf' : f' ∈ sec (T.Q.Xo j) c' a n)
    {as : Fin m → c'.F} {gs : Fin m → T.R j} (hgs : ∀ i, gs i ∈ sec (T.Q.Xo j) T.Q.c a n)
    (hBC : IsBC hle f' as gs)
    (h0 : ∑ i, σ' (as i) • rdU (T.U j (σ'.comp (incF T.Q.c c' hle))) (gs i) = 0) : f' = 0 := by
  classical
  letI : Algebra T.Q.c.F c'.F := (incF T.Q.c c' hle).toAlgebra
  have hσ' : ∀ x : T.Q.c.F, σ' (algebraMap T.Q.c.F c'.F x) = (σ'.comp (incF T.Q.c c' hle)) x := fun _ => rfl
  have hI := (GlobalTheory.ReadingComparison.indepToC_bcMap_iff hσ'
    ((rdU (T.U j (σ'.comp (incF T.Q.c c' hle)))).comp (sec (T.Q.Xo j) T.Q.c a n).subtype)).2
    (indepToC_sec T hM hj hσ a n)
  let t : c'.F ⊗[T.Q.c.F] (sec (T.Q.Xo j) T.Q.c a n) :=
    ∑ i, as i ⊗ₜ[T.Q.c.F] (⟨gs i, hgs i⟩ : sec (T.Q.Xo j) T.Q.c a n)
  have hbt : GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeTensorProduct.bcMap hσ'
      ((rdU (T.U j (σ'.comp (incF T.Q.c c' hle)))).comp (sec (T.Q.Xo j) T.Q.c a n).subtype) t = 0 := by
    simp only [t, map_sum, GlobalTheory.ReadingComparison.bcMap_tmul]
    exact h0
  have ht : t = 0 := by
    by_contra ht
    have h1 := hI 1 ![t] (linearIndependent_unique_iff.2 (by exact ht))
    exact h1.ne_zero 0 (by exact hbt)
  funext p y
  show f' p y = 0
  letI : Algebra T.Q.c.F p.R := GlobalTheory.FieldBC.resAlg hle p.R
  have hA : AlgOver T.Q.c c' hle p.R := fun _ => rfl
  have hv : f' p y = evR (T.Q.Xo j) c' f' y := by
    have hft : FromTest (K := c'.F) (fun S _ _ => FrPt (T.Q.Xo j) c' S) (fun φ y z => FrMap φ y z) y :=
      ⟨p, AlgHom.id _ _, y, ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_refl y⟩
    show _ = evalAt (K := c'.F) (fun S _ _ => FrPt (T.Q.Xo j) c' S) (fun φ y z => FrMap φ y z) f' y
    unfold evalAt
    rw [dif_pos hft]
    exact hf'.1 _ _ _ _ _ hft.choose_spec.choose_spec.choose_spec
  rw [hv, hBC p.R hA y]
  have hadd : ∀ g g' : T.R j, evR (T.Q.Xo j) T.Q.c (g + g') (y.res hle hA) =
      evR (T.Q.Xo j) T.Q.c g (y.res hle hA) + evR (T.Q.Xo j) T.Q.c g' (y.res hle hA) :=
    fun g g' => evalAt_add _ _ g g' _
  have hsmul : ∀ (k : T.Q.c.F) (g : T.R j), evR (T.Q.Xo j) T.Q.c (k • g) (y.res hle hA) =
      algebraMap T.Q.c.F p.R k * evR (T.Q.Xo j) T.Q.c g (y.res hle hA) :=
    fun k g => evalAt_smul _ _ k g _
  let B : c'.F →+ (sec (T.Q.Xo j) T.Q.c a n) →+ p.R :=
    { toFun := fun x =>
        { toFun := fun g => algebraMap c'.F p.R x * evR (T.Q.Xo j) T.Q.c (g : T.R j) (y.res hle hA)
          map_zero' := by
            rw [ZeroMemClass.coe_zero, show evR (T.Q.Xo j) T.Q.c (0 : T.R j) (y.res hle hA) = 0 from
              evalAt_zero _ _ _, mul_zero]
          map_add' := fun g g' => by rw [Submodule.coe_add, hadd, mul_add] }
      map_zero' := by ext g; simp
      map_add' := fun x x' => by ext g; simp [add_mul] }
  have hB : ∀ (k : T.Q.c.F) (x : c'.F) (g : sec (T.Q.Xo j) T.Q.c a n), B (k • x) g = B x (k • g) := by
    intro k x g
    simp only [B, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [Submodule.coe_smul, hsmul, Algebra.smul_def, map_mul]
    have e : algebraMap T.Q.c.F p.R k = algebraMap c'.F p.R (algebraMap T.Q.c.F c'.F k) := rfl
    rw [e]; ring
  let Φ : c'.F ⊗[T.Q.c.F] (sec (T.Q.Xo j) T.Q.c a n) →+ p.R := TensorProduct.liftAddHom B hB
  have e := congrArg Φ ht
  rw [map_zero] at e
  have e2 : Φ t = ∑ i, algebraMap c'.F p.R (as i) * evR (T.Q.Xo j) T.Q.c (gs i) (y.res hle hA) := by
    simp only [t, map_sum, Φ, TensorProduct.liftAddHom_tmul]
    rfl
  rw [← e2, e]

theorem exists_gq_of_cast {D : D7} {V W : HSp D} (hV : V = W) (P : GA D V → Prop)
    (h : ∀ q : AutQ W, P (cast (congrArg (GA D) hV.symm) q.out)) : ∀ x : GA D V, ∃ γ ∈ GQ V, P (γ * x) := by
  subst hV
  intro x
  have hq := h (Quotient.mk _ x)
  have hr := @Quotient.mk_out _ (QuotientGroup.rightRel (GQ V)) x
  rw [QuotientGroup.rightRel_apply] at hr
  refine ⟨(x * (Quotient.mk (QuotientGroup.rightRel (GQ V)) x).out⁻¹)⁻¹, inv_mem hr, ?_⟩
  simpa [mul_assoc] using hq

end GlobalTheory.MovedUnifNe

namespace GlobalTheory.MovedUnifNe

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.OneMapAll

set_option maxHeartbeats 1000000 in

theorem exists_jFn_actLev_ne : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T0 : Type) (A : FamIn D.what₂.LL Γ Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ (j : Fin D.R.m), OMPins T R κ v₀ O j → OneMapRow0 T R κ v₀ O j → ∀ f ∈ GlobalTheory.OneMapAll.cuspOver (O j) (κ j), f ≠ 0 → ∀ z : Γ, z ∈ Subgroup.center Γ → ∃ q, jFn (Wc D j) (inC (O j).c') (rdU (unfBC (O j).hle (T.toCore.U ((j : ℕ) + 1)) (inC (O j).c'))) (O j).dict (O j).mu (actLev (O j).c' (O j).lev2 z f) q ≠ 0 := by
  intro D Γ _ _ Pl0 T0 A T _ R F κ v₀ O hnV hC hFW hIo j hP hrow f hf hf0 z hz
  by_contra hne
  push_neg at hne
  obtain ⟨W⟩ := hFW
  have hM : LawsM T.toCore := W.laws.toLawsM
  have hj : InR D ((j : ℕ) + 1) := ⟨by omega, by have := j.isLt; omega⟩
  have hs0 : GoodEmb T.Q.c (O j).s0 := by
    rw [OMDat.s0, sOv_eq]; exact T.toCore.good_σ₀
  have hact := hP.2.act.1
  have hact' := hP.2.act.2
  obtain ⟨m, as, fs, hfs, hBC⟩ :=
    (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ (O j).hle).2 _ (T.toCore.U ((j : ℕ) + 1)) _ _ f hf
  have hfsec := ((mem_cusp _ _ _ _ _ _).1 hf).1
  have hs : ∀ k, fs k ∈ sec _ T.Q.c (wtA (κ j)) (Vc D j).rank := fun k => ((mem_cusp _ _ _ _ _ _).1 (hfs k)).1
  have h1 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ (O j).hle _ _ hact).2 _ _ z m as fs f hfsec hs hBC
  have hgs : ∀ k, actLev T.Q.c (O j).lev2 z (fs k) ∈ sec _ T.Q.c (wtA (κ j)) (Vc D j).rank :=
    fun k => GlobalTheory.LevelEquivCompare.actLev_mem_sec hact z (hs k)
  have hF' : actLev (O j).c' (O j).lev2 z f ∈ sec _ (O j).c' (wtA (κ j)) (Vc D j).rank :=
    GlobalTheory.LevelEquivCompare.actLev_mem_sec hact' z hfsec
  have hrd := rdU_unfBC (O j).hle (T.toCore.U ((j : ℕ) + 1)) (inC (O j).c') h1
  have hrel := rel_of_dict T.toCore hM hj hs0 _ hgs (fun i => inC (O j).c' (as i)) (by
    refine exists_gq_of_cast (O j).hV (fun g => ∑ i, (inC (O j).c') (as i) *
      (rdU (T.U ((j : ℕ) + 1) (O j).s0)) ((actLev T.Q.c (O j).lev2 z) (fs i)) (T.dict ((j : ℕ) + 1) (O j).s0 g).fst
        (T.dict ((j : ℕ) + 1) (O j).s0 g).snd = 0) fun q => ?_
    have e := hne q
    have hmu : (O j).mu q.out ≠ 0 := by
      have h := (hM.muUnit _ hj _ hs0).2.1 (cast (congrArg (GA D) (O j).hV.symm) q.out)
      intro h0
      have h0' : T.mu ((j : ℕ) + 1) (O j).s0 (cast (congrArg (GA D) (O j).hV.symm) q.out) = 0 := h0
      rw [h0', norm_zero] at h
      exact zero_ne_one h
    have e2 : rdU (unfBC (O j).hle (T.toCore.U ((j : ℕ) + 1)) (inC (O j).c')) (actLev (O j).c' (O j).lev2 z f)
        ((O j).dict q.out).1 ((O j).dict q.out).2 = 0 := by
      have e1 : jFn (Wc D j) (inC (O j).c') (rdU (unfBC (O j).hle (T.toCore.U ((j : ℕ) + 1)) (inC (O j).c')))
          (O j).dict (O j).mu (actLev (O j).c' (O j).lev2 z f) q = (O j).mu q.out *
          rdU (unfBC (O j).hle (T.toCore.U ((j : ℕ) + 1)) (inC (O j).c')) (actLev (O j).c' (O j).lev2 z f)
            ((O j).dict q.out).1 ((O j).dict q.out).2 := rfl
      rw [e1] at e
      exact (mul_eq_zero.1 e).resolve_left hmu
    rw [hrd] at e2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e2
    exact e2)
  have hz0 := eq_zero_of_rdU T.toCore hM hj (O j).c' (O j).hle (inC (O j).c') hs0 hF' hgs h1 hrel
  apply hf0
  have e3 : actLev (O j).c' (O j).lev2 (z⁻¹ * z) f = f := by
    rw [inv_mul_cancel]
    exact Formalism.L2.Pj.actL_one _ _ _ hact'.total hact'.func hact'.one hfsec.1
  rw [← e3]
  have e4 := Formalism.L2.Pj.actL_mul _ _ _ hact'.total hact'.func hact'.mul z⁻¹ z hfsec.1
  refine e4.trans ?_
  show actLev (O j).c' (O j).lev2 z⁻¹ (actLev (O j).c' (O j).lev2 z f) = 0
  rw [hz0, map_zero]

end GlobalTheory.MovedUnifNe

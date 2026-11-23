import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSwapR
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinMEqOneIffMemGinfC
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RatEquiv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousChartLevelCharactersAdelicTupleStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.ChartReps

section Gen
variable {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
  (y : cl → UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
  (U : Subgroup (GA D V)) (hU : ∀ g, g ∈ U ↔ g ∈ GfC V ∧ ∃ κ : S.U, κ.1.1 = finM V hn g)
  (h : cl → GA D V) (hh : ∀ c, h c ∈ GfC V ∧ finM V hn (h c) = (y c).1.1)

def finHomN : GA D V →* GL (Fin n) (EF D) where
  toFun g := GlobalTheory.AdForm.Model.finGL V hn g
  map_one' := Units.ext (GlobalTheory.AdForm.Model.finM_one V hn)
  map_mul' g g' := Units.ext (GlobalTheory.AdForm.Model.finM_mul V hn g g')

theorem finHomN_val (g : GA D V) : (finHomN V hn g).1 = finM V hn g := rfl

theorem finHomN_eq_one (g : GA D V) : finHomN V hn g = 1 ↔ g ∈ GinfC V := by
  rw [Units.ext_iff, finHomN_val, Units.val_one, GlobalTheory.AdForm.finM_eq_one_iff_mem_GinfC D V n hn g]

include hU in

theorem lift_mem (e : ↥(GfC V) ≃* ↥(UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (he : ∀ g, (e g).1.1 = finM V hn g.1) (κ : S.U) :
    (e.symm ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩).1 ∈ U ∧ finM V hn (e.symm ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩).1 = κ.1.1 := by
  have h1 : finM V hn (e.symm ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩).1 = κ.1.1 := by rw [← he, e.apply_symm_apply]
  exact ⟨(hU _).2 ⟨(e.symm _).2, κ, h1.symm⟩, h1⟩

include hU hh in
set_option maxHeartbeats 1000000 in

theorem reps_of_chart (hy : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls S))) : IsReps V U h := by
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D V n hn
  obtain ⟨r, hr⟩ := GlobalTheory.RatPtsEquiv.rat_equiv D V n hn
  have hmemU : ∀ (g : GfC V), g.1 ∈ U ↔ (e g).1 ∈ S.U := by
    intro g
    rw [hU]
    constructor
    · rintro ⟨_, κ, hκ⟩
      have : (e g).1 = κ.1 := Units.ext ((he g).trans hκ.symm)
      rw [this]; exact κ.2
    · intro hx; exact ⟨g.2, ⟨(e g).1, hx⟩, he g⟩
  have hΦe : ∀ g : GfC V, finHomN V hn g.1 = (e g).1 := fun g => Units.ext (he g).symm
  refine ⟨fun g hg => ((hU g).1 hg).1, ?_, ?_, fun c => (hh c).1, ?_, ?_⟩
  · have hset : (U : Set (GA D V)) = (fun x => (e.symm x).1) '' {x | x.1 ∈ S.U} := by
      ext g
      constructor
      · intro hg
        have hgf := ((hU g).1 hg).1
        exact ⟨e ⟨g, hgf⟩, (hmemU ⟨g, hgf⟩).1 hg, by simp only [e.symm_apply_apply]⟩
      · rintro ⟨x, hx, rfl⟩
        exact (hmemU _).2 (by rw [e.apply_symm_apply]; exact hx)
    have hc : IsCompact {x : ↥(UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) | x.1 ∈ S.U} := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
      convert S.U_compact using 1
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hz; exact ⟨⟨z, ((S.U_eq z).1 hz).1⟩, hz, rfl⟩
    rw [hset]
    exact hc.image (continuous_subtype_val.comp e.symm.continuous)
  · have : ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) = e ⁻¹' {x | x.1 ∈ S.U} := by
      ext g
      exact (Subgroup.mem_subgroupOf).trans (hmemU g)
    rw [this]
    exact S.U_open.preimage e.continuous
  · intro g
    obtain ⟨p, hpq⟩ : ∃ p : GinfC V × GfC V, g = p.1.1 * p.2.1 :=
      ⟨(GlobalTheory.AdelicSplit.splitEquiv V).symm g, ((GlobalTheory.AdelicSplit.splitEquiv V).apply_symm_apply g).symm⟩
    obtain ⟨⟨c, δ, κ0⟩, hδ, hdec⟩ := GlobalTheory.AdForm.Model.exists_dec V hn S y hy.2 p.2.1
    obtain ⟨κ, hκU, hκf⟩ : ∃ κ ∈ U, finM V hn κ = κ0.1.1 :=
      ⟨_, (lift_mem V hn S U hU e.toMulEquiv he κ0).1, (lift_mem V hn S U hU e.toMulEquiv he κ0).2⟩
    obtain ⟨γ, hγ, hΦγ⟩ : ∃ γ ∈ GQ V, finHomN V hn γ = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ := by
      refine ⟨(r.symm ⟨δ, hδ⟩).1, (r.symm ⟨δ, hδ⟩).2, ?_⟩
      apply Units.ext
      have h1 := hr (r.symm ⟨δ, hδ⟩)
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1
    refine ⟨γ, hγ, c, (h c)⁻¹ * γ⁻¹ * g * κ⁻¹, ?_, κ, hκU, by group⟩
    rw [← finHomN_eq_one V hn]
    have e1 : finHomN V hn g = finHomN V hn p.2.1 := by
      rw [hpq, map_mul, (finHomN_eq_one V hn _).2 p.1.2, one_mul]
    have e2 : finHomN V hn p.2.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ * (y c).1 * κ0.1 :=
      Units.ext (by rw [finHomN_val, hdec])
    have e3 : finHomN V hn (h c) = (y c).1 := Units.ext (by rw [finHomN_val, (hh c).2])
    have e4 : finHomN V hn κ = κ0.1 := Units.ext (by rw [finHomN_val, hκf])
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, e1, e2, e3, e4, hΦγ]
    group
  · intro c c' γ hγ k hk κ hκ heq
    obtain ⟨_, κ0, hκ0⟩ := (hU κ).1 hκ
    have hΦγ : finHomN V hn γ = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r ⟨γ, hγ⟩).1 :=
      Units.ext (by rw [finHomN_val, hr ⟨γ, hγ⟩])
    have e3 : ∀ c, finHomN V hn (h c) = (y c).1 := fun c => Units.ext (by rw [finHomN_val, (hh c).2])
    have e4 : finHomN V hn κ = κ0.1 := Units.ext (by rw [finHomN_val, ← hκ0])
    have key : (y c').1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r ⟨γ, hγ⟩).1 * (y c).1 * κ0.1 := by
      rw [← e3, ← e3, heq, ← e4, ← hΦγ]
      simp only [map_mul, (finHomN_eq_one V hn k).2 hk, mul_one]
    have hmemγ : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r ⟨γ, hγ⟩).1 ∈
        UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
      rw [← hΦγ]; exact GlobalTheory.AdForm.Model.finGL_mem V hn γ
    apply hy.1
    show (Quotient.mk'' (y c) : Cls S) = Quotient.mk'' (y c')
    refine (DoubleCoset.eq _ _ _ _).2 ⟨⟨_, hmemγ⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem _ (r ⟨γ, hγ⟩).2),
      ⟨κ0.1, ((S.U_eq κ0.1).1 κ0.2).1⟩, Subgroup.mem_subgroupOf.2 κ0.2, Subtype.ext key⟩

end Gen

section Gen2
variable {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
  (y : cl → UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
  (U : Subgroup (GA D V)) (hU : ∀ g, g ∈ U ↔ g ∈ GfC V ∧ ∃ κ : S.U, κ.1.1 = finM V hn g)
  (h : cl → GA D V) (hh : ∀ c, h c ∈ GfC V ∧ finM V hn (h c) = (y c).1.1)

include hU hh in
set_option maxHeartbeats 1000000 in

theorem stabOrd_of_chart {stab : cl → Type} [∀ c, Group (stab c)]
    (stabI : ∀ c, stab c →* UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn)))
    (hinj : ∀ c, Function.Injective (stabI c))
    (hran : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn))),
      γ ∈ (stabI c).range ↔ bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        S.U.map (MulAut.conj (y c).1).toMonoidHom)
    (c : cl) : stabOrd U (h c) = Nat.card (stab c) := by
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D V n hn
  obtain ⟨r, hr⟩ := GlobalTheory.RatPtsEquiv.rat_equiv D V n hn
  have hΦγ : ∀ γ : GQ V, finHomN V hn γ.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r γ).1 :=
    fun γ => Units.ext (hr γ)
  have e3 : finHomN V hn (h c) = (y c).1 := Units.ext (by rw [finHomN_val, (hh c).2])
  have hcond : ∀ γ : GQ V, (∃ k ∈ GinfC V, ∃ κ ∈ U, γ.1 * h c = h c * k * κ) ↔ r γ ∈ (stabI c).range := by
    intro γ
    rw [hran]
    constructor
    · rintro ⟨k, hk, κ, hκ, heq⟩
      obtain ⟨_, κ0, hκ0⟩ := (hU κ).1 hκ
      have e4 : finHomN V hn κ = κ0.1 := Units.ext (by rw [finHomN_val, ← hκ0])
      have key := congrArg (finHomN V hn) heq
      rw [map_mul, map_mul, map_mul, hΦγ, e3, e4, (finHomN_eq_one V hn k).2 hk, mul_one] at key
      refine Subgroup.mem_map.2 ⟨κ0.1, κ0.2, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← key]
      group
    · intro hmem
      obtain ⟨κ1, hκ1, hconj⟩ := Subgroup.mem_map.1 hmem
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hconj
      obtain ⟨κ, hκU, hκf⟩ : ∃ κ ∈ U, finM V hn κ = κ1.1 :=
        ⟨_, (lift_mem V hn S U hU e.toMulEquiv he ⟨κ1, hκ1⟩).1, (lift_mem V hn S U hU e.toMulEquiv he ⟨κ1, hκ1⟩).2⟩
      have e4 : finHomN V hn κ = κ1 := Units.ext (by rw [finHomN_val, hκf])
      refine ⟨(h c)⁻¹ * γ.1 * h c * κ⁻¹, ?_, κ, hκU, by group⟩
      rw [← finHomN_eq_one V hn, map_mul, map_mul, map_mul, map_inv, map_inv, hΦγ, e3, e4, ← hconj]
      group
  unfold stabOrd
  rw [Nat.card_congr (r.toEquiv.subtypeEquiv hcond)]
  exact (Nat.card_congr (MonoidHom.ofInjective (hinj c)).toEquiv).symm

end Gen2

set_option maxHeartbeats 1000000 in

theorem twDat_reps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, IsReps ((I.rec7 l Z).sp.X i) (A.U i β) (A.h i β) ∧ (Continuous fun κ => ((A.chi i β κ : ℂˣ) : ℂ)) ∧ ∀ c, stabOrd (A.U i β) (A.h i β c) = Nat.card ((I.chain l u a).stab i c.1) := by
  intro B X I hOk hP l Z u a Ch A hA i hi β
  exact ⟨reps_of_chart _ (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y (A.U i β) (hA.U i hi β) (A.h i β)
      (hA.h i hi β) (A.K i hi β).y_bij,
    GlobalTheory.T.continuous_chartLevelCharacters_adelic_tuple I hOk hP l Z u a Ch A hA i hi β,
    fun c => stabOrd_of_chart _ (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y (A.U i β) (hA.U i hi β) (A.h i β)
      (hA.h i hi β) (A.K i hi β).stabI (A.K i hi β).stabI_inj (A.K i hi β).stabI_range c⟩

end GlobalTheory.ChartReps

import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReprMemOfBasisRational
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DoubleCosetOperatorEqLabelOperatorLocalRepsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertHeckeLift

theorem dualC_single {d : List ℤ} (hd : dualLab d = d) :
    dualC (Finsupp.mapRange star (star_zero ℂ) (Finsupp.single d (1 : ℂ))) = Finsupp.single d 1 := by
  rw [Finsupp.mapRange_single, star_one, dualC, Finsupp.mapDomain_single, hd]

theorem ext_mul {Gr Γ W K : Type} [Group Gr] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
    [StarRing K] {ι : Γ →* Gr} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup Gr} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι S σ ρ J χ) (f : S.Forms) (g : Gr) (k : J) (hk : χ k = 1) : P.ext f.1 (g * k) = P.ext f.1 g := by
  have h2 := (GlobalTheory.classPres_basic ι S σ ρ J χ P).1 f 1 g k
  rwa [map_one, map_one, one_mul, Module.End.one_apply, hk, Units.val_one, one_smul] at h2

theorem csum_adj {Gr Γ W K : Type} [Group Gr] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
    [StarRing K] {ι : Γ →* Gr} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup Gr} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (Gr → W)) (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y))
    (jm : S.Forms → M.H) (hj : ∀ f, M.e (jm f) = P.ext f.1) (U : Module.End K S.Forms) (u : Module.End ℂ M.H)
    (hu : LinearMap.adjoint u = u) (hU : ∀ f, jm (U f) = u (jm f)) (f g : S.Forms) :
    S.csum (U f).1 g.1 = S.csum f.1 (U g).1 := by
  have hin : ∀ f g : S.Forms, inner ℂ (jm f) (jm g) = σ (S.csum f.1 g.1) := by
    intro f g
    rw [hM.2.2, hj, hj]
    exact (GlobalTheory.classPres_basic ι S σ ρ J χ P).2.1 f g
  apply σ.injective
  rw [← hin, ← hin, hU, hU, ← LinearMap.adjoint_inner_right, hu]

theorem tie_label {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : LevDat D.host.E ℂ V.rank) (hβ : IsSDFrame V β Λ 1) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : GQ V →* Module.End ℂ W} {K : Type} [Field K] [NumberField K] [StarRing K] {σ : K →+* ℂ} {S : CSD K}
    (Pr : Bridge.ClassPres (Bridge.ratF V) S σ ρ (levEnv V β L).J (levEnv V β L).χ) {I : Type} {pl : I → Pl D.host.E}
    {ty : I → List ℤ} {op : I → Module.End K S.Forms} {inR : I → Prop}
    (Comparison₂ : Bridge.HeckeTie (Bridge.ratF V) Pr op inR (fun i => IsLabElt V (pl i) (ty i)) (fun i => IsLocElt V (pl i)))
    (i : I) (hi : inR i) (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ pl i ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i))
    (hpw : (ty i).Pairwise (fun a b => b ≤ a)) :
    IsLab V (pl i) (ty i) ∧ ∀ f : S.Forms, Pr.ext (op i f).1 = hkF V (pl i) (Finsupp.single (ty i) 1) (Pr.ext f.1) := by
  obtain ⟨c, hc⟩ := hβ
  rw [one_pow] at hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ (pl i).asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 (pl i).isPrime.ne_top
  have hd := GlobalTheory.T.doubleCosetOperator_eq_labelOperator_localReps V β Λ 1 L hc (pl i) h1 hoff (ty i) (Comparison₂.hx i) (Comparison₂.hA i) hpw
    (Comparison₂.hx_ok i hi) (Comparison₂.hA_loc i hi) (Comparison₂.hDC i hi)
  exact ⟨hd.1, fun f => (Comparison₂.op_eq i hi f).trans (hd.2 W _ fun g k hk => ext_mul Pr f g k (Comparison₂.chi_loc i hi k hk))⟩

theorem inert_lifts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → ∀ j t, ∀ (I : Type) (pl : I → Pl D.host.E) (ty : I → List ℤ) (op : I → Module.End D.what₂.LL (A.MtCSD j t).Forms) (inR : I → Prop), (∀ i, inR i → Good R t (pl i) ∧ conjPl (pl i) = pl i ∧ (ty i).Pairwise (fun a b => b ≤ a)) → Bridge.HeckeTie (Bridge.ratF (Vc D j)) (R.B.L j t).pres op inR (fun i => IsLabElt (Vc D j) (pl i) (ty i)) (fun i => IsLocElt (Vc D j) (pl i)) → ∀ i, inR i → (∀ a b, LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis (op i) a b ∈ cmMax D.what₂.LL) ∧ (∀ f g : (A.MtCSD j t).Forms, (A.MtCSD j t).csum ((op i f : (A.MtCSD j t).Forms) : (A.MtCSD j t).Cl → (A.MtCSD j t).V) (g : (A.MtCSD j t).Cl → (A.MtCSD j t).V) = (A.MtCSD j t).csum (f : (A.MtCSD j t).Cl → (A.MtCSD j t).V) ((op i g : (A.MtCSD j t).Forms) : (A.MtCSD j t).Cl → (A.MtCSD j t).V)) ∧ IsLab (Vc D j) (pl i) (ty i) ∧ ∀ h, IsOpsV R j t h → ∀ f, R.jV j t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jV j t f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF hM j t I pl ty op inR hin Comparison₂ i hi
  have hgood := (hin i hi).1
  have hd := tie_label (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j t) (hL.βV j) (R.B.L j t).pres Comparison₂ i hi hgood (hin i hi).2.2
  have hj : ∀ f : (A.MtCSD j t).Forms, (R.HV j t).e (R.jV j t f) = (R.B.L j t).pres.ext f.1 := fun f => hM.jV j t f
  have hint : ∀ h, IsOpsV R j t h → ∀ f, R.jV j t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jV j t f) :=
    fun h hh f => (hM.HV j t).1 (((hj _).trans (hd.2 f)).trans
      ((congrArg (hkF (Vc D j) (pl i) (Finsupp.single (ty i) 1)) (hj f).symm).trans (hh (pl i) hgood _ _).symm))
  refine ⟨GlobalTheory.HeckeRational.lifts_dcOp_mem_cmMax R hF.tie j t (Comparison₂.hA i) (op i) (Comparison₂.op_eq i hi), ?_, hd.1, hint⟩
  refine ((GlobalTheory.T.realization_family_normal_operators R F hL hF hM).2 j t).elim fun h hh => ?_
  have hdual : dualLab (ty i) = ty i := ((GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing (Vc D j) (pl i) (ty i)).1 hd.1).2.2 (hin i hi).2.1
  have hadj := (hh.2.2 (pl i) hgood (Finsupp.single (ty i) 1)).trans (congrArg (h (pl i)) (dualC_single hdual))
  exact csum_adj (R.B.L j t).pres (R.HV j t) (hM.HV j t) (fun f => R.jV j t f) hj (op i) _ hadj (hint h hh.1)

end GlobalTheory.InertHeckeLift

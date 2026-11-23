import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DoubleCosetOperatorEqLabelOperatorLocalRepsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitHeckeElementLabelZerosThenNegOnesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVectorStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesPropertiesStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHeckeLabel

theorem ext_mul {Gr Γ W K : Type} [Group Gr] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
    [StarRing K] {ι : Γ →* Gr} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup Gr} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι S σ ρ J χ) (f : S.Forms) (g : Gr) (k : J) (hk : χ k = 1) : P.ext f.1 (g * k) = P.ext f.1 g := by
  have h2 := (GlobalTheory.classPres_basic ι S σ ρ J χ P).1 f 1 g k
  rwa [map_one, map_one, one_mul, Module.End.one_apply, hk, Units.val_one, one_smul] at h2

def rightTr {H Gr : Type} [Group H] [Group Gr] (φ : H →* Gr) (W : Type) [AddCommGroup W] [Module ℂ W] :
    H →* Module.End ℂ (Gr → W) where
  toFun g := LinearMap.funLeft ℂ W (fun h => h * φ g)
  map_one' := by ext F h; simp [LinearMap.funLeft]
  map_mul' g g' := by ext F h; simp [LinearMap.funLeft, mul_assoc]

theorem rightTr_sum {H Gr : Type} [Group H] [Group Gr] (φ : H →* Gr) {W : Type} [AddCommGroup W] [Module ℂ W] (s : Finset H)
    (F : Gr → W) (h : Gr) : (∑ γ ∈ s, rightTr φ W γ) F h = ∑ γ ∈ s, F (h * φ γ) := by
  rw [LinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem opOf_single {D : D7} {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M)
    (P : Pl D.host.E) (d : List ℤ) : opOf π P (Finsupp.single d 1) = ∑ γ ∈ Hk3.rep V P d, π γ := by
  unfold opOf
  rw [Finsupp.sum_single_index (by exact zero_smul ℂ _), one_smul]

theorem hkF_single {D : D7} (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (d : List ℤ)
    (F : Bridge.Gf V → W) :
    hkF V P (Finsupp.single d 1) F = opOf (rightTr (finHom V).rangeRestrict W) P (Finsupp.single d 1) F := by
  funext h
  have e1 : hkF V P (Finsupp.single d 1) F h = (1 : ℂ) • ∑ γ ∈ Hk3.rep V P d, F (h * (finHom V).rangeRestrict γ) :=
    Finsupp.sum_single_index (h := fun d (z : ℂ) => z • ∑ γ ∈ Hk3.rep V P d, F (h * (finHom V).rangeRestrict γ))
      (zero_smul ℂ _)
  exact e1.trans ((one_smul ℂ _).trans ((rightTr_sum (finHom V).rangeRestrict _ F h).symm.trans
    (congrArg (fun u : Module.End ℂ (Bridge.Gf V → W) => u F h) (opOf_single _ P d).symm)))

theorem side_label {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : LevDat D.host.E ℂ V.rank) (hβ : IsSDFrame V β Λ 1) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : GQ V →* Module.End ℂ W} {K : Type} [Field K] [NumberField K] [StarRing K] {σ : K →+* ℂ} {S : CSD K}
    (Pr : Bridge.ClassPres (Bridge.ratF V) S σ ρ (levEnv V β L).J (levEnv V β L).χ) {Pl0 : Type} (pl : Pl0 → Pl D.host.E)
    (ok : Set Pl0) (op : ok × ℕ → Module.End K S.Forms)
    (Comparison₂ : Bridge.HeckeTie (Bridge.ratF V) Pr op (fun i => 1 ≤ i.2 ∧ i.2 ≤ V.rank) (isTEnv V pl ok) (isLocEnv V pl ok))
    (P : ok) (h0 : op (P, 0) = 1) (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ pl P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl P))
    (k : ℕ) (hk : k ≤ V.rank) (f : S.Forms) :
    Pr.ext (op (P, k) f).1 = hkF V (pl P) (Finsupp.single (splitLab V.rank k) 1) (Pr.ext f.1) := by
  refine hβ.elim fun c hc => ?_
  have hc' : IsBaseFrame V β Λ 1 := (one_pow c : (1 : ℕ) ^ c = 1) ▸ hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ (pl P).asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 (pl P).isPrime.ne_top
  have hl := fun e f' he => (GlobalTheory.LevSplit.lev_split V β Λ 1 (flag1L L) hc').2 (pl P) e f' he h1 hoff
  have hinv : ∀ g (x : (levEnv V β L).J), IsLocElt V (pl P) x → Pr.ext f.1 (g * x) = Pr.ext f.1 g := by
    rintro g ⟨x, hx⟩ ⟨e, f', a, he, ha, hxa, hs⟩
    obtain rfl : x = (finHom V).rangeRestrict a := Subtype.ext hxa
    exact ext_mul Pr f g _ (Units.ext ((hl e f' he).2.1 a ⟨ha, hx⟩ hs))
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · have e0 : splitLab V.rank 0 = List.replicate V.rank 0 := by simp [splitLab]
    rw [h0, e0, hkF_single]
    refine ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V (pl P)).2.2.1.2 _ _ _ fun a ha => ?_).symm
    obtain ⟨ha, e, f', he, hs⟩ := ha
    funext g
    exact hinv g ⟨(finHom V).rangeRestrict a, (((hl e f' he).1 a hs).2 ha).2⟩ ⟨e, f', a, he, ha.1, rfl, hs⟩
  · have hi : 1 ≤ ((P, k) : ok × ℕ).2 ∧ ((P, k) : ok × ℕ).2 ≤ V.rank := ⟨hpos, hk⟩
    have hs := fun x => GlobalTheory.T.split_hecke_element_label_zeros_then_neg_ones V pl ok (P, k) x
    have hd := GlobalTheory.T.doubleCosetOperator_eq_labelOperator_localReps V β Λ 1 L hc' (pl P) h1 hoff (splitLab V.rank k) (Comparison₂.hx (P, k)) (Comparison₂.hA (P, k)) (hs 1).2.2
      ((hs _).1 hk (Comparison₂.hx_ok _ hi)) (fun a ha => (hs a).2.1 (Comparison₂.hA_loc _ hi a ha)) (Comparison₂.hDC _ hi)
    exact (Comparison₂.op_eq _ hi f).trans (hd.2 W _ hinv)

theorem split_ops : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ t h, IsOpsX R t h → ∀ (P : A.ok t) k, k ≤ D.sp.X'.rank → ∀ f, R.jX t (A.heckeR t (P, k) f) = h (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (R.jX t f)) ∧ ∀ j t h, IsOpsV R j t h → ∀ (P : A.ok t) k, k ≤ (Vc D j).rank → ∀ f, R.jV j t (A.heckeL j t (P, k) f) = h (R.pl P) (Finsupp.single (splitLab (Vc D j).rank k) 1) (R.jV j t f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF hM
  have hgood : ∀ t (P : A.ok t), Good R t (R.pl P) := fun t P => ((GlobalTheory.T.theta_lift_levels_good_primes_properties R F hL).2.2.2 hF t P P.2).1
  refine ⟨fun t h hh P k hk f => ?_, fun j t h hh P k hk f => ?_⟩
  · have hd := side_label D.sp.X' R.βX R.ΛX (R.datXt t) hL.βX (R.B.R t).pres R.pl (A.ok t) (A.heckeR t) (R.B.R t).hecke
      P (hF.degR t P).1 (hgood t P) k hk f
    refine (hM.HX t).1 ?_
    refine (hM.jX t _).trans (Eq.trans ?_ (hh _ (hgood t P) _ _).symm)
    exact hd.trans (congrArg (hkF D.sp.X' (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1)) (hM.jX t f).symm)
  · have hd := side_label (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j t) (hL.βV j) (R.B.L j t).pres R.pl (A.ok t) (A.heckeL j t)
      (R.B.L j t).hecke P (hF.degL j t P).1 (hgood t P) k hk f
    refine (hM.HV j t).1 ?_
    refine (hM.jV j t _).trans (Eq.trans ?_ (hh _ (hgood t P) _ _).symm)
    exact hd.trans (congrArg (hkF (Vc D j) (R.pl P) (Finsupp.single (splitLab (Vc D j).rank k) 1)) (hM.jV j t f).symm)

end GlobalTheory.SplitHeckeLabel

end

import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrincPet

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem value_laws (hP : GlobalTheory.Published.CuspRapidDecay) {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    (hθ : IsInfFam θ) {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} (hχ : ∀ k ∈ J, χ k = 1)
    {U : MMap M} (hU : U ∈ Mult θ M J χ) :
    ∀ v, Continuous (U v) ∧ (∃ C : ℝ, ∀ g, ‖U v g‖ ≤ C) ∧ ∀ k ∈ J, ∀ g, U v (g * k) = U v g := by
  unfold Mult at hU
  induction hU using Submodule.span_induction with
  | mem T hT =>
    intro v
    refine ⟨(hT.aut v).cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hT.aut v) (hT.cusp v), fun k hk g => ?_⟩
    rw [hT.lev v k hk g, hχ k hk, one_mul]
  | zero =>
    intro v
    exact ⟨continuous_const, ⟨0, fun g => by simp⟩, fun k _ g => by simp⟩
  | add U U' _ _ h h' =>
    intro v
    obtain ⟨c1, ⟨C1, b1⟩, i1⟩ := h v
    obtain ⟨c2, ⟨C2, b2⟩, i2⟩ := h' v
    refine ⟨by simpa using c1.add c2, ⟨C1 + C2, fun g => ?_⟩, fun k hk g => ?_⟩
    · simp only [MultilinearMap.add_apply, Pi.add_apply]
      exact (norm_add_le _ _).trans (add_le_add (b1 g) (b2 g))
    · simp only [MultilinearMap.add_apply, Pi.add_apply, i1 k hk g, i2 k hk g]
  | smul a U _ h =>
    intro v
    obtain ⟨c1, ⟨C1, b1⟩, i1⟩ := h v
    refine ⟨by simpa using c1.const_smul a, ⟨‖a‖ * C1, fun g => ?_⟩, fun k hk g => ?_⟩
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (b1 g) (norm_nonneg _)
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, i1 k hk g]

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levChi_triv (R : RealDat D A Ks) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1 := by
  have hP : (R.datWp i R.triv).P = LevelP.triv R.Pg D.R.r ℂ := rfl
  have hs : (R.datWp i R.triv).s = 0 := rfl
  have hQ : (R.datWp i R.triv).Q = ∅ := rfl
  have hchi : ∀ (Q : LevelP R.Pg D.R.r ℂ), Q = LevelP.triv R.Pg D.R.r ℂ → ∀ y : Q.H, Q.chi y = 1 := by
    rintro _ rfl y; rfl
  have h1 : ∀ x, ext1 (R.datWp i R.triv).P.H (⇑(R.datWp i R.triv).P.chi) x = 1 := by
    intro x
    unfold ext1
    split
    · exact hchi _ hP _
    · rfl
  simp only [levChi, levFn, h1, hs, hQ, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one,
    Units.val_one]

end GlobalTheory.PrincPet

namespace GlobalTheory.PrincPet

theorem petW_continuous_rightInv : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ i σ, IsOpen {h : GA D (Wc D i) | finE (Wc D i) h ∈ lev D.sp.cm (Wc D i).gram (R.βW i) (R.datWp i R.triv)} ∧ ∀ U₁ ∈ R.Wall i σ, ∀ U₂ ∈ R.Wall i σ, ∀ v₁ v₂ : (R.MW i σ).Vec, (Continuous fun g => petW R i (rTr (Wc D i) g (U₁ v₁)) (U₂ v₂)) ∧ ∀ g, ∀ k ∈ levW R i, petW R i (rTr (Wc D i) (g * k) (U₁ v₁)) (U₂ v₂) = petW R i (rTr (Wc D i) g (U₁ v₁)) (U₂ v₂) := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hC i σ
  refine ⟨GlobalTheory.AdelicScalar.isOpen_level (Wc D i) (R.βW i) (R.datWp i R.triv), ?_⟩
  intro U₁ hU₁ U₂ hU₂ v₁ v₂
  have hθ : IsInfFam R.θ := hC.models.inf
  have hχ : ∀ k ∈ levS (Wc D i) (R.βW i) (R.datWp i R.triv),
      levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1 := fun k _ => levChi_triv R i k
  obtain ⟨c₁, ⟨C₁, b₁⟩, inv₁⟩ := value_laws hP hθ hχ hU₁ v₁
  obtain ⟨c₂, ⟨C₂, b₂⟩, -⟩ := value_laws hP hθ hχ hU₂ v₂
  refine ⟨?_, fun g k hk => ?_⟩
  · have : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
    have hμ := (hC.models.νW i).1.1
    have hfin : R.νW i (R.fdW i) < ⊤ :=
      GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol (Wc D i) (R.νW i) (R.fdW i) hμ (hC.models.νW i).2
    haveI : IsFiniteMeasure ((R.νW i).restrict (R.fdW i)) := isFiniteMeasure_restrict.2 hfin.ne
    have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans (b₁ 1)
    show Continuous fun g => ∫ x in R.fdW i, rTr (Wc D i) g (U₁ v₁) x * starRingEnd ℂ (U₂ v₂ x) ∂(R.νW i)
    refine continuous_of_dominated (bound := fun _ => C₁ * C₂) (fun g => ?_) (fun g => ?_) (integrable_const _) ?_
    · exact ((c₁.comp (continuous_id.mul continuous_const)).mul
        (Complex.continuous_conj.comp c₂)).aestronglyMeasurable
    · refine .of_forall fun x => ?_
      simp only [rTr, norm_mul, Complex.norm_conj]
      exact mul_le_mul (b₁ _) (b₂ _) (norm_nonneg _) hC₁
    · exact .of_forall fun x => (c₁.comp (continuous_const.mul continuous_id)).mul continuous_const
  · have e : rTr (Wc D i) (g * k) (U₁ v₁) = rTr (Wc D i) g (U₁ v₁) := by
      funext x
      simp only [rTr]
      rw [← mul_assoc]
      exact inv₁ k hk (x * g)
    rw [e]

end GlobalTheory.PrincPet

end

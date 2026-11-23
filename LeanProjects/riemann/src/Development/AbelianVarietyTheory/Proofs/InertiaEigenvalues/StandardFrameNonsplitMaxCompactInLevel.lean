import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyPolarized
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaOfOfIsCharLab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open scoped TensorProduct

noncomputable section
set_option maxHeartbeats 1000000

namespace GlobalTheory.NonSplitLevel

theorem comp_swapCast {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) (Q : HeightOneSpectrum (𝓞 E))
    (x y : E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2)
    (e : Algebra.TensorProduct.map (AlgHom.id F2 E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F2 (Q.under (𝓞 F2))) x =
      Algebra.TensorProduct.map (AlgHom.id F2 E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F2 (Q.under (𝓞 F2))) y) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F1 (Q.under (𝓞 F1))) (AlgHom.id F1 E) ((swapCast h).symm x) =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F1 (Q.under (𝓞 F1))) (AlgHom.id F1 E) ((swapCast h).symm y) := by
  subst h
  have key : ∀ z : E ⊗[F1] FiniteAdeleRing (𝓞 F1) F1,
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F1 (Q.under (𝓞 F1))) (AlgHom.id F1 E) ((swapCast (rfl : F1 = F1)).symm z) =
        Algebra.TensorProduct.comm F1 E _
          (Algebra.TensorProduct.map (AlgHom.id F1 E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F1 (Q.under (𝓞 F1))) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [key, key, e]

variable {D : D7}

theorem projV_eq_one {V : TH.HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : Formalism.IndefR.principalLevelFrame.RowPsi V n}
    (hP : StdFrame hF P) (κ : GAf D.host.E n) (Q : PlE D.host)
    (hκ : (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map
      (compAt D.host.E (HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) Q)) = 1) :
    GlobalTheory.FinZeta.projV V (Q.under (𝓞 D.host.F)) (P.ψ κ) = 1 := by
  classical
  obtain ⟨⟨β, β', h1, -, hβ⟩, -⟩ := hP
  let g := (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F (Q.under (𝓞 D.host.F))) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hK : ((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (swapCast hF).symm).map g = 1 := by
    ext i j
    have e2 := congrFun (congrFun hκ i) j
    rw [Matrix.map_apply] at e2
    rw [Matrix.map_apply, Matrix.map_apply]
    rw [Matrix.one_apply] at e2 ⊢
    split_ifs at e2 ⊢
    · exact (comp_swapCast hF Q _ 1 (e2.trans (map_one _).symm)).trans (by rw [map_one, map_one])
    · exact (comp_swapCast hF Q _ 0 (e2.trans (map_zero _).symm)).trans (by rw [map_zero, map_zero])
  refine GlobalTheory.AdelicU.matHom_injective _ D.sp.cm.sig V.gram (Units.ext ?_)
  rw [MonoidHom.map_one, Units.val_one]
  have e1 : (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.FinZeta.projV V (Q.under (𝓞 D.host.F)) (P.ψ κ))).1 =
      (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (P.ψ κ)).map g :=
    Matrix.ext fun i j => (GlobalTheory.FinZeta.LevelOff.evalV_finPart (Q.under (𝓞 D.host.F)) _).symm
  rw [e1, hβ κ, Matrix.map_mul, Matrix.map_mul, hK, Matrix.mul_one, ← Matrix.map_mul, h1,
    Matrix.map_one _ (map_zero g) (map_one g)]

theorem split_of_not_conj {Q : PlE D.host} (h : ¬ Formalism.IndefR.Lev.IsConjPl Q Q) : IsSplitPl D.host Q := by
  unfold Formalism.IndefR.Lev.IsConjPl at h
  push Not at h
  obtain ⟨c, hc, h⟩ := h
  have e : star (c : D.host.E) = D.host.conj c := by
    apply D.host.φ₀.injective
    have := D.host.isCMField_hostE
    exact (IsCMField.complexEmbedding_complexConj _ D.host.φ₀ _).trans
      (D.host.conjE_apply D.host.φ₀ _).symm
  exact ⟨c, hc, fun y hy hyQ => h y hyQ (hy.trans e.symm)⟩

theorem mem_level {V : TH.HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : Formalism.IndefR.principalLevelFrame.RowPsi V n}
    (hP : StdFrame hF P) {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (hL : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → IsSplitPl D.host PP) {w' : PlE D.host} (hw : ¬ IsSplitPl D.host w')
    {κ : GAf D.host.E n} (hU : κ ∈ Umax D.host.E n)
    (hT : TrivOutside {HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w'} κ) :
    P.ψ κ ∈ Formalism.IndefR.Links.levS V β L ∧ Formalism.IndefR.Lev.levChi V β L (P.ψ κ) = 1 := by
  have hS := (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hB (P.into κ)).2 ((hP.2 κ).1 hU)
  have hred : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
    intro PP hPP
    refine GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {PP.under (𝓞 D.host.F)} hS (fun u hu => ?_) (Finset.mem_singleton_self _)
    rw [Finset.mem_singleton.1 hu]
    refine projV_eq_one hP κ PP (hT _ fun e => ?_)
    have e' : HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) PP =
        HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w' := e
    exact GlobalTheory.SphNonSplit.not_split_of_overPl D (w := w') (w' := PP)
      (v := HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w') rfl
      (congrArg HeightOneSpectrum.asIdeal e') hw (hL PP hPP)
  refine ⟨⟨P.into κ, GlobalTheory.LevSplit.mem_lev_of_red _ _ β L _ (GlobalTheory.LevSplit.finE_mem_UA V _) hS hred⟩, ?_⟩
  unfold Formalism.IndefR.Lev.levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one β L _ hred, Units.val_one]

theorem lift_level : OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (i : Fin (w.st Z).toD7.R.m)
      (P : Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (w.st Z).toD7.R.nV), StdFrame Y.hF P →
      ∀ w' : PlE (w.st Z).toD7.host, ¬ IsSplitPl (w.st Z).toD7.host w' →
      ∀ κ ∈ Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
        TrivOutside {HeightOneSpectrum.under (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) w'} κ →
        P.ψ κ ∈ Formalism.IndefR.Links.levS _ (z.R.toRealDat.βV i)
            (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0) (z.R.toRealDat.levR z.F.lv2 false)) ∧
          Formalism.IndefR.Lev.levChi _ (z.R.toRealDat.βV i)
            (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0) (z.R.toRealDat.levR z.F.lv2 false))
            (P.ψ κ) = 1 := by
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w _ Z Wt hX z p0 Y _ _ _ _ _ i P hP w' hw κ hU hT => ?_
  have hlev := z.pins.char.base.lev
  obtain ⟨c, hc⟩ := hlev.βV i
  rw [one_pow] at hc
  refine mem_level hP hc _ (fun PP hPP => ?_) hw hU hT
  rcases hPP with h | h
  · obtain ⟨k, hk⟩ := (hlev.Pg PP).1 h
    exact GlobalTheory.SphNonSplit.split_of_over_g _ k (GlobalTheory.Mem.TypePl.div_over _ hk)
  · exact split_of_not_conj ((hlev.Q_pl _ PP h).2 PP h)

end GlobalTheory.NonSplitLevel

end

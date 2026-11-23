import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocSubLocGen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicTypeFiniteDimStableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubmodulePowSimpleEqSumEquivValuesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelKFiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacesDistinctTranslationsDerivativesCommuteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.CuspGKId

theorem local_sum_model : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (φ : GA D V → ℂ), IsAutFunSm θ V φ → IsTypeAt θ V τ (S τ) φ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W) →
    ∃ (m : ℕ) (T : Fin m → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] (GA D V → ℂ)))
      (p : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ (M.ε τ) (M.σ τ) (M.fr τ) (T j)) ∧ φ = ∑ j, T j (p j) := GlobalTheory.T.automorphic_type_finite_dim_stable

theorem sub_pow_sum : ∀ {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type} (a : ι → Module.End ℂ P),
    (∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) →
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, ∃ (n : ℕ) (Sm : Fin n → (P →ₗ[ℂ] (Fin m → P))) (q : Fin n → P),
      (∀ l i p, Sm l (a i p) = fun j => a i (Sm l p j)) ∧ (∀ l p, Sm l p ∈ N) ∧ y = ∑ l, Sm l (q l) := GlobalTheory.T.exists_sum_intertwined_of_mem_invariant_submodule

theorem kfin_struct : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau),
    (∃ p : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), p ≠ 0) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
      ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), M.rep τ g (v : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) ∧
    (∀ X ∈ lieAt V τ, ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), ∃ w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ),
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0) ∧
    ∀ B : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), B ≠ ⊥ →
      (∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), v ∈ B →
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 → w ∈ B) → B = ⊤ := GlobalTheory.T.discrete_series_model_K_finite

theorem place_comm : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    IsInfFam (D := D) θ → ∀ τ τ' : D.what₂.Tau, τ ≠ τ' →
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), ∀ f : GA D V → ℂ,
      rTr V (atTau θ V τ g) (rTr V (atTau θ V τ' h) f) = rTr V (atTau θ V τ' h) (rTr V (atTau θ V τ g) f)) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ X ∈ lieAt V τ', ∀ f : GA D V → ℂ,
      Rder θ V τ' X (rTr V (atTau θ V τ g) f) = rTr V (atTau θ V τ g) (Rder θ V τ' X f)) ∧
    (∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt V τ', ∀ f : GA D V → ℂ, IsAutFunSm θ V f →
      Rder θ V τ X (Rder θ V τ' Y f) = Rder θ V τ' Y (Rder θ V τ X f)) := GlobalTheory.T.realPlaces_distinct_translations_derivatives_commute

end GlobalTheory.CuspGKId

noncomputable section

namespace GlobalTheory.CuspGKId

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}

variable (M) in

abbrev Tup : Type := ∀ τ : D.what₂.Tau, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)

variable (M) in

abbrev MMK : Type := MultilinearMap ℂ (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (GA D V → ℂ)

variable (θ M) in

structure IsPartMult (A : Submodule ℂ (GA D V → ℂ)) (s : Finset D.what₂.Tau) (p0 : Tup M)
    (lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ) (F : MMK M) : Prop where
  mem : ∀ u, F u ∈ A
  equivK : ∀ τ ∈ s, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
    ∀ (u : Tup M) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), (w : M.H τ) = M.rep τ g (u τ) →
      F (Function.update u τ w) = rTr V (atTau θ V τ g) (F u)
  equivLie : ∀ τ ∈ s, ∀ X ∈ lieAt V τ, ∀ (u : Tup M) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
    HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (u τ : M.H τ)) (w : M.H τ) 0 →
      F (Function.update u τ w) = Rder θ V τ X (F u)
  other : ∀ τ ∉ s, ∀ (u : Tup M) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
    F (Function.update u τ w) = lam τ w • F (Function.update u τ (p0 τ))

variable (θ M) in

def partSub (A : Submodule ℂ (GA D V → ℂ)) (hsm : ∀ f ∈ A, IsAutFunSm θ V f) (s : Finset D.what₂.Tau) (p0 : Tup M)
    (lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ) : Submodule ℂ (MMK M) where
  carrier := {F | IsPartMult θ M A s p0 lam F}
  zero_mem' :=
    { mem := fun _ => A.zero_mem
      equivK := fun _ _ _ _ _ _ _ _ => rfl
      equivLie := fun τ _ X _ _ _ _ => (Formalism.IndefR.Mult.rder_zero θ V τ X).symm
      other := fun _ _ _ _ => (smul_zero _).symm }
  add_mem' := by
    intro F G hF hG
    refine ⟨fun u => A.add_mem (hF.mem u) (hG.mem u), fun τ hτ g hg hk u w hw => ?_,
      fun τ hτ X hX u w hw => ?_, fun τ hτ u w => ?_⟩
    · simp only [MultilinearMap.add_apply, hF.equivK τ hτ g hg hk u w hw, hG.equivK τ hτ g hg hk u w hw]
      rfl
    · simp only [MultilinearMap.add_apply, hF.equivLie τ hτ X hX u w hw, hG.equivLie τ hτ X hX u w hw]
      exact (GlobalTheory.Mem.AutSpace.Rder_add (hsm _ (hF.mem u)).smooth (hsm _ (hG.mem u)).smooth hX).symm
    · simp only [MultilinearMap.add_apply, hF.other τ hτ u w, hG.other τ hτ u w, smul_add]
  smul_mem' := by
    intro c F hF
    refine ⟨fun u => A.smul_mem c (hF.mem u), fun τ hτ g hg hk u w hw => ?_,
      fun τ hτ X hX u w hw => ?_, fun τ hτ u w => ?_⟩
    · simp only [MultilinearMap.smul_apply, hF.equivK τ hτ g hg hk u w hw]
      rfl
    · simp only [MultilinearMap.smul_apply, hF.equivLie τ hτ X hX u w hw]
      exact (GlobalTheory.Mem.AutSpace.Rder_smul c _ τ X).symm
    · simp only [MultilinearMap.smul_apply, hF.other τ hτ u w]
      exact smul_comm _ _ _

def evAt (p0 : Tup M) : MMK M →ₗ[ℂ] (GA D V → ℂ) where
  toFun F := F p0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (V) in

def rTrL (k : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := rTr V k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def postRder (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (F : MMK M)
    (hF : ∀ u, IsAutFunSm θ V (F u)) : MMK M where
  toFun u := Rder θ V τ X (F u)
  map_update_add' u i a b := by
    rw [F.map_update_add, GlobalTheory.Mem.AutSpace.Rder_add (hF _).smooth (hF _).smooth hX]
  map_update_smul' u i c a := by
    rw [F.map_update_smul, GlobalTheory.Mem.AutSpace.Rder_smul]

end GlobalTheory.CuspGKId

noncomputable section

namespace GlobalTheory.CuspGKId

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem Rder_sum {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) {n : ℕ}
    (f : Fin n → GA D V → ℂ) (hf : ∀ j, IsAutFunSm θ V (f j)) :
    Rder θ V τ X (∑ j, f j) = ∑ j, Rder θ V τ X (f j) := by
  classical
  have key : ∀ t : Finset (Fin n), Rder θ V τ X (∑ j ∈ t, f j) = ∑ j ∈ t, Rder θ V τ X (f j) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using Formalism.IndefR.Mult.rder_zero θ V τ X
    | insert j t hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, GlobalTheory.Mem.AutSpace.Rder_add (hf j).smooth
        ((GlobalTheory.Mem.AutSpace.SmFun θ V).sum_mem fun j _ => (hf j).smooth) hX, ih]
  exact key Finset.univ

theorem isAutFunSm_sum {n : ℕ} (f : Fin n → GA D V → ℂ) (hf : ∀ j, IsAutFunSm θ V (f j)) :
    IsAutFunSm θ V (∑ j, f j) := by
  classical
  have key : ∀ t : Finset (Fin n), IsAutFunSm θ V (∑ j ∈ t, f j) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      exact Formalism.IndefR.Mult.isAutFunSm_zero θ V
    | insert j t hj ih =>
      rw [Finset.sum_insert hj]
      exact GlobalTheory.Mem.AutSpace.isAutFunSm_add (hf j) ih
  exact key Finset.univ

theorem local_sum_gen : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (φ : GA D V → ℂ), IsAutFunSm θ V φ → IsTypeAt θ V τ (S τ) φ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W) →
    ∃ (n : ℕ) (T : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] (GA D V → ℂ)))
      (p : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ l, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ (M.ε τ) (M.σ τ) (M.fr τ) (T l)) ∧
      (∀ l v, T l v ∈ GlobalTheory.CuspGKId.locGen θ M τ φ) ∧ φ = ∑ l, T l (p l) := by
  intro hPr D θ V S M hθ τ φ hφ hty hW
  obtain ⟨m, T, p, hT, hsum⟩ := local_sum_model hPr θ V S M hθ τ φ hφ hty hW
  obtain ⟨-, hKst, hder, hsimp⟩ := kfin_struct hPr V S M τ
  let P := GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)

  let kOp : {g // g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)} → Module.End ℂ P :=
    fun g => LinearMap.codRestrict P ((M.rep τ g.1 : M.H τ →ₗ[ℂ] M.H τ).comp P.subtype) fun v => hKst g.1 g.2.1 g.2.2 v
  have hdu : ∀ X ∈ lieAt V τ, ∀ v w w' : P,
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 →
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w' : M.H τ) 0 → w = w' :=
    fun X _ v w w' h h' => Subtype.ext (h.unique h')
  let dOp : {X // X ∈ lieAt V τ} → Module.End ℂ P := fun X =>
    { toFun := fun v => Classical.choose (hder X.1 X.2 v)
      map_add' := fun a b => by
        refine (hdu X.1 X.2 (a + b) _ _ (Classical.choose_spec (hder X.1 X.2 (a + b))) ?_)
        have h := (Classical.choose_spec (hder X.1 X.2 a)).add (Classical.choose_spec (hder X.1 X.2 b))
        have e : (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X.1)) ((a + b : P) : M.H τ)) =
            fun t => M.rep τ (NormedSpace.exp (t • X.1)) (a : M.H τ) + M.rep τ (NormedSpace.exp (t • X.1)) (b : M.H τ) :=
          funext fun t => by rw [Submodule.coe_add, map_add]
        rw [e, Submodule.coe_add]
        exact h
      map_smul' := fun c a => by
        refine (hdu X.1 X.2 (c • a) _ _ (Classical.choose_spec (hder X.1 X.2 (c • a))) ?_)
        have h := (Classical.choose_spec (hder X.1 X.2 a)).const_smul c
        have e : (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X.1)) ((c • a : P) : M.H τ)) =
            fun t => c • M.rep τ (NormedSpace.exp (t • X.1)) (a : M.H τ) :=
          funext fun t => by rw [Submodule.coe_smul, map_smul]
        rw [e, Submodule.coe_smul]
        exact h }
  have hdOp : ∀ X : {X // X ∈ lieAt V τ}, ∀ v : P,
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X.1)) (v : M.H τ)) (dOp X v : M.H τ) 0 :=
    fun X v => Classical.choose_spec (hder X.1 X.2 v)
  let a : ({g // g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)} ⊕
      {X // X ∈ lieAt V τ}) → Module.End ℂ P := fun i => Sum.elim kOp dOp i
  have hsimple : ∀ B : Submodule ℂ P, (∀ i, ∀ v ∈ B, a i v ∈ B) → B ≠ ⊥ → B = ⊤ := fun B hB h0 =>
    hsimp B h0 fun X hX v w hv hd => by
      rw [hdu X hX v w _ hd (hdOp ⟨X, hX⟩ v)]
      exact hB (Sum.inr ⟨X, hX⟩) v hv

  let Ttot : (Fin m → P) →ₗ[ℂ] (GA D V → ℂ) := ∑ j, (T j).comp (LinearMap.proj j)
  have hTtot : ∀ y, Ttot y = ∑ j, T j (y j) := fun y => by
    simp [Ttot, LinearMap.sum_apply]
  have hTK : ∀ (g : {g // g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)})
      (y : Fin m → P), Ttot (fun j => kOp g (y j)) = rTr V (atTau θ V τ g.1) (Ttot y) := fun g y => by
    rw [hTtot, hTtot, show rTr V (atTau θ V τ g.1) (∑ j, T j (y j)) = ∑ j, rTr V (atTau θ V τ g.1) (T j (y j))
      from map_sum (rTrL V (atTau θ V τ g.1)) (fun j => T j (y j)) Finset.univ]
    exact Finset.sum_congr rfl fun j _ => (hT j).mapK g.1 g.2.1 g.2.2 (y j) _ rfl
  have hTL : ∀ (X : {X // X ∈ lieAt V τ}) (y : Fin m → P), Ttot (fun j => dOp X (y j)) = Rder θ V τ X.1 (Ttot y) :=
    fun X y => by
      rw [hTtot, hTtot, Rder_sum X.2 _ fun j => (hT j).aut _]
      exact Finset.sum_congr rfl fun j _ => (hT j).mapLie X.1 X.2 (y j) _ (hdOp X (y j))
  have hloc := isLocSub_locGen θ M τ φ
  let N : Submodule ℂ (Fin m → P) := (locGen θ M τ φ).comap Ttot
  have hN : ∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N := by
    rintro (g | X) y hy
    · show Ttot (fun j => kOp g (y j)) ∈ locGen θ M τ φ
      rw [hTK]
      exact hloc.k g.1 g.2 _ hy
    · show Ttot (fun j => dOp X (y j)) ∈ locGen θ M τ φ
      rw [hTL]
      exact hloc.lie X.1 X.2 _ hy
  have hpN : p ∈ N := by
    show Ttot p ∈ locGen θ M τ φ
    rw [hTtot, ← hsum]
    exact mem_locGen θ M τ φ
  obtain ⟨n, Sm, q, hSa, hSN, hpq⟩ := sub_pow_sum a hsimple m N hN p hpN
  refine ⟨n, fun l => Ttot.comp (Sm l), q, fun l => ⟨fun v => ?_, fun g hg hk v w hw => ?_,
    fun X hX v w hw => ?_⟩, fun l v => hSN l v, ?_⟩
  · rw [LinearMap.comp_apply, hTtot]
    exact isAutFunSm_sum _ fun j => (hT j).aut _
  · have e : w = kOp ⟨g, hg, hk⟩ v := Subtype.ext hw
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    have := hSa l (Sum.inl ⟨g, hg, hk⟩) v
    simp only [a, Sum.elim_inl] at this
    rw [this, hTK]
  · have e : w = dOp ⟨X, hX⟩ v := hdu X hX v w _ hw (hdOp ⟨X, hX⟩ v)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    have := hSa l (Sum.inr ⟨X, hX⟩) v
    simp only [a, Sum.elim_inr] at this
    rw [this, hTL]
  · rw [hsum, ← hTtot p, hpq, map_sum]
    rfl

end GlobalTheory.CuspGKId

noncomputable section

namespace GlobalTheory.CuspGKId

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}

theorem IsPartMult.eq_zero {A : Submodule ℂ (GA D V → ℂ)} {s : Finset D.what₂.Tau} {p0 : Tup M}
    {lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ} {F : MMK M} (hF : IsPartMult θ M A s p0 lam F)
    (hp0 : ∀ τ, p0 τ ≠ 0)
    (hsimple : ∀ τ, ∀ B : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), B ≠ ⊥ →
      (∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), v ∈ B →
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 → w ∈ B) → B = ⊤)
    (h0 : F p0 = 0) : F = 0 := by
  have key : ∀ t : Finset D.what₂.Tau, ∀ u : Tup M, (∀ τ ∉ t, u τ = p0 τ) → F u = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro u hu
      have : u = p0 := funext fun τ => hu τ (Finset.notMem_empty τ)
      rw [this, h0]
    | insert τ t hτt ih =>
      intro u hu
      have h1 : F (Function.update u τ (p0 τ)) = 0 := ih _ fun τ' h' => by
        by_cases e : τ' = τ
        · subst e
          simp
        · rw [Function.update_of_ne e]
          exact hu τ' (by simp [e, h'])
      by_cases hs : τ ∈ s
      · let B : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) :=
          { carrier := {w | F (Function.update u τ w) = 0}
            zero_mem' := by
              show F (Function.update u τ 0) = 0
              exact F.map_coord_zero τ (by simp)
            add_mem' := by
              intro a b ha hb
              show F (Function.update u τ (a + b)) = 0
              rw [F.map_update_add]
              rw [show F (Function.update u τ a) = 0 from ha, show F (Function.update u τ b) = 0 from hb, add_zero]
            smul_mem' := by
              intro c a ha
              show F (Function.update u τ (c • a)) = 0
              rw [F.map_update_smul, show F (Function.update u τ a) = 0 from ha, smul_zero] }
        have hB : B = ⊤ := by
          refine hsimple τ B ?_ ?_
          · intro e
            have : p0 τ ∈ B := h1
            rw [e, Submodule.mem_bot] at this
            exact hp0 τ this
          · intro X hX v w hv hd
            show F (Function.update u τ w) = 0
            have := hF.equivLie τ hs X hX (Function.update u τ v) w (by simpa using hd)
            rw [Function.update_idem] at this
            rw [this, show F (Function.update u τ v) = 0 from hv]
            exact Formalism.IndefR.Mult.rder_zero θ V τ X
        have : u τ ∈ B := hB ▸ Submodule.mem_top
        have e : F (Function.update u τ (u τ)) = 0 := this
        rwa [Function.update_eq_self] at e
      · rw [← Function.update_eq_self τ u, hF.other τ hs, h1, smul_zero]
  ext u : 1
  exact key Finset.univ u fun τ h => absurd (Finset.mem_univ τ) h

end GlobalTheory.CuspGKId

noncomputable section

namespace GlobalTheory.CuspGKId

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}

theorem IsPartMult.rTr_comp (hθ : IsInfFam (D := D) θ) {A : Submodule ℂ (GA D V → ℂ)}
    (hA : GlobalTheory.CuspGK.IsGKSub θ M A) {s : Finset D.what₂.Tau} {p0 : Tup M}
    {lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ} {F : MMK M} (hF : IsPartMult θ M A s p0 lam F)
    {τ : D.what₂.Tau} (hτ : τ ∉ s) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : GlobalTheory.CuspGK.InK M τ g) :
    IsPartMult θ M A s p0 lam ((rTrL V (atTau θ V τ g)).compMultilinearMap F) := by
  refine ⟨fun u => hA.k τ g hg _ (hF.mem u), fun τ' hτ' h hh hk u w hw => ?_, fun τ' hτ' Y hY u w hw => ?_,
    fun τ' hτ' u w => ?_⟩
  · have hne : τ ≠ τ' := fun e => hτ (e ▸ hτ')
    simp only [LinearMap.compMultilinearMap_apply, rTrL, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hF.equivK τ' hτ' h hh hk u w hw]
    exact (place_comm θ V hθ τ τ' hne).1 g hg.1 h hh _
  · have hne : τ ≠ τ' := fun e => hτ (e ▸ hτ')
    simp only [LinearMap.compMultilinearMap_apply, rTrL, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hF.equivLie τ' hτ' Y hY u w hw]
    exact ((place_comm θ V hθ τ τ' hne).2.1 g hg.1 Y hY _).symm
  · simp only [LinearMap.compMultilinearMap_apply, hF.other τ' hτ' u w, map_smul]

theorem IsPartMult.postRder_comp (hθ : IsInfFam (D := D) θ) {A : Submodule ℂ (GA D V → ℂ)}
    (hA : GlobalTheory.CuspGK.IsGKSub θ M A) (hsm : ∀ f ∈ A, IsAutFunSm θ V f) {s : Finset D.what₂.Tau} {p0 : Tup M}
    {lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ} {F : MMK M} (hF : IsPartMult θ M A s p0 lam F)
    {τ : D.what₂.Tau} (hτ : τ ∉ s) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    IsPartMult θ M A s p0 lam (postRder (θ := θ) τ X hX F fun u => hsm _ (hF.mem u)) := by
  refine ⟨fun u => hA.lie τ X hX _ (hF.mem u), fun τ' hτ' h hh hk u w hw => ?_, fun τ' hτ' Y hY u w hw => ?_,
    fun τ' hτ' u w => ?_⟩
  · have hne : τ' ≠ τ := fun e => hτ (e ▸ hτ')
    show Rder θ V τ X (F _) = rTr V _ (Rder θ V τ X (F u))
    rw [hF.equivK τ' hτ' h hh hk u w hw]
    exact (place_comm θ V hθ τ' τ hne).2.1 h hh X hX _
  · have hne : τ ≠ τ' := fun e => hτ (e ▸ hτ')
    show Rder θ V τ X (F _) = Rder θ V τ' Y (Rder θ V τ X (F u))
    rw [hF.equivLie τ' hτ' Y hY u w hw]
    exact (place_comm θ V hθ τ τ' hne).2.2 X hX Y hY _ (hsm _ (hF.mem u))
  · show Rder θ V τ X (F _) = lam τ' w • Rder θ V τ X (F _)
    rw [hF.other τ' hτ' u w, GlobalTheory.Mem.AutSpace.Rder_smul]

end GlobalTheory.CuspGKId

noncomputable section

namespace GlobalTheory.CuspGKId

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}

theorem IsPartMult.decomp (hPr : GlobalTheory.FunPr.Hypotheses₂) (hθ : IsInfFam (D := D) θ) {A : Submodule ℂ (GA D V → ℂ)}
    (hA : GlobalTheory.CuspGK.IsGKSub θ M A) (hAf : ∀ f ∈ A, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f) {s : Finset D.what₂.Tau}
    {p0 : Tup M} {lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ} (hp0 : ∀ τ, p0 τ ≠ 0)
    (hsimple : ∀ τ, ∀ B : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), B ≠ ⊥ →
      (∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), v ∈ B →
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 → w ∈ B) → B = ⊤)
    {F : MMK M} (hF : IsPartMult θ M A s p0 lam F) {τ : D.what₂.Tau} (hτ : τ ∉ s) :
    ∃ (n : ℕ) (T : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] MMK M))
      (q : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ m p, IsPartMult θ M A s p0 lam (T m p)) ∧
      (∀ m, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
        ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), (w : M.H τ) = M.rep τ g v →
          ∀ u, T m w u = rTr V (atTau θ V τ g) (T m v u)) ∧
      (∀ m, ∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ),
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 →
          ∀ u, T m w u = Rder θ V τ X (T m v u)) ∧
      F = ∑ m, T m (q m) := by
  have hsm : ∀ f ∈ A, IsAutFunSm θ V f := fun f hf => (hAf f hf).1
  set Hs := partSub θ M A hsm s p0 lam with hHs
  have hinj : ∀ F₁ ∈ Hs, ∀ F₂ ∈ Hs, F₁ p0 = F₂ p0 → F₁ = F₂ := by
    intro F₁ h₁ F₂ h₂ e
    have h3 : F₁ - F₂ ∈ Hs := Hs.sub_mem h₁ h₂
    have := IsPartMult.eq_zero h3 hp0 hsimple (by rw [MultilinearMap.sub_apply, e, sub_self])
    exact sub_eq_zero.1 this
  set E := Hs.map (evAt p0) with hE
  have hEloc : IsLocSub θ M τ E := by
    refine ⟨fun g hg y hy => ?_, fun X hX y hy => ?_⟩
    · obtain ⟨F', hF', rfl⟩ := hy
      exact ⟨_, IsPartMult.rTr_comp hθ hA hF' hτ hg, rfl⟩
    · obtain ⟨F', hF', rfl⟩ := hy
      exact ⟨_, IsPartMult.postRder_comp hθ hA hsm hF' hτ hX, rfl⟩
  have hx : F p0 ∈ A := hF.mem p0
  obtain ⟨hxa, -, hxt, W, hW1, hW2, hW3⟩ := hAf _ hx
  obtain ⟨n, T, p, hT, hTl, hsum⟩ :=
    local_sum_gen hPr θ V S M hθ τ (F p0) hxa (hxt τ) ⟨W, hW1, hW2, hW3 τ⟩
  have hgen : locGen θ M τ (F p0) ≤ E := locGen_le θ M ⟨F, hF, rfl⟩ hEloc
  let f := (evAt p0).domRestrict Hs
  have hfi : Function.Injective f := fun a b e => Subtype.ext (hinj a a.2 b b.2 e)
  let e := LinearEquiv.ofInjective f hfi
  have hrange : ∀ l v, T l v ∈ LinearMap.range f := fun l v => by
    rw [LinearMap.range_domRestrict]
    exact hgen (hTl l v)
  let T' : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] MMK M) := fun l =>
    Hs.subtype.comp (e.symm.toLinearMap.comp ((T l).codRestrict (LinearMap.range f) (hrange l)))
  have hT'mem : ∀ l v, T' l v ∈ Hs := fun l v => (e.symm _).2
  have hT'ev : ∀ l v, T' l v p0 = T l v := fun l v => by
    have := LinearEquiv.ofInjective_apply (h := hfi) f (e.symm ⟨T l v, hrange l v⟩)
    have h2 : e (e.symm ⟨T l v, hrange l v⟩) = ⟨T l v, hrange l v⟩ := e.apply_symm_apply _
    exact (this.symm.trans (congrArg Subtype.val h2))
  refine ⟨n, T', p, fun m v => hT'mem m v, fun m g hg hk v w hw u => ?_, fun m X hX v w hw u => ?_, ?_⟩
  · have h1 : T' m w = (rTrL V (atTau θ V τ g)).compMultilinearMap (T' m v) :=
      hinj _ (hT'mem m w) _ (IsPartMult.rTr_comp hθ hA (hT'mem m v) hτ ⟨hg, hk⟩) (by
        rw [hT'ev, LinearMap.compMultilinearMap_apply, hT'ev]
        exact (hT m).mapK g hg hk v w hw)
    rw [h1]
    rfl
  · have h1 : T' m w = GlobalTheory.CuspGKId.postRder (θ := θ) τ X hX (T' m v) (fun u => hsm _ ((hT'mem m v).mem u)) :=
      hinj _ (hT'mem m w) _ (IsPartMult.postRder_comp hθ hA hsm (hT'mem m v) hτ hX) (by
        rw [hT'ev]
        show T m w = Rder θ V τ X (T' m v p0)
        rw [hT'ev]
        exact (hT m).mapLie X hX v w hw)
    rw [h1]
    rfl
  · refine hinj _ hF _ (Hs.sum_mem fun m _ => hT'mem m (p m)) ?_
    rw [MultilinearMap.sum_apply]
    simp only [hT'ev]
    exact hsum

end GlobalTheory.CuspGKId

noncomputable section

namespace GlobalTheory.CuspGKId

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}

def glue (τ : D.what₂.Tau) (T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] MMK M)
    (p : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) : MMK M where
  toFun u := T (u τ) (Function.update u τ p)
  map_update_add' := by
    intro inst u i a b
    obtain rfl : inst = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
    by_cases h : i = τ
    · subst h
      simp only [Function.update_self, Function.update_idem, map_add, MultilinearMap.add_apply]
    · simp only [Function.update_of_ne (Ne.symm h), Function.update_comm h]
      exact (T (u τ)).map_update_add _ i a b
  map_update_smul' := by
    intro inst u i c a
    obtain rfl : inst = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
    by_cases h : i = τ
    · subst h
      simp only [Function.update_self, Function.update_idem, map_smul, MultilinearMap.smul_apply]
    · simp only [Function.update_of_ne (Ne.symm h), Function.update_comm h]
      exact (T (u τ)).map_update_smul _ i c a

theorem glue_apply (τ : D.what₂.Tau) (T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] MMK M)
    (p : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (u : Tup M) : glue τ T p u = T (u τ) (Function.update u τ p) := rfl

theorem isPartMult_glue {A : Submodule ℂ (GA D V → ℂ)} {s : Finset D.what₂.Tau} {p0 : Tup M}
    {lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ} {τ : D.what₂.Tau} (hτ : τ ∉ s)
    {T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] MMK M} (hT : ∀ p, IsPartMult θ M A s p0 lam (T p))
    (hK : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
        ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), (w : M.H τ) = M.rep τ g v →
          ∀ u, T w u = rTr V (atTau θ V τ g) (T v u))
    (hL : ∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ),
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 →
          ∀ u, T w u = Rder θ V τ X (T v u)) :
    IsPartMult θ M A (insert τ s) p0 lam (glue τ T (p0 τ)) := by
  refine ⟨fun u => (hT _).mem _, fun τ' hτ' g hg hk u w hw => ?_, fun τ' hτ' X hX u w hw => ?_,
    fun τ' hτ' u w => ?_⟩
  · rw [glue_apply, glue_apply]
    by_cases e : τ' = τ
    · subst e
      simp only [Function.update_self, Function.update_idem]
      exact hK g hg hk _ _ hw _
    · have hs : τ' ∈ s := (Finset.mem_insert.1 hτ').resolve_left e
      rw [Function.update_of_ne (Ne.symm e), Function.update_comm e]
      refine (hT (u τ)).equivK τ' hs g hg hk _ w ?_
      rwa [Function.update_of_ne e]
  · rw [glue_apply, glue_apply]
    by_cases e : τ' = τ
    · subst e
      simp only [Function.update_self, Function.update_idem]
      exact hL X hX _ _ hw _
    · have hs : τ' ∈ s := (Finset.mem_insert.1 hτ').resolve_left e
      rw [Function.update_of_ne (Ne.symm e), Function.update_comm e]
      refine (hT (u τ)).equivLie τ' hs X hX _ w ?_
      rwa [Function.update_of_ne e]
  · have e : τ' ≠ τ := fun h => hτ' (h ▸ Finset.mem_insert_self τ s)
    have hs : τ' ∉ s := fun h => hτ' (Finset.mem_insert_of_mem h)
    rw [glue_apply, glue_apply, Function.update_of_ne (Ne.symm e), Function.update_comm e,
      (hT (u τ)).other τ' hs, Function.update_of_ne (Ne.symm e), Function.update_comm e]

theorem mem_span_partMult (hPr : GlobalTheory.FunPr.Hypotheses₂) (hθ : IsInfFam (D := D) θ) {A : Submodule ℂ (GA D V → ℂ)}
    (hA : GlobalTheory.CuspGK.IsGKSub θ M A) (hAf : ∀ f ∈ A, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f)
    {p0 : Tup M} {lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ} (hp0 : ∀ τ, p0 τ ≠ 0)
    (hlam : ∀ τ, lam τ (p0 τ) = 1)
    (hsimple : ∀ τ, ∀ B : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), B ≠ ⊥ →
      (∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), v ∈ B →
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 → w ∈ B) → B = ⊤)
    (s : Finset D.what₂.Tau) :
    A ≤ Submodule.span ℂ {y | ∃ (F : MMK M) (u : Tup M), IsPartMult θ M A s p0 lam F ∧ y = F u} := by
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    let F : MMK M := (MultilinearMap.mkPiRing ℂ D.what₂.Tau f).compLinearMap lam
    have hFu : ∀ u : Tup M, F u = (∏ τ, lam τ (u τ)) • f := fun u => by
      simp [F, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiRing_apply]
    refine Submodule.subset_span ⟨F, p0, ⟨fun u => by rw [hFu]; exact A.smul_mem _ hf,
      fun τ h => absurd h (Finset.notMem_empty τ), fun τ h => absurd h (Finset.notMem_empty τ),
      fun τ _ u w => ?_⟩, ?_⟩
    · rw [hFu, hFu, smul_smul]
      congr 1
      have h1 : ∀ w' : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ),
          (∏ τ', lam τ' (Function.update u τ w' τ')) = lam τ w' * ∏ τ' ∈ Finset.univ.erase τ, lam τ' (u τ') := by
        intro w'
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Function.update_self]
        congr 1
        refine Finset.prod_congr rfl fun τ' h' => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase h')]
      rw [h1, h1, hlam, one_mul]
    · rw [hFu, Finset.prod_congr rfl (fun τ _ => hlam τ), Finset.prod_const_one, one_smul]
  | insert τ s hτ ih =>
    refine ih.trans (Submodule.span_le.2 ?_)
    rintro y ⟨F, u, hF, rfl⟩
    obtain ⟨n, T, q, hT, hK, hL, hsum⟩ := IsPartMult.decomp hPr hθ hA hAf hp0 hsimple hF hτ
    rw [hsum, MultilinearMap.sum_apply]
    refine Submodule.sum_mem _ fun m _ => ?_
    have h1 : T m (q m) u = lam τ (u τ) • glue τ (T m) (p0 τ) (Function.update u τ (q m)) := by
      rw [glue_apply, Function.update_self, Function.update_idem, ← (hT m (q m)).other τ hτ u (u τ),
        Function.update_eq_self]
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, isPartMult_glue hτ (hT m) (hK m) (hL m), rfl⟩)

end GlobalTheory.CuspGKId

noncomputable section

namespace GlobalTheory.CuspGKId

theorem le_multSpan : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ A : Submodule ℂ (GA D V → ℂ), GlobalTheory.CuspGK.IsIrrGKSub θ M A → (∀ f ∈ A, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f) →
    A ≤ GlobalTheory.CuspGK.multSpan θ M := by
  intro hPr D θ V S M hθ A hA hAf
  have hA1 := hA.1
  have hst := fun τ => kfin_struct hPr V S M τ
  choose p0 hp0 using fun τ => (hst τ).1
  have hl : ∀ τ, ∃ l : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ, l (p0 τ) = 1 := by
    intro τ
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), φ (p0 τ) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hp0 τ ((Module.forall_dual_apply_eq_zero_iff ℂ (p0 τ)).1 h)
    exact ⟨(φ (p0 τ))⁻¹ • φ, by simp [hφ]⟩
  choose lam hlam using hl
  have hsimple := fun τ => (hst τ).2.2.2
  refine (mem_span_partMult hPr hθ hA1 hAf (p0 := p0) (lam := lam) hp0 hlam hsimple Finset.univ).trans ?_
  refine Submodule.span_mono ?_
  rintro y ⟨F, u, hF, rfl⟩
  refine ⟨F, u, ⟨fun v => (hAf _ (hF.mem v)).1, fun v => (hAf _ (hF.mem v)).2.1,
    fun τ => hF.equivK τ (Finset.mem_univ τ), fun τ => hF.equivLie τ (Finset.mem_univ τ)⟩, rfl⟩

end GlobalTheory.CuspGKId

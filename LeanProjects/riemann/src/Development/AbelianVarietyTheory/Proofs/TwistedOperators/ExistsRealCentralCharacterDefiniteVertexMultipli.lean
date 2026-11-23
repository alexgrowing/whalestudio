import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinCoefMultT
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DefCenChar

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

theorem unframe_mem_UH {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {u : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hu : u ∈ Formalism.MainNotions.S.UJset (M.ε τ)) :
    (M.fr τ)⁻¹ * u * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hJ : uᴴ * Formalism.REAL.Jm (M.ε τ) * u = Formalism.REAL.Jm (M.ε τ) := hu
  have e1 : M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ) = u * M.fr τ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  change ((M.fr τ)⁻¹ * u * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * u * M.fr τ) = gramAt D V τ
  rw [← M.fr_gram τ]
  calc ((M.fr τ)⁻¹ * u * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * ((M.fr τ)⁻¹ * u * M.fr τ)
      = (M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ))ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ)) := by
        rw [Matrix.conjTranspose_mul (M.fr τ)]; simp only [Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ := by
        rw [e1, Matrix.conjTranspose_mul]
        calc (M.fr τ)ᴴ * uᴴ * Formalism.REAL.Jm (M.ε τ) * (u * M.fr τ) = (M.fr τ)ᴴ * (uᴴ * Formalism.REAL.Jm (M.ε τ) * u) * M.fr τ := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hJ]

theorem rep_scalar {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)]
    {a : Matrix (Fin V.rank) (Fin V.rank) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), g * a = a * g) : ∃ c : ℂ, ∀ w, M.rep τ a w = c • w := by
  haveI : Nontrivial (M.H τ) := (M.ds τ).2.1
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  let A : Module.End ℂ (M.H τ) := (M.rep τ a : M.H τ →ₗ[ℂ] M.H τ)
  obtain ⟨c, hcA⟩ := Module.End.exists_eigenvalue A
  refine ⟨c, fun w => ?_⟩
  have hirr := (M.ds τ).2.2.2.1
  have hinv : ∀ u ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ v ∈ A.eigenspace c, M.σ τ u v ∈ A.eigenspace c := by
    intro u hu v hv
    have hg := unframe_mem_UH M τ hu
    have e : M.σ τ u = M.rep τ ((M.fr τ)⁻¹ * u * M.fr τ) := by
      unfold DSModel.rep
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [e]
    show M.rep τ a (M.rep τ _ v) = c • M.rep τ _ v
    rw [← GlobalTheory.ConjMult.rep_mul M τ _ ha _ hg, ← hc _ hg, GlobalTheory.ConjMult.rep_mul M τ _ hg _ ha]
    have hv' : M.rep τ a v = c • v := hv
    rw [hv', map_smul]
  rcases hirr (A.eigenspace c) (Submodule.closed_of_finiteDimensional _) hinv with h | h
  · exact absurd h hcA
  · have hw : w ∈ A.eigenspace c := h ▸ Submodule.mem_top
    exact (Module.End.mem_eigenspace_iff).1 hw

theorem infMat_comm {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {z : GA D V} (hzc : z ∈ Subgroup.center (GA D V))
    (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    g * infMat D.sp.cm.sig V.gram (θ τ) z = infMat D.sp.cm.sig V.gram (θ τ) z * g := by
  have e := congrArg (infMat D.sp.cm.sig V.gram (θ τ)) (Subgroup.mem_center_iff.1 hzc (atTau θ V τ g))
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul,
    (GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg).2.1] at e
  exact e

theorem rTr_atTau_of_scalar {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {c : ℂ} (hc : ∀ w, M.rep τ g w = c • w) (v : M.Vec) :
    rTr V (atTau θ V τ g) (T v) = c • T v := by
  classical
  have e := hT.equiv τ g hg v (c • v τ) (by rw [hc]; rfl)
  rw [← e, T.map_update_smul, Function.update_eq_self]

theorem rTr_realAll {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T)
    (Mz : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hM : ∀ ρ, Mz ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ))
    (c : D.what₂.Tau → ℂ) (hc : ∀ ρ w, M.rep ρ (Mz ρ) w = c ρ • w) (v : M.Vec) :
    rTr V (GlobalTheory.RowReal.realAll θ V Mz) (T v) = (∏ ρ, c ρ) • T v := by
  classical
  have key : ∀ s : Finset D.what₂.Tau,
      rTr V (GlobalTheory.RowReal.realAll θ V (fun ρ => if ρ ∈ s then Mz ρ else 1)) (T v) = (∏ ρ ∈ s, c ρ) • T v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : (fun ρ : D.what₂.Tau => if ρ ∈ (∅ : Finset D.what₂.Tau) then Mz ρ else 1) = 1 := by
        funext ρ; simp
      rw [e, GlobalTheory.RowReal.realAll_one hθ, Finset.prod_empty, one_smul]
      funext x; simp [rTr]
    | insert τ s hτ ih =>
      have hMs : ∀ ρ, (fun ρ => if ρ ∈ insert τ s then Mz ρ else 1) ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := fun ρ => by
        dsimp only
        split_ifs
        · exact hM ρ
        · exact GlobalTheory.PointAtPlaceHom.one_mem_UH _
      rw [GlobalTheory.RowReal.realAll_eq_atTau_mul hθ hMs τ]
      have e : Function.update (fun ρ => if ρ ∈ insert τ s then Mz ρ else 1) τ 1 =
          fun ρ => if ρ ∈ s then Mz ρ else 1 := by
        funext ρ
        by_cases h : ρ = τ
        · subst h; simp [hτ]
        · rw [Function.update_of_ne h]; simp [Finset.mem_insert, h]
      rw [e, Finset.prod_insert hτ]
      simp only [Finset.mem_insert_self, if_true]
      funext x
      have i1 := congrFun ih (x * atTau θ V τ (Mz τ))
      have i2 := congrFun (rTr_atTau_of_scalar hT τ (hM τ) (hc τ) v) x
      simp only [rTr, Pi.smul_apply, smul_eq_mul] at i1 i2 ⊢
      rw [← mul_assoc, i1, i2]
      ring
  have e : (fun ρ : D.what₂.Tau => if ρ ∈ (Finset.univ : Finset D.what₂.Tau) then Mz ρ else 1) = Mz := by
    funext ρ; simp
  have := key Finset.univ
  rwa [e] at this

theorem cusp_hasCen : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ν : ℕ) (P : D.what₂.Tau → SPar), N.Is ν 0 P → ∃ χ : GA D N.V → ℂ, ∀ (F : N.Cusp θ) (v : SmT N.M), GlobalTheory.SeeSaw.HasCen N.V χ (F.1 v) := by
  intro D θ hθ N ν P hN
  have hs : N.V.SigOK := hN.sigOK
  have hd : N.V.IsDefinite := fun τ => Or.inl (by rw [hN.sig, hN.rank]; simp)
  have hfd : ∀ τ, FiniteDimensional ℂ (N.M.H τ) := fun τ => GlobalTheory.DefiniteEnd.finiteDimensional_model hs hd N.M τ
  have key : ∀ (z : GA D N.V) (ρ : D.what₂.Tau), ∃ c : ℂ, z ∈ Subgroup.center (GA D N.V) →
      ∀ w, N.M.rep ρ (infMat D.sp.cm.sig N.V.gram (θ ρ) z) w = c • w := by
    intro z ρ
    by_cases hz : z ∈ Subgroup.center (GA D N.V)
    · haveI := hfd ρ
      obtain ⟨c, hc⟩ := rep_scalar N.M ρ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ N.V z ρ)
        (fun g hg => infMat_comm hθ hz ρ hg)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose c hc using key
  refine ⟨fun z => ∏ ρ, c z ρ, fun F v z hz hzc h => ?_⟩
  have hreal : ∀ T : MMap N.M, IsMultMap θ N.M ∅ 1 T → ∀ (u : N.M.Vec) (g : GA D N.V),
      T u (g * z) = (∏ ρ, c z ρ) * T u g := by
    intro T hT u g
    have e : GlobalTheory.RowReal.realAll θ N.V (fun ρ => infMat D.sp.cm.sig N.V.gram (θ ρ) z) = z :=
      GlobalTheory.RowReal.realAll_eq hθ (fun ρ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ N.V z ρ) ⟨hz, fun ρ => rfl⟩
    have := rTr_realAll hθ hT _ (fun ρ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ N.V z ρ) (c z)
      (fun ρ => hc z ρ hzc) u
    rw [e] at this
    exact congrFun this g
  have key2 : ∀ T ∈ Mult θ N.M ∅ 1, ∀ (x : SmT N.M) (g : GA D N.V),
      PiTensorProduct.lift T x (g * z) = (∏ ρ, c z ρ) * PiTensorProduct.lift T x g := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      intro x
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        intro g
        simp only [map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul]
        rw [hreal T hT f g]
        ring
      | add a b ha hb =>
        intro g
        simp only [map_add, Pi.add_apply]
        rw [ha g, hb g]
        ring
    | zero => intro x g; simp
    | add T T' _ _ h1 h2 =>
      intro x g
      simp only [map_add, LinearMap.add_apply, Pi.add_apply]
      rw [h1 x g, h2 x g]
      ring
    | smul a T _ h =>
      intro x g
      simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      rw [h x g]
      ring
  have hm : PiTensorProduct.lift.symm F.1 ∈ Mult θ N.M ∅ 1 := (mem_multT θ N.M ∅ 1 F.1).1 F.2
  have := key2 _ hm v h
  rw [LinearEquiv.apply_symm_apply] at this
  exact this

end GlobalTheory.DefCenChar

end

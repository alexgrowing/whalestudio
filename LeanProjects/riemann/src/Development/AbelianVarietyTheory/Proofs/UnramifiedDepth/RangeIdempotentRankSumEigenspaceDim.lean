import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SquarefreeMapMinpolyInt
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EmbeddingsLiftIntegersIdempotentsConjugation
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicIntAlgebraOfIsAdicCompleteMatrixUnique
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem finrank_iSup_indep {K V I : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    [Fintype I] (S : I → Submodule K V) (hi : iSupIndep S) :
    Module.finrank K ↥(⨆ i, S i) = ∑ i, Module.finrank K (S i) := by
  classical
  rw [Submodule.iSup_eq_range_dfinsupp_lsum, LinearMap.finrank_range_of_inj hi.dfinsupp_lsum_injective]
  exact Module.finrank_directSum (R := K) (fun i => S i)

private theorem range_idem {O : Type} [CommRing O] [IsLocalRing O] {g : ℕ} (P : Matrix (Fin g) (Fin g) O)
    (h : P * P = P) : ∃ r : ℕ, Matrix.trace P = (r : O) ∧ Module.finrank O (LinearMap.range (Matrix.mulVecLin P)) = r ∧
      Nonempty (LinearMap.range (Matrix.mulVecLin P) ≃ₗ[O] (Fin r → O)) := by
  have hf : IsIdempotentElem (Matrix.mulVecLin P) := by
    show Matrix.mulVecLin P ∘ₗ Matrix.mulVecLin P = _
    rw [← Matrix.mulVecLin_mul, h]
  have hp := LinearMap.IsIdempotentElem.isProj_range _ hf
  haveI : Module.Projective O (LinearMap.range (Matrix.mulVecLin P)) :=
    Module.Projective.of_split (LinearMap.range (Matrix.mulVecLin P)).subtype hp.codRestrict (by
      ext x : 1
      exact hp.codRestrict_apply_cod x)
  haveI : Module.Free O (LinearMap.range (Matrix.mulVecLin P)) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Projective O (LinearMap.ker (Matrix.mulVecLin P)) := by
    have hq := LinearMap.IsIdempotentElem.isProj_range _ hf.one_sub
    have : LinearMap.range (1 - Matrix.mulVecLin P) = LinearMap.ker (Matrix.mulVecLin P) :=
      (LinearMap.IsIdempotentElem.ker_eq_range_one_sub hf).symm
    rw [this] at hq
    exact Module.Projective.of_split (LinearMap.ker (Matrix.mulVecLin P)).subtype hq.codRestrict (by
      ext x : 1
      exact hq.codRestrict_apply_cod x)
  haveI : Module.Finite O (LinearMap.ker (Matrix.mulVecLin P)) := by
    rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub hf]
    infer_instance
  haveI : Module.Free O (LinearMap.ker (Matrix.mulVecLin P)) := Module.free_of_flat_of_isLocalRing
  refine ⟨_, ?_, rfl, ⟨(Module.finBasis O _).equivFun⟩⟩
  rw [← hp.trace, ← Matrix.toLin'_apply', Matrix.trace_toLin'_eq]

theorem range_idempotent_equiv_sum_eigDim : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (g : ℕ) (ρ : (ℤ_[p] ⊗[ℤ] OE) →+* Matrix (Fin g) (Fin g) O) (e : ℤ_[p] ⊗[ℤ] OE), e * e = e → ∀ (n : ℕ) (t : Fin n ≃ Emb (O := O) e), Nonempty (LinearMap.range (Matrix.mulVecLin (ρ e)) ≃ₗ[O] (Fin (∑ j, eigDim C (fun a : OE => ρ (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O))) → O)) := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ g ρ e he n t
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hP : ρ e * ρ e = ρ e := by rw [← map_mul, he]
  obtain ⟨r, htr, -, hne⟩ := range_idem (ρ e) hP
  have hPC : (ρ e).map (algebraMap O C) * (ρ e).map (algebraMap O C) = (ρ e).map (algebraMap O C) := by
    rw [← Matrix.map_mul, hP]
  obtain ⟨r', htr', hrk, -⟩ := range_idem _ hPC
  have hrr : r = r' := by
    have : ((r : ℕ) : C) = r' := by
      rw [← htr', ← AddMonoidHom.map_trace (algebraMap O C) (ρ e), htr]
      simp
    exact_mod_cast this
  let σ : (ℤ_[p] ⊗[ℤ] OE) →+* Module.End C (Fin g → C) :=
    (Matrix.toLinAlgEquiv' (R := C) (n := Fin g)).toRingEquiv.toRingHom.comp
      ((algebraMap O C).mapMatrix.comp ρ)
  have hσ : ∀ x, σ x = Matrix.toLin' ((ρ x).map (algebraMap O C)) := fun x => rfl
  let ρE : OE →+* Module.End C (Fin g → C) :=
    σ.comp (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom
  obtain ⟨-, hd⟩ := GlobalTheory.order_rep_diagonalisable C OE
  obtain ⟨hind, htop⟩ := hd (Fin g → C) ρE
  obtain ⟨hex, h01, -⟩ := GlobalTheory.ChF.embeddings_idempotents_conjugation p C v O hv OE
  have hz := (GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).2 g
    (ρ.comp (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ℤ_[p]) (B := OE)))
  set E : (OE →+* C) → Submodule C (Fin g → C) :=
    fun τ => ⨅ a : OE, Module.End.eigenspace (ρE a) (τ a) with hE
  have hact : ∀ (τ : OE →+* O) (y : Fin g → C), y ∈ E ((algebraMap O C).comp τ) →
      ∀ x, σ x y = algebraMap O C (tauExt τ x) • y := by
    intro τ y hy x
    have hy' : ∀ a, σ (1 ⊗ₜ[ℤ] a) y = algebraMap O C (τ a) • y := by
      intro a
      have := (Submodule.mem_iInf _).1 hy a
      exact Module.End.mem_eigenspace_iff.1 this
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' h h' => rw [map_add, map_add, map_add, LinearMap.add_apply, h, h', add_smul]
    | tmul c a =>
      have h1 : (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = (c ⊗ₜ[ℤ] 1) * (1 ⊗ₜ[ℤ] a) := by simp
      have h2 : ρ (c ⊗ₜ[ℤ] 1) = algebraMap ℤ_[p] O c • (1 : Matrix (Fin g) (Fin g) O) := hz c
      have h3 : ∀ z, σ (c ⊗ₜ[ℤ] 1) z = algebraMap O C (algebraMap ℤ_[p] O c) • z := by
        intro z
        have : (algebraMap ℤ_[p] O c • (1 : Matrix (Fin g) (Fin g) O)).map (algebraMap O C)
            = algebraMap O C (algebraMap ℤ_[p] O c) • (1 : Matrix (Fin g) (Fin g) C) := by
          ext i j
          rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
            Matrix.one_apply, Matrix.one_apply]
          split_ifs
          · rw [map_one]
          · rw [map_zero]
        rw [hσ, h2, this, map_smul, Matrix.toLin'_one]
        rfl
      have h4 : tauExt τ (c ⊗ₜ[ℤ] a) = algebraMap ℤ_[p] O c * τ a := by
        simp [tauExt, Algebra.ofId_apply]
      rw [h4, h1, map_mul, Module.End.mul_apply, h3, hy', smul_smul, map_mul]
  have hinj : Function.Injective
      (fun j : Fin n => (algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O)) := by
    intro i j hij
    apply t.injective
    apply Subtype.ext
    exact (hex _).unique hij rfl
  have hrange : LinearMap.range (σ e) =
      ⨆ j : Fin n, E ((algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O)) := by
    apply le_antisymm
    · rw [LinearMap.range_eq_map, ← htop, Submodule.map_iSup]
      refine iSup_le fun τ => ?_
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨τ', rfl, -⟩ := hex τ
      rw [hact τ' y hy e]
      rcases h01 e τ' he with h | h
      · rw [h]; simp
      · rw [h, map_one, one_smul]
        refine Submodule.mem_iSup_of_mem (t.symm ⟨τ', h⟩) ?_
        rw [Equiv.apply_symm_apply]
        exact hy
    · refine iSup_le fun j => fun y hy => ⟨y, ?_⟩
      have h : tauExt ((t j : Emb (O := O) e) : OE →+* O) e = 1 := (t j).2
      rw [hact _ y hy e, h, map_one, one_smul]
  have hsum := finrank_iSup_indep _ (hind.comp hinj)
  have hfin : r' = ∑ j, eigDim C (fun a : OE => ρ (1 ⊗ₜ[ℤ] a))
      ((algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O)) := by
    have h1 : Module.finrank C (LinearMap.range (σ e)) = r' := hrk
    rw [← h1, hrange]
    exact hsum
  rw [← hfin, ← hrr]
  exact hne

end GlobalTheory.ChF

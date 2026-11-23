import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemScLatOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdeleSupportedAtFinitePlaceOfSupportedAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBlockSumSelfDualTraceSkewForm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ptO_eq {D : D7} (S : HSp D) {d n : ℕ} (e : Fin d ≃ Fin n) (x : Matrix (Fin n) (Fin S.rank) (AE D))
    (p : Fin S.rank) (q : Fin d) : ptO S.gram e x p q = GlobalTheory.BigDat.divG S x (e q) p := rfl

private noncomputable def ptH {D : D7} (S : HSp D) {d n : ℕ} (e : Fin d ≃ Fin n) :
    Matrix (Fin n) (Fin S.rank) (AE D) →+ Matrix (Fin S.rank) (Fin d) (AE D) :=
  AddMonoidHom.mk' (ptO S.gram e) fun x y => by
    ext p q
    rw [Matrix.add_apply, ptO_eq, ptO_eq, ptO_eq, GlobalTheory.BigDat.divG, Matrix.add_mul]
    rfl

private theorem ptO_inj {D : D7} (S : HSp D) {d n : ℕ} (e : Fin d ≃ Fin n) {x y : Matrix (Fin n) (Fin S.rank) (AE D)}
    (h : ptO S.gram e x = ptO S.gram e y) : x = y := by
  have h1 : GlobalTheory.BigDat.divG S x = GlobalTheory.BigDat.divG S y := by
    ext q p
    obtain ⟨q, rfl⟩ := e.surjective q
    rw [← ptO_eq, ← ptO_eq, h]
  rw [← GlobalTheory.BigDat.mulG_divG S x, h1, GlobalTheory.BigDat.mulG_divG]

private theorem ptO_gen {D : D7} (S : HSp D) {d n : ℕ} (e : Fin d ≃ Fin n) (β : AF D.host.F) (a : D.host.E)
    (s : Fin S.rank → D.host.E) (t : Fin n → D.host.E) :
    ptO S.gram e (Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) (fun q => a * t (e q))) := by
  ext p q
  refine (ptO_eq S e _ p q).trans ((GlobalTheory.BigDat.divG_gen S β a s t (e q) p).trans ?_)
  rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, mul_comm]
  rfl

private theorem at_eq_pairA {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {b : AF F}
    (hb : At (evFin F v) b) (hi : evFin F v b ∈ v.adicCompletionIntegers F) : ∃ α ∈ intAf F, b = pairA F 0 α := by
  refine ⟨GlobalTheory.AdelicU.singleFin v (evFin F v b), fun w => ?_, GlobalTheory.VacAny.eq_atPlace_of_at v b hb⟩
  by_cases h : w = v
  · subst h
    rw [GlobalTheory.AdelicU.evalV_singleFin_self]
    exact hi
  · rw [GlobalTheory.AdelicU.evalV_singleFin_ne h]
    exact zero_mem _

private theorem finiteRing_sq_sub_mul_sq_eq_of_card {D : D7} (S X : HSp D) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E))
    (hL : IsLat e Vs Ws ΛS ΛX) :
    (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (x : WO S X), ptO S.gram e x ∈ latAtV Vs Ws v → x ∈ (latO S X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True)) ∧
        ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (a : AF D.host.F), At (evFin D.host.F v) a →
          evFin D.host.F v a ∈ v.adicCompletionIntegers D.host.F → ∀ x ∈ (latO S X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True), a • ptO S.gram e x ∈ latAtV Vs Ws v := by
  refine ⟨fun v x hx => ?_, fun v b hb hi x hx => ?_⟩
  · have key : latAtV Vs Ws v ≤ (latO S X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E))
        fun _ => True).map (ptH S e) := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨b, hb, hi, x, hx, y, hy, rfl⟩
      obtain ⟨α, hα, rfl⟩ := at_eq_pairA hb hi
      have h1 : (1 : D.host.E) ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) *
          ((D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) := by
        rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ GlobalTheory.SkewLat.DualPair.AA_ne]
        exact FractionalIdeal.one_mem_one _
      have h2 : ∀ z ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) *
          ((D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)),
          pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec x (z • y)) ∈
            (latO S X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True).map (ptH S e) := by
        intro z hz
        refine Submodule.mul_induction_on hz (fun a ha c hc => ?_) (fun z z' hz hz' => ?_)
        · refine ⟨_, AddSubgroup.subset_closure ⟨α, hα, fun _ h => (h trivial).elim, a, ha, star x, (hL.1 x).1 hx,
            c • fun k => y (e.symm k), (hL.2 y).1 hy c hc, rfl⟩, ?_⟩
          refine (ptO_gen S e _ a _ _).trans ?_
          rw [star_star]
          congr 3
          funext q
          simp only [Pi.smul_apply, smul_eq_mul, Equiv.symm_apply_apply, mul_assoc]
        · have h3 : pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec x ((z + z') • y)) =
              pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec x (z • y)) +
              pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec x (z' • y)) := by
            refine Matrix.ext fun p q => ?_
            rw [Matrix.add_apply, GlobalTheory.BigDat.smul_incM_apply, GlobalTheory.BigDat.smul_incM_apply, GlobalTheory.BigDat.smul_incM_apply,
              ← TensorProduct.tmul_add]
            simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add]
          rw [h3]
          exact add_mem hz hz'
      have h4 := h2 1 h1
      rwa [one_smul] at h4
    obtain ⟨x', hx', h⟩ := key hx
    rwa [← ptO_inj S e h]
  · refine GlobalTheory.BigDat.map_mem_of_closure ((DistribMulAction.toAddMonoidHom _ b).comp (ptH S e)) ?_ hx
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    refine (congrArg (fun z => b • z ∈ latAtV Vs Ws v) (ptO_gen S e (pairA _ 0 α) a s t)).mpr ?_
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨_, ?_, ?_, _, (hL.1 _).2 (by rw [star_star]; exact hs), _, (hL.2 _).2 ?_, rfl⟩
    · intro u hu
      rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u, hb u hu, zero_mul]
    · rw [map_mul]
      exact mul_mem hi (hα v)
    · simp only [Equiv.apply_symm_apply]
      exact GlobalTheory.BigDat.smul_mem_scLat_of_mem ha ht

theorem UpperTheory.ptO_sgn_mem_latAtV_iff_mem_latO :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (e : Fin d ≃ Fin X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X e Bs Vs Ws M → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)),
        IsLat e Vs Ws ΛS ΛX →
        (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (x : WO (sgn ε S) X), ptO (sgn ε S).gram e x ∈ latAtV Vs Ws v → x ∈ (latO (sgn ε S) X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True)) ∧
        ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (a : AF D.host.F), At (evFin D.host.F v) a →
          evFin D.host.F v a ∈ v.adicCompletionIntegers D.host.F → ∀ x ∈ (latO (sgn ε S) X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True), a • ptO (sgn ε S).gram e x ∈ latAtV Vs Ws v := by
  intro D ψ ε S X d e Bs Vs Ws M _ ΛS ΛX hL
  exact finiteRing_sq_sub_mul_sq_eq_of_card (sgn ε S) X e Vs Ws ΛS ΛX hL

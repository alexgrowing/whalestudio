import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AutomorphicArithmetic.DivisorFrames.ThetaOperatorIntertwinesHeisenberg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceComponentArchLineComplexStructureStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ptO_smul' {D : D7} {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d) (a : AF D.host.F)
    (x : Mx D d m) : ptO G e (a • x) = a • ptO G e x := by
  unfold GlobalTheory.TripleRead.ptO
  rw [Matrix.smul_mul, transpose_smul]
  rfl

private theorem ptO_zero' {D : D7} {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d) :
    ptO G e (0 : Mx D d m) = 0 := by
  unfold GlobalTheory.TripleRead.ptO
  rw [Matrix.zero_mul]
  rfl

private theorem realAd_one_smul {F : Type} [Field F] [NumberField F] {U : Type} [AddCommGroup U] [Module (AF F) U] {u : U}
    (hu : At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F 1 • u = u := by
  have h := hu (1 - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F 1) (by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (1 - (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ (1 : ℝ))) = 0
    rw [map_sub, RingEquiv.apply_symm_apply, map_one, map_one, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm

set_option maxHeartbeats 1000000 in
theorem UpperTheory.exists_polynomial_of_isFinF_thetaLift_pureTensor :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (e : Fin d ≃ Fin X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X e Bs Vs Ws M → ∀ (θ : InfFam D), IsInfFam θ → ∀ (A : Fr S) (B : Fr X), IsCart ε A B e Bs Vs Ws →
        ∀ (g : SInf D.host.F (Fin S.rank × Fin d))
          (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → Fv D.host.F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
        (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → g ≠ 0 → (∀ v, φ v ≠ 0) →
        IsFinF ψ θ ε A B (thO M ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) →
        ∀ g₁ ∈ M.Pol Bs.ψ Bs.emb, ∃ P : PolF D X.rank S.rank,
          fockF ψ θ ε A B (thO M ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) P =
            thO M ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) := by
  intro D ψ ε S X d e Bs Vs Ws M hP θ hθ A B hc g φ hSB hev g0 hφ0 hv
  obtain ⟨-, hH, tadd, tsm, tinj, -⟩ := UpperTheory.thetaOperator_intertwines_heisenberg D ψ ε S X d e Bs Vs Ws M hP
  obtain ⟨hBs, hψe, hJ, hJW, ⟨r, s, hV⟩, ⟨r', s', hW⟩, hM⟩ := hP
  subst hψe
  have hψ : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hBs.std
  have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1 :=
    (hev.and hM.std).mono fun v hv => hv.1.trans hv.2
  have hm : ∀ f : SInf D.host.F (Fin S.rank × Fin d), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ GlobalTheory.WeilM.schA D.host.F _ := fun f =>
    GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : SInf D.host.F (Fin S.rank × Fin d) →ₗ[ℂ] (WO (sgn ε S) X → ℂ),
      ∀ f, Θ f = thO M Bs.ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) :=
    ⟨{ toFun := fun f => thO M Bs.ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)
       map_add' := fun f f' => by
         rw [← tadd _ (hm f) _ (hm f')]
         exact congrArg _ (funext fun x => add_mul _ _ _)
       map_smul' := fun c f => by
         rw [RingHom.id_apply, ← tsm]
         exact congrArg _ (funext fun x => mul_assoc _ _ _) }, fun _ => rfl⟩
  have hi : ∀ f, Θ f = 0 → f = 0 := fun f h => by
    by_contra hf
    refine GlobalTheory.EvNonzero.pure_ne_zero f hf φ hφ0 hstd (tinj _ (hm f) _ (zero_mem _) ?_)
    rw [← hΘ, h]
    simpa only [zero_smul] using (tsm 0 0).symm
  obtain ⟨Dr, hD1, hD2, hD3⟩ := GlobalTheory.RealDict.FockMap.exists_der M hBs.std
  obtain ⟨dir, hdir⟩ : ∃ dir : D.what₂.Tau → Matrix (Fin X.rank) (Fin S.rank) ℂ → Matrix (Fin S.rank) (Fin d) (AE D),
      ∀ t z, dir t z = ptO (sgn ε S).gram e (lineAt θ t z 1) := ⟨_, fun _ _ => rfl⟩
  have hat : ∀ t z, At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (dir t z) := fun t z a ha => by
    rw [hdir, ← ptO_smul', (GlobalTheory.LineRealAd.lineAt_realAd_smul D θ hθ t z).2 a ha, ptO_zero']
  have hd : ∀ t z f, Formalism.IndefR.Datum.dRho (heisO Bs.ψ (sgn ε S) X) θ t z (Θ f) = Θ (Dr (dir t z) f) := by
    intro t z f
    have hl := (GlobalTheory.LineRealAd.lineAt_realAd_smul D θ hθ t z).1
    have hrest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) f
        (fun x : Fin S.rank × Fin d → AF D.host.F => ∏ᶠ v, φ v fun i => evFin D.host.F v (x i)) :=
      GlobalTheory.RealDict.FockMap.rest_fin f
        (g := fun y => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v (y i))
        ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩
    funext x
    have := GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho M.co Bs.ψ inferInstance hψ.1 (dir t z) _ (hm f) _ (hm (Dr (dir t z) f))
      (hD1 _ (hat t z) f _ hrest) (ptO (sgn ε S).gram e x)
    rw [hΘ (Dr _ _)]
    refine Eq.trans ?_ this.deriv
    unfold Formalism.IndefR.Datum.dRho
    congr 1
    funext a
    rw [hΘ, ← hH, hl a, ptO_smul', ← hdir]
    rfl
  have hG : IsUnit (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram).det :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (sgn ε S)
  have hg : (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram) =
      (if ε then -1 else 1 : D.host.E) • S.gram := by
    cases ε
    · simp only [Bool.false_eq_true, if_false, one_smul]; rfl
    · simp only [if_true, neg_smul, one_smul]; exact neg_gram S
  obtain ⟨cS, hcS, hcS'⟩ : ∃ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) :
        Matrix (Fin X.rank) (Fin S.rank) (AE D))) ∧ ∀ x, cS.symm x = ptO (sgn ε S).gram e x :=
    ⟨GlobalTheory.FockThetaOnto.crd (D := D) (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram) hG e,
      fun u => by rw [← hg]; rfl, fun _ => rfl⟩
  have hsum : ∀ u, At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → ∀ f, Dr u f = ∑ t, Dr (dir t (compAt θ t (cS u))) f := by
    intro u hu f
    have h : At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (show Mx D X.rank S.rank from cS u) := fun a ha => by
      have h0 : a • uᵀ.submatrix e.symm id = 0 := congrArg (fun y => yᵀ.submatrix e.symm id) (hu a ha)
      show a • (show Mx D X.rank S.rank from cS u) = 0
      rw [hcS, ← Matrix.smul_mul, h0, Matrix.zero_mul]
    have h1 := congrArg cS.symm (GlobalTheory.RealDict.FockMap.eq_sum_lineAt hθ h)
    have h2 : u = ∑ t, dir t (compAt θ t (cS u)) := by
      refine ((cS.symm_apply_apply u).symm.trans h1).trans ((map_sum cS.symm _ _).trans ?_)
      exact Finset.sum_congr rfl fun t _ => (hcS' _).trans (hdir _ _).symm
    rw [← hD3 _ _ _ fun t => hat t _, ← h2]
  rw [← hΘ] at hv ⊢
  have hg₀ : ∀ t z, Dr (dir t z) g + Complex.I • Dr (dir t (cplxO ((frSgn ε A).cart t) (B.cart t) z)) g = 0 := fun t z =>
    hi _ (by rw [map_add, map_smul, ← hd, ← hd]; exact hv.2 t z)
  have hGa : M.IsGauss Bs.ψ Bs.emb g := ⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => by
    rw [hD2 u hu _ _ hf, hD2 u' hu' _ _ hf', hsum u hu, hsum u' hu', Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have k := GlobalTheory.T.realPlaceComponent_archLine_complexStructure D θ hθ ε S X A B e.symm Bs Vs Ws hc cS hcS u u' (fun w => by simpa using hrel w) t
    rw [GlobalTheory.VacTransfer.archLine_apply, GlobalTheory.VacTransfer.archLine_apply, realAd_one_smul hu, realAd_one_smul hu'] at k
    rw [k, eq_neg_of_add_eq_zero_left (hg₀ t (compAt θ t (cS u))), smul_neg, smul_smul,
      Complex.I_mul_I, neg_one_smul, neg_neg]⟩
  intro g₁ hg₁
  rw [← hΘ]
  have hle : M.Pol Bs.ψ Bs.emb ≤ (LinearMap.range (fockF Bs.ψ θ ε A B (Θ g))).comap Θ := by
    refine sInf_le ⟨fun f hf => ?_, ?_⟩
    · obtain ⟨z, rfl⟩ := GlobalTheory.RealDict.FockMap.gauss_line M Bs.ψ Bs.emb hBs.cm hBs.std (fun w => (hV.cartan w).1)
        (fun w => (hW.cartan w).1) f g hGa g0 hf
      exact Submodule.smul_mem _ z ⟨1, GlobalTheory.LieScalar.ptF_one (frSgn ε A) B _⟩
    · rintro u hu f ⟨P, hP⟩ f₁ h1
      rw [hD2 u hu _ _ h1, hsum u hu]
      refine Submodule.sum_mem _ fun t _ => ?_
      obtain ⟨Q, hQ⟩ := GlobalTheory.RealDict.FockMap.dRho_ptF (frSgn ε A) B hψ hθ hv t (compAt θ t (cS u)) P
      refine ⟨Q, ?_⟩
      rw [← hd, ← hP]
      exact hQ.symm
  exact hle hg₁

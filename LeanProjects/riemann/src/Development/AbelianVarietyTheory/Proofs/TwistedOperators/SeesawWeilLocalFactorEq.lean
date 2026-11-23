import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelProjectionFactorisation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DarbouxModelAlgebraicVectorsLeAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumLineFirst

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TripleAssembly.LieInv

theorem exists_factor {U V P : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup P]
    [Module ℂ P] (T : U →ₗ[ℂ] V) (S : Submodule ℂ U) (hT : ∀ x ∈ S, T x = 0 → x = 0) (p : U →ₗ[ℂ] P) :
    ∃ q : V →ₗ[ℂ] P, ∀ x ∈ S, q (T x) = p x := by
  obtain ⟨r, hr⟩ := (T.comp S.subtype).exists_leftInverse_of_injective (by
    rw [LinearMap.ker_eq_bot']
    exact fun x hx => Subtype.ext (hT x.1 x.2 hx))
  refine ⟨p.comp (S.subtype.comp r), fun x hx => ?_⟩
  have := LinearMap.congr_fun hr ⟨x, hx⟩
  change r (T x) = ⟨x, hx⟩ at this
  simp [this]

theorem det_ne_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  subst hn
  intro h0
  have h1 : Aᵀ * M * A.map star = (A.submatrix finSumFinEquiv id)ᵀ * M.submatrix finSumFinEquiv finSumFinEquiv *
      (A.map star).submatrix finSumFinEquiv id := by
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have h2 := congrArg Matrix.det hA
  rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, h0, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at h2
  simp only [mul_zero, zero_mul, Matrix.det_one, one_mul, mul_one] at h2
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h2.symm

theorem det_ne_of_hasSig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  refine det_ne_of_hasSig h ?_
  have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [Matrix.det_smul, this, h0, map_zero, mul_zero]

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w)
    {Ψ : (Fin n × Fin d → AF F) → ℂ} (hΨ : Ψ ∈ darbAlg M ψ τ) :
    ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ τ ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
  obtain ⟨m, c, g, hg⟩ := Submodule.mem_span_set'.1 hΨ
  have hg' := fun i => (g i).2
  simp only [Set.mem_setOf_eq] at hg'
  choose f φ hf hφ hφv hfe using hg'
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hφv i⟩, ?_⟩
  rw [← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hfe i]
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

variable {D : D7}

theorem toUX_one (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) : GlobalTheory.TripleRead.toUX X e hJ 1 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [GlobalTheory.TripleRead.toUX_val]
  simp [Formalism.L2.Theta.mt]

end GlobalTheory.TripleAssembly.LieInv

namespace GlobalTheory.TripleAssembly.LieInv

variable {D : D7}

theorem conjU_mul (M : HSp D) {J : Matrix (Fin M.rank) (Fin M.rank) D.host.E} (c : D.host.E) (hc : J = c • M.gram)
    (g h : GA D M) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (g * h) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc h := by
  apply Subtype.ext
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_mul]
  rfl

theorem conjU_one' (M : HSp D) {J : Matrix (Fin M.rank) (Fin M.rank) D.host.E} (c : D.host.E) (hc : J = c • M.gram) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc 1 = 1 := by
  apply Subtype.ext
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_one]
  rfl

theorem finTens_cA (z : AE D) : GlobalTheory.LFun.finTens D.host.F D.host.E (Formalism.L2.Theta.cA D z) =
    Algebra.TensorProduct.map (AlgHom.id D.host.F _) D.sp.cm.sig (GlobalTheory.LFun.finTens D.host.F D.host.E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.TripleAssembly.LieInv

namespace GlobalTheory.TripleAssembly.LieInv

variable {D : D7}

theorem conjU_mem_UAt (M : HSp D) (Yd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (c : D.host.E)
    (hc : Yd.J = c • M.gram) {g : GA D M} (hg : g ∈ GinfC M) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Yd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) := by
  intro u hu
  have hf : finHom M g = 1 := hg
  have hent : ∀ a b, GlobalTheory.LFun.finTens D.host.F D.host.E (Formalism.L2.Theta.mt M g a b) =
      (1 : Matrix (Fin M.rank) (Fin M.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) a b := by
    intro a b
    have := congrArg (fun k : GL (Fin M.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => k.1 a b) hf
    exact this
  ext i j
  have hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc g) i j = Formalism.L2.Theta.cA D (Formalism.L2.Theta.mt M g i j) := rfl
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply]
  apply GlobalTheory.KapXLine.smul_eq_zero_of_finTens hu
  rw [hm, map_sub, finTens_cA, hent, Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem exists_line_conjU (θ : InfFam D) (M : HSp D) (τ : D.what₂.Tau) (Y : Matrix (Fin M.rank) (Fin M.rank) ℂ)
    (hθ : IsInfFam θ) (hY : Y ∈ lieAt M τ) (Yd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (c : D.host.E)
    (hc : Yd.J = c • M.gram) :
    ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Yd, ∀ t : ℝ,
      γ (Multiplicative.ofAdd t) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (oneP θ M τ Y t) := by
  let γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Yd.J :=
    { toFun := fun t => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (oneP θ M τ Y (Multiplicative.toAdd t))
      map_one' := by
        show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (oneP θ M τ Y 0) = 1
        rw [GlobalTheory.Mem.Lift.oneP_zero hθ, conjU_one']
      map_mul' := fun s t => by
        show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (oneP θ M τ Y (Multiplicative.toAdd s + Multiplicative.toAdd t)) = _
        rw [GlobalTheory.Mem.Lift.oneP_add hθ hY, conjU_mul] }
  refine ⟨γ, ⟨?_, fun t => ?_⟩, fun t => rfl⟩
  · exact (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU M c hc).comp ((GlobalTheory.Mem.Lift.continuous_oneP hθ hY).comp continuous_toAdd)
  · exact conjU_mem_UAt M Yd c hc (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY _).1

end GlobalTheory.TripleAssembly.LieInv

namespace GlobalTheory.TripleAssembly.LieInv

variable {D : D7}

theorem thetaLift_der_eq_zero (hP : GlobalTheory.FunPr.Hypotheses₂) {k : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D}
    {Yv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Yv Z) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Yv Z) (ω : WRep M X)
    (e : Fin k ≃ Fin X.rank) (c : D.host.E) (hc : Yv.J = c • M.gram)
    (hX : Z.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    (emb : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver (E := D.host.E) w)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E)
    {P : Type} [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin k) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin M.rank × Fin k → Fv D.host.F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v)
    (hs : ∀ᶠ v in Filter.cofinite, pv v (Mo.vac v) = s v)
    (hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (hM : Mo.IsGood ψ) (hW : Mo.IsWeil ψ χX χW om)
    (hDer : ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Yv,
      GlobalTheory.RealActs.DerOn (Mo.Pol ψ emb) (fun t => om (γ (Multiplicative.ofAdd t), 1)))
    (hlie : ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Yv, ∀ f ∈ Mo.Pol ψ emb,
      ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin k),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
        pr f₁ = 0)
    (T : ((Fin M.rank × Fin k → AF D.host.F) → ℂ) →ₗ[ℂ] (WO M X → ℂ))
    (hT : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin k), T Φ = GlobalTheory.TripleRead.thO Mo ψ (sgn ε M).gram e Φ)
    (hinj : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin k), T Φ = 0 → Φ = 0)
    (htr : GlobalTheory.TripleRead.IsTransp ψ ε Mo om ω e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc) (GlobalTheory.TripleRead.toUX X e hX))
    (hθ : IsInfFam θ) (τ : D.what₂.Tau) (Y : Matrix (Fin M.rank) (Fin M.rank) ℂ) (hY : Y ∈ lieAt M τ)
    (Ψ : (Fin M.rank × Fin k → AF D.host.F) → ℂ) (hΨ : Ψ ∈ darbAlg Mo ψ emb) (Φ' : WO M X → ℂ)
    (hD : IsDer θ M (fun g => ω (g, 1)) τ Y (T Ψ) Φ') :
    thetaLift Mo ψ (sgn ε M).gram e (darbAlg Mo ψ emb) (liftPure Mo pr pv s) Φ' = 0 := by
  classical
  obtain ⟨γ, hγ, hγt⟩ := exists_line_conjU θ M τ Y hθ hY Yv c hc
  obtain ⟨Dop, hDpol, hDiff⟩ := hDer γ hγ
  obtain ⟨m, f, φ, hf, rfl⟩ := exists_sum_pure Mo ψ emb hΨ
  let f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin k) := fun i => Dop (f i)
  have hA : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F)
      (fun t => om (γ (Multiplicative.ofAdd t), 1)) (f i) (f₁ i) := fun i => (hDiff (f i) (hf i).1 (f₁ i)).2 rfl
  have hstdv : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers D.host.F} 1 := by
    intro i
    filter_upwards [hM.std, (hf i).2.2] with v hv hv' using hv'.trans hv
  have hsch : ∀ g : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin k),
      ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g i) (φ i) ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin k) := fun g =>
    Submodule.sum_mem _ fun i _ => GlobalTheory.TensUniq.pure_mem_schA _ _ (hf i).2.1 (hstdv i)
  have hΨ₁ : ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i) ∈ darbAlg Mo ψ emb :=
    Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f₁ i, φ i, hDpol _ (hf i).1, (hf i).2.1, (hf i).2.2, rfl⟩
  have hder := GlobalTheory.ThetaLineDerFirst.hasDerivAt_thetaSum_lineFirst hP Mo ψ χX χW om hstd hM hW γ hγ m f f₁ φ (fun i => ⟨(hf i).2.1, (hf i).2.2⟩) hA
  have hΦ' : Φ' = GlobalTheory.TripleRead.thO Mo ψ (sgn ε M).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) := by
    funext z
    have h1 := hD z
    have h2 := hder (GlobalTheory.TripleRead.ptO (sgn ε M).gram e z)
    refine h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
    have h3 := htr _ (hsch f) (oneP θ M τ Y t) 1
    rw [toUX_one, ← hγt t] at h3
    show ω (oneP θ M τ Y t, 1) (T _) z = GlobalTheory.TripleRead.thO Mo ψ (sgn ε M).gram e _ z
    rw [hT _ (hsch f), ← h3]
  have hsub := GlobalTheory.TripleAssembly.darbAlg_le_schA _ _ _ Mo ψ emb hM
  have H : ∃ q : (Matrix (Fin X.rank) (Fin M.rank) (AE D) → ℂ) →ₗ[ℂ] P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens s,
      ∀ Ψ ∈ darbAlg Mo ψ emb, q (GlobalTheory.TripleRead.thO Mo ψ (sgn ε M).gram e Ψ) = liftPure Mo pr pv s Ψ := by
    obtain ⟨q, hq⟩ := exists_factor T (darbAlg Mo ψ emb) (fun x hx => hinj x (hsub hx)) (liftPure Mo pr pv s)
    exact ⟨q, fun Ψ hΨ => by rw [← hT Ψ (hsub hΨ)]; exact hq Ψ hΨ⟩
  have e1 : thetaLift Mo ψ (sgn ε M).gram e (darbAlg Mo ψ emb) (liftPure Mo pr pv s) Φ' =
      liftPure Mo pr pv s (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) := by
    rw [hΦ']
    unfold thetaLift
    rw [dif_pos H]
    exact H.choose_spec _ hΨ₁
  have HL := GlobalTheory.PureLift.exists_pureLift D.sp.cm.sig Yv Z Mo ψ hM P pr N pv s hs
  have e2 : ∀ i, liftPure Mo pr pv s (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) = 0 := by
    intro i
    unfold liftPure
    rw [dif_pos HL, HL.choose_spec _ _ (hf i).2.1 (hf i).2.2, hlie γ hγ (f i) (hf i).1 (f₁ i) (hA i),
      TensorProduct.zero_tmul]
  rw [e1, map_sum]
  exact Finset.sum_eq_zero fun i _ => e2 i

end GlobalTheory.TripleAssembly.LieInv

open GlobalTheory.TripleAssembly.LieInv in

theorem GlobalTheory.TripleAssembly.LieInv.mapA_mapB_lie_eq_zero : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ τ, ∀ Y ∈ lieAt W τ, ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ W (fun g => ωA (g, 1)) τ Y Φ Φ' → GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ' = 0) ∧
          ∀ τ, ∀ Y ∈ lieAt W₁ τ, ∀ Φ ∈ algF ψ θ false A₁ B, ∀ Φ' ∈ algF ψ θ false A₁ B, IsDer θ W₁ (fun g => ωB (g, 1)) τ Y Φ Φ' → GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ' = 0 := by
  intro hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm
  obtain ⟨iA, iB⟩ := GlobalTheory.T.seesaw_weil_factorization hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm
  have hg := hm.triple.geo
  have hψ' : Bs.ψ = ψ := h.ψ
  subst hψ'
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd Bs.ψ := hm.triple.base.std
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have dV : Γ.V.J.det ≠ 0 := det_ne_of_hasSig_map (Bs.emb w).1 1 (by rw [one_smul]; exact hg.hV.sig w)
  have dV' : Γ.V'.J.det ≠ 0 := det_ne_of_hasSig_map (Bs.emb w).1 1 (by rw [one_smul]; exact hg.hV'.sig w)
  have dW : Γ.W.J.det ≠ 0 := det_ne_of_hasSig_map (Bs.emb w).1 Complex.I (hg.hW.sig w)
  have gA : (sgn true W).gram.det ≠ 0 := by
    have e1 : (sgn true W).gram = -W.gram := rfl
    rw [h.JW, one_smul] at dV
    rw [e1, Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) dV
  have gB : (sgn false W₁).gram.det ≠ 0 := by
    have e1 : (sgn false W₁).gram = W₁.gram := rfl
    rw [h.JW₁, Matrix.det_smul] at dV'
    rw [e1]
    exact right_ne_zero_of_mul dV'
  have PA := GlobalTheory.T.polynomial_datum_action_of_pair hP _ _ D.sp.cm.sig Bs _ _ Γ.V Γ.W Γ.M _ _ om _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hm.triple)
  have PB := GlobalTheory.T.polynomial_datum_action_of_pair hP _ _ D.sp.cm.sig Bs _ _ Γ.V' Γ.W Γ.M' _ _ om' _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hm.triple)
  constructor
  · intro τ Y hY Φ hΦ Φ' _ hD
    obtain ⟨T, hT, hinj⟩ := GlobalTheory.ThetaTransformInj.linear_injective D Γ.M Bs.ψ (sgn true W).gram e hg.hM hstd dV dW gA
    have hΦ2 : Φ ∈ (darbAlg Γ.M Bs.ψ Bs.emb).map T := by rw [iA T hT]; exact hΦ
    obtain ⟨Ψ, hΨ, rfl⟩ := hΦ2
    exact thetaLift_der_eq_zero hP Bs.ψ θ true Γ.M om ωA e 1 h.JW h.JX Bs.emb Xc.β (Xc.β / Xc.α) R.p Rf.p (vacIm Γ Rf)
      (Filter.Eventually.of_forall fun _ => rfl) hstd hg.hM hm.triple.weil PA.1 hm.real.quot.lie T hT hinj tA hθ τ Y hY
      Ψ hΨ Φ' hD
  · intro τ Y hY Φ hΦ Φ' _ hD
    obtain ⟨T, hT, hinj⟩ := GlobalTheory.ThetaTransformInj.linear_injective D Γ.M' Bs.ψ (sgn false W₁).gram e hg.hM' hstd dV' dW gB
    have hΦ2 : Φ ∈ (darbAlg Γ.M' Bs.ψ Bs.emb).map T := by rw [iB T hT]; exact hΦ
    obtain ⟨Ψ, hΨ, rfl⟩ := hΦ2
    refine thetaLift_der_eq_zero hP Bs.ψ θ false Γ.M' om' ωB e (-1) h.JW₁ h.JX Bs.emb Xc.α (Xc.α / Xc.β) R.p' Rf.p'
      (vacIm Γ Rf) ?_ hstd hg.hM' hm.triple.weil' PB.1 hm.real.quot'.lie T hT hinj tB hθ τ Y hY Ψ hΨ Φ' hD
    filter_upwards [Xc.T.eventually_cofinite_notMem] with v hv using (hm.fin.sph v hv).1.symm

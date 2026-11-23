import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AutomorphicArithmetic.DivisorFrames.ExistsThOEqOfIsLatVacThetaFun
import Development.AutomorphicArithmetic.DivisorFrames.IsSBHalfThetaFunOfHalfIdempotentPlaces
import Development.AutomorphicArithmetic.DivisorFrames.ExistsGlStdFstEqProductLocal
import Development.AutomorphicArithmetic.DivisorFrames.ExistsGlStdSndEqProductLocal
import Development.AutomorphicArithmetic.DivisorFrames.BigPStdSchwartzTranslateEqSmallPOfIsUnif
import Development.AutomorphicArithmetic.DivisorFrames.ExistsPolynomialOfIsFinFThetaLiftPureTensor
import Development.AutomorphicArithmetic.DivisorFrames.IdempotentSumFixesIffHalfEl
import Development.AutomorphicArithmetic.DivisorFrames.StdAStdBMemSchwartzBruhat
import Development.AutomorphicArithmetic.DivisorFrames.ExistsLatticeThetaDataOfRamificationPlacesCMDatu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartFrSgnFalseRigFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareInfinityExponentGapLargeGridsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageFinitePlacesUnramifiedOrSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockAlgebraicThetaVectorsStableFiniteAdelesLieStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawFramesWeilEquivalenceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilIntertwiningValueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilLocalFactorEqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilArchimedeanFactorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilUnramifiedFactorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilGlobalFactorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaArchimedeanStatement

noncomputable section

namespace GlobalTheory.FinMatch

section Local

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.SplitFlip GlobalTheory.StdPairCone
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem isLin_smul {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {v : Pl F}
    {π₁ π₀ : AE F E →+* Fv F v} {co ι} (h : M.IsLin ψ π₁ π₀ co ι) {c : ℂ} (hc : c ≠ 0) : M.IsLin ψ π₁ π₀ co (c • ι) := by
  refine ⟨⟨fun φ hφ => Submodule.smul_mem _ c (h.bij.mapsTo hφ), fun φ hφ φ' hφ' e => h.bij.injOn hφ hφ' ?_, fun Ψ hΨ => ?_⟩,
    fun u a b φ hφ φ₁ hφ₁ ha Y => ?_, fun u a b φ hφ φ₁ hφ₁ ha x hx hx' => ?_⟩
  · exact smul_right_injective _ hc e
  · obtain ⟨φ, hφ, e⟩ := h.bij.surjOn (Submodule.smul_mem _ c⁻¹ hΨ)
    exact ⟨φ, hφ, by rw [LinearMap.smul_apply, e, smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  · simp only [LinearMap.smul_apply, Pi.smul_apply, h.trans u a b φ hφ φ₁ hφ₁ ha Y]
  · simp only [LinearMap.smul_apply, Pi.smul_apply, h.mult u a b φ hφ φ₁ hφ₁ ha x hx hx', smul_eq_mul]
    ring

private theorem local_match {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {R : FinMaps F a a'} (v : B.P) (hZ : IsZetaAt B G X R v) (n : ℕ)
    (g : GL (Fin a) (Fv F v)) (g' : GL (Fin a') (Fv F v)) (m : GL (Fin (a + a')) (Fv F v)) :
    ∃ (b : GL (Fin a) (Fv F v)) (c : GL (Fin (a + a')) (Fv F v)) (b' : GL (Fin a') (Fv F v)) (c' : GL (Fin (a + a')) (Fv F v))
      (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ))
      (ι' : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ))
      (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) (φ' : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      G.M.IsLin B.ψ (piW (B.τ v)) (piW ((B.τ v).comp σ)) (fun u => b.1 * u.map (piW (B.τ v)) * c.1) ι ∧
      G.M'.IsLin B.ψ (piW ((B.τ v).comp σ)) (piW (B.τ v)) (fun u => b'.1 * u.map (piW ((B.τ v).comp σ)) * c'.1) ι' ∧
      φ ∈ SB _ ∧ φ' ∈ SB _ ∧
      (∀ U : Matrix (Fin a) (Fin (a + a')) (Fv F v), ι φ (b.1 * U * c.1) = stdA (chrW X.ν (B.τ v)) (unifAt v.1) n a a' (g.1 * U * (invT m).1)) ∧
      (∀ U : Matrix (Fin a') (Fin (a + a')) (Fv F v), ι' φ' (b'.1 * U * c'.1) = stdB (chrW X.ν (B.τ v)) (unifAt v.1) n a a' (g'.1 * U * (G.W.J.map (B.τ v))ᵀ * m.1)) ∧
      R.p v φ = R.p' v φ' ∧ R.p v φ ≠ 0 := by
  obtain ⟨ι, ι', hι, hι', -, -, hz⟩ := hZ
  have hν : GlobalTheory.LFun.IsHecke F E X.ν := ⟨hT.chars.heckeα.1.div' hT.chars.heckeβ.1, fun x => by
    rw [Chars.ν, MonoidHom.div_apply, hT.chars.heckeα.2, hT.chars.heckeβ.2, div_one]⟩
  have h1 := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.ν hν v (B.τ v)).2.1
  have hdiv : chrW X.ν (B.τ v) = chrW X.α (B.τ v) / chrW X.β (B.τ v) := by
    ext x
    simp [chrW, Chars.ν, GlobalTheory.LFun.locChar]
  have hϖ : IsUnif (unifAt v.1) := (exists_isUnif (k := Fv F v.1)).choose_spec
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have dV : G.V'.J.det ≠ 0 :=
    GlobalTheory.TripleAssembly.PureImage.det_ne_of_sig_map (B.emb w).1 1 (by rw [one_smul]; exact hT.geo.hV'.sig w)
  have dW : G.W.J.det ≠ 0 := GlobalTheory.TripleAssembly.PureImage.det_ne_of_sig_map (B.emb w).1 Complex.I (hT.geo.hW.sig w)
  have dm : ∀ {k : ℕ} (J : Matrix (Fin k) (Fin k) E), J.det ≠ 0 → (J.map (B.τ v)).det ≠ 0 := fun J hJ => by
    have : (J.map (B.τ v)).det = B.τ v J.det := (RingHom.map_det (B.τ v : E →+* Fv F v) J).symm
    rw [this]
    exact (map_ne_zero _).2 hJ
  let JV := GeneralLinearGroup.mkOfDetNeZero _ (dm _ dV)
  let JW := GeneralLinearGroup.mkOfDetNeZero _ (dm _ dW)
  generalize G.V.bas v = b at hι
  generalize G.W.bas v = c at hι hι'
  generalize G.V'.bas v = b₂ at hι'
  let b' : GL (Fin a') (Fv F v) := -((invT b₂)⁻¹ * JV)
  let c' : GL (Fin (a + a')) (Fv F v) := (invT JW)⁻¹ * c
  obtain ⟨sA, sB⟩ := UpperTheory.stdA_stdB_mem_schwartzBruhat (Fv F v) (chrW X.ν (B.τ v)) (unifAt v.1) hϖ h1 n a a'
  obtain ⟨hne, l, hl⟩ := UpperTheory.bigZeta_stdSchwartz_translate_eq_smallZeta (Fv F v) (unifAt v.1) hϖ _ _ _ hdiv n a a' (g * b) (g' * b'⁻¹) (m⁻¹ * c)
  have sA' := comp_mul_mem_SB (g * b) (invT (m⁻¹ * c))⁻¹ sA
  have sB' := comp_mul_mem_SB (g' * b'⁻¹) (m⁻¹ * c)⁻¹ sB
  obtain ⟨φ, hφ, eφ⟩ := hι.bij.surjOn sA'
  obtain ⟨φ', hφ', eφ'⟩ := hι'.bij.surjOn (Submodule.smul_mem _ l sB')
  have s0 : smallP (haarVol (GlobalTheory.SplitWeil.KO (Fv F v) (Fin a'))) (finSumFinEquiv (m := a) (n := a')) (chrW X.ν (B.τ v))
      (chrW X.α (B.τ v)) 0 = 0 := by
    funext h; simp [smallP, smallF]
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_smul, s0] at hl
    exact hne hl
  refine ⟨b⁻¹, invT c, b', c', ι, l⁻¹ • ι', φ, φ', hι, isLin_smul ?_ (inv_ne_zero hl0), hφ, hφ', fun U => ?_, fun U => ?_,
    (hz φ hφ φ' hφ').2 (by rw [eφ, eφ']; exact hl), fun h0 => hne ?_⟩
  · have e : (fun u : Matrix (Fin a') (Fin (a + a')) (AE F E) => b'.1 * u.map (piW ((B.τ v).comp σ)) * c'.1) = fun u =>
        -(b₂.1ᵀ * G.V'.J.map (B.τ v) * u.map (piW ((B.τ v).comp σ)) * (G.W.J.map (B.τ v))ᵀ * c.1) := by
      funext u
      have e1 : b'.1 = -(b₂.1ᵀ * G.V'.J.map (B.τ v)) := rfl
      have e2 : c'.1 = (G.W.J.map (B.τ v))ᵀ * c.1 := rfl
      rw [e1, e2]
      simp only [Matrix.neg_mul, Matrix.mul_assoc]
    rw [e]
    exact hι'
  · rw [eφ]
    beta_reduce
    refine congrArg _ ?_
    have e1 : (invT c).1 * ((invT (m⁻¹ * c))⁻¹).1 = (invT m).1 := by
      rw [← Units.val_mul, map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    have e2 : (g * b).1 * (b⁻¹).1 = g.1 := by rw [← Units.val_mul, mul_inv_cancel_right]
    rw [← e1, ← e2]
    simp only [Matrix.mul_assoc]
  · rw [LinearMap.smul_apply, eφ', smul_smul, inv_mul_cancel₀ hl0, one_smul]
    refine congrArg (stdB (chrW X.ν (B.τ v)) (unifAt v.1) n a a') ?_
    have e1 : c'.1 * ((m⁻¹ * c)⁻¹).1 = (G.W.J.map (B.τ v))ᵀ * m.1 := by
      rw [← Units.val_mul, _root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
      rfl
    have e2 : (g' * b'⁻¹).1 * b'.1 = g'.1 := by rw [← Units.val_mul, inv_mul_cancel_right]
    rw [Matrix.mul_assoc (g'.1 * U), ← e1, ← e2]
    simp only [Matrix.mul_assoc]
  · have := (hz φ hφ 0 (zero_mem _)).1 (by rw [h0, map_zero])
    rw [eφ, map_zero, s0] at this
    exact this

end Local

section Pair

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

private theorem fock_of_thetaAt {ψ : AddChar (AF D.host.F) ℂ} {ε : Bool} {S X : HSp D} {d : ℕ} {e : Fin d ≃ Fin X.rank}
    {Bs : Base D.host.F D.host.E} {Vs : Spc D.host.F D.host.E S.rank} {Ws : Spc D.host.F D.host.E d}
    {M : Model D.sp.cm.sig Vs Ws} (hP : IsPair ψ ε S X e Bs Vs Ws M)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)}
    (hL : IsLat e Vs Ws ΛS ΛX) (h1 : IsSelfDualC (sgn ε S) ΛS) (h2 : IsSelfDualC X ΛX)
    {θ : InfFam D} (hθ : IsInfFam θ) {A : Fr S} {B : Fr X} (hc : IsCart ε A B e Bs Vs Ws)
    {P : Finset (HeightOneSpectrum (𝓞 D.host.F))} {t₁ t₀ : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v}
    (ht : ∀ v x, t₀ v x = t₁ v (D.sp.cm.sig x)) {eh : AE D} (hh : ∀ z : AE D, eh * z = z ↔ HalfEl P t₀ z)
    (hh' : ∀ z : AE D, cA D eh * z = z ↔ HalfEl P t₁ z)
    {b : ∀ v : P, GL (Fin S.rank) (Fv D.host.F v)} {c : ∀ v : P, GL (Fin d) (Fv D.host.F v)}
    {ι : ∀ v : P, ((Fin S.rank × Fin d → Fv D.host.F v) → ℂ) →ₗ[ℂ] (Matrix (Fin S.rank) (Fin d) (Fv D.host.F v) → ℂ)}
    (hι : ∀ v, M.IsLin ψ (piW (t₁ v)) (piW (t₀ v)) (fun u => (b v).1 * u.map (piW (t₁ v)) * (c v).1) (ι v))
    {φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → Fv D.host.F v) → ℂ} (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (hφ' : ∀ v, v ∉ P → φ v = M.vac v) (hφ0 : ∀ v, φ v ≠ 0) {sS sX} {f₀ Φ f : WO (sgn ε S) X → ℂ}
    (hv : IsVacO ψ θ (sgn ε S) X sS sX (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) f₀)
    (hΦ : ∀ x, Φ x = if IsHalf eh x then
      ∏ v : P, ι v (φ v) ((b v).1 * (ptO (sgn ε S).gram e x).map (piW (t₁ v)) * (c v).1) else 0)
    (hf : IsThetaAt ψ (symplO (sgn ε S) X) (heisO ψ (sgn ε S) X) eh
      (latO (sgn ε S) X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True) 1 f₀ Φ f)
    (hF : IsFinF ψ θ ε A B f) : ∀ g₁ ∈ M.Pol Bs.ψ Bs.emb, ∃ Q : PolF D X.rank S.rank,
      fockF ψ θ ε A B f Q = thO M ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) := by
  obtain ⟨g, hg⟩ := UpperTheory.exists_thO_eq_of_isLatVac_thetaFun D ψ ε S X d e Bs Vs Ws M hP ΛS ΛX hL f₀ hv.2.theta hv.2.lat
  have g0 : g ≠ 0 := by
    rintro rfl
    have : f₀ = 0 := by
      rw [hg]
      funext x
      simp [thO, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    subst this
    obtain ⟨⟨p, hp⟩, hn⟩ := hv.2.norm
    simpa [nrm2] using hn p hp
  rw [hg] at hf
  obtain ⟨z, hz, rfl⟩ := UpperTheory.isSBHalf_thetaFun_of_halfIdempotent_places D ψ ε S X d e Bs Vs Ws M hP ΛS ΛX hL h1 h2 P t₁ t₀ ht eh hh hh' b c ι hι φ hφ hφ' g Φ f hΦ hf
  refine UpperTheory.exists_polynomial_of_isFinF_thetaLift_pureTensor D ψ ε S X d e Bs Vs Ws M hP θ hθ A B hc _ φ hφ ?_ (smul_ne_zero hz g0) hφ0 hF
  exact Filter.eventually_cofinite.2 (P.finite_toSet.subset fun v hv => by_contra fun h => hv (hφ' v h))

private theorem pureT_ne_zero {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] {s ξ : ∀ i, N i}
    (h : Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ) (h0 : ∀ i, ξ i ≠ 0) : GlobalTheory.SmallThetaModules.pureT s ξ ≠ 0 := by
  have : ∀ i, ∃ l : N i →ₗ[ℂ] ℂ, l (ξ i) = 1 := fun i => by
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (N i), φ (ξ i) ≠ 0 :=
      not_forall.1 fun h => h0 i ((Module.forall_dual_apply_eq_zero_iff ℂ (ξ i)).1 h)
    exact ⟨(φ (ξ i))⁻¹ • φ, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ]⟩
  choose l hl using this
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.SmallThetaModules.pureT_sep s l (h.subset fun i hi e => hi (e ▸ hl i))
  intro e
  have := hΛ ξ h
  simp [e, hl] at this

end Pair

section Main

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem exists_match (hP : GlobalTheory.FunPr.Hypotheses₂) (hLM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW)
    {α β : T → ((AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))}
    (hX : X.Is ψ θ α β νH S) (t : T) (hT : IsTriple A A' WW (α t) (β t))
    (hram : ∀ v ε, IsPlaceIdem D v ε → ((∃ w ∈ S t, w.under (𝓞 D.host.F) = v) → ¬ GlobalTheory.WeilParts.UnramAt ε (α t / β t)) ∧
      ((∀ w ∈ S t, w.under (𝓞 D.host.F) ≠ v) → GlobalTheory.WeilParts.UnramAt ε (α t) ∧ GlobalTheory.WeilParts.UnramAt ε (β t)))
    (FA : Fr A) (FA' : Fr A') (FW : Fr WW) (hf : IsFinF ψ θ true FA FW (X.f t)) (hf' : IsFinF ψ θ false FA' FW (X.f' t)) :
    ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi)
      (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi)
      (p : (WO A WW → ℂ) →ₗ[ℂ] Pi) (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi),
      IsMatch ψ θ FA FA' FW (α t) (β t) (X.ω t) (X.ω' t) Pi rf rl p p' ∧
      ∃ (P : PolF D WW.rank A.rank) (P' : PolF D WW.rank A'.rank) (κ : ℂ),
        p (fockF ψ θ true FA FW (X.f t) P) ≠ 0 ∧
        p (fockF ψ θ true FA FW (X.f t) P) = κ • p' (fockF ψ θ false FA' FW (X.f' t) P') := by
  have hH := hP.howeDualityReal
  have hr := hX.rank
  have hA := hX.weil t
  have hB := hX.weil' t
  obtain ⟨Bs, Γ, Xc, om, om', h, hTr, hTA, hTB, hLA, hLB, hTP, hPS, hτ⟩ := UpperTheory.exists_lattice_theta_data_of_ramification_places_CMDatum D ψ hψ A A' WW FA FA' FW _ _ hT _ _ hA hB
    _ _ _ hX.rigA.1 hX.rigA'.1 hX.rigW.1 (S t) hram (finCongr hr)
  obtain ⟨R, Rf, hM⟩ := hLM D.host.F D.host.E D.sp.cm.sig Bs A.rank A'.rank Γ Xc om om' hTr
  have pA : IsPair ψ true A WW (finCongr hr) Bs Γ.V Γ.W Γ.M :=
    ⟨hTr.base, h.ψ, h.JW, h.JX, ⟨_, _, hTr.geo.hV⟩, ⟨_, _, hTr.geo.hW⟩, hTr.geo.hM⟩
  have pB : IsPair ψ false A' WW (finCongr hr) Bs Γ.V' Γ.W Γ.M' :=
    ⟨hTr.base, h.ψ, h.JW₁, h.JX, ⟨_, _, hTr.geo.hV'⟩, ⟨_, _, hTr.geo.hW⟩, hTr.geo.hM'⟩
  have cA' : IsCart true FA FW (finCongr hr) Bs Γ.V Γ.W := fun w => by
    obtain ⟨τ, h1, h2, -, h4⟩ := h.cart w
    exact ⟨τ, h1, by rw [h2]; simp, h4⟩
  have cB' : IsCart false FA' FW (finCongr hr) Bs Γ.V' Γ.W := fun w => by
    obtain ⟨τ, h1, -, h2, h4⟩ := h.cart w
    exact ⟨τ, h1, by rw [h2]; simp, h4⟩
  let m : ∀ v : Bs.P, GL (Fin (A.rank + A'.rank)) (Fv D.host.F v) := fun v =>
    Units.map (Matrix.reindexAlgEquiv (Fv D.host.F v) (Fv D.host.F v) (finCongr hr).symm).toMonoidHom
      (GeneralLinearGroup.map (piF (Bs.τ v)) X.rW.β)
  obtain ⟨g, hg⟩ := UpperTheory.exists_gl_stdFst_eq_product_local D _ _ (hX.idem t) Bs.P Bs.τ hPS hτ (α t / β t) (X.c t) A WW A'.rank hr X.rA.β X.rW.β m
    fun _ => rfl
  obtain ⟨g', hg'⟩ := UpperTheory.exists_gl_stdSnd_eq_product_local D _ _ (hX.idem t) Bs.P Bs.τ hPS hτ (α t / β t) (X.c t) A' WW A.rank hr X.rA'.β X.rW.β m
    fun _ => rfl
  obtain ⟨hh, hh'⟩ := UpperTheory.idempotentSum_fixes_iff_halfEl D _ _ (hX.idem t) Bs.P Bs.τ hPS hτ
  have hν : Xc.ν = α t / β t := by rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars.ν, h.α, h.β]
  choose b c b' c' ι ι' φl φl' hι hι' hφ hφ' eφ eφ' hp hp0 using fun v : Bs.P =>
    local_match hTr v (hM.fin.zeta v (by rw [hTP]; exact v.2)) (X.c t (splitPrime (Bs.τ v))) (g v) (g' v) (m v)
  let φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin A.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ :=
    fun v => if hv : v ∈ Bs.P then φl ⟨v, hv⟩ else Γ.M.vac v
  let φ' : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin A'.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ :=
    fun v => if hv : v ∈ Bs.P then φl' ⟨v, hv⟩ else Γ.M'.vac v
  have e1 : ∀ v : Bs.P, φ v = φl v := fun v => dif_pos v.2
  have e1' : ∀ v : Bs.P, φ' v = φl' v := fun v => dif_pos v.2
  have e2 : ∀ v, v ∉ Bs.P → φ v = Γ.M.vac v := fun v hv => dif_neg hv
  have e2' : ∀ v, v ∉ Bs.P → φ' v = Γ.M'.vac v := fun v hv => dif_neg hv
  have sb : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _ := fun v => by
    by_cases hv : v ∈ Bs.P
    · exact e1 ⟨v, hv⟩ ▸ hφ ⟨v, hv⟩
    · exact e2 v hv ▸ (hTr.geo.hM.vac v).1
  have sb' : ∀ v, φ' v ∈ GlobalTheory.WeilM.SB _ := fun v => by
    by_cases hv : v ∈ Bs.P
    · exact e1' ⟨v, hv⟩ ▸ hφ' ⟨v, hv⟩
    · exact e2' v hv ▸ (hTr.geo.hM'.vac v).1
  have im : ∀ v, Rf.p v (φ v) = Rf.p' v (φ' v) ∧ Rf.p v (φ v) ≠ 0 := fun v => by
    by_cases hv : v ∈ Bs.P
    · have a1 := e1 ⟨v, hv⟩
      have a2 := e1' ⟨v, hv⟩
      dsimp only at a1 a2
      rw [a1, a2]
      exact ⟨hp ⟨v, hv⟩, hp0 ⟨v, hv⟩⟩
    · rw [e2 v hv, e2' v hv]
      exact hM.fin.sph v (hTP ▸ hv)
  have cof : ∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v :=
    Filter.eventually_cofinite.2 (Bs.P.finite_toSet.subset fun v hv => by_contra fun h => hv (e2 v h))
  have cof' : ∀ᶠ v in Filter.cofinite, φ' v = Γ.M'.vac v :=
    Filter.eventually_cofinite.2 (Bs.P.finite_toSet.subset fun v hv => by_contra fun h => hv (e2' v h))
  have sdA : IsSelfDualC (sgn true A) X.rA.Λ := by
    refine ⟨hX.rigA.1.1, fun y => (hX.rigA.1.2 y).trans (forall₂_congr fun x _ => ?_)⟩
    have : ∑ i, ∑ j, star (x i) * (sgn true A).gram i j * y j = -∑ i, ∑ j, star (x i) * A.gram i j * y j := by
      simp only [neg_gram, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]
    rw [this]
    exact ⟨fun ⟨b, hb⟩ => ⟨-b, by rw [← hb]; rfl⟩, fun ⟨b, hb⟩ => ⟨-b, by rw [← neg_neg (Finset.sum _ _), ← hb]; rfl⟩⟩
  have kA := fock_of_thetaAt pA hLA sdA hX.rigW.1 hθ cA' (t₁ := Bs.τ) (fun _ _ => rfl) hh hh' (h.ψ ▸ hι) sb e2
    (fun v h0 => (im v).2 (by rw [h0, map_zero])) hX.isVac (fun x => by
      refine (hg x).trans (if_congr Iff.rfl (Finset.prod_congr rfl fun v _ => ?_) rfl)
      rw [e1, eφ, hν]) (hX.fst t) hf
  have kB := fock_of_thetaAt pB hLB hX.rigA'.1 hX.rigW.1 hθ cB' (t₀ := Bs.τ) (t₁ := fun v => (Bs.τ v).comp D.sp.cm.sig)
    (fun v x => congrArg (Bs.τ v) (star_star x).symm) hh' (fun z => by rw [Formalism.L2.Theta.cA_cA]; exact hh z) (h.ψ ▸ hι') sb' e2'
    (fun v h0 => (im v).2 (by rw [(im v).1, h0, map_zero])) hX.isVac' (fun x => by
      refine (hg' x).trans (if_congr Iff.rfl (Finset.prod_congr rfl fun v _ => ?_) rfl)
      rw [e1', eφ', hν, h.JX]) (hX.snd t) hf'
  haveI := hM.real.nontriv
  obtain ⟨y, hy⟩ := exists_ne (0 : R.Pi)
  obtain ⟨f, hfP, hfy⟩ := Submodule.mem_map.1 (hM.real.quot.onto ▸ Submodule.mem_top (x := y))
  obtain ⟨f', hfP', hfy'⟩ := Submodule.mem_map.1 (hM.real.quot'.onto ▸ Submodule.mem_top (x := y))
  obtain ⟨Q, hQ⟩ := kA f hfP
  obtain ⟨Q', hQ'⟩ := kB f' hfP'
  have mA := GlobalTheory.TripleAssembly.PureImage.mapA_thO_sum_pure hH hP D ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h
    hTA hTB R Rf hM 1 (fun _ => f) (fun _ => φ) (fun _ => ⟨sb, cof⟩)
    (by rw [Fin.sum_univ_one]; exact Submodule.subset_span ⟨f, φ, hfP, sb, cof, rfl⟩)
  have mB := GlobalTheory.T.seesaw_weil_zeta_archimedean hH hP D ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h
    hTA hTB R Rf hM 1 (fun _ => f') (fun _ => φ') (fun _ => ⟨sb', cof'⟩)
    (by rw [Fin.sum_univ_one]; exact Submodule.subset_span ⟨f', φ', hfP', sb', cof', rfl⟩)
  rw [Fin.sum_univ_one, Fin.sum_univ_one, ← hQ, hfy] at mA
  rw [Fin.sum_univ_one, Fin.sum_univ_one, ← hQ', hfy', ← funext fun v => (im v).1] at mB
  have sA := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D ψ θ hψ hθ true A WW FA FW _ _ _ hA
  have sB := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D ψ θ hψ hθ false A' WW FA' FW _ _ _ hB
  obtain ⟨oA, oB⟩ := GlobalTheory.T.algF_map_mapA_and_mapB_eq_top hH hP D ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨iA, iB⟩ := GlobalTheory.T.mapA_mapB_invariant_under_finite_group hH hP D ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨lA, lB⟩ := GlobalTheory.T.seesaw_weil_local_factor_eq hH hP D ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨fA, fB⟩ := GlobalTheory.T.seesaw_weil_archimedean_factor hH hP D ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨dA, dB⟩ := GlobalTheory.T.seesaw_weil_unramified_factor hH hP D ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  have ir := GlobalTheory.T.seesaw_weil_global_factor hH hP D ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  refine ⟨ModuleCat.of ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf), _, _, _, _,
    ⟨hA, hB, ir, ⟨sA.1, sA.2, oA, iA, lA, fA, dA⟩, ⟨sB.1, sB.2, oB, iB, lB, fB, dB⟩⟩, Q, Q', 1, ?_, ?_⟩
  · refine ne_of_eq_of_ne mA fun h0 => ?_
    have hn := pureT_ne_zero (s := GlobalTheory.TripleAssembly.vacIm Γ Rf) (ξ := fun v => Rf.p v (φ v))
      ((Filter.eventually_cofinite.1 cof).subset fun v hv e => hv (congrArg (Rf.p v) e)) fun v => (im v).2
    obtain ⟨l, hl⟩ : ∃ l : Module.Dual ℂ R.Pi, l y ≠ 0 :=
      not_forall.1 fun h => hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 h)
    have := congrArg (fun z => TensorProduct.lid ℂ _ (l.rTensor _ z)) h0
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_zero, smul_eq_zero] at this
    exact this.elim hl hn
  · rw [one_smul]
    exact mA.trans mB.symm

end Main

end GlobalTheory.FinMatch

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.FinMatch

private theorem pow_apply' {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (x) : (χ ^ a).1 x = χ.1 x ^ a := by
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

private theorem loc_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) :
    (χ ^ a).loc v x = χ.loc v x ^ a :=
  pow_apply' χ a _

private theorem locK_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) :
    (χ ^ a).locK v x = χ.locK v x ^ a :=
  pow_apply' χ a _

private theorem unrAt_pow {E : Type} [Field E] [NumberField E] {χ : HChar E} {v} (h : χ.UnrAt v) (a : ℕ) :
    (χ ^ a).UnrAt v :=
  fun x hx => by rw [loc_pow, h x hx, one_pow]

private theorem chrEq_pow {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) (a : ℕ) :
    ChrEq (c ^ a) (χ ^ a) := by
  refine ⟨⟨?_, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · have : ((c ^ a : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => c x ^ a := by
      funext x; simp
    rw [this]
    exact h.1.1.pow a
  · have h1 := h.1.2 x
    simp only [MonoidHom.pow_apply, h1, one_pow]
  · rw [MonoidHom.pow_apply, locK_pow, Units.val_pow_eq_pow_val, ← h.2 P e he k x hx]
    exact map_pow Circle.coeHom _ _

private theorem grid_ram {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (t : T) (i j : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F) (he : IsPlaceIdem D v e) :
    ((∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) → ¬ GlobalTheory.WeilParts.UnramAt e
      (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)))) ∧
    ((∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) → GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) ∧
      GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) := by
  classical
  have hm1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have hm2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  have hα : ChrEq (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (alphaH Lc t i j) :=
    GlobalTheory.TwistChr.chrEq_mul (GlobalTheory.TwistChr.chrEq_mul (hL.mu0 j) (hL.xi t)) (chrEq_pow hL.eta _)
  have hβ : ChrEq (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (betaH G i j) :=
    GlobalTheory.TwistChr.chrEq_mul (G.ch.chi_eq _ hm1 hm2) (chrEq_pow hL.eta _)
  have hν : ChrEq (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)))
      (nuH G t i j) := by
    rw [mul_div_mul_right_eq_div]
    exact chrEq_nu G t i j hL
  have hmu : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ∉ S1 D → (Lc.C.mu0 j).UnrAt P :=
    fun P hP => (Lc.C.isMu0 j).unr _ fun k hk => hP (by
      have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
        rw [map_natCast]; exact hk
      refine (S1_mem_OmF D).2 ?_
      fin_cases k
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
  have hxi : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      (∀ PP ∈ Lc.Q t, PP.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F)) → (Lc.xiH t).UnrAt P := fun P hP => by
    by_contra hc
    rcases (hL.Q_ram t P).1 hc with h | ⟨PP', h, hc'⟩
    · exact hP P h rfl
    · exact hP PP' h (GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc')
  have hchi : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ∉ G.pl.S0 →
      (G.ch.chiH (D.R.m - i)).UnrAt P := fun P hP => G.ch.unr _ hm1 hm2 P hP
  have heta : ∀ P : HeightOneSpectrum (𝓞 D.host.E), (Lc.C.eta ^ (rankV D i j % 2)).UnrAt P :=
    fun P => unrAt_pow (Lc.C.isEta.unr P) _
  constructor
  · rintro ⟨w, hw, hv⟩ hu
    have hS : v ∈ G.pl.S0 ∨ ∃ PP ∈ Lc.Q t, PP.under (𝓞 D.host.F) = v := by
      rcases Finset.mem_union.1 hw with hw | hw
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hw
        exact Or.inl (hv ▸ (G.pl.under_w hu).symm ▸ hu)
      · exact Or.inr ⟨w, hw, hv⟩
    have key : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v → (nuH G t i j).UnrAt P :=
      fun P hP => (GlobalTheory.LFun.unrAt_iff_of_chrEq hν P).1 (GlobalTheory.UnrOverPlace.unrAt_of_unramAt D _ v e he hu P hP)
    by_cases h0 : v = G.pl.v0
    · subst h0
      exact GlobalTheory.RowTest.squareNuHeckeCharacter_not_unramified_at_chosenPlace hL G t i j (key _ (G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))))
    · by_cases h1 : v ∈ S1 D
      · have hv : v ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inr h1)
        have hwv' := G.pl.under_w hv
        apply (G.ch.lev1 _ hm1 hm2 (G.pl.w v) (by rw [hwv']; exact h1)).2
        have ee : G.ch.chiH (D.R.m - i) = Lc.C.mu0 j * Lc.xiH t / nuH G t i j := by
          rw [nuH, div_div_cancel]
        rw [ee, div_eq_mul_inv]
        exact HChar.LevelLe.mul (HChar.LevelLe.mul ((Lc.C.isMu0 j).tame _) (hL.xi_tame t _))
          (HChar.LevelLe.inv (fun x hx _ => key _ hwv' x hx))
      · obtain ⟨PP, hP, hPv⟩ := hS.resolve_left fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim h0 h1
        apply (hL.Q_ram t PP).2 (Or.inl hP)
        have ee : Lc.xiH t = nuH G t i j * G.ch.chiH (D.R.m - i) / Lc.C.mu0 j := by
          rw [nuH, div_mul_cancel, mul_div_cancel_left]
        rw [ee, div_eq_mul_inv]
        exact ((key PP hPv).mul (hchi PP (by rw [hPv]; exact fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim h0 h1))).mul
          (hmu PP (by rw [hPv]; exact h1)).inv
  · intro h
    have hS0 : v ∉ G.pl.S0 := fun h0 =>
      h _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h0)) (G.pl.under_w h0)
    have hQ : ∀ PP ∈ Lc.Q t, PP.under (𝓞 D.host.F) ≠ v := fun w hw => h w (Finset.mem_union_right _ hw)
    have hS1 : v ∉ S1 D := fun h => hS0 (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
    refine ⟨GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D _ _ hα v e he fun P hP => ?_, GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D _ _ hβ v e he fun P hP => ?_⟩
    · exact ((hmu P (by rw [hP]; exact hS1)).mul (hxi P fun PP hPP h => hQ PP hPP (h.trans hP))).mul (heta P)
    · exact (hchi P (by rw [hP]; exact hS0)).mul (heta P)

end GlobalTheory.FinMatch

theorem _root_.GlobalTheory.T.square_tower_finite_frame : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (a b : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j a b X →
    ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) → GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) →
    ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi)
      (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi)
      (p : (WO A WW → ℂ) →ₗ[ℂ] Pi) (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi),
      GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' ∧
      ∃ (P : PolF D WW.rank A.rank) (P' : PolF D WW.rank A'.rank) (κ : ℂ),
        p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) ≠ 0 ∧
        p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) = κ • p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') := by
  intro hP _ hLM
  obtain ⟨a₁, h₁⟩ := GlobalTheory.T.gridSquare_infinityExponent_gap_largeGrids
  obtain ⟨a₂, h₂⟩ := GlobalTheory.T.towerStage_finitePlaces_unramified_or_split
  refine ⟨max a₁ a₂, fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, h₁⟩ := h₁ ε CF (le_of_max_le_left hCF)
  obtain ⟨C₂, x₂, h₂⟩ := h₂ ε CF (le_of_max_le_right hCF)
  refine ⟨max C₁ C₂, max x₁ x₂, fun C hC D large₂ he hx r T Lc μ hLc G W i j p q A A' WW X hX FA FA' FW t hf hf' => ?_⟩
  obtain ⟨a, b, hab⟩ := h₁ C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) r T Lc μ hLc G W i j
  have hram := h₂ C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) r T Lc μ hLc G W i j p q A A' WW X hX t
  obtain ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩ := hX
  have hsz := GlobalTheory.StageDict.stage_sizes i j hp hq hrA hrA'
  have hrk : WW.rank = A.rank + A'.rank := hXi.rank.symm
  refine GlobalTheory.FinMatch.exists_match hP hLM W.ψ_std W.θ_is X hXi t ?_ (GlobalTheory.FinMatch.grid_ram G hLc t i j) FA FA' FW hf hf'
  refine
    { hecA := (hXi.weil' t).hecS
      hecB := (hXi.weil t).hecS
      resA := (hXi.weil' t).resS
      resB := (hXi.weil t).resS
      rank := hrk
      even := by rw [hrk]; exact hsz.1
      sig := ⟨p, q, fun τ => ⟨hnA τ, hnA' τ, hnW τ⟩, hsz.2.1, hsz.2.2.1⟩
      gap := fun τ => ⟨a τ, b τ, (hab t τ).1, (hab t τ).2.1, ?_⟩
      ram := hram }
  have h1 := (hab t τ).2.2
  have h2 : ((WW.rank : ℕ) : ℚ) ≤ ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) := by
    exact_mod_cast (hrk ▸ hsz.2.2.2)
  linarith

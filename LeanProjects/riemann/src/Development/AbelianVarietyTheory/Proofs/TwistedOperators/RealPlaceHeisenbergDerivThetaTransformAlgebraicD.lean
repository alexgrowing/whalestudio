import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanLineEqRealScalarSmulSupportedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelSymplecticEqOrientedPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumHeisenbergLineStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.HeisDeriv

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

section Gen

variable {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
  {κ : Type} [Fintype κ]

theorem rho_rho (d : Darboux B κ) (ψ : AddChar (AF F) ℂ) (w v : W) (Φ : (κ → AF F) → ℂ) :
    d.rho ψ w (d.rho ψ v Φ) = ψ (⅟(2 : AF F) * B w v) • d.rho ψ (w + v) Φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, map_add, Prod.fst_add, Prod.snd_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  rw [d.form]
  simp only [add_dotProduct, dotProduct_add]
  have h2 : ⅟(2 : AF F) + ⅟(2 : AF F) = 1 := invOf_two_add_invOf_two
  linear_combination (-((d.e w).1 ⬝ᵥ (d.e v).2)) * h2

theorem thetaSum_smul (c : ℂ) (Φ : (κ → AF F) → ℂ) : thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

end Gen

section Model

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {Wd : Spc F E d}

theorem algD_le_schA (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w)
    (hM : M.IsGood ψ) : algD M ψ emb ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, -, hSB, hev, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hM.std).mono fun v hv => hv.1.trans hv.2)

theorem exists_actsD_mem_Pol (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w)
    (hψ : IsStd ψ) (u : Matrix (Fin n) (Fin d) (AE F E)) (hu : At (evI F) u) (g : SInf F (Fin n × Fin d))
    (hg : g ∈ M.Pol ψ emb) : ∃ g₁ ∈ M.Pol ψ emb, ActsD (evI F) (M.heisLine ψ u) g g₁ := by
  obtain ⟨Dr, hDr⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F Y.J) (incM F Wd.J) M.co hψ
  have hSD := (hDr u hu g).1
  have hA : ActsD (evI F) (M.heisLine ψ u) g (Dr u g) :=
    (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) g (Dr u g) (Dr u g)).1 (M.heisLine ψ u)
      (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr]) hSD
  refine ⟨Dr u g, Submodule.mem_sInf.2 fun N hN => hN.2 u hu g (Submodule.mem_sInf.1 hg N hN) _ hA, hA⟩

theorem exists_deriv_algD (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w)
    (hψ : IsStd ψ) (hM : M.IsGood ψ) (u : Matrix (Fin n) (Fin d) (AE F E)) (hu : At (evI F) u) :
    ∀ Φ ∈ algD M ψ emb, ∃ Φ' ∈ algD M ψ emb,
      ∀ x, HasDerivAt (fun t : ℝ => M.co.rho ψ (realAd F t • u) Φ x) (Φ' x) 0 := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, zero_mem _, fun x => ?_⟩
    simpa [Darboux.rho, schr] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add a b _ _ ha hb =>
    obtain ⟨a', ha', hda⟩ := ha
    obtain ⟨b', hb', hdb⟩ := hb
    refine ⟨a' + b', add_mem ha' hb', fun x => ?_⟩
    have e : (fun t : ℝ => M.co.rho ψ (realAd F t • u) (a + b) x) =
        fun t => M.co.rho ψ (realAd F t • u) a x + M.co.rho ψ (realAd F t • u) b x := by
      funext t; simp [Darboux.rho, schr, mul_add]
    rw [e]
    exact (hda x).add (hdb x)
  | smul c a _ ha =>
    obtain ⟨a', ha', hda⟩ := ha
    refine ⟨c • a', Submodule.smul_mem _ c ha', fun x => ?_⟩
    have e : (fun t : ℝ => M.co.rho ψ (realAd F t • u) (c • a) x) =
        fun t => c * M.co.rho ψ (realAd F t • u) a x := by
      funext t; simp [Darboux.rho, schr]; ring
    rw [e]
    simpa using (hda x).const_mul c
  | mem Φ hΦ =>
    obtain ⟨g, φ, hg, hSB, hev, rfl⟩ := hΦ
    obtain ⟨g₁, hg₁, hA⟩ := exists_actsD_mem_Pol M ψ emb hψ u hu g hg
    have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hev.and hM.std).mono fun v hv => hv.1.trans hv.2
    refine ⟨pure g₁ φ, Submodule.subset_span ⟨g₁, φ, hg₁, hSB, hev, rfl⟩, fun x => ?_⟩
    exact hA _ (GlobalTheory.ThK.EvUniqInf.rest_pure g φ hSB hstd) x

end Model

end GlobalTheory.SquareAgree.HeisDeriv

namespace GlobalTheory.SquareAgree.HeisDeriv

theorem heisDeriv_algD : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∀ f : WO S X → ℂ, IsDatum M ψ cS ΦD f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
        ∃ ΦD' ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD' (dRho (heisO ψ (sgn ε S) X) θ τ z f) := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS ΦD hΦD f hf τ z
  subst hψ
  obtain ⟨hline, hAt⟩ := GlobalTheory.T.archimedeanLine_eq_realScalar_smul_supported D θ hθ τ z
  have hsm : ∀ (a : AF D.host.F) (u : Matrix (Fin S.rank) (Fin d) (AE D)), cS (a • u) = a • cS u := by
    intro a u
    rw [hcS, hcS]
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, Finset.smul_sum,
      smul_mul_assoc, id]
  set w₀ := lineAt θ τ z 1 with hw₀
  set u := cS.symm w₀ with hu_def
  have hcu : cS u = w₀ := cS.apply_symm_apply w₀
  have hu : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u := by
    intro a ha
    apply cS.injective
    rw [hsm, hcu, map_zero]
    exact hAt a ha
  have hLt : ∀ t : ℝ, cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u) = lineAt θ τ z t := by
    intro t
    rw [hsm, hcu, hline t]
  have hstd := hBs.std
  obtain ⟨Φ', hΦ', hder⟩ := exists_deriv_algD M Bs.ψ Bs.emb hstd hM u hu ΦD hΦD
  refine ⟨Φ', hΦ', algD_le_schA M Bs.ψ Bs.emb hM hΦ', fun u' => ?_⟩
  have h2 : ⅟(2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    simp
  have key : ∀ t : ℝ, GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u' (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u) ΦD)) =
      heisO Bs.ψ (sgn ε S) X (lineAt θ τ z t) f (cS u') := by
    intro t
    rw [rho_rho, thetaSum_smul, hf.2, map_add, ← hLt t, heisO, symplOH, ← GlobalTheory.T.schrodingerModel_symplectic_eq_orientedPair D ε S X e Vs Ws hJ hJW cS hcS, h2]
  have hd := GlobalTheory.T.hasDerivAt_thetaSum_heisenbergLine M.co Bs.ψ hstd u hu ΦD (algD_le_schA M Bs.ψ Bs.emb hM hΦD) Φ' (algD_le_schA M Bs.ψ Bs.emb hM hΦ')
    hder u'
  simp only [key] at hd
  exact hd.deriv.symm

end GlobalTheory.SquareAgree.HeisDeriv

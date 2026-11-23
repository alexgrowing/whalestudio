import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.EquivIoYOf
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ThetaFinsetSum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.KerDiag

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def OmFinDRho (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsStdChar D ψ (-1) → IsInfFam θ →
    IsWeilDatumO ψ S T χS χT om → ∀ κ ∈ GfC S, ∀ κ' ∈ GfC T, ∀ (τ : D.what₂.Tau)
      (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f →
      om (κ, κ') (Datum.dRho (heisO ψ S T) θ τ z f) = Datum.dRho (heisO ψ S T) θ τ z (om (κ, κ') f)

section Gen

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem dRho_smul (θ : InfFam D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (c : ℂ)
    (g : WO S T → ℂ) : Datum.dRho (heisO ψ S T) θ τ z (c • g) = c • Datum.dRho (heisO ψ S T) θ τ z g := by
  unfold Formalism.IndefR.Datum.dRho
  funext x
  have hx : ∀ t, heisO ψ S T ((lineAt θ τ z) t) (c • g) x = c * heisO ψ S T ((lineAt θ τ z) t) g x := by
    intro t
    first
      | (rw [map_smul]; rfl)
      | (simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring)
      | (unfold heisO; simp only [Pi.smul_apply, smul_eq_mul]; ring)
      | simp [heisO, mul_left_comm]
  simp only [hx, Pi.smul_apply, smul_eq_mul]
  first
    | exact congrFun (deriv_const_mul_field' c) 0
    | rw [deriv_const_mul_field']
    | done

theorem comm_pureTensorO (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (W : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hW : ∀ τ z g, IsThetaFunO ψ S T g → W (Datum.dRho (heisO ψ S T) θ τ z g) = Datum.dRho (heisO ψ S T) θ τ z (W g))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    W (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (W f) P := by
  have hs := Formalism.IndefR.Fin.dRhoStable D ψ θ hψ hθ S T
  have hsub : ∀ u w : WO S T → ℂ, IsThetaFunO ψ S T u → IsThetaFunO ψ S T w →
      IsThetaFunO ψ S T (u - Complex.I • w) := by
    intro u w hu hw
    have h2 := Formalism.IndefR.Fock.CCR.theta_function_linear_combination hu hw 1 (-Complex.I)
    rwa [one_smul, neg_smul, ← sub_eq_add_neg] at h2
  have hsm : ∀ (r : ℂ) (u : WO S T → ℂ), IsThetaFunO ψ S T u → IsThetaFunO ψ S T (r • u) := by
    intro r u hu
    have h2 := Formalism.IndefR.Fock.CCR.theta_function_linear_combination hu hu r 0
    rwa [zero_smul, add_zero] at h2
  have hsmR : ∀ (r : ℝ) (u : WO S T → ℂ), IsThetaFunO ψ S T u → IsThetaFunO ψ S T (r • u) := by
    intro r u hu
    have h2 := hsm (r : ℂ) u hu
    rwa [Complex.coe_smul] at h2
  have hAθ : ∀ x g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT x g) := by
    intro x g hg
    unfold aPlusAll aPlus crea
    first
      | exact hsm _ _ (hsub _ _ (hs _ _ _ hg) (hs _ _ _ hg))
      | exact hsmR _ _ (hsub _ _ (hs _ _ _ hg) (hs _ _ _ hg))
  have hAW : ∀ x g, IsThetaFunO ψ S T g → W (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT x g) = aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT x (W g) := by
    intro x g hg
    unfold aPlusAll aPlus crea
    first
      | rw [map_smul, map_sub, map_smul, hW _ _ _ hg, hW _ _ _ hg]
      | rw [LinearMap.map_smul_of_tower, map_sub, map_smul, hW _ _ _ hg, hW _ _ _ hg]
  unfold Formalism.IndefR.Datum.pureTensorO
  generalize aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT = A at hAθ hAW ⊢
  unfold pureTensorL
  have hL : ∀ L : List (FVar D T.rank S.rank), IsThetaFunO ψ S T (List.foldr (fun i g => A i g) f L) ∧
      W (List.foldr (fun i g => A i g) f L) = List.foldr (fun i g => A i g) (W f) L := by
    intro L
    induction L with
    | nil => exact ⟨hf, rfl⟩
    | cons i L ih =>
      refine ⟨?_, ?_⟩
      · simp only [List.foldr_cons]
        exact hAθ _ _ ih.1
      · simp only [List.foldr_cons]
        rw [hAW _ _ ih.1, ih.2]
  have hO : ∀ m, W (opPow A m f) = opPow A m (W f) := by
    intro m
    unfold opPow
    exact (hL _).2
  first
    | (rw [show (fun m => opPow A m (W f)) = W ∘ (fun m => opPow A m f) from funext fun m => (hO m).symm]
       first
         | (rw [Module.Basis.constr_comp] <;> rfl)
         | (rw [Basis.constr_comp] <;> rfl))
    | (simp only [← hO]
       rw [show (fun m => W (opPow A m f)) = W ∘ (fun m => opPow A m f) from rfl]
       first
         | (rw [Module.Basis.constr_comp] <;> rfl)
         | (rw [Basis.constr_comp] <;> rfl))

theorem pureTensorO_smul (θ : InfFam D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (c : ℂ) (f : WO S T → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (c • f) P = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  have hA : ∀ x (g : WO S T → ℂ), aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT x (c • g) = c • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT x g := by
    intro x g
    unfold aPlusAll aPlus crea
    rw [dRho_smul, dRho_smul]
    first
      | module
      | rw [smul_comm Complex.I c, ← smul_sub, smul_comm]
      | (simp only [smul_sub, smul_smul]; ring_nf)
  unfold Formalism.IndefR.Datum.pureTensorO
  generalize aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT = A at hA ⊢
  unfold pureTensorL
  have hO : ∀ m, opPow A m (c • f) = c • opPow A m f := by
    intro m
    unfold opPow
    generalize (Finsupp.toMultiset m).toList = L
    induction L with
    | nil => rfl
    | cons i L ih => simp only [List.foldr_cons, ih, hA]
  first
    | rw [show (fun m => opPow A m (c • f)) = c • (fun m => opPow A m f) from funext fun m => hO m,
        map_smul, LinearMap.smul_apply]
    | (simp only [hO]
       rw [show (fun m => c • opPow A m f) = c • (fun m => opPow A m f) from rfl, map_smul, LinearMap.smul_apply])

end Gen

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def VecDiagY : Prop :=
  ∀ t k, k + 1 < D.R.m →
    ∀ κS ∈ levG (Yc D k) (R.βY k) (flagL (R.datYt t k R.triv)),
    ∀ κT ∈ levG (Yc D (k + 1)) (R.βY (k + 1)) (flagL (R.datYt t (k + 1) R.triv)),
      rTup (R.βY k) (R.datYt t k R.triv) (finE (Yc D k) κS) =
          rTup (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) (finE (Yc D (k + 1)) κT) →
        R.ωY t k (κS, κT) (R.vY t k) =
          (levChi (Yc D k) (R.βY k) (flagL (R.datYt t k R.triv)) κS *
            (levChi (Yc D (k + 1)) (R.βY (k + 1)) (flagL (R.datYt t (k + 1) R.triv)) κT)⁻¹) • R.vY t k

end Formalism.IndefR.Eqv.KerDiag

end

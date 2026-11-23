import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.ExistsAlpha
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.NuPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.BcTens
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.SmoothModelFiniteLengthLink
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.LsSeqEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfLseqFirstStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitDivisibleOfVanishingLevelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleFiniteLimitOfLseqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedCokernelLimitToLevelStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace CrystallineSemistableComparison.Pb

set_option maxHeartbeats 1000000

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K)

def sT (M : Model l K) (j : ℕ) : Sys.{1} (AW r) := HMS r M j

def sH (M : Model l K) (j : ℕ) : Sys.{1} (AW r) := M.HS true j

def gH (M : Model l K) (j : ℕ) : Sys.Hom (HSW r M j) (sT r M j) (algebraMap (WittVector l r.k) (AW r)) :=
  ⟨fun n => bW r M n j, fun n y => bW_red r M n j y⟩

def ψA (N : ℕ) : AW r →+* AW r := Mid.phiA l N

variable {N : ℕ} (hT : Mid.TeichmullerCongruence r N)

def nuH (M : Model l K) (j : ℕ) : Sys.Hom (sH r M j) (sT r M j) (ψA r N) := ⟨fun n => Mid.nu r M n j hT, fun n x => nu_red r hT M n j x⟩

def muH (M : Model l K) (j : ℕ) : Sys.Hom (sT r M j) (sH r M j) (RingHom.id _) := ⟨fun n => Mid.mu r M n j hT, fun n x => mu_red r hT M n j x⟩

theorem lw_fin (M : Model l K) (hM : M.Sm) (j : ℕ) : Module.Finite (WittVector l r.k) (HSW r M j).lim := by
  obtain ⟨E⟩ := LsG.ls_seq r M hM j
  exact GlobalTheory.T.module_finite_limit_of_lseq _ l _ _ E (smooth_model_finite_length_link r M hM j)

theorem pin_all (M : Model l K) (j : ℕ) : ∃ (e : ℕ) (α : (sH r M j).lim →+ AW r ⊗[WittVector l r.k] (HSW r M j).lim),
    M.Sm → Fa.Pin l (gH r M j) (nuH r hT M j) e α := by
  by_cases hM : M.Sm
  swap
  · exact ⟨0, 0, fun h => absurd h hM⟩
  obtain ⟨E⟩ := LsG.ls_seq r M hM j
  have ha : ∀ n, IsArtinian (WittVector l r.k) ((HSW r M j).M n) := fun n =>
    (isFiniteLength_iff_isNoetherian_isArtinian.1 (GlobalTheory.T.finite_length_of_lseq_first _ l _ _ E (smooth_model_finite_length_link r M hM j) n)).2
  obtain ⟨c, hc⟩ := GlobalTheory.T.bounded_cokernel_limit_to_level _ l _ _ E ha (lw_fin r M hM (j + 1))
  have := flatW r
  have : IsAdicComplete (Ideal.span {(l : AW r)}) (AW r) := adicA
  obtain ⟨α, hα⟩ := Fa.pin_ex l (WittVector.irreducible l) c (lw_fin r M hM j) E.kill (GlobalTheory.T.limit_divisible_of_vanishing_level _ l _ _ E ha) hc (gH r M j)
    (bc_tens r M hM j) (nuH r hT M j)
  exact ⟨c, α, fun _ => hα⟩

theorem iter_lim {R : Type} [CommRing R] {S : Sys.{1} R} {σ : R →+* R} (φ : Sys.Hom S S σ) (N n : ℕ) (x : S.lim) :
    ((⇑φ.lim.toAddMonoidHom)^[N] x).1 n = (⇑(φ.f n))^[N] (x.1 n) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

def betaP (M : Model l K) (j : ℕ) : AL r M j →ₗ[(per l K).A] HL M j where
  toFun w := Fa.beta (A := AW r) (gH r M j) (muH r hT M j) w
  map_add' := (Fa.beta (A := AW r) (gH r M j) (muH r hT M j)).map_add
  map_smul' a w := (Fa.beta (A := AW r) (gH r M j) (muH r hT M j)).map_smul (ofA r a) w

theorem phiA_iter (N : ℕ) (a : Acris l) : Mid.phiA l N a = (ACris.phi ℂ_[l] l)^[N] a := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Mid.phiA_succ, Function.iterate_succ_apply', ih]

def φA : AW r →+* AW r := ACris.phi ℂ_[l] l

def σA (σ : Gal(PadicAlgCl l/K)) : AW r →+* AW r := ACris.galCris σ

def Pinned (F : Fac r N) : Prop := ∀ M : Model l K, M.Sm → ∀ j, Fa.Pin l (gH r M j) (nuH r hT M j) (F.e M j) (F.α M j) ∧
  ∀ w, F.β M j w = Fa.beta (gH r M j) (muH r hT M j) w

def MuNu : Prop := ∀ (M : Model l K) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true n j),
  Mid.mu r M n j hT (Mid.nu r M n j hT x) = (⇑(B.phiHc (B.schFn M.p) (okToOC l K) n j))^[N] x

theorem fac_ex (hmn : MuNu r hT) (hφ : ∀ w, ACris.phi ℂ_[l] l (r.w w) = r.w (WittVector.frobenius w))
    (hσ : ∀ (g : K.fixingSubgroup) w, ACris.galCris (IntermediateField.fixingSubgroupEquiv K g) (r.w w) = r.w w) :
    ∃ F : Fac r N, Pinned r hT F := by
  choose e α h using pin_all r hT
  refine ⟨{ e := e
            α := α
            β := betaP r hT
            phiT := fun M j => Fa.tmap (A := AW r) (φA r) (Wc.phiS l (B.schFn M.p) r.ρ j).lim hφ
            galT := fun M j g => Fa.tmap (A := AW r) (σA r (IntermediateField.fixingSubgroupEquiv K g)) (τW := RingHom.id _) LinearMap.id (hσ g)
            phiT_tmul := fun _ _ _ _ _ => rfl
            galT_tmul := fun _ _ _ _ _ _ => rfl
            lin := ?_, fac := ?_, phi := ?_, gal := ?_, galβ := ?_, nat := ?_ }, fun M hM j => ⟨h M j hM, fun _ => rfl⟩⟩
  · intro M hM j a x
    exact ((h M j hM).lin a x).trans (congrArg (fun b : AW r => b • α M j x) (phiA_iter N a))
  · intro M hM j x
    exact (h M j hM).fac (muH r hT M j) x _ fun n => (hmn M n j _).trans (iter_lim (M.phiH j) N n x).symm
  · intro M hM j x
    exact ((h M j hM).op (h M j hM) (τ := φA r) (fun n => phiM r M n j) (Wc.phiS l (B.schFn M.p) r.ρ j).lim
      (fun n y => (bW_phi r M n j _).symm) _ (fun _ _ => rfl) x (phiL M j x) fun n => nu_phi r hT M n j _).2 rfl
  · intro M hM j g x
    exact ((h M j hM).op (h M j hM) (τ := σA r (IntermediateField.fixingSubgroupEquiv K g)) (fun n => galM r M _ (hσ g) n j) id
      (fun n y => (bW_gal r M _ (hσ g) n j _).symm) _ (fun _ _ => rfl) x (galL M j g x) fun n => nu_gal r hT M _ (hσ g) n j _).2 rfl
  · intro M hM j g y
    refine Subtype.ext (funext fun n => (mu_gal r hT M _ (hσ g) n j _).trans (congrArg (Mid.mu r M n j hT) ?_))
    have e1 : Fa.E (gH r M j) n ((1 : AW r) ⊗ₜ y) = bW r M n j (y.1 n) := (Fa.E_tmul _ n 1 y).trans (one_smul _ _)
    exact (congrArg (galM r M _ (hσ g) n j) e1).trans ((bW_gal r M _ (hσ g) n j _).trans e1.symm)
  · intro M M' u hu hM hM' j x
    refine ⟨0, ?_⟩
    rw [pow_zero, one_smul, sub_eq_zero]
    exact ((h M' j hM').op (h M j hM) (τ := RingHom.id _) (fun n => pullM r u hu n j) (Wc.pullS l r.ρ (B.schMap u hu) j).lim
      (fun n y => (bW_pull r u hu n j _).symm) (LinearMap.lTensor (AW r) (Wc.pullS l r.ρ (B.schMap u hu) j).lim).toAddMonoidHom
      (fun _ _ => rfl) x (pullL u hu j x) fun n => nu_pull r hT u hu n j _).1

end CrystallineSemistableComparison.Pb

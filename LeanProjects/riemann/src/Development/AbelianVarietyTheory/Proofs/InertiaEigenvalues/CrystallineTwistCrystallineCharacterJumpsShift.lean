import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysIffOfTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBcrisBasicTheoremsProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrankStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsJumpVOfInjective

noncomputable section

namespace GlobalTheory.TwistRepCrys

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem finrank_fildR_of_equiv {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    finrank LL (FildR PD ρ τ a) = finrank LL (FildR PD ρ' τ a) := by
  rw [GlobalTheory.HTW.FildR_eq_comap PD ρ ρ' e.toLinearMap e.injective he τ a]
  exact (LinearEquiv.ofSubmodule'
    (AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)) (FildR PD ρ' τ a)).finrank_eq

theorem multV_of_equiv {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    multV PD ρ τ a = multV PD ρ' τ a := by
  rw [multV, multV, finrank_fildR_of_equiv PD e he, finrank_fildR_of_equiv PD e he]

theorem multV_of_le_one (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    [FiniteDimensional LL (DdRE PD ρ τ)] (h1 : finrank LL (DdRE PD ρ τ) ≤ 1) {b : ℤ}
    (hb : IsJumpV PD ρ τ b) (a : ℤ) : multV PD ρ τ a = if a = b then 1 else 0 := by
  haveI : ∀ a, FiniteDimensional LL (FildR PD ρ τ a) := fun a =>
    Submodule.finiteDimensional_of_le (S₂ := DdRE PD ρ τ) inf_le_left
  have anti : Antitone (FildR PD ρ τ) := fun a a' haa =>
    inf_le_inf_left _ (GlobalTheory.Cmp.SmallJumps.filV_anti PD haa)
  have mono : ∀ a a', a ≤ a' → finrank LL (FildR PD ρ τ a') ≤ finrank LL (FildR PD ρ τ a) :=
    fun a a' h => Submodule.finrank_mono (anti h)
  have le1 : ∀ a, finrank LL (FildR PD ρ τ a) ≤ 1 := fun a =>
    (Submodule.finrank_mono (inf_le_left : FildR PD ρ τ a ≤ DdRE PD ρ τ)).trans h1
  have lt : finrank LL (FildR PD ρ τ (b + 1)) < finrank LL (FildR PD ρ τ b) :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (anti (by omega)) hb)
  have := le1 a
  have := le1 b
  rw [multV]
  rcases lt_trichotomy a b with h | h | h
  · have := mono (a + 1) b (by omega)
    have := mono a (a + 1) (by omega)
    rw [if_neg h.ne]
    omega
  · subst h
    rw [if_pos rfl]
    omega
  · have := mono (b + 1) a (by omega)
    have := mono a (a + 1) (by omega)
    rw [if_neg h.ne']
    omega

def transport (e : V ≃ₗ[LL] V') (ρ' : Representation LL G V') : Representation LL G V where
  toFun g := e.symm.toLinearMap ∘ₗ ρ' g ∘ₗ e.toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

omit [Module Qp V] [IsScalarTower Qp LL V] [Module Qp V'] [IsScalarTower Qp LL V'] in
theorem transport_apply (e : V ≃ₗ[LL] V') (ρ' : Representation LL G V') (g : G) (x : V) :
    e (transport e ρ' g x) = ρ' g (e x) := by
  simp [transport]

end Generic

theorem isCrys_and_multV_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (χ : ↥(GK K) →* (↥LL.1)ˣ), IsTwistRep χ ρ ρ' → IsCrys (P.PD K) (charRep χ) → IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ' ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a b : ℤ), IsJumpV (P.PD K) (charRep χ) τ b → multV (P.PD K) ρ' τ (a + b) = multV (P.PD K) ρ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' χ ⟨e, he⟩ cχ cρ
  let f : (Fin 1 → ↥LL.1) ≃ₗ[↥LL.1] ↥LL.1 := LinearEquiv.funUnique (Fin 1) ↥LL.1 ↥LL.1
  let ν := transport f (charRep χ)
  have hν : ∀ g x, ν g x = ((χ g : (↥LL.1)ˣ) : ↥LL.1) • x := fun g x => by
    apply f.injective
    rw [transport_apply, map_smul]
    rfl
  have hρ : ∀ g x, transport e ρ' g x = ((χ g : (↥LL.1)ˣ) : ↥LL.1) • ρ g x := fun g x => by
    apply e.injective
    rw [transport_apply, he, map_smul]
  have cν : IsCrys (P.PD K) ν :=
    GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD K) f.symm (fun g x => by
      apply f.injective
      rw [transport_apply, f.apply_symm_apply, f.apply_symm_apply]) cχ
  refine ⟨GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD K) e (transport_apply e ρ')
    ((GlobalTheory.TwistCrys.isCrys_iff_of_twist GlobalTheory.MemLoc.fontaineBcris l P AI T K LL V ρ _ ν _ hν hρ cν).1 cρ),
    fun τ a b hb => ?_⟩
  obtain ⟨hfin, hle, -⟩ := (GlobalTheory.T.deRhamComponents_crystallineLetters_finrank l P AI T K LL ↥LL.1 (charRep χ)).1 τ
  rw [finrank_self] at hle
  rw [← multV_of_equiv (P.PD K) e (transport_apply e ρ')]
  refine GlobalTheory.TwistJump.multV_twist_char l P AI T K LL V ρ _ ν _ hν hρ
    (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K LL _ ν cν).1 τ b (fun c => ?_) a
  rw [multV_of_equiv (P.PD K) f (transport_apply f (charRep χ))]
  exact multV_of_le_one (P.PD K) (charRep χ) τ hle hb c

end GlobalTheory.TwistRepCrys

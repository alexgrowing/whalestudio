import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankPeriodFunctorCoeffBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExtEmbeddingSplitting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepresentationHomFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqOfExhaustive

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateDualFil

section Linear

variable {G : Type} [Group G] {LL : Type} [Field LL] (L : Type) [Field L] [Algebra LL L]
  {V : Type} [AddCommGroup V] [Module LL V] {V' : Type} [AddCommGroup V'] [Module LL V']

def extRep (ρ : Representation LL G V) : Representation L G (L ⊗[LL] V) where
  toFun g := (ρ g).baseChange L
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one _ _
  map_mul' g h := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

theorem extRep_tmul (ρ : Representation LL G V) (g : G) (a : L) (x : V) :
    extRep L ρ g (a ⊗ₜ[LL] x) = a ⊗ₜ[LL] ρ g x := rfl

theorem exists_ext_pairing [FiniteDimensional LL V] (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (hm : Function.Bijective m.flip) :
    ∃ m' : L ⊗[LL] V →ₗ[L] L ⊗[LL] V' →ₗ[L] L, Function.Bijective m' ∧
      ∀ (a b : L) x y, m' (a ⊗ₜ[LL] x) (b ⊗ₜ[LL] y) = a * b * algebraMap LL L (m x y) := by
  obtain ⟨v, w, hvw⟩ := GlobalTheory.DRFil.exists_dual_bases m hm
  let v' := Algebra.TensorProduct.basis L v
  let w' := Algebra.TensorProduct.basis L w
  let e := v'.equiv w'.dualBasis (Equiv.refl _)
  refine ⟨e.toLinearMap, e.bijective, fun a b x y => ?_⟩
  have h1 : ∀ i, e.toLinearMap (a ⊗ₜ[LL] v i) (b ⊗ₜ[LL] y) = a * b * algebraMap LL L (m (v i) y) := by
    intro i
    have h2 : a ⊗ₜ[LL] v i = a • v' i := by
      simp [v', Algebra.TensorProduct.basis_apply, smul_tmul']
    have h3 : m (v i) y = w.repr y i := by
      conv_lhs => rw [← w.sum_repr y]
      simp only [map_sum, map_smul, hvw, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    rw [h2, map_smul, h3]
    simp only [e, LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply, LinearMap.smul_apply,
      Basis.dualBasis_apply, w', Algebra.TensorProduct.basis_repr_tmul]
    simp [mul_assoc]
  rw [← v.sum_repr x, tmul_sum, map_sum, map_sum, LinearMap.sum_apply, LinearMap.sum_apply, map_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h4 : a ⊗ₜ[LL] (v.repr x i • v i) = algebraMap LL L (v.repr x i) • (a ⊗ₜ[LL] v i) := by
    rw [algebraMap_smul, tmul_smul]
  rw [h4, map_smul, LinearMap.smul_apply, h1, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
    map_mul]
  ring

end Linear

theorem exists_eq_bot {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (D : Submodule k M) [FiniteDimensional k D] (F : ℤ → Submodule k M) (hF : Antitone F)
    (hle : ∀ a, F a ≤ D) (hsep : ∀ x, (∀ a, x ∈ F a) → x = 0) : ∃ b : ℤ, ∀ a, b ≤ a → F a = ⊥ := by
  have hfin : ∀ a, FiniteDimensional k (F a) := fun a => Submodule.finiteDimensional_of_le (hle a)
  obtain ⟨b, hb⟩ : ∃ b : ℤ, ∀ a, finrank k (F b) ≤ finrank k (F a) :=
    ⟨Function.argmin fun a => finrank k (F a), fun a => Function.argmin_le (fun a => finrank k (F a)) a⟩
  have h1 : ∀ a, b ≤ a → F a = F b := fun a ha => Submodule.eq_of_le_of_finrank_le (hF ha) (hb a)
  refine ⟨b, fun a ha => ?_⟩
  rw [h1 a ha, eq_bot_iff]
  intro x hx
  refine hsep x fun c => ?_
  rcases le_total b c with h | h
  · rw [h1 c h]; exact hx
  · exact hF h hx

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem finrank_fil_zero_add (ρ : Representation LL G V) (ρ' : Representation LL G V')
    [FiniteDimensional LL ↥(DdR PD ρ)] [FiniteDimensional LL ↥(DdR PD ρ')] (τ : K →ₐ[Qp] LL)
    (h : ∀ a, multV PD ρ' τ (-a - 1) = multV PD ρ τ a) :
    finrank LL ↥(FildR PD ρ' τ 0) + finrank LL ↥(FildR PD ρ τ 0) = finrank LL ↥(DdRE PD ρ τ) := by
  have : FiniteDimensional LL ↥(DdRE PD ρ τ) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  obtain ⟨b, hb⟩ := GlobalTheory.Per.FilCount.exists_eq_of_exhaustive (DdRE PD ρ τ) (FildR PD ρ τ)
    (fun a b hab => inf_le_inf_left _ (GlobalTheory.DRFil.FilV_antitone PD hab)) (fun a => inf_le_left)
    (fun x hx => (GlobalTheory.DRFil.exists_mem_FilV PD (LL := LL) x).imp fun a ha => ⟨hx, ha⟩)
  obtain ⟨c, hc⟩ := exists_eq_bot (DdR PD ρ') (FildR PD ρ' τ)
    (fun a b hab => inf_le_inf_left _ (GlobalTheory.DRFil.FilV_antitone PD hab))
    (fun a => le_trans inf_le_left inf_le_left)
    (fun x hx => GlobalTheory.DRFil.eq_zero_of_forall_mem_FilV PD (LL := LL) x fun a => (hx a).2)
  let s : ℤ → ℕ := fun a => finrank LL ↥(FildR PD ρ' τ (-a)) + finrank LL ↥(FildR PD ρ τ a)
  have hs : ∀ a, s (a + 1) = s a := fun a => by
    have h1 := h a
    unfold multV at h1
    rw [show -a - 1 + 1 = -a by ring, show -a - 1 = -(a + 1) by ring] at h1
    simp only [s]
    omega
  have hs0 : ∀ a, s a = s 0 := fun a => by
    induction a using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [hs, ih]
    | pred n ih => rw [← hs, sub_add_cancel, ih]
  have h2 := hs0 (min b (-c))
  simp only [s] at h2
  rw [hb _ (min_le_left _ _), hc _ (by omega), finrank_bot, zero_add, neg_zero] at h2
  exact h2.symm

theorem descend (L : Type) [Field L] [Algebra Qp L] [Algebra LL L] [IsScalarTower Qp LL L]
    [FiniteDimensional LL L] [FiniteDimensional LL V] [FiniteDimensional LL V']
    (H : ∀ (W : Type) [AddCommGroup W] [Module L W] [Module Qp W] [IsScalarTower Qp L W]
      [FiniteDimensional L W] (σ : Representation L G W)
      (W' : Type) [AddCommGroup W'] [Module L W'] [Module Qp W'] [IsScalarTower Qp L W']
      [FiniteDimensional L W'] (σ' : Representation L G W') (n : W →ₗ[L] W' →ₗ[L] L),
      Function.Bijective n → (∀ g x y, n (σ g x) (σ' g y) = ((cycLL PD L g : Lˣ) : L) * n x y) →
      IsDR PD σ → IsDR PD σ' ∧
        finrank L ↥(DdR PD σ' ⊓ FilV PD (LL := L) (V := W') 0) +
          finrank L ↥(DdR PD σ ⊓ FilV PD (LL := L) (V := W) 0) = finrank L ↥(DdR PD σ))
    (ρ : Representation LL G V) (ρ' : Representation LL G V') (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (h : IsDR PD ρ) (hm : IsDual1 PD ρ ρ' m) :
    IsDR PD ρ' ∧
      finrank LL ↥(DdR PD ρ' ⊓ FilV PD (LL := LL) (V := V') 0) +
        finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0) = finrank LL ↥(DdR PD ρ) := by
  have hbij : Function.Bijective m.flip := by
    have hi : Function.Injective m.flip := (injective_iff_map_eq_zero _).2 fun y hy =>
      hm.2.2.1 y fun x => LinearMap.congr_fun hy x
    refine ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hi⟩
    rw [← hm.2.2.2]
    exact Subspace.dual_finrank_eq.symm
  obtain ⟨m', hm', hm''⟩ := exists_ext_pairing L m hbij
  obtain ⟨a1, -, -, ⟨a2, -⟩, a3, -⟩ := GlobalTheory.T.finrank_periodFunctor_coeff_baseChange PD LL L V (L ⊗[LL] V) ρ (extRep L ρ)
    (TensorProduct.mk LL L V 1) (TensorProduct.isBaseChange LL V L) (fun g x => rfl)
  obtain ⟨b1, -, -, ⟨b2, -⟩, b3, -⟩ := GlobalTheory.T.finrank_periodFunctor_coeff_baseChange PD LL L V' (L ⊗[LL] V') ρ' (extRep L ρ')
    (TensorProduct.mk LL L V' 1) (TensorProduct.isBaseChange LL V' L) (fun g x => rfl)
  have hχ : ∀ g, ((cycLL PD L g : Lˣ) : L) = algebraMap LL L ((cycLL PD LL g : LLˣ) : LL) := fun g =>
    IsScalarTower.algebraMap_apply Qp LL L _
  have hinv : ∀ g x y, m' (extRep L ρ g x) (extRep L ρ' g y) = ((cycLL PD L g : Lˣ) : L) * m' x y := by
    intro g x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', mul_add]
    | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, hy, hy', mul_add]
      | tmul b y =>
        rw [extRep_tmul, extRep_tmul, hm'', hm'', hm.1, map_mul, hχ]
        ring
  have hL : IsDR PD (extRep L ρ) := by
    rw [IsDR, a1, a2]; exact h
  obtain ⟨c1, c2⟩ := H _ (extRep L ρ) _ (extRep L ρ') m' hm' hinv hL
  refine ⟨by rw [IsDR, ← b1, ← b2]; exact c1, ?_⟩
  rw [← a2, ← a3, ← b3, c2]

end Period

theorem tateDual_split (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K L : FinExt l) (hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥L.1) = finrank ℚ_[l] ↥K.1)
    (W : Type) [AddCommGroup W] [Module ↥L.1 W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] ↥L.1 W]
    [FiniteDimensional ↥L.1 W] (σ : Representation ↥L.1 ↥(GK K) W)
    (W' : Type) [AddCommGroup W'] [Module ↥L.1 W'] [Module ℚ_[l] W'] [IsScalarTower ℚ_[l] ↥L.1 W']
    [FiniteDimensional ↥L.1 W'] (σ' : Representation ↥L.1 ↥(GK K) W') (n : W →ₗ[↥L.1] W' →ₗ[↥L.1] ↥L.1)
    (hn : Function.Bijective n)
    (hinv : ∀ g x y, n (σ g x) (σ' g y) = ((cycLL (P.PD K) ↥L.1 g : (↥L.1)ˣ) : ↥L.1) * n x y)
    (h : IsDR (P.PD K) σ) :
    IsDR (P.PD K) σ' ∧
      finrank ↥L.1 ↥(DdR (P.PD K) σ' ⊓ FilV (P.PD K) (LL := ↥L.1) (V := W') 0) +
        finrank ↥L.1 ↥(DdR (P.PD K) σ ⊓ FilV (P.PD K) (LL := ↥L.1) (V := W) 0) =
          finrank ↥L.1 ↥(DdR (P.PD K) σ) := by
  have := K.2
  obtain ⟨c1, c2⟩ := GlobalTheory.DRDual.twisted_dual_deRham l P AI T K L W σ W' σ' n 1 hn
    (fun g x y => by rw [zpow_one]; exact hinv g x y) h
  refine ⟨c1, ?_⟩
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K L W σ).1
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K L W' σ').1
  have hc : Fintype.card (↥K.1 →ₐ[ℚ_[l]] ↥L.1) = finrank ℚ_[l] ↥K.1 := by
    rw [← hcard, Nat.card_eq_fintype_card]
  obtain ⟨d1, d2⟩ := GlobalTheory.DeRhamSplit.finrank_split (P.PD K) hc σ
  obtain ⟨-, d3⟩ := GlobalTheory.DeRhamSplit.finrank_split (P.PD K) hc σ'
  rw [d1, d2, d3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun τ _ =>
    finrank_fil_zero_add (P.PD K) σ σ' τ fun a => c2 τ a hcard

theorem tateDual (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [FiniteDimensional LL V] (ρ : Representation LL ↥(GK K) V)
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL ↥(GK K) V') (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (h : IsDR (P.PD K) ρ) (hm : IsDual1 (P.PD K) ρ ρ' m) :
    IsDR (P.PD K) ρ' ∧
      finrank LL ↥(DdR (P.PD K) ρ' ⊓ FilV (P.PD K) (LL := LL) (V := V') 0) +
        finrank LL ↥(DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := LL) (V := V) 0) =
          finrank LL ↥(DdR (P.PD K) ρ) := by
  obtain ⟨L, ⟨f⟩, hcard, -⟩ := GlobalTheory.exists_finExt_embedding_splitting l K LL
  have := L.2
  letI : Algebra LL ↥L.1 := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] LL ↥L.1 := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  haveI : FiniteDimensional LL ↥L.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] LL ↥L.1
  exact descend (P.PD K) ↥L.1 (tateDual_split l P AI T K L hcard) ρ ρ' m h hm

theorem main : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm8 D := by
  intro D l _ K
  refine ⟨fun LL _ _ _ O _ _ hO A A' m h hm => ?_, fun LL _ _ _ O _ _ hO A A' m h hm => ?_⟩
  · haveI := hO.2.1
    exact (tateDual l (D.loc l) (D.locA l) (D.locT l) K LL A.ρ A'.ρ m h hm).1
  · haveI := hO.2.1
    exact (tateDual l (D.loc l) (D.locA l) (D.locT l) K LL A.ρ A'.ρ m h hm).2

end GlobalTheory.TateDualFil

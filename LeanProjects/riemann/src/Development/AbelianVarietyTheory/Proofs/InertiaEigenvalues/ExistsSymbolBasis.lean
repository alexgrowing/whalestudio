import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFamilyAdaptedToSeparatedFiltration
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamTensorCoordinatesOfBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamInvariantsCoordinatesFinrankEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SerreTateLinearIndependentOfWeightwise
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFilGradedSymbolToTateTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateInvariantsTwist

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DeRhamSymbolBasis

open GlobalTheory.DeRhamSymbol

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : ThetaL P AI)

theorem theta_zero : J.θ 0 = 0 := by
  have h := J.θ_add 0 (zero_mem _) 0 (zero_mem _)
  rw [add_zero] at h
  simpa using h

theorem theta_sum {ι : Type} (s : Finset ι) (f : ι → P.R.BdR)
    (hf : ∀ i, f i ∈ (P.PD (botExt l)).Fil 0) : J.θ (∑ i ∈ s, f i) = ∑ i ∈ s, J.θ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using theta_zero J
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      J.θ_add _ (hf a) _ (Submodule.sum_mem _ fun i _ => hf i), ih]

theorem om_mul_mem (c : Om l) {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil 0) :
    algebraMap (Om l) P.R.BdR c * x ∈ (P.PD (botExt l)).Fil 0 := by
  simpa using (P.PD (botExt l)).Fil_mul _ _ _ _ (om_mem c) hx

theorem theta_comb {n : ℕ} (c : Fin n → Om l) (f : Fin n → P.R.BdR)
    (hf : ∀ i, f i ∈ (P.PD (botExt l)).Fil 0) :
    J.θ (∑ i, algebraMap (Om l) P.R.BdR (c i) * f i) = ∑ i, (c i : PadicComplex l) * J.θ (f i) := by
  rw [theta_sum J _ _ fun i => om_mul_mem (c i) (hf i)]
  exact Finset.sum_congr rfl fun i _ => by rw [J.θ_mul _ (om_mem _) _ (hf i), J.θ_Om]

omit J in
theorem shift_act (a : ℤ) (g : GQ l) (x : P.R.BdR) :
    ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * P.actQdR g x =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) *
        P.actQdR g (((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x) := by
  rw [map_mul, DeRhamSymbol.act_zpow, ← mul_assoc, ← mul_assoc,
    ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
    map_one, one_mul]

omit J in
theorem exists_adapted {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (b : Module.Basis (Fin d) Qp V)
    (hL : FiniteDimensional Qp LL) (hV : FiniteDimensional LL V) (hDR : IsDR PD ρ) :
    ∃ (x : Fin d → Fin d → BdR) (u : Fin d → ℤ), (∀ k, (∀ g : G, (Matrix.of fun i j =>
      algebraMap Qp BdR (b.repr (ρ g (b j)) i)).mulVec (fun i => PD.actdR g (x k i)) = x k) ∧
      ∀ i, x k i ∈ PD.Fil (u k)) ∧ ∀ (a : ℤ) (c : Fin d → K), (∀ k, u k ≠ a → c k = 0) →
      (∀ i, ∑ k, algebraMap K BdR (c k) * x k i ∈ PD.Fil (a + 1)) → ∀ k, c k = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨Fin.elim0, Fin.elim0, fun k => k.elim0, fun _ _ _ _ k => k.elim0⟩
  haveI : Nontrivial V := ⟨⟨b ⟨0, hd⟩, 0, b.ne_zero _⟩⟩
  haveI := PD.finK
  have hfin : Module.Finite LL ↥(DdR PD ρ) := by
    apply Module.finite_of_finrank_pos
    rw [hDR]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  obtain ⟨Φ, -, hΦ⟩ := GlobalTheory.exists_coord_tensor_dR PD ρ b
  obtain ⟨D, hD, hDf, hDr⟩ := GlobalTheory.deRham_invariants_coord_finrank PD ρ b hL hfin hDR Φ hΦ
  obtain ⟨x, u, hx, hind⟩ := GlobalTheory.exists_family_adapted_filtration K (Fin d → BdR) D
    (fun a => Submodule.pi Set.univ fun _ => PD.Fil a) d hDf hDr
    (fun a z hz i hi => PD.Fil_anti a (hz i hi))
    (fun z => by
      have anti : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti
      choose f hf using fun i => PD.Fil_exh (z i)
      obtain ⟨m, hm⟩ := (Set.finite_range f).bddBelow
      exact ⟨m, fun i _ => anti (hm ⟨i, rfl⟩) (hf i)⟩)
    (fun z hz => funext fun i => PD.Fil_sep _ fun a => hz a i trivial)
  refine ⟨x, u, fun k => ⟨(hD _).1 (hx k).1, fun i => (hx k).2 i trivial⟩, fun a c hc hs => ?_⟩
  refine hind a c hc fun i _ => ?_
  have := hs i
  simp only [← Algebra.smul_def] at this
  simpa only [Finset.sum_apply, Pi.smul_apply, SetLike.mem_coe] using this

omit J in
theorem sum_mem_DdR {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (b : Module.Basis (Fin d) Qp V) (x : Fin d → BdR)
    (hx : ∀ g : G, (Matrix.of fun i j =>
      algebraMap Qp BdR (b.repr (ρ g (b j)) i)).mulVec (fun i => PD.actdR g (x i)) = x) :
    ∑ i, b i ⊗ₜ[Qp] x i ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]
  intro g
  have hact : ∀ (v : V) (y : BdR),
      actVdR PD ρ g (v ⊗ₜ y) = ρ g v ⊗ₜ PD.actdR g y := by
    intro v y
    unfold actVdR
    rw [TensorProduct.AlgebraTensorModule.map_tmul]
    rfl
  obtain ⟨Φ, h, -⟩ := GlobalTheory.exists_tensor_coord_of_basis (M := BdR) b
  apply Φ.injective
  funext i
  rw [map_sum, map_sum, map_sum, Finset.sum_apply, Finset.sum_apply]
  simp only [hact, h, Module.Basis.repr_self]
  have h1 := congrFun (hx g) i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ← Algebra.smul_def] at h1
  rw [h1, Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    simp [Finsupp.single_apply, hij]
  · simp

omit J in

theorem exists_symbol_basis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (θ : ThetaL P AI) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsDR (P.PD K) T.ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℚ_[l] T.V) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)), (∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (b.repr (T.ρ g (b j)) i)) → ∀ t : (P.R.BdR)ˣ, (t : P.R.BdR) = P.ιB P.tB → ∃ (u : Fin d → ℤ) (y : Fin d → Fin d → P.R.BdR), (∀ k i, y k i ∈ (P.PD K).Fil 0) ∧ (∀ k, ∑ i, b i ⊗ₜ[ℚ_[l]] (y k i * ((t ^ u k : (P.R.BdR)ˣ) : P.R.BdR)) ∈ DdR (P.PD K) T.ρ) ∧ LinearIndependent (PadicComplex l) (fun k i => θ.θ (y k i)) ∧ ∀ σ ∈ GK K, ∀ k, twAct AI.actC P.χQ (u k) M σ (fun i => θ.θ (y k i)) = fun i => θ.θ (y k i) := by
  intro l _ P AI J K LL T hDR d b M hM t ht
  obtain rfl : t = tU P := Units.ext ht
  obtain ⟨x, u, hx, hind⟩ := exists_adapted (P.PD K) T.ρ b LL.2 T.fdim hDR
  have key : ∀ k i, ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i ∈ (P.PD (botExt l)).Fil 0 :=
    fun k i => (shift_iff J (u k) 0 _).2 (by
      rw [add_zero]; exact (mem_iff K _ _).1 ((hx k).2 i))
  have heq : ∀ σ ∈ GK K, ∀ k, twAct AI.actC P.χQ (u k) M σ
      (fun i => J.θ (((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i)) =
      fun i => J.θ (((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i) := by
    intro σ hσ k
    funext i
    generalize hN : (fun i j => b.repr (T.ρ ⟨σ, hσ⟩ (b j)) i : Fin d → Fin d → ℚ_[l]) = N
    have hN' : ∀ i j, b.repr (T.ρ ⟨σ, hσ⟩ (b j)) i = N i j := fun i j => congrFun (congrFun hN i) j
    have h1 := congrFun ((hx k).1 ⟨σ, hσ⟩) i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, P.PD_actdR, hN'] at h1
    have h2 : ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i =
        ∑ j, algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l)
          (((P.χQ σ ^ u k : ℚ_[l]ˣ) : ℚ_[l]) * N i j)) *
          P.actQdR σ (((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k j) := by
      conv_lhs => rw [← h1]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, shift_act, ← IsScalarTower.algebraMap_apply,
        map_mul (algebraMap ℚ_[l] P.R.BdR), mul_left_comm, mul_assoc]
    conv_rhs => rw [h2, theta_comb J _ _ fun j => act_mem σ (key k j)]
    simp only [twAct, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [J.θ_act σ _ (key k j), hM ⟨σ, hσ⟩ i j, hN', ← mul_assoc, chiC, ← map_mul]
    rfl
  refine ⟨u, fun k i => ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i,
    fun k i => (mem_iff K _ _).2 (key k i), fun k => ?_, ?_, heq⟩
  · have : ∀ i, ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i *
        ((tU P ^ u k : P.R.BdRˣ) : P.R.BdR) = x k i := fun i => by
      rw [mul_right_comm, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
        one_mul]
    simp only [this]
    exact sum_mem_DdR (P.PD K) T.ρ b _ (hx k).1
  · refine GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise l AI.actC P.χQ (GK K) K.1
      (tate_invariants_twist l AI.actC P.χQ ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K) d d M _ u heq ?_
    intro a c hc hs
    refine hind a c hc fun i => ?_
    have h1 := congrFun hs i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    rw [← theta_comb J (fun k => ((c k : ↥K.1) : Om l)) _ (fun k => key k i),
      J.θ_ker _ (Submodule.sum_mem _ fun k _ => om_mul_mem _ (key k i))] at h1
    rw [mem_iff K, ← shift_iff J, Finset.mul_sum]
    convert h1 using 2 with k
    by_cases hk : u k = a
    · rw [hk, mul_left_comm]
      rfl
    · simp [hc k hk]

end GlobalTheory.DeRhamSymbolBasis

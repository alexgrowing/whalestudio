import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFilGradedSymbolToTateTwist

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EmbeddingJump

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mulVdR_tmul (c : K) (v : V) (z : BdR) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (Qp := Qp) c (v ⊗ₜ[Qp] z) =
      v ⊗ₜ[Qp] (algebraMap K BdR c * z) := by
  simp [mulVdR]

theorem act_mul (g : G) (c : K) (x : V ⊗[Qp] BdR) :
    actVdR PD ρ g (mulVdR (K := K) (LL := LL) c x) = mulVdR (K := K) (LL := LL) c (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v z => simp [mulVdR, actVdR]

theorem mul_mem_DdR (c : K) {x : V ⊗[Qp] BdR} (hx : x ∈ DdR PD ρ) :
    mulVdR (K := K) (LL := LL) c x ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  rw [act_mul, hx g]

theorem tmul_mem_FilV (a : ℤ) (v : V) {z : BdR} (hz : z ∈ PD.Fil a) :
    v ⊗ₜ[Qp] z ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨v ⊗ₜ[Qp] ⟨z, hz⟩, by simp⟩

theorem mul_mem_FilV (a : ℤ) (c : K) {x : V ⊗[Qp] BdR} (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    mulVdR (K := K) (LL := LL) c x ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add]; exact Submodule.add_mem _ hx hy
  | tmul v z =>
    simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply,
      Submodule.subtype_apply]
    rw [mulVdR_tmul, ← Algebra.smul_def]
    exact tmul_mem_FilV PD a v ((PD.Fil a).smul_mem c z.2)

theorem mul_mul (c c' : K) (x : V ⊗[Qp] BdR) :
    mulVdR (K := K) (LL := LL) c (mulVdR (K := K) (LL := LL) c' x) =
      mulVdR (K := K) (LL := LL) (c * c') x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v z => simp only [mulVdR_tmul, map_mul, mul_assoc]

theorem mul_add' (c c' : K) (x : V ⊗[Qp] BdR) :
    mulVdR (K := K) (LL := LL) (c + c') x =
      mulVdR (K := K) (LL := LL) c x + mulVdR (K := K) (LL := LL) c' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | tmul v z => simp only [mulVdR_tmul, map_add, add_mul, TensorProduct.tmul_add]

theorem mul_smul' (r : Qp) (c : K) (x : V ⊗[Qp] BdR) :
    mulVdR (K := K) (LL := LL) (r • c) x = r • mulVdR (K := K) (LL := LL) c x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul v z =>
    simp only [mulVdR_tmul]
    rw [← TensorProduct.tmul_smul, ← Algebra.smul_def, ← Algebra.smul_def, smul_assoc]

def projMap (τ : K →ₐ[Qp] LL) (x : V ⊗[Qp] BdR) : K ⊗[Qp] K →ₗ[Qp] V ⊗[Qp] BdR :=
  TensorProduct.lift (LinearMap.mk₂ Qp (fun a c => τ a • mulVdR (K := K) (LL := LL) c x)
    (fun a a' c => by rw [map_add, add_smul])
    (fun r a c => by rw [map_smul, smul_assoc])
    (fun a c c' => by rw [mul_add', smul_add])
    (fun r a c => by rw [mul_smul', smul_comm]))

theorem proj_mem (τ : K →ₐ[Qp] LL) {n : ℕ} (α β : Fin n → K)
    (h : ∀ κ : K, ∑ j, (κ * α j) ⊗ₜ[Qp] β j = ∑ j, α j ⊗ₜ[Qp] (κ * β j)) (u : ℤ)
    {x : V ⊗[Qp] BdR} (hx : x ∈ DdR PD ρ) (hu : x ∈ FilV PD (LL := LL) (V := V) u)
    (hj : ¬ IsJumpV PD ρ τ u) :
    ∑ j, τ (α j) • mulVdR (K := K) (LL := LL) (β j) x ∈ FilV PD (LL := LL) (V := V) (u + 1) := by
  have he : FildR PD ρ τ (u + 1) = FildR PD ρ τ u := not_not.1 hj
  have : ∑ j, τ (α j) • mulVdR (K := K) (LL := LL) (β j) x ∈ FildR PD ρ τ u := by
    refine ⟨⟨Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mul_mem_DdR PD ρ _ hx), ?_⟩,
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mul_mem_FilV PD u _ hu)⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    intro c
    have := congrArg (projMap τ x) (h c)
    simp only [map_sum, projMap, TensorProduct.lift.tmul, LinearMap.mk₂_apply] at this
    simp only [map_sum, map_smul, mul_mul, Finset.smul_sum, smul_smul, ← map_mul]
    exact this.symm
  rw [← he] at this
  exact this.2

def coordMap (f : V →ₗ[Qp] Qp) : V ⊗[Qp] BdR →ₗ[Qp] BdR :=
  (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id

theorem coordMap_mem (f : V →ₗ[Qp] Qp) (a : ℤ) {x : V ⊗[Qp] BdR}
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) : coordMap f x ∈ PD.Fil a := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add]; exact Submodule.add_mem _ hx hy
  | tmul v z =>
    simp only [coordMap, TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply,
      Submodule.subtype_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
      LinearEquiv.coe_coe, TensorProduct.lid_tmul]
    exact ((PD.Fil a).restrictScalars Qp).smul_mem _ z.2

theorem coord_proj (τ : K →ₐ[Qp] LL) {n d : ℕ} (α β : Fin n → K) (f : V →ₗ[Qp] Qp)
    (b : Fin d → V) (y : Fin d → BdR) (s : BdR) :
    coordMap f (∑ j, τ (α j) • mulVdR (K := K) (LL := LL) (β j) (∑ k, b k ⊗ₜ[Qp] (y k * s))) =
      (∑ j, ∑ k, (algebraMap K BdR (β j) * algebraMap Qp BdR (f (τ (α j) • b k))) * y k) * s := by
  simp only [map_sum, mulVdR_tmul, Finset.smul_sum, TensorProduct.smul_tmul', coordMap,
    LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
    LinearMap.id_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def]
  ring

end General

open GlobalTheory.DeRhamSymbol

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : ThetaL P AI)

theorem theta_sum {ι : Type} (s : Finset ι) (z : ι → P.R.BdR)
    (hz : ∀ i, z i ∈ (P.PD (botExt l)).Fil 0) : J.θ (∑ i ∈ s, z i) = ∑ i ∈ s, J.θ (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (J.θ_ker 0 (Submodule.zero_mem _)).2 (Submodule.zero_mem _)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      J.θ_add _ (hz a) _ (Submodule.sum_mem _ fun i _ => hz i), ih]

theorem theta_lin {n d : ℕ} (c : Fin n → Fin d → Om l) (y : Fin d → P.R.BdR)
    (hy : ∀ k, y k ∈ (P.PD (botExt l)).Fil 0)
    (h : ∑ j, ∑ k, algebraMap (Om l) P.R.BdR (c j k) * y k ∈ (P.PD (botExt l)).Fil 1) :
    ∑ j, ∑ k, ((c j k : Om l) : PadicComplex l) * J.θ (y k) = 0 := by
  have hm : ∀ (c : Om l) (k : Fin d), algebraMap (Om l) P.R.BdR c * y k ∈
      (P.PD (botExt l)).Fil 0 := fun c k => by
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ (om_mem c) (hy k)
    rwa [zero_add] at this
  have h3 := (J.θ_ker _ (Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ => hm _ k)).2 h
  rw [theta_sum J _ _ (fun j => Submodule.sum_mem _ fun k _ => hm _ k)] at h3
  rw [← h3]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [theta_sum J _ _ (fun k => hm _ k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [J.θ_mul _ (om_mem _) _ (hy k), J.θ_Om]

theorem mat_apply {n d : ℕ} (β : Fin n → Om l) (m : Fin n → Fin d → Fin d → ℚ_[l])
    (w : Fin d → PadicComplex l) (i : Fin d) :
    (∑ j, ((β j : Om l) : PadicComplex l) • Matrix.of (fun i k : Fin d =>
      algebraMap ℚ_[l] (PadicComplex l) (m j k i))).mulVec w i =
    ∑ k, ∑ j, ((β j * algebraMap ℚ_[l] (Om l) (m j k i) : Om l) : PadicComplex l) * w k := by
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply,
    Finset.sum_mul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [UniformSpace.Completion.coe_mul]
  rfl

theorem proj_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (θ : ThetaL P AI) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (d : ℕ) (b : Module.Basis (Fin d) ℚ_[l] T.V) (n : ℕ) (α β : Fin n → ↥K.1), (∀ κ : ↥K.1, ∑ j, (κ * α j) ⊗ₜ[ℚ_[l]] β j = ∑ j, α j ⊗ₜ[ℚ_[l]] (κ * β j)) → ∀ t : (P.R.BdR)ˣ, (t : P.R.BdR) = P.ιB P.tB → ∀ (u : ℤ) (y : Fin d → P.R.BdR), (∀ i, y i ∈ (P.PD K).Fil 0) → ∑ i, b i ⊗ₜ[ℚ_[l]] (y i * ((t ^ u : (P.R.BdR)ˣ) : P.R.BdR)) ∈ DdR (P.PD K) T.ρ → ¬ IsJumpV (P.PD K) T.ρ τ u → (∑ j, ((β j : Om l) : PadicComplex l) • Matrix.of (fun i k : Fin d => algebraMap ℚ_[l] (PadicComplex l) (b.repr (τ (α j) • b k) i))).mulVec (fun i => θ.θ (y i)) = 0 := by
  intro l _ P AI θ K LL T τ d b n α β h t ht u y hy hD hj
  obtain rfl : t = tU P := Units.ext ht
  have hF : ∑ i, b i ⊗ₜ[ℚ_[l]] (y i * ((tU P ^ u : (P.R.BdR)ˣ) : P.R.BdR)) ∈
      FilV (P.PD K) (LL := ↥LL.1) (V := T.V) u := by
    refine Submodule.sum_mem _ fun i _ => tmul_mem_FilV _ _ _ ?_
    have := (P.PD K).Fil_mul _ _ _ _ (hy i) ((mem_iff K u _).2 (zpow_mem θ u))
    rwa [zero_add] at this
  have h1 := proj_mem (P.PD K) T.ρ τ α β h u hD hF hj
  funext i
  have h2 := coordMap_mem (P.PD K) (b.coord i) _ h1
  rw [coord_proj, mem_iff, ← shift_iff θ, mul_left_comm, ← Units.val_mul, ← zpow_add,
    neg_add_cancel, zpow_zero, Units.val_one, mul_one] at h2
  have e : ∀ (j : Fin n) (k : Fin d), algebraMap (↥K.1) P.R.BdR (β j) *
      algebraMap ℚ_[l] P.R.BdR (b.coord i (τ (α j) • b k)) =
      algebraMap (Om l) P.R.BdR ((β j : Om l) *
        algebraMap ℚ_[l] (Om l) (b.repr (τ (α j) • b k) i)) := by
    intro j k
    rw [map_mul, ← IsScalarTower.algebraMap_apply]
    rfl
  simp only [e] at h2
  have h3 := theta_lin θ (fun j k => (β j : Om l) *
    algebraMap ℚ_[l] (Om l) (b.repr (τ (α j) • b k) i)) y (fun k => (mem_iff K 0 _).1 (hy k)) h2
  rw [Finset.sum_comm] at h3
  exact (mat_apply (fun j => (β j : Om l)) (fun j k i => b.repr (τ (α j) • b k) i) _ i).trans h3

end GlobalTheory.EmbeddingJump

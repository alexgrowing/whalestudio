import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfInvariant

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.DRFil

namespace GlobalTheory.DRFil

private theorem eq_zero_of_sum_smul_invariant_eq_zero_of_card_support_le {G E M ι : Type} [CommRing E] [DecidableEq E] [DecidableEq ι]
    (hE : IsField E) [AddCommGroup M] [Module E M] [Fintype ι] (σ : G → (E →+* E)) (ρ : G → (M →+ M))
    (hρ : ∀ g (e : E) (m : M), ρ g (e • m) = σ g e • ρ g m) (v : ι → M)
    (hv : ∀ g i, ρ g (v i) = v i)
    (hind : ∀ c : ι → E, (∀ g i, σ g (c i) = c i) → ∑ i, c i • v i = 0 → ∀ i, c i = 0) :
    ∀ n : ℕ, ∀ c : ι → E, (Finset.univ.filter (fun i => c i ≠ 0)).card ≤ n →
      ∑ i, c i • v i = 0 → ∀ i, c i = 0 := by
  intro n
  induction n with
  | zero =>
    intro c hcard _ i
    by_contra hi
    have hmem : i ∈ Finset.univ.filter (fun i => c i ≠ 0) := by simp [hi]
    have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  | succ n ih =>
    intro c hcard hsum
    by_contra hne
    push_neg at hne
    obtain ⟨i₀, hi₀⟩ := hne
    obtain ⟨b, hb⟩ := hE.mul_inv_cancel hi₀

    obtain ⟨c', hc'⟩ : ∃ c' : ι → E, ∀ i, c' i = b * c i := ⟨fun i => b * c i, fun _ => rfl⟩
    have hsum' : ∑ i, c' i • v i = 0 := by
      simp only [hc', mul_smul, ← Finset.smul_sum, hsum, smul_zero]
    have hone : c' i₀ = 1 := by rw [hc', mul_comm, hb]
    have hsupp : ∀ i, c' i ≠ 0 → c i ≠ 0 := by
      intro i h hci
      exact h (by rw [hc', hci, mul_zero])
    have hinv : ∀ g i, σ g (c' i) = c' i := by
      intro g

      obtain ⟨d, hd⟩ : ∃ d : ι → E, ∀ i, d i = σ g (c' i) - c' i := ⟨fun i => σ g (c' i) - c' i, fun _ => rfl⟩
      have h1 : ∑ i, σ g (c' i) • v i = 0 := by
        have hmap : ρ g (∑ i, c' i • v i) = ∑ i, σ g (c' i) • v i := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [hρ, hv]
        rw [← hmap, hsum', map_zero]
      have hdsum : ∑ i, d i • v i = 0 := by
        simp only [hd, sub_smul, Finset.sum_sub_distrib, h1, hsum', sub_zero]
      have hdcard : (Finset.univ.filter (fun i => d i ≠ 0)).card ≤ n := by
        have hsub : Finset.univ.filter (fun i => d i ≠ 0) ⊆
            (Finset.univ.filter (fun i => c i ≠ 0)).erase i₀ := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, ?_⟩
          · rintro rfl
            apply hi
            rw [hd, hone, map_one, sub_self]
          · apply hsupp
            intro h0
            apply hi
            rw [hd, h0, map_zero, sub_zero]
        have hmem : i₀ ∈ Finset.univ.filter (fun i => c i ≠ 0) := by simp [hi₀]
        have hle := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hmem] at hle
        omega
      intro i
      have h0 := ih d hdcard hdsum i
      rw [hd, sub_eq_zero] at h0
      exact h0
    have h1 := hind c' hinv hsum' i₀
    rw [hone] at h1
    haveI : Nontrivial E := ⟨hE.exists_pair_ne⟩
    exact one_ne_zero h1

theorem indep_of_invariant_isField {G E M ι : Type} [CommRing E] (hE : IsField E) [AddCommGroup M]
    [Module E M] [Fintype ι] (σ : G → (E →+* E)) (ρ : G → (M →+ M))
    (hρ : ∀ g (e : E) (m : M), ρ g (e • m) = σ g e • ρ g m) (v : ι → M)
    (hv : ∀ g i, ρ g (v i) = v i)
    (hind : ∀ c : ι → E, (∀ g i, σ g (c i) = c i) → ∑ i, c i • v i = 0 → ∀ i, c i = 0)
    (c : ι → E) (hc : ∑ i, c i • v i = 0) : ∀ i, c i = 0 := by
  classical
  exact eq_zero_of_sum_smul_invariant_eq_zero_of_card_support_le hE σ ρ hρ v hv hind
    (Finset.univ.filter (fun i => c i ≠ 0)).card c le_rfl hc

private theorem idem_mul_tmul_one_eq_idem_mul_one_tmul {Qp K : Type} [Field Qp] [Field K] [Algebra Qp K]
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp K] [CharZero Qp]
    {F : Type} [CommRing F] [Algebra Qp F] [Algebra K F] [IsScalarTower Qp K F]
    (τ : K →ₐ[Qp] LL) (c : K) :
    idem F τ * (τ c ⊗ₜ[Qp] (1 : F)) = idem F τ * ((1 : LL) ⊗ₜ[Qp] algebraMap K F c) := by
  unfold idem
  generalize_proofs
  rename_i hex
  obtain ⟨-, hspec⟩ := hex.choose_spec
  have h1 := congrArg (Algebra.TensorProduct.map (AlgHom.id Qp LL) (IsScalarTower.toAlgHom Qp K F))
    (hspec c)
  rw [map_mul, Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul] at h1
  simp only [AlgHom.id_apply, map_one, IsScalarTower.coe_toAlgHom'] at h1
  rw [mul_comm]
  exact h1.symm.trans (mul_comm _ _)

theorem exists_idem_mul_eq {Qp K : Type} [Field Qp] [Field K] [Algebra Qp K]
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp K] [CharZero Qp]
    {F : Type} [CommRing F] [Algebra Qp F] [Algebra K F] [IsScalarTower Qp K F]
    (τ : K →ₐ[Qp] LL) {κ : Type} [Fintype κ] (l : κ → LL)
    (hl : ∀ a : LL, ∃ c : κ → K, a = ∑ j, τ (c j) * l j) (r : LL ⊗[Qp] F) :
    ∃ b : κ → F, idem F τ * r = idem F τ * ∑ j, l j ⊗ₜ[Qp] b j := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a f =>
    obtain ⟨c, hc⟩ := hl a
    refine ⟨fun j => algebraMap K F (c j) * f, ?_⟩
    rw [hc, TensorProduct.sum_tmul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    calc idem F τ * ((τ (c j) * l j) ⊗ₜ[Qp] f)
        = idem F τ * (τ (c j) ⊗ₜ[Qp] (1 : F)) * (l j ⊗ₜ[Qp] f) := by
          rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      _ = idem F τ * ((1 : LL) ⊗ₜ[Qp] algebraMap K F (c j)) * (l j ⊗ₜ[Qp] f) := by
          rw [idem_mul_tmul_one_eq_idem_mul_one_tmul]
      _ = idem F τ * (l j ⊗ₜ[Qp] (algebraMap K F (c j) * f)) := by
          rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy =>
    obtain ⟨bx, hbx⟩ := hx
    obtain ⟨by', hby⟩ := hy
    refine ⟨fun j => bx j + by' j, ?_⟩
    simp only [TensorProduct.tmul_add, Finset.sum_add_distrib, mul_add, hbx, hby]

private theorem sm_tmul_tmul {Qp LL V F : Type} [Field Qp] [CommRing F] [Algebra Qp F] [Field LL]
    [Algebra Qp LL] [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (a : LL) (f : F) (v : V) (f' : F) :
    sm Qp F LL V (a ⊗ₜ[Qp] f) (v ⊗ₜ[Qp] f') = (a • v) ⊗ₜ[Qp] (f * f') := by
  simp [sm, bil]

private theorem sm_mul_inertia_eigenvalues {Qp LL V F : Type} [Field Qp] [CommRing F] [Algebra Qp F] [Field LL]
    [Algebra Qp LL] [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (x x' : LL ⊗[Qp] F) (y : V ⊗[Qp] F) :
    sm Qp F LL V (x * x') y = sm Qp F LL V x (sm Qp F LL V x' y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [add_mul, map_add, LinearMap.add_apply, h₁, h₂]
  | tmul a f =>
    induction x' using TensorProduct.induction_on with
    | zero => simp
    | add x₁ x₂ h₁ h₂ => simp only [mul_add, map_add, LinearMap.add_apply, h₁, h₂]
    | tmul a' f' =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
      | tmul v f'' =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, sm_tmul_tmul, sm_tmul_tmul, sm_tmul_tmul, mul_smul,
          mul_assoc]

theorem indep_of_linearIndependent_DdRE {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B F : Type} [CommRing B]
    [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp F] [Algebra K₀ F]
    [Algebra K F] [IsScalarTower Qp K F] [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F) {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL]
    [FiniteDimensional Qp K] [CharZero Qp] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V]
    [IsScalarTower Qp LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    {ι : Type} [Fintype ι] (d : ι → V ⊗[Qp] F) (hF : IsField F) (hd : ∀ i, d i ∈ DdRE PD ρ τ)
    (hind : LinearIndependent LL d) (r : ι → LL ⊗[Qp] F)
    (hr : ∑ i, sm Qp F LL V (r i) (d i) = 0) : ∀ i, idem F τ * r i = 0 := by
  classical

  have hinvd : ∀ i g, actVdR PD ρ g (d i) = d i := by
    intro i g
    have h := hd i
    unfold DdRE DdR at h
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h
    exact h.1 g
  have hτd : ∀ i (c : K), mulVdR (K := K) (BdR := F) (V := V) (LL := LL) c (d i) = τ c • d i := by
    intro i c
    have h := hd i
    unfold DdRE DdR at h
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h
    exact h.2 c
  have hmul : ∀ (c : K) (y : V ⊗[Qp] F), sm Qp F LL V ((1 : LL) ⊗ₜ[Qp] algebraMap K F c) y =
      mulVdR (K := K) (BdR := F) (V := V) (LL := LL) c y := by
    intro c y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
    | tmul v f => simp [sm_tmul_tmul, mulVdR]
  have hleft : ∀ (a : LL) (f : F) (y : V ⊗[Qp] F),
      sm Qp F LL V (a ⊗ₜ[Qp] f) y = a • sm Qp F LL V ((1 : LL) ⊗ₜ[Qp] f) y := by
    intro a f y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, smul_add]
    | tmul v f' => rw [sm_tmul_tmul, sm_tmul_tmul, one_smul, TensorProduct.smul_tmul']

  have hfix : ∀ i, sm Qp F LL V (idem F τ) (d i) = d i := by
    intro i
    unfold idem
    generalize_proofs
    rename_i hex
    obtain ⟨h1, -⟩ := hex.choose_spec
    have key : ∀ e' : LL ⊗[Qp] K,
        sm Qp F LL V (Algebra.TensorProduct.map (AlgHom.id Qp LL) (IsScalarTower.toAlgHom Qp K F) e')
          (d i) = Algebra.TensorProduct.lift (AlgHom.id Qp LL) τ (fun _ _ => Commute.all _ _) e' • d i := by
      intro e'
      induction e' using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, add_smul]
      | tmul a k =>
        simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply,
          IsScalarTower.toAlgHom_apply]
        rw [hleft, hmul, hτd, mul_smul]
    rw [key]
    have h1' : Algebra.TensorProduct.lift (AlgHom.id Qp LL) τ (fun _ _ => Commute.all _ _) hex.choose = 1 :=
      h1
    rw [h1', one_smul]
  have hidem : ∀ i (X : LL ⊗[Qp] F), sm Qp F LL V (idem F τ * X) (d i) = sm Qp F LL V X (d i) := by
    intro i X
    rw [mul_comm, sm_mul_inertia_eigenvalues, hfix]

  letI : Algebra K LL := τ.toRingHom.toAlgebra
  haveI : IsScalarTower Qp K LL := IsScalarTower.of_algebraMap_eq (fun q => (τ.commutes q).symm)
  haveI : FiniteDimensional K LL := Module.Finite.of_restrictScalars_finite Qp K LL
  obtain ⟨n, l, hgen, hlind⟩ : ∃ (n : ℕ) (l : Fin n → LL),
      (∀ a : LL, ∃ c : Fin n → K, a = ∑ j, τ (c j) * l j) ∧
        (∀ c : Fin n → K, ∑ j, τ (c j) * l j = 0 → ∀ j, c j = 0) := by
    refine ⟨_, Module.finBasis K LL, fun a => ⟨fun j => (Module.finBasis K LL).repr a j, ?_⟩,
      fun c hc => Fintype.linearIndependent_iff.mp (Module.finBasis K LL).linearIndependent c hc⟩
    conv_lhs => rw [← (Module.finBasis K LL).sum_repr a]
    rfl
  choose b hb using fun i => exists_idem_mul_eq τ l hgen (r i)
  have hrel : ∑ i, sm Qp F LL V (∑ j, l j ⊗ₜ[Qp] b i j) (d i) = 0 := by
    rw [← hr]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hidem i, ← hb i, hidem i]

  let w : ι × Fin n → F ⊗[Qp] V := fun p => TensorProduct.comm Qp V F (l p.2 • d p.1)
  let ρ' : G → (F ⊗[Qp] V →+ F ⊗[Qp] V) := fun g => AddMonoidHom.mk'
    (fun m => TensorProduct.comm Qp V F (actVdR PD ρ g ((TensorProduct.comm Qp V F).symm m)))
    (fun x y => by simp only [map_add])
  let σ' : G → (F →+* F) := fun g => (PD.actdR g).toAlgHom.toRingHom
  have hρ' : ∀ g (e : F) (m : F ⊗[Qp] V), ρ' g (e • m) = σ' g e • ρ' g m := by
    intro g e m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
    | tmul f v => simp [ρ', σ', actVdR, TensorProduct.smul_tmul', smul_eq_mul, map_mul]
  have hv' : ∀ g p, ρ' g (w p) = w p := by
    intro g p
    simp only [ρ', w, AddMonoidHom.mk'_apply, LinearEquiv.symm_apply_apply, map_smul, hinvd]
  have hL1 : ∀ (k : K) (y : V ⊗[Qp] F), algebraMap K F k • TensorProduct.comm Qp V F y =
      TensorProduct.comm Qp V F (mulVdR (K := K) (BdR := F) (V := V) (LL := LL) k y) := by
    intro k y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, smul_add, hx, hy, map_add, map_add]
    | tmul v f =>
      simp only [mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply,
        TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  have hind' : ∀ c : ι × Fin n → F, (∀ g p, σ' g (c p) = c p) → ∑ p, c p • w p = 0 → ∀ p, c p = 0 := by
    intro c hcinv hcsum
    have hk : ∀ p, ∃ k : K, algebraMap K F k = c p := fun p => PD.invdR (c p) (fun g => hcinv g p)
    choose k hk using hk
    have hterm : ∀ p, c p • w p = TensorProduct.comm Qp V F ((τ (k p) * l p.2) • d p.1) := by
      intro p
      show c p • TensorProduct.comm Qp V F (l p.2 • d p.1) = _
      rw [← hk p, hL1, map_smul, hτd, smul_smul, mul_comm]
    have hzero : ∑ i, (∑ j, τ (k (i, j)) * l j) • d i = 0 := by
      have h2 : TensorProduct.comm Qp V F (∑ i, (∑ j, τ (k (i, j)) * l j) • d i) = 0 := by
        rw [← hcsum, Fintype.sum_prod_type]
        simp only [hterm, map_sum, Finset.sum_smul]
      exact (TensorProduct.comm Qp V F).map_eq_zero_iff.mp h2
    have hcoef := Fintype.linearIndependent_iff.mp hind (fun i => ∑ j, τ (k (i, j)) * l j) hzero
    rintro ⟨i, j⟩
    have hkij : k (i, j) = 0 := hlind (fun j => k (i, j)) (hcoef i) j
    rw [← hk (i, j), hkij, map_zero]
  have hL2 : ∀ (a : LL) (f : F) (y : V ⊗[Qp] F),
      TensorProduct.comm Qp V F (sm Qp F LL V (a ⊗ₜ[Qp] f) y) = f • TensorProduct.comm Qp V F (a • y) := by
    intro a f y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
    | tmul v f' => simp [sm_tmul_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  have hcomb : ∑ p, b p.1 p.2 • w p = 0 := by
    have h2 := congrArg (TensorProduct.comm Qp V F) hrel
    rw [map_zero] at h2
    rw [← h2, Fintype.sum_prod_type]
    simp only [w, map_sum, LinearMap.sum_apply, hL2]
  have hb0 := indep_of_invariant_isField hF σ' ρ' hρ' w hv' hind' (fun p => b p.1 p.2) hcomb
  intro i
  have hbij : ∀ j, b i j = 0 := fun j => hb0 (i, j)
  rw [hb i]
  simp [hbij]

end GlobalTheory.DRFil

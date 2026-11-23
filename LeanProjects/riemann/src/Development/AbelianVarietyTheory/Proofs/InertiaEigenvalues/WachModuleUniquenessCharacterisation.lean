import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapConstantCoeffEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFreeLatticeEqWachLatticeInvertXStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.FrobeniusMatrixUniqueness

section Comb

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ}

theorem comb_mul (b : Fin r → M) (P P' : Matrix (Fin r) (Fin r) R) (j : Fin r) :
    ∑ i, (P * P') i j • b i = ∑ k, P' k j • ∑ i, P i k • b i := by
  simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

theorem comb_smul (b : Fin r → M) (c : R) (P : Matrix (Fin r) (Fin r) R) (j : Fin r) :
    ∑ i, (c • P) i j • b i = c • ∑ i, P i j • b i := by
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

theorem comb_one (b : Fin r → M) (j : Fin r) :
    ∑ i, (1 : Matrix (Fin r) (Fin r) R) i j • b i = b j := by
  simp [Matrix.one_apply]

theorem matrix_eq_of_comb {b : Fin r → M} (hb : LinearIndependent R b) {P P' : Matrix (Fin r) (Fin r) R}
    (h : ∀ j, ∑ i, P i j • b i = ∑ i, P' i j • b i) : P = P' := by
  ext i j
  have h0 : ∑ k, (P k j - P' k j) • b k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h j, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hb _ h0 i)

theorem exists_pow_uniform {S : Submodule R M} (q : R) (w : Fin r → M) (h : ∀ k, ∃ e : ℕ, q ^ e • w k ∈ S) :
    ∃ e : ℕ, ∀ k, q ^ e • w k ∈ S := by
  choose e he using h
  refine ⟨∑ k, e k, fun k => ?_⟩
  have hk : e k ≤ ∑ k, e k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  rw [← Nat.sub_add_cancel hk, pow_add, mul_smul]
  exact S.smul_mem _ (he k)

theorem coords {S : Submodule R M} (bS : Module.Basis (Fin r) R ↥S) {x : M} (hx : x ∈ S) :
    ∃ c : Fin r → R, x = ∑ i, c i • (bS i : M) := by
  refine ⟨bS.repr ⟨x, hx⟩, ?_⟩
  have h := congrArg Subtype.val (bS.sum_repr ⟨x, hx⟩)
  rw [Submodule.coe_sum] at h
  simp only [Submodule.coe_smul] at h
  exact h.symm

end Comb

section Generic

open Formalism.MainNotions.DeltaInvariantLattices

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem φD_smulA (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  have h := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at h
  exact h

theorem γ_smulA (a : LetA O n) (x : W.DD T) : W.γ T (a • x) = W.γA W.gam a • W.γ T x := by
  have h := W.γD_smul T W.gam (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at h
  exact h

theorem X_pow_smul_cancel (a : ℕ) {x y : W.DD T} (h : W.X ^ a • x = W.X ^ a • y) : x = y := by
  rw [← algebraMap_smul W.EE (W.X ^ a) x, ← algebraMap_smul W.EE (W.X ^ a) y, map_pow] at h
  exact ((GlobalTheory.NL.IoXQ.isUnit_X W).pow a).smul_left_cancel.1 h

theorem basis_of_freeA {S : Submodule (LetA O n) (W.DD T)} (hS : FreeA W T S) :
    ∃ r : ℕ, Nonempty (Module.Basis (Fin r) (LetA O n) ↥S) := by
  obtain ⟨r, b, hb, hu⟩ := hS
  let w : Fin r → ↥S := fun j => ⟨b j, hb j⟩
  have li : LinearIndependent (LetA O n) w := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    have hg' : (0 : W.DD T) = ∑ j, g j • b j := by
      have := congrArg Subtype.val hg
      rw [Submodule.coe_sum] at this
      simpa [w] using this.symm
    have h0 : (0 : W.DD T) = ∑ j, (0 : Fin r → LetA O n) j • b j := by simp
    have := (hu 0 S.zero_mem).unique hg' h0
    exact congrFun this i
  have sp : ⊤ ≤ Submodule.span (LetA O n) (Set.range w) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨c, hc, -⟩ := hu x hx
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨c, Subtype.ext ?_⟩
    rw [Submodule.coe_sum]
    simp [w, hc]
  exact ⟨r, ⟨Module.Basis.mk li sp⟩⟩

end Generic

section Key

open Formalism.MainNotions.DeltaInvariantLattices

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem gam_matrix {r : ℕ} {S : Submodule (LetA O n) (W.DD T)} (bS : Module.Basis (Fin r) (LetA O n) ↥S)
    (h : ∀ x ∈ S, ∃ y ∈ S, W.γ T x - x = (letπ : LetA O n) • y) :
    ∃ Gm : Matrix (Fin r) (Fin r) (LetA O n), (∀ i j, (Gm - 1) i j ∈ Ideal.span {(letπ : LetA O n)}) ∧
      ∀ k, W.γ T (bS k) = ∑ i, Gm i k • (bS i : W.DD T) := by
  choose y hy hyeq using fun k => h _ (bS k).2
  choose c hc using fun k => coords bS (hy k)
  refine ⟨1 + (letπ : LetA O n) • Matrix.of (fun i k => c k i), fun i j => ?_, fun k => ?_⟩
  · rw [add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
  · simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
    rw [comb_one, comb_smul]
    simp only [Matrix.of_apply]
    rw [← hc k, ← hyeq k, add_sub_cancel]

theorem phi_matrix {r : ℕ} {S : Submodule (LetA O n) (W.DD T)} (bS : Module.Basis (Fin r) (LetA O n) ↥S)
    (h : ∀ x ∈ S, ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ S) :
    ∃ (e : ℕ) (F : Matrix (Fin r) (Fin r) (LetA O n)),
      ∀ k, W.Q ^ e • W.φD T (bS k) = ∑ i, F i k • (bS i : W.DD T) := by
  obtain ⟨e, he⟩ := exists_pow_uniform W.Q (fun k => W.φD T (bS k)) (fun k => h _ (bS k).2)
  choose c hc using fun k => coords bS (he k)
  exact ⟨e, Matrix.of fun i k => c k i, hc⟩

theorem phiinv_matrix {r : ℕ} {S : Submodule (LetA O n) (W.DD T)} (bS : Module.Basis (Fin r) (LetA O n) ↥S)
    (h : ∀ y ∈ S, ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T S) :
    ∃ (e : ℕ) (P : Matrix (Fin r) (Fin r) (LetA O n)),
      ∀ k, ∑ i, P i k • W.φD T (bS i) = W.Q ^ e • (bS k : W.DD T) := by
  have hspan : φspan W T S ≤ Submodule.span (LetA O n) (Set.range fun i => W.φD T (bS i)) := by
    rw [φspan, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := coords bS hx
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [φD_smulA]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨e, he⟩ := exists_pow_uniform W.Q (fun k => (bS k : W.DD T))
    (S := Submodule.span (LetA O n) (Set.range fun i => W.φD T (bS i)))
    (fun k => let ⟨e, he⟩ := h _ (bS k).2; ⟨e, hspan he⟩)
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun (LetA O n)).1 (he k)
  exact ⟨e, Matrix.of fun i k => c k i, hc⟩

theorem le_of_X_pow_smul_le
    (hmat : ∀ (r a m m' : ℕ) (B G G₁ Pm P₁ P₁' : Matrix (Fin r) (Fin r) (LetA O n)),
      (∀ i j, (G - 1) i j ∈ Ideal.span {(letπ : LetA O n)}) →
      (∀ i j, (G₁ - 1) i j ∈ Ideal.span {(letπ : LetA O n)}) →
      (W.X ^ a) • (G * B.map (W.γA W.gam)) = (W.γA W.gam W.X ^ a) • (B * G₁) →
      P₁ * P₁' = (W.Q ^ m') • (1 : Matrix (Fin r) (Fin r) (LetA O n)) →
      Pm * B.map W.φA = (W.Q ^ m) • (B * P₁) → ∀ i j, W.X ^ a ∣ B i j)
    {M M₁ : Submodule (LetA O n) (W.DD T)} {r : ℕ}
    (bM : Module.Basis (Fin r) (LetA O n) ↥M) (bM₁ : Module.Basis (Fin r) (LetA O n) ↥M₁)
    (hγ : ∀ x ∈ M, ∃ y ∈ M, W.γ T x - x = (letπ : LetA O n) • y)
    (hφ : ∀ x ∈ M, ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ M)
    (hγ₁ : ∀ x ∈ M₁, ∃ y ∈ M₁, W.γ T x - x = (letπ : LetA O n) • y)
    (hφ₁ : ∀ x ∈ M₁, ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ M₁)
    (hφinv₁ : ∀ y ∈ M₁, ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T M₁)
    (a : ℕ) (ha : ∀ x ∈ M₁, W.X ^ a • x ∈ M) : M₁ ≤ M := by
  set b : Fin r → W.DD T := fun i => (bM i : W.DD T) with hbdef
  set b₁ : Fin r → W.DD T := fun i => (bM₁ i : W.DD T) with hb₁def
  have hbM : ∀ i, b i ∈ M := fun i => (bM i).2
  have hb₁M : ∀ i, b₁ i ∈ M₁ := fun i => (bM₁ i).2
  have li : LinearIndependent (LetA O n) b := bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have li₁ : LinearIndependent (LetA O n) b₁ :=
    bM₁.linearIndependent.map' M₁.subtype (Submodule.ker_subtype M₁)
  choose Bt hBt using fun j => coords bM (ha _ (hb₁M j))
  set Bm : Matrix (Fin r) (Fin r) (LetA O n) := Matrix.of fun i j => Bt j i with hBm
  have hB : ∀ j, W.X ^ a • b₁ j = ∑ i, Bm i j • b i := fun j => hBt j
  obtain ⟨Gm, hG1, hG⟩ := gam_matrix W T bM hγ
  obtain ⟨Gm₁, hG₁1, hG₁⟩ := gam_matrix W T bM₁ hγ₁
  obtain ⟨hM, F, hF⟩ := phi_matrix W T bM hφ
  obtain ⟨h₁, F₁, hF₁⟩ := phi_matrix W T bM₁ hφ₁
  obtain ⟨e, P', hP'⟩ := phiinv_matrix W T bM₁ hφinv₁
  have R1 : (W.X ^ a) • (Gm * Bm.map (W.γA W.gam)) = (W.γA W.gam W.X ^ a) • (Bm * Gm₁) := by
    refine matrix_eq_of_comb li fun j => ?_
    rw [comb_smul, comb_mul, comb_smul, comb_mul]
    have e1 : ∑ k, Bm.map (W.γA W.gam) k j • ∑ i, Gm i k • b i = W.γ T (W.X ^ a • b₁ j) := by
      rw [hB j, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [γ_smulA, ← hG k, Matrix.map_apply]
    have e2 : ∑ k, Gm₁ k j • ∑ i, Bm i k • b i = W.X ^ a • W.γ T (b₁ j) := by
      rw [hG₁ j, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hB k, smul_comm]
    rw [e1, e2, γ_smulA, map_pow]
    exact smul_comm _ _ _
  have R2 : F₁ * P' = (W.Q ^ (h₁ + e)) • (1 : Matrix (Fin r) (Fin r) (LetA O n)) := by
    refine matrix_eq_of_comb li₁ fun j => ?_
    rw [comb_mul, comb_smul, comb_one]
    have e1 : ∑ k, P' k j • ∑ i, F₁ i k • b₁ i = W.Q ^ h₁ • ∑ k, P' k j • W.φD T (b₁ k) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hF₁ k, smul_comm]
    rw [e1, hP' j, smul_smul, ← pow_add]
  have R3 : (W.Q ^ h₁ • F) * Bm.map W.φA = (W.Q ^ (a + hM)) • (Bm * F₁) := by
    refine matrix_eq_of_comb li fun j => ?_
    rw [Matrix.smul_mul, comb_smul, comb_mul, comb_smul, comb_mul]
    have e1 : ∑ k, Bm.map W.φA k j • ∑ i, F i k • b i = W.Q ^ hM • W.φD T (W.X ^ a • b₁ j) := by
      rw [hB j, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [φD_smulA, ← hF k, Matrix.map_apply, smul_comm]
    have e2 : ∑ k, F₁ k j • ∑ i, Bm i k • b i = W.X ^ a • W.Q ^ h₁ • W.φD T (b₁ j) := by
      rw [hF₁ j, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hB k, smul_comm]
    rw [e1, e2, φD_smulA, map_pow, W.φA_X]
    simp only [smul_smul]
    congr 1
    ring
  have hdiv := hmat r a (a + hM) (h₁ + e) Bm Gm Gm₁ (W.Q ^ h₁ • F) F₁ P' hG1 hG₁1 R1 R2 R3
  choose d hd using hdiv
  have hb₁ : ∀ j, b₁ j ∈ M := by
    intro j
    have h' : W.X ^ a • b₁ j = W.X ^ a • ∑ i, d i j • b i := by
      rw [hB j, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hd i j, mul_smul]
    rw [X_pow_smul_cancel W T a h']
    exact M.sum_mem fun i _ => M.smul_mem _ (hbM i)
  intro x hx
  obtain ⟨c, rfl⟩ := coords bM₁ hx
  exact M.sum_mem fun j _ => M.smul_mem _ (hb₁ j)

end Key

open Formalism.MainNotions.DeltaInvariantLattices in
set_option maxHeartbeats 800000 in

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), WachCharacterisation D HW F := by
  intro D HW F l _ K s LL h T hT N₁ hfree hbc hγN₁ hγπ hφ hφinv
  obtain ⟨a, h1, h2⟩ := GlobalTheory.T.wachFreeLattice_eq_wachLattice_invert_X D HW F l K s LL h T hT N₁ hfree hbc hφ hφinv
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  obtain ⟨r₁, ⟨b₁⟩⟩ := basis_of_freeA _ T hfree
  haveI : Nontrivial ((HW l).W K s LL h).EE := ((HW l).W K s LL h).EE_inj.nontrivial
  have hr : r₁ = Module.finrank ↥(OL LL) ↥T.L.T := by
    have e := (hbc.basis b₁).indexEquiv ((((HW l).W K s LL h).N_base T hT).basis nb)
    simpa using Fintype.card_congr e
  subst hr
  have hmat := fun r a m m' B G G₁ Pm P₁ P₁' =>
    GlobalTheory.NL.WachMat.X_pow_dvd_entry D HW l K s LL h r a m m' B G G₁ Pm P₁ P₁'
  have hγ₁ : ∀ x ∈ N₁, ∃ y ∈ N₁, ((HW l).W K s LL h).γ T x - x = (letπ : AA K LL) • y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := hγπ x hx
    exact ⟨y, hy, e.symm⟩
  have hγN : ∀ x ∈ ((HW l).W K s LL h).N T, ∃ y ∈ ((HW l).W K s LL h).N T,
      ((HW l).W K s LL h).γ T x - x = (letπ : AA K LL) • y :=
    fun x hx => ((HW l).W K s LL h).N_π T _ x hx
  apply le_antisymm
  · exact le_of_X_pow_smul_le _ T hmat nb b₁ hγN (((HW l).W K s LL h).N_φ T) hγ₁ hφ hφinv a h1
  · exact le_of_X_pow_smul_le _ T hmat b₁ nb hγ₁ hφ hγN (((HW l).W K s LL h).N_φ T)
      (((HW l).W K s LL h).N_φinv T) a h2

end GlobalTheory.NL.FrobeniusMatrixUniqueness

import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TupMemLatT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepTupleSpanSaturationBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepTupleRelationMemPowSpanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledProductSpanLatticeExistsPadicBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRepOfMatrixTuplePadicBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledProductSpanLatticeStableGaloisRepTupleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledProductSpanLatticeEntriesAndSpanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceEstimateScaledProductSpanLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.CovLayer

open GlobalTheory.TraceConjugationCover

variable {l : ℕ} [Fact l.Prime]

theorem sumZ {Γ V : Type} [AddCommGroup V] [Module (Om l) V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] (Om l) V]
    (v : Γ → V) (F : Γ →₀ ℤ_[l]) : (F.sum fun g c => zOm l c • v g) = Finsupp.linearCombination ℤ_[l] v F := by
  simp only [Finsupp.linearCombination_apply, zOm_smul]

theorem sumZ_fin {ι V : Type} [Fintype ι] [AddCommGroup V] [Module (Om l) V] [Module ℤ_[l] V]
    [IsScalarTower ℤ_[l] (Om l) V] (v : ι → V) (w : ι → ℤ_[l]) : ∑ i, zOm l (w i) • v i = ∑ i, w i • v i := by
  simp only [zOm_smul]

theorem lpow_smul {V : Type} [AddCommGroup V] [Module (Om l) V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] (Om l) V]
    (N : ℕ) (x : V) : (l : Om l) ^ N • x = ((l : ℤ_[l]) ^ N) • x := by
  rw [← zOm_smul]; simp [zOm, map_pow, map_natCast]

theorem coord_unique {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V]
    [IsScalarTower ℤ_[l] ℚ_[l] V] {b : ι → V} (hb : LinearIndependent ℚ_[l] b) {v w : ι → ℤ_[l]}
    (h : ∑ i, v i • b i = ∑ i, w i • b i) : v = w := by
  have hz : LinearIndependent ℤ_[l] b := (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).2 hb
  funext i
  exact Fintype.linearIndependent_iffₛ.1 hz v w h i

theorem lc_translate {Γ A : Type} [Group Γ] [Ring A] [Module ℤ_[l] A] [SMulCommClass ℤ_[l] A A]
    [IsScalarTower ℤ_[l] A A] (v : Γ → A) (hv : ∀ g h, v (g * h) = v g * v h) (g : Γ) (F : Γ →₀ ℤ_[l]) :
    Finsupp.linearCombination ℤ_[l] v (F.mapDomain (g * ·)) = v g * Finsupp.linearCombination ℤ_[l] v F := by
  rw [Finsupp.linearCombination_mapDomain]
  have : (v ∘ (g * ·)) = (LinearMap.mulLeft ℤ_[l] (v g)) ∘ v := by funext h; simp [hv]
  rw [this, ← Finsupp.apply_linearCombination]
  rfl

theorem tup_mul {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g h : Γ) :
    tup ρs (g * h) = tup ρs g * tup ρs h := by
  funext k; simp [tup, map_mul, Units.val_mul]

theorem tup_one {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) : tup ρs 1 = 1 := by
  funext k; simp [tup]

theorem coordsB {Γ : Type} [Group Γ] {a d : ℕ} {ρ : Γ →* GL (Fin d) ℤ_[l]} {r : Γ →* GL (Fin a) (Om l)}
    {b : Fin d → Matrix (Fin a) (Fin a) (Om l)} {e : Fin d → ℤ_[l]} (hR : Reads ρ r b e) (f : Γ →₀ ℤ_[l]) :
    Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) f =
      ∑ i, (f.sum fun h c => c * ∑ j, ((ρ h : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) i j * e j) • b i := by
  have key : ∀ h, ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) =
      ∑ i, (∑ j, ((ρ h : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) i j * e j) • b i := by
    intro h
    have h1 := hR.one
    have h2 := hR.equi h
    simp only [zOm_smul] at h1 h2
    calc ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) = (r h).val * ∑ j, e j • b j := by
          rw [h1, Matrix.mul_one]
      _ = ∑ j, e j • ((r h).val * b j) := by rw [Matrix.mul_sum]; simp only [Matrix.mul_smul]
      _ = ∑ j, e j • ∑ i, ((ρ h).val i j) • b i := by simp only [h2]
      _ = _ := by
        simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, hf, hg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_smul, Finsupp.sum_add_index' (by simp) (by intros; ring)]
  | single h c =>
    rw [Finsupp.linearCombination_single, key h, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_single_index (by simp), smul_smul]

theorem layer : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (d : ℕ) (ρ : Γ →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → LinearIndependent ℚ_[l] b → (∀ i, ∃ f : Γ →₀ ℤ_[l], b i = f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → ∀ c : ℕ, (∀ (n : ℕ) (f : Γ →₀ ℤ_[l]), (∀ g, ‖((f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) * ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + c)) → ∃ f' : Γ →₀ ℤ_[l], (f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) = (l : Om l) ^ n • (f'.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))) → ∀ (n N : ℕ), n ≤ N → (∀ w : Fin d → ℤ_[l], ‖((l : Om l) ^ N • ∑ i, zOm l (w i) • b i).trace‖ ≤ ((l : ℝ) ^ n)⁻¹) → ∀ (m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (L : Fin m → FinExt l) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))), (∀ k, Continuous (ρs k)) → (∀ k g i j, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ (L k).1) → (∀ k, ∀ x ∈ t k, ∀ i j, x i j ∈ (L k).1) → (∀ k (x : Matrix (Fin a) (Fin a) (Om l)), (∀ i j, x i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l)))) → (∀ k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t k, zOm l (c' y) • y = 1) → (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → ∀ cs : Fin m → Om l, (∀ g, ‖trc r g - ∑ k, cs k * trc (ρs k) g‖ ≤ ((l : ℝ)⁻¹) ^ (N + c)) → ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∃ (d' : ℕ) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)) (e' : Fin d' → ℤ_[l]) (P : Matrix (Fin d) (Fin d') ℤ_[l]), Continuous ρ' ∧ (∀ s k i j, bb s k i j ∈ (L k).1) ∧ LinearIndependent ℚ_[l] bb ∧ (∀ x : Fin m → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (Set.range bb)) ∧ (∀ k, Reads ρ' (ρs k) (fun s => bb s k) e') ∧ (∀ s, bb s ∈ GlobalTheory.TraceConjugationCover.latT ρs t M) ∧ (∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s) ∧ GlobalTheory.TraceConjugationCover.Carries r b ρs t M bb P N ∧ Onto (fun g => ((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l])) (fun g => ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) P n ∧ (∀ i, (l : ℤ_[l]) ^ n ∣ (P *ᵥ e' - e) i) ∧ ∀ s, ‖(∑ i, zOm l (P i s) • b i).trace - ∑ k, cs k * (bb s k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
  intro l _ Γ _ _ a r d ρ b e hR hind hspan c hlow n N hnN hN m ρs L t hcont hρL htL hLspan hone hstab cs happ
  obtain ⟨u, hu⟩ := GlobalTheory.T.galoisRepTuple_span_saturation_bound l Γ a m ρs t hone hstab
  obtain ⟨M₁, hM₁⟩ := GlobalTheory.T.trace_estimate_scaledProductSpanLattice l Γ a r m ρs t c N n cs hnN happ
  refine ⟨max (N + u) M₁, fun M hM => ?_⟩
  have hMu : N + u ≤ M := le_trans (le_max_left _ _) hM
  have hM1 : M₁ ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨hstL, hstT⟩ := GlobalTheory.T.scaledProductSpanLattice_stable_galoisRepTuple l Γ a m ρs t M hstab
  obtain ⟨hentT, hspT⟩ := GlobalTheory.T.scaledProductSpanLattice_entries_and_span l Γ a m ρs L t M hρL htL hLspan
  obtain ⟨d', bb, hbbind, hbbmem, hbbco⟩ := GlobalTheory.T.scaledProductSpanLattice_exists_padic_basis l Γ a m ρs t M hone hstab
  obtain ⟨ρ', hρ'c, hact⟩ := GlobalTheory.T.continuous_rep_of_matrixTuple_padic_basis l Γ a m ρs (latT ρs t M) d' bb hcont hbbind hbbmem hbbco hstT
  have hW : ∀ H : Γ →₀ ℤ_[l], Finsupp.linearCombination ℤ_[l] (tup ρs) H ∈ latL t M →
      ∃ w : Fin d → ℤ_[l], Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) H = (l : Om l) ^ N • ∑ i, w i • b i := by
    intro H hH
    rw [← sumZ] at hH
    obtain ⟨H', hH'⟩ := hu N M hMu H hH
    rw [sumZ, sumZ, lpow_smul] at hH'
    obtain ⟨f', hf'⟩ := GlobalTheory.T.galoisRepTuple_relation_mem_pow_span l Γ a r m ρs c N cs hlow happ (H - (l : ℤ_[l]) ^ N • H') (by
      rw [sumZ, map_sub, map_smul, hH', sub_self])
    rw [sumZ, sumZ, map_sub, map_smul, lpow_smul] at hf'
    refine ⟨fun i => (f' + H').sum fun h c => c * ∑ j, ((ρ h : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) i j * e j, ?_⟩
    rw [← coordsB hR (f' + H'), map_add, lpow_smul, smul_add, ← hf', sub_add_cancel]
  have hdec : ∀ s, ∃ (F : Γ →₀ ℤ_[l]) (y : Fin m → Matrix (Fin a) (Fin a) (Om l)), y ∈ latL t M ∧ bb s = Finsupp.linearCombination ℤ_[l] (tup ρs) F + y := by
    intro s
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hbbmem s)
    obtain ⟨F, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hx
    exact ⟨F, y, hy, by rw [← hxy, Finsupp.linearCombination_apply]⟩
  choose F y hy hFy using hdec
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin d) (Fin d') ℤ_[l], ∀ s, ∑ i, P i s • b i = Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) (F s) :=
    ⟨Matrix.of fun i s => (F s).sum fun h c => c * ∑ j, ((ρ h : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) i j * e j,
      fun s => (coordsB hR (F s)).symm⟩
  have hPz : ∀ z : Fin d' → ℤ_[l], ∑ i, (P *ᵥ z) i • b i = Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) (∑ s, z s • F s) := by
    intro z
    simp only [map_sum, map_smul, ← hP, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  have hCar : ∀ (z : Fin d' → ℤ_[l]) (G : Γ →₀ ℤ_[l]) (y0 : Fin m → Matrix (Fin a) (Fin a) (Om l)), y0 ∈ latL t M →
      ∑ s, z s • bb s = Finsupp.linearCombination ℤ_[l] (tup ρs) G + y0 →
      ∃ w : Fin d → ℤ_[l], ∑ i, (P *ᵥ z) i • b i = Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) G + (l : Om l) ^ N • ∑ i, w i • b i := by
    intro z G y0 hy0 heq
    obtain ⟨w, hw⟩ := hW (∑ s, z s • F s - G) (by
      have hLF : ∀ s, Finsupp.linearCombination ℤ_[l] (tup ρs) (F s) = bb s - y s := fun s => by rw [hFy s]; abel
      have : Finsupp.linearCombination ℤ_[l] (tup ρs) (∑ s, z s • F s - G) = y0 - ∑ s, z s • y s := by
        rw [map_sub, map_sum]
        simp only [map_smul, hLF, smul_sub, Finset.sum_sub_distrib, heq]
        abel
      rw [this]
      exact Submodule.sub_mem _ hy0 (Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (hy s)))
    refine ⟨w, ?_⟩
    rw [hPz, ← hw, map_sub]
    abel

  have h1T : (1 : Fin m → Matrix (Fin a) (Fin a) (Om l)) ∈ latT ρs t M := by rw [← tup_one ρs]; exact tup_mem_latT ρs t M 1
  obtain ⟨e', he'⟩ := hbbco 1 h1T
  have hrb : ∀ g (v : Fin d → ℤ_[l]), ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * ∑ s, v s • b s =
      ∑ i, (((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) *ᵥ v) i • b i := by
    intro g v
    have h2 := hR.equi g
    simp only [zOm_smul] at h2
    rw [Matrix.mul_sum]
    simp only [Matrix.mul_smul, h2, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  have hrmul : ∀ g h, ((r (g * h) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) = ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) := fun g h => by simp [map_mul, Units.val_mul]
  refine ⟨d', ρ', bb, e', P, hρ'c, fun s k i j => hentT _ (hbbmem s) k i j, hbbind, ?_, ?_, hbbmem, hbbco, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine Submodule.span_le.2 ?_ (hspT x hx)
    intro v hv
    obtain ⟨z, rfl⟩ := hbbco v hv
    refine Submodule.sum_mem _ fun s _ => ?_
    rw [show zOm l (z s) = algebraMap ℚ_[l] (Om l) (algebraMap ℤ_[l] ℚ_[l] (z s)) from rfl, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · intro k
    constructor
    · intro g j
      have := congrFun (hact g j) k
      simpa only [Pi.mul_apply, Finset.sum_apply, Pi.smul_apply, tup] using this
    · have := congrFun he'.symm k
      simpa only [Finset.sum_apply, Pi.smul_apply, Pi.one_apply] using this
  · intro z G y0 hy0 heq
    rw [sumZ_fin, sumZ] at heq
    obtain ⟨w, hw⟩ := hCar z G y0 hy0 heq
    exact ⟨w, by rw [sumZ_fin, sumZ, sumZ_fin]; exact hw⟩
  · constructor
    · intro g i j
      have hz := hact g j
      rw [sumZ_fin] at hz
      obtain ⟨w, hw⟩ := hCar (fun s => ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l]) s j)
        ((F j).mapDomain (g * ·)) (tup ρs g * y j) (hstL g _ (hy j)) (by
          rw [← hz, lc_translate _ (tup_mul ρs) g, hFy j, mul_add])
      rw [lc_translate _ hrmul g, ← hP j, hrb, lpow_smul, Finset.smul_sum, ← Finset.sum_add_distrib] at hw
      simp only [smul_smul, ← add_smul] at hw
      have := congrFun (coord_unique hind hw) i
      have e1 : (P * ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) i j =
          (P *ᵥ fun s => ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l]) s j) i := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      have e2 : (((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) * P) i j =
          (((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) *ᵥ fun s => P s j) i := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [Matrix.sub_apply, e1, e2, this, add_sub_cancel_left]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ hnN) _
    · have hb : ∀ j, ∃ f : Γ →₀ ℤ_[l], b j = Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) f := fun j => by
        obtain ⟨f, hf⟩ := hspan j
        exact ⟨f, by rw [hf, sumZ]⟩
      choose f hf using hb
      have hz : ∀ j, ∃ z : Fin d' → ℤ_[l], Finsupp.linearCombination ℤ_[l] (tup ρs) (f j) = ∑ s, z s • bb s := fun j => by
        obtain ⟨z, hz⟩ := hbbco _ (Submodule.mem_sup_left (Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨f j, by rw [Finsupp.linearCombination_apply]⟩) : Finsupp.linearCombination ℤ_[l] (tup ρs) (f j) ∈ latT ρs t M)
        exact ⟨z, by rw [hz, sumZ_fin]⟩
      choose z hz using hz
      refine ⟨Matrix.of fun s j => z j s, fun i j => ?_⟩
      obtain ⟨w, hw⟩ := hCar (z j) (f j) 0 (Submodule.zero_mem _) (by rw [add_zero, hz j])
      rw [← hf j, lpow_smul, Finset.smul_sum] at hw
      have hbj : b j = ∑ i, (1 : Matrix (Fin d) (Fin d) ℤ_[l]) i j • b i := by
        simp [Matrix.one_apply, ite_smul]
      rw [hbj, ← Finset.sum_add_distrib] at hw
      simp only [smul_smul, ← add_smul] at hw
      have := congrFun (coord_unique hind hw) i
      have e1 : (P * Matrix.of fun s j => z j s) i j = (P *ᵥ z j) i := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [Matrix.sub_apply, e1, this, add_sub_cancel_left]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ hnN) _
  · intro i
    obtain ⟨w, hw⟩ := hCar e' (Finsupp.single 1 1) 0 (Submodule.zero_mem _) (by
      rw [add_zero, Finsupp.linearCombination_single, one_smul, tup_one, he', sumZ_fin])
    rw [Finsupp.linearCombination_single, one_smul, map_one, Units.val_one, ← hR.one, sumZ_fin, lpow_smul,
      Finset.smul_sum, ← Finset.sum_add_distrib] at hw
    simp only [smul_smul, ← add_smul] at hw
    have := congrFun (coord_unique hind hw) i
    rw [Pi.sub_apply, this, add_sub_cancel_left]
    exact Dvd.dvd.mul_right (pow_dvd_pow _ hnN) _
  · intro s
    have := hM₁ M hM1 (F s) (y s) (hy s)
    rw [sumZ_fin, hP s, hFy s, ← sumZ, ← sumZ]
    exact this

end GlobalTheory.CovLayer

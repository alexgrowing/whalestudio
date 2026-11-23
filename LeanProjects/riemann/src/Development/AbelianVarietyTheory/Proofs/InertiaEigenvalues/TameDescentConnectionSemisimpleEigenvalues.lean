import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerEAddSmulMemEisensteinShiftGradedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemAnalyticFiltrationIffLatticeFiltrationAddStatement

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.LcSemisimple

theorem chain_aeval_mem : ∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V] (T : Module.End K V) (F : ℤ → Submodule K V) (lam : ℤ → K) (W W' : Submodule K V) (a b : ℤ) (J : Finset ℤ), a ≤ b → (∀ j, ∀ x ∈ F j, T x - lam j • x ∈ F (j + 1)) → (∀ x ∈ W, T x ∈ W) → (∀ x ∈ W', T x ∈ W') → W ≤ W' → F b ≤ W → W' ≤ F a → (∀ j, a ≤ j → j < b → j ∉ J → W' ⊓ F j ≤ W ⊓ F j ⊔ F (j + 1)) → ∀ x ∈ W', Polynomial.aeval T (∏ j ∈ J, (Polynomial.X - Polynomial.C (lam j))) x ∈ W := by
  intro K V _ _ _ T F lam W W' a b J hab hstep hW hW' hWW' hb ha hJ
  classical
  have hWq : ∀ (q : Polynomial K), ∀ w ∈ W, Polynomial.aeval T q w ∈ W := by
    intro q
    refine Polynomial.induction_on q (fun c w hw => ?_) (fun p q hp hq w hw => ?_)
      (fun n c ih w hw => ?_)
    · simpa [Algebra.algebraMap_eq_smul_one] using W.smul_mem c hw
    · simpa using W.add_mem (hp w hw) (hq w hw)
    · have e1 : Polynomial.aeval T (Polynomial.C c * Polynomial.X ^ (n + 1)) w =
          Polynomial.aeval T (Polynomial.C c * Polynomial.X ^ n) (T w) := by
        rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
      rw [e1]
      exact ih _ (hW w hw)
  have key : ∀ n : ℕ, (n : ℤ) ≤ b - a → ∀ J' : Finset ℤ,
      (∀ j ∈ J, b - n ≤ j → j < b → j ∈ J') → ∀ x ∈ W' ⊓ F (b - n),
      Polynomial.aeval T (∏ j ∈ J', (Polynomial.X - Polynomial.C (lam j))) x ∈ W := by
    intro n
    induction n with
    | zero =>
      intro _ J' _ x hx
      exact hWq _ x (hb (by simpa using (Submodule.mem_inf.1 hx).2))
    | succ n ih =>
      intro hn J' hJ' x hx
      obtain ⟨k, hk⟩ : ∃ k, k = b - ((n + 1 : ℕ) : ℤ) := ⟨_, rfl⟩
      rw [← hk] at hx
      have hk' : k = b - n - 1 := by rw [hk]; push_cast; ring
      have hk1 : k + 1 = b - n := by omega
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
      by_cases hkJ : k ∈ J'
      · rw [← Finset.prod_erase_mul J' _ hkJ, map_mul, Module.End.mul_apply]
        have hy : T x - lam k • x ∈ W' ⊓ F (b - n) :=
          Submodule.mem_inf.2 ⟨W'.sub_mem (hW' x hx1) (W'.smul_mem _ hx1), hk1 ▸ hstep k x hx2⟩
        have h2 : Polynomial.aeval T (Polynomial.X - Polynomial.C (lam k)) x = T x - lam k • x := by
          simp [Algebra.algebraMap_eq_smul_one]
        rw [h2]
        refine ih (by omega) (J'.erase k) (fun j hj h1 h3 => Finset.mem_erase.2 ⟨by omega,
          hJ' j hj (by push_cast; omega) h3⟩) _ hy
      · have hkJ0 : k ∉ J := fun h => hkJ (hJ' k h (by push_cast; omega) (by omega))
        have h1 := hJ k (by push_cast at hn; omega) (by omega) hkJ0 (Submodule.mem_inf.2 ⟨hx1, hx2⟩)
        obtain ⟨w, hw, f, hf, rfl⟩ := Submodule.mem_sup.1 h1
        rw [map_add]
        have hf' : f ∈ W' ⊓ F (b - n) := by
          refine Submodule.mem_inf.2 ⟨?_, hk1 ▸ hf⟩
          simpa using W'.sub_mem hx1 (hWW' (Submodule.mem_inf.1 hw).1)
        exact W.add_mem (hWq _ w (Submodule.mem_inf.1 hw).1)
          (ih (by omega) J' (fun j hj h3 h4 => hJ' j hj (by push_cast; omega) h4) f hf')
  intro x hx
  refine key (b - a).toNat (by omega) J (fun j hj _ _ => hj) x (Submodule.mem_inf.2 ⟨hx, ?_⟩)
  rw [show b - ((b - a).toNat : ℤ) = a by omega]
  exact ha hx

theorem aeval_intertwine {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] (g : V →ₗ[K] V') (f : Module.End K V) (f' : Module.End K V')
    (h : ∀ x, g (f x) = f' (g x)) (q : Polynomial K) (x : V) : g (Polynomial.aeval f q x) = Polynomial.aeval f' q (g x) := by
  suffices H : ∀ x, g (Polynomial.aeval f q x) = Polynomial.aeval f' q (g x) from H x
  refine Polynomial.induction_on q (fun c x => ?_) (fun p q hp hq x => ?_) (fun n c ih x => ?_)
  · simp [Algebra.algebraMap_eq_smul_one]
  · simp [hp, hq]
  · have e1 : Polynomial.aeval f (Polynomial.C c * Polynomial.X ^ (n + 1)) x = Polynomial.aeval f (Polynomial.C c * Polynomial.X ^ n) (f x) := by
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    have e2 : Polynomial.aeval f' (Polynomial.C c * Polynomial.X ^ (n + 1)) (g x) = Polynomial.aeval f' (Polynomial.C c * Polynomial.X ^ n) (f' (g x)) := by
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    rw [e1, e2, ih, h]

theorem ker_aeval_prod {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) (v : ℤ → K) (hv : Function.Injective v) (s : Finset ℤ) :
    LinearMap.ker (Polynomial.aeval f (∏ i ∈ s, (Polynomial.X - Polynomial.C (v i)))) = ⨆ i ∈ s, f.eigenspace (v i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
    exact LinearMap.ker_id
  · intro a s ha ih
    rw [Finset.prod_insert ha, ← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime, ih, Finset.iSup_insert]
    · congr 1
      rw [Module.End.eigenspace_def, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    · exact IsCoprime.prod_right fun i hi =>
        (Polynomial.pairwise_coprime_X_sub_C hv) (fun h => ha (h ▸ hi))

theorem semisimple_of_aeval {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) (s : Finset ℤ) (v : ℤ → K) (hv : Function.Injective v)
    (h : Polynomial.aeval f (∏ n ∈ s, (Polynomial.X - Polynomial.C (v n))) = 0) :
    f.IsSemisimple ∧ (∀ μ, f.HasEigenvalue μ → ∃ n ∈ s, μ = v n) ∧
      ⨆ n ∈ s, f.eigenspace (v n) = ⊤ := by
  refine ⟨Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    ((Polynomial.separable_prod_X_sub_C_iff'.2 hv.injOn).squarefree) h, fun μ hμ => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
    have h1 := Module.End.aeval_apply_of_hasEigenvector (p := ∏ n ∈ s, (Polynomial.X - Polynomial.C (v n))) hx
    rw [h, LinearMap.zero_apply, eq_comm, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h1
      obtain ⟨n, hn, h2⟩ := h1
      exact ⟨n, hn, by simpa [sub_eq_zero] using h2⟩
    · exact absurd h1 hx.2
  · rw [← ker_aeval_prod f v hv s, h, LinearMap.ker_zero]

theorem lc_semisimple : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ U : Finset ℤ, D.jumps ⊆ U → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Semisimple D U := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D U hU
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have he0 : (e : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne e)
  set Lan := D.ext (Rpi O K l e) with hLan
  let F : ℤ → Submodule K (Vec K a ι) := fun j => (shiftE l e j Lan).restrictScalars K
  let lam : ℤ → K := fun j => ((-j * e * l : ℤ) : K)
  let J : Finset ℤ := (GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.shifts U η).image (fun n => -n)
  have hp : ∏ j ∈ J, (Polynomial.X - Polynomial.C (lam j)) =
      ∏ n ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.shifts U η, (Polynomial.X - Polynomial.C (((n * e * l : ℤ) : K))) := by
    rw [Finset.prod_image (fun x _ y _ h => neg_injective h)]
    simp [lam]
  have hstep : ∀ j, ∀ x ∈ F j, D.EN x - lam j • x ∈ F (j + 1) := by
    intro j x hx
    have h1 := GlobalTheory.T.eulerE_add_smul_mem_eisenstein_shift_graded O K l e a ι η H D j x hx
    have h2 : D.EN x - lam j • x = D.EN x + ((j * e * l : ℤ) : K) • x := by
      rw [sub_eq_add_neg, ← neg_smul]
      congr 2
      simp only [lam]
      push_cast
      ring
    rw [h2]
    exact h1
  have hb : F η ≤ D.Man := by
    intro x hx
    have h1 := D.smul_mem_Mext (A_le_Rpi l e) ((mem_shiftE).1 hx)
    rwa [smul_smul, E_pow_mul_Ezpow_neg, one_smul] at h1
  have ha : divE l e η D.Man ≤ F (-((η : ℤ) + H)) := by
    intro x hx
    have h1 := D.smul_mem_ext_of_basis (c := E K l e ^ H) (fun i => D.lower _ (D.bas_mem_M i))
      (A_le_Rpi l e) ((mem_divE).1 hx)
    show Ezpow K l e (-(-((η : ℤ) + H))) • x ∈ Lan
    rwa [neg_neg, Ezpow_add, Ezpow_natCast, Ezpow_natCast, mul_comm, mul_smul]
  have hJ : ∀ j, -((η : ℤ) + H) ≤ j → j < η → j ∉ J →
      divE l e η D.Man ⊓ F j ≤ D.Man ⊓ F j ⊔ F (j + 1) := by
    intro j _ _ hj x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    have hx1' : E K l e ^ η • x ∈ D.Man := hx1
    have hx2' : Ezpow K l e (-j) • x ∈ Lan := hx2
    have hnj : ∀ i, -j - η ≤ i → i ≤ -j - 1 → D.filL (i + 1) = D.filL i := by
      intro i h1 h2
      by_contra hne
      have hi : i ∈ U := hU (show i ∈ D.jumps from hne)
      exact hj (Finset.mem_image.2 ⟨-j, GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.mem_shifts.2
        ⟨i, hi, -j - i, ⟨by omega, by omega⟩, by ring⟩, neg_neg j⟩)
    have hFA : ∀ i, D.filL (i + 1) = D.filL i → ∀ y,
        y ∈ (Lan ⊓ shiftE l e i (D.Mext (Rpi O K l e))) ⊔ shiftE l e 1 Lan →
        y ∈ (Lan ⊓ shiftE l e (i + 1) (D.Mext (Rpi O K l e))) ⊔ shiftE l e 1 Lan := by
      intro i h y hy
      rw [GlobalTheory.T.mem_analytic_filtration_iff_lattice_filtration_add O K l e a ι D.toPhiMod i y] at hy
      rw [GlobalTheory.T.mem_analytic_filtration_iff_lattice_filtration_add O K l e a ι D.toPhiMod (i + 1) y, h]
      exact hy
    have hchain : ∀ k : ℕ, k ≤ η → ∀ y,
        y ∈ (Lan ⊓ shiftE l e (-j - η) (D.Mext (Rpi O K l e))) ⊔ shiftE l e 1 Lan →
        y ∈ (Lan ⊓ shiftE l e (-j - η + k) (D.Mext (Rpi O K l e))) ⊔ shiftE l e 1 Lan := by
      intro k
      induction k with
      | zero => intro _ y hy; simpa using hy
      | succ k ih =>
        intro hk y hy
        have h1 := hFA (-j - η + k) (hnj _ (by omega) (by omega)) y (ih (by omega) y hy)
        rwa [show -j - (η : ℤ) + k + 1 = -j - η + ((k + 1 : ℕ) : ℤ) by push_cast; ring] at h1
    set z := Ezpow K l e (-j) • x with hz
    have hz1 : z ∈ (Lan ⊓ shiftE l e (-j - η) (D.Mext (Rpi O K l e))) ⊔ shiftE l e 1 Lan := by
      refine Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hx2', ?_⟩)
      rw [mem_shiftE, hz, smul_smul, ← Ezpow_add, show -(-j - (η : ℤ)) + -j = η by ring,
        Ezpow_natCast]
      exact hx1'
    have hz2 := hchain η le_rfl z hz1
    rw [show -j - (η : ℤ) + η = -j by ring] at hz2
    obtain ⟨w, hw, f, hf, hwf⟩ := Submodule.mem_sup.1 hz2
    obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.1 hw
    have hxz : x = Ezpow K l e j • w + Ezpow K l e j • f := by
      rw [← smul_add, hwf, hz, smul_smul, ← Ezpow_add, add_neg_cancel]
      simp [Ezpow]
    rw [hxz]
    refine Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨?_, ?_⟩) ?_
    · have h1 : Ezpow K l e (-(-j)) • w ∈ D.Mext (Rpi O K l e) := (mem_shiftE).1 hw2
      rwa [neg_neg] at h1
    · show Ezpow K l e (-j) • Ezpow K l e j • w ∈ Lan
      rwa [smul_smul, Ezpow_neg_mul, one_smul]
    · show Ezpow K l e (-(j + 1)) • Ezpow K l e j • f ∈ Lan
      rw [smul_smul, ← Ezpow_add, show -(j + 1) + j = -1 by ring]
      exact (mem_shiftE).1 hf
  have key := chain_aeval_mem D.EN F lam D.Man (divE l e η D.Man) (-((η : ℤ) + H)) η J (by omega) hstep
    (fun x hx => D.EN_mem_Man hx) (fun x hx => D.EN_mem_divE hx)
    (fun x hx => (mem_divE).2 (D.smul_mem_Man (pow_mem (E_mem l e _) η) hx)) hb ha hJ
  rw [hp] at key
  have hann : ∀ w ∈ D.PolEta η, Polynomial.aeval D.Lc
      (∏ n ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.shifts U η, (Polynomial.X - Polynomial.C (((n * e * l : ℤ) : K)))) w = 0 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← aeval_intertwine D.cls D.EN D.Lc (fun _ => rfl)]
    exact (D.cls_eq_zero_iff).2 (key y hy)
  have hZ : Polynomial.aeval D.LcZ
      (∏ n ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.shifts U η, (Polynomial.X - Polynomial.C (((n * e * l : ℤ) : K)))) = 0 := by
    ext w
    have h1 := aeval_intertwine D.Zl.subtype D.LcZ D.Lc (fun _ => rfl)
      (∏ n ∈ GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.shifts U η, (Polynomial.X - Polynomial.C (((n * e * l : ℤ) : K)))) w
    simp only [Submodule.subtype_apply] at h1
    rw [LinearMap.zero_apply, Submodule.coe_zero, h1]
    exact hann _ (Submodule.mem_inf.1 w.2).1
  have hinj : Function.Injective (fun n : ℤ => ((n * e * l : ℤ) : K)) := by
    intro m n h
    have h1 : m * e * l = n * e * l := Int.cast_injective h
    exact mul_right_cancel₀ he0 (mul_right_cancel₀ hl0 h1)
  exact semisimple_of_aeval D.LcZ _ _ hinj hZ

end GlobalTheory.LcSemisimple

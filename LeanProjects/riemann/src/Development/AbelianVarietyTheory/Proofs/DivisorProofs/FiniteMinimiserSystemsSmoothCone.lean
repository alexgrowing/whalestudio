import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLatticeQuadraticSumGeDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DicksonExistsFiniteSubfamilyBelow
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.MinSys

open Matrix

theorem finite_of_pos {r : ℕ} (G : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hs : ∀ a b, G a b = G b a)
    (hn : ∀ x, 0 ≤ G x x) (hp : ∀ x, x ≠ 0 → 0 < G x x) (B : ℤ) : {x | G x x ≤ B}.Finite := by
  classical
  set S : Matrix (Fin r) (Fin r) ℤ := LinearMap.BilinForm.toMatrix' G with hS
  have hGS : ∀ x, G x x = x ⬝ᵥ S *ᵥ x := fun x => by
    rw [← Matrix.toBilin'_apply', hS, Matrix.toBilin'_toMatrix']
  have hdet : S.det ≠ 0 := by
    intro h
    obtain ⟨z, hz, hSz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    have h1 := hp z hz
    rw [hGS, hSz, dotProduct_zero] at h1
    exact lt_irrefl _ h1
  have hpsd : (S.map (Int.cast : ℤ → ℝ)).PosSemidef := by
    have h := GlobalTheory.Poinc.QWDom.gram_posSemidef G hs hn (fun u => Pi.single u 1)
    convert h using 1
    ext u v
    simp [hS, LinearMap.BilinForm.toMatrix'_apply]
  have hpd : (S.map (Int.cast : ℤ → ℝ)).PosDef := by
    rw [hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← Int.cast_det]
    exact_mod_cast hdet
  obtain ⟨c, hc, hP⟩ := GlobalTheory.Poinc.QWDom.exists_pos_posSemidef_sub_smul_one hpd
  have key : ∀ x : Fin r → ℤ, c * ∑ u, ((x u : ℝ)) ^ 2 ≤ (G x x : ℝ) := by
    intro x
    have h := hP.dotProduct_mulVec_nonneg (fun u => (x u : ℝ))
    simp only [star_trivial, sub_mulVec, dotProduct_sub, sub_nonneg] at h
    have e1 : (fun u => (x u : ℝ)) ⬝ᵥ (S.map (Int.cast : ℤ → ℝ)) *ᵥ (fun u => (x u : ℝ)) = ((x ⬝ᵥ S *ᵥ x : ℤ) : ℝ) := by
      simp [dotProduct, mulVec, Matrix.map_apply]
    have e2 : (fun u => (x u : ℝ)) ⬝ᵥ (c • (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ (fun u => (x u : ℝ)) =
        c * ∑ u, ((x u : ℝ)) ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Matrix.one_apply, Finset.mul_sum, sq]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, e2] at h
    rw [hGS]
    exact h
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (B : ℝ) / c ≤ M := exists_nat_ge _
  rw [div_le_iff₀ hc] at hM
  refine (Set.Finite.pi' (fun _ : Fin r => Set.finite_Icc (-(M : ℤ)) M)).subset fun x hx => ?_
  intro u
  have hxB : (G x x : ℝ) ≤ B := by exact_mod_cast hx
  have h1 : ((x u : ℝ)) ^ 2 ≤ ∑ v, ((x v : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun v => ((x v : ℝ)) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ u)
  have h2 : c * ((x u : ℝ)) ^ 2 ≤ c * M := by
    have := (mul_le_mul_of_nonneg_left h1 hc.le).trans ((key x).trans hxB)
    linarith
  have h3 : ((x u : ℝ)) ^ 2 ≤ M := le_of_mul_le_mul_left h2 hc
  have h4 : (x u) ^ 2 ≤ (M : ℤ) := by exact_mod_cast h3
  have h5 := Int.le_self_sq (x u)
  have h6 := Int.le_self_sq (-(x u))
  rw [neg_sq] at h6
  exact ⟨by linarith, by linarith⟩

theorem qW_sum_nsmul {s m : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (cf : Fin m → ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) (y : Fin s → X) :
    qW W (∑ j, cf j • γ j) y = ∑ j, (cf j : ℤ) * qW W (γ j) y := by
  simp only [qW, LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem qW_nsmul {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (k : ℕ)
    (b : LinearMap.BilinForm ℤ X) (y : Fin s → X) : qW W (k • b) y = (k : ℤ) * qW W b y := by
  simp only [qW, LinearMap.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

theorem finite_minimiser_systems : ∀ (φ : InvFun ℤ), ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)), IsCone id φ γ → (∀ x, x ≠ 0 → 0 < ∑ j, γ j x x) → ∃ Sμ : Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (k : ℕ) (cf : Fin m → ℕ), 0 < k → (∀ j, 0 < cf j) → k • b = ∑ j, cf j • γ j → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α) → μ ∈ Sμ := by
  intro φ W hW N _ _ r m γ hC hdef
  classical
  obtain ⟨c0, hc0, hge⟩ := GlobalTheory.Poinc.QWDom.qW_ge 8 W hW
  have hsym : ∀ j a b, γ j a b = γ j b a := fun j => (hC.mem j).1
  have hnn : ∀ j y, 0 ≤ γ j y y := hC.nonneg
  have hq0 : ∀ j (α : Fin 8 → Fin r → ℤ), 0 ≤ qW W (γ j) α := fun j α => by
    have h := hge (Fin r → ℤ) (γ j) (hsym j) (hnn j) α
    have h1 : (0 : ℝ) ≤ c0 * ((∑ u, γ j (α u) (α u) : ℤ) : ℝ) :=
      mul_nonneg hc0.le (by exact_mod_cast Finset.sum_nonneg fun u _ => hnn j (α u))
    exact_mod_cast h1.trans h
  set G : LinearMap.BilinForm ℤ (Fin r → ℤ) := ∑ j, γ j with hG
  have hGapp : ∀ a b, G a b = ∑ j, γ j a b := fun a b => by simp [hG, LinearMap.sum_apply]
  have hGsym : ∀ a b, G a b = G b a := fun a b => by simp only [hGapp, hsym _ a b]
  have hGnn : ∀ y, 0 ≤ G y y := fun y => by rw [hGapp]; exact Finset.sum_nonneg fun j _ => hnn j y
  have hGpos : ∀ x, x ≠ 0 → 0 < G x x := fun x hx => by rw [hGapp]; exact hdef x hx
  have hGq : ∀ α, qW W G α = ∑ j, qW W (γ j) α := fun α => by
    have := qW_sum_nsmul W (fun _ => 1) γ α
    simpa [hG] using this
  have hfinG : ∀ B : ℤ, {α : Fin 8 → Fin r → ℤ | qW W G α ≤ B}.Finite := by
    intro B
    obtain ⟨M, hM⟩ : ∃ M : ℕ, (B : ℝ) / c0 ≤ M := exists_nat_ge _
    rw [div_le_iff₀ hc0] at hM
    refine (Set.Finite.pi' fun _ : Fin 8 => finite_of_pos G hGsym hGnn hGpos M).subset fun α hα u => ?_
    have h := hge (Fin r → ℤ) G hGsym hGnn α
    have h1 : G (α u) (α u) ≤ ∑ v, G (α v) (α v) :=
      Finset.single_le_sum (f := fun v => G (α v) (α v)) (fun v _ => hGnn (α v)) (Finset.mem_univ u)
    have hα' : (qW W G α : ℝ) ≤ B := by exact_mod_cast hα
    have h1' : ((G (α u) (α u) : ℤ) : ℝ) ≤ ((∑ v, G (α v) (α v) : ℤ) : ℝ) := by exact_mod_cast h1
    have h2 : c0 * (G (α u) (α u) : ℝ) ≤ c0 * M := by
      have := (mul_le_mul_of_nonneg_left h1' hc0.le).trans (h.trans hα')
      linarith
    have h3 : (G (α u) (α u) : ℝ) ≤ M := le_of_mul_le_mul_left h2 hc0
    show G (α u) (α u) ≤ ((M : ℕ) : ℤ)
    exact_mod_cast h3
  let T : (Fin 8 → Fin r → ZMod N) → Type := fun c =>
    {α : Fin 8 → Fin r → ℤ // ∀ u i, ((α u i : ℤ) : ZMod N) = c u i}
  have hD : ∀ c, ∃ F : Finset (T c), ∀ α : T c, ∃ β ∈ F,
      (fun j => (qW W (γ j) β.1).toNat) ≤ (fun j => (qW W (γ j) α.1).toNat) :=
    fun c => GlobalTheory.dickson_finite_below_every m (fun (α : T c) j => (qW W (γ j) α.1).toNat)
  choose F hF using hD
  let Bd : (Fin 8 → Fin r → ZMod N) → ℤ := fun c => ∑ β ∈ F c, qW W G β.1
  have hfin : {μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ) | ∀ c, μ c ∈ {α | qW W G α ≤ Bd c}}.Finite :=
    Set.Finite.pi' fun c => hfinG (Bd c)
  refine ⟨hfin.toFinset, fun b k cf hk hcf hkb μ hμ hmin => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  intro c
  obtain ⟨β, hβF, hβ⟩ := hF c ⟨μ c, hμ c⟩
  have hle : ∀ j, qW W (γ j) β.1 ≤ qW W (γ j) (μ c) := fun j => by
    have h1 : (qW W (γ j) β.1).toNat ≤ (qW W (γ j) (μ c)).toNat := hβ j
    have := hq0 j β.1
    have := hq0 j (μ c)
    omega
  have hkq : ∀ α, (k : ℤ) * qW W b α = ∑ j, (cf j : ℤ) * qW W (γ j) α := fun α => by
    rw [← qW_nsmul, hkb, qW_sum_nsmul]
  have h2 : ∑ j, (cf j : ℤ) * qW W (γ j) (μ c) ≤ ∑ j, (cf j : ℤ) * qW W (γ j) β.1 := by
    rw [← hkq, ← hkq]
    exact mul_le_mul_of_nonneg_left (hmin c β.1 β.2) (by positivity)
  have h3 : ∀ j, qW W (γ j) (μ c) - qW W (γ j) β.1 ≤
      (cf j : ℤ) * qW W (γ j) (μ c) - (cf j : ℤ) * qW W (γ j) β.1 := fun j => by
    have h4 := hle j
    have h5 : (1 : ℤ) ≤ cf j := by exact_mod_cast hcf j
    nlinarith
  have h6 : ∑ j, qW W (γ j) (μ c) ≤ ∑ j, qW W (γ j) β.1 := by
    have h7 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h3 j
    simp only [Finset.sum_sub_distrib] at h7
    linarith
  have h8 : qW W G β.1 ≤ Bd c :=
    Finset.single_le_sum (f := fun β : T c => qW W G β.1)
      (fun β _ => by rw [hGq]; exact Finset.sum_nonneg fun j _ => hq0 j β.1) hβF
  rw [hGq] at h8 ⊢
  linarith

end GlobalTheory.Poinc.MinSys

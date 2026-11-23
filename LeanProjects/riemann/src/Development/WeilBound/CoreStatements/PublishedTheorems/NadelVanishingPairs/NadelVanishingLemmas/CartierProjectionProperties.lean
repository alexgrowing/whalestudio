import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EulerContractionCartanFormula
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierProjectionPthPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCoordinateWedgeLinearIndependentSpanEqTopStatement

set_option autoImplicit false

noncomputable section

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.CartierHomotopy

variable {K : Type} [Field K]

theorem extD_extD (η : abelian₂ K) : extD K (extD K η) = 0 := by
  rw [extD_apply, extD_apply]
  exact CechDR.dDR_dDR (x := η)

theorem pow_act (A : AddMonoid.End (abelian₂ K)) (B : AddMonoid.End K) (w : abelian₂ K)
    (h : ∀ c, A (c • w) = B c • w) (k : ℕ) (c : K) : (A ^ k) (c • w) = (B ^ k) c • w := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ']
    show A ((A ^ k) (c • w)) = B ((B ^ k) c) • w
    rw [ih, h]

theorem one_sub_pow_act (A : AddMonoid.End (abelian₂ K)) (B : AddMonoid.End K) (w : abelian₂ K)
    (h : ∀ c, A (c • w) = B c • w) (k : ℕ) (c : K) :
    (1 - A ^ k) (c • w) = (1 - B ^ k) c • w := by
  change c • w - (A ^ k) (c • w) = (c - (B ^ k) c) • w
  rw [pow_act A B w h, sub_smul]

theorem prod_act {n : ℕ} (A : Fin n → AddMonoid.End (abelian₂ K)) (B : Fin n → AddMonoid.End K) (w : abelian₂ K)
    (hAB : ∀ i c, A i (c • w) = B i c • w) (L : List (Fin n)) (c : K) :
    (L.map A).prod (c • w) = (L.map B).prod c • w := by
  induction L generalizing c with
  | nil => rfl
  | cons i L ih =>
    simp only [List.map_cons, List.prod_cons]
    change A i ((L.map A).prod (c • w)) = B i ((L.map B).prod c) • w
    rw [ih, hAB]

theorem dK_pow_char (p : ℕ) [CharP K p] (g : K) : dK (g ^ p) = 0 := by
  unfold dK
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

end GlobalTheory.CartierHomotopy

namespace GlobalTheory.CartierHomotopy

private theorem dDR_iota_dlog_eq_zero (K : Type) [Field K] (u : Kˣ) :
    CechDR.dDR ℤ K (ExteriorAlgebra.ι K (dlog u)) = 0 := by
  have h1 : (ExteriorAlgebra.ι K (dlog u) : CechDR.DR ℤ K) =
      ((u : K)⁻¹) • CechDR.ι1 (KaehlerDifferential.D ℤ K (u : K)) := by
    show ExteriorAlgebra.ι K (((u⁻¹ : Kˣ) : K) • KaehlerDifferential.D ℤ K (u : K)) = _
    rw [map_smul, Units.val_inv_eq_inv_val]
  rw [h1, CechDR.dDR_smul, CechDR.dDR_D, smul_zero, add_zero, Derivation.leibniz_inv, map_smul,
    smul_mul_assoc]
  have h2 : (CechDR.ι1 (KaehlerDifferential.D ℤ K (u : K)) : CechDR.DR ℤ K) *
      CechDR.ι1 (KaehlerDifferential.D ℤ K (u : K)) = 0 := ExteriorAlgebra.ι_sq_zero _
  rw [h2, smul_zero]

private theorem dDR_prod_dlog_eq_zero_and_euler_contraction (K : Type) [Field K] {n : ℕ} (x : Fin n → Kˣ) (I : Finset (Fin n)) :
    extD K (logWedge x I) = 0 := by
  rw [extD_apply]
  show CechDR.dDR ℤ K (((I.sort (· ≤ ·)).map (fun j => ExteriorAlgebra.ι K (dlog (x j)))).prod) = 0
  generalize I.sort (· ≤ ·) = l
  induction l with
  | nil =>
    have h := CechDR.dDR_algebraMap (R := ℤ) (B := K) 1
    rw [map_one, Derivation.map_one_eq_zero, map_zero] at h
    exact h
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [CechDR.dDR_mul, ih, dDR_iota_dlog_eq_zero, mul_zero, zero_mul, add_zero]

private theorem exists_dual_basis_dlog_of_isCoord (K : Type) [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) :
    ∃ φ : Fin n → Module.Dual K Ω[K⁄ℤ], (∀ i j, φ i (dlog (x j)) = if i = j then 1 else 0) ∧
      ∀ v, ∑ i, φ i v • dlog (x i) = v := by
  refine ⟨fun i => (dlogBasis x hx).coord i, ?_, ?_⟩
  · intro i j
    show (dlogBasis x hx).coord i (dlog (x j)) = _
    rw [← dlogBasis_apply x hx j, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
    by_cases h : i = j
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (Ne.symm h), if_neg h]
  · intro v
    conv_rhs => rw [← (dlogBasis x hx).sum_repr v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dlogBasis_apply]
    rfl

private theorem addMonoidEnd_pow_mem_of_mapsTo {M : Type} [AddCommGroup M] (f : AddMonoid.End M) (S : AddSubgroup M)
    (hf : ∀ η ∈ S, f η ∈ S) (k : ℕ) : ∀ η ∈ S, (f ^ k) η ∈ S := by
  induction k with
  | zero => exact fun η hη => hη
  | succ k ih =>
    intro η hη
    rw [pow_succ']
    exact hf _ (ih η hη)

private theorem homotopy_maps_filtration_of_list_maps {M : Type} [AddCommGroup M] (d : AddMonoid.End M)
    (l : List (AddMonoid.End M × AddMonoid.End M))
    (hX : ∀ a ∈ l, a.1 = d * a.2 + a.2 * d) (hc : ∀ a ∈ l, Commute d a.1) :
    ∃ h : AddMonoid.End M, 1 - (l.map (fun a => 1 - a.1)).prod = d * h + h * d ∧
      ∀ T : ℕ → AddSubgroup M, (∀ a ∈ l, (∀ q, ∀ η ∈ T (q + 1), a.2 η ∈ T q) ∧
        (∀ η ∈ T 0, a.2 η = 0) ∧ ∀ q, ∀ η ∈ T q, a.1 η ∈ T q) →
      (∀ q, ∀ η ∈ T (q + 1), h η ∈ T q) ∧ (∀ η ∈ T 0, h η = 0) ∧
        ∀ q, ∀ η ∈ T q, ((l.map (fun a => 1 - a.1)).prod : AddMonoid.End M) η ∈ T q := by
  induction l with
  | nil =>
    refine ⟨0, by simp, fun T _ => ⟨fun q η _ => zero_mem _, fun _ _ => rfl, fun q η hη => hη⟩⟩
  | cons a l ih =>
    obtain ⟨h', hh', hT'⟩ := ih (fun b hb => hX b (List.mem_cons_of_mem _ hb))
      (fun b hb => hc b (List.mem_cons_of_mem _ hb))
    have hPc : Commute d (l.map (fun a => 1 - a.1)).prod := by
      apply Commute.list_prod_right
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨b, hb, rfl⟩ := hy
      exact (Commute.one_right d).sub_right (hc b (List.mem_cons_of_mem _ hb))
    generalize hP : (l.map (fun a => 1 - a.1)).prod = P at hh' hT' hPc
    have hXa := hX a List.mem_cons_self
    refine ⟨h' + a.2 * P, ?_, ?_⟩
    · simp only [List.map_cons, List.prod_cons, hP]
      have e1 : a.2 * d * P = a.2 * P * d := by rw [mul_assoc, hPc.eq, ← mul_assoc]
      calc (1 : AddMonoid.End M) - (1 - a.1) * P = (1 - P) + a.1 * P := by noncomm_ring
        _ = d * h' + h' * d + (d * a.2 * P + a.2 * d * P) := by rw [hh', hXa]; noncomm_ring
        _ = d * (h' + a.2 * P) + (h' + a.2 * P) * d := by rw [e1]; noncomm_ring
    · intro T hT
      obtain ⟨h1, h2, h3⟩ := hT' T (fun b hb => hT b (List.mem_cons_of_mem _ hb))
      obtain ⟨a1, a2, a3⟩ := hT a List.mem_cons_self
      refine ⟨?_, ?_, ?_⟩
      · intro q η hη
        show h' η + a.2 (P η) ∈ T q
        exact add_mem (h1 q η hη) (a1 q _ (h3 (q + 1) η hη))
      · intro η hη
        show h' η + a.2 (P η) = 0
        rw [h2 η hη, a2 _ (h3 0 η hη), add_zero]
      · intro q η hη
        simp only [List.map_cons, List.prod_cons, hP]
        show P η - a.1 (P η) ∈ T q
        exact sub_mem (h3 q η hη) (a3 q _ (h3 q η hη))

theorem cartier_projector_homotopic : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ) (x : Fin n → Kˣ), IsCoord x → ∃ (h Q : abelian₂ K →+ abelian₂ K) (π : K →+ K), (∀ η, η - Q η = extD K (h η) + h (extD K η)) ∧ (∀ c I, Q (c • logWedge x I) = π c • logWedge x I) ∧ (∀ c, ∃ g : K, π c = g ^ p) ∧ (∀ g : K, π (g ^ p) = g ^ p) ∧ (∀ η, Q (extD K η) = 0) ∧ ∀ T : ℕ → AddSubgroup (abelian₂ K), (∀ q, ∀ η ∈ T q, extD K η ∈ T (q + 1)) → (∀ i θ, IsEulerContraction x i θ → (∀ q, ∀ η ∈ T (q + 1), θ η ∈ T q) ∧ ∀ η ∈ T 0, θ η = 0) → (∀ q, ∀ η ∈ T (q + 1), h η ∈ T q) ∧ (∀ η ∈ T 0, h η = 0) ∧ ∀ q, ∀ η ∈ T q, Q η ∈ T q := by
  intro K _ p _ _ n x hx
  have hpr : p.Prime := Fact.out
  obtain ⟨m, hm⟩ : ∃ m, p - 1 = m + 1 := ⟨p - 2, by have := hpr.two_le; omega⟩
  obtain ⟨φ, hφ, hsum⟩ := exists_dual_basis_dlog_of_isCoord K x hx
  let D : Fin n → Derivation ℤ K K := fun i => (φ i).compDer (KaehlerDifferential.D ℤ K)
  have hDapp : ∀ i c, D i c = φ i (KaehlerDifferential.D ℤ K c) := fun _ _ => rfl
  have hd : ∀ c, dK c = ∑ j, D j c • dlog (x j) := fun c => (hsum _).symm
  have hD : ∀ i j, D i (x j : K) = if i = j then (x j : K) else 0 := by
    intro i j
    rw [hDapp]
    have e : KaehlerDifferential.D ℤ K (x j : K) = (x j : K) • dlog (x j) := by
      show _ = (x j : K) • (((x j)⁻¹ : Kˣ) : K) • KaehlerDifferential.D ℤ K (x j : K)
      rw [smul_smul, Units.mul_inv, one_smul]
    rw [e, map_smul, hφ, smul_eq_mul]
    split_ifs <;> simp
  let θ : Fin n → (abelian₂ K →ₗ[K] abelian₂ K) := fun i =>
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K Ω[K⁄ℤ])) (φ i)
  have hθ : ∀ i, IsEulerContraction x i (θ i) := by
    intro i
    refine ⟨CliffordAlgebra.contractLeft_one _ _, ?_, ?_⟩
    · intro v η
      show CliffordAlgebra.contractLeft (φ i) (CliffordAlgebra.ι 0 v * η) =
        CliffordAlgebra.contractLeft (φ i) (CliffordAlgebra.ι 0 v) * η -
          CliffordAlgebra.ι 0 v * CliffordAlgebra.contractLeft (φ i) η
      rw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι, Algebra.smul_def]
    · intro j
      show CliffordAlgebra.contractLeft (φ i) (CliffordAlgebra.ι 0 (dlog (x j))) = _
      rw [CliffordAlgebra.contractLeft_ι, hφ]
      by_cases hij : i = j
      · subst hij
        simp
      · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]
  let dE : AddMonoid.End (abelian₂ K) := extD K
  let θE : Fin n → AddMonoid.End (abelian₂ K) := fun i => (θ i).toAddMonoidHom
  let LE : Fin n → AddMonoid.End (abelian₂ K) := fun i => dE * θE i + θE i * dE
  have hdd : dE * dE = 0 := AddMonoidHom.ext fun η => extD_extD η
  have hcomm : ∀ i, Commute dE (LE i) := by
    intro i
    show dE * (dE * θE i + θE i * dE) = (dE * θE i + θE i * dE) * dE
    rw [mul_add, add_mul, ← mul_assoc, hdd, zero_mul, mul_assoc (θE i), hdd, mul_zero, zero_add,
      add_zero, mul_assoc]
  let pairs : List (AddMonoid.End (abelian₂ K) × AddMonoid.End (abelian₂ K)) :=
    List.ofFn fun i => (LE i ^ (p - 1), θE i * LE i ^ m)
  have hX : ∀ a ∈ pairs, a.1 = dE * a.2 + a.2 * dE := by
    intro a ha
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    show LE i ^ (p - 1) = dE * (θE i * LE i ^ m) + θE i * LE i ^ m * dE
    rw [hm, pow_succ', mul_assoc (θE i), ((hcomm i).pow_right m).eq.symm]
    show (dE * θE i + θE i * dE) * LE i ^ m = _
    noncomm_ring
  have hc : ∀ a ∈ pairs, Commute dE a.1 := by
    intro a ha
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact (hcomm i).pow_right _
  obtain ⟨h, hh, hT⟩ := homotopy_maps_filtration_of_list_maps dE pairs hX hc
  let Q : AddMonoid.End (abelian₂ K) := (pairs.map (fun a => 1 - a.1)).prod
  let Dend : Fin n → AddMonoid.End K := fun i => (D i).toLinearMap.toAddMonoidHom
  let π : AddMonoid.End K := (List.ofFn fun i => 1 - Dend i ^ (p - 1)).prod
  obtain ⟨hπ1, hπ2⟩ := ProjFn.projector_pthPow K p n x D hx hd hD π rfl
  have hQeq : Q =
      ((List.finRange n).map fun i => 1 - LE i ^ (p - 1)).prod := by
    show ((List.ofFn fun i => (LE i ^ (p - 1), θE i * LE i ^ m)).map (fun a => 1 - a.1)).prod = _
    rw [List.map_ofFn, List.ofFn_eq_map]
    rfl
  have hπeq : π = ((List.finRange n).map fun i => 1 - Dend i ^ (p - 1)).prod := by
    show (List.ofFn fun i => 1 - Dend i ^ (p - 1)).prod = _
    rw [List.ofFn_eq_map]
  have hLact : ∀ I i c, LE i (c • logWedge x I) = Dend i c • logWedge x I := by
    intro I i c
    exact euler_cartan_logWedge K n x i (θ i) (hθ i) c (fun j => D j c) I (hd c)
  have hQact : ∀ c I, Q (c • logWedge x I) =
      π c • logWedge x I := by
    intro c I
    rw [hQeq, hπeq]
    exact prod_act (fun i => 1 - LE i ^ (p - 1)) (fun i => 1 - Dend i ^ (p - 1)) (logWedge x I)
      (fun i c => one_sub_pow_act (LE i) (Dend i) _ (hLact I i) (p - 1) c) (List.finRange n) c
  refine ⟨h, Q, π, ?_, hQact, hπ1, hπ2, ?_, ?_⟩
  · intro η
    exact congrArg (fun f : AddMonoid.End (abelian₂ K) => f η) hh
  · intro η
    have hQc : Commute dE Q := by
      apply Commute.list_prod_right
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨b, hb, rfl⟩ := hy
      exact (Commute.one_right dE).sub_right (hc b hb)
    have e1 : Q (extD K η) = dE (Q η) :=
      (congrArg (fun f : AddMonoid.End (abelian₂ K) => f η) hQc.eq).symm
    refine e1.trans ?_
    have hb := logWedge_basis K n x hx
    let b := Module.Basis.mk hb.1 (by rw [hb.2])
    rw [← b.sum_repr η, map_sum, map_sum]
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [Module.Basis.mk_apply, hQact]
    obtain ⟨g, hg⟩ := hπ1 (b.repr η I)
    show extD K (π (b.repr η I) • logWedge x I) = 0
    rw [hg, extD_apply, CechDR.dDR_smul, ← extD_apply, dDR_prod_dlog_eq_zero_and_euler_contraction, smul_zero, add_zero]
    have hz : KaehlerDifferential.D ℤ K (g ^ p) = 0 := dK_pow_char p g
    rw [hz, map_zero, zero_mul]
  · intro T hdT hθT
    apply hT T
    intro a ha
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨hθ1, hθ0⟩ := hθT i (θ i) (hθ i)
    have hLT : ∀ q, ∀ η ∈ T q, LE i η ∈ T q := by
      intro q η hη
      show extD K (θ i η) + θ i (extD K η) ∈ T q
      refine add_mem ?_ (hθ1 q _ (hdT q η hη))
      cases q with
      | zero => rw [hθ0 η hη, map_zero]; exact zero_mem _
      | succ q => exact hdT q _ (hθ1 q η hη)
    refine ⟨?_, ?_, ?_⟩
    · intro q η hη
      show θ i ((LE i ^ m) η) ∈ T q
      exact hθ1 q _ (addMonoidEnd_pow_mem_of_mapsTo (LE i) (T (q + 1)) (hLT (q + 1)) m η hη)
    · intro η hη
      show θ i ((LE i ^ m) η) = 0
      exact hθ0 _ (addMonoidEnd_pow_mem_of_mapsTo (LE i) (T 0) (hLT 0) m η hη)
    · intro q η hη
      exact addMonoidEnd_pow_mem_of_mapsTo (LE i) (T q) (hLT q) (p - 1) η hη

end GlobalTheory.CartierHomotopy

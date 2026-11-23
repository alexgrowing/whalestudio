import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorsLEOfIndex
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankTensor
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.InvariantSectionsTransportGL

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems Formalism.GradedWeylDivisibility MvPolynomial

theorem tn_const {A : Type} [CommRing A] (r n : ℕ) (f : MvPolynomial (Fin r × Fin n) A)
    (hf : f ∈ dualWeyl A r n 0) : f = C (coeff 0 f) := by
  have hf' := (Submodule.mem_inf.mp hf).1
  rw [mem_weightedHomogeneousSubmodule] at hf'
  have hw : ∀ v : Fin r × Fin n, colW r n v ≠ 0 := by
    intro v h
    have := congrFun h v.2
    simp [colW] at this
  simpa using (weightedHomogeneousComponent_eq_self hf').symm.trans
    (weightedHomogeneousComponent_zero f hw)

theorem tn_C_mem {A : Type} [CommRing A] (r n : ℕ) (c : A) : (C c : MvPolynomial (Fin r × Fin n) A) ∈ dualWeyl A r n 0 := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_C _ _
  · simp only [Submodule.mem_iInf]
    intro l j _
    simp [colAddGen, LinearMap.mem_ker]

theorem tn_nuOf_zero (m : ℕ) : nuOf (0 : Fin (m + 1) → ℤ) = 0 := by
  funext t
  simp [nuOf]

theorem tn_rowAct_C {K : Type} [CommRing K] {r n : ℕ} (g : Matrix (Fin r) (Fin r) K) (c : K) :
    rowAct K (n := n) g (C c) = C c := by simp [rowAct]

theorem tn_rowAct_one {K : Type} [CommRing K] {r n : ℕ} (F : MvPolynomial (Fin r × Fin n) K) :
    rowAct K (n := n) (1 : Matrix (Fin r) (Fin r) K) F = F := by
  have e : rowAct K (n := n) (1 : Matrix (Fin r) (Fin r) K) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [rowAct, Matrix.one_apply]
  rw [e, AlgHom.id_apply]

private theorem rowAct_invariant_zero_weight_iff {K : Type} [CommRing K] {r n : ℕ} (g h : Matrix (Fin r) (Fin r) K)
    (F : MvPolynomial (Fin r × Fin n) K) : rowAct K (n := n) g (rowAct K h F) = rowAct K (h * g) F := by
  have e : (rowAct K (n := n) g).comp (rowAct K h) = rowAct K (h * g) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, Matrix.mul_apply, C_mul,
      Finset.mul_sum, Finset.sum_mul, algebraMap_eq, mul_assoc]
    exact Finset.sum_comm
  exact AlgHom.congr_fun e F

theorem invariant_sections_zero_weight_iff {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (Λ : Submodule O (Fin (m + 1) → Kf))
    (hΛ : IsLattice O Λ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :
    F ∈ H0 O m 0 Λ ↔ ∃ c : O, F = C (algebraMap O Kf c) := by
  have hA : Antitone (0 : Fin (m + 1) → ℤ) := antitone_const
  have hw : (fun t : Fin (m + 1) => ((0 : Fin (m + 1) → ℤ) t - (0 : Fin (m + 1) → ℤ) (Fin.last m)).toNat) = 0 := by
    funext t
    simp
  simp only [H0, if_pos hA, Submodule.mem_iInf, nablaLTw, nablaL, hw, Submodule.mem_map, Submodule.mem_comap]
  simp
  constructor
  · intro h
    obtain ⟨g, hg, hΛg⟩ := hΛ
    obtain ⟨y, hy, hyF⟩ := h g hg.ne_zero hΛg
    rw [tn_const (m + 1) (m + 1) y hy, map_C] at hyF
    refine ⟨coeff 0 y, ?_⟩
    have h1 : F = rowAct Kf g⁻¹ (rowAct Kf g F) := by
      rw [rowAct_invariant_zero_weight_iff, Matrix.mul_nonsing_inv g hg, tn_rowAct_one]
    rw [h1, ← hyF, tn_rowAct_C]
  · rintro ⟨c, rfl⟩ g _ _
    exact ⟨C c, tn_C_mem (m + 1) (m + 1) c, by rw [map_C, tn_rowAct_C]⟩

theorem tn_mul {A Kf : Type} [CommRing A] [Field Kf] [Algebra A Kf] {S : Type} [Fintype S] {k n : ℕ}
    (M M1 M2 : S → Submodule A (MvPolynomial (Fin k × Fin n) Kf))
    (ha : ∀ s, ∀ F ∈ M1 s, ∀ r ∈ M2 s, F * r ∈ M s)
    (hb : ∀ s, ∀ G ∈ M s, ∃ F ∈ M1 s, ∃ r ∈ M2 s, G = F * r) :
    tensorLat A Kf M = tensorLat A Kf M1 * tensorLat A Kf M2 := by
  unfold tensorLat
  rw [Submodule.span_mul_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro P ⟨G, hG, rfl⟩
    choose F hF r hr hGe using fun s => hb s (G s) (hG s)
    apply Submodule.subset_span
    refine ⟨∏ s, blockEmb Kf s (F s), ⟨F, hF, rfl⟩, ∏ s, blockEmb Kf s (r s), ⟨r, hr, rfl⟩, ?_⟩
    simp only [hGe, map_mul, Finset.prod_mul_distrib]
  · rw [Submodule.span_le]
    rintro P ⟨a, ⟨F, hF, rfl⟩, b, ⟨r, hr, rfl⟩, rfl⟩
    apply Submodule.subset_span
    exact ⟨fun s => F s * r s, fun s => ha s _ (hF s) _ (hr s), by simp only [map_mul, Finset.prod_mul_distrib]⟩

theorem tn_lamAt_zero {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') (h : lam0 s = 0) :
    lamAt lam0 s = 0 := by
  unfold lamAt
  split_ifs
  · exact h
  · funext i
    simp [h]

theorem tn_top {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    (s ∈ TT → lamAt (topW TT lam0) s = lamAt lam0 s ∧ lamAt (othW TT lam0) s = 0) ∧
    (s ∉ TT → lamAt (topW TT lam0) s = 0 ∧ lamAt (othW TT lam0) s = lamAt lam0 s) := by
  by_cases hs : s ∈ TT
  · simp [lamAt, topW, othW, hs, Pi.zero_def]
  · simp [lamAt, topW, othW, hs, Pi.zero_def]

theorem tn_smulC {A Kf : Type} [CommRing A] [Field Kf] [Algebra A Kf] {σ : Type} (c : A) (F : MvPolynomial σ Kf) :
    C (algebraMap A Kf c) * F = c • F := by
  rw [Algebra.smul_def, MvPolynomial.algebraMap_apply]

theorem tn_family {A Kf : Type} [CommRing A] [Field Kf] [Algebra A Kf] {n' m : ℕ} (TT : Finset (Fin n'))
    (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (H : Fin n' → (Fin (m + 1) → ℤ) → Submodule A (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf))
    (hZ : ∀ s F, F ∈ H s 0 ↔ ∃ c : A, F = C (algebraMap A Kf c)) :
    tensorLat A Kf (fun s => H s (lamAt lam0 s)) =
      tensorLat A Kf (fun s => H s (lamAt (topW TT lam0) s)) * tensorLat A Kf (fun s => H s (lamAt (othW TT lam0) s)) := by
  apply tn_mul
  · intro s F hF r hr
    by_cases hs : s ∈ TT
    · rw [((tn_top TT lam0 s).1 hs).1] at hF
      rw [((tn_top TT lam0 s).1 hs).2, hZ] at hr
      obtain ⟨c, rfl⟩ := hr
      rw [mul_comm, tn_smulC]
      exact Submodule.smul_mem _ c hF
    · rw [((tn_top TT lam0 s).2 hs).1, hZ] at hF
      rw [((tn_top TT lam0 s).2 hs).2] at hr
      obtain ⟨c, rfl⟩ := hF
      rw [tn_smulC]
      exact Submodule.smul_mem _ c hr
  · intro s G hG
    by_cases hs : s ∈ TT
    · refine ⟨G, ?_, C (algebraMap A Kf 1), ?_, ?_⟩
      · rw [((tn_top TT lam0 s).1 hs).1]
        exact hG
      · rw [((tn_top TT lam0 s).1 hs).2, hZ]
        exact ⟨1, rfl⟩
      · simp
    · refine ⟨C (algebraMap A Kf 1), ?_, G, ?_, ?_⟩
      · rw [((tn_top TT lam0 s).2 hs).1, hZ]
        exact ⟨1, rfl⟩
      · rw [((tn_top TT lam0 s).2 hs).2]
        exact hG
      · simp

theorem tn_Hten {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ} (TT : Finset (Fin n'))
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf)) (hΛ : ∀ s, IsLattice O (Λ s)) :
    Hten O lam0 Λ = Hten O (topW TT lam0) Λ * Hten O (othW TT lam0) Λ :=
  tn_family TT lam0 (fun s lam => H0 O m lam (Λ s)) fun s F => invariant_sections_zero_weight_iff m (Λ s) (hΛ s) F

theorem tn_Vsp {Kf : Type} [Field Kf] {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    Vsp Kf lam0 = Vsp Kf (topW TT lam0) * Vsp Kf (othW TT lam0) := by
  refine tn_family TT lam0 (fun _ lam => if Antitone lam then dualWeyl Kf (m + 1) (m + 1) (nuOf lam) else ⊥)
    fun s F => ?_
  have hanti : Antitone (0 : Fin (m + 1) → ℤ) := fun _ _ _ => le_rfl
  simp only [if_pos hanti, tn_nuOf_zero]
  constructor
  · intro hF
    exact ⟨_, tn_const _ _ F hF⟩
  · rintro ⟨c, rfl⟩
    exact tn_C_mem _ _ _

theorem tn_Hten_le {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ}
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (hDom : IsDominant lam0) (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf))
    (hΛ : ∀ s, IsLattice O (Λ s)) (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)
    (hP : P ∈ Hten O lam0 Λ) : P ∈ Vsp Kf lam0 := by
  have key : ∀ s, ∀ F ∈ H0 O m (lamAt lam0 s) (Λ s),
      F ∈ (if Antitone (lamAt lam0 s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)) else ⊥) := by
    intro s F hF
    unfold H0 at hF
    split_ifs at hF ⊢ with ha
    · obtain ⟨g, hg, hΛg⟩ := hΛ s
      have hF' := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hF g) ⟨hg, hΛg⟩
      exact Formalism.MainNotions.G.LatticeSystems.la_nablaLTw_le m _ g hg F hF'
    · exact hF
  have hle : Hten O lam0 Λ ≤ (Vsp Kf lam0).restrictScalars O := by
    unfold Hten Vsp tensorLat
    rw [Submodule.span_le]
    rintro Q ⟨F, hF, rfl⟩
    exact Submodule.subset_span ⟨F, fun s => key s (F s) (hF s), rfl⟩
  exact hle hP

section Mu

variable {Kf : Type} [Field Kf] {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ)

def tnMu : Vsp Kf (topW TT lam0) →ₗ[Kf] Vsp Kf (othW TT lam0) →ₗ[Kf] Vsp Kf lam0 :=
  LinearMap.mk₂ Kf (fun F r => ⟨F.1 * r.1, by rw [tn_Vsp TT lam0]; exact Submodule.mul_mem_mul F.2 r.2⟩)
    (fun F F' r => Subtype.ext (add_mul _ _ _))
    (fun c F r => Subtype.ext (smul_mul_assoc _ _ _))
    (fun F r r' => Subtype.ext (mul_add _ _ _))
    (fun c F r => Subtype.ext (mul_smul_comm _ _ _))

theorem tnMu_val (F : Vsp Kf (topW TT lam0)) (r : Vsp Kf (othW TT lam0)) : (tnMu TT lam0 F r).1 = F.1 * r.1 := rfl

variable {O : Type} [CommRing O] [Algebra O Kf]

theorem tn_toV (M M1 M2 : Submodule O (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) (hM : M = M1 * M2)
    (h1 : ∀ P ∈ M1, P ∈ Vsp Kf (topW TT lam0)) (h2 : ∀ P ∈ M2, P ∈ Vsp Kf (othW TT lam0)) :
    toV lam0 M = Pr (tnMu TT lam0) (toV (topW TT lam0) M1) (toV (othW TT lam0) M2) := by
  subst hM
  apply le_antisymm
  · intro x hx
    have hx' : x.1 ∈ M1 * M2 := hx
    suffices H : ∀ y ∈ M1 * M2, ∃ hy : y ∈ Vsp Kf lam0,
        (⟨y, hy⟩ : Vsp Kf lam0) ∈ Pr (tnMu TT lam0) (toV (topW TT lam0) M1) (toV (othW TT lam0) M2) by
      obtain ⟨hy, h⟩ := H _ hx'
      exact h
    intro y hy
    refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun u v ihu ihv => ?_)
    · have hab : a * b ∈ Vsp Kf lam0 := by
        rw [tn_Vsp TT lam0]
        exact Submodule.mul_mem_mul (h1 a ha) (h2 b hb)
      have e : (⟨a * b, hab⟩ : Vsp Kf lam0) = tnMu TT lam0 ⟨a, h1 a ha⟩ ⟨b, h2 b hb⟩ := by
        apply Subtype.ext
        rw [tnMu_val]
      exact ⟨hab, Submodule.subset_span ⟨⟨a, h1 a ha⟩, ha, ⟨b, h2 b hb⟩, hb, e⟩⟩
    · obtain ⟨hu1, hu2⟩ := ihu
      obtain ⟨hv1, hv2⟩ := ihv
      have e : (⟨u + v, add_mem hu1 hv1⟩ : Vsp Kf lam0) = ⟨u, hu1⟩ + ⟨v, hv1⟩ := rfl
      exact ⟨add_mem hu1 hv1, by rw [e]; exact add_mem hu2 hv2⟩
  · unfold Pr
    rw [Submodule.span_le]
    rintro x ⟨F, hF, r, hr, rfl⟩
    show (tnMu TT lam0 F r).1 ∈ M1 * M2
    rw [tnMu_val]
    exact Submodule.mul_mem_mul hF hr

end Mu

section Nu

open TensorProduct

variable {Kf : Type} [Field Kf] {n' m : ℕ} (TT : Finset (Fin n'))

open Classical in

def tnDelta : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₐ[Kf]
    MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf ⊗[Kf] MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf :=
  aeval fun v => if v.1 ∈ TT then (X v) ⊗ₜ 1 else 1 ⊗ₜ (X v)

theorem tnDelta_left (s : Fin n') (hs : s ∈ TT) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :
    tnDelta (Kf := Kf) (m := m) TT (blockEmb Kf s f) =
      (Algebra.TensorProduct.includeLeft : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₐ[Kf] MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf ⊗[Kf] MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) (blockEmb Kf s f) := by
  have e : (tnDelta (Kf := Kf) (m := m) TT).comp (blockEmb Kf s) =
      (Algebra.TensorProduct.includeLeft : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₐ[Kf] MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf ⊗[Kf] MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf).comp (blockEmb Kf s) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [tnDelta, blockEmb, hs]
  exact AlgHom.congr_fun e f

theorem tnDelta_right (s : Fin n') (hs : s ∉ TT) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :
    tnDelta (Kf := Kf) (m := m) TT (blockEmb Kf s f) =
      (Algebra.TensorProduct.includeRight : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₐ[Kf] MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf ⊗[Kf] MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) (blockEmb Kf s f) := by
  have e : (tnDelta (Kf := Kf) (m := m) TT).comp (blockEmb Kf s) =
      (Algebra.TensorProduct.includeRight : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₐ[Kf] MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf ⊗[Kf] MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf).comp (blockEmb Kf s) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [tnDelta, blockEmb, hs]
  exact AlgHom.congr_fun e f

theorem tn_blockEmb_C (s : Fin n') (c : Kf) :
    blockEmb Kf (k := m + 1) (n := m + 1) s (C c) =
      algebraMap Kf (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) c := by
  simp [blockEmb, MvPolynomial.algebraMap_eq]

theorem tnDelta_on (lam1 : Fin n' → Fin (m + 1) → ℤ) (hDom : IsDominant lam1)
    (φ : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₐ[Kf]
      MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf ⊗[Kf] MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)
    (h : ∀ s, lamAt lam1 s = 0 ∨ ∀ f, tnDelta (Kf := Kf) (m := m) TT (blockEmb Kf s f) = φ (blockEmb Kf s f))
    (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) (hP : P ∈ Vsp Kf lam1) :
    tnDelta (Kf := Kf) (m := m) TT P = φ P := by
  have hanti := kp_lamAt_antitone lam1 hDom
  unfold Vsp tensorLat at hP
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨F, hF, rfl⟩ := hP
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rcases h s with h0 | h1
    · have hFs : F s ∈ dualWeyl Kf (m + 1) (m + 1) 0 := by
        have := hF s
        have hz : Antitone (0 : Fin (m + 1) → ℤ) := fun _ _ _ => le_rfl
        simp only [h0, tn_nuOf_zero, if_pos hz] at this
        exact this
      rw [tn_const _ _ _ hFs, tn_blockEmb_C, AlgHom.commutes, AlgHom.commutes]
    · exact h1 _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, map_smul, hx]

end Nu

def RestLeLat : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (e : Edge R.W R.Qq (m + 1)), IsEdge p n' 1 e →
    ∀ s : ℕ, IsLattice R.O (LeAt p R.ι R.σ R.w s e)

theorem tn_finrank_zero (Kf : Type) [Field Kf] (k n : ℕ) : Module.finrank Kf (dualWeyl Kf k n 0) = 1 := by
  have h : dualWeyl Kf k n 0 = Submodule.span Kf {1} := by
    ext f
    rw [Submodule.mem_span_singleton]
    constructor
    · intro hf
      refine ⟨coeff 0 f, ?_⟩
      conv_rhs => rw [tn_const k n f hf]
      rw [smul_eq_C_mul, mul_one]
    · rintro ⟨a, rfl⟩
      rw [smul_eq_C_mul, mul_one]
      exact tn_C_mem k n a
  rw [h, finrank_span_singleton one_ne_zero]

theorem tn_dimV (Kf : Type) [Field Kf] {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hDom : IsDominant lam0) :
    dimV Kf lam0 = ∏ s, Module.finrank Kf (dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))) := by
  have hanti := kp_lamAt_antitone lam0 hDom
  unfold dimV Vsp
  have e : (fun s => if Antitone (lamAt lam0 s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)) else ⊥) =
      fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)) := by
    funext s
    rw [if_pos (hanti s)]
  rw [e]
  exact finrank_tensor Kf (Fin n') (m + 1) (m + 1) _

theorem restTensor_of (hLat : RestLeLat) : RestTensor := by
  intro p n' R m TT lam0 hDom
  have hT : IsDominant (topW TT lam0) := by
    intro s
    unfold topW
    split_ifs
    · exact hDom s
    · exact antitone_const
  have hO : IsDominant (othW TT lam0) := by
    intro s
    unfold othW
    split_ifs
    · exact antitone_const
    · exact hDom s
  have dL : ∀ P ∈ Vsp R.Kf (topW TT lam0), tnDelta (Kf := R.Kf) (m := m) TT P =
      P ⊗ₜ[R.Kf] (1 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf) := by
    intro P hP
    rw [← Algebra.TensorProduct.includeLeft_apply (S := R.Kf)]
    refine tnDelta_on TT (topW TT lam0) hT _ ?_ P hP
    intro s
    by_cases hs : s ∈ TT
    · exact Or.inr fun f => tnDelta_left TT s hs f
    · exact Or.inl ((tn_top TT lam0 s).2 hs).1
  have dR : ∀ P ∈ Vsp R.Kf (othW TT lam0), tnDelta (Kf := R.Kf) (m := m) TT P =
      (1 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf) ⊗ₜ[R.Kf] P := by
    intro P hP
    rw [← Algebra.TensorProduct.includeRight_apply]
    refine tnDelta_on TT (othW TT lam0) hO _ ?_ P hP
    intro s
    by_cases hs : s ∈ TT
    · exact Or.inl ((tn_top TT lam0 s).1 hs).2
    · exact Or.inr fun f => tnDelta_right TT s hs f
  obtain ⟨π1, hπ1⟩ := (Vsp R.Kf (topW TT lam0)).subtype.exists_leftInverse_of_injective
    (Submodule.ker_subtype _)
  obtain ⟨π2, hπ2⟩ := (Vsp R.Kf (othW TT lam0)).subtype.exists_leftInverse_of_injective
    (Submodule.ker_subtype _)
  let D : Vsp R.Kf lam0 →ₗ[R.Kf] TensorProduct R.Kf (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf)
      (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf) :=
    (tnDelta (Kf := R.Kf) (m := m) TT).toLinearMap ∘ₗ (Vsp R.Kf lam0).subtype
  let Tm : ((TensorProduct R.Kf (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf) (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf)) →ₗ[R.Kf] TensorProduct R.Kf R.Kf R.Kf) →ₗ[R.Kf] Module.Dual R.Kf (Vsp R.Kf lam0) :=
    ((LinearMap.llcomp R.Kf (Vsp R.Kf lam0) (TensorProduct R.Kf (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf) (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf)) R.Kf).flip D) ∘ₗ
      (LinearMap.llcomp R.Kf (TensorProduct R.Kf (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf) (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf)) (TensorProduct R.Kf R.Kf R.Kf) R.Kf (TensorProduct.lid R.Kf R.Kf).toLinearMap)
  refine ⟨tnMu TT lam0,
    ((TensorProduct.mapBilinear (RingHom.id R.Kf) (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf) (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf) R.Kf R.Kf).compl₁₂ π1.dualMap π2.dualMap).compr₂ Tm,
    ?_, ?_, ?_, ?_⟩
  · intro G ρ F r
    have h1 : π1 F.1 = F := LinearMap.congr_fun hπ1 F
    have h2 : π2 r.1 = r := LinearMap.congr_fun hπ2 r
    simp [Tm, D, tnMu_val, dL F.1 F.2, dR r.1 r.2, Algebra.TensorProduct.tmul_mul_tmul, h1, h2]
  · intro L hL
    have hΛ : ∀ s : Fin n', IsLattice R.O (extO R.O R.ι R.σ (s : ℕ) L) := by
      intro s
      obtain ⟨g, hg, rfl⟩ := hL
      have hst := R.std.1
      refine ⟨Formalism.MainNotions.G.LatticeSystems.la_tw R.ι R.σ s g, Formalism.MainNotions.G.LatticeSystems.la_tw_det R.ι R.σ s g hg, ?_⟩
      refine Formalism.MainNotions.G.LatticeSystems.la_extO R.ι R.σ R.jO ?_ hst.ι_comp s g
      intro x
      obtain ⟨y, hy⟩ := hst.frob x
      exact ⟨_, hy⟩
    unfold HL
    exact tn_toV TT lam0 _ _ _ (tn_Hten TT lam0 _ hΛ) (fun P hP => tn_Hten_le _ hT _ hΛ P hP)
      (fun P hP => tn_Hten_le _ hO _ hΛ P hP)
  · intro e he
    have hΛ : ∀ s : Fin n', IsLattice R.O (LeAt p R.ι R.σ R.w (s : ℕ) e) := fun s => hLat p n' R m e he s
    unfold HLe
    exact tn_toV TT lam0 _ _ _ (tn_Hten TT lam0 _ hΛ) (fun P hP => tn_Hten_le _ hT _ hΛ P hP)
      (fun P hP => tn_Hten_le _ hO _ hΛ P hP)
  · rw [tn_dimV R.Kf lam0 hDom, tn_dimV R.Kf _ hT, tn_dimV R.Kf _ hO, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    by_cases hs : s ∈ TT
    · rw [((tn_top TT lam0 s).1 hs).1, ((tn_top TT lam0 s).1 hs).2, tn_nuOf_zero, tn_finrank_zero, mul_one]
    · rw [((tn_top TT lam0 s).2 hs).1, ((tn_top TT lam0 s).2 hs).2, tn_nuOf_zero, tn_finrank_zero, one_mul]

end Formalism.MainNotions.flipOneThree.Pf

end

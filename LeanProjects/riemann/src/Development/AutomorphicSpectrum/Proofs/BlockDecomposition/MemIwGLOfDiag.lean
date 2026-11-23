import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestBis

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.EigTorus

theorem exists_common_eigenvector : ∀ (d : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    {I : Type} (T : I → Module.End ℂ E), (∀ a b, Commute (T a) (T b)) → Module.finrank ℂ E = d → 0 < d →
    ∃ w : E, w ≠ 0 ∧ ∃ c : I → ℂ, ∀ i, T i w = c i • w :=
  _root_.UpperTheory.Reformulated.B.Ygb8.main

theorem diag_commute {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {g h : GL (Fin n) L}
    (hg : IsDiagM g) (hh : IsDiagM h) : g * h = h * g := by
  have key : ∀ a : GL (Fin n) L, IsDiagM a →
      (a : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => (a : Matrix (Fin n) (Fin n) L) i i) := by
    intro a ha
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal_apply_ne _ hij, ha i j hij]
  apply Units.ext
  simp only [Units.val_mul]
  rw [key g hg, key h hh, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  exact mul_comm _ _

theorem mem_latK_iff {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (a : GL (Fin n) L)
    (ha : IsDiagM a) (hv : ∀ i, Valued.v ((a : Matrix (Fin n) (Fin n) L) i i) = 1) (k : ℕ) (x : Fin n → L) :
    (a : Matrix (Fin n) (Fin n) L).mulVec x ∈ latK L n k ↔ x ∈ latK L n k := by
  have hc : ∀ i, (a : Matrix (Fin n) (Fin n) L).mulVec x i = (a : Matrix (Fin n) (Fin n) L) i i * x i := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · intro j _ hj
      rw [ha i j (Ne.symm hj), zero_mul]
    · simp
  have hvv : ∀ i, Valued.v ((a : Matrix (Fin n) (Fin n) L).mulVec x i) = Valued.v (x i) := by
    intro i
    rw [hc, map_mul, hv, one_mul]
  simp only [latK, Set.mem_setOf_eq, hvv]

theorem mem_iwGL_of_diag {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (a : GL (Fin n) L)
    (ha : IsDiagM a) (hv : ∀ i, Valued.v ((a : Matrix (Fin n) (Fin n) L) i i) = 1) : a ∈ IwGL L n := by
  unfold IwGL
  rw [Subgroup.mem_iInf]
  intro k
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_latK_iff a ha hv k y).2 hy
  · intro hx
    refine ⟨((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).mulVec x, ?_, ?_⟩
    · rw [← mem_latK_iff a ha hv k, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]
      simpa using hx
    · show (a : Matrix (Fin n) (Fin n) L).mulVec (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).mulVec x) = x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]
      simp

theorem mem_iwU_of_diag {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
    (k : GU σ n) (hk : k ∈ KU σ n) (hd : IsDiagM (k : GL (Fin n) L)) : k ∈ IwU σ n := by
  refine Subgroup.mem_subgroupOf.2 (mem_iwGL_of_diag _ hd fun i => ?_)
  obtain ⟨-, r, hr⟩ := Subgroup.mem_subgroupOf.1 hk
  have hint : ∀ (s : GL (Fin n) (intL L)) (i j : Fin n),
      Valued.v (((Formalism.UG.bc (n := Fin n) (intL L).subtype s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 := by
    intro s i j
    exact ((s : Matrix (Fin n) (Fin n) (intL L)) i j).2
  have h1 := hint r i i
  have h2 := hint r⁻¹ i i
  rw [map_inv, hr] at h2
  rw [hr] at h1
  have hmul : ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      ((((k : GL (Fin n) L))⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) L => M i i) (Units.mul_inv (k : GL (Fin n) L))
    simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
    rw [Finset.sum_eq_single i] at h
    · simpa using h
    · intro j _ hj
      rw [hd i j (Ne.symm hj), zero_mul]
    · simp
  have hm := congrArg Valued.v hmul
  rw [map_mul, map_one] at hm
  refine le_antisymm h1 ?_
  by_contra hlt
  push_neg at hlt
  have : Valued.v (((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) *
      Valued.v (((((k : GL (Fin n) L))⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  exact absurd hm (ne_of_lt this)

theorem eigU_of (hIw : IwahoriU) (hDom : DomU) (hKU : KUFacts)
    (hA4 : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], A4 G) :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    IsUnramInv ϖ σ q → IsAdmissible ρ → ∀ y : V, y ∉ jacU ρ →
    (∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ρ k y - y ∈ jacU ρ) →
    ∃ (y' : V) (ξ : GU σ n → ℂ), y' ∉ jacU ρ ∧ (∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ρ t y' - ξ t • y' ∈ jacU ρ) ∧
      ∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ξ k = 1 := by
  intro L _ _ _ ϖ σ q n V _ _ ρ hu hadm y hy hfix
  obtain ⟨D, hJ, hN, hNm, hT⟩ := hIw L ϖ σ q hu n
  obtain ⟨-, -, hIK, t₀, ht₀d, ht₀s⟩ := hKU L ϖ σ q n hu
  have hstr : D.IsStrDom ⟨t₀, (hT _).2 ht₀d⟩ :=
    (hDom L ϖ σ q hu n D hJ hN hNm hT ⟨t₀, (hT _).2 ht₀d⟩).2 ht₀s
  obtain ⟨-, honto⟩ := hA4 (GU σ n) D V ρ hadm ⟨_, hstr⟩
  have hker : twKer ρ D.N 1 = jacU ρ := twKer_eq_jacSub D _ hN ρ
  have hpi : ∀ (t : D.T) (v : V), D.piN ρ t (D.proj ρ v) = D.proj ρ (ρ (t : GU σ n) v) := fun _ _ => rfl
  have hproj0 : ∀ v : V, D.proj ρ v = 0 ↔ v ∈ jacU ρ := by
    intro v
    rw [← hker]
    exact Submodule.Quotient.mk_eq_zero _
  have hprojeq : ∀ v v' : V, D.proj ρ v = D.proj ρ v' ↔ v - v' ∈ jacU ρ := by
    intro v v'
    rw [← hker]
    exact Submodule.Quotient.eq _
  have hfd : FiniteDimensional ℂ (fixed ρ D.J) := hadm.2 D.J D.isOpen_J D.isCompact_J
  let S : Submodule ℂ (Jacquet ρ D.N) := fixed (D.piN ρ) D.JT
  let p : fixed ρ D.J →ₗ[ℂ] Jacquet ρ D.N := (twKer ρ D.N 1).mkQ ∘ₗ (fixed ρ D.J).subtype
  have hSle : S ≤ LinearMap.range p := by
    intro w hw
    obtain ⟨v, hv⟩ := honto w hw
    exact ⟨v, hv⟩
  have hSfd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSle
  have hmemS : ∀ w : Jacquet ρ D.N, w ∈ S ↔ ∀ s : D.JT, D.piN ρ (s : D.T) w = w := by
    intro w
    refine ⟨fun h s => by simpa using h s, fun h s => by simpa using h s⟩
  have hw₀ : D.proj ρ y ∈ S := by
    refine (hmemS _).2 fun s => ?_
    rw [hpi, hprojeq]
    have hsJ : ((s : D.T) : GU σ n) ∈ D.J := s.2
    exact hfix _ (hIK (hJ ▸ hsJ)) ((hT _).1 (s : D.T).2)
  have hw₀0 : D.proj ρ y ≠ 0 := fun h => hy ((hproj0 y).1 h)
  have hcomm : ∀ a b : D.T, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    exact diag_commute ((hT _).1 a.2) ((hT _).1 b.2)
  have hst : ∀ t : D.T, ∀ w ∈ S, D.piN ρ t w ∈ S := by
    intro t w hw
    refine (hmemS _).2 fun s => ?_
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, (hmemS w).1 hw s]
  have hpos : 0 < Module.finrank ℂ S := by
    have : Nontrivial S := ⟨⟨⟨_, hw₀⟩, 0, fun h => hw₀0 (congrArg Subtype.val h)⟩⟩
    exact Module.finrank_pos
  obtain ⟨w, hw0, c, hc⟩ := exists_common_eigenvector _ S (fun t : D.T => (D.piN ρ t).restrict (hst t))
    (fun a b => by
      ext x
      have h : D.piN ρ a (D.piN ρ b x) = D.piN ρ b (D.piN ρ a x) := by
        rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
      simpa [Module.End.mul_apply, LinearMap.restrict_apply] using h) rfl hpos
  have hc' : ∀ t : D.T, D.piN ρ t (w : Jacquet ρ D.N) = c t • (w : Jacquet ρ D.N) := fun t => by
    simpa [LinearMap.restrict_apply] using congrArg Subtype.val (hc t)
  have hwne : (w : Jacquet ρ D.N) ≠ 0 := fun h => hw0 (Subtype.ext h)
  obtain ⟨y', hy'⟩ : ∃ y' : V, D.proj ρ y' = (w : Jacquet ρ D.N) := Submodule.Quotient.mk_surjective _ _
  classical
  refine ⟨y', fun g => if h : g ∈ D.T then c ⟨g, h⟩ else 1, fun h => hwne (hy' ▸ (hproj0 y').2 h), ?_, ?_⟩
  · intro t ht
    have htT : t ∈ D.T := (hT t).2 ht
    beta_reduce
    rw [dif_pos htT, ← hproj0]
    have h1 := hc' ⟨t, htT⟩
    rw [← hy', hpi] at h1
    show D.proj ρ (ρ t y' - c ⟨t, htT⟩ • y') = 0
    have hsub : D.proj ρ (ρ t y' - c ⟨t, htT⟩ • y') = D.proj ρ (ρ t y') - c ⟨t, htT⟩ • D.proj ρ y' := rfl
    rw [hsub, h1, sub_self]
  · intro k hk hkd
    have hkT : k ∈ D.T := (hT k).2 hkd
    beta_reduce
    rw [dif_pos hkT]
    have hkJ : k ∈ D.J := hJ ▸ mem_iwU_of_diag k hk hkd
    have h1 := hc' ⟨k, hkT⟩
    have h2 := (hmemS _).1 w.2 ⟨⟨k, hkT⟩, hkJ⟩
    have h3 : c ⟨k, hkT⟩ • (w : Jacquet ρ D.N) = (1 : ℂ) • (w : Jacquet ρ D.N) := by
      rw [← h1, one_smul]
      exact h2
    exact smul_left_injective ℂ hwne h3

end GlobalTheory.CompanionTheory.EigTorus

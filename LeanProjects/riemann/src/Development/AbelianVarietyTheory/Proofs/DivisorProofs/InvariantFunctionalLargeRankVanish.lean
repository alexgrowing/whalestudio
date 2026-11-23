import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAt

open ValuativeRel Matrix GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.DetEqv.RowZero

theorem mem_SB_of {X : Type} [TopologicalSpace X] {f : X → ℂ} (hf : IsLocallyConstant f) {K : Set X}
    (hK : IsCompact K) (h : ∀ x, f x ≠ 0 → x ∈ K) : f ∈ SB X := by
  refine ⟨hf, ?_⟩
  have hcl : IsClosed (Function.support f) := by
    have : Function.support f = (f ⁻¹' {0})ᶜ := by ext; simp
    rw [this]; exact (hf.isOpen_fiber 0).isClosed_compl
  unfold HasCompactSupport tsupport
  rw [hcl.closure_eq]
  exact hK.of_isClosed_subset hcl h

theorem isLocallyConstant_indicator {X : Type} [TopologicalSpace X] {W : Set X} (hW : IsClopen W) (c : ℂ) :
    IsLocallyConstant (W.indicator fun _ => c) := fun s => by
  have h := Set.indicator_const_preimage W s c
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h <;> rw [h]
  exacts [isOpen_univ, hW.isOpen, hW.isClosed.isOpen_compl, isOpen_empty]

theorem mem_SB_mul {Y : Type} [TopologicalSpace Y] {k : Type} [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] {a m : ℕ} (g : GL (Fin m) k) {f : Y × Matrix (Fin a) (Fin m) k → ℂ}
    (hf : f ∈ SB (Y × Matrix (Fin a) (Fin m) k)) :
    (fun p : Y × Matrix (Fin a) (Fin m) k => f (p.1, p.2 * (g : Matrix (Fin m) (Fin m) k))) ∈
      SB (Y × Matrix (Fin a) (Fin m) k) := by
  refine mem_SB_of (hf.1.comp_continuous (continuous_fst.prodMk (continuous_snd.matrix_mul continuous_const)))
    ((hf.2.image (continuous_fst.prodMk (continuous_snd.matrix_mul continuous_const) :
      Continuous fun p : Y × Matrix (Fin a) (Fin m) k =>
        (p.1, p.2 * ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k))))) fun p hp => ?_
  refine ⟨(p.1, p.2 * (g : Matrix (Fin m) (Fin m) k)), subset_tsupport _ hp, ?_⟩
  simp only [Matrix.mul_assoc]
  rw [show (g : Matrix (Fin m) (Fin m) k) * ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) = 1 from
    Units.mul_inv g, Matrix.mul_one]

end GlobalTheory.DetEqv.RowZero

namespace GlobalTheory.DetEqv

open RowZero in

theorem vanish_of_vanish_off_rowZero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), GlobalTheory.DetEqv.VanishAt k n → ∀ (Y : Type) [TopologicalSpace Y] (m : ℕ), n + 1 < m →
    ∀ μ : kˣ →* ℂˣ, (∀ t : ℝ, μ ≠ GlobalTheory.SmGL.absPow k (t : ℂ)) → ∀ L : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin m) k) →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin m) k) (Φ Φ' : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin m) k)),
        (∀ (y : Y) (X : Matrix (Fin (n + 1)) (Fin m) k),
          (Φ' : Y × Matrix (Fin (n + 1)) (Fin m) k → ℂ) (y, X) =
            (Φ : Y × Matrix (Fin (n + 1)) (Fin m) k → ℂ) (y, X * (g : Matrix (Fin m) (Fin m) k))) →
        L Φ' = (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * L Φ) →
      (∀ Φ : GlobalTheory.SplitWeil.SB (Y × Matrix (Fin (n + 1)) (Fin m) k),
        (∀ (y : Y) (X : Matrix (Fin (n + 1)) (Fin m) k), X 0 = 0 → (Φ : Y × Matrix (Fin (n + 1)) (Fin m) k → ℂ) (y, X) = 0) →
        L Φ = 0) →
      L = 0 := by
  intro k _ _ _ _ n hV Y _ m hm μ hμ L hL hz
  classical
  set S : Set (Fin m → k) := Set.univ.pi fun _ => (𝒪[k] : Set k) with hS
  have hSc : IsClopen S := ⟨isClosed_set_pi fun _ _ => Valuation.isClosed_integer,
    isOpen_set_pi Set.finite_univ fun _ _ => Valuation.isOpen_integer⟩
  have hSk : IsCompact S := isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1
  set ι : (Fin m → k) → ℂ := S.indicator fun _ => 1 with hιdef
  have hι : IsLocallyConstant ι := isLocallyConstant_indicator hSc 1
  have hι0 : ι 0 = 1 := Set.indicator_of_mem (by simp [hS]) _
  let tl : Y × Matrix (Fin (n + 1)) (Fin m) k → Y × Matrix (Fin n) (Fin m) k :=
    fun p => (p.1, Matrix.of fun i j => p.2 i.succ j)
  have htl : Continuous tl :=
    continuous_fst.prodMk (continuous_matrix fun i j => continuous_snd.matrix_elem i.succ j)
  let cs : (Fin m → k) × (Y × Matrix (Fin n) (Fin m) k) → Y × Matrix (Fin (n + 1)) (Fin m) k :=
    fun q => (q.2.1, Matrix.of (Fin.cons (α := fun _ => Fin m → k) q.1 q.2.2))
  have hcs : Continuous cs := by
    refine continuous_snd.fst.prodMk (continuous_matrix fun i j => ?_)
    cases i using Fin.cases with
    | zero => exact (continuous_apply j).comp continuous_fst
    | succ i => exact continuous_snd.snd.matrix_elem i j
  have hrow : Continuous fun p : Y × Matrix (Fin (n + 1)) (Fin m) k => p.2 0 :=
    continuous_pi fun j => continuous_snd.matrix_elem 0 j
  let Ef : (Y × Matrix (Fin n) (Fin m) k → ℂ) → Y × Matrix (Fin (n + 1)) (Fin m) k → ℂ :=
    fun ψ p => ι (p.2 0) * ψ (tl p)
  have hE : ∀ ψ ∈ SB (Y × Matrix (Fin n) (Fin m) k), Ef ψ ∈ SB (Y × Matrix (Fin (n + 1)) (Fin m) k) := by
    intro ψ hψ
    refine mem_SB_of ((hι.comp_continuous hrow).mul (hψ.1.comp_continuous htl))
      ((hSk.prod hψ.2).image hcs) fun p hp => ?_
    have h1 : ι (p.2 0) ≠ 0 := left_ne_zero_of_mul hp
    have h2 : ψ (tl p) ≠ 0 := right_ne_zero_of_mul hp
    refine ⟨(p.2 0, tl p), ⟨Set.mem_of_indicator_ne_zero h1, subset_tsupport _ h2⟩, ?_⟩
    refine Prod.ext rfl ?_
    ext i j
    cases i using Fin.cases <;> rfl
  let E : SB (Y × Matrix (Fin n) (Fin m) k) →ₗ[ℂ] SB (Y × Matrix (Fin (n + 1)) (Fin m) k) :=
    { toFun := fun Ψ => ⟨Ef Ψ, hE Ψ Ψ.2⟩
      map_add' := fun a b => Subtype.ext (funext fun p => by simp [Ef, mul_add])
      map_smul' := fun c a => Subtype.ext (funext fun p => by simp [Ef, mul_left_comm]) }
  have hL' : ∀ (g : GL (Fin m) k) (Ψ Ψ' : SB (Y × Matrix (Fin n) (Fin m) k)),
      (∀ (y : Y) (X : Matrix (Fin n) (Fin m) k),
        (Ψ' : Y × Matrix (Fin n) (Fin m) k → ℂ) (y, X) =
          (Ψ : Y × Matrix (Fin n) (Fin m) k → ℂ) (y, X * (g : Matrix (Fin m) (Fin m) k))) →
      (L ∘ₗ E) Ψ' = (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * (L ∘ₗ E) Ψ := by
    intro g Ψ Ψ' h
    let Φ'' : SB (Y × Matrix (Fin (n + 1)) (Fin m) k) := ⟨_, mem_SB_mul g (hE Ψ Ψ.2)⟩
    have h1 := hL g (E Ψ) Φ'' (fun y X => rfl)
    have h2 : L (Φ'' - E Ψ') = 0 := hz _ fun y X hX => by
      show ι ((X * (g : Matrix (Fin m) (Fin m) k)) 0) *
          (Ψ : Y × Matrix (Fin n) (Fin m) k → ℂ) (y, Matrix.of fun (i : Fin n) (j : Fin m) => (X * (g : Matrix (Fin m) (Fin m) k)) i.succ j) -
        ι (X 0) * (Ψ' : Y × Matrix (Fin n) (Fin m) k → ℂ) (y, Matrix.of fun i j => X i.succ j) = 0
      rw [h]
      have e1 : (X * (g : Matrix (Fin m) (Fin m) k)) 0 = X 0 := by
        funext j; simp [Matrix.mul_apply, hX]
      have e2 : (Matrix.of fun (i : Fin n) (j : Fin m) => (X * (g : Matrix (Fin m) (Fin m) k)) i.succ j) =
          (Matrix.of fun (i : Fin n) (j : Fin m) => X i.succ j) * (g : Matrix (Fin m) (Fin m) k) := by
        ext i j; simp [Matrix.mul_apply]
      rw [e1, e2, sub_self]
    rw [map_sub, sub_eq_zero] at h2
    show L (E Ψ') = _ * L (E Ψ)
    rw [← h2, h1]
  have hL'0 : L ∘ₗ E = 0 := hV Y m (by omega) μ hμ (L ∘ₗ E) hL'
  refine LinearMap.ext fun Φ => ?_
  have hΦ0 : (fun q => (Φ : Y × Matrix (Fin (n + 1)) (Fin m) k → ℂ) (cs (0, q))) ∈
      SB (Y × Matrix (Fin n) (Fin m) k) := by
    refine mem_SB_of (Φ.2.1.comp_continuous (hcs.comp (continuous_const.prodMk continuous_id)))
      (Φ.2.2.image htl) fun q hq => ⟨cs (0, q), subset_tsupport _ hq, ?_⟩
    refine Prod.ext rfl ?_
    ext i j
    rfl
  have h3 : L (Φ - E ⟨_, hΦ0⟩) = 0 := hz _ fun y X hX => by
    show (Φ : Y × Matrix (Fin (n + 1)) (Fin m) k → ℂ) (y, X) -
      ι (X 0) * (Φ : Y × Matrix (Fin (n + 1)) (Fin m) k → ℂ) (cs (0, tl (y, X))) = 0
    have e : cs (0, tl (y, X)) = (y, X) := by
      refine Prod.ext rfl ?_
      ext i j
      cases i using Fin.cases with
      | zero => exact (congrFun hX j).symm
      | succ i => rfl
    rw [e, hX, hι0, one_mul, sub_self]
  have h4 : L (E ⟨_, hΦ0⟩) = 0 := LinearMap.congr_fun hL'0 _
  rw [map_sub, h4, sub_zero] at h3
  exact h3

end GlobalTheory.DetEqv

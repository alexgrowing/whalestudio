import Formalism.LocalToGlobal.GlobalTheory.GL6.IntegralTensorBasisLinIndep
import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.PairingContinuityBound

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

section Cls

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (τ₀ : ι) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
  [∀ τ, DecidableEq (κ τ)] (b : ∀ τ, κ τ → MvPolynomial (Fin N × Fin N) ℂ) (O : Subring ℂ)

def tenSpan : Submodule O (MvPolynomial (ι × Fin N × Fin N) ℂ) :=
  Submodule.span O (Set.range fun g : (∀ τ, κ τ) => Formalism.L2.Forms.ten (fun τ => b τ (g τ)))

def gRest (g : ∀ τ, κ τ) : ∀ τ : {τ // τ ≠ τ₀}, κ τ.1 := fun τ => g τ.1

def gExt (g : ∀ τ : {τ // τ ≠ τ₀}, κ τ.1) (k : κ τ₀) : ∀ τ, κ τ :=
  fun τ => if h : τ = τ₀ then (by subst h; exact k) else g ⟨τ, h⟩

theorem gRest_gExt (g : ∀ τ : {τ // τ ≠ τ₀}, κ τ.1) (k : κ τ₀) : gRest τ₀ κ (gExt τ₀ κ g k) = g := by
  funext τ
  unfold gRest gExt
  rw [dif_neg τ.2]

theorem gExt_self (g : ∀ τ : {τ // τ ≠ τ₀}, κ τ.1) (k : κ τ₀) : gExt τ₀ κ g k τ₀ = k := by
  unfold gExt
  rw [dif_pos rfl]

theorem ten_eq_psi (g : ∀ τ, κ τ) :
    Formalism.L2.Forms.ten (fun τ => b τ (g τ)) = mvPolynomialProductExtension τ₀ κ b (Pi.single (gRest τ₀ κ g) (b τ₀ (g τ₀))) := by
  classical
  unfold Formalism.L2.Forms.ten
  simp only [mvPolynomialProductExtension, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single (gRest τ₀ κ g)]
  · rw [Pi.single_eq_same]
    exact Fintype.prod_eq_mul_prod_subtype_ne _ τ₀
  · intro g' _ hg'
    rw [Pi.single_eq_of_ne hg', map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem tenSpan_eq_psi (Λ : Submodule O (MvPolynomial (Fin N × Fin N) ℂ))
    (hΛ : Λ = Submodule.span O (Set.range (b τ₀))) :
    tenSpan κ b O = (Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ).map
      ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O) := by
  classical
  apply le_antisymm
  · rw [tenSpan, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    dsimp only
    rw [ten_eq_psi τ₀ κ b g]
    refine ⟨Pi.single (gRest τ₀ κ g) (b τ₀ (g τ₀)), ?_, rfl⟩
    intro g' _
    by_cases hg : g' = gRest τ₀ κ g
    · subst hg
      rw [Pi.single_eq_same, hΛ]
      exact Submodule.subset_span ⟨g τ₀, rfl⟩
    · rw [Pi.single_eq_of_ne hg]
      exact Λ.zero_mem
  · rintro _ ⟨h, hh, rfl⟩
    have hsingle : ∀ (g' : ∀ τ : {τ // τ ≠ τ₀}, κ τ.1) (v : MvPolynomial (Fin N × Fin N) ℂ), v ∈ Λ →
        mvPolynomialProductExtension τ₀ κ b (Pi.single g' v) ∈ tenSpan κ b O := by
      intro g' v hv
      have hle : Λ ≤ (tenSpan κ b O).comap (((mvPolynomialProductExtension τ₀ κ b).restrictScalars O).comp
          (LinearMap.single O (fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => MvPolynomial (Fin N × Fin N) ℂ) g')) := by
        rw [hΛ, Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        have h1 := ten_eq_psi τ₀ κ b (gExt τ₀ κ g' k)
        rw [gRest_gExt, gExt_self] at h1
        show mvPolynomialProductExtension τ₀ κ b (Pi.single g' (b τ₀ k)) ∈ tenSpan κ b O
        rw [← h1]
        exact Submodule.subset_span ⟨gExt τ₀ κ g' k, rfl⟩
      exact hle hv
    have hsum : h = ∑ g', Pi.single g' (h g') := (Finset.univ_sum_single h).symm
    show mvPolynomialProductExtension τ₀ κ b h ∈ tenSpan κ b O
    rw [hsum, map_sum]
    exact Submodule.sum_mem _ fun g' _ => hsingle g' (h g') (hh g' (Set.mem_univ _))

theorem psi_subP (o : ι → Matrix (Fin N) (Fin N) ℂ) (ho : ∀ τ, τ ≠ τ₀ → o τ = 1)
    (h : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) → MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.L2.Forms.subP o (mvPolynomialProductExtension τ₀ κ b h) = mvPolynomialProductExtension τ₀ κ b (fun g => Formalism.GradedWeylDivisibility.rowAct ℂ (o τ₀) (h g)) := by
  have hren : ∀ (τ : ι) (q : MvPolynomial (Fin N × Fin N) ℂ),
      Formalism.L2.Forms.subP o (rename (Prod.mk τ) q) = rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.rowAct ℂ (o τ) q) := by
    intro τ q
    have h1 : (Formalism.L2.Forms.subP o).comp (rename (Prod.mk τ)) = (rename (Prod.mk τ)).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (o τ)) := by
      apply MvPolynomial.algHom_ext
      intro v
      simp [Formalism.L2.Forms.subP, Formalism.GradedWeylDivisibility.rowAct, rename_X, map_sum]
    exact AlgHom.congr_fun h1 q
  have hone : ∀ q : MvPolynomial (Fin N × Fin N) ℂ, Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin N) (Fin N) ℂ) q = q := by
    intro q
    have h1 : Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (1 : Matrix (Fin N) (Fin N) ℂ) = AlgHom.id ℂ _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply]
    rw [h1, AlgHom.id_apply]
  simp only [mvPolynomialProductExtension, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_mul, map_prod, hren]
  refine Finset.sum_congr rfl fun g _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [ho τ.1 τ.2, hone]

theorem map_psi_pi (L : MvPolynomial (Fin N × Fin N) ℂ →ₗ[O] MvPolynomial (Fin N × Fin N) ℂ)
    (L' : MvPolynomial (ι × Fin N × Fin N) ℂ →ₗ[O] MvPolynomial (ι × Fin N × Fin N) ℂ)
    (hc : ∀ h, L' (mvPolynomialProductExtension τ₀ κ b h) = mvPolynomialProductExtension τ₀ κ b (fun g => L (h g)))
    (Λ : Submodule O (MvPolynomial (Fin N × Fin N) ℂ)) :
    ((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ).map
        ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)).map L' =
      (Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ.map L).map
        ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O) := by
  classical
  ext x
  constructor
  · rintro ⟨y, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨fun g => L (h g), fun g _ => ⟨h g, hh g (Set.mem_univ _), rfl⟩, ?_⟩
    exact (hc h).symm
  · rintro ⟨h', hh', rfl⟩
    have hh'' : ∀ g, ∃ y ∈ Λ, L y = h' g := fun g => hh' g (Set.mem_univ _)
    choose h hh hhe using hh''
    refine ⟨mvPolynomialProductExtension τ₀ κ b h, ⟨h, fun g _ => hh g, rfl⟩, ?_⟩
    show L' (mvPolynomialProductExtension τ₀ κ b h) = mvPolynomialProductExtension τ₀ κ b h'
    rw [hc]
    congr 1
    funext g
    exact hhe g

abbrev scO (σ : Type) (c : ℂ) : MvPolynomial σ ℂ →ₗ[O] MvPolynomial σ ℂ :=
  (c • LinearMap.id : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ).restrictScalars O

theorem cls_len (hb : ∀ τ, τ ≠ τ₀ → LinearIndependent ℂ (b τ)) (Λ : Submodule O (MvPolynomial (Fin N × Fin N) ℂ))
    (hΛ : Λ = Submodule.span O (Set.range (b τ₀))) (o : ι → Matrix (Fin N) (Fin N) ℂ) (ho : ∀ τ, τ ≠ τ₀ → o τ = 1)
    (c₁ c₂ : ℂ) :
    Module.length O
      ((((tenSpan κ b O).map ((Formalism.L2.Forms.subP o).toLinearMap.restrictScalars O)).map (scO O _ c₁)) ⧸
        ((tenSpan κ b O).map (scO O _ c₂)).comap
          (((tenSpan κ b O).map ((Formalism.L2.Forms.subP o).toLinearMap.restrictScalars O)).map (scO O _ c₁)).subtype) =
      (∏ τ : {τ // τ ≠ τ₀}, Fintype.card (κ τ.1)) •
        Module.length O (((Λ.map (mvPolynomialRowLinearMap O (o τ₀))).map (mvPolynomialScalingMap O c₁)) ⧸
          (Λ.map (mvPolynomialScalingMap O c₂)).comap ((Λ.map (mvPolynomialRowLinearMap O (o τ₀))).map (mvPolynomialScalingMap O c₁)).subtype) := by
  have hrow : (tenSpan κ b O).map ((Formalism.L2.Forms.subP o).toLinearMap.restrictScalars O) =
      (Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ.map (mvPolynomialRowLinearMap O (o τ₀))).map
        ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O) := by
    rw [tenSpan_eq_psi τ₀ κ b O Λ hΛ]
    exact map_psi_pi τ₀ κ b O (mvPolynomialRowLinearMap O (o τ₀)) ((Formalism.L2.Forms.subP o).toLinearMap.restrictScalars O)
      (fun h => psi_subP τ₀ κ b o ho h) Λ
  have hsc : ∀ (c : ℂ) (Λ' : Submodule O (MvPolynomial (Fin N × Fin N) ℂ)),
      ((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ').map
        ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)).map (scO O _ c) =
      (Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ'.map (mvPolynomialScalingMap O c)).map
        ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O) := by
    intro c Λ'
    refine map_psi_pi τ₀ κ b O (mvPolynomialScalingMap O c) (scO O _ c) (fun h => ?_) Λ'
    show c • mvPolynomialProductExtension τ₀ κ b h = mvPolynomialProductExtension τ₀ κ b (fun g => c • h g)
    rw [← map_smul]
    rfl
  rw [hrow, hsc, tenSpan_eq_psi τ₀ κ b O Λ hΛ, hsc]
  exact length_quot_map_positionMap τ₀ κ b hb O _ _

end Cls

end Formalism.L2.GlobalTheoryTheory.LemB

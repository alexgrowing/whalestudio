import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsJacMapZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedRepresentationIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharInducedJacquetStatement

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.KSplit GlobalTheory.RankFibre GlobalTheory.IndLineGL
open scoped TensorProduct

namespace GlobalTheory.JacLineGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev PSp (ν β : kˣ →* ℂˣ) (a b : ℕ) : Type :=
  IndSp (two (stdSum (rfl : a + b = a + b)))
    ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)

abbrev pRep (ν β : kˣ →* ℂˣ) (a b : ℕ) : Representation ℂ (GL (Fin (a + b)) k) (PSp ν β a b) :=
  prod₂ (detRep (Fin a) (ν * β)) (detRep (Fin b) β)

theorem indSp_mul (ν β : kˣ →* ℂˣ) (a b : ℕ) : indSp a b (ν * β) β = indScal ν β a b := by
  rw [indSp_eq_indScal]
  congr 1
  ext x
  simp

theorem val_mem (ν β : kˣ →* ℂˣ) (a b : ℕ) (F : PSp ν β a b) : indScalVal ν β a b F ∈ indSp a b (ν * β) β := by
  rw [indSp_mul]
  refine ⟨mem_smoothPart_of_nhds ?_, fun p x => ?_⟩
  · have ho : IsOpen {g | pRep ν β a b g F = F} := isSmooth_prod₂ _ _ F
    refine Filter.mem_of_superset (ho.mem_nhds (by simp)) fun g hg => funext fun x => ?_
    have hg' : pRep ν β a b g F = F := hg
    show TensorProduct.lid ℂ ℂ (F.1.1 (x * g)) = TensorProduct.lid ℂ ℂ (F.1.1 x)
    exact congrArg (fun G : PSp ν β a b => TensorProduct.lid ℂ ℂ (G.1.1 x)) hg'
  · have h := F.1.2 p x
    show TensorProduct.lid ℂ ℂ (F.1.1 (p * x)) = ofChar _ p (TensorProduct.lid ℂ ℂ (F.1.1 x))
    rw [h]
    obtain ⟨c, hc⟩ := (TensorProduct.lid ℂ ℂ).symm.surjective (F.1.1 x)
    rw [← hc]
    simp only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, MonoidHom.coe_coe]
    simp [parChar, detRep, ofChar_apply]
    ring

def scalEquiv (ν β : kˣ →* ℂˣ) (a b : ℕ) : PSp ν β a b ≃ₗ[ℂ] indSp a b (ν * β) β :=
  LinearEquiv.ofBijective ((indScalVal ν β a b).codRestrict _ (val_mem ν β a b))
    ⟨fun F G h => Subtype.ext (Subtype.ext (funext fun x =>
      (TensorProduct.lid ℂ ℂ).injective (congrFun (congrArg Subtype.val h) x))),
     fun f => ⟨indScalLift ν β a b (indSp_mul ν β a b ▸ f.2), Subtype.ext (indScal_scal_lift ν β a b _)⟩⟩

theorem scalEquiv_rep (ν β : kˣ →* ℂˣ) (a b : ℕ) (g x : GL (Fin (a + b)) k) (F : PSp ν β a b) :
    (scalEquiv ν β a b (pRep ν β a b g F) : GL (Fin (a + b)) k → ℂ) x =
      (scalEquiv ν β a b F : GL (Fin (a + b)) k → ℂ) (x * g) := rfl

def sum3 (m : ℕ) : Fin 1 ⊕ Fin m ⊕ Fin 1 ≃ (Σ i : Fin 3, Fin (blk3 m i)) :=
  Equiv.ofBijective (Sum.elim (fun i => ⟨0, i⟩) (Sum.elim (fun i => ⟨1, i⟩) (fun i => ⟨2, i⟩)))
    ((Fintype.bijective_iff_surjective_and_card _).2 ⟨by
      rintro ⟨i, j⟩
      fin_cases i
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr (Sum.inl j), rfl⟩
      · exact ⟨Sum.inr (Sum.inr j), rfl⟩, by simp [Fin.sum_univ_three, add_assoc]⟩)

def part3 (a b : ℕ) : (Σ i : Fin 3, Fin (blk3 (a + b) i)) ≃ Fin (a + (b + 2)) :=
  (sum3 (a + b)).symm.trans (JacLine.blk3 a b)

theorem jacquet_line_block_inl (a b : ℕ) (i : Fin 1) : JacLine.blk3 a b (Sum.inl i) = part3 a b ⟨0, i⟩ :=
  congrArg (JacLine.blk3 a b) ((sum3 (a + b)).symm_apply_apply _).symm

theorem jacquet_line_block_inr_inl (a b : ℕ) (i : Fin (a + b)) : JacLine.blk3 a b (Sum.inr (Sum.inl i)) = part3 a b ⟨1, i⟩ :=
  congrArg (JacLine.blk3 a b) ((sum3 (a + b)).symm_apply_apply _).symm

theorem jacquet_line_block_inr_inr (a b : ℕ) (i : Fin 1) : JacLine.blk3 a b (Sum.inr (Sum.inr i)) = part3 a b ⟨2, i⟩ :=
  congrArg (JacLine.blk3 a b) ((sum3 (a + b)).symm_apply_apply _).symm

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem unip_shape {a b : ℕ} {u : GL (Fin (a + (b + 2))) k} (hu : u ∈ unipRad k (part3 a b)) :
    u.val.submatrix (JacLine.blk3 a b) (JacLine.blk3 a b) =
      fromBlocks 1 (of fun i j => u.val (JacLine.blk3 a b (Sum.inl i)) (JacLine.blk3 a b (Sum.inr j))) 0
        (fromBlocks 1 (of fun i j => u.val (JacLine.blk3 a b (Sum.inr (Sum.inl i)))
          (JacLine.blk3 a b (Sum.inr (Sum.inr j)))) 0 1) := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hu
  have h3 := mem_parab_iff.1 h1
  ext (i | i | i) (j | j | j) <;> rw [submatrix_apply]
  · exact (congrArg₂ u.val (jacquet_line_block_inl a b i) (jacquet_line_block_inl a b j)).trans (h2 0 i j)
  · rfl
  · rfl
  · exact (congrArg₂ u.val (jacquet_line_block_inr_inl a b i) (jacquet_line_block_inl a b j)).trans (h3 1 0 i j (by decide))
  · exact (congrArg₂ u.val (jacquet_line_block_inr_inl a b i) (jacquet_line_block_inr_inl a b j)).trans (h2 1 i j)
  · rfl
  · exact (congrArg₂ u.val (jacquet_line_block_inr_inr a b i) (jacquet_line_block_inl a b j)).trans (h3 2 0 i j (by decide))
  · exact (congrArg₂ u.val (jacquet_line_block_inr_inr a b i) (jacquet_line_block_inr_inl a b j)).trans (h3 2 1 i j (by decide))
  · exact (congrArg₂ u.val (jacquet_line_block_inr_inr a b i) (jacquet_line_block_inr_inr a b j)).trans (h2 2 i j)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem levi_shape {a b : ℕ} (l : Levi k (fun i : Fin 3 => Fin (blk3 (a + b) i))) :
    (leviEmb k (part3 a b) l).val.submatrix (JacLine.blk3 a b) (JacLine.blk3 a b) =
      fromBlocks (of fun _ _ => ((GeneralLinearGroup.det (l 0) : kˣ) : k)) 0 0
        (fromBlocks (show GL (Fin (a + b)) k from l 1).val 0 0 (of fun _ _ => ((GeneralLinearGroup.det (l 2) : kˣ) : k))) := by
  have hd : ∀ (g : GL (Fin 1) k) (i j : Fin 1), g.val i j = ((GeneralLinearGroup.det g : kˣ) : k) := fun g i j => by
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; simp
  ext (i | i | i) (j | j | j) <;> simp only [submatrix_apply, jacquet_line_block_inl, jacquet_line_block_inr_inl, jacquet_line_block_inr_inr]
  · exact (leviEmb_apply_same k _ l 0 i j).trans (hd (l 0) i j)
  · exact leviEmb_apply_ne k _ l (by decide) _ _
  · exact leviEmb_apply_ne k _ l (by decide) _ _
  · exact leviEmb_apply_ne k _ l (by decide) _ _
  · exact leviEmb_apply_same k _ l 1 i j
  · exact leviEmb_apply_ne k _ l (by decide) _ _
  · exact leviEmb_apply_ne k _ l (by decide) _ _
  · exact leviEmb_apply_ne k _ l (by decide) _ _
  · exact (leviEmb_apply_same k _ l 2 i j).trans (hd (l 2) i j)

section Frob

variable {a b : ℕ} {α β : kˣ →* ℂˣ} {P P₁ : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁]
  (π : Representation ℂ (GL (Fin (a + (b + 2))) k) P) (σ : Representation ℂ (GL (Fin (a + b)) k) P₁)
  (E : P ≃ₗ[ℂ] indSp a (b + 2) α β) (E₁ : P₁ ≃ₗ[ℂ] indSp a b α β)

def frob (φ : indSp a (b + 2) α β →ₗ[ℂ] indSp a b α β) : P →ₗ[ℂ] (GL (Fin (a + (b + 2))) k → P₁) :=
  LinearMap.pi fun h => E₁.symm.toLinearMap ∘ₗ φ ∘ₗ E.toLinearMap ∘ₗ π h

theorem frob_apply (φ : indSp a (b + 2) α β →ₗ[ℂ] indSp a b α β) (x : P) (h : GL (Fin (a + (b + 2))) k) :
    frob π E E₁ φ x h = E₁.symm (φ (E (π h x))) := rfl

theorem frob_one (φ : indSp a (b + 2) α β →ₗ[ℂ] indSp a b α β) (f : indSp a (b + 2) α β) :
    φ f = E₁ (frob π E E₁ φ (E.symm f) 1) := by
  rw [frob_apply, map_one, Module.End.one_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem isGLIndMap_frob
    (hE : ∀ g x F, (E (π g F) : GL (Fin (a + (b + 2))) k → ℂ) x = (E F : GL (Fin (a + (b + 2))) k → ℂ) (x * g))
    (hE₁ : ∀ g x F, (E₁ (σ g F) : GL (Fin (a + b)) k → ℂ) x = (E₁ F : GL (Fin (a + b)) k → ℂ) (x * g))
    {ξ₁ ξ₂ : kˣ →* ℂˣ} {φ : indSp a (b + 2) α β →ₗ[ℂ] indSp a b α β}
    (hφ : JacLine.IsJacMap a b α β (fun x => (ξ₁ x : ℂ)) (fun x => (ξ₂ x : ℂ)) φ) :
    IsGLIndMap (part3 a b) π σ ξ₁ ξ₂ (frob π E E₁ φ) where
  right g x h := by rw [frob_apply, frob_apply, map_mul, Module.End.mul_apply]
  unip u hu x h := by
    rw [frob_apply, frob_apply, map_mul, Module.End.mul_apply,
      hφ.1 u _ _ (unip_shape hu) (E (π h x)) (E (π u (π h x))) fun y => hE u y _]
  levi l x h := by
    rw [frob_apply, frob_apply, map_mul π, Module.End.mul_apply, LinearEquiv.symm_apply_eq, map_smul]
    refine Subtype.ext (funext fun y => ?_)
    rw [hφ.2 _ _ _ _ (levi_shape l) (E (π h x)) (E (π (leviEmb k (part3 a b) l) (π h x))) (fun y => hE _ y _) y,
      Submodule.coe_smul, Pi.smul_apply, Units.val_mul, smul_eq_mul]
    have h1 := hE₁ (l 1) y (E₁.symm (φ (E (π h x))))
    rw [LinearEquiv.apply_symm_apply] at h1
    exact congrArg _ h1.symm

end Frob

theorem jacMap_line : GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a b : ℕ) (α β : kˣ →* ℂˣ), GlobalTheory.KSplit.IsSmU α → GlobalTheory.KSplit.IsSmU β → b + 2 < a →
    ∀ φ φ' : GlobalTheory.KSplit.indSp a (b + 2) α β →ₗ[ℂ] GlobalTheory.KSplit.indSp a b α β,
      GlobalTheory.JacLine.IsJacMap a b α β (fun x => (β x : ℂ) * GlobalTheory.SplitFlip.apow x ((a : ℂ) / 2))
        (fun y => (β y : ℂ) * GlobalTheory.SplitFlip.apow y (-(a : ℂ) / 2)) φ →
      GlobalTheory.JacLine.IsJacMap a b α β (fun x => (β x : ℂ) * GlobalTheory.SplitFlip.apow x ((a : ℂ) / 2))
        (fun y => (β y : ℂ) * GlobalTheory.SplitFlip.apow y (-(a : ℂ) / 2)) φ' →
      φ = 0 ∨ ∃ c : ℂ, φ' = c • φ := by
  intro H k _ _ _ _ a b α β hα hβ hab
  obtain ⟨ν, rfl⟩ : ∃ ν : kˣ →* ℂˣ, α = ν * β := ⟨α * β⁻¹, by ext x; simp⟩
  intro φ φ' hφ hφ'
  have h₁ := GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp a (χ := ν * β) hα.1 hα.2
  have h₂ := GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp b (χ := β) hβ.1 hβ.2
  have hirr : (pRep ν β a b).IsIrreducible := H.base.bernsteinUnitaryProductIrreducible k a b ℂ ℂ _ _
    h₁.1 h₁.2.1 h₁.2.2 h₂.1 h₂.2.1 h₂.2.2
  have key := GlobalTheory.T.unitary_char_induced_jacquet H k a (b + 2) (a + b) (by omega) hab (ν * β) β hα.1 hβ.1 hα.2 hβ.2 _ _
    (pRep ν β a (b + 2)) (pRep ν β a b) (isSmooth_prod₂ _ _) ⟨Representation.Equiv.refl _⟩ hirr (part3 a b)
    (β * absPow k ((a : ℂ) / 2)) (β * absPow k (-(a : ℂ) / 2)) _ _
    (isGLIndMap_frob _ _ (scalEquiv ν β a (b + 2)) (scalEquiv ν β a b) (scalEquiv_rep ν β a (b + 2))
      (scalEquiv_rep ν β a b) hφ)
    (isGLIndMap_frob _ _ (scalEquiv ν β a (b + 2)) (scalEquiv ν β a b) (scalEquiv_rep ν β a (b + 2))
      (scalEquiv_rep ν β a b) hφ')
  refine key.imp (fun h => LinearMap.ext fun f => ?_) fun ⟨c, h⟩ => ⟨c, LinearMap.ext fun f => ?_⟩
  · refine (frob_one (pRep ν β a (b + 2)) (scalEquiv ν β a (b + 2)) (scalEquiv ν β a b) φ f).trans ?_
    rw [h]
    exact map_zero _
  · refine (frob_one (pRep ν β a (b + 2)) (scalEquiv ν β a (b + 2)) (scalEquiv ν β a b) φ' f).trans ?_
    rw [h]
    exact (map_smul _ c _).trans (congrArg (c • ·)
      (frob_one (pRep ν β a (b + 2)) (scalEquiv ν β a (b + 2)) (scalEquiv ν β a b) φ f).symm)

end GlobalTheory.JacLineGL

end

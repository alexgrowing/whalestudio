import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SecondClosedOfFirstClosed

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.SSComplement

section Rep

variable {Γ k : Type} [Group Γ] [Field k]

def blockM {a b n : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : Γ →* GL (Fin a) k) (ρ₂ : Γ →* GL (Fin b) k) :
    Γ →* Matrix (Fin n) (Fin n) k where
  toFun g := Matrix.reindex e0 e0
    (Matrix.fromBlocks (ρ₁ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ₂ g : Matrix (Fin b) (Fin b) k))
  map_one' := by simp
  map_mul' g g' := by simp [Matrix.fromBlocks_multiply]

def diagM {t : ℕ} (χ : Fin t → Γ →* kˣ) : Γ →* Matrix (Fin t) (Fin t) k where
  toFun g := Matrix.diagonal fun c => ((χ c g : kˣ) : k)
  map_one' := by simp
  map_mul' g h := by simp [Matrix.diagonal_mul_diagonal]

theorem blockM_inl {a b n : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : Γ →* GL (Fin a) k)
    (ρ₂ : Γ →* GL (Fin b) k) (g : Γ) (p q : Fin a) :
    blockM e0 ρ₁ ρ₂ g (e0 (Sum.inl p)) (e0 (Sum.inl q)) = (ρ₁ g : Matrix (Fin a) (Fin a) k) p q := by
  simp [blockM]

theorem blockM_charpoly {a b n : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : Γ →* GL (Fin a) k)
    (ρ₂ : Γ →* GL (Fin b) k) (g : Γ) :
    (blockM e0 ρ₁ ρ₂ g).charpoly =
      (ρ₁ g : Matrix (Fin a) (Fin a) k).charpoly * (ρ₂ g : Matrix (Fin b) (Fin b) k).charpoly := by
  show (Matrix.reindex e0 e0 _).charpoly = _
  rw [Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₂₁]

theorem blockM_ss {a b n : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : Γ →* GL (Fin a) k)
    (ρ₂ : Γ →* GL (Fin b) k) (h₁ : IsSSRep ρ₁) (h₂ : IsSSRep ρ₂) : IsSSRep (blockM e0 ρ₁ ρ₂).toHomUnits := by
  refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_prod ((LinearEquiv.funCongrLeft k k e0).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) h₁ h₂
  show _ = _
  ext i <;> simp [blockM, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft] <;> rfl

theorem ss_of_scalar {a : ℕ} (ρ : Γ →* GL (Fin a) k) (c : Γ → k)
    (h : ∀ g v, (ρ g : Matrix (Fin a) (Fin a) k).mulVec v = c g • v) : IsSSRep ρ := by
  intro W _
  obtain ⟨W', hW'⟩ := W.exists_isCompl
  exact ⟨W', fun g v hv => by rw [h]; exact W'.smul_mem _ hv, hW'⟩

theorem diagM_ss : ∀ {t : ℕ} (χ : Fin t → Γ →* kˣ), IsSSRep (diagM χ).toHomUnits
  | 0, χ => ss_of_scalar _ (fun _ => 0) fun g v => funext fun c => c.elim0
  | t + 1, χ => by
    refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_prod (ρ₁ := (diagM fun c : Fin t => χ (Fin.castAdd 1 c)).toHomUnits)
      (ρ₂ := (diagM fun c : Fin 1 => χ (Fin.natAdd t c)).toHomUnits)
      ((LinearEquiv.funCongrLeft k k finSumFinEquiv).trans
        (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) (diagM_ss _)
      (ss_of_scalar _ (fun g => ((χ (Fin.last t) g : kˣ) : k)) fun g v => ?_)
    · show _ = _
      ext i <;> simp [diagM, Matrix.mulVec_diagonal, LinearMap.funLeft]
    · funext c
      obtain rfl : c = 0 := Subsingleton.elim _ _
      simp [diagM, Matrix.mulVec_diagonal]
      exact Or.inl rfl

theorem diagM_charpoly {t : ℕ} (χ : Fin t → Γ →* kˣ) (g : Γ) :
    (diagM χ g).charpoly = ∏ c, (X - C ((χ c g : kˣ) : k)) :=
  Matrix.charpoly_diagonal _

end Rep

theorem prod_Icc_eq_prod_fin {M : Type} [CommMonoid M] (t : ℕ) (f : ℕ → M) :
    ∏ c ∈ Finset.Icc 1 t, f c = ∏ c : Fin t, f ((c : ℕ) + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
    Finset.prod_range]
  exact Finset.prod_congr rfl fun c _ => by rw [add_comm]

theorem cont : ∀ (D : D7), Formalism.MainNotions.SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i)
    (r : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i),
    IsSSRep (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) ρ) →
    (∀ g, ((r g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly =
      ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly *
        ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i))) →
    GlobalTheory.LocalInv.Cont D.nd i ρ := by
  intro D h5 i x r hr ρ hρ hch
  set φ := algebraMap (D.nd.O i) (Kf D.nd i) with hφ
  let χK : Fin D.R.t → G D.host.E D.nd.Om →* (Kf D.nd i)ˣ := fun c =>
    (Units.map φ.toMonoidHom).comp (D.nd.chi i ((c : ℕ) + 1))
  let e0 : Fin D.R.r ⊕ Fin D.R.t ≃ Fin D.R.nV := finSumFinEquiv.trans (finCongr rfl)
  let S := (blockM e0 (mapRep φ ρ) (diagM χK).toHomUnits).toHomUnits
  have hS : IsSSRep S := blockM_ss e0 _ _ hρ (diagM_ss χK)
  have hpoly : ∀ g, ((mapRep φ r g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i)).charpoly =
      ((S g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i)).charpoly := by
    intro g
    show (((r g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map φ).charpoly =
      (blockM e0 (mapRep φ ρ) (diagM χK).toHomUnits g).charpoly
    rw [blockM_charpoly, Matrix.charpoly_map, hch g, Polynomial.map_mul, prod_Icc_eq_prod_fin,
      Polynomial.map_prod]
    show _ = (((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map φ).charpoly * (diagM χK g).charpoly
    rw [Matrix.charpoly_map, diagM_charpoly]
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp [χK]
  obtain ⟨Pm, hPm⟩ := h5.2.2.2 (Kf D.nd i) D.R.nV (mapRep φ r) S hr.2.1 hS hpoly
  refine continuous_matrix fun p q => ?_
  refine GlobalTheory.BlockJumpsCompare.continuous_of_comb (D.nd.O_adic i)
    (fun jk : Fin D.R.nV × Fin D.R.nV =>
      ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i)) (e0 (Sum.inl p)) jk.1 *
        (Pm : Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i)) jk.2 (e0 (Sum.inl q)))
    (h := fun jk g => ((r g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) jk.1 jk.2)
    (fun jk => hr.1.matrix_elem jk.1 jk.2) fun g => ?_
  have e1 : φ (((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) p q) =
      ((S g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i)) (e0 (Sum.inl p)) (e0 (Sum.inl q)) := by
    show _ = blockM e0 (mapRep φ ρ) (diagM χK).toHomUnits g (e0 (Sum.inl p)) (e0 (Sum.inl q))
    rw [blockM_inl]
    rfl
  rw [e1, hPm g, Units.val_mul, Units.val_mul, Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  show _ = _ * φ (((r g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) j k)
  change _ * (((r g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map φ) j k * _ = _
  rw [Matrix.map_apply]
  ring

end GlobalTheory.SSComplement

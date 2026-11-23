import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCastRfl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedParabolicInductionReindexEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorTorusCharacter
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

namespace GlobalTheory.IndLineGL.MidColumn

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Transport

variable {α : Type} [Fintype α] [LinearOrder α] {m m' : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n']

variable (k) in

def leviMap (τ : ∀ a, m' a ≃ m a) : Levi k m' →* Levi k m :=
  MonoidHom.pi fun a => (Units.map (Matrix.reindexAlgEquiv k k (τ a)).toMonoidHom).comp
    (Pi.evalMonoidHom (fun a => GL (m' a) k) a)

theorem val_leviMap (τ : ∀ a, m' a ≃ m a) (l : Levi k m') (a : α) :
    ((leviMap k τ l a : GL (m a) k) : Matrix (m a) (m a) k) = Matrix.reindex (τ a) (τ a) (l a : Matrix (m' a) (m' a) k) :=
  rfl

theorem det_leviMap (τ : ∀ a, m' a ≃ m a) (l : Levi k m') (a : α) :
    Matrix.GeneralLinearGroup.det (leviMap k τ l a) = Matrix.GeneralLinearGroup.det (l a) := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, val_leviMap,
    Matrix.det_reindex_self]

theorem deltaHalf_leviMap (τ : ∀ a, m' a ≃ m a) (l : Levi k m') :
    deltaHalf k m (leviMap k τ l) = deltaHalf k m' l := by
  have hc : ∀ a, Fintype.card (m a) = Fintype.card (m' a) := fun a => (Fintype.card_congr (τ a)).symm
  have he : ∀ a, modExp m a = modExp m' a := fun a => by simp only [modExp, hc]
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [he a, det_leviMap]

theorem exists_parab_reindex {e : (Σ a, m a) ≃ n} {e' : (Σ a, m' a) ≃ n'} (τ : ∀ a, m' a ≃ m a) (ψ : n' ≃ n)
    (h : ∀ a i, ψ (e' ⟨a, i⟩) = e ⟨a, τ a i⟩) (p : parab k e') :
    ∃ q : parab k e, (q : GL n k) = Units.map (Matrix.reindexAlgEquiv k k ψ).toMonoidHom (p : GL n' k) ∧
      leviProj k e q = leviMap k τ (leviProj k e' p) := by
  have hs : ∀ a x, ψ.symm (e ⟨a, x⟩) = e' ⟨a, (τ a).symm x⟩ := fun a x => by
    rw [Equiv.symm_apply_eq, h, Equiv.apply_symm_apply]
  refine ⟨⟨Units.map (Matrix.reindexAlgEquiv k k ψ).toMonoidHom (p : GL n' k), mem_parab_iff.2 fun a b i j hab => ?_⟩,
    rfl, ?_⟩
  · show Matrix.reindex ψ ψ ((p : GL n' k) : Matrix n' n' k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, hs, hs]
    exact mem_parab_iff.1 p.2 a b _ _ hab
  · funext a
    ext i j
    show Matrix.reindex ψ ψ ((p : GL n' k) : Matrix n' n' k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
      Matrix.reindex (τ a) (τ a) ((leviProj k e' p a : GL (m' a) k) : Matrix (m' a) (m' a) k) i j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, hs, hs, Matrix.reindex_apply, Matrix.submatrix_apply,
      leviProj_apply]

theorem exists_parab_reindex_symm {e : (Σ a, m a) ≃ n} {e' : (Σ a, m' a) ≃ n'} (τ : ∀ a, m' a ≃ m a) (ψ : n' ≃ n)
    (h : ∀ a i, ψ (e' ⟨a, i⟩) = e ⟨a, τ a i⟩) (q : parab k e) :
    ∃ p : parab k e', (p : GL n' k) = Units.map (Matrix.reindexAlgEquiv k k ψ.symm).toMonoidHom (q : GL n k) ∧
      leviMap k τ (leviProj k e' p) = leviProj k e q := by
  refine ⟨⟨Units.map (Matrix.reindexAlgEquiv k k ψ.symm).toMonoidHom (q : GL n k),
    mem_parab_iff.2 fun a b i j hab => ?_⟩, rfl, ?_⟩
  · show Matrix.reindex ψ.symm ψ.symm ((q : GL n k) : Matrix n n k) (e' ⟨a, i⟩) (e' ⟨b, j⟩) = 0
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, h, h]
    exact mem_parab_iff.1 q.2 a b _ _ hab
  · funext a
    ext i j
    show Matrix.reindex (τ a) (τ a) (Matrix.of fun x y =>
        Matrix.reindex ψ.symm ψ.symm ((q : GL n k) : Matrix n n k) (e' ⟨a, x⟩) (e' ⟨a, y⟩)) i j =
      ((q : GL n k) : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩)
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Equiv.symm_symm, h,
      Equiv.apply_symm_apply]

theorem continuous_reindex (ψ : n' ≃ n) :
    Continuous (Units.map (Matrix.reindexAlgEquiv k k ψ).toMonoidHom) :=
  Continuous.units_map _ (continuous_pi fun i => continuous_pi fun j =>
    continuous_apply_apply (ψ.symm i) (ψ.symm j))

theorem parInd_transport (e : (Σ a, m a) ≃ n) (e' : (Σ a, m' a) ≃ n') (τ : ∀ a, m' a ≃ m a) (ψ : n' ≃ n)
    (h : ∀ a i, ψ (e' ⟨a, i⟩) = e ⟨a, τ a i⟩) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k m) W) :
    Nonempty ((parInd e' (ρ.comp (leviMap k τ))).Equiv
      ((parInd e ρ).comp (Units.map (Matrix.reindexAlgEquiv k k ψ).toMonoidHom))) := by
  refine Relabel.smInd_equiv_comp (Units.map (Matrix.reindexAlgEquiv k k ψ).toMonoidHom)
    (Units.map (Matrix.reindexAlgEquiv k k ψ.symm).toMonoidHom) (continuous_reindex ψ)
    (continuous_reindex ψ.symm) (fun x => ?_) (fun x => ?_) (fun q => ?_) (fun p => ?_)
  · ext i j
    simp [Matrix.coe_reindexAlgEquiv]
  · ext i j
    simp [Matrix.coe_reindexAlgEquiv]
  · obtain ⟨p, hp, hl⟩ := exists_parab_reindex_symm τ ψ h q
    refine ⟨p, hp, ?_⟩
    ext v
    simp only [MonoidHom.comp_apply, twist_apply, deltaHalf_leviMap, hl]
    rw [← deltaHalf_leviMap τ, hl]
  · obtain ⟨q, hq, hl⟩ := exists_parab_reindex τ ψ h p
    refine ⟨q, hq, ?_⟩
    ext v
    simp only [MonoidHom.comp_apply, twist_apply, hl, deltaHalf_leviMap]

end Transport

end GlobalTheory.IndLineGL.MidColumn

namespace GlobalTheory.IndLineGL.MidColumn

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Column

def twoBlocks (d : Bool → ℕ) : ∀ x : Bool, Two (Fin (d false)) (Fin (d true)) x ≃ Fin (d x)
  | false => Equiv.refl _
  | true => Equiv.refl _

theorem modExp_three_one (d : Fin 3 → ℕ) :
    modExp (fun j : Fin 3 => Fin (d j)) 1 = (d 2 : ℤ) - d 0 := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_three]

theorem deltaHalf_mulSingle_one (d : Fin 3 → ℕ) (h : GL (Fin (d 1)) k) :
    deltaHalf k (fun j : Fin 3 => Fin (d j)) (Pi.mulSingle (M := fun j : Fin 3 => GL (Fin (d j)) k) 1 h) =
      absPow k ((((d 2 : ℕ) : ℂ) - (d 0 : ℕ)) / 2) (Matrix.GeneralLinearGroup.det h) := by
  rw [deltaHalf_apply, Fin.prod_univ_three, Pi.mulSingle_eq_same,
    Pi.mulSingle_eq_of_ne (by decide : (0 : Fin 3) ≠ 1), Pi.mulSingle_eq_of_ne (by decide : (2 : Fin 3) ≠ 1),
    map_one, map_one, map_one, map_one, one_mul, mul_one, modExp_three_one]
  congr 2
  push_cast
  ring

theorem det_leviEmb_mulSingle_one (d : Fin 3 → ℕ) {X : Type} [Fintype X] [DecidableEq X]
    (e : (Σ j, Fin (d j)) ≃ X) (h : GL (Fin (d 1)) k) :
    Matrix.GeneralLinearGroup.det (leviEmb k e (Pi.mulSingle (M := fun j : Fin 3 => GL (Fin (d j)) k) 1 h)) =
      Matrix.GeneralLinearGroup.det h := by
  rw [det_leviEmb, Fin.prod_univ_three, Pi.mulSingle_eq_same,
    Pi.mulSingle_eq_of_ne (by decide : (0 : Fin 3) ≠ 1), Pi.mulSingle_eq_of_ne (by decide : (2 : Fin 3) ≠ 1),
    map_one, map_one, one_mul, mul_one]

theorem swapBlocks_mulSingle_one (b : Bool → Fin 3 → ℕ) (L : ∀ i, GL (Fin (b i 1)) k) (i : Bool) :
    swapBlocks k (fun i j => Fin (b i j)) (Pi.mulSingle (M := fun j : Fin 3 => Levi k fun i => Fin (b i j)) 1 L) i =
      Pi.mulSingle (M := fun j : Fin 3 => GL (Fin (b i j)) k) 1 (L i) := by
  funext j
  show (Pi.mulSingle (M := fun j : Fin 3 => Levi k fun i => Fin (b i j)) 1 L) j i = _
  by_cases hj : j = 1
  · subst hj
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj]
    rfl

theorem detPair_apply (a a' : ℕ) (α₀ β₀ : kˣ →* ℂˣ) (x : Levi k (Two (Fin a) (Fin a'))) (v : ℂ ⊗[ℂ] ℂ) :
    detPair k a a' α₀ β₀ x v =
      ((α₀ (Matrix.GeneralLinearGroup.det (x false)) * β₀ (Matrix.GeneralLinearGroup.det (x true)) : ℂˣ) : ℂ) • v :=
  CellTorus.extTensor_detRep_apply α₀ β₀ _ v

theorem twKer_detPair {a a' : ℕ} {c : Bool → Fin 3 → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (f : ∀ i, (Σ j, c i j) ≃ Two (Fin a) (Fin a') i) (α₀ β₀ : kˣ →* ℂˣ) :
    twKer (detPair k a a' α₀ β₀) (relUnip k f) 1 = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨u, v, rfl⟩
  have hu : ∀ i, Matrix.GeneralLinearGroup.det ((u : Levi k (Two (Fin a) (Fin a'))) i) = 1 := fun i =>
    det_eq_one_of_mem_unipRad k ((Subgroup.mem_pi _).1 u.2 i (Set.mem_univ i))
  rw [detPair_apply, hu, hu]
  simp

theorem colRep_detPair_equiv (a a' : ℕ) (α₀ β₀ : kˣ →* ℂˣ) (b : Bool → Fin 3 → ℕ)
    (f : ∀ i, (Σ j, Fin (b i j)) ≃ Two (Fin a) (Fin a') i) :
    Nonempty (Representation.Equiv ((colRep f (detPair k a a' α₀ β₀) 1).comp (leviMap k (twoBlocks fun i => b i 1)))
      ((extTensor (detRep (Fin (b false 1)) (α₀ * absPow k ((((b false 0 : ℕ) : ℂ) - (b false 2 : ℕ)) / 2)))
        (detRep (Fin (b true 1)) (β₀ * absPow k ((((b true 0 : ℕ) : ℂ) - (b true 2 : ℕ)) / 2)))).comp
        (leviTwo k (Fin (b false 1)) (Fin (b true 1))).symm.toMonoidHom)) := by
  refine ⟨.mk (Submodule.quotEquivOfEqBot _ (twKer_detPair f α₀ β₀)) fun l => ?_⟩
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, MonoidHom.comp_apply]
  rw [show colRep f (detPair k a a' α₀ β₀) 1 (leviMap k (twoBlocks fun i => b i 1) l) =
      relJac f (detPair k a a' α₀ β₀) (swapBlocks k (fun i j => Fin (b i j))
        (Pi.mulSingle (M := fun j : Fin 3 => Levi k fun i => Fin (b i j)) 1
          (leviMap k (twoBlocks fun i => b i 1) l))) from rfl, relJac_mk, detPair_apply,
    Submodule.Quotient.mk_smul, smul_smul, map_smul]
  simp only [LinearEquiv.coe_coe, Submodule.quotEquivOfEqBot_apply_mk]
  rw [CellTorus.extTensor_detRep_apply, ← Units.val_mul]
  congr 2
  rw [relDeltaHalf_apply, Fintype.prod_bool, relEmb_apply, relEmb_apply, swapBlocks_mulSingle_one,
    swapBlocks_mulSingle_one, deltaHalf_mulSingle_one, deltaHalf_mulSingle_one, det_leviEmb_mulSingle_one,
    det_leviEmb_mulSingle_one]
  have hd : ∀ x, Matrix.GeneralLinearGroup.det (leviMap k (twoBlocks fun i => b i 1) l x) =
      Matrix.GeneralLinearGroup.det (l x) := fun x => det_leviMap _ l x
  rw [hd false, hd true]
  change _ = (α₀ * _) (Matrix.GeneralLinearGroup.det (l false)) * (β₀ * _) (Matrix.GeneralLinearGroup.det (l true))
  have hn : ∀ x y : ℕ, absPow k (((x : ℂ) - (y : ℂ)) / 2) = (absPow k (((y : ℂ) - (x : ℂ)) / 2))⁻¹ := by
    intro x y
    rw [← absPow_neg]
    congr 1
    ring
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, hn (b false 0), hn (b true 0)]
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, MonoidHom.inv_apply]
  ring

end Column

theorem parInd_colRep_equiv_cellMid : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (a a' m : ℕ) (α₀ β₀ : kˣ →* ℂˣ) (b : SizeMatrix (Two (Fin a) (Fin a')) fun j : Fin 3 => Fin (blk3 m j))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin a) (Fin a') i) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (blk3 m j))
    (hm : b.1 false 1 + b.1 true 1 = m),
    Nonempty (Representation.Equiv ((parInd (g 1) (colRep f (detPair k a a' α₀ β₀) 1)).comp (glCast k hm))
      (cellMid k α₀ β₀ b.1)) := by
  intro k _ _ _ _ a a' m α₀ β₀ b f g hm
  let e' : (Σ x, Two (Fin (b.1 false 1)) (Fin (b.1 true 1)) x) ≃ Fin (b.1 false 1 + b.1 true 1) :=
    (Equiv.sigmaCongrRight (twoBlocks fun i => b.1 i 1)).trans ((g 1).trans (finCongr hm).symm)
  let ρ₂ := (extTensor (detRep (Fin (b.1 false 1)) (α₀ * absPow k ((((b.1 false 0 : ℕ) : ℂ) - (b.1 false 2 : ℕ)) / 2)))
      (detRep (Fin (b.1 true 1)) (β₀ * absPow k ((((b.1 true 0 : ℕ) : ℂ) - (b.1 true 2 : ℕ)) / 2)))).comp
      (leviTwo k (Fin (b.1 false 1)) (Fin (b.1 true 1))).symm.toMonoidHom
  have h₁ : Nonempty (Representation.Equiv
      (parInd e' ((colRep f (detPair k a a' α₀ β₀) 1).comp (leviMap k (twoBlocks fun i => b.1 i 1))))
      ((parInd (g 1) (colRep f (detPair k a a' α₀ β₀) 1)).comp (glCast k hm))) :=
    parInd_transport (k := k) (g 1) e' (twoBlocks fun i => b.1 i 1) (finCongr hm)
      (fun x i => Equiv.apply_symm_apply _ _) (colRep f (detPair k a a' α₀ β₀) 1)
  have h₂ : Nonempty (Representation.Equiv
      ((colRep f (detPair k a a' α₀ β₀) 1).comp (leviMap k (twoBlocks fun i => b.1 i 1))) ρ₂) :=
    colRep_detPair_equiv (k := k) a a' α₀ β₀ b.1 f
  have h₃ : Nonempty (Representation.Equiv (parInd e' ρ₂) (cellMid k α₀ β₀ b.1)) :=
    (Placing.parInd_jac_placing k Bool (Fin (b.1 false 1 + b.1 true 1))
      (Two (Fin (b.1 false 1)) (Fin (b.1 true 1))) e' (two (stdSum rfl)) (ℂ ⊗[ℂ] ℂ)).1 ρ₂
  obtain ⟨φ₁⟩ := h₁
  obtain ⟨φ₂⟩ := h₂
  obtain ⟨φ₃⟩ := h₃
  exact ⟨(φ₁.symm.trans (GlobalTheory.LocGL.parIndEquiv e' φ₂)).trans φ₃⟩

end GlobalTheory.IndLineGL.MidColumn

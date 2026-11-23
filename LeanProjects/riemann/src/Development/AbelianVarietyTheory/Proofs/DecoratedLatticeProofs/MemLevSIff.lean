import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.TopLevQ.moved_mat {k Z : Type} [Field k] [Fintype Z] [DecidableEq Z] {n : ℕ} (β : Matrix (Fin n) Z k) (γ : Matrix Z (Fin n) k) (hγβ : γ * β = 1) (x : Matrix Z Z k) (e : Z ≃ Fin n) : β * x * γ * β.submatrix id e.symm = β.submatrix id e.symm * x.submatrix e.symm e.symm := by
  rw [Matrix.submatrix_mul_equiv β x id e.symm e.symm, Matrix.mul_assoc (β * x)]
  have h1 : γ * β.submatrix id e.symm = (γ * β).submatrix id e.symm := by
    ext i j; simp [Matrix.mul_apply]
  rw [h1, hγβ]
  ext i j; simp [Matrix.mul_apply, Matrix.one_apply]

theorem GlobalTheory.TopLevQ.suppAt_conj {D : D7} {e : AE D} {V : HSp D} (g b : GA D V) (hg : Formalism.L2.Theta.SuppAt e V g) :
    Formalism.L2.Theta.SuppAt e V (b⁻¹ * g * b) := by
  have hm : ∀ x y : GA D V, Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := fun x y => by
    unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl
  have h1 : Formalism.L2.Theta.mt V b⁻¹ * Formalism.L2.Theta.mt V b = 1 := by
    rw [← hm, inv_mul_cancel]; unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  have key : Formalism.L2.Theta.mt V (b⁻¹ * g * b) - 1 =
      Formalism.L2.Theta.mt V b⁻¹ * (Formalism.L2.Theta.mt V g - 1) * Formalism.L2.Theta.mt V b := by
    rw [hm, hm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have hg' : (e + (cA D) e) • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 := by
    ext i j; exact hg i j
  have h2 : (e + (cA D) e) • (Formalism.L2.Theta.mt V b⁻¹ * (Formalism.L2.Theta.mt V g - 1) * Formalism.L2.Theta.mt V b) =
      Formalism.L2.Theta.mt V b⁻¹ * ((e + (cA D) e) • (Formalism.L2.Theta.mt V g - 1)) * Formalism.L2.Theta.mt V b := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hg'] at h2
  intro i j
  rw [key]
  exact congrFun (congrFun h2 i) j

theorem GlobalTheory.TopLevQ.blk_iff {K : Type} [Field K] [ValuativeRel K] {κ τ s n : ℕ}
    (e : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ≃ Fin n) (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e)
    (x : Matrix (GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2)) (GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2)) K) :
    (∀ i j : Fin n, Formalism.L2.DIV.blk2 (κ + (s + 1)) j < Formalism.L2.DIV.blk2 (κ + (s + 1)) i →
      ValuativeRel.valuation K (x (e.symm i) (e.symm j)) < 1) ↔ GlobalTheory.StepData.MaxM x.toBlocks₂₁ := by
  have hlo : ∀ a : Fin κ ⊕ Fin (s + 1), (e (Sum.inl a)).val < κ + (s + 1) := by
    intro a; rw [he]; rcases a with a | a <;> simp [GlobalTheory.SymBridge.zPos] <;> omega
  have hhi : ∀ p : Fin (s + 2) × Fin τ, κ + (s + 1) ≤ (e (Sum.inr p)).val := by
    intro p; rw [he]; simp only [GlobalTheory.SymBridge.zPos]; exact Nat.le_add_right_of_le (Nat.le_add_right _ _)
  constructor
  · intro h p a
    have := h (e (Sum.inr p)) (e (Sum.inl a)) (by
      simp only [Formalism.L2.DIV.blk2, if_pos (hlo a), if_neg (Nat.not_lt.2 (hhi p))]; omega)
    simp only [Equiv.symm_apply_apply] at this
    exact this
  · intro h i j hij
    have hj : j.val < κ + (s + 1) := by
      by_contra hc
      simp only [Formalism.L2.DIV.blk2, if_neg hc] at hij
      split_ifs at hij <;> omega
    have hi : ¬ i.val < κ + (s + 1) := by
      intro hc
      simp only [Formalism.L2.DIV.blk2, if_pos hc, if_pos hj] at hij
      omega
    obtain ⟨p, hp⟩ : ∃ p, e.symm i = Sum.inr p := by
      rcases hi' : e.symm i with a | p
      · exfalso; apply hi; have := hlo a; rw [← hi', Equiv.apply_symm_apply] at this; exact this
      · exact ⟨p, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a, e.symm j = Sum.inl a := by
      rcases hj' : e.symm j with a | p
      · exact ⟨a, rfl⟩
      · exfalso; have := hhi p; rw [← hj', Equiv.apply_symm_apply] at this; omega
    rw [hp, ha]
    exact h p a

theorem GlobalTheory.TopLevQ.mem_levS_iff {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (y : GA D V) :
    y ∈ levS V β L ↔ y ∈ GfC V ∧ ((Lev.finE V y ∈ Formalism.L2.DIV.St β ∧
        (∀ PP' ∈ L.Pg, Formalism.L2.DIV.redFn β PP' (Lev.finE V y) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t)) ∧
        ∀ PP' ∈ L.Q, Formalism.L2.DIV.redFn β PP' (Lev.finE V y) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 L.r)) ∧
        Formalism.L2.DIV.rTup β L (Lev.finE V y) ∈ L.P.H) := by
  show y ∈ GfC V ⊓ Subgroup.comap (Lev.finE V) (Formalism.L2.DIV.lev _ _ β L) ↔ _
  rw [Subgroup.mem_inf, Subgroup.mem_comap]
  show _ ∧ (_ ∈ Formalism.L2.DIV.parLev _ _ _ _ ∧ _) ↔ _
  rw [Formalism.L2.DIV.mem_parLev]
  simp only [GlobalTheory.LevSplit.finE_mem_UA, true_and]

end

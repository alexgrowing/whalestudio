import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpZeroMemLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZeroRead

theorem matrix_in_frame {k n Y A : Type} [CommRing k] [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y] [Fintype A]
    [DecidableEq A] (β : Matrix n Y k) (γ : Matrix Y n k) (h : γ * β = 1) (b : GL Y k) (σ : A ≃ Y) (e : A ≃ n)
    (X : Matrix A A k) (m : Matrix n n k)
    (hm : ((β * b.val).submatrix id fun i => σ (e.symm i)) * m =
      β * (b.val * X.submatrix σ.symm σ.symm * (b⁻¹).val) * γ * (β * b.val).submatrix id fun i => σ (e.symm i)) :
    m = X.submatrix e.symm e.symm := by
  let ρ : n ≃ Y := e.symm.trans σ
  have h1 : ((b⁻¹).val * γ) * (β * b.val) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc γ, h, Matrix.one_mul, Units.inv_mul]
  have h2 : β * (b.val * X.submatrix σ.symm σ.symm * (b⁻¹).val) * γ * (β * b.val) =
      β * b.val * X.submatrix σ.symm σ.symm := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc (b.val * _), ← Matrix.mul_assoc (b⁻¹).val, h1, Matrix.mul_one,
      Matrix.mul_assoc]
  have h3 : ∀ (P : Matrix n n k) (Q : Matrix n Y k), P * Q.submatrix id ρ = (P * Q).submatrix id ρ := fun _ _ => rfl
  have h4 : ∀ (P : Matrix Y n k) (Q : Matrix n Y k), P.submatrix ρ id * Q.submatrix id ρ = (P * Q).submatrix ρ ρ :=
    fun _ _ => rfl
  change (β * b.val).submatrix id ρ * m = _ * (β * b.val).submatrix id ρ at hm
  rw [h3, h2] at hm
  have h5 := congrArg (fun Z => ((b⁻¹).val * γ).submatrix ρ id * Z) hm
  try simp only at h5
  rw [← Matrix.mul_assoc, h4, h4, h1, ← Matrix.mul_assoc, h1, Matrix.submatrix_one_equiv, Matrix.one_mul, Matrix.one_mul] at h5
  rw [h5]
  ext i j
  simp [ρ]

theorem toEAf_onto (D : D7) : Function.Surjective (toEAf D) := by
  refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
  exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id

theorem finE_val {D : D7} (V : HSp D) (g : GA D V) : (Lev.finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := rfl

theorem upperLeftBlock_apply_of_eq {κ : Type} [CommRing κ] {r n : ℕ} (hr : r ≤ n) (hn : n ≤ r) (g : GL (Fin n) κ) (i j : Fin r) :
    (upperLeftBlock hr g).val i j = g.val (Fin.castLE hr i) (Fin.castLE hr j) := by
  have hg : g ∈ blockTri (κ := κ) (blk2 r) := fun i j h => by
    have hi : i.val < r := lt_of_lt_of_le i.2 hn
    have hj : j.val < r := lt_of_lt_of_le j.2 hn
    simp [blk2, hi, hj] at h
  rw [upper_block_val_submatrix hr hg]
  rfl

set_option maxHeartbeats 1000000 in

theorem red_of_isLoc : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP), d.Base → ∀ (hr : D.R.r ≤ (d.st 0).V.rank) (g : GA D (d.st 0).V) (x : G.S.P.J), (GlobalTheory.LocMod.ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) g (GlobalTheory.LevZeroGen.upZero G.S (Fin D.R.t) x.1) → finE (d.st 0).V ((d.t 0)⁻¹ * g * d.t 0) ∈ St (d.st 0).β → G.Red x (upperLeftBlock hr (redFn (d.st 0).β PP (finE (d.st 0).V ((d.t 0)⁻¹ * g * d.t 0)))) := by
  intro D u d τ PP G hB hr g x hg hS
  obtain ⟨π', h1, h2, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D G.k G.q PP G.idem
  obtain ⟨e, he, hM⟩ := G.frame 0 (G.s + 1) (Nat.zero_add _)
  obtain ⟨m, hm⟩ := hS
  choose f hf using toEAf_onto D
  have hπ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) (Formalism.L2.Theta.AE D)), (Z.map (toEAf D)).map π' = Z.map (GlobalTheory.LocMod.ofSplit G.q).π := fun Z => by
    ext i j; exact h1 _
  have hb : (((d.st 0).β.val.map f).map (toEAf D)) = (d.st 0).β.val := by ext i j; exact hf _
  have hM' := hM _ hb
  rw [← hπ, Matrix.map_mul (f := toEAf D), hb, ← finE_val] at hM'
  have hg2 := hg.2
  rw [← hπ, ← finE_val] at hg2
  have hmul : Lev.finE (d.st 0).V (d.t 0) * (d.st 0).β * intGL _ _ _ m =
      Lev.finE (d.st 0).V g * (Lev.finE (d.st 0).V (d.t 0) * (d.st 0).β) := by
    have : (d.st 0).β * intGL _ _ _ m * (d.st 0).β⁻¹ = _ := hm
    rw [map_mul, map_mul, map_inv] at this
    rw [mul_assoc, eq_mul_of_mul_inv_eq this]
    group
  have hmul' := congrArg (fun Z : GL (Fin (d.st 0).V.rank) (Lev.EAf D) => Z.val.map π') hmul
  simp only [Units.val_mul] at hmul'
  rw [Matrix.map_mul (L := _ * _), Matrix.map_mul (M := _ * _), hM', hg2] at hmul'
  have key := matrix_in_frame _ _ (G.FY 0 (G.s + 1) (Nat.zero_add _)).γβ _ _ e
    (x.1.val.submatrix (GlobalTheory.StepData.ixZero _ (Fin D.R.t)).symm (GlobalTheory.StepData.ixZero _ (Fin D.R.t)).symm) _ hmul'
  have hn : (d.st 0).V.rank ≤ D.R.r := by
    have := (hB.st 0 (by have := G.hs; omega)).rank
    rw [this]; simp [Formalism.BasicNotions.Ranks.rankY]
  intro a b a' b' ha hb' z hz
  rw [upperLeftBlock_apply_of_eq hr hn, ← hm, redFn_frGL] at hz
  have ea : e.symm (Fin.castLE hr a') = Sum.inl a := by
    rw [Equiv.symm_apply_eq]; apply Fin.ext; rw [he]; rcases a with a | a <;> exact ha
  have eb : e.symm (Fin.castLE hr b') = Sum.inl b := by
    rw [Equiv.symm_apply_eq]; apply Fin.ext; rw [he]; rcases b with b | b <;> exact hb'
  have k2 := congrFun (congrFun key (Fin.castLE hr a')) (Fin.castLE hr b')
  rw [Matrix.submatrix_apply, ea, eb] at k2
  have k3 : resS D.host.F PP (m.val (Fin.castLE hr a') (Fin.castLE hr b') - oToS D.host.F D.host.E z) = 0 := by
    rw [map_sub, resS_oToS, hz]; exact sub_self _
  have k4 := (h2.ker _).1 k3
  rw [map_sub] at k4
  have k5 : π' (oToS D.host.F D.host.E z).1 = (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) := by
    refine Eq.trans (congrArg π' ?_) (h1 (incA D (z : D.host.E)))
    rfl
  convert k4 using 3
  · exact k2.symm
  · exact k5.symm

end GlobalTheory.LevZeroRead

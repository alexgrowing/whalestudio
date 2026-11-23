import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatMoveStd

variable {D : D7}

theorem mt_mul'' (V : HSp D) (g g' : GA D V) : mt V (g * g') = mt V g * mt V g' := by
  show (matHom V (g * g')).1 = (matHom V g).1 * (matHom V g').1
  rw [map_mul, Units.val_mul]

theorem mt_one'' (V : HSp D) : mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  rw [map_one, Units.val_one]

theorem cA_cA'' (x : AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a e =>
    show (a ⊗ₜ[D.host.F] D.sp.cm.sig (D.sp.cm.sig e)) = _
    rw [show D.sp.cm.sig (D.sp.cm.sig e) = e from star_star e]

theorem unitary (V : HSp D) (hg : V.gram = 1) (g : GA D V) :
    ((mt V g).map (cA D))ᵀ * mt V g = 1 := by
  have h : ((mt V g).map (cA D))ᵀ * V.gram.map (incA D) * mt V g = V.gram.map (incA D) :=
    (g : HR (AF D.host.F) D.sp.cm.sig V.gram).2
  rw [hg, Matrix.map_one (incA D) (map_zero _) (map_one _), Matrix.mul_one] at h
  exact h

theorem mt_inv_eq (V : HSp D) (hg : V.gram = 1) (g : GA D V) : mt V g⁻¹ = ((mt V g).map (cA D))ᵀ := by
  have h1 := unitary V hg g
  have h2 : mt V g * mt V g⁻¹ = 1 := by rw [← mt_mul'', mul_inv_cancel, mt_one'']
  calc mt V g⁻¹ = (((mt V g).map (cA D))ᵀ * mt V g) * mt V g⁻¹ := by rw [h1, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]

set_option synthInstance.maxHeartbeats 200000 in

theorem int_of_moves (V : HSp D) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hM : Moves V rfl g N) (x : Fin V.rank → D.host.E) (hx : x ∈ N) (i : Fin V.rank) :
    finPart D ((mt V g⁻¹ *ᵥ fun k => incA D (x k)) i) ∈ intAE D := by
  rw [GlobalTheory.SplitDec.int_iff]
  have := (hM x).1 hx i
  have e : toEAf D ((mt V g⁻¹ *ᵥ fun k => incA D (x k)) i) = (finM V rfl g⁻¹ *ᵥ fun j => eToEAf D (x j)) i := by
    simp only [Matrix.mulVec, dotProduct]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    rfl
  rw [e]; exact this

theorem gen_eq (α : Af D.host.F) (c x y : D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * x * y) = (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) * incA D x * incA D y := by
  simp [incA, inclR, Algebra.TensorProduct.tmul_mul_tmul]

end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd

variable {D : D7}

set_option synthInstance.maxHeartbeats 200000 in

theorem int_conj (V : HSp D) (hg : V.gram = 1) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hM : Moves V rfl g N) (s : Fin V.rank → D.host.E) (hs : s ∈ N) (j : Fin V.rank) :
    finPart D (∑ l, cA D (incA D (s l)) * mt V g l j) ∈ intAE D := by
  rw [← GlobalTheory.FinPl.FrameLat.cA_int_iff]
  have e : cA D (∑ l, cA D (incA D (s l)) * mt V g l j) = (mt V g⁻¹ *ᵥ fun k => incA D (s k)) j := by
    rw [mt_inv_eq V hg g, map_sum]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, cA_cA'', mul_comm]
  rw [e]; exact int_of_moves V g N hM s hs j

theorem single_mem (S T : HSp D) (hgS : S.gram = 1) (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (c : D.host.E)
    (hc : c ∈ D.host.AA) (i0 : Fin T.rank) (j0 : Fin S.rank) :
    (Matrix.single i0 j0 (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) : WO S T) ∈
      latO S T (intVec D _) (intVec D _) (fun _ => True) := by
  have hint : ∀ {n : ℕ} (k : Fin n), Pi.single k (1 : D.host.E) ∈ intVec D n := by
    intro n k l
    by_cases h : l = k
    · subst h; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
  refine AddSubgroup.subset_closure ⟨α, hα, fun _ h => absurd trivial h, c, hc, Pi.single j0 1, hint j0,
    Pi.single i0 1, hint i0, ?_⟩
  ext i j
  rw [Matrix.of_apply, hgS]
  have hsum : ∑ k, star ((Pi.single j0 (1 : D.host.E) : Fin S.rank → D.host.E) k) *
      (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E) k j =
      star ((Pi.single j0 (1 : D.host.E) : Fin S.rank → D.host.E) j) := by
    rw [Finset.sum_eq_single j (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), Matrix.one_apply_eq, mul_one]
  rw [hsum]
  by_cases hi : i = i0
  · subst hi
    by_cases hj : j = j0
    · subst hj
      rw [Matrix.single_apply_same, Pi.single_eq_same, Pi.single_eq_same, star_one, mul_one, mul_one]
    · rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hj), Pi.single_eq_of_ne hj, star_zero, mul_zero,
        TensorProduct.tmul_zero]
  · rw [Matrix.single_apply_of_row_ne (Ne.symm hi), Pi.single_eq_of_ne hi, mul_zero, zero_mul,
      TensorProduct.tmul_zero]

end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd

variable {D : D7}

theorem row_one {n : ℕ} (s : Fin n → D.host.E) (l : Fin n) :
    ∑ m, star (s m) * (1 : Matrix (Fin n) (Fin n) D.host.E) m l = star (s l) := by
  rw [Finset.sum_eq_single l (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero])
    (fun h => absurd (Finset.mem_univ l) h), Matrix.one_apply_eq, mul_one]

set_option synthInstance.maxHeartbeats 200000 in

theorem gen_mem (S T : HSp D) (hgS : S.gram = 1) (hgT : T.gram = 1) (g : GA D S) (h : GA D T)
    (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hN : Moves S rfl g N) (hN' : Moves T rfl h N') (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (c : D.host.E)
    (hc : c ∈ D.host.AA) (s : Fin S.rank → D.host.E) (hs : s ∈ N) (t : Fin T.rank → D.host.E) (ht : t ∈ N') :
    actO S T g⁻¹ h⁻¹ (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j))
      ∈ latO S T (intVec D _) (intVec D _) (fun _ => True) := by
  have e1 : actO S T g⁻¹ h⁻¹
      (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j)) =
      Matrix.of fun i j => ((mt T h⁻¹ *ᵥ fun k => incA D (t k)) i * ∑ l, cA D (incA D (s l)) * mt S g l j) *
        (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) := by
    ext i j
    simp only [actO, inv_inv, Matrix.mul_apply, Matrix.of_apply, hgS, row_one, gen_eq,
      ← GlobalTheory.FinPl.FrameLat.cA_incA, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  rw [e1, Matrix.matrix_eq_sum_single ((Matrix.of fun i j =>
    ((mt T h⁻¹ *ᵥ fun k => incA D (t k)) i * ∑ l, cA D (incA D (s l)) * mt S g l j) *
        (pairA D.host.F 0 α ⊗ₜ[D.host.F] c)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))]
  refine sum_mem fun i0 _ => sum_mem fun j0 _ => ?_
  rw [Matrix.of_apply, ← smul_eq_mul, ← Matrix.smul_single]
  refine GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ?_ _ (single_mem S T hgS α hα c hc i0 j0)
  rw [map_mul]
  exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE (int_of_moves T h N' hN' t ht i0) (int_conj S hgS g N hN s hs j0)

end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd

theorem latO_moved_onto : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b), S.gram = 1 → T.gram = 1 → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), Moves S hS g N → Moves T hT h N' → ∀ u' ∈ latO S T (latFr S hS N) (latFr T hT N') (fun _ => True), ∃ u ∈ latO S T (intVec D _) (intVec D _) (fun _ => True), actO S T g h u = u' := by
  intro D S T a b hS hT hgS hgT g _ h _ N N' hN hN' u' hu'
  subst hS; subst hT
  refine ⟨actO S T g⁻¹ h⁻¹ u', ?_, ?_⟩
  · let Ψ : WO S T →+ WO S T :=
      { toFun := actO S T g⁻¹ h⁻¹
        map_zero' := by simp only [actO, Matrix.mul_zero, Matrix.zero_mul]
        map_add' := fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul] }
    have key : latO S T (latFr S rfl N) (latFr T rfl N') (fun _ => True) ≤
        (latO S T (intVec D _) (intVec D _) (fun _ => True)).comap Ψ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨α, hα, -, c, hc, s, hs, t, ht, rfl⟩
      exact gen_mem S T hgS hgT g h N N' hN hN' α hα c hc s hs t ht
    exact key hu'
  · simp only [actO]
    rw [inv_inv, Matrix.mul_assoc (mt T h), Matrix.mul_assoc (mt T h⁻¹ * u'), ← mt_mul'', mul_inv_cancel, mt_one'', Matrix.mul_one,
      ← Matrix.mul_assoc, ← mt_mul'', mul_inv_cancel, mt_one'', Matrix.one_mul]

end GlobalTheory.LatMoveStd

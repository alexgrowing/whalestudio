import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocSympl

variable {D : D7}

theorem conj_conj (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_ι (p : Place D k) (x : k) : p.e * p.ι x = p.ι x := by
  have h := p.ι_π (p.ι x)
  rw [p.π_ι] at h
  exact h.symm

theorem conj_ι_mul_ι (p : Place D k) (u v : k) : cA D (p.ι u) * p.ι v = 0 := by
  calc cA D (p.ι u) * p.ι v = cA D (p.e * p.ι u) * (p.e * p.ι v) := by rw [e_mul_ι, e_mul_ι]
    _ = (p.e * cA D p.e) * (cA D (p.ι u) * p.ι v) := by rw [map_mul]; ring
    _ = 0 := by rw [p.split.2.1, zero_mul]

end GlobalTheory.LocSympl

namespace GlobalTheory.LocSympl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem up_half (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x : Matrix Y Y' k) :
    IsHalf p.e (p.up FS FT x) := fun i j => e_mul_ι p _

theorem down_up (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x : Matrix Y Y' k) :
    p.down FS FT (p.up FS FT x) = x := by
  have hm : ((FT.β * x * FS.γ).map p.ι).map p.π = FT.β * x * FS.γ := by
    ext i j; simp [p.π_ι]
  unfold Place.down Place.up
  rw [hm, show FT.γ * (FT.β * x * FS.γ) * FS.β = (FT.γ * FT.β) * x * (FS.γ * FS.β) by simp only [Matrix.mul_assoc],
    FT.γβ, FS.γβ, Matrix.one_mul, Matrix.mul_one]

theorem up_down (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (z : WO S T)
    (hz : IsHalf p.e z) : p.up FS FT (p.down FS FT z) = z := by
  unfold Place.down Place.up
  rw [show FT.β * (FT.γ * (z : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * FS.β) * FS.γ
      = (FT.β * FT.γ) * (z : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * (FS.β * FS.γ) by
      simp only [Matrix.mul_assoc], FT.βγ, FS.βγ, Matrix.one_mul, Matrix.mul_one]
  ext i j
  simp only [Matrix.map_apply]
  rw [p.ι_π]
  exact hz i j

theorem hO_up_up (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x y : Matrix Y Y' k) :
    hO S T (p.up FS FT x) (p.up FS FT y) = 0 := by
  unfold hO
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  show incA D _ * cA D (p.ι _) * incA D _ * p.ι _ = 0
  rw [show ∀ A B C E' : AE D, A * C * B * E' = A * B * (C * E') from fun _ _ _ _ => by ring, conj_ι_mul_ι, mul_zero]

theorem e_mul_hO_up (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (t : Matrix Y Y' k)
    (y : WO S T) : p.e * hO S T (p.up FS FT t) y = hO S T (p.up FS FT t) y := by
  have key : ∀ (A B C : AE D) (u : k), p.e * (A * B * C * p.ι u) = A * B * C * p.ι u := fun A B C u => by
    calc p.e * (A * B * C * p.ι u) = A * B * C * (p.e * p.ι u) := by ring
      _ = _ := by rw [e_mul_ι]
  unfold hO
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  exact key _ _ _ _

end GlobalTheory.LocSympl

namespace GlobalTheory.LocSympl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem psi_sympl_up (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle) (hχ : p.IsChar ψ ψk) (t : Matrix Y Y' k) (y : WO S T) :
    ψ (symplO S T (p.up FS FT t) y) = ψk (p.π (hO S T (p.up FS FT t) y)) := by
  rw [hχ, p.ι_π, e_mul_hO_up]
  rfl

theorem sum_four_eq_trace_mul {m n : Type} [Fintype m] [Fintype n] (A : Matrix m m k) (N : Matrix m n k) (B : Matrix n n k)
    (X : Matrix n m k) : ∑ a, ∑ b, ∑ c, ∑ d, A a b * N b c * B c d * X d a = Matrix.trace (A * N * B * X) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun d _ => Finset.sum_comm))

theorem pi_hO_up (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (t : Matrix Y Y' k)
    (N : Matrix (Fin S.rank) (Fin T.rank) k) :
    p.π (hO S T (p.up FS FT t) (N.transpose.map fun a => cA D (p.ι a))) =
      Matrix.trace ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * (FT.β * t * FS.γ)) := by
  unfold hO
  rw [← sum_four_eq_trace_mul]
  simp only [map_sum, map_mul]
  have hterm : ∀ a b c d, p.π (incA D (S.gram⁻¹ a b)) * p.π (cA D ((N.transpose.map fun a => cA D (p.ι a)) c b)) *
      p.π (incA D (T.gram c d)) * p.π (p.up FS FT t d a) =
      (S.gram⁻¹).map (p.π.comp (incA D)) a b * N b c * T.gram.map (p.π.comp (incA D)) c d * (FT.β * t * FS.γ) d a := by
    intro a b c d
    simp only [Matrix.map_apply, Matrix.transpose_apply, conj_conj, p.π_ι, Place.up, RingHom.comp_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => hterm a b c d

theorem exists_pairing (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (b : Matrix Y Y' k) :
    ∃ y : WO S T, IsHalf (cA D p.e) y ∧ ∀ t, p.π (hO S T (p.up FS FT t) y) = ∑ r, ∑ q, b r q * t r q := by
  set f := p.π.comp (incA D)
  set N : Matrix (Fin S.rank) (Fin T.rank) k := S.gram.map f * FS.β * b.transpose * FT.γ * (T.gram⁻¹).map f
  refine ⟨N.transpose.map fun a => cA D (p.ι a), fun i j => ?_, fun t => ?_⟩
  · show cA D p.e * cA D (p.ι _) = cA D (p.ι _)
    rw [← map_mul, e_mul_ι]
  · rw [pi_hO_up]
    have hA : (S.gram⁻¹).map f * S.gram.map f = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S), Matrix.map_one _ (map_zero f) (map_one f)]
    have hB : (T.gram⁻¹).map f * T.gram.map f = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit T), Matrix.map_one _ (map_zero f) (map_one f)]
    have hANB : (S.gram⁻¹).map f * N * T.gram.map f = FS.β * b.transpose * FT.γ := by
      simp only [N, Matrix.mul_assoc]
      rw [hB, Matrix.mul_one, ← Matrix.mul_assoc ((S.gram⁻¹).map f), hA, Matrix.one_mul]
    rw [hANB]
    rw [show FS.β * b.transpose * FT.γ * (FT.β * t * FS.γ) = FS.β * (b.transpose * (FT.γ * FT.β) * t * FS.γ) by
      simp only [Matrix.mul_assoc], FT.γβ, Matrix.mul_one, Matrix.trace_mul_comm, Matrix.mul_assoc, FS.γβ, Matrix.mul_one]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_comm

end GlobalTheory.LocSympl

namespace GlobalTheory.LocSympl

theorem halves_at_split : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → (∀ x, IsHalf p.e (p.up FS FT x) ∧ p.down FS FT (p.up FS FT x) = x) ∧ (∀ z : WO S T, IsHalf p.e z → p.up FS FT (p.down FS FT z) = z) ∧ (∀ x y, symplO S T (p.up FS FT x) (p.up FS FT y) = 0) ∧ (∀ t (y : WO S T), IsHalf (cA D p.e) y → ψ (symplO S T (p.up FS FT t) y) = ψk (p.π (hO S T (p.up FS FT t) y))) ∧ ∀ b : Matrix Y Y' k, ∃ y : WO S T, IsHalf (cA D p.e) y ∧ ∀ t, p.π (hO S T (p.up FS FT t) y) = ∑ r, ∑ q, b r q * t r q := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ ψk hχ
  exact ⟨fun x => ⟨up_half p FS FT x, down_up p FS FT x⟩, fun z hz => up_down p FS FT z hz,
    fun x y => by unfold symplO; rw [hO_up_up, mul_zero, map_zero],
    fun t y _ => psi_sympl_up p FS FT ψ ψk hχ t y, fun b => exists_pairing p FS FT b⟩

end GlobalTheory.LocSympl

end

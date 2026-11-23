import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CoordDnApply

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.DualPairCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke

section Gen
variable {M N : Type} [AddCommGroup M] [TopologicalSpace M] [AddCommGroup N] [TopologicalSpace N]

def SmoothAlong (Z : M → Prop) (f : M → ℂ) : Prop :=
  ∀ (k : ℕ) (L : (Fin k → ℝ) →+ M), Continuous L → (∀ t, Z (L t)) → ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)

theorem gen_smooth_iff {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] (Z : M → Prop)
    (r : P →+ M) (hr : Continuous r) (hZ : ∀ p, Z (r p)) (co : M →+ P) (hc : Continuous co)
    (h3 : ∀ z, Z z → r (co z) = z) (f : M → ℂ) :
    SmoothAlong Z f ↔ ∀ w, ContDiff ℝ ∞ fun p => f (w + r p) := by
  constructor
  · intro h w
    let e : P ≃L[ℝ] (Fin (Module.finrank ℝ P) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
    have := (h _ (r.comp e.symm.toLinearEquiv.toLinearMap.toAddMonoidHom) (hr.comp e.symm.continuous)
      (fun t => hZ _) w).comp e.contDiff
    convert this using 2 with p
    exact congrArg (fun q => f (w + r q)) (e.symm_apply_apply p).symm
  · intro h k L hL h0 w
    have := (h w).comp ((co.comp L).toRealLinearMap (hc.comp hL)).contDiff
    convert this using 2 with t
    exact congrArg (fun q => f (w + q)) (h3 _ (h0 t)).symm

theorem gen_smooth_comp (φ : M →+ N) (hφ : Continuous φ) (Z : M → Prop) (Z' : N → Prop) (hZ : ∀ x, Z x → Z' (φ x))
    (f : N → ℂ) (h : SmoothAlong Z' f) : SmoothAlong Z (f ∘ φ) := by
  intro k L hL h0 w
  have := h k (φ.comp L) (hφ.comp hL) (fun t => hZ _ (h0 t)) (φ w)
  convert this using 2 with t
  exact congrArg f (φ.map_add _ _)

theorem gen_smooth_equiv (φ : M ≃+ N) (h1 : Continuous φ) (h2 : Continuous φ.symm) (Z : M → Prop) (Z' : N → Prop)
    (hZ : ∀ x, Z' (φ x) ↔ Z x) (f : N → ℂ) : SmoothAlong Z' f ↔ SmoothAlong Z (f ∘ φ) := by
  refine ⟨gen_smooth_comp φ.toAddMonoidHom h1 Z Z' (fun x => (hZ x).2) f, fun h => ?_⟩
  have := gen_smooth_comp φ.symm.toAddMonoidHom h2 Z' Z (fun x hx => (hZ _).1 (by simpa using hx)) _ h
  convert this using 1
  funext x
  simp

theorem gen_level (φ : M ≃+ N) (h1 : Continuous φ) (h2 : Continuous φ.symm) (Z Q : M → Prop) (Z' Q' : N → Prop)
    (hZ : ∀ x, Z' (φ x) ↔ Z x) (hQ : ∀ x, Q' (φ x) ↔ Q x) :
    (∃ U : AddSubgroup N, IsOpen (U : Set N) ∧ ∀ u ∈ U, Z' u → Q' u) ↔
      ∃ U : AddSubgroup M, IsOpen (U : Set M) ∧ ∀ u ∈ U, Z u → Q u := by
  constructor
  · rintro ⟨U, hU, h⟩
    exact ⟨U.comap φ.toAddMonoidHom, hU.preimage h1, fun u hu h0 => (hQ u).1 (h _ hu ((hZ u).2 h0))⟩
  · rintro ⟨U, hU, h⟩
    refine ⟨U.comap φ.symm.toAddMonoidHom, hU.preimage h2, fun u hu h0 => ?_⟩
    obtain ⟨u, rfl⟩ := φ.surjective u
    exact (hQ u).2 (h u (by simpa using hu) ((hZ u).1 h0))

theorem gen_cont_equiv (φ : M ≃+ N) (h2 : Continuous φ.symm) (f : N → ℂ) (h : Continuous (f ∘ φ)) : Continuous f := by
  convert h.comp h2 using 1
  funext x
  simp

omit [TopologicalSpace M] [TopologicalSpace N] in
theorem gen_quasi (φ : M ≃+ N) (S : AddSubgroup M) (S' : AddSubgroup N) (hS : ∀ x, φ x ∈ S' ↔ x ∈ S)
    (κ : M → M → ℂ) (κ' : N → N → ℂ) (hκ : ∀ x y, κ' (φ x) (φ y) = κ x y) (f : N → ℂ) :
    (∀ γ ∈ S', ∀ w, f (γ + w) = κ' γ w * f w) ↔ ∀ γ ∈ S, ∀ w, (f ∘ φ) (γ + w) = κ γ w * (f ∘ φ) w := by
  simp only [φ.surjective.forall, hS, hκ, Function.comp_apply, map_add]

theorem gen_continuous [IsTopologicalAddGroup M] {A : Type} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] (ψ : AddChar A ℂ) (hψ : Continuous ψ) (s : M → M → A)
    (hs : Continuous fun p : M × M => s p.1 p.2) (R : M →+ M) (hR : Continuous R) (U : AddSubgroup M)
    (hU : IsOpen (U : Set M)) (g : M → ℂ) (h1 : ∀ w, Continuous fun d => g (w + R d))
    (h2 : ∀ d, d - R d ∈ U → ∀ x, ψ (s x (d - R d)) * g (x + (d - R d)) = g x) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro w₀
  have hd : Continuous fun w => w - w₀ := continuous_id.sub continuous_const
  have hu : Continuous fun w => (w - w₀) - R (w - w₀) := hd.sub (hR.comp hd)
  have hG : Continuous fun w => ψ (-s (w₀ + R (w - w₀)) ((w - w₀) - R (w - w₀))) * g (w₀ + R (w - w₀)) :=
    (hψ.comp (hs.comp ((continuous_const.add (hR.comp hd)).prodMk hu)).neg).mul ((h1 w₀).comp hd)
  refine hG.continuousAt.congr ?_
  filter_upwards [(hU.preimage hu).mem_nhds (show w₀ ∈ _ by simp)] with w hw
  rw [← h2 _ hw (w₀ + R (w - w₀)), ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one,
    one_mul]
  congr 1
  abel

theorem gen_cont_herm {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {a b : ℕ} (σ : R →+* R)
    (hσ : Continuous σ) (Ji : Matrix (Fin a) (Fin a) R) (K : Matrix (Fin b) (Fin b) R) (ξ : R) :
    Continuous fun p : Matrix (Fin a) (Fin b) R × Matrix (Fin a) (Fin b) R =>
      ξ * Matrix.trace ((Ji * Formalism.UG.cT σ p.2ᵀ * K)ᵀᵀ * p.1ᵀ) :=
  continuous_const.mul
    (((continuous_const.matrix_mul (continuous_snd.matrix_transpose.matrix_map
      hσ).matrix_transpose).matrix_mul continuous_const).matrix_transpose.matrix_transpose.matrix_mul
        continuous_fst.matrix_transpose).matrix_trace

end Gen

def realMat (D : D7) (m n : ℕ) :
    (Fin m → Fin n → (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ)) →+ Matrix (Fin m) (Fin n) (AE D) :=
  AddMonoidHom.mk' (fun p => Matrix.of fun i j => HeisenbergWeilMatrices.realPt D (p i j)) fun p q =>
    Matrix.ext fun i j => (realPtHom D).map_add (p i j) (q i j)

theorem continuous_realMat (D : D7) (m n : ℕ) : Continuous (realMat D m n) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_realPt D).comp ((continuous_apply j).comp (continuous_apply i))

theorem exists_coMat (D : D7) (m n : ℕ) : ∃ co : Matrix (Fin m) (Fin n) (AE D) →+
    (Fin m → Fin n → (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ)), Continuous co ∧
    (∀ z, (z - realMat D m n (co z)).map (infPart D) = 0) ∧ ∀ z, z.map (finPart D) = 0 → realMat D m n (co z) = z := by
  obtain ⟨co, h1, h2, h3⟩ := exists_co D
  exact ⟨AddMonoidHom.mk' (fun z i j => co (z i j)) fun z w => funext₂ fun i j => co.map_add _ _,
    continuous_pi fun i => continuous_pi fun j => h1.comp ((continuous_apply j).comp (continuous_apply i)),
    fun z => Matrix.ext fun i j => h2 (z i j),
    fun z hz => Matrix.ext fun i j => h3 (z i j) (congrFun₂ hz i j)⟩

theorem smoothAlong_iff {m n : ℕ} (f : Matrix (Fin m) (Fin n) (AE D) → ℂ) :
    SmoothAlong (fun z => z.map (finPart D) = 0) f ↔ ∀ w, ContDiff ℝ ∞ fun p => f (w + realMat D m n p) := by
  obtain ⟨co, c1, -, c3⟩ := exists_coMat D m n
  exact gen_smooth_iff (fun z : Matrix (Fin m) (Fin n) (AE D) => z.map (finPart D) = 0) (realMat D m n) (continuous_realMat D m n)
    (fun p => Matrix.ext fun i j => finPart_realPt D (p i j)) co c1 c3 f

theorem continuous_cA (D : D7) : Continuous (cA D) :=
  IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap

theorem continuous_hsymp (A B : HSp D) : Continuous fun p : HeisenbergWeilMatrices.WA A B × HeisenbergWeilMatrices.WA A B => HeisenbergWeilMatrices.hsymp p.1 p.2 :=
  continuous_const.mul ((IsModuleTopology.continuous_of_linearMap (HeisenbergWeilMatrices.trA D)).comp
    (gen_cont_herm (cA D) (continuous_cA D) (HeisenbergWeilMatrices.gramInvA A) (HeisenbergWeilMatrices.gramA B) (incA D D.host.xi0)))

theorem continuous_of_isTheta {A B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {g : HeisenbergWeilMatrices.WA A B → ℂ}
    (hg : HeisenbergWeilMatrices.IsTheta ψ g) : Continuous g := by
  obtain ⟨-, hs, U, hU, hl⟩ := hg
  obtain ⟨co, c1, c2, -⟩ := exists_coMat D A.rank B.rank
  exact gen_continuous ψ hψ HeisenbergWeilMatrices.hsymp (continuous_hsymp A B) ((realMat D _ _).comp co)
    ((continuous_realMat D _ _).comp c1) U hU g (fun w => (hs w).continuous.comp c1)
    fun d hd x => congrFun (hl _ hd (c2 d)) x

end GlobalTheory.DualPairCompare

end

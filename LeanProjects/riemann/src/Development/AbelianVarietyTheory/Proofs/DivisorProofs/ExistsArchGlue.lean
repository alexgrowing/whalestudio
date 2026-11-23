import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairLatticeLocalSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicVectorLatticeLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanIwasawaMajorantFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicArchimedeanEigenvectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSubgroupAdjointScalarStatement
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.IwLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

open Classical in

theorem exists_arch_glue (x : ∀ w : InfinitePlace F, GArch σ J w) (s : Finset (InfinitePlace F)) :
    ∃ q : GAd σ J, (∀ v, proj σ J v q = 1) ∧ ∀ w, projArch σ J w q = if w ∈ s then x w else 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, fun v => map_one _, fun w => by simp⟩
  | insert w s hw ih =>
    obtain ⟨q, h1, h2⟩ := ih
    refine ⟨embArch σ J w (x w) * q, fun v => by simp [h1 v], fun u => ?_⟩
    by_cases e : u = w
    · subst e; simp [h2 u, hw]
    · rw [map_mul, projArch_embArch_ne σ J e, one_mul, h2 u]; simp [Finset.mem_insert, e]

open Classical in

theorem exists_fin_glue (x : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), GLoc σ J v)
    (s : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) :
    ∃ q : GAd σ J, (∀ w, projArch σ J w q = 1) ∧ ∀ v, proj σ J v q = if v ∈ s then x v else 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, fun w => map_one _, fun v => by simp⟩
  | insert v s hv ih =>
    obtain ⟨q, h1, h2⟩ := ih
    refine ⟨emb σ J v (x v) * q, fun w => by simp [h1 w], fun u => ?_⟩
    by_cases e : u = v
    · subst e; simp [h2 u, hv]
    · rw [map_mul, proj_emb_ne σ J e, one_mul, h2 u]; simp [Finset.mem_insert, e]

theorem inv_mul_eq_smul {R : Type} [CommRing R] {m k : ℕ} (M : GL (Fin m) R) (X : Matrix (Fin m) (Fin k) R) (l : Rˣ)
    (h : M.1 * X = l.1 • X) : (M⁻¹).1 * X = (l⁻¹).1 • X := by
  have e : (M⁻¹).1 * (M.1 * X) = X := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [h, Matrix.mul_smul] at e
  calc (M⁻¹).1 * X = (l⁻¹).1 • (l.1 • ((M⁻¹).1 * X)) := by
        rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    _ = (l⁻¹).1 • X := by rw [e]

omit [NumberField F] [NumberField E] in

theorem first_cols {r : ℕ} (A B : Matrix (Fin n) (Fin (r + 1)) E) :
    cT (σ : E →+* E) (A.submatrix id (fun _ : Fin 1 => 0)) * J * B.submatrix id (fun _ : Fin 1 => 0) =
      (cT (σ : E →+* E) A * J * B).submatrix (fun _ => 0) (fun _ => 0) := by
  ext i j; simp [cT, Matrix.mul_apply]

end GlobalTheory.IwLine

namespace GlobalTheory.IwLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem yx_of_xy (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (x y : Matrix (Fin n) (Fin 1) E)
    (h : cT (σ : E →+* E) x * J * y = 1) : cT (σ : E →+* E) y * J * x = 1 := by
  have hs : ∀ z : E, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hσ.2.2.2, hσ.2.2.2, star_star])
  have key : (cT (σ : E →+* E) y * J * x) 0 0 = σ ((cT (σ : E →+* E) x * J * y) 0 0) := by
    simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, AlgHom.coe_toRingHom, hs,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← hJ.1 l k, hs]; ring
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0, key, h]
  simp

end GlobalTheory.IwLine

namespace GlobalTheory.IwLine

open Classical in

theorem iwasawa_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ (x : Matrix (Fin n) (Fin 1) E), x = X.submatrix id (fun _ => 0) → ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsAdapted σ J X Y L a → (∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧ ∃ k ∈ levelAll σ J L a, g = p * k) ∧ ∃ h : GAd σ J → ℝ, ∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l := by
  intro F E _ _ _ _ _ σ hσ hun n J hJ r X Y hW x hx L a hA
  haveI : Submodule.IsLattice E L := hA.lat
  set y : Matrix (Fin n) (Fin 1) E := Y.submatrix id (fun _ => 0) with hy
  have hxx : cT (σ : E →+* E) x * J * x = 0 := by
    rw [hx, first_cols, hW.xx]; rfl
  have hyy : cT (σ : E →+* E) y * J * y = 0 := by
    rw [hy, first_cols, hW.yy]; rfl
  have hxy : cT (σ : E →+* E) x * J * y = 1 := by
    rw [hx, hy, first_cols, hW.xy]; ext i j; simp [Matrix.one_apply, Subsingleton.elim i j]
  have hyx : cT (σ : E →+* E) y * J * x = 1 := yx_of_xy σ J hσ hJ x y hxy
  have loc : ∀ v (g : GLoc σ J v), ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧
      ∃ β : GL (Fin 1) (Fv F v ⊗[F] E),
        (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := fun v g =>
    if hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v then
      GlobalTheory.T.hyperbolic_pair_lattice_local_split F E σ hσ n J hJ x y hxx hyy hxy hyx L hA.lat v hs (hA.dual v) g
    else GlobalTheory.T.isotropic_vector_lattice_local F E σ hσ hun n J hJ x y hxx hyx L hA.lat v hs (hA.dual v) g
  have iw : ∀ g : GAd σ J, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧
      ∃ k ∈ levelAll σ J L a, g = p * k := by
    intro g
    choose pf kf hkf hf βf hβf using fun v => loc v (proj σ J v g)
    choose pa ka hka ha βa hβa using fun w => GlobalTheory.T.archimedean_iwasawa_majorant_frame F E σ hσ n J hJ x y hxx hyx a hA.maj w (projArch σ J w g)
    have hS := eventually_proj_mem_stabLoc σ J L g
    set S := (Filter.eventually_cofinite.1 hS).toFinset with hSdef
    obtain ⟨qa, qa1, qa2⟩ := exists_arch_glue σ J pa Finset.univ
    obtain ⟨qf, qf1, qf2⟩ := exists_fin_glue σ J pf S
    have pa' : ∀ w, projArch σ J w (qa * qf) = pa w := fun w => by
      rw [map_mul, qa2 w, qf1 w, mul_one, if_pos (Finset.mem_univ w)]
    have pf' : ∀ v, proj σ J v (qa * qf) = if v ∈ S then pf v else 1 := fun v => by
      rw [map_mul, qa1 v, qf2 v, one_mul]
    obtain ⟨l, hl⟩ := GlobalTheory.T.parabolic_archimedean_eigenvector F E σ n J x (cT (σ : E →+* E) y * J) hyx (qa * qf)
      (fun w => ⟨βa w, by rw [pa' w]; exact hβa w⟩) (fun v => by
        rw [pf' v]
        split_ifs
        · exact ⟨βf v, hβf v⟩
        · exact ⟨1, by simp⟩)
    refine ⟨qa * qf, l, hl, (qa * qf)⁻¹ * g, mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩,
      (mul_inv_cancel_left (qa * qf) g).symm⟩
    · rw [map_mul, map_inv, pf' v]
      split_ifs with h
      · rw [hf v, inv_mul_cancel_left]; exact hkf v
      · rw [inv_one, one_mul]
        by_contra hc
        exact h ((Set.Finite.mem_toFinset _).2 hc)
    · rw [map_mul, map_inv, pa' w, ha w, inv_mul_cancel_left]
      exact hka w
  refine ⟨iw, fun g => (absE F E (iw g).choose_spec.choose : ℝ), fun p l hp k hk => ?_⟩
  obtain ⟨hp', k', hk', e⟩ := (iw (p * k)).choose_spec.choose_spec
  set p' := (iw (p * k)).choose
  set l' := (iw (p * k)).choose_spec.choose
  have hK : p'⁻¹ * p ∈ levelAll σ J L a := by
    have : p'⁻¹ * p = k' * k⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, e, inv_mul_cancel_left]
    rw [this]; exact mul_mem hk' (inv_mem hk)
  have hm : (matHom _ σ J (p'⁻¹ * p)).1 * adMat F x = (l * l'⁻¹).1 • adMat F x := by
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hp, Matrix.mul_smul, map_inv,
      inv_mul_eq_smul _ _ _ hp', smul_smul, Units.val_mul]
  have h1 := GlobalTheory.T.level_subgroup_adjoint_scalar F E σ hσ n J L hA.lat a x (cT (σ : E →+* E) y * J) hyx _ hK _ hm
  rw [map_mul, map_inv, mul_inv_eq_one₀ (GlobalTheory.Doubling.hom_pos _ _).ne'] at h1
  show (absE F E l' : ℝ) = absE F E l
  rw [h1]

end GlobalTheory.IwLine

end

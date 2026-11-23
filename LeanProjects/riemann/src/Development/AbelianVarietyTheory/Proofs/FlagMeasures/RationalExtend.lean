import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.RatExt

section General
variable {E R : Type} [Field E] [CommRing R] (ι : E →+* R)

theorem single_comp {n : ℕ} (i : Fin n) :
    (fun j => ι ((Pi.single i 1 : Fin n → E) j)) = (Pi.single i 1 : Fin n → R) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem span_range {n : ℕ} :
    Submodule.span R (Set.range fun (x : Fin n → E) (i : Fin n) => ι (x i)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun R (Fin n)).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨Pi.single i 1, by simpa using single_comp ι i⟩

theorem lin_ext {n : ℕ} {M : Type} [AddCommGroup M] [Module R M] (a b : (Fin n → R) →ₗ[R] M)
    (h : ∀ x : Fin n → E, a (fun i => ι (x i)) = b (fun i => ι (x i))) : a = b :=
  LinearMap.ext_on_range (span_range ι) h

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {E R : Type} [Field E] [CommRing R] (ι : E →+* R) in
theorem _root_.GlobalTheory.HL.RatExt.exists_equiv {n : ℕ} (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    ∃ g' : (Fin n → R) ≃ₗ[R] (Fin n → R), ∀ x, g' (fun i => ι (x i)) = fun i => ι (g x i) := by
  set M := LinearMap.toMatrix' (g : (Fin n → E) →ₗ[E] (Fin n → E))
  set N := LinearMap.toMatrix' (g.symm : (Fin n → E) →ₗ[E] (Fin n → E))
  have hMN : M * N = 1 := by
    simp only [M, N, ← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  have hNM : N * M = 1 := by
    simp only [M, N, ← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  refine ⟨LinearEquiv.ofLinear (Matrix.toLin' (M.map ι)) (Matrix.toLin' (N.map ι)) ?_ ?_, ?_⟩
  · rw [← Matrix.toLin'_mul, ← Matrix.map_mul, hMN, Matrix.map_one _ (map_zero ι) (map_one ι),
      Matrix.toLin'_one]
  · rw [← Matrix.toLin'_mul, ← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero ι) (map_one ι),
      Matrix.toLin'_one]
  · intro x
    funext i
    simp only [LinearEquiv.ofLinear_apply, Matrix.toLin'_apply]
    have h := LinearMap.toMatrix'_mulVec (g : (Fin n → E) →ₗ[E] (Fin n → E)) x
    rw [show g x = M.mulVec x from h.symm, RingHom.map_mulVec]
    rfl

end General

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
private theorem exists_dual_family_of_linearIndependent {E : Type} [Field E] {n m : ℕ} {v : Fin m → Fin n → E}
    (hv : LinearIndependent E v) :
    ∃ φ : Fin m → (Fin n → E) →ₗ[E] E, ∀ a b, φ b (v a) = if a = b then 1 else 0 := by
  choose φ hφ using fun b =>
    LinearMap.exists_extend ((Module.Basis.span hv).coord b)
  refine ⟨φ, fun a b => ?_⟩
  have h := LinearMap.congr_fun (hφ b) ⟨v a, Submodule.subset_span (Set.mem_range_self a)⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h
  rw [h]
  have hb : (⟨v a, Submodule.subset_span (Set.mem_range_self a)⟩ : Submodule.span E (Set.range v))
      = Module.Basis.span hv a := by
    ext; simp [Module.Basis.span_apply]
  rw [hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in

theorem _root_.GlobalTheory.HL.RatExt.rational_extend : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig), ∀ (n : ℕ) (p : HeightOneSpectrum (𝓞 F)), Function.Injective (A.bc (n := n) p) ∧ Submodule.span (A.loc p).Ep (Set.range (A.bc (n := n) p)) = ⊤ ∧ (∀ g : (Fin n → E) ≃ₗ[E] (Fin n → E), ∃! g', A.Ext p g g') ∧ (∀ (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) g' (Λ : Submodule (𝓞 E) (Fin n → E)), A.Ext p g g' → A.lat p (Λ.map ((g : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))) = g' • A.lat p Λ) ∧ (∀ (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E), _root_.GlobalTheory.HL.hf (A.L p) (Hm.map (A.loc p).ιE) (A.bc p x) (A.bc p y) = (A.loc p).ιE (∑ i, ∑ j, x i * Hm i j * sig (y j))) ∧ ∀ (m : ℕ) (v : Fin m → Fin n → E), LinearIndependent E v ↔ LinearIndependent (A.loc p).Ep fun a => A.bc p (v a) := by
  intro F E _ _ _ _ _ sig A n p
  have hbc : ∀ x : Fin n → E, A.bc p x = fun i => (A.loc p).ιE (x i) := fun _ => rfl
  haveI : Nontrivial (A.loc p).Ep := by
    have h := (A.L p).rank
    exact Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by omega)
  have hinj : Function.Injective (A.bc (n := n) p) := by
    intro x y h
    funext i
    exact (A.loc p).ιE.injective (congrFun h i)
  have hspan : Submodule.span (A.loc p).Ep (Set.range (A.bc (n := n) p)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun (A.loc p).Ep (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    rw [hbc, Pi.basisFun_apply]
    funext j
    rcases eq_or_ne j i with rfl | h <;> simp [*]
  have hext : ∀ g : (Fin n → E) ≃ₗ[E] (Fin n → E), ∃ g', A.Ext p g g' := by
    intro g
    obtain ⟨g', hg'⟩ := _root_.GlobalTheory.HL.RatExt.exists_equiv (A.loc p).ιE g
    exact ⟨g', fun x => hg' x⟩
  refine ⟨hinj, hspan, fun g => ?_, fun g g' Λ hg => ?_, fun Hm x y => ?_, fun m v => ?_⟩
  · obtain ⟨g', hg'⟩ := hext g
    refine ⟨g', hg', fun g'' hg'' => ?_⟩
    apply LinearEquiv.toLinearMap_injective
    refine LinearMap.ext_on_range hspan fun x => ?_
    simp only [LinearEquiv.coe_coe]
    rw [hg'' x, hg' x]
  · unfold _root_.GlobalTheory.HL.Places.lat
    rw [Submodule.smul_span]
    congr 1
    rw [Submodule.map_coe, Set.image_image, ← Set.image_smul, Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [LinearEquiv.smul_def, hg x]
    rfl
  · unfold _root_.GlobalTheory.HL.hf
    rw [_root_.GlobalTheory.HL.Places.L_cj]
    simp [hbc, map_sum, map_mul, Matrix.map_apply, _root_.Formalism.MainNotions.S.Loc.LocAt.cj_ιE]
  · constructor
    · intro hv
      obtain ⟨φ, hφ⟩ := exists_dual_family_of_linearIndependent hv
      rw [Fintype.linearIndependent_iff]
      intro c hc b
      have key : ∀ a, ∑ j, (A.loc p).ιE (v a j) *
          (A.loc p).ιE (φ b (fun k => if j = k then 1 else 0)) = if a = b then 1 else 0 := by
        intro a
        have h := congrArg (A.loc p).ιE (LinearMap.pi_apply_eq_sum_univ (φ b) (v a))
        rw [hφ] at h
        simp only [map_sum, smul_eq_mul, map_mul] at h
        rw [← h]
        split_ifs <;> simp
      calc c b = ∑ a, c a * (if a = b then 1 else 0) := by simp
        _ = ∑ a, c a * ∑ j, (A.loc p).ιE (v a j) *
              (A.loc p).ιE (φ b (fun k => if j = k then 1 else 0)) := by simp only [key]
        _ = ∑ j, (∑ a, c a • A.bc p (v a)) j *
              (A.loc p).ιE (φ b (fun k => if j = k then 1 else 0)) := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hbc, Finset.mul_sum,
            Finset.sum_mul, mul_assoc]
          exact Finset.sum_comm
        _ = 0 := by rw [hc]; simp
    · intro hv
      rw [Fintype.linearIndependent_iff] at hv ⊢
      intro c hc a
      have h := hv (fun a => (A.loc p).ιE (c a)) (by
        funext j
        have hj := congrFun hc j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hbc] at hj ⊢
        rw [← map_zero (A.loc p).ιE, ← hj, map_sum]
        simp [map_mul])
      exact (map_eq_zero_iff _ (A.loc p).ιE.injective).mp (h a)

end GlobalTheory.HL.RatExt

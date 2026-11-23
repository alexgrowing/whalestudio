import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPositiveDefiniteQuadraticFormEndomorphismsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyTorsionFiniteEndomorphismDivisibleStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SimilitudeDefiniteFormIsAlgebraicOnVectorStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS
open Polynomial

theorem exists_surj_of_torsion {N : Type} [AddCommGroup N] [Finite N] (l n c : ℕ) (hn : ∀ x : N, l ^ n • x = 0)
    (hc : Nat.card {x : N // l • x = 0} ≤ c) :
    ∃ π : (Fin c → ℤ) →ₗ[ℤ] N, Function.Surjective π := by
  classical
  let m : N →+ N := nsmulAddMonoidHom l
  have h1 : Nat.card (N ⧸ m.range) = Nat.card m.ker := by
    have a := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup m.range
    have b := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup m.ker
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange m).toEquiv, _root_.mul_comm] at b
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (a.symm.trans b)
  have h2 : Nat.card (N ⧸ m.range) ≤ Nat.card (Fin c) := by
    rw [h1, Nat.card_fin]; exact hc
  obtain ⟨e⟩ : Nonempty ((N ⧸ m.range) ↪ Fin c) := by
    have := Fintype.ofFinite (N ⧸ m.range)
    apply Function.Embedding.nonempty_of_card_le
    simpa using h2
  let v : Fin c → N := fun i => (Function.invFun e i).out
  let π : (Fin c → ℤ) →ₗ[ℤ] N := Fintype.linearCombination ℤ v
  have hv : ∀ i, v i ∈ LinearMap.range π := fun i => ⟨Pi.single i 1, by simp [π]⟩
  have key : ∀ j : ℕ, ∀ x : N, ∃ y : N, x - l ^ j • y ∈ LinearMap.range π := by
    intro j
    induction j with
    | zero => exact fun x => ⟨x, by simp⟩
    | succ j ih =>
      intro x
      obtain ⟨y, hy⟩ := ih x
      have h3 : (QuotientAddGroup.mk (v (e y)) : N ⧸ m.range) = QuotientAddGroup.mk y := by
        simp only [v, QuotientAddGroup.out_eq']
        exact Function.leftInverse_invFun e.injective _
      obtain ⟨z, hz⟩ := QuotientAddGroup.eq.1 h3
      have hz' : l • z = - v (e y) + y := hz
      refine ⟨z, ?_⟩
      have : x - l ^ (j + 1) • z = (x - l ^ j • y) + l ^ j • v (e y) := by
        rw [pow_succ, mul_smul, hz', smul_add, smul_neg]; abel
      rw [this]
      exact add_mem hy (nsmul_mem (hv _) _)
  refine ⟨π, fun x => ?_⟩
  obtain ⟨y, hy⟩ := key n x
  rwa [hn, sub_zero] at hy

theorem aeval_intertwine {M N : Type} [AddCommGroup M] [AddCommGroup N] (π : M →ₗ[ℤ] N) (S : Module.End ℤ M)
    (T : Module.End ℤ N) (h : ∀ x, T (π x) = π (S x)) (p : ℤ[X]) : ∀ x, aeval T p (π x) = π (aeval S p x) := by
  induction p using Polynomial.induction_on with
  | C a => intro x; rw [aeval_C, aeval_C, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  | add p q hp hq => intro x; simp [hp, hq]
  | monomial n a ih =>
    intro x
    rw [pow_succ, ← _root_.mul_assoc, map_mul, map_mul (aeval _) _ X, aeval_X, aeval_X, Module.End.mul_apply,
      Module.End.mul_apply, h, ih]

theorem exists_monic_of_surj {N : Type} [AddCommGroup N] (c : ℕ) (π : (Fin c → ℤ) →ₗ[ℤ] N)
    (hπ : Function.Surjective π) (T : Module.End ℤ N) :
    ∃ χ : ℤ[X], χ.Monic ∧ χ.natDegree = c ∧ aeval T χ = 0 := by
  obtain ⟨S, hS⟩ := Module.projective_lifting_property π (T ∘ₗ π) hπ
  have h := aeval_intertwine π S T fun x => (LinearMap.congr_fun hS x).symm
  refine ⟨S.charpoly, S.charpoly_monic, by simp [LinearMap.charpoly_natDegree], ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := hπ x
  rw [h, LinearMap.aeval_self_charpoly]
  simp

theorem exists_monic_torsion {M : Type} [AddCommGroup M] (l : ℕ) (hf : ∀ n : ℕ, Finite {x : M // l ^ n • x = 0})
    (T : Module.End ℤ M) : ∃ r : ℕ, ∀ n : ℕ, ∃ χ : ℤ[X], χ.Monic ∧ χ.natDegree = r ∧
      ∀ x : M, l ^ n • x = 0 → aeval T χ x = 0 := by
  refine ⟨Nat.card {x : M // l ^ 1 • x = 0}, fun n => ?_⟩
  let N : Submodule ℤ M := LinearMap.ker (l ^ n • LinearMap.id)
  have hN : ∀ x : M, x ∈ N ↔ l ^ n • x = 0 := fun x => Iff.rfl
  have : Finite N := by
    have := hf n
    exact Finite.of_equiv _ (Equiv.subtypeEquivRight fun x => (hN x).symm)
  have hT : ∀ x ∈ N, T x ∈ N := fun x hx => by
    rw [hN] at hx ⊢
    rw [← map_nsmul, hx, map_zero]
  have := hf 1
  obtain ⟨π, hπ⟩ := exists_surj_of_torsion (N := N) l n (Nat.card {x : M // l ^ 1 • x = 0})
    (fun x => Subtype.ext ((hN _).1 x.2))
    (Nat.card_le_card_of_injective (fun x => (⟨x.1.1, by rw [pow_one]; exact congrArg Subtype.val x.2⟩ :
      {x : M // l ^ 1 • x = 0})) fun x y h => Subtype.ext (Subtype.ext (by simpa using h)))
  obtain ⟨χ, h1, h2, h3⟩ := exists_monic_of_surj _ π hπ (T.restrict hT)
  refine ⟨χ, h1, h2, fun x hx => ?_⟩
  have h := aeval_intertwine N.subtype (T.restrict hT) T (fun _ => rfl) χ ⟨x, (hN x).2 hx⟩
  rw [h3] at h
  exact h

section
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]

noncomputable def ptEnd (F : End B) (hF : IsMonHom (show B ⟶ B from F)) (Z : Over S) :
    Module.End ℤ (Additive (Z ⟶ B)) :=
  (MonoidHom.toAdditive (IsMonHom.monoidHom (show B ⟶ B from F) Z)).toIntLinearMap

theorem ptEnd_pow (F : End B) (hF : IsMonHom (show B ⟶ B from F)) {Z : Over S} (x : Z ⟶ B) (n : ℕ) :
    (ptEnd F hF Z ^ n) (Additive.ofMul x) = Additive.ofMul (x ≫ (show B ⟶ B from F ^ n)) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact congrArg Additive.ofMul (Category.comp_id x).symm
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, ih]
    exact congrArg Additive.ofMul (Category.assoc x (show B ⟶ B from F ^ n) (show B ⟶ B from F))

theorem aeval_ptEnd (F : End B) (hF : IsMonHom (show B ⟶ B from F)) {Z : Over S} (x : Z ⟶ B) (P : ℤ[X]) :
    aeval (ptEnd F hF Z) P (Additive.ofMul x) = Additive.ofMul (polyPt F P x) := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply]
  change _ = Additive.ofMul (∏ n ∈ Finset.range (P.natDegree + 1), (x ≫ (show B ⟶ B from F ^ n)) ^ P.coeff n)
  rw [ofMul_prod]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [LinearMap.smul_apply, ptEnd_pow, ofMul_zpow]

noncomputable def evalPt {Z : Over S} (x : Z ⟶ B) : Additive (B ⟶ B) →ₗ[ℤ] Additive (Z ⟶ B) :=
  (AddMonoidHom.mk' (fun f => Additive.ofMul (x ≫ Additive.toMul f))
    fun f g => by rw [toMul_add, MonObj.comp_mul, ofMul_mul]).toIntLinearMap

noncomputable def homSub (B : Over S) [GrpObj B] [IsCommMonObj B] : Submodule ℤ (Additive (B ⟶ B)) :=
  AddSubgroup.toIntSubmodule
    { carrier := {f | IsMonHom (Additive.toMul f)}
      zero_mem' := by
        change IsMonHom (1 : B ⟶ B)
        rw [Hom.one_def]; infer_instance
      add_mem' := fun {f g} hf hg => by
        change IsMonHom (Additive.toMul f) at hf
        change IsMonHom (Additive.toMul g) at hg
        change IsMonHom (Additive.toMul f * Additive.toMul g)
        rw [Hom.mul_def]; infer_instance
      neg_mem' := fun {f} hf => by
        change IsMonHom (Additive.toMul f) at hf
        change IsMonHom (Additive.toMul f)⁻¹
        infer_instance }

end

theorem exists_poly_normSq_roots : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∀ (F : End B) (q : ℕ), IsMonHom (show B ⟶ B from F) → PullPow (show B ⟶ B from F).left L q → ∃ P : Polynomial ℤ, P ≠ 0 ∧ (∀ β : ℂ, Polynomial.aeval β P = 0 → Complex.normSq β = q) ∧ ∀ x : (𝟙_ (Over (Sp k)) ⟶ B), polyPt F P x = 1 := by
  intro k _ _ B _ hB L hL F q hF hq
  have := hB.comm
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ (l : k) ≠ 0 := by
    by_cases h : ((2 : ℕ) : k) = 0
    · refine ⟨2 + 1, by norm_num, ?_⟩
      rw [Nat.cast_add, h]; simp
    · exact ⟨2, le_rfl, h⟩
  have hD := fun n : ℕ => GlobalTheory.T.abelianVariety_torsion_finite_endomorphism_divisible k B hB (l ^ n) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl)
  obtain ⟨Q, Q1, Q2, Q3, Q4⟩ := GlobalTheory.T.exists_positiveDefinite_quadraticForm_endomorphisms k B hB L hL
  obtain ⟨r, hr⟩ := exists_monic_torsion (M := Additive (𝟙_ (Over (Sp k)) ⟶ B)) l (fun n => (hD n).1) (ptEnd F hF _)
  have hT : ∀ f ∈ homSub B, ptEnd F hF B f ∈ homSub B := fun f hf => by
    change IsMonHom (Additive.toMul f) at hf
    change IsMonHom (Additive.toMul f ≫ (show B ⟶ B from F))
    infer_instance
  let e : homSub B := ⟨Additive.ofMul (𝟙 B), inferInstanceAs (IsMonHom (𝟙 B))⟩
  let φ : Module.End ℤ (homSub B) := (ptEnd F hF B).restrict hT
  have hev : ∀ (x : 𝟙_ (Over (Sp k)) ⟶ B) (p : ℤ[X]), aeval (ptEnd F hF _) p (Additive.ofMul x) =
      Additive.ofMul (x ≫ Additive.toMul (aeval φ p e).1) := fun x p => by
    have h := aeval_intertwine (evalPt x ∘ₗ (homSub B).subtype) φ (ptEnd F hF _)
      (fun f => congrArg Additive.ofMul (Category.assoc x (Additive.toMul f.1) (show B ⟶ B from F))) p e
    have h' : (evalPt x ∘ₗ (homSub B).subtype) e = Additive.ofMul x := congrArg Additive.ofMul (Category.comp_id x)
    rw [h'] at h
    exact h
  obtain ⟨P, hP, h0, hβ⟩ := GlobalTheory.T.similitude_definite_form_isAlgebraic_on_vector (homSub B) (fun f => Q (Additive.toMul f.1)) φ e q l r hl2
    (fun x y => by
      have := Q1 (Additive.toMul x.1) (Additive.toMul y.1)
      rw [sub_eq_add_neg]
      exact this)
    (fun x => Q2 _) (fun x hx => Subtype.ext (Q3 _ x.2 hx)) (fun x => Q4 _ q hq _)
    (fun n => by
      obtain ⟨χ, h1, h2, h3⟩ := hr n
      obtain ⟨g, hg, hg'⟩ := (hD n).2 (Additive.toMul (aeval φ χ e).1) (aeval φ χ e).2 fun x hx =>
        (hev x χ).symm.trans (h3 (Additive.ofMul x) hx)
      exact ⟨χ, ⟨Additive.ofMul g, hg⟩, h1, h2, Subtype.ext hg'⟩)
  refine ⟨P, hP, hβ, fun x => ?_⟩
  have h := (aeval_ptEnd F hF x P).symm.trans (hev x P)
  rw [h0] at h
  exact h.trans (MonObj.comp_one x)

end GlobalTheory.SS

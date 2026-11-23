import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.CartanCoinv

open GlobalTheory.PRep

section Gen
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)

theorem sub_mem_coinv {k : G} (hk : k ∈ K) (v : V) : ρ k v - v ∈ twKer ρ K 1 :=
  Submodule.subset_span ⟨⟨k, hk⟩, v, by simp⟩

theorem apply_mem_coinv {k : G} (hk : k ∈ K) {v : V} (hv : v ∈ twKer ρ K 1) : ρ k v ∈ twKer ρ K 1 := by
  have := (twKer ρ K 1).add_mem (sub_mem_coinv ρ K hk v) hv
  simpa using this

theorem mem_coinv_of_eigen {k : G} (hk : k ∈ K) {v : V} {c : ℂ} (hc : c ≠ 1) (hv : ρ k v = c • v) :
    v ∈ twKer ρ K 1 := by
  have h := (twKer ρ K 1).smul_mem (c - 1)⁻¹ (sub_mem_coinv ρ K hk v)
  have e : (c - 1)⁻¹ • (ρ k v - v) = v := by
    have : ρ k v - v = (c - 1) • v := by rw [hv, sub_smul, one_smul]
    rw [this, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hc), one_smul]
  rwa [e] at h

end Gen

def diagUnit {R : Type} [CommRing R] {a : ℕ} (f : Fin a → Rˣ) : GL (Fin a) R where
  val := Matrix.diagonal fun i => (f i : R)
  inv := Matrix.diagonal fun i => ((f i)⁻¹ : Rˣ)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp

theorem exists_diag {L : Type} [Field L] (O : Subring L) {a : ℕ} (ha : 1 ≤ a) (u : Lˣ) (h1 : (u : L) ∈ O)
    (h2 : ((u⁻¹ : Lˣ) : L) ∈ O) : ∃ d ∈ Formalism.UG.GLint (Fin a) O, Matrix.GeneralLinearGroup.det d = u ∧
      ∃ f : Fin a → L, (d : Matrix (Fin a) (Fin a) L) = Matrix.diagonal f := by
  let u' : Oˣ := ⟨⟨u, h1⟩, ⟨(u⁻¹ : Lˣ), h2⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  let f : Fin a → Oˣ := Function.update 1 ⟨0, ha⟩ u'
  have hm : ((Formalism.UG.bc O.subtype (diagUnit f) : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) =
      Matrix.diagonal fun i => ((f i : O) : L) := by
    change (Matrix.diagonal fun i => (f i : O)).map O.subtype = _
    rw [Matrix.diagonal_map (map_zero _)]
    rfl
  refine ⟨Formalism.UG.bc O.subtype (diagUnit f), ⟨_, rfl⟩, ?_, _, hm⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, hm, Matrix.det_diagonal,
    Finset.prod_eq_single (⟨0, ha⟩ : Fin a)]
  · simp [f, u']
  · intro b _ hb
    simp [f, Function.update_of_ne hb]
  · simp

theorem translate_mem_twKer : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (u : (w.adicCompletion E)ˣ), 1 ≤ a → Valued.v (u : w.adicCompletion E) = 1 → χ u ≠ 1 → ∀ y : V, (∀ k ∈ GlobalTheory.LFun.KGL w a, ρ k y = (((χ (Matrix.GeneralLinearGroup.det k))⁻¹ : ℂˣ) : ℂ) • y) → ∀ g, ρ g y ∈ GlobalTheory.PRep.twKer ρ (GlobalTheory.LFun.KGL w a) 1 := by
  intro E _ _ w a V _ _ ρ χ u ha hu hχ y hy g
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  obtain ⟨ex, -, k₁, hk₁, k₂, hk₂, e⟩ :=
    Formalism.UG.Final.CartanDecomp E w a ϖ (GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ) hϖ g
  set D : GL (Fin a) (w.adicCompletion E) := k₁⁻¹ * g * k₂⁻¹ with hDdef
  have hD : (D : Matrix (Fin a) (Fin a) (w.adicCompletion E)) = Formalism.UG.diagPow E w ϖ ex := by
    rw [hDdef, Units.val_mul, Units.val_mul, e]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hg : g = k₁ * D * k₂ := by rw [hDdef]; group
  clear_value D
  have h1 : (u : w.adicCompletion E) ∈ Formalism.UG.Ov E w := by
    change Valued.v (u : w.adicCompletion E) ≤ 1
    exact hu.le
  have h2 : ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ∈ Formalism.UG.Ov E w := by
    change Valued.v ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  obtain ⟨d, hd, hdet, f, hf⟩ := exists_diag (Formalism.UG.Ov E w) ha u h1 h2
  have hcomm : d * D = D * d := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD, hf, Formalism.UG.diagPow, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hDy : ρ D y ∈ twKer ρ (GlobalTheory.LFun.KGL w a) 1 := by
    refine mem_coinv_of_eigen ρ _ hd (c := (((χ u)⁻¹ : ℂˣ) : ℂ)) ?_ ?_
    · intro h
      exact hχ (inv_eq_one.1 (Units.ext h))
    · rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, hy d hd, hdet, map_smul]
  rw [hg, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hy k₂ hk₂, map_smul, map_smul]
  exact Submodule.smul_mem _ _ (apply_mem_coinv ρ _ hk₁ hDy)

end GlobalTheory.CartanCoinv

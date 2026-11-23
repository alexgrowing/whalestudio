import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate ComplexOrder Matrix

namespace GlobalTheory.Up.Definite

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

theorem _root_.GlobalTheory.Up.Definite.herm_one (x y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (1 : Matrix (Fin r) (Fin r) E) x y = ∑ a, x a * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y a) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Matrix.one_apply, Ne.symm hb]
  · simp

open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

theorem _root_.GlobalTheory.Up.Definite.map_herm_one_self (φ : E →+* ℂ) (x : Fin r → E) :
    φ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm (1 : Matrix (Fin r) (Fin r) E) x x) = ((∑ a, ‖φ (x a)‖ ^ 2 : ℝ) : ℂ) := by
  rw [_root_.GlobalTheory.Up.Definite.herm_one, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, _root_.ReciprocityTheory.ChartRestriction.G.FD.emb_cc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

variable (E r) in

def intVec : Submodule (𝓞 E) (Fin r → E) := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.Up.Definite.mem_intVec (x : Fin r → E) :
    x ∈ _root_.GlobalTheory.Up.Definite.intVec E r ↔ ∀ a, IsIntegral ℤ (x a) := by
  simp only [_root_.GlobalTheory.Up.Definite.intVec, Submodule.mem_pi, Set.mem_univ, true_implies,
    Submodule.mem_one]
  refine forall_congr' fun a => ⟨?_, fun h => ⟨⟨x a, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact y.isIntegral_coe

open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.Up.Definite.single_mem_intVec (b : Fin r) :
    (Pi.single b 1 : Fin r → E) ∈ _root_.GlobalTheory.Up.Definite.intVec E r := by
  rw [_root_.GlobalTheory.Up.Definite.mem_intVec]
  intro a
  by_cases h : a = b
  · subst h
    simpa using isIntegral_one
  · simpa [h] using isIntegral_zero

open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [IsCMField E] in
private theorem finite_GL_of_scaled_entries_integral_bounded (c : E) (hc : c ≠ 0) (B : ℝ) :
    {γ : GL (Fin r) E | ∀ a b, IsIntegral ℤ (c * (γ : Matrix (Fin r) (Fin r) E) a b) ∧
      ∀ φ : E →+* ℂ, ‖φ (c * (γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ B}.Finite := by
  have hT := Embeddings.finite_of_norm_le E ℂ B
  have hpi : (Set.univ.pi fun _ : Fin r => Set.univ.pi fun _ : Fin r =>
      {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ B}).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => hT
  have hinj : Function.Injective fun γ : GL (Fin r) E => fun a b => c * (γ : Matrix (Fin r) (Fin r) E) a b := by
    intro γ δ h
    ext a b
    exact mul_left_cancel₀ hc (congrFun (congrFun h a) b)
  refine (hpi.preimage hinj.injOn).subset fun γ hγ => ?_
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
  exact fun a b => hγ a b

open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [IsCMField E] in

theorem _root_.GlobalTheory.Up.Definite.finite_small :
    {γ : GL (Fin r) E | ∀ a b, IsIntegral ℤ ((γ : Matrix (Fin r) (Fin r) E) a b) ∧
      ∀ φ : E →+* ℂ, ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 1}.Finite := by
  simpa using finite_GL_of_scaled_entries_integral_bounded (r := r) (1 : E) one_ne_zero 1

variable (E r) in

noncomputable def data : Data E r where
  Ψ := (inhab (E := E)).Ψ
  cmType := inhab.cmType
  Gm := 1
  Gm_herm a b := by by_cases h : a = b <;> simp [Matrix.one_apply, h, eq_comm, cc_one, cc_zero]
  Gm_det := by simp
  p0 := r
  p0_le := le_rfl
  signature τ := by
    refine ⟨1, by simp, ?_⟩
    ext a b
    by_cases h : a = b <;>
      simp [gram, hermC, col, sgn, Matrix.one_apply, Matrix.diagonal_apply, h, eq_comm, apply_ite]
  Λ := intVec E r
  Λ_fg := Submodule.fg_pi fun _ => by rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  Λ_span := by
    rw [eq_top_iff, ← (Pi.basisFun E (Fin r)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨b, rfl⟩
    rw [Pi.basisFun_apply]
    exact single_mem_intVec b
  den := 1
  den_ne := one_ne_zero
  Λ_int x hx y hy := by
    rw [mem_intVec] at hx hy
    rw [herm_one, show ((1 : 𝓞 E) : E) = 1 by simp, one_mul]
    exact IsIntegral.sum _ fun a _ => (hx a).mul (isIntegral_cc (hy a))
  Γ := ⊥
  Γ_stab γ hγ := by
    rw [Subgroup.mem_bot] at hγ
    subst hγ
    simp [IsUStab]
  Γ_index := by
    refine ⟨finite_small.toFinset, fun γ hγ => ⟨γ, ?_, by simp⟩⟩
    rw [Set.Finite.mem_toFinset]
    intro a b
    have hcol : (γ : Matrix (Fin r) (Fin r) E) *ᵥ (Pi.single b 1) =
        fun a => (γ : Matrix (Fin r) (Fin r) E) a b := by
      ext a; simp
    have hi := (mem_intVec _).mp ((hγ.2 _).mp (single_mem_intVec b))
    rw [hcol] at hi
    refine ⟨hi a, fun φ => ?_⟩
    have h1 := congrArg φ (hγ.1 (Pi.single b 1) (Pi.single b 1))
    rw [map_herm_one_self, map_herm_one_self, hcol] at h1
    have h2 : ∑ a, ‖φ ((Pi.single b 1 : Fin r → E) a)‖ ^ 2 = 1 := by
      rw [Finset.sum_eq_single b] <;> simp +contextual
    have h3 := Complex.ofReal_injective h1
    rw [h2] at h3
    have h4 := Finset.single_le_sum (f := fun a => ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
    rw [h3] at h4
    nlinarith [norm_nonneg (φ ((γ : Matrix (Fin r) (Fin r) E) a b))]
  Γ_free γ hγ _ _ _ _ _ := Subgroup.mem_bot.mp hγ
  χ _ _ := 1
  χ_mul := by intros; simp
  χ_add := by intros; simp
  χ_fin _ := ⟨1, one_pos, by intros; simp⟩
  ξ0 := (inhab (E := E)).ξ0
  ξ0_im := inhab.ξ0_im
  ξ0_ne := inhab.ξ0_ne
  κ0 := (inhab (E := E)).κ0
  κ0_xi := inhab.κ0_xi
  κ0_sign := inhab.κ0_sign
  m := 1
  m_pos := one_pos
  transv ξ _ hiso s _ _ := by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 := congrArg φ hiso
    rw [map_herm_one_self, map_zero, Complex.ofReal_eq_zero,
      Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _] at h1
    have hξ : ∀ a, ξ a = 0 := fun a => by simpa using h1 a (Finset.mem_univ a)
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    ext a b
    simp [transvMat, hξ, Matrix.one_apply]

theorem gram_one (τ : E →+* ℂ) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ (1 : Matrix (Fin r) (Fin r) E) x = (x.map conj)ᴴ * x.map conj := by
  ext a b
  simp [gram, hermC, col, Matrix.one_apply, apply_ite, Matrix.mul_apply]

theorem mem_dom (x : Frame (data E r).Ψ r) : x ∈ (data E r).dom ↔ ∀ τ, (mat x τ).det ≠ 0 := by
  refine ⟨fun h τ => (h τ).1, fun h τ => ⟨h τ, fun i => ?_⟩⟩
  have hp : psgn r i = 1 := by
    refine Finset.prod_eq_one fun a ha => ?_
    have := Finset.mem_range.mp ha
    have := i.isLt
    exact if_pos (by omega)
  have hd : ((mat x τ).map conj).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using h τ
  have hpd : (gram τ.1 (1 : Matrix (Fin r) (Fin r) E) (mat x τ)).PosDef := by
    rw [gram_one]
    exact Matrix.PosDef.conjTranspose_mul_self _
      (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hd.isUnit))
  have := (hpd.submatrix (Fin.castLE_injective (Nat.le_of_lt_succ i.isLt))).det_pos
  change 0 < psgn r i * (lminor (gram τ.1 (1 : Matrix (Fin r) (Fin r) E) (mat x τ)) i).re
  rw [hp, one_mul]
  exact (Complex.lt_def.mp this).1

omit [NumberField E] [IsCMField E] in

theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact 1 x = x := by
  funext τ
  simp only [lact, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rfl

theorem card_cmType (X : Data E r) (h : Module.finrank ℚ E = 2) : Fintype.card X.Ψ = 1 := by
  classical
  have hc : Fintype.card (E →+* ℂ) = 2 := by rw [Embeddings.card, h]
  have hb : X.Ψ.card = X.Ψᶜ.card := by
    refine Finset.card_bij (fun τ _ => ComplexEmbedding.conjugate τ)
      (fun τ hτ => Finset.mem_compl.mpr ((X.cmType τ).mp hτ)) (fun _ _ _ _ h => star_injective h)
      fun τ hτ => ⟨ComplexEmbedding.conjugate τ, (X.cmType _).mpr ?_, star_star τ⟩
    rw [show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ from star_star τ]
    exact Finset.mem_compl.mp hτ
  have := X.Ψ.card_add_card_compl
  rw [Fintype.card_coe]
  omega

end GlobalTheory.Up.Definite

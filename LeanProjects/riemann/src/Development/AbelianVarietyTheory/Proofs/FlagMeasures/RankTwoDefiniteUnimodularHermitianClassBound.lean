import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassNumberLeMinkowskiCount
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootDiscrGeThreeHalvesOfIsTotallyComplexStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnimodularPlaneSplitAlongVectorStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardUnimodularGluingsTwoLinesLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardRealGeneratedIdealsLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsShortVectorUnimodularHermitianLatticeRankTStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardRankOneHermitianLatticeClassesLeStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.RankTwoCount

theorem enat_card_sigma_le {α : Type*} {β : α → Type*} (a b : ℕ) (ha : ENat.card α ≤ a)
    (hb : ∀ i, ENat.card (β i) ≤ b) : ENat.card (Σ i, β i) ≤ ((a * b : ℕ) : ENat) := by
  classical
  haveI : Finite α := ENat.card_lt_top.1 (lt_of_le_of_lt ha (ENat.coe_lt_top a))
  haveI : ∀ i, Finite (β i) := fun i => ENat.card_lt_top.1 (lt_of_le_of_lt (hb i) (ENat.coe_lt_top b))
  haveI := Fintype.ofFinite α
  rw [ENat.card_eq_coe_natCard] at ha ⊢
  have ha' : Nat.card α ≤ a := by exact_mod_cast ha
  have hb' : ∀ i, Nat.card (β i) ≤ b := fun i => by
    have := hb i
    rw [ENat.card_eq_coe_natCard] at this
    exact_mod_cast this
  rw [Nat.card_sigma]
  have h1 : ∑ i, Nat.card (β i) ≤ Fintype.card α * b := by
    simpa using Finset.sum_le_card_nsmul Finset.univ (fun i => Nat.card (β i)) b (fun i _ => hb' i)
  rw [← Nat.card_eq_fintype_card] at h1
  exact_mod_cast h1.trans (Nat.mul_le_mul_right b ha')

theorem enat_card_le_of_rel {α β : Type*} (P : α → β → Prop) (h : ∀ a, ∃ b, P a b)
    (hu : ∀ a a' b, P a b → P a' b → a = a') : ENat.card α ≤ ENat.card β := by
  choose f hf using h
  exact ENat.card_le_card_of_injective (f := f) fun a a' e => hu a a' (f a) (hf a) (e ▸ hf a')

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def LineRel (X Y : E × Submodule (𝓞 E) E) : Prop :=
  ∃ c : E, c ≠ 0 ∧ star c * Y.1 * c = X.1 ∧ ∀ y, c * y ∈ Y.2 ↔ y ∈ X.2

theorem lineRel_equivalence : Equivalence (LineRel (E := E)) where
  refl X := ⟨1, one_ne_zero, by simp, by simp⟩
  symm := by
    rintro X Y ⟨c, hc, h1, h2⟩
    have hs : star c ≠ 0 := by simpa using hc
    refine ⟨c⁻¹, inv_ne_zero hc, ?_, fun y => ?_⟩
    · rw [← h1, star_inv₀]; field_simp
    · rw [← h2, mul_inv_cancel_left₀ hc]
  trans := by
    rintro X Y Z ⟨c, hc, h1, h2⟩ ⟨d, hd, k1, k2⟩
    refine ⟨d * c, mul_ne_zero hd hc, ?_, fun y => ?_⟩
    · rw [← h1, ← k1, star_mul]; ring
    · rw [← h2, ← k2, mul_assoc]

theorem lineRel_out {p : E × Submodule (𝓞 E) E → Prop} (Y : {X // p X}) :
    LineRel (Quot.out (Quot.mk (fun X Y : {X // p X} => LineRel X.1 Y.1) Y)).1 Y.1 := by
  have he : Equivalence (fun X Y : {X // p X} => LineRel X.1 Y.1) :=
    ⟨fun X => lineRel_equivalence.refl _, fun h => lineRel_equivalence.symm h,
      fun h k => lineRel_equivalence.trans h k⟩
  exact he.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq _))

theorem form_transport {r : ℕ} (J g : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    star y ⬝ᵥ ((gᴴ * J * g) *ᵥ x) = star (g *ᵥ y) ⬝ᵥ (J *ᵥ (g *ᵥ x)) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

def pull {r : ℕ} (γ : GL (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) : Submodule (𝓞 E) (Fin r → E) :=
  Λ.comap ((Matrix.mulVecLin (γ : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E))

theorem mem_pull {r : ℕ} (γ : GL (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (y : Fin r → E) :
    y ∈ pull γ Λ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ y ∈ Λ := Iff.rfl

theorem mulVec_inv_cancel {r : ℕ} (γ : GL (Fin r) E) (y : Fin r → E) :
    (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y) = y := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem inv_mulVec_cancel {r : ℕ} (γ : GL (Fin r) E) (y : Fin r → E) :
    ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = y := by
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem pull_isLattice {r : ℕ} (γ : GL (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (h : Submodule.IsLattice E Λ) : Submodule.IsLattice E (pull γ Λ) := by
  have hm : pull γ Λ = Λ.map ((Matrix.mulVecLin
      ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E)) := by
    ext y
    rw [mem_pull, Submodule.mem_map]
    constructor
    · intro hy
      exact ⟨_, hy, inv_mulVec_cancel γ y⟩
    · rintro ⟨x, hx, rfl⟩
      change (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x) ∈ Λ
      rwa [mulVec_inv_cancel]
  refine ⟨hm ▸ h.fg.map _, ?_⟩
  rw [eq_top_iff]
  intro y _
  have hy : (γ : Matrix (Fin r) (Fin r) E) *ᵥ y ∈ Submodule.span E (Λ : Set (Fin r → E)) := by
    rw [h.span_eq_top]; trivial
  have := Submodule.mem_map_of_mem (f := Matrix.mulVecLin
      ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) hy
  rw [Submodule.map_span, Matrix.mulVecLin_apply, inv_mulVec_cancel] at this
  rw [hm]
  exact this

theorem pull_unimodular {r : ℕ} (γ : GL (Fin r) E) (J : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E))
    (h : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) (x : Fin r → E) :
    x ∈ pull γ Λ ↔ ∀ y ∈ pull γ Λ, star y ⬝ᵥ (((γ : Matrix (Fin r) (Fin r) E)ᴴ * J *
      (γ : Matrix (Fin r) (Fin r) E)) *ᵥ x) ∈ (algebraMap (𝓞 E) E).range := by
  rw [mem_pull, h]
  constructor
  · intro H y hy
    rw [form_transport]
    exact H _ hy
  · intro H y hy
    have := H (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y)
      (by rw [mem_pull, mulVec_inv_cancel]; exact hy)
    rwa [form_transport, mulVec_inv_cancel] at this

theorem pull_pos {r : ℕ} (γ : GL (Fin r) E) (J : Matrix (Fin r) (Fin r) E)
    (h : ∀ (φ : E →+* ℂ) (y : Fin r → E), y ≠ 0 → 0 < (φ (star y ⬝ᵥ (J *ᵥ y))).re)
    (φ : E →+* ℂ) (y : Fin r → E) (hy : y ≠ 0) :
    0 < (φ (star y ⬝ᵥ (((γ : Matrix (Fin r) (Fin r) E)ᴴ * J *
      (γ : Matrix (Fin r) (Fin r) E)) *ᵥ y))).re := by
  rw [form_transport]
  refine h φ _ fun h0 => hy ?_
  rw [← inv_mulVec_cancel γ y, h0, mulVec_zero]

noncomputable def diagGL (c d : E) (hc : c ≠ 0) (hd : d ≠ 0) : GL (Fin 2) E :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![c, d]) (by simp [Fin.prod_univ_two, hc, hd])

theorem diag_conj (c d b e : E) :
    (Matrix.diagonal ![c, d])ᴴ * Matrix.diagonal ![b, e] * Matrix.diagonal ![c, d] =
      Matrix.diagonal ![star c * b * c, star d * e * d] := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp

theorem diag_mulVec (c d s t : E) : Matrix.diagonal ![c, d] *ᵥ ![s, t] = ![c * s, d * t] := by
  ext i
  fin_cases i <;> simp [mulVec_diagonal]

abbrev Lines (N : Submodule (𝓞 E) E) : Type :=
  {X : E × Submodule (𝓞 E) E // star X.1 = X.1 ∧ (∀ φ : E →+* ℂ, 0 < (φ X.1).re) ∧
    Submodule.IsLattice E X.2 ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ X.2, ∃ y ∈ X.2, t = star x * X.1 * y} = N}

abbrev LineCls (N : Submodule (𝓞 E) E) : Type := Quot (fun X Y : Lines N => LineRel X.1 Y.1)

abbrev Glued (X₁ X₂ : E × Submodule (𝓞 E) E) : Type :=
  {M : Submodule (𝓞 E) (Fin 2 → E) // Submodule.IsLattice E M ∧
    (∀ x, x ∈ M ↔ ∀ y ∈ M, star y ⬝ᵥ ((Matrix.diagonal ![X₁.1, X₂.1]) *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) ∧
    (∀ t, t ∈ X₁.2 ↔ ![t, 0] ∈ M) ∧ ∀ t, t ∈ X₂.2 ↔ ![0, t] ∈ M}

variable (E) in

def realIdeals (Y : ℝ) : Set (Ideal (𝓞 E)) :=
  {𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2}

variable (E) in

abbrev GlueData (Y : ℝ) : Type :=
  Σ 𝔫 : realIdeals E Y,
    Σ q₁ : LineCls (Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫.1),
      Σ q₂ : LineCls (Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫.1),
        Glued (Quot.out q₁).1 (Quot.out q₂).1

theorem card_glueData_le (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) (Y : ℝ) (hY : 1 ≤ Y) :
    ENat.card (GlueData E Y) ≤ (((realIdeals E Y).ncard * ((classNumber E * 2 ^ Formalism.HermitianLatticesTheory.fDeg E) *
      ((classNumber E * 2 ^ Formalism.HermitianLatticesTheory.fDeg E) * ⌊Y ^ 2⌋₊)) : ℕ) : ENat) := by
  refine enat_card_sigma_le _ _ ?_ fun 𝔫 => enat_card_sigma_le _ _ (GlobalTheory.T.card_rankOne_hermitian_lattice_classes_le E hE _) fun q₁ =>
    enat_card_sigma_le _ _ (GlobalTheory.T.card_rankOne_hermitian_lattice_classes_le E hE _) fun q₂ => ?_
  · have hf : (realIdeals E Y).Finite := (GlobalTheory.T.ncard_realGenerated_ideals_le E hE Y hY).1
    rw [hf.cast_ncard_eq]
    exact le_rfl
  · obtain ⟨a1, a2, a3, a4⟩ := (Quot.out q₁).2
    obtain ⟨b1, b2, b3, b4⟩ := (Quot.out q₂).2
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have ha : (Quot.out q₁).1.1 ≠ 0 := fun h => by simpa [h] using a2 φ
    have hb : (Quot.out q₂).1.1 ≠ 0 := fun h => by simpa [h] using b2 φ
    refine (GlobalTheory.T.card_unimodular_gluings_two_lines_le E hE _ _ _ _ 𝔫.1 a1 b1 ha hb a3 b3 a4).trans ?_
    exact_mod_cast Nat.le_floor 𝔫.2.2.2

theorem defClassNum_le_card (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) :
    defClassNum E 2 ≤ ENat.card (GlueData E ((2 * Formalism.HermitianLatticesTheory.vInv E) ^ Formalism.HermitianLatticesTheory.fDeg E)) := by
  unfold defClassNum
  refine enat_card_le_of_rel (fun c t => ∃ X, Quot.mk _ X = c ∧
    X.1 = (Matrix.diagonal ![(Quot.out t.2.1).1.1, (Quot.out t.2.2.1).1.1], t.2.2.2.1)) ?_ ?_
  · intro c
    obtain ⟨⟨⟨J, Λ⟩, hJ, hpos, hlat, huni⟩, rfl⟩ := Quot.exists_rep c
    obtain ⟨u, hu, hu0, hub⟩ := GlobalTheory.T.exists_short_vector_unimodular_hermitian_lattice_rank_two E hE J hJ hpos Λ hlat huni
    obtain ⟨γ, β₁, β₂, N₁, N₂, 𝔫, hγ, s₁, s₂, hp, l₁, l₂, m₁, m₂, e₁, e₂, n0, nr, nb⟩ :=
      GlobalTheory.T.definiteUnimodularPlane_split_along_vector E hE J hJ hpos Λ hlat huni u hu hu0 _ hub
    have h𝔫 : 𝔫 ∈ realIdeals E ((2 * Formalism.HermitianLatticesTheory.vInv E) ^ Formalism.HermitianLatticesTheory.fDeg E) :=
      ⟨n0, nr, by rwa [← pow_mul, mul_comm _ 2]⟩
    let Y₁ : Lines (Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫) := ⟨(β₁, N₁), s₁, fun φ => (hp φ).1, l₁, e₁⟩
    let Y₂ : Lines (Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫) := ⟨(β₂, N₂), s₂, fun φ => (hp φ).2, l₂, e₂⟩
    obtain ⟨c₁, hc₁, k₁, j₁⟩ := lineRel_out Y₁
    obtain ⟨c₂, hc₂, k₂, j₂⟩ := lineRel_out Y₂
    set q₁ : LineCls (Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫) := Quot.mk _ Y₁ with hq₁
    set q₂ : LineCls (Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫) := Quot.mk _ Y₂ with hq₂
    let δ : GL (Fin 2) E := γ * diagGL c₁ c₂ hc₁ hc₂
    have hδv : (δ : Matrix (Fin 2) (Fin 2) E) = γ * Matrix.diagonal ![c₁, c₂] := rfl
    have hδ : (δ : Matrix (Fin 2) (Fin 2) E)ᴴ * J * (δ : Matrix (Fin 2) (Fin 2) E) =
        Matrix.diagonal ![(Quot.out q₁).1.1, (Quot.out q₂).1.1] := by
      rw [← k₁, ← k₂, ← diag_conj, ← hγ, hδv, conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have hu' := pull_unimodular δ J Λ huni
    have hp' := pull_pos δ J hpos
    have hh : ((δ : Matrix (Fin 2) (Fin 2) E)ᴴ * J * (δ : Matrix (Fin 2) (Fin 2) E))ᴴ =
        (δ : Matrix (Fin 2) (Fin 2) E)ᴴ * J * (δ : Matrix (Fin 2) (Fin 2) E) := by
      have hJ' : Jᴴ = J := hJ
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, hJ', Matrix.mul_assoc]
    rw [hδ] at hu' hp' hh
    have hl' := pull_isLattice δ Λ hlat
    refine ⟨⟨⟨𝔫, h𝔫⟩, q₁, q₂, pull δ Λ, hl', hu', fun t => ?_, fun t => ?_⟩,
      ⟨(_, pull δ Λ), hh, hp', hl', hu'⟩, Quot.sound ⟨δ, hδ, fun y => Iff.rfl⟩, rfl⟩
    · rw [mem_pull, hδv, ← mulVec_mulVec, diag_mulVec, mul_zero, ← m₁]
      exact (j₁ t).symm
    · rw [mem_pull, hδv, ← mulVec_mulVec, diag_mulVec, mul_zero, ← m₂]
      exact (j₂ t).symm
  · rintro _ _ t ⟨X, rfl, hX⟩ ⟨X', rfl, hX'⟩
    rw [Subtype.ext (hX.trans hX'.symm)]

theorem rankTwoClasses : RankTwoClasses := by
  intro E _ _ _ hE
  obtain ⟨hdeg, -, hrd, hsq⟩ := GlobalTheory.T.rootDiscr_ge_three_halves_of_isTotallyComplex E hE.1
  set f := Formalism.HermitianLatticesTheory.fDeg E with hf
  set ρ := 2 * Formalism.HermitianLatticesTheory.vInv E with hρ
  have hρ1 : 1 ≤ ρ := by linarith
  have hY : 1 ≤ ρ ^ f := one_le_pow₀ hρ1
  have h1 := (defClassNum_le_card hE).trans (card_glueData_le hE _ hY)
  have h2 : ((realIdeals E (ρ ^ f)).ncard : ℝ) ≤ ρ ^ f * (1 + Real.log (ρ ^ f)) ^ f :=
    (GlobalTheory.T.ncard_realGenerated_ideals_le E hE _ hY).2
  have h3 := GlobalTheory.classNumber_le_minkowski_count E
  rw [← hf, ← hρ] at h1
  rw [hsq, hdeg] at h3
  rw [Real.log_pow] at h2 h3
  have h4 : ((⌊(ρ ^ f) ^ 2⌋₊ : ℕ) : ℝ) ≤ (ρ ^ f) ^ 2 := Nat.floor_le (by positivity)
  have hL : 0 ≤ 1 + f * Real.log ρ := by
    have := Real.log_nonneg hρ1
    positivity
  refine (ENat.toENNReal_le.2 h1).trans ?_
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  set L := 1 + f * Real.log ρ
  calc _ ≤ (ρ ^ f * L ^ f) * ((ρ ^ f * L ^ (2 * f) * 2 ^ f) * ((ρ ^ f * L ^ (2 * f) * 2 ^ f) * (ρ ^ f) ^ 2)) := by
        gcongr
    _ = _ := by
        have h44 : (4 : ℝ) ^ f = 2 ^ f * 2 ^ f := by rw [← mul_pow]; norm_num
        rw [h44]
        clear_value L ρ f
        ring

end GlobalTheory.RankTwoCount

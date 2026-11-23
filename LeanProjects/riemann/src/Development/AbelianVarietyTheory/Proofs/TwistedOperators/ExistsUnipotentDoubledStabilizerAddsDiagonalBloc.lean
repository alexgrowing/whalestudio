import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetAdelicUnitaryPreservesLatticeAlmostA
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacUnip

section Alg

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {n : Type} [Fintype n] [DecidableEq n]

def uni (Z : Matrix n n A) : Matrix (n ⊕ n) (n ⊕ n) A := Matrix.fromBlocks (1 + Z) (-Z) Z (1 - Z)

theorem uni_mul_uni_neg (Z : Matrix n n A) : uni Z * uni (-Z) = 1 := by
  rw [uni, uni, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1 <;> noncomm_ring

def uniGL (Z : Matrix n n A) : GL (n ⊕ n) A :=
  ⟨uni Z, uni (-Z), uni_mul_uni_neg Z, by simpa using uni_mul_uni_neg (-Z)⟩

theorem uni_unitary (c : A →ₐ[R] A) (J Z : Matrix n n A) (h : Zᵀ * J + J * Z.map c = 0) :
    (uni Z)ᵀ * dbl J * (uni Z).map c = dbl J := by
  have h1 : (1 + Z).map c = 1 + Z.map c := by
    rw [Matrix.map_add _ (map_add c), Matrix.map_one _ (map_zero c) (map_one c)]
  have h2 : (1 - Z).map c = 1 - Z.map c := by
    rw [Matrix.map_sub _ (map_sub c), Matrix.map_one _ (map_zero c) (map_one c)]
  have h3 : (-Z).map c = - Z.map c := by
    ext i j; simp
  have h4 : J * Z.map c = - (Zᵀ * J) := eq_neg_of_add_eq_zero_right h
  rw [uni, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, h1, h2, h3, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_neg]
  generalize Z.map c = Zc at *
  generalize Zᵀ = Zt at *
  congr 1
  · calc _ = J + (Zt * J + J * Zc) := by noncomm_ring
      _ = J := by rw [h, add_zero]
  · calc _ = - (Zt * J + J * Zc) := by noncomm_ring
      _ = 0 := by rw [h, neg_zero]
  · calc _ = - (Zt * J + J * Zc) := by noncomm_ring
      _ = 0 := by rw [h, neg_zero]
  · calc _ = -J + (Zt * J + J * Zc) := by noncomm_ring
      _ = -J := by rw [h, add_zero]

theorem uni_mul_diagCols (Z : Matrix n n A) : uni Z * (diagCols n : Matrix (n ⊕ n) n A) = diagCols n := by
  rw [uni, diagCols, Matrix.fromBlocks_mul_fromRows]
  congr 1 <;> simp

theorem smul_uni_sub_one (u : R) (Z : Matrix n n A) (h : u • Z = 0) : u • (uni Z - 1) = 0 := by
  have h' : ∀ i j, u • Z i j = 0 := fun i j => congrFun (congrFun h i) j
  ext (i | i) (j | j) <;> simp [uni, Matrix.one_apply, h']

theorem uni_mulVec_inl (Z : Matrix n n A) (z : n ⊕ n → A) :
    (uni Z *ᵥ z) ∘ Sum.inl = z ∘ Sum.inl + Z *ᵥ (z ∘ Sum.inl - z ∘ Sum.inr) := by
  rw [uni, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec,
    Matrix.mulVec_sub]
  abel

theorem uni_mulVec_inr (Z : Matrix n n A) (z : n ⊕ n → A) :
    (uni Z *ᵥ z) ∘ Sum.inr = z ∘ Sum.inr + Z *ᵥ (z ∘ Sum.inl - z ∘ Sum.inr) := by
  rw [uni, Matrix.fromBlocks_mulVec, Sum.elim_comp_inr, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_sub]
  abel

theorem blocks_uni_mul (Z : Matrix n n A) (g : Matrix (n ⊕ n) (n ⊕ n) A) :
    (uni Z * g).toBlocks₁₁ + (uni Z * g).toBlocks₁₂ + (uni Z * g).toBlocks₂₁ + (uni Z * g).toBlocks₂₂ =
      g.toBlocks₁₁ + g.toBlocks₁₂ + g.toBlocks₂₁ + g.toBlocks₂₂ +
        (Z + Z) * (g.toBlocks₁₁ + g.toBlocks₁₂ - g.toBlocks₂₁ - g.toBlocks₂₂) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks g, uni, Matrix.fromBlocks_multiply]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂]
  noncomm_ring

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evFin_invOf_two_mem {v : Pl F} (h : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have h0 : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  rw [h0, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (algebraMap (𝓞 F) F 2) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 h
  rw [map_ofNat] at h1
  have h2 : Valued.v (algebraMap F (Fv F v) (2 : F)⁻¹) = v.valuation F (2 : F)⁻¹ :=
    v.valuedAdicCompletion_eq_valuation' _
  simp only [map_inv₀] at h2
  rw [h1, inv_one, map_ofNat] at h2
  rw [map_inv₀, h2]

theorem uni_mulVec_mem {d : ℕ} (W : Spc F E d) (v : Pl F) (Z : Matrix (Fin d) (Fin d) (AE F E))
    (hZ : ∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ∀ z ∈ GlobalTheory.DblVac.latD W v, uni Z *ᵥ z ∈ GlobalTheory.DblVac.latD W v := by
  intro z hz
  refine ⟨?_, ?_⟩
  · rw [uni_mulVec_inl]; exact add_mem hz.1 (hZ _ (sub_mem hz.1 hz.2))
  · rw [uni_mulVec_inr]; exact add_mem hz.2 (hZ _ (sub_mem hz.1 hz.2))

theorem mul_mem_KD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} {p g : GlobalTheory.DblVac.UD σ W}
    (hp : p ∈ GlobalTheory.DblVac.KD σ W v) (hg : g ∈ GlobalTheory.DblVac.KD σ W v) : p * g ∈ GlobalTheory.DblVac.KD σ W v := by
  have hm : ∀ a b : GlobalTheory.DblVac.UD σ W, GlobalTheory.DblVac.matD (a * b) = GlobalTheory.DblVac.matD a * GlobalTheory.DblVac.matD b :=
    fun _ _ => rfl
  refine ⟨fun u hu => ?_, fun z hz => ⟨?_, ?_⟩⟩
  · have e : GlobalTheory.DblVac.matD (p * g) - 1 =
        (GlobalTheory.DblVac.matD p - 1) * GlobalTheory.DblVac.matD g + (GlobalTheory.DblVac.matD g - 1) := by
      rw [hm]; noncomm_ring
    rw [e, smul_add, ← Matrix.smul_mul, hp.1 u hu, hg.1 u hu, Matrix.zero_mul, add_zero]
  · rw [hm, ← Matrix.mulVec_mulVec]
    exact (hp.2 _ (hg.2 z hz).1).1
  · rw [mul_inv_rev, hm, ← Matrix.mulVec_mulVec]
    exact (hg.2 _ (hp.2 z hz).2).2

theorem exists_unip : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Y : Matrix (Fin d) (Fin d) (AE F E),
      At (evFin F v) Y → (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 →
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ ∀ g ∈ GlobalTheory.DblVac.KD σ W v, p * g ∈ GlobalTheory.DblVac.KD σ W v ∧
        GlobalTheory.DblVac.diagonalBlockOfMatrix (p * g) = GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂)) := by
  intro F E _ _ _ _ _ σ d W v h2 Y hAt hL hY
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin d) (Fin d) (AE F E), Z = ⅟(2 : AF F) • Y := ⟨_, rfl⟩
  have hZZ : Z + Z = Y := by
    rw [← two_smul (AF F) Z, hZ, smul_smul, mul_invOf_self, one_smul]
  have hZc : Z.map (cA σ) = ⅟(2 : AF F) • Y.map (cA σ) := by
    rw [hZ]; ext i j; simp
  have hZu : Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0 := by
    rw [hZc, hZ, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hY, smul_zero]
  have hZL : ∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    rw [hZ, Matrix.smul_mulVec]
    exact GlobalTheory.LatAlmostAll.smul_mem_latAt W v (evFin_invOf_two_mem h2) (hL z hz)
  have hZL' : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (-Z) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    rw [Matrix.neg_mulVec]
    exact neg_mem (hZL z hz)
  let p : GlobalTheory.DblVac.UD σ W := ⟨uniGL Z, uni_unitary (cA σ) (incM F W.J) Z hZu⟩
  have hp : p ∈ GlobalTheory.DblVac.KD σ W v := by
    refine ⟨fun u hu => ?_, fun z hz => ⟨uni_mulVec_mem W v Z hZL z hz, uni_mulVec_mem W v (-Z) hZL' z hz⟩⟩
    refine smul_uni_sub_one u Z ?_
    rw [hZ, smul_comm, hAt u hu, smul_zero]
  refine ⟨p, hp, ⟨1, ?_⟩, fun g hg => ⟨mul_mem_KD hp hg, ?_⟩⟩
  · exact (uni_mul_diagCols Z).trans (Matrix.mul_one _).symm
  · have e : GlobalTheory.DblVac.matD (p * g) = uni Z * GlobalTheory.DblVac.matD g := rfl
    rw [GlobalTheory.DblVac.diagonalBlockOfMatrix, GlobalTheory.DblVac.diagonalBlockOfMatrix, e, blocks_uni_mul, smul_add, hZZ, Matrix.mul_smul]

end GlobalTheory.DblVacUnip

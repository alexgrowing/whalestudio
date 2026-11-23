import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameDualGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSmallUnitary

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviFrameH

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_herm {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (a b : Fin n → E) : form σ J a b = σ (form σ J b a) := by
  have hs : ∀ i j, σ (J i j) = J j i := fun i j => hJ j i
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hs, GlobalTheory.PlaneFrame.conj_conj hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem frame_dual (σ : E →ₐ[F] E) (B : Base F E) {d : ℕ} (W : Spc F E d) {r s d₁ : ℕ} (W₁ : Spc F E d₁)
    (H' : Plane E d d₁) {i₀ i₁ : ℕ} (hσ : IsCMExt F E σ) (hW : W.IsHerm σ B r s)
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁) : ∃ π : Matrix (Fin d₁) (Fin d) E, π * H'.ι = 1 ∧
      Matrix.vecMulVec H'.x (W.J *ᵥ fun i => σ (H'.y i)) + H'.ι * π + Matrix.vecMulVec H'.y (W.J *ᵥ fun i => σ (H'.x i)) = 1 := by
  obtain ⟨hrank, hxx, hyy, hxy, horth, -, -, hsplit, -, -, -⟩ := hH
  subst hrank
  have hhe := form_herm hσ hW.herm
  have hyx : form σ W.J H'.y H'.x = 1 := by rw [hhe, hxy, map_one]
  have hlin : ∀ (u : Fin d₁ → E) (a b : E) (w : Fin (d₁ + 2) → E),
      form σ W.J (H'.ι *ᵥ u + (a • H'.x + b • H'.y)) w =
        form σ W.J (H'.ι *ᵥ u) w + a * form σ W.J H'.x w + b * form σ W.J H'.y w := by
    intro u a b w
    simp only [form, add_dotProduct, smul_dotProduct, smul_eq_mul]; ring
  let Φ : ((Fin d₁ → E) × E × E) →ₗ[E] (Fin (d₁ + 2) → E) :=
    H'.ι.mulVecLin.coprod ((LinearMap.toSpanSingleton E _ H'.x).coprod (LinearMap.toSpanSingleton E _ H'.y))
  have hΦ : ∀ p, Φ p = H'.ι *ᵥ p.1 + (p.2.1 • H'.x + p.2.2 • H'.y) := fun p => rfl
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hW.lat.span_eq_top, Submodule.span_le]
    intro z hz
    obtain ⟨a, b, u, -, -, -, rfl⟩ := hsplit z hz
    exact ⟨(u, a, b), by rw [hΦ]; abel⟩
  have hinj : Function.Injective Φ := by
    rw [LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hsurj
    · simp [Module.finrank_prod]
  let eΦ := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  let πl : (Fin (d₁ + 2) → E) →ₗ[E] (Fin d₁ → E) := LinearMap.fst E _ _ ∘ₗ eΦ.symm.toLinearMap
  have hπ : ∀ p, πl (Φ p) = p.1 := by
    intro p
    simp only [πl, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.fst_apply]
    rw [show Φ p = eΦ p from rfl, LinearEquiv.symm_apply_apply]
  refine ⟨LinearMap.toMatrix' πl, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one, LinearMap.comp_apply, Matrix.toLin'_apply]
    have := hπ (u, 0, 0)
    rw [hΦ] at this
    simpa using this
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun z => ?_
    obtain ⟨⟨u, a, b⟩, rfl⟩ := hsurj z
    rw [Matrix.toLin'_one, LinearMap.id_apply, Matrix.toLin'_apply]
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec,
      ← Matrix.mulVec_mulVec, show LinearMap.toMatrix' πl *ᵥ Φ (u, a, b) = πl (Φ (u, a, b)) from
        (Matrix.toLin'_apply _ _).symm.trans (by rw [Matrix.toLin'_toMatrix']), hπ]
    have e1 : (W.J *ᵥ fun i => σ (H'.y i)) ⬝ᵥ Φ (u, a, b) = a := by
      rw [dotProduct_comm, ← form, hΦ, hlin, (horth u).2, hxy, hyy]; ring
    have e2 : (W.J *ᵥ fun i => σ (H'.x i)) ⬝ᵥ Φ (u, a, b) = b := by
      rw [dotProduct_comm, ← form, hΦ, hlin, (horth u).1, hxx, hyx]; ring
    rw [e1, e2, hΦ]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul]
    ring

end GlobalTheory.LeviFrameH

namespace GlobalTheory.LeviFrameH

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem frame_facts (σ : E →ₐ[F] E) (B : Base F E) {d : ℕ} (W : Spc F E d) {r s d₁ : ℕ} (W₁ : Spc F E d₁)
    (H' : Plane E d d₁) {i₀ i₁ : ℕ} (hσ : IsCMExt F E σ) (hW : W.IsHerm σ B r s)
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁) : ∃ π : Matrix (Fin d₁) (Fin d) E, π * H'.ι = 1 ∧ π *ᵥ H'.x = 0 ∧
      π *ᵥ H'.y = 0 ∧ H'.ιᵀ * W.J = W₁.J * π.map σ ∧ W.J * H'.ι.map σ = πᵀ * W₁.J := by
  obtain ⟨π, hπι, hF⟩ := frame_dual σ B W W₁ H' hσ hW hH
  have hhe := form_herm hσ hW.herm
  set a : Fin d → E := W.J *ᵥ fun i => σ (H'.y i) with ha
  set b : Fin d → E := W.J *ᵥ fun i => σ (H'.x i) with hb
  have hax : a ⬝ᵥ H'.x = 1 := by rw [dotProduct_comm]; exact hH.xy
  have hbx : b ⬝ᵥ H'.x = 0 := by rw [dotProduct_comm]; exact hH.xx
  have hay : a ⬝ᵥ H'.y = 0 := by rw [dotProduct_comm]; exact hH.yy
  have hby : b ⬝ᵥ H'.y = 1 := by
    rw [dotProduct_comm]; show form σ W.J H'.y H'.x = 1
    rw [hhe, hH.xy, map_one]
  have hker : ∀ v, H'.ι *ᵥ (π *ᵥ v) = 0 → π *ᵥ v = 0 := fun v hv => by
    rw [← Matrix.one_mulVec (π *ᵥ v), ← hπι, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have hπx : π *ᵥ H'.x = 0 := by
    apply hker
    have := congrArg (· *ᵥ H'.x) hF
    simp only [Matrix.add_mulVec, Matrix.vecMulVec_mulVec, hax, hbx, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, MulOpposite.op_one, one_smul, MulOpposite.op_zero, zero_smul, add_zero] at this
    simpa using this
  have hπy : π *ᵥ H'.y = 0 := by
    apply hker
    have := congrArg (· *ᵥ H'.y) hF
    simp only [Matrix.add_mulVec, Matrix.vecMulVec_mulVec, hay, hby, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, MulOpposite.op_zero, MulOpposite.op_one, one_smul, zero_smul, zero_add] at this
    simpa using this
  have hιv : ∀ v : Fin d → E, (∀ u, form σ W.J (H'.ι *ᵥ u) v = 0) → H'.ιᵀ *ᵥ (W.J *ᵥ fun i => σ (v i)) = 0 := by
    intro v hv
    ext j
    have := hv (Pi.single j 1)
    simp only [form, Matrix.mulVec_single_one] at this
    rw [Matrix.mulVec_transpose]
    simpa [Matrix.vecMul, dotProduct, Matrix.transpose_apply, mul_comm] using this
  have hvι : ∀ v : Fin d → E, (∀ u, form σ W.J v (H'.ι *ᵥ u) = 0) → v ᵥ* (W.J * H'.ι.map σ) = 0 := by
    intro v hv
    ext j
    have := hv (Pi.single j 1)
    simp only [form, Matrix.mulVec_single_one] at this
    rw [← Matrix.vecMul_vecMul]
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, Finset.mul_sum,
      Finset.sum_mul] at this ⊢
    rw [Finset.sum_comm]
    simpa [mul_assoc] using this
  have hιb : H'.ιᵀ *ᵥ b = 0 := hιv _ fun u => (hH.orth u).1
  have hιa : H'.ιᵀ *ᵥ a = 0 := hιv _ fun u => (hH.orth u).2
  have hxι : H'.x ᵥ* (W.J * H'.ι.map σ) = 0 := hvι _ fun u => by rw [hhe, (hH.orth u).1, map_zero]
  have hyι : H'.y ᵥ* (W.J * H'.ι.map σ) = 0 := hvι _ fun u => by rw [hhe, (hH.orth u).2, map_zero]
  refine ⟨π, hπι, hπx, hπy, ?_, ?_⟩
  · let σR : E →+* E := σ.toRingHom
    have hFσ : Matrix.vecMulVec (fun i => σ (H'.x i)) (fun i => σ (a i)) + H'.ι.map σR * π.map σR +
        Matrix.vecMulVec (fun i => σ (H'.y i)) (fun i => σ (b i)) = 1 := by
      have := congrArg (RingHom.mapMatrix σR) hF
      rw [map_add, map_add, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
        Matrix.map_mul] at this
      rw [← this]
      congr 1 <;> [congr 1; skip] <;> ext i j <;> simp [Matrix.vecMulVec, σR]
    calc H'.ιᵀ * W.J = H'.ιᵀ * W.J * 1 := (Matrix.mul_one _).symm
      _ = W₁.J * π.map σ := by
        rw [← hFσ, Matrix.mul_add, Matrix.mul_add, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        rw [show (W.J *ᵥ fun i => σ (H'.x i)) = b from rfl, show (W.J *ᵥ fun i => σ (H'.y i)) = a from rfl, hιb, hιa]
        rw [← Matrix.mul_assoc, show H'.ι.map σR = H'.ι.map σ from rfl, hH.gram]
        simp [Matrix.vecMulVec, σR]
        ext i j; simp
  · have hFt : Matrix.vecMulVec a H'.x + πᵀ * H'.ιᵀ + Matrix.vecMulVec b H'.y = 1 := by
      have := congrArg Matrix.transpose hF
      rwa [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_vecMulVec, Matrix.transpose_vecMulVec,
        Matrix.transpose_mul, Matrix.transpose_one] at this
    calc W.J * H'.ι.map σ = 1 * (W.J * H'.ι.map σ) := (Matrix.one_mul _).symm
      _ = πᵀ * W₁.J := by
        rw [← hFt, Matrix.add_mul, Matrix.add_mul, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, hxι, hyι,
          Matrix.mul_assoc, ← Matrix.mul_assoc H'.ιᵀ, hH.gram]
        simp [Matrix.vecMulVec]
        ext i j; simp

end GlobalTheory.LeviFrameH

namespace GlobalTheory.LeviFrameH

theorem isLevi_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} (H : Plane E n n₁) (l : (AE F E)ˣ) (g₀ : UA σ X₁.J)
    (m₀ m₁ : UA σ X.J) (h₀ : IsLevi (W₁ := X₁) H l 1 m₀) (h₁ : IsLevi (W₁ := X₁) H 1 g₀ m₁) :
    IsLevi (W₁ := X₁) H l g₀ (m₀ * m₁) := by
  obtain ⟨a0, b0, c0⟩ := h₀
  obtain ⟨a1, b1, c1⟩ := h₁
  have hm : mat (m₀ * m₁) = mat m₀ * mat m₁ := rfl
  have h1 : mat (1 : UA σ X₁.J) = 1 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, ← Matrix.mulVec_mulVec, a1, Units.val_one, one_smul, a0]
  · rw [hm, ← Matrix.mulVec_mulVec, b1, inv_one, Units.val_one, map_one, one_smul, b0]
  · rw [hm, Matrix.mul_assoc, c1, ← Matrix.mul_assoc, c0, h1, Matrix.mul_one]

theorem exists_levi_herm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ → ∀ (l : (AE F E)ˣ) (g₀ : UA σ X₁.J), ∃ m : UA σ X.J, IsLevi (W₁ := X₁) H l g₀ m := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ H r s i₀ i₁ hB hX hA t g₀

  have hm₀ : ∃ m₀ : UA σ X.J, IsLevi (W₁ := X₁) H t 1 m₀ := by
    have hσ := GlobalTheory.LeviTorusH.sigma_invol hB.cm
    have hc : ∀ a : AE F E, (cA σ).toRingHom ((cA σ).toRingHom a) = a := GlobalTheory.LeviTorusH.cA_invol hσ
    have hJ : ∀ i j, (cA σ).toRingHom (incM F X.J j i) = incM F X.J i j := by
      intro i j
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, incM, Matrix.map_apply, GlobalTheory.LeviTorusH.cA_incl]
      exact congrArg _ (hX.herm i j)
    have hXX : incV F H.x ⬝ᵥ incM F X.J *ᵥ (fun i => (cA σ).toRingHom (incV F H.x i)) = 0 := by
      rw [show (fun i => (cA σ).toRingHom (incV F H.x i)) = fun i => cA σ (incV F H.x i) from rfl,
        GlobalTheory.LeviTorusH.form_incl]
      exact (congrArg _ hA.xx).trans (map_zero _)
    have hYY : incV F H.y ⬝ᵥ incM F X.J *ᵥ (fun i => (cA σ).toRingHom (incV F H.y i)) = 0 := by
      rw [show (fun i => (cA σ).toRingHom (incV F H.y i)) = fun i => cA σ (incV F H.y i) from rfl,
        GlobalTheory.LeviTorusH.form_incl]
      exact (congrArg _ hA.yy).trans (map_zero _)
    have hXY : incV F H.x ⬝ᵥ incM F X.J *ᵥ (fun i => (cA σ).toRingHom (incV F H.y i)) = 1 := by
      rw [show (fun i => (cA σ).toRingHom (incV F H.y i)) = fun i => cA σ (incV F H.y i) from rfl,
        GlobalTheory.LeviTorusH.form_incl]
      exact (congrArg _ hA.xy).trans (map_one _)
    have h01 := GlobalTheory.LeviTorusH.torus_mul_inv hc hJ hXY t hXX hYY
    have h10 : GlobalTheory.LeviTorusH.torusMat (cA σ).toRingHom (incM F X.J) (incV F H.x) (incV F H.y) t⁻¹ *
        GlobalTheory.LeviTorusH.torusMat (cA σ).toRingHom (incM F X.J) (incV F H.x) (incV F H.y) t = 1 :=
      by simpa only [inv_inv] using GlobalTheory.LeviTorusH.torus_mul_inv hc hJ hXY t⁻¹ hXX hYY
    refine ⟨⟨⟨GlobalTheory.LeviTorusH.torusMat (cA σ).toRingHom (incM F X.J) (incV F H.x) (incV F H.y) t, _, h01, h10⟩, ?_⟩, ?_, ?_, ?_⟩
    · exact GlobalTheory.LeviTorusH.torus_unitary hc hJ hXY t hXX hYY
    · exact GlobalTheory.LeviTorusH.torus_mulVec_x hXY t hXX
    · exact GlobalTheory.LeviTorusH.torus_mulVec_y hc hJ hXY t hYY
    · have hu : (incM F X.J *ᵥ fun i => (cA σ).toRingHom (incV F H.y i)) ᵥ* incM F H.ι = 0 := by
        rw [show (fun i => (cA σ).toRingHom (incV F H.y i)) = fun i => cA σ (incV F H.y i) from rfl,
          GlobalTheory.LeviTorusH.vecMul_incM]
        funext j
        exact (congrArg _ (hA.orth (Pi.single j 1)).2).trans (map_zero _)
      have hw : (incM F X.J *ᵥ fun i => (cA σ).toRingHom (incV F H.x i)) ᵥ* incM F H.ι = 0 := by
        rw [show (fun i => (cA σ).toRingHom (incV F H.x i)) = fun i => cA σ (incV F H.x i) from rfl,
          GlobalTheory.LeviTorusH.vecMul_incM]
        funext j
        exact (congrArg _ (hA.orth (Pi.single j 1)).1).trans (map_zero _)
      show GlobalTheory.LeviTorusH.torusMat (cA σ).toRingHom (incM F X.J) (incV F H.x) (incV F H.y) t * incM F H.ι =
        incM F H.ι * 1
      rw [Matrix.mul_one]
      exact GlobalTheory.LeviTorusH.torus_mul_of t _ hu hw

  have hm₁ : ∃ m₁ : UA σ X.J, IsLevi (W₁ := X₁) H 1 g₀ m₁ := by
    obtain ⟨π, hπι, hπx, hπy, hc, hd⟩ := frame_facts σ B X X₁ H hB.cm hX hA
    let c : AE F E →+* AE F E := (cA σ).toRingHom
    have hPI : incM F π * incM F H.ι = 1 := by
      simp only [incM]; rw [← Matrix.map_mul, hπι, Matrix.map_one _ (map_zero _) (map_one _)]
    have hcM : (incM F H.ι)ᵀ * incM F X.J = incM F X₁.J * (incM F π).map c := by
      rw [show (incM F π).map c = (incM F π).map (cA σ) from rfl, GlobalTheory.LeviFrame.incM_map_cA]
      simp only [incM]; rw [← Matrix.transpose_map, ← Matrix.map_mul, hc, Matrix.map_mul]
    have hdM : incM F X.J * (incM F H.ι).map c = (incM F π)ᵀ * incM F X₁.J := by
      rw [show (incM F H.ι).map c = (incM F H.ι).map (cA σ) from rfl, GlobalTheory.LeviFrame.incM_map_cA]
      simp only [incM]; rw [← Matrix.transpose_map, ← Matrix.map_mul, hd, Matrix.map_mul]
    have hU : (mat g₀)ᵀ * incM F X₁.J * (mat g₀).map c = incM F X₁.J := g₀.2
    have hHK : mat g₀ * mat g₀⁻¹ = 1 := by
      show ((g₀ : GL (Fin n₁) (AE F E)) : Matrix (Fin n₁) (Fin n₁) (AE F E)) *
        (((g₀⁻¹ : UA σ X₁.J) : GL (Fin n₁) (AE F E)) : Matrix (Fin n₁) (Fin n₁) (AE F E)) = 1
      rw [Subgroup.coe_inv, Units.mul_inv]
    have hKH : mat g₀⁻¹ * mat g₀ = 1 := by
      show (((g₀⁻¹ : UA σ X₁.J) : GL (Fin n₁) (AE F E)) : Matrix (Fin n₁) (Fin n₁) (AE F E)) *
        ((g₀ : GL (Fin n₁) (AE F E)) : Matrix (Fin n₁) (Fin n₁) (AE F E)) = 1
      rw [Subgroup.coe_inv, Units.inv_mul]
    let g : GL (Fin n) (AE F E) :=
      ⟨1 + incM F H.ι * ((mat g₀ - 1) * incM F π), 1 + incM F H.ι * ((mat g₀⁻¹ - 1) * incM F π),
        GlobalTheory.LeviFrame.levi_inv_alg _ _ _ _ hPI hHK, GlobalTheory.LeviFrame.levi_inv_alg _ _ _ _ hPI hKH⟩
    have hg : g ∈ UG (cA σ) (incM F X.J) :=
      GlobalTheory.LeviFrame.levi_unit_alg c (incM F X.J) (incM F X₁.J) (incM F H.ι) (incM F π) (mat g₀) hPI hcM hdM hU
    refine ⟨⟨g, hg⟩, ?_, ?_, ?_⟩
    · show (1 + incM F H.ι * ((mat g₀ - 1) * incM F π)) *ᵥ incV F H.x = ((1 : (AE F E)ˣ) : AE F E) • incV F H.x
      rw [Units.val_one, one_smul, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, GlobalTheory.LeviFrame.incM_mulVec_incV, hπx,
        show incV F (0 : Fin n₁ → E) = 0 from funext fun _ => map_zero _,
        Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
    · show (1 + incM F H.ι * ((mat g₀ - 1) * incM F π)) *ᵥ incV F H.y =
        cA σ (((1 : (AE F E)ˣ)⁻¹ : (AE F E)ˣ) : AE F E) • incV F H.y
      rw [inv_one, Units.val_one, map_one, one_smul, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, GlobalTheory.LeviFrame.incM_mulVec_incV, hπy,
        show incV F (0 : Fin n₁ → E) = 0 from funext fun _ => map_zero _,
        Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
    · show (1 + incM F H.ι * ((mat g₀ - 1) * incM F π)) * incM F H.ι = incM F H.ι * mat g₀
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hPI, Matrix.mul_one, Matrix.mul_sub,
        Matrix.mul_one, add_sub_cancel]
  obtain ⟨m₀, h₀⟩ := hm₀
  obtain ⟨m₁, h₁⟩ := hm₁
  exact ⟨m₀ * m₁, isLevi_mul H t g₀ m₀ m₁ h₀ h₁⟩

end GlobalTheory.LeviFrameH

end

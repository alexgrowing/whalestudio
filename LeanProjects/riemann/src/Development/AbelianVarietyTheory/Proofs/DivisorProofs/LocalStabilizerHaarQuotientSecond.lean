import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerLocallyCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingLocalMeasurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerFixesIsotropicVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv

noncomputable section

namespace GlobalTheory.ThK.LemF.LeviInv

open Matrix GlobalTheory.LeviElem

section Abstract

variable {R : Type} [CommRing R]

theorem exists_conj {b n : ℕ} (s : R →+* R) (hs : ∀ z, s (s z) = z) (ι : Matrix (Fin n) (Fin b) R) (x y : Fin n → R)
    (J : Matrix (Fin n) (Fin n) R) (J₁ : Matrix (Fin b) (Fin b) R) (Q : Matrix (Fin b ⊕ Fin 2) (Fin n) R)
    (hQP : Q * fromCols ι (cols2 x y) = 1) (hPQ : fromCols ι (cols2 x y) * Q = 1)
    (hK : (fromCols ι (cols2 x y))ᵀ * J * (fromCols ι (cols2 x y)).map s = fromBlocks J₁ 0 0 swap2)
    (M : Matrix (Fin b) (Fin b) R) (hM : Mᵀ * J₁ * M.map s = J₁.map s) (hM' : M * M.map s = 1) :
    ∃ N : Matrix (Fin n) (Fin n) R, N * N.map s = 1 ∧ Nᵀ * J * N.map s = J.map s ∧ N *ᵥ (s ∘ x) = x ∧
      N *ᵥ (s ∘ y) = y ∧ N * ι.map s = ι * M := by
  set P := fromCols ι (cols2 x y) with hP
  set D : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) R := fromBlocks M 0 0 1 with hD
  have hss : ∀ {p q : Type} (X : Matrix p q R), (X.map s).map s = X := fun X => by ext i j; simp [hs]
  have hQP' : Q.map s * P.map s = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero s) (map_one s)]
  have hDs : D.map s = fromBlocks (M.map s) 0 0 1 := by
    rw [hD, fromBlocks_map, Matrix.map_zero _ (map_zero s), Matrix.map_zero _ (map_zero s),
      Matrix.map_one _ (map_zero s) (map_one s)]
  have hDD : D * D.map s = 1 := by
    rw [hDs, hD, fromBlocks_multiply]
    simp [hM']
  have hNP : P * D * Q.map s * P.map s = fromCols (ι * M) (cols2 x y) := by
    rw [Matrix.mul_assoc, hQP', Matrix.mul_one, hP, hD, fromCols_mul_fromBlocks]
    simp
  have hPs : P.map s = fromCols (ι.map s) (cols2 (s ∘ x) (s ∘ y)) := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  rw [hPs, mul_fromCols] at hNP
  obtain ⟨h1, h2⟩ := fromCols_inj hNP
  refine ⟨P * D * Q.map s, ?_, ?_, ?_, ?_, h1⟩
  · rw [Matrix.map_mul, Matrix.map_mul, hss]
    calc P * D * Q.map s * (P.map s * D.map s * Q) = P * (D * (Q.map s * P.map s) * D.map s) * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP', Matrix.mul_one, hDD, Matrix.mul_one, hPQ]
  · have e1 : Dᵀ * (Pᵀ * J * P.map s) * D.map s = (Pᵀ * J * P.map s).map s := by
      rw [hK, hDs, hD, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_map]
      have : (swap2 : Matrix (Fin 2) (Fin 2) R).map s = swap2 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [swap2]
      simp [hM, this]
    have e2 : Qᵀ * (Pᵀ * J * P.map s) * Q.map s = J := by
      have : Qᵀ * (Pᵀ * J * P.map s) * Q.map s = (P * Q)ᵀ * J * (P * Q).map s := by
        simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      rw [this, hPQ]
      simp
    calc (P * D * Q.map s)ᵀ * J * (P * D * Q.map s).map s
        = (Q.map s)ᵀ * (Dᵀ * (Pᵀ * J * P.map s) * D.map s) * (Q.map s).map s := by
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = J.map s := by rw [e1, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, e2]
  · funext i
    have := congrFun (congrFun h2 i) 0
    simpa [Matrix.mul_apply, cols2, mulVec, dotProduct] using this
  · funext i
    have := congrFun (congrFun h2 i) 1
    simpa [Matrix.mul_apply, cols2, mulVec, dotProduct] using this

theorem ext_cols {b n : ℕ} (ι : Matrix (Fin n) (Fin b) R) (x y : Fin n → R) (Q : Matrix (Fin b ⊕ Fin 2) (Fin n) R)
    (hPQ : fromCols ι (cols2 x y) * Q = 1) {A A' : Matrix (Fin n) (Fin n) R} (hx : A *ᵥ x = A' *ᵥ x)
    (hy : A *ᵥ y = A' *ᵥ y) (hι : A * ι = A' * ι) : A = A' := by
  have h2 : A * cols2 x y = A' * cols2 x y := by
    ext i k
    fin_cases k
    · simpa [Matrix.mul_apply, cols2, mulVec, dotProduct] using congrFun hx i
    · simpa [Matrix.mul_apply, cols2, mulVec, dotProduct] using congrFun hy i
  rw [← Matrix.mul_one A, ← Matrix.mul_one A', ← hPQ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_fromCols,
    mul_fromCols, hι, h2]

theorem conj_fix {n : ℕ} (s : R →+* R) (hs : ∀ z, s (s z) = z) {N g : Matrix (Fin n) (Fin n) R} {x : Fin n → R}
    (hN : N *ᵥ (s ∘ x) = x) (hg : g *ᵥ x = x) : (N * g.map s * N.map s) *ᵥ x = x := by
  have h1 : N.map s *ᵥ x = s ∘ x := by
    have := GlobalTheory.AdelicUnimod.comp_mulVec (σ := s) N (s ∘ x)
    rw [hN, show s ∘ s ∘ x = x from funext fun i => hs _] at this
    exact this.symm
  rw [← mulVec_mulVec, ← mulVec_mulVec, h1, ← GlobalTheory.AdelicUnimod.comp_mulVec, hg, hN]

theorem conj_block {n b : ℕ} (s : R →+* R) (hs : ∀ z, s (s z) = z) {N g : Matrix (Fin n) (Fin n) R}
    {ι : Matrix (Fin n) (Fin b) R} {M h h' : Matrix (Fin b) (Fin b) R} (hN : N * ι.map s = ι * M)
    (hM : M * M.map s = 1) (hg : g * ι = ι * h) (hh : h' * M = M * h.map s) :
    N * g.map s * N.map s * ι = ι * h' := by
  have hss : (ι.map s).map s = ι := by ext i j; simp [hs]
  have h1 : N.map s * ι = ι.map s * M.map s := by
    conv_lhs => rw [← hss]
    rw [← Matrix.map_mul, hN, Matrix.map_mul]
  rw [Matrix.mul_assoc, h1, Matrix.mul_assoc, ← Matrix.mul_assoc (g.map s), ← Matrix.map_mul, hg, Matrix.map_mul,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hN, Matrix.mul_assoc ι, ← hh, Matrix.mul_assoc, Matrix.mul_assoc, hM,
    Matrix.mul_one]

theorem exists_aut {R₀ : Type} [CommRing R₀] [Algebra R₀ R] [TopologicalSpace R] [IsTopologicalRing R] {n : ℕ}
    (c : R →ₐ[R₀] R) (hc : Continuous c) (hs : ∀ z, c (c z) = z) {J N : Matrix (Fin n) (Fin n) R}
    (hN : N * N.map c = 1) (hJ : Nᵀ * J * N.map c = J.map c) :
    ∃ T : UG c J →* UG c J, Continuous T ∧
      ∀ g, ((T g).1 : Matrix (Fin n) (Fin n) R) = N * (g.1 : Matrix (Fin n) (Fin n) R).map c * N.map c := by
  have hss : ∀ X : Matrix (Fin n) (Fin n) R, (X.map c).map c = X := fun X => by ext i j; simp [hs]
  let m : GL (Fin n) R := ⟨N, N.map c, hN, mul_eq_one_comm.1 hN⟩
  let T₀ : GL (Fin n) R →* GL (Fin n) R :=
    (MulAut.conj m).toMonoidHom.comp (Units.map (c.toRingHom.mapMatrix (m := Fin n)).toMonoidHom)
  have hT₀ : ∀ g : GL (Fin n) R, (T₀ g : Matrix (Fin n) (Fin n) R) = N * (g : Matrix (Fin n) (Fin n) R).map c * N.map c :=
    fun g => rfl
  have hmem : ∀ g : UG c J, T₀ g ∈ UG c J := fun g => by
    show (T₀ g : Matrix (Fin n) (Fin n) R)ᵀ * J * (T₀ g : Matrix (Fin n) (Fin n) R).map c = J
    set a : Matrix (Fin n) (Fin n) R := g.1.1 with ha
    have hg : aᵀ * J * a.map c = J := g.2
    have h1 : (a.map c)ᵀ * J.map c * (a.map c).map c = J.map c := by
      rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hg]
    have h2 : (N.map c)ᵀ * J.map c * (N.map c).map c = J := by
      rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hJ, hss]
    calc _ = (N.map c)ᵀ * ((a.map c)ᵀ * (Nᵀ * J * N.map c) * (a.map c).map c) * (N.map c).map c := by
          rw [hT₀]; simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc, ha]
      _ = J := by rw [hJ, h1, h2]
  have hcv : Continuous fun g : GL (Fin n) R => (T₀ g : Matrix (Fin n) (Fin n) R) :=
    (continuous_const.matrix_mul (Units.continuous_val.matrix_map hc)).matrix_mul continuous_const
  have hc₀ : Continuous T₀ := Units.continuous_iff.2 ⟨hcv, by
    simp only [← map_inv]
    exact hcv.comp continuous_inv⟩
  exact ⟨(T₀.comp (UG c J).subtype).codRestrict _ hmem, (hc₀.comp continuous_subtype_val).subtype_mk _, fun g => rfl⟩

end Abstract

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem eq_zero_of_at {v : Pl F} {z : AE F E} (hz : At (evFin F v) z) (h : compFin F E v z = 0) : z = 0 := by
  obtain ⟨h1, h2⟩ := at_evFin_iff.1 hz
  refine GlobalTheory.Doubling.adele_ext (fun w => ?_) fun w => ?_
  · rw [h1, map_zero]
  · rw [map_zero]
    by_cases hw : w = v
    · rw [hw, h]
    · exact h2 w hw

omit [NumberField E] in
theorem smul_map_cA {p q : Type} (u : AF F) (X : Matrix p q (AE F E)) : u • X.map (cA σ) = (u • X).map (cA σ) := by
  ext i j
  simp

omit [NumberField E] in
theorem compFin_cA (v : Pl F) (z : AE F E) : compFin F E v (cA σ z) = sigR (Fv F v) σ (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem char_trivial (hcm : IsCMExt F E σ) {n : ℕ} (X : Spc F E n) {M : Matrix (Fin n) (Fin n) E}
    (hM : GlobalTheory.AdelicUnimod.Framed (σ : E →+* E) X.Jᵀ M) (v : Pl F) (χ : UAtSub σ X (evFin F v) →* ℝ≥0)
    (hχ : ∀ g g' : UAtSub σ X (evFin F v), mat g'.1 * incM F M = incM F M * (mat g.1).map (cA σ) → χ g' = χ g)
    (g : UAtSub σ X (evFin F v)) : χ g = 1 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hss := GlobalTheory.HermLineZeros.conj_invol hcm
  obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hcm
  have hF : GlobalTheory.AdelicUnimod.Framed (sigR (Fv F v) σ) (JR (Fv F v) X.Jᵀ) (M.map (inclR (Fv F v))) :=
    hM.map fun _ => rfl
  haveI : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) _
  letI : Algebra ℚ (Fv F v ⊗[F] E) := ((inclR (F := F) (Fv F v)).comp (algebraMap ℚ E)).toAlgebra
  have hgen : GlobalTheory.AdelicUnimod.Generic (sigR (Fv F v) σ) :=
    GlobalTheory.AdelicUnimod.generic_of_semilocal (δ := inclR (Fv F v) (σ d - d)) ((sub_ne_zero.2 hd).isUnit.map _)
      (by
        have : σ (σ d - d) = -(σ d - d) := by rw [map_sub, hss, neg_sub]
        rw [← map_neg, ← this]
        rfl)
  let e := GlobalTheory.LocUnitaryUnimod.locEquiv σ v X
  let χ' : HA (Fv F v) σ X.Jᵀ →* ℝ≥0 := χ.comp e.symm.toMulEquiv.toMonoidHom
  have hmat : ∀ k : UAtSub σ X (evFin F v),
      (HA.mat (Fv F v) σ X.Jᵀ (e k) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = (mat k.1).map (compFin F E v) :=
    fun k => Matrix.ext fun r s => GlobalTheory.AutFunCompare.mat_mapH σ X.Jᵀ (evFin F v) _ r s
  have h1 := GlobalTheory.AdelicUnimod.char_eq_one (GlobalTheory.AdelicPointsUnimod.sigR_sigR hss) hF hgen χ' (fun x x' h => by
    obtain ⟨k, rfl⟩ := e.surjective x
    obtain ⟨k', rfl⟩ := e.surjective x'
    show χ (e.symm (e k')) = χ (e.symm (e k))
    rw [e.symm_apply_apply, e.symm_apply_apply]
    refine hχ k k' ?_
    have h' : (mat k'.1).map (compFin F E v) * M.map (inclR (Fv F v)) =
        M.map (inclR (Fv F v)) * ((mat k.1).map (compFin F E v)).map (sigR (Fv F v) σ) := by
      rw [← hmat, ← hmat]
      exact h
    have hMv : (incM F M).map (compFin F E v) = M.map (inclR (Fv F v)) := by
      ext i j
      show (evFin F v 1) ⊗ₜ[F] M i j = 1 ⊗ₜ[F] M i j
      rw [map_one]
    have hz : (mat k'.1 * incM F M - incM F M * (mat k.1).map (cA σ)).map (compFin F E v) = 0 := by
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, hMv, h', sub_eq_zero]
      congr 1
      ext i j
      exact (compFin_cA v _).symm
    have hat : At (evFin F v) (mat k'.1 * incM F M - incM F M * (mat k.1).map (cA σ)) := fun u hu => by
      have : mat k'.1 * incM F M - incM F M * (mat k.1).map (cA σ) =
          (mat k'.1 - 1) * incM F M - incM F M * (mat k.1 - 1).map (cA σ) := by
        rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.sub_mul, Matrix.mul_sub,
          Matrix.one_mul, Matrix.mul_one]
        abel
      rw [this, smul_sub, ← Matrix.smul_mul, ← Matrix.mul_smul, smul_map_cA, k'.2 u hu, k.2 u hu,
        Matrix.map_zero _ (map_zero _), Matrix.zero_mul, Matrix.mul_zero, sub_zero]
    rw [← sub_eq_zero]
    ext i j
    exact eq_zero_of_at (fun u hu => congrFun (congrFun (hat u hu) i) j) (congrFun (congrFun hz i) j)) (e g)
  have h2 : χ' (e g) = χ g := congrArg χ (e.symm_apply_apply g)
  exact h2.symm.trans h1

end Local

theorem levi_map_mul_right : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F),
    ∀ μ : Measure (stabAt σ G.V (evFin F v) H.x), μ.IsHaarMeasure →
    ∀ q : stabAt σ G.V (evFin F v) H.x, (∃ g₀ : UA σ G₁.V.J, IsLevi H 1 g₀ q.1.1 ∧ g₀ ∈ UAt σ G₁.V (evFin F v)) →
      Measure.map (· * q) μ = μ := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v μ hμ q ⟨g₀, hq, hg₀⟩
  have hB := hT.base
  have hG := hT.geo
  have hG₁ := hT₁.geo
  have hσ : ∀ z, σ (σ z) = z := GlobalTheory.HermLineZeros.conj_invol hB.cm
  have hdet : G₁.V.J.det ≠ 0 := GlobalTheory.ThetaKInv.det_ne_zero_of_isHerm hG₁.hV
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * G.V.J * P.map σ = fromBlocks G₁.V.J 0 0 swap2 := gram_block σ hσ B hG.hV.herm hC.hH
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks G₁.V.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [swap2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  have hPQ : P * Q = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP
  obtain ⟨M, hM⟩ := GlobalTheory.AdelicUnimod.exists_framed (σ := (σ : E →+* E)) hσ (J := G₁.V.Jᵀ)
    (by ext i j; exact hG₁.hV.herm j i) (by rwa [Matrix.det_transpose])
  have hM1 : Mᵀ * G₁.V.J * M.map (σ : E →+* E) = G₁.V.J.map (σ : E →+* E) := by
    have := congrArg Matrix.transpose hM.2.2.1
    rw [Formalism.UG.cT, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
      ← Matrix.transpose_map, Matrix.transpose_transpose, ← Matrix.mul_assoc] at this
    exact this
  obtain ⟨N, hN1, hN2, hNx, hNy, hNι⟩ :=
    exists_conj (σ : E →+* E) hσ H.ι H.x H.y G.V.J G₁.V.J Q hQP hPQ hK M hM1 hM.2.2.2
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  set c : AE F E →+* AE F E := (cA σ : AE F E →+* AE F E) with hc
  have hcc : ∀ z, c (c z) = z := cA_invol hσ
  have hcf : ∀ {p r : Type} (Z : Matrix p r E), (incM F Z).map c = (Z.map (σ : E →+* E)).map f := fun Z => rfl
  have hcv : ∀ {k : ℕ} (z : Fin k → E), c ∘ incV F z = f ∘ (σ : E →+* E) ∘ z := fun z => rfl
  have hPf : P.map f = fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hPQ' : fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) * Q.map f = 1 := by
    rw [← hPf, ← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero f) (map_one f)]
  have hA1 : incM F N * (incM F N).map c = 1 := by
    rw [hcf, show incM F N = N.map f from rfl, ← Matrix.map_mul, hN1, Matrix.map_one _ (map_zero f) (map_one f)]
  have hA2 : (incM F N)ᵀ * incM F G.V.J * (incM F N).map c = (incM F G.V.J).map c := by
    rw [hcf, hcf, show incM F N = N.map f from rfl, show incM F G.V.J = G.V.J.map f from rfl,
      ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hN2]
  have hAv : ∀ z : Fin (b + 2) → E, N *ᵥ ((σ : E →+* E) ∘ z) = z → incM F N *ᵥ (c ∘ incV F z) = incV F z :=
    fun z hz => by
      rw [hcv, show incM F N = N.map f from rfl]
      funext i
      rw [← RingHom.map_mulVec, hz]
      rfl
  have hAι : incM F N * (incM F H.ι).map c = incM F H.ι * incM F M := by
    rw [hcf, show incM F N = N.map f from rfl, ← Matrix.map_mul, hNι, Matrix.map_mul]
    rfl
  have hAM : incM F M * (incM F M).map c = 1 := by
    rw [hcf, show incM F M = M.map f from rfl, ← Matrix.map_mul, hM.2.2.2, Matrix.map_one _ (map_zero f) (map_one f)]

  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (UA σ G.V.J) := inferInstanceAs (IsTopologicalGroup (UG (cA σ) (incM F G.V.J)))
  obtain ⟨_, _, _, -⟩ := GlobalTheory.LocUnitaryUnimod.lcsc_unimodular_UAtSub F E σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v
  haveI : LocallyCompactSpace (stabAt σ G.V (evFin F v) H.x) :=
    (isClosed_stabAt_vec G.V (evFin F v) H.x).locallyCompactSpace

  obtain ⟨T₀, hT₀c, hT₀⟩ := exists_aut (cA σ) (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ) hcc hA1 hA2
  have hT₀' : ∀ g : UA σ G.V.J, mat (T₀ g) = incM F N * (mat g).map c * (incM F N).map c := hT₀
  have hs1 : ∀ g : UAtSub σ G.V (evFin F v), T₀ g.1 ∈ UAtSub σ G.V (evFin F v) := fun g u hu => by
    have : mat (T₀ g.1) - 1 = incM F N * (mat g.1 - 1).map (cA σ) * (incM F N).map c := by
      rw [hT₀', Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_one, hA1]
      rfl
    rw [this, ← Matrix.smul_mul, ← Matrix.mul_smul, smul_map_cA, g.2 u hu, Matrix.map_zero _ (map_zero _),
      Matrix.mul_zero, Matrix.zero_mul]
  let T₁ : UAtSub σ G.V (evFin F v) →* UAtSub σ G.V (evFin F v) :=
    (T₀.comp (UAtSub σ G.V (evFin F v)).subtype).codRestrict _ hs1
  have hs2 : ∀ g : stabAt σ G.V (evFin F v) H.x, T₁ g.1 ∈ stabAt σ G.V (evFin F v) H.x := fun g => by
    show mat (T₀ g.1.1) *ᵥ incV F H.x = incV F H.x
    rw [hT₀']
    exact conj_fix c hcc (hAv _ hNx) g.2
  let T : stabAt σ G.V (evFin F v) H.x →* stabAt σ G.V (evFin F v) H.x :=
    (T₁.comp (stabAt σ G.V (evFin F v) H.x).subtype).codRestrict _ hs2
  have hTm : ∀ g, mat (T g).1.1 = incM F N * (mat g.1.1).map c * (incM F N).map c := fun g => hT₀' _
  have hTc : Continuous T :=
    ((hT₀c.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk _
  have hext : ∀ g g' : stabAt σ G.V (evFin F v) H.x, mat g.1.1 = mat g'.1.1 → g = g' := fun g g' h =>
    Subtype.ext (Subtype.ext (Subtype.ext (Units.ext h)))
  have hTT : ∀ g, T (T g) = g := fun g => hext _ _ (by
    have hss : ∀ Z : Matrix (Fin (b + 2)) (Fin (b + 2)) (AE F E), (Z.map c).map c = Z := fun Z => by
      ext i j; exact hcc _
    rw [hTm, hTm, Matrix.map_mul, Matrix.map_mul, hss, hss, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hA1,
      Matrix.one_mul, Matrix.mul_assoc, hA1, Matrix.mul_one])

  have hlev : ∀ {h : UA σ G₁.V.J} {g : UA σ G.V.J}, IsLevi H 1 h g ↔ mat g *ᵥ incV F H.x = incV F H.x ∧
      mat g *ᵥ incV F H.y = incV F H.y ∧ mat g * incM F H.ι = incM F H.ι * mat h := by
    intro h g
    simp only [IsLevi, inv_one, Units.val_one, map_one, one_smul]
  have huniq : ∀ {h : UA σ G₁.V.J} {g g' : stabAt σ G.V (evFin F v) H.x}, IsLevi H 1 h g.1.1 → IsLevi H 1 h g'.1.1 →
      g = g' := fun h1 h2 => by
    obtain ⟨a1, a2, a3⟩ := hlev.1 h1
    obtain ⟨b1, b2, b3⟩ := hlev.1 h2
    exact hext _ _ (ext_cols _ _ _ _ hPQ' (a1.trans b1.symm) (a2.trans b2.symm) (a3.trans b3.symm))
  have hex : ∀ h : UAtSub σ G₁.V (evFin F v), ∃ g : stabAt σ G.V (evFin F v) H.x, IsLevi H 1 h.1 g.1.1 := fun h => by
    obtain ⟨m, hm⟩ := levi_exists F E σ B b a' G G₁ H H' hC hB hG hG₁
    obtain ⟨a1, a2, a3⟩ := hlev.1 (hm 1 h.1)
    have hsm : ∀ {k : ℕ} (a : AF F) (Z : Matrix (Fin k) (Fin k) (AE F E)), a • Z = (algebraMap (AF F) (AE F E) a) • Z :=
      fun a Z => (algebraMap_smul (AE F E) a Z).symm
    have hgs : m 1 h.1 ∈ UAtSub σ G.V (evFin F v) := fun a ha => by
      rw [hsm]
      exact StabDec.levi_supp _ _ _ _ hPQ' (mat (m 1 h.1)) (mat h.1) a1 a2 a3 _ (by rw [← hsm]; exact h.2 a ha)
    exact ⟨⟨⟨m 1 h.1, hgs⟩, a1⟩, hm 1 h.1⟩
  choose l hl using hex
  let L : UAtSub σ G₁.V (evFin F v) →* stabAt σ G.V (evFin F v) H.x := MonoidHom.mk' l fun h h' => huniq (hl _) (by
    obtain ⟨a1, a2, a3⟩ := hlev.1 (hl h)
    obtain ⟨b1, b2, b3⟩ := hlev.1 (hl h')
    have e1 : mat (l h * l h').1.1 = mat (l h).1.1 * mat (l h').1.1 := rfl
    have e2 : mat (h * h').1 = mat h.1 * mat h'.1 := rfl
    refine hlev.2 ⟨?_, ?_, ?_⟩
    · rw [e1, ← mulVec_mulVec, b1, a1]
    · rw [e1, ← mulVec_mulVec, b2, a2]
    · rw [e1, e2, Matrix.mul_assoc, b3, ← Matrix.mul_assoc, a3, Matrix.mul_assoc])
  have h1 := char_trivial hB.cm G₁.V hM v
    ((Measure.modularCharacter (G := stabAt σ G.V (evFin F v) H.x)).comp L) (fun h h' hh => by
      have : l h' = T (l h) := huniq (hl h') (by
        obtain ⟨a1, a2, a3⟩ := hlev.1 (hl h)
        refine hlev.2 ⟨?_, ?_, ?_⟩ <;> rw [hTm]
        · exact conj_fix c hcc (hAv _ hNx) a1
        · exact conj_fix c hcc (hAv _ hNy) a2
        · exact conj_block c hcc hAι hAM a3 hh)
      show Measure.modularCharacter (l h') = Measure.modularCharacter (l h)
      rw [this]
      exact GlobalTheory.AdelicUnimod.modular_involution T hTc hTT _) ⟨g₀, hg₀⟩
  have h2 : Measure.modularCharacter q = 1 := by
    rw [huniq hq (hl ⟨g₀, hg₀⟩)]
    exact h1
  rw [GlobalTheory.AdelicUnimod.map_mul_right_eq, h2, one_smul]

end GlobalTheory.ThK.LemF.LeviInv

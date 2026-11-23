import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDualOfAnisotropicOrthogonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryOrthogonalEmbeddingStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentRadicalMemAdelic

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold.RatPts

open GlobalTheory.RatDiscrete

theorem eq_map_of_resolution {E R : Type} [CommRing E] [CommRing R] (ι : E →+* R) {n m : ℕ}
    {x u : Fin n → E} {A : Matrix (Fin n) (Fin m) E} {A' : Matrix (Fin m) (Fin n) E}
    (h : vecMulVec x u + A * A' = 1) (M : Matrix (Fin n) (Fin n) R) (g : Matrix (Fin m) (Fin m) E)
    (hx : M *ᵥ (fun i => ι (x i)) = fun i => ι (x i)) (hA : M * A.map ι = A.map ι * g.map ι) :
    M = (vecMulVec x u + A * g * A').map ι := by
  have h1 : (vecMulVec x u + A * A').map ι = 1 := by
    rw [h]; exact Matrix.map_one ι (map_zero ι) (map_one ι)
  have hvm : ∀ y w : Fin n → E, (vecMulVec y w).map ι = vecMulVec (fun i => ι (y i)) (fun i => ι (w i)) := by
    intro y w; ext i j; simp [vecMulVec_apply]
  have key : M * vecMulVec (fun i => ι (x i)) (fun i => ι (u i)) =
      vecMulVec (fun i => ι (x i)) (fun i => ι (u i)) := by
    ext i j
    have hi := congrFun hx i
    simp only [mulVec, dotProduct] at hi
    simp only [mul_apply, vecMulVec_apply]
    rw [← hi, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => (mul_assoc _ _ _).symm
  calc M = M * (vecMulVec x u + A * A').map ι := by rw [h1, Matrix.mul_one]
    _ = (vecMulVec x u + A * g * A').map ι := by
      rw [Matrix.map_add _ (map_add ι), Matrix.map_add _ (map_add ι), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hvm,
        Matrix.mul_add, key, ← Matrix.mul_assoc, hA]

theorem exists_isImage (I : AutInst) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) : ∃ a : I.GA, IsImage I γ a := by
  have hU : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J *
      (γ : Matrix (Fin I.n) (Fin I.n) I.E) = I.J := hγ
  have hG : ∀ v, ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = I.J.map (I.φ v) := by
    intro v
    have h2 := congrArg (fun M : Matrix (Fin I.n) (Fin I.n) I.E => M.map (I.φ v)) hU
    simp only [Matrix.map_mul] at h2
    convert h2 using 3
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
    exact (I.cm.cmUnram.2.1 (I.φ v) _).symm
  have hR : ∀ v, Formalism.REAL.inUJ (I.ε v)
      ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) := by
    intro v
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    have hdH : IsUnit (I.P v)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hd.star
    unfold Formalism.REAL.inUJ
    rw [← I.P_spec v]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((I.P v)ᴴ)⁻¹ (I.P v)ᴴ, Matrix.nonsing_inv_mul _ hdH, Matrix.one_mul,
      ← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hG v]
  have hC : ∀ v (X Y : Matrix (Fin I.n) (Fin I.n) ℂ),
      ((I.P v)⁻¹ * X * I.P v) * ((I.P v)⁻¹ * Y * I.P v) = (I.P v)⁻¹ * (X * Y) * I.P v := by
    intro v X Y
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  have hE : ∀ v (X : Matrix (Fin I.n) (Fin I.n) I.E) (Y : Matrix (Fin I.n) (Fin I.n) I.E), X * Y = 1 →
      ((I.P v)⁻¹ * X.map (I.φ v) * I.P v) * ((I.P v)⁻¹ * Y.map (I.φ v) * I.P v) = 1 := by
    intro v X Y hXY
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    rw [hC, ← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ hd]
  let ι := Formalism.UG.inclE (F := I.F) (E := I.E) (Af I.F)
  have hF : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map ι) *
      I.J.map ι * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map ι = I.J.map ι := by
    have h2 := congrArg (fun M : Matrix (Fin I.n) (Fin I.n) I.E => M.map ι) hU
    simp only [Matrix.map_mul] at h2
    convert h2 using 3
    ext i j
    simp [ι, Formalism.UG.cT, Formalism.UG.sigR, Formalism.UG.inclE]
    rfl
  let af : GL (Fin I.n) (I.E ⊗[I.F] Af I.F) := Units.map (RingHom.mapMatrix ι).toMonoidHom γ
  have haf : af ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) := by
    unfold Formalism.UG.UPts
    exact hF
  refine ⟨(fun v => ⟨⟨(I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
      (I.P v)⁻¹ * ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
      hE v _ _ (Units.mul_inv γ), hE v _ _ (Units.inv_mul γ)⟩, hR v⟩, ⟨af, haf⟩), fun v => rfl, rfl⟩

theorem isImage_embA {I : AutInst} (D : Sib I) {x u : Fin I.n → I.E} {A : Matrix (Fin I.n) (Fin D.n) I.E}
    {A' : Matrix (Fin D.n) (Fin I.n) I.E} (h : vecMulVec x u + A * A' = 1)
    {jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)} {jf : D.inst.Gf →* I.Gf}
    (hv : IsInfEmb D x A jv) (hf : IsFinEmb D x A jf) {γ : Matrix (Fin D.n) (Fin D.n) I.E} {g : D.inst.GA}
    (hg : IsImage D.inst γ g) : IsImage I (vecMulVec x u + A * γ * A') (embA D jv jf g) := by
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨fun v => ?_, ?_⟩
  · have hPu := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    have hDu := (Matrix.isUnit_iff_isUnit_det _).mp (D.P_unit v)
    obtain ⟨h1, h2⟩ := hv v (g.1 v)
    have hxv : (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) *ᵥ (fun i => I.φ v (x i)) =
        fun i => I.φ v (x i) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      change I.P v *ᵥ (uMat (jv v (g.1 v)) *ᵥ infVec I v x) = _
      rw [h1, infVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]
    have key : I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹ * A.map (I.φ v) * D.P v =
        A.map (I.φ v) * γ.map (I.φ v) * D.P v := by
      calc I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹ * A.map (I.φ v) * D.P v
          = I.P v * (uMat (jv v (g.1 v)) * ((I.P v)⁻¹ * A.map (I.φ v) * D.P v)) := by
            simp only [Matrix.mul_assoc]
        _ = I.P v * (((I.P v)⁻¹ * A.map (I.φ v) * D.P v) *
            ((D.P v)⁻¹ * γ.map (I.φ v) * D.P v)) :=
            congrArg (I.P v * ·) (h2.trans (congrArg (infMat D v A * ·) (hg1 v)))
        _ = A.map (I.φ v) * γ.map (I.φ v) * D.P v := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (D.P v) (D.P v)⁻¹, Matrix.mul_nonsing_inv _ hDu, Matrix.one_mul,
              ← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
    have hAv : (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) * A.map (I.φ v) =
        A.map (I.φ v) * γ.map (I.φ v) := by
      calc (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) * A.map (I.φ v)
          = (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) * A.map (I.φ v) * D.P v * (D.P v)⁻¹ := by
            rw [Matrix.mul_assoc _ (D.P v), Matrix.mul_nonsing_inv _ hDu, Matrix.mul_one]
        _ = A.map (I.φ v) * γ.map (I.φ v) * D.P v * (D.P v)⁻¹ := by rw [key]
        _ = A.map (I.φ v) * γ.map (I.φ v) := by
            rw [Matrix.mul_assoc _ (D.P v), Matrix.mul_nonsing_inv _ hDu, Matrix.mul_one]
    have hM := eq_map_of_resolution (I.φ v) h (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) γ hxv hAv
    change uMat (jv v (g.1 v)) = _
    rw [← hM]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hPu, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu,
      Matrix.one_mul]
  · change I.fmat (jf g.2) = _
    exact eq_map_of_resolution (Formalism.UG.inclE (F := I.F) (Af I.F)) h (I.fmat (jf g.2)) γ (hf g.2).1
      ((hf g.2).2.trans (congrArg (afMat I A * ·) hg2))

theorem inclE_injective (I : AutInst) :
    Function.Injective (Formalism.UG.inclE (F := I.F) (E := I.E) (Af I.F)) := by
  have hnf : ¬ IsField (𝓞 I.F) := by
    exact NumberField.RingOfIntegers.not_isField I.F
  obtain ⟨p, hp0, hpp⟩ := Ring.not_isField_iff_exists_prime.mp hnf
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F) := ⟨p, hpp, hp0⟩
  have : Nontrivial (Af I.F) :=
    ⟨⟨1, 0, fun h => one_ne_zero (congrArg (fun a : Af I.F => (a.1 v : v.adicCompletion I.F)) h)⟩⟩
  intro a b hab
  exact Algebra.TensorProduct.includeLeft_injective (R := I.F) (S := I.F) (A := I.E) (B := Af I.F)
    (RingHom.injective _) hab

end GlobalTheory.StabUnfold.RatPts

namespace GlobalTheory.StabUnfold

open GlobalTheory.RatDiscrete RatPts

theorem image_rational_eq_stab : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ (jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)) (jf : D.inst.Gf →* I.Gf), IsInfEmb D x A jv → IsFinEmb D x A jf → embA D jv jf '' D.inst.GFset = stabF I x := by
  intro I D s x A xf hP jv jf hv hf
  obtain ⟨hn, hβ, hxA, hAJ, -, -⟩ := hP
  have hJ : I.Jᴴ = I.J := by
    have hh := I.J_herm
    unfold Formalism.UG.IsHerm at hh
    ext i j
    have hij := congrFun (congrFun hh i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at hij
    rw [Matrix.conjTranspose_apply]
    exact hij
  have hβ0 : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    rw [hβ]; cases s <;> simp [GlobalTheory.GaussMean.sgn]
  obtain ⟨u, A', hA'A, hA'x, huA, hux, hres, hAJx⟩ :=
    exists_dual_of_anisotropic_orthogonal I.E I.n D.n I.J D.J x A hn hJ D.J_det hβ0 hxA hAJ
  obtain ⟨j, hjv, hjr⟩ := GlobalTheory.T.exists_unitary_orthogonal_embedding_stabilizer I.E (starRingEnd I.E) I.n D.n I.J D.J x u A A'
    (isUnit_iff_ne_zero.mpr hβ0) hxA hAJx hAJ hA'A hA'x huA hux hres
  ext y
  constructor
  · rintro ⟨g, ⟨γ, hγ, hg1, hg2⟩, rfl⟩
    have hIm := isImage_embA D hres hv hf (γ := (γ : Matrix (Fin D.n) (Fin D.n) I.E)) (g := g) ⟨hg1, hg2⟩
    have hj := hjv ⟨γ, hγ⟩
    refine ⟨⟨(j ⟨γ, hγ⟩ : GL (Fin I.n) I.E), (j ⟨γ, hγ⟩).2, ?_⟩, (hf g.2).1⟩
    change IsImage I _ _
    rw [hj]
    exact hIm
  · rintro ⟨⟨δ, hδ, hy1, hy2⟩, hyx⟩
    have h3 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((δ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x) i)) =
        fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i) := by
      rw [← GlobalTheory.Proof.rational_unipotentRadical_mem_adelic.map_mulVec_incl, ← hy2]
      exact hyx
    have hδx : (δ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x = x := by
      funext i
      exact inclE_injective I (congrFun h3 i)
    obtain ⟨γ₀, hγ₀⟩ := hjr ⟨δ, hδ⟩ hδx
    obtain ⟨g, hg⟩ := exists_isImage D.inst (γ₀ : GL (Fin D.n) I.E) γ₀.2
    refine ⟨g, ⟨(γ₀ : GL (Fin D.n) I.E), γ₀.2, hg.1, hg.2⟩, ?_⟩
    have hIm := isImage_embA D hres hv hf hg
    have hM : vecMulVec x u + A * ((γ₀ : GL (Fin D.n) I.E) : Matrix (Fin D.n) (Fin D.n) I.E) * A' =
        (δ : Matrix (Fin I.n) (Fin I.n) I.E) := by
      rw [← hjv γ₀, hγ₀]
    rw [hM] at hIm
    exact subsingleton_isImage I _ hIm ⟨hy1, hy2⟩

end GlobalTheory.StabUnfold

import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.MkLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.I

section Alg
variable {R : Type} [CommRing R]

private def pe (e : R) (he : e * e = e) : Matrix (Fin 2) (Fin 2) R →* Matrix (Fin 2) (Fin 2) R where
  toFun M := 1 + e • (M - 1)
  map_one' := by simp
  map_mul' A B := by
    obtain ⟨X, rfl⟩ : ∃ X, A = 1 + X := ⟨A - 1, by abel⟩
    obtain ⟨Y, rfl⟩ : ∃ Y, B = 1 + Y := ⟨B - 1, by abel⟩
    have h1 : (1 + X) * (1 + Y) - 1 = X + Y + X * Y := by noncomm_ring
    change 1 + e • ((1 + X) * (1 + Y) - 1) = (1 + e • (1 + X - 1)) * (1 + e • (1 + Y - 1))
    rw [h1, add_sub_cancel_left, add_sub_cancel_left]
    simp only [smul_add, mul_add, add_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, he]
    abel

private theorem pe_val (e : R) (he : e * e = e) (M : Matrix (Fin 2) (Fin 2) R) :
    pe e he M = 1 + e • (M - 1) := rfl

private theorem idem_compl (e : R) (he : e * e = e) : (1 - e) * (1 - e) = 1 - e := by
  linear_combination he

private theorem comm0 (c : R) (X Y : Matrix (Fin 2) (Fin 2) R) (h : c • Y = 0) :
    Commute (1 + c • X) (1 + Y) := by
  have h1 : (c • X) * Y = 0 := by rw [Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_zero]
  have h2 : Y * (c • X) = 0 := by rw [Matrix.mul_smul, ← Matrix.smul_mul, h, Matrix.zero_mul]
  change _ * _ = _ * _
  simp only [mul_add, add_mul, one_mul, mul_one, h1, h2]
  abel

private theorem split (e : R) (he : e * e = e) (M : Matrix (Fin 2) (Fin 2) R) :
    M = pe (1 - e) (idem_compl e he) M * pe e he M := by
  obtain ⟨X, rfl⟩ : ∃ X, M = 1 + X := ⟨M - 1, by abel⟩
  have h0 : (1 - e) * e = 0 := by linear_combination -he
  have h1 : ((1 - e) • X) * (e • X) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h0, zero_smul]
  have e1 : pe (1 - e) (idem_compl e he) (1 + X) = 1 + (1 - e) • X := by
    rw [pe_val, add_sub_cancel_left]
  have e2 : pe e he (1 + X) = 1 + e • X := by rw [pe_val, add_sub_cancel_left]
  rw [e1, e2]
  simp only [mul_add, add_mul, one_mul, mul_one, h1]
  rw [sub_smul, one_smul]
  abel

end Alg

section Ad
variable {E : Type} [Field E] [NumberField E]

private theorem fin_of_inf (g : GL (Fin 2) (A E))
    (hg : ∀ i j, (g.val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j).1) :
    g = finGL E 2 (Matrix.GeneralLinearGroup.map (pFin E) g) := by
  have h1 := map_cornerGL_of_zero (sFin E) (RingHom.fst (InfiniteAdeleRing E) (Af E)) (fun _ => rfl)
    (Matrix.GeneralLinearGroup.map (pFin E) g)
  have h2 := pFin_finGL (E := E) (a := 2) (Matrix.GeneralLinearGroup.map (pFin E) g)
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · have h3 : ((finGL E 2 (Matrix.GeneralLinearGroup.map (pFin E) g)).val i j).1 =
        (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing E)) i j :=
      congrArg (fun x : GL (Fin 2) (InfiniteAdeleRing E) => x.val i j) h1
    rw [hg, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  · exact (congrArg (fun x : GL (Fin 2) (Af E) => x.val i j) h2).symm

end Ad

section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem two_ne (v : P F) : (2 : Kv v) ≠ 0 := by
  intro h
  have h' : algebraMap F (Kv v) 2 = 0 := by rw [map_ofNat]; exact h
  exact two_ne_zero ((map_eq_zero _).1 h')

private theorem sg_zero (v : P F) : sg v 0 = 0 := by
  obtain ⟨hadd, -⟩ := sgLaws F v
  have := hadd 0 0
  simpa using this

private theorem mk_zero (D : Dat F E) : D.mkE 0 0 = 0 := by simp [Dat.mkE]

private theorem pm (D : Dat F E) (v : P F) (θ : Kv v) (hθ : θ ^ 2 = algebraMap F (Kv v) D.δ) (a b c d : Kv v) :
    D.mkE (sg v a) (sg v b) * D.mkE (sg v c) (sg v d) =
      D.mkE (sg v (a * c + θ ^ 2 * (b * d))) (sg v (a * d + b * c)) := by
  obtain ⟨hmul, -⟩ := mkLaws F E D
  obtain ⟨hadd, hsm, hcp, -⟩ := sgLaws F v
  have hr : cp v (rt D.δ) = θ ^ 2 := by rw [hθ]; rfl
  rw [hmul, hadd, hadd]
  simp only [hsm, hcp, hr]

private noncomputable def ee (D : Dat F E) (v : P F) (θ : Kv v) : A E := D.mkE (sg v (1 / 2)) (sg v (-(1 / (2 * θ))))

private theorem ee_idem (D : Dat F E) (v : P F) (θ : Kv v) (hθ : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) :
    ee D v θ * ee D v θ = ee D v θ := by
  have h2 := two_ne v
  rw [ee, pm D v θ hθ]
  congr 2
  · field_simp; ring
  · field_simp; ring

private theorem ee_sE (D : Dat F E) (v : P F) (θ : Kv v) (hθ : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (k : Kv v) :
    ee D v θ * sE D v θ k = 0 := by
  have h2 := two_ne v
  rw [ee, sE, pm D v θ hθ]
  have e1 : (1 / 2 * (k / 2) + θ ^ 2 * (-(1 / (2 * θ)) * (k / (2 * θ))) : Kv v) = 0 := by field_simp; ring
  have e2 : (1 / 2 * (k / (2 * θ)) + -(1 / (2 * θ)) * (k / 2) : Kv v) = 0 := by field_simp; ring
  rw [e1, e2, sg_zero, mk_zero]

private theorem squareRoot_idempotent_embed (D : Dat F E) (v : P F) (θ : Kv v) (hθ : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (s : Kv v) :
    ee D v θ * D.mkE (sg v (s / 2)) (sg v (-(s / (2 * θ)))) = D.mkE (sg v (s / 2)) (sg v (-(s / (2 * θ)))) := by
  have h2 := two_ne v
  rw [ee, pm D v θ hθ]
  congr 2
  · field_simp; ring
  · field_simp; ring

private theorem ee_fst (D : Dat F E) (v : P F) (θ : Kv v) : (ee D v θ).1 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, hs, -, -⟩ := sgLaws F v
  have h : ∀ x, (AdeleBaseChange.adeleMap F E (sg v x)).1 = 0 := fun x => by
    change InfinitePlace.infiniteAdeleRingMap (sg v x).1 = 0
    rw [(hs x).1, map_zero]
  change (AdeleBaseChange.adeleMap F E _).1 + (AdeleBaseChange.adeleMap F E _).1 * (rt D.θ).1 = 0
  rw [h, h, zero_mul, add_zero]

end Main

end UpperTheory.ConvolutionTheory.R2.I

theorem UpperTheory.ConvolutionTheory.R2.I.decomp :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex E] (D : Dat F E) (v : P F) (θ : Kv v) (J : GLv v →* GL (Fin 2) (A E)), Splt D v θ J → ∀ h : GL (Fin 2) (A E),
      ∃ h' k, h = h' * finGL E 2 k ∧ (∀ s, Commute h' (nbar D v θ s)) ∧ ∀ x, Commute (finGL E 2 k) (J x) := by
  intro F E _ _ _ _ _ _ D v θ J hs h
  have he := ee_idem D v θ hs.sq hs.ne
  obtain ⟨k, hk⟩ : ∃ k, Units.map (pe (ee D v θ) he) h = finGL E 2 k := by
    refine ⟨_, fin_of_inf _ fun i j => ?_⟩
    change ((1 + ee D v θ • (h.val - 1) : Matrix (Fin 2) (Fin 2) (A E)) i j).1 = _
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    change ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j).1 + (ee D v θ).1 * _ = _
    rw [ee_fst, zero_mul, add_zero]
  refine ⟨Units.map (pe (1 - ee D v θ) (idem_compl _ he)) h, k, ?_, fun s => ?_, fun x => ?_⟩
  · rw [← hk]
    exact Units.ext (split _ he h.val)
  · have hn : (nbar D v θ s).val = 1 + !![0, D.mkE (sg v (s / 2)) (sg v (-(s / (2 * θ)))); 0, 0] := by
      ext i j
      change (!![1, D.mkE (sg v (s / 2)) (sg v (-(s / (2 * θ)))); 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j = _
      fin_cases i <;> fin_cases j <;> simp
    have hz := squareRoot_idempotent_embed D v θ hs.sq hs.ne s
    refine Units.ext ?_
    have := comm0 (1 - ee D v θ) (h.val - 1) !![0, D.mkE (sg v (s / 2)) (sg v (-(s / (2 * θ)))); 0, 0] (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sub_mul, hz])
    rw [← hn] at this
    exact this.eq
  · rw [← hk]
    have hj : (J x).val = 1 + Matrix.of fun i j => sE D v θ (x.val i j - (1 : M2 v) i j) := by
      ext i j
      rw [hs.val]; rfl
    refine Units.ext ?_
    have := comm0 (ee D v θ) (h.val - 1) (Matrix.of fun i j => sE D v θ (x.val i j - (1 : M2 v) i j)) (by
      ext i j
      simp [ee_sE D v θ hs.sq hs.ne])
    rw [← hj] at this
    exact this.eq

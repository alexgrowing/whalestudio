import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.MkLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.I

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (D : Dat F E) (v : P F) (θ : Kv v)

private theorem two_ne : (2 : Kv v) ≠ 0 := by
  rw [← map_ofNat (algebraMap F (Kv v)) 2]
  exact (map_ne_zero _).2 two_ne_zero

private theorem sg_add' (x y : Kv v) : sg v (x + y) = sg v x + sg v y := (sgLaws F v).1 x y
private theorem sg_mul' (a : A F) (x : Kv v) : a * sg v x = sg v (cp v a * x) := (sgLaws F v).2.1 a x
private theorem cp_sg' (x : Kv v) : cp v (sg v x) = x := (sgLaws F v).2.2.1 x
private theorem sg_zero' : sg v (0 : Kv v) = 0 := by
  have h := sg_add' v (0 : Kv v) 0
  simpa using h
private theorem sg_neg' (x : Kv v) : sg v (-x) = -sg v x := by
  have h := sg_add' v (-x) x
  rw [neg_add_cancel, sg_zero'] at h
  exact eq_neg_of_add_eq_zero_left h.symm
private theorem sg_mm (x y : Kv v) : sg v x * sg v y = sg v (x * y) := by rw [sg_mul', cp_sg']
private theorem cp_rt' (c : F) : cp v (rt c) = algebraMap F (Kv v) c := rfl

private theorem mk_add (u t u' t' : A F) : D.mkE u t + D.mkE u' t' = D.mkE (u + u') (t + t') :=
  (mkLaws F E D).2.1 u t u' t'
private theorem mk_mul (u t u' t' : A F) :
    D.mkE u t * D.mkE u' t' = D.mkE (u * u' + rt D.δ * (t * t')) (u * t' + t * u') :=
  (mkLaws F E D).1 u t u' t'
private theorem mk_zero : D.mkE (0 : A F) 0 = 0 := by
  have h := mk_add D (0 : A F) 0 0 0
  simpa using h
private theorem mk_co (u t : A F) : D.co (D.mkE u t) = ![u, t] := (mkLaws F E D).2.2.2.1 u t

private noncomputable def sB (k : Kv v) : A E := D.mkE (sg v (k / 2)) (sg v (-(k / (2 * θ))))

variable {θ}

private theorem mk_sE (hq : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (u t : A F) (k : Kv v) :
    D.mkE u t * sE D v θ k = sE D v θ ((cp v u + cp v t * θ) * k) := by
  have h2 := two_ne (F := F) v
  unfold sE
  rw [mk_mul]
  simp only [sg_mul', ← sg_add', map_mul, cp_sg', cp_rt']
  rw [← hq]
  congr 2
  · congr 1; field_simp
  · congr 1; field_simp

private theorem mk_sB (hq : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (u t : A F) (k : Kv v) :
    D.mkE u t * sB D v θ k = sB D v θ ((cp v u - cp v t * θ) * k) := by
  have h2 := two_ne (F := F) v
  unfold sB
  rw [mk_mul]
  simp only [sg_mul', ← sg_add', map_mul, cp_sg', cp_rt']
  rw [← hq]
  congr 2
  · congr 1; field_simp; ring
  · congr 1; field_simp; ring

private theorem sE_mul (hq : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (k k' : Kv v) :
    sE D v θ k * sE D v θ k' = sE D v θ (k * k') := by
  have h2 := two_ne (F := F) v
  have h := mk_sE D v hq h0 (sg v (k / 2)) (sg v (k / (2 * θ))) k'
  rw [cp_sg', cp_sg'] at h
  have e : (k / 2 + k / (2 * θ) * θ) * k' = k * k' := by field_simp; ring
  rw [e] at h
  exact h

private theorem sE_sB (hq : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (k k' : Kv v) :
    sE D v θ k * sB D v θ k' = 0 := by
  have h2 := two_ne (F := F) v
  have h := mk_sE D v hq h0 (sg v (k' / 2)) (sg v (-(k' / (2 * θ)))) k
  rw [cp_sg', cp_sg'] at h
  have e : (k' / 2 + -(k' / (2 * θ)) * θ) * k = 0 := by field_simp; ring
  rw [e] at h
  rw [mul_comm]
  refine h.trans ?_
  unfold sE
  simp [sg_zero', mk_zero]

private theorem bar_sE (k : Kv v) : D.bar (sE D v θ k) = sB D v θ k := by
  unfold sE sB
  rw [sg_neg']
  exact (mkLaws F E D).2.2.2.2.2.1 _ _

private theorem add_pair (h0 : θ ≠ 0) (u t : A F) (k k' : Kv v) :
    D.mkE u t + sE D v θ k + sB D v θ k' =
      D.mkE (u + sg v ((k + k') / 2)) (t + sg v ((k - k') / (2 * θ))) := by
  have h2 := two_ne (F := F) v
  unfold sE sB
  rw [mk_add, mk_add, add_assoc, add_assoc, ← sg_add', ← sg_add']
  congr 3
  · ring
  · ring

private theorem herm_sE (hq : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (X : V4 F) (i j : Fin 2) (k : Kv v) :
    D.herm X i j * sE D v θ k = sE D v θ (mat v θ X i j * k) := by
  fin_cases i <;> fin_cases j
  · simpa [Dat.herm, mat, sub_eq_add_neg] using mk_sE D v hq h0 (X 1) 0 k
  · simpa [Dat.herm, mat, sub_eq_add_neg] using mk_sE D v hq h0 (X 2) (X 3) k
  · simpa [Dat.herm, mat, sub_eq_add_neg] using mk_sE D v hq h0 (X 2) (-X 3) k
  · simpa [Dat.herm, mat, sub_eq_add_neg] using mk_sE D v hq h0 (X 0) 0 k

private theorem herm_sB (hq : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (X : V4 F) (i j : Fin 2) (k : Kv v) :
    D.herm X i j * sB D v θ k = sB D v θ (mat v θ X j i * k) := by
  fin_cases i <;> fin_cases j
  · simpa [Dat.herm, mat, sub_eq_add_neg] using mk_sB D v hq h0 (X 1) 0 k
  · simpa [Dat.herm, mat, sub_eq_add_neg] using mk_sB D v hq h0 (X 2) (X 3) k
  · simpa [Dat.herm, mat, sub_eq_add_neg] using mk_sB D v hq h0 (X 2) (-X 3) k
  · simpa [Dat.herm, mat, sub_eq_add_neg] using mk_sB D v hq h0 (X 0) 0 k

private theorem sE_add (k l : Kv v) : sE D v θ (k + l) = sE D v θ k + sE D v θ l := by
  unfold sE
  rw [mk_add, ← sg_add', ← sg_add']
  congr 2 <;> ring

private theorem sE_sub (k l : Kv v) : sE D v θ (k - l) = sE D v θ k - sE D v θ l := by
  have h := sE_add (θ := θ) D v (k - l) l
  rw [sub_add_cancel] at h
  rw [h]
  ring

private theorem sB_add (k l : Kv v) : sB D v θ (k + l) = sB D v θ k + sB D v θ l := by
  unfold sB
  rw [mk_add, ← sg_add', ← sg_add']
  congr 2 <;> ring

private theorem act_eq {J : GLv v →* GL (Fin 2) (A E)} (hs : Splt D v θ J) (y : GLv v) (X : V4 F) (Pm : M2 v)
    (hP : Pm = (y.val - 1) * mat v θ X) :
    D.act (J y) X = ![X 0 + sg v (Pm 1 1), X 1 + sg v (Pm 0 0), X 2 + sg v ((Pm 0 1 + Pm 1 0) / 2),
      X 3 + sg v ((Pm 0 1 - Pm 1 0) / (2 * θ))] := by
  have hq := hs.sq
  have h0 := hs.ne
  have h2 := two_ne (F := F) v
  obtain ⟨N, hN⟩ : ∃ N : M2 v, N = y.val - 1 := ⟨_, rfl⟩
  rw [← hN] at hP
  have hNe : ∀ i j, y.val i j - (1 : M2 v) i j = N i j := by
    intro i j
    rw [hN]
    rfl
  obtain ⟨H, hH⟩ : ∃ H, H = D.herm X := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin 2) (Fin 2) (A E), ∀ i j, T i j = sE D v θ (N i j) :=
    ⟨fun i j => sE D v θ (N i j), fun _ _ => rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T : Matrix (Fin 2) (Fin 2) (A E), ∀ i j, T i j = sB D v θ (N i j) :=
    ⟨fun i j => sB D v θ (N i j), fun _ _ => rfl⟩
  have hv : (J y).val = 1 + T := by
    ext i j
    rw [hs.val, Matrix.add_apply, hNe, hT]
  have hb : (J y).val.map D.bar = 1 + T' := by
    ext i j
    rw [Matrix.map_apply, hs.val, map_add, bar_sE, Matrix.add_apply]
    have e : D.bar ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j) = (1 : Matrix (Fin 2) (Fin 2) (A E)) i j := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    rw [e, hNe, hT']
  have hz : T * H * T'ᵀ = 0 := by
    ext i j
    have z := sE_sB D v hq h0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.zero_apply, hT, hT']
    linear_combination H 0 0 * z (N i 0) (N j 0) + H 1 0 * z (N i 1) (N j 0) +
      H 0 1 * z (N i 0) (N j 1) + H 1 1 * z (N i 1) (N j 1)
  have hTH : ∀ i j, (T * H) i j = sE D v θ (Pm i j) := by
    intro i j
    have e := fun a b k => herm_sE D v hq h0 X a b k
    rw [← hH] at e
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hT]
    rw [hP, Matrix.mul_apply, Fin.sum_univ_two, sE_add, mul_comm (sE D v θ _) (H 0 j),
      mul_comm (sE D v θ _) (H 1 j), e, e, mul_comm (mat v θ X 0 j), mul_comm (mat v θ X 1 j)]
  have hHT : ∀ i j, (H * T'ᵀ) i j = sB D v θ (Pm j i) := by
    intro i j
    have e := fun a b k => herm_sB D v hq h0 X a b k
    rw [← hH] at e
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, hT']
    rw [hP, Matrix.mul_apply, Fin.sum_univ_two, sB_add, e, e, mul_comm (mat v θ X 0 i),
      mul_comm (mat v θ X 1 i)]
  have hR : (J y).val * H * ((J y).val.map D.bar)ᵀ = H + T * H + H * T'ᵀ := by
    rw [hb, hv, Matrix.transpose_add, Matrix.transpose_one]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hz, add_zero]
  have hent : ∀ i j, ((J y).val * H * ((J y).val.map D.bar)ᵀ) i j =
      H i j + sE D v θ (Pm i j) + sB D v θ (Pm j i) := by
    intro i j
    rw [hR, Matrix.add_apply, Matrix.add_apply, hTH, hHT]
  have e00 : H 0 0 = D.mkE (X 1) 0 := by rw [hH]; rfl
  have e01 : H 0 1 = D.mkE (X 2) (X 3) := by rw [hH]; rfl
  have e11 : H 1 1 = D.mkE (X 0) 0 := by rw [hH]; rfl
  have hd : ∀ a : Kv v, (a + a) / 2 = a := fun a => by
    rw [← two_mul, mul_div_cancel_left₀ _ h2]
  unfold Dat.act Dat.unherm
  rw [← hH]
  simp only [hent, e00, e01, e11, add_pair D v h0, mk_co, hd, sub_self, zero_div, sg_zero', add_zero]
  funext i
  fin_cases i <;> simp

private theorem nu_J {J : GLv v →* GL (Fin 2) (A E)} (hs : Splt D v θ J) (x : GLv v) :
    nu F (J x) = idl v (Matrix.GeneralLinearGroup.det x) := by
  have hq := hs.sq
  have h0 := hs.ne
  have h2 := two_ne (F := F) v
  obtain ⟨d, hd⟩ : ∃ d : Kv v, d = x.val.det - 1 := ⟨_, rfl⟩
  have hz : ((Matrix.GeneralLinearGroup.det (J x) : (A E)ˣ) : A E) =
      D.mkE (1 + sg v (d / 2)) (sg v (d / (2 * θ))) := by
    have h1 : D.mkE (1 + sg v (d / 2)) (sg v (d / (2 * θ))) = 1 + sE D v θ d := by
      unfold sE
      rw [← (mkLaws F E D).2.2.1, mk_add, zero_add]
    have h3 : d = (x.val 0 0 - 1) + (x.val 1 1 - 1) + (x.val 0 0 - 1) * (x.val 1 1 - 1) -
        x.val 0 1 * x.val 1 0 := by
      rw [hd, Matrix.det_fin_two]
      ring
    rw [h1, h3, sE_sub, sE_add, sE_add, ← sE_mul D v hq h0, ← sE_mul D v hq h0,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    simp only [hs.val, Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true,
      Matrix.one_apply_ne, sub_zero, zero_add]
    ring
  refine Units.ext ?_
  unfold nu
  rw [(mkLaws F E D).2.2.2.2.2.2 _ _ _ hz, (sgLaws F v).2.2.2.1,
    Matrix.GeneralLinearGroup.val_det_apply, ← hd]
  have s : sg v d = sg v (d / 2) + sg v (d / 2) := by
    rw [← sg_add', add_halves]
  have t : rt D.δ * sg v (d / (2 * θ)) ^ 2 = sg v (d / 2) ^ 2 := by
    rw [sq, sq, sg_mm, sg_mm, sg_mul', cp_rt', ← hq]
    congr 1
    field_simp
  rw [t, s]
  ring

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.R2.I

theorem UpperTheory.ConvolutionTheory.R2.I.actJ :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F) (θ : Kv v) (J : GLv v →* GL (Fin 2) (A E)), Splt D v θ J → ∀ x,
      nu F (J x) = idl v (Matrix.GeneralLinearGroup.det x) ∧
      ∀ X, away v (D.act (J x)⁻¹ X) = away v X ∧ mat v θ (D.act (J x)⁻¹ X) = (x⁻¹).val * mat v θ X := by
  intro F E _ _ _ _ _ D v θ J hs x
  refine ⟨nu_J D v hs x, fun X => ?_⟩
  have h0 := hs.ne
  have h2 := two_ne (F := F) v
  rw [← map_inv]
  obtain ⟨Pm, hP⟩ : ∃ Pm : M2 v, Pm = ((x⁻¹).val - 1) * mat v θ X := ⟨_, rfl⟩
  rw [act_eq D v hs x⁻¹ X Pm hP]
  have aw : ∀ (a : A F) (c : Kv v), (a + sg v c) - sg v (cp v (a + sg v c)) = a - sg v (cp v a) := by
    intro a c
    rw [map_add, cp_sg', sg_add']
    ring
  refine ⟨funext fun i => ?_, ?_⟩
  · fin_cases i
    · exact aw (X 0) _
    · exact aw (X 1) _
    · exact aw (X 2) _
    · exact aw (X 3) _
  · have e : (x⁻¹).val * mat v θ X = mat v θ X + Pm := by
      rw [hP, Matrix.sub_mul, Matrix.one_mul]
      abel
    rw [e]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · change cp v (X 1 + sg v (Pm 0 0)) = cp v (X 1) + Pm 0 0
      rw [map_add, cp_sg']
    · change cp v (X 2 + sg v ((Pm 0 1 + Pm 1 0) / 2)) + cp v (X 3 + sg v ((Pm 0 1 - Pm 1 0) / (2 * θ))) * θ =
        cp v (X 2) + cp v (X 3) * θ + Pm 0 1
      rw [map_add, map_add, cp_sg', cp_sg']
      field_simp
      ring
    · change cp v (X 2 + sg v ((Pm 0 1 + Pm 1 0) / 2)) - cp v (X 3 + sg v ((Pm 0 1 - Pm 1 0) / (2 * θ))) * θ =
        cp v (X 2) - cp v (X 3) * θ + Pm 1 0
      rw [map_add, map_add, cp_sg', cp_sg']
      field_simp
      ring
    · change cp v (X 0 + sg v (Pm 1 1)) = cp v (X 0) + Pm 1 1
      rw [map_add, cp_sg']

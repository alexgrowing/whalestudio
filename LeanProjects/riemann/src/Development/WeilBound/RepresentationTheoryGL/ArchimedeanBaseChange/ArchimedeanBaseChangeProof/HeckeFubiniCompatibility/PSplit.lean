import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntZero

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E
open PositivityTheory.RgTw (G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)

namespace PositivityTheory.Rg.BcB.CG

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def infP (n : ℕ) (y : InfinitePlace E → G n) : GA E n :=
  infGL E n (Units.map (Matrix.piRingEquiv (n := Fin n) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
    (MulEquiv.piUnits.symm y))

theorem infinitePart_mul (n : ℕ) (y y' : InfinitePlace E → G n) : infP n (y * y') = infP n y * infP n y' := by
  simp only [infP, map_mul]

theorem gInf_infGL (n : ℕ) (v : InfinitePlace E) (x : GL (Fin n) (Cinf E)) (i j : Fin n) :
    (gInf v (infGL E n x)).val i j = x.val i j v :=
  congrArg (fun y : GL (Fin n) (Cinf E) => y.val i j v) (pInf_infGL (E := E) (a := n) x)

theorem gInf_infP (n : ℕ) (y : InfinitePlace E → G n) (v : InfinitePlace E) : gInf v (infP n y) = y v := by
  ext i j
  exact gInf_infGL n v _ i j

theorem gFin_infP (n : ℕ) (y : InfinitePlace E → G n) : gFin (infP n y) = 1 :=
  pFin_infGL _

theorem gInf_finGL (n : ℕ) (v : InfinitePlace E) (k : GL (Fin n) (Af E)) : gInf v (finGL E n k) = 1 := by
  ext i j
  have h2 : (GeneralLinearGroup.map (pInf E) (finGL E n k)).val i j = (1 : GL (Fin n) (Cinf E)).val i j :=
    congrArg (fun y : GL (Fin n) (Cinf E) => y.val i j) (pInf_finGL (E := E) (a := n) k)
  change (GeneralLinearGroup.map (pInf E) (finGL E n k)).val i j v = _
  rw [h2]
  by_cases h : i = j <;> simp [h]

omit [IsCMField E] in
theorem gFin_finGL (n : ℕ) (k : GL (Fin n) (Af E)) : gFin (finGL E n k) = k :=
  pFin_finGL k

theorem infinitePart_gInf (n : ℕ) (g : GA E n) : infP n (fun v => gInf v g) = infGL E n (GeneralLinearGroup.map (pInf E) g) := by
  rfl

theorem infinitePart_mul_finGL (n : ℕ) (g : GA E n) : infP n (fun v => gInf v g) * finGL E n (gFin g) = g := by
  rw [infinitePart_gInf]; exact infGL_mul_finGL g

theorem continuous_pInf' : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_gInf (n : ℕ) (v : InfinitePlace E) : Continuous (gInf (n := n) v : GA E n → G n) :=
  Continuous.units_map _ (continuous_id.matrix_map ((continuous_apply v).comp continuous_pInf'))

omit [IsCMField E] in
theorem continuous_gFin (n : ℕ) : Continuous (gFin : GA E n → GL (Fin n) (Af E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_snd)

theorem continuous_infGL' (n : ℕ) : Continuous (infGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))))

omit [IsCMField E] in
theorem continuous_finGL' (n : ℕ) : Continuous (finGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map (continuous_const.prodMk continuous_id :
    Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))

theorem continuous_infP (n : ℕ) : Continuous (infP (E := E) n) := by
  refine (continuous_infGL' n).comp ?_
  refine Continuous.units_map _ ?_ |>.comp (ContinuousMulEquiv.piUnits (M := fun _ : InfinitePlace E =>
    Matrix (Fin n) (Fin n) ℂ)).symm.continuous
  exact continuous_pi fun i => continuous_pi fun j => continuous_pi fun v => (continuous_apply v).matrix_elem i j

def splitGA (n : ℕ) : (InfinitePlace E → G n) × GL (Fin n) (Af E) ≃ₜ* GA E n where
  toFun p := infP n p.1 * finGL E n p.2
  invFun g := (fun v => gInf v g, gFin g)
  left_inv p := by
    ext1
    · funext v; simp [gInf_infP, gInf_finGL]
    · simp [gFin_infP, gFin_finGL]
  right_inv g := infinitePart_mul_finGL n g
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, infinitePart_mul, map_mul]
    have h : finGL E n p.2 * infP n q.1 = infP n q.1 * finGL E n p.2 := (infGL_comm _ _).symm
    rw [show infP n p.1 * finGL E n p.2 * (infP n q.1 * finGL E n q.2) =
      infP n p.1 * ((finGL E n p.2 * infP n q.1) * finGL E n q.2) by simp only [mul_assoc], h]
    simp only [mul_assoc]
  continuous_toFun := ((continuous_infP n).comp continuous_fst).mul ((continuous_finGL' n).comp continuous_snd)
  continuous_invFun := (continuous_pi fun v => continuous_gInf n v).prodMk (continuous_gFin n)

theorem splitGA_apply (n : ℕ) (p : (InfinitePlace E → G n) × GL (Fin n) (Af E)) :
    splitGA n p = infP n p.1 * finGL E n p.2 := rfl

theorem gInf_splitGA (n : ℕ) (p : (InfinitePlace E → G n) × GL (Fin n) (Af E)) (v : InfinitePlace E) :
    gInf v (splitGA n p) = p.1 v := by
  simp [splitGA_apply, gInf_infP, gInf_finGL]

theorem gFin_splitGA (n : ℕ) (p : (InfinitePlace E → G n) × GL (Fin n) (Af E)) : gFin (splitGA n p) = p.2 := by
  simp [splitGA_apply, gFin_infP, gFin_finGL]

def splitH (a b : ℕ) : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b) ≃ₜ* H E a b where
  toFun z := (splitGA a (z.1, z.2.2.1), splitGA b (z.2.1, z.2.2.2))
  invFun g := (((splitGA a).symm g.1).1, ((splitGA b).symm g.2).1, ((splitGA a).symm g.1).2, ((splitGA b).symm g.2).2)
  left_inv z := by simp
  right_inv g := by simp
  map_mul' z w := by
    simp only [Prod.fst_mul, Prod.snd_mul, ← map_mul, Prod.mk_mul_mk]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem splitH_apply (a b : ℕ) (z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b)) :
    splitH a b z = (infP a z.1 * finGL E a z.2.2.1, infP b z.2.1 * finGL E b z.2.2.2) := rfl

theorem gInf_splitH₁ {a b : ℕ} (z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b)) (v : InfinitePlace E) :
    gInf v (splitH a b z).1 = z.1 v := gInf_splitGA a _ v

theorem gInf_splitH₂ {a b : ℕ} (z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b)) (v : InfinitePlace E) :
    gInf v (splitH a b z).2 = z.2.1 v := gInf_splitGA b _ v

theorem hFin_splitH {a b : ℕ} (z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b)) :
    hFin (splitH a b z) = z.2.2 := Prod.ext (gFin_splitGA a _) (gFin_splitGA b _)

end PositivityTheory.Rg.BcB.CG

end

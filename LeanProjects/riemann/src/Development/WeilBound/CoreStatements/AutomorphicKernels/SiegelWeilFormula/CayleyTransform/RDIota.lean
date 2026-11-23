import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DZTranspose
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RdExOf

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Krd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Glue

variable (d : SD σ)

def sc : (InfinitePlace F → ℂ) → AE F E := (Place.exists_sec d.cm d.B.emb).choose

theorem sc_cont : Continuous (sc d) := (Place.exists_sec d.cm d.B.emb).choose_spec.1

theorem sc_pi (x : InfinitePlace F → ℂ) (w : InfinitePlace F) : piInf (d.B.emb w) (sc d x) = x w :=
  (Place.exists_sec d.cm d.B.emb).choose_spec.2.1 x w

theorem sc_fin (x : InfinitePlace F → ℂ) : finOne F • sc d x = 0 := (Place.exists_sec d.cm d.B.emb).choose_spec.2.2.1 x

variable {p : Type} [Fintype p] [DecidableEq p]

open Classical in

def fam (w : InfinitePlace F) (Z : Matrix p p ℂ) (w' : InfinitePlace F) : Matrix p p ℂ := if w' = w then Z else 1

def atM (w : InfinitePlace F) (Z : Matrix p p ℂ) : Matrix p p (AE F E) :=
  Matrix.of fun i j => sc d (fun w' => fam w Z w' i j) + finOne F • (1 : Matrix p p (AE F E)) i j

theorem fin_idem : finOne F * finOne F = finOne F := by
  show ((0 : Ainf F), (1 : Af F)) * ((0 : Ainf F), (1 : Af F)) = ((0 : Ainf F), (1 : Af F))
  rw [Prod.mk_mul_mk, mul_zero, mul_one]

theorem fin_mul {q : Type} [Fintype q] (A B : Matrix q q (AE F E)) :
    finOne F • (A * B) = (finOne F • A) * (finOne F • B) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, fin_idem]

theorem cw_mul {q : Type} [Fintype q] (w : InfinitePlace F) (A B : Matrix q q (AE F E)) :
    d.cw w (A * B) = d.cw w A * d.cw w B :=
  Matrix.map_mul (f := piInf (d.B.emb w))

theorem cw_one {q : Type} [DecidableEq q] (w : InfinitePlace F) : d.cw w (1 : Matrix q q (AE F E)) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem cw_atM (w w' : InfinitePlace F) (Z : Matrix p p ℂ) : d.cw w' (atM d w Z) = fam w Z w' := by
  ext i j
  simp only [SD.cw, Matrix.map_apply, atM, Matrix.of_apply, map_add, sc_pi, Place.piInf_finOne, add_zero]

theorem fin_atM (w : InfinitePlace F) (Z : Matrix p p ℂ) : finOne F • atM d w Z = finOne F • (1 : Matrix p p (AE F E)) := by
  ext i j
  simp only [Matrix.smul_apply, atM, Matrix.of_apply, smul_add, sc_fin, zero_add, smul_smul, fin_idem]

theorem atM_mul (w : InfinitePlace F) (Z Z' : Matrix p p ℂ) : atM d w (Z * Z') = atM d w Z * atM d w Z' := by
  refine Place.cw_ext d (fun w' => ?_) ?_
  · rw [cw_mul, cw_atM, cw_atM, cw_atM]
    unfold fam
    split_ifs <;> simp
  · rw [fin_mul, fin_atM, fin_atM, fin_atM, ← fin_mul, Matrix.mul_one]

theorem atM_one (w : InfinitePlace F) : atM d w (1 : Matrix p p ℂ) = 1 := by
  refine Place.cw_ext d (fun w' => ?_) ?_
  · rw [cw_atM, cw_one]
    unfold fam
    split_ifs <;> rfl
  · rw [fin_atM]

theorem continuous_atM (w : InfinitePlace F) : Continuous (atM (p := p) d w) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Continuous.add ((sc_cont d).comp (continuous_pi fun w' => ?_)) continuous_const
  unfold fam
  split_ifs
  · exact (continuous_apply j).comp ((continuous_apply i).comp continuous_id)
  · exact continuous_const

end Glue

section Iota

variable (d : SD σ)

theorem incM_mul {p : Type} [Fintype p] (M N : Matrix p p E) : incM F (M * N) = incM F M * incM F N :=
  Matrix.map_mul (f := inclR (F := F) (AF F))

theorem incM_one {p : Type} [DecidableEq p] : incM F (1 : Matrix p p E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem bb : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
  rw [← incM_mul, Units.mul_inv, incM_one]

theorem bb' : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
  rw [← incM_mul, Units.inv_mul, incM_one]

def Zm (ζ : ℂ) (y : GR d.n) : M2 d.n := dZ d.n ζ⁻¹ * mR y * dZ d.n ζ

theorem Zm_mul {ζ : ℂ} (h : ζ ≠ 0) (y y' : GR d.n) : Zm d ζ (y * y') = Zm d ζ y * Zm d ζ y' := by
  simp only [Zm]
  rw [show mR (y * y') = mR y * mR y' from rfl]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dZ d.n ζ) (dZ d.n ζ⁻¹), dZ_mul_inv h, Matrix.one_mul]

theorem Zm_one {ζ : ℂ} (h : ζ ≠ 0) : Zm d ζ 1 = 1 := by
  simp only [Zm]
  rw [show mR (1 : GR d.n) = 1 from rfl, Matrix.mul_one, dZ_inv_mul h]

def MxI (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  incM F d.b.1 * atM d w (Zm d ζ y) * incM F (d.b⁻¹).1

theorem MxI_mul {ζ : ℂ} (h : ζ ≠ 0) (w : InfinitePlace F) (y y' : GR d.n) : MxI d w ζ (y * y') = MxI d w ζ y * MxI d w ζ y' := by
  simp only [MxI, Zm_mul d h, atM_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F (d.b⁻¹).1) (incM F d.b.1), bb', Matrix.one_mul]

theorem MxI_one {ζ : ℂ} (h : ζ ≠ 0) (w : InfinitePlace F) : MxI d w ζ 1 = 1 := by
  rw [MxI, Zm_one d h, atM_one, Matrix.mul_one, bb]

theorem inFrame_MxI (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) :
    incM F (d.b⁻¹).1 * MxI d w ζ y * incM F d.b.1 = atM d w (Zm d ζ y) := by
  simp only [MxI, Matrix.mul_assoc]
  rw [bb', Matrix.mul_one, ← Matrix.mul_assoc, bb', Matrix.one_mul]

theorem dbl_incM : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
  simp only [dbl, incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]
  congr 1
  ext i j
  simp

theorem conj_unit {ι : Type} [Fintype ι] [DecidableEq ι] (b bi Z D Q : Matrix ι ι ℂ) (hb : b * bi = 1)
    (hQ : bᵀ * D * b.map star = Q) (hZ : Zᵀ * Q * Z.map star = Q) : (b * Z * bi)ᵀ * D * (b * Z * bi).map star = D := by
  have hD : D = biᵀ * Q * bi.map star := by
    calc D = (b * bi)ᵀ * D * (b * bi).map star := by
          rw [hb, Matrix.transpose_one, mapStar_one, Matrix.one_mul, Matrix.mul_one]
      _ = biᵀ * (bᵀ * D * b.map star) * bi.map star := by
          rw [Matrix.transpose_mul, mapStar_mul]; simp only [Matrix.mul_assoc]
      _ = biᵀ * Q * bi.map star := by rw [hQ]
  calc (b * Z * bi)ᵀ * D * (b * Z * bi).map star = biᵀ * (Zᵀ * (bᵀ * D * b.map star) * Z.map star) * bi.map star := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, mapStar_mul, mapStar_mul]; simp only [Matrix.mul_assoc]
    _ = D := by rw [hQ, hZ, ← hD]

theorem cw_transpose {p q : Type} (w : InfinitePlace F) (A : Matrix p q (AE F E)) : d.cw w Aᵀ = (d.cw w A)ᵀ :=
  Matrix.transpose_map

theorem cw_incM {p q : Type} (w : InfinitePlace F) (M : Matrix p q E) : d.cw w (incM F M) = M.map (d.B.emb w).1 :=
  Matrix.ext fun i j => PositivityTheory.ThKG.Tow.Levi.piInf_incl (d.B.emb w) (M i j)

theorem map_sig_emb {p q : Type} (w : InfinitePlace F) (M : Matrix p q E) :
    (M.map σ).map (d.B.emb w).1 = (M.map (d.B.emb w).1).map star := by
  ext i j
  exact d.cm.2.2.2 _ _

theorem hQ_w {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (w : InfinitePlace F) :
    (d.b.1.map (d.B.emb w).1)ᵀ * (dbl d.Y.J).map (d.B.emb w).1 * (d.b.1.map (d.B.emb w).1).map star = Qc d.n ε := by
  have h := congrArg (fun M => M.map (d.B.emb w).1) hε
  simp only [Matrix.map_mul (f := (d.B.emb w).1), map_sig_emb] at h
  rw [Matrix.transpose_map] at h
  rw [h]
  simp only [Qc, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem map_cA_smul {p q : Type} (a : AF F) (A : Matrix p q (AE F E)) : (a • A).map (cA σ) = a • A.map (cA σ) := by
  ext i j
  exact map_smul (cA σ) a (A i j)

theorem fin_MxI (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) : finOne F • MxI d w ζ y = finOne F • 1 := by
  rw [MxI, fin_mul, fin_mul, fin_atM, ← fin_mul, ← fin_mul, Matrix.mul_one, bb]

theorem MxI_unitary {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) (y : GR d.n) :
    (MxI d w ζ y)ᵀ * dbl (incM F d.Y.J) * (MxI d w ζ y).map (cA σ) = dbl (incM F d.Y.J) := by
  refine Place.cw_ext d (fun w' => ?_) ?_
  · rw [cw_mul, cw_mul, Place.cw_cA, cw_transpose, dbl_incM, cw_incM]
    have hM : d.cw w' (MxI d w ζ y) = d.b.1.map (d.B.emb w').1 * fam w (Zm d ζ y) w' * (d.b⁻¹).1.map (d.B.emb w').1 := by
      rw [MxI, cw_mul, cw_mul, cw_incM, cw_incM, cw_atM]
    rw [hM]
    refine conj_unit _ _ _ _ _ ?_ (hQ_w d hε w') ?_
    · rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · unfold fam
      split_ifs
      · exact (unitary_iff hζ (mR y)).2 y.2
      · rw [Matrix.transpose_one, mapStar_one, Matrix.one_mul, Matrix.mul_one]
  · have e1 : (finOne F • (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))).map (cA σ) = finOne F • 1 := by
      rw [map_cA_smul, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [fin_mul, fin_mul, ← Matrix.transpose_smul, fin_MxI, ← map_cA_smul, fin_MxI, e1, Matrix.transpose_smul,
      Matrix.transpose_one, ← fin_mul, ← fin_mul, Matrix.mul_one, Matrix.one_mul]

def iotaF {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) (y : GR d.n) : d.G :=
  ⟨⟨MxI d w ζ y, MxI d w ζ y⁻¹, by rw [← MxI_mul d (zeta_ne hζ), mul_inv_cancel, MxI_one d (zeta_ne hζ)],
    by rw [← MxI_mul d (zeta_ne hζ), inv_mul_cancel, MxI_one d (zeta_ne hζ)]⟩, MxI_unitary d hε hζ w y⟩

def iota {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) : GR d.n →* d.G where
  toFun := iotaF d hε hζ w
  map_one' := Subtype.ext (Units.ext (MxI_one d (zeta_ne hζ) w))
  map_mul' a b := Subtype.ext (Units.ext (MxI_mul d (zeta_ne hζ) w a b))

theorem inFrame_iota {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) (y : GR d.n) :
    inFrame d.b (iota d hε hζ w y) = atM d w (Zm d ζ y) :=
  inFrame_MxI d w ζ y

theorem continuous_iota {ε : ℤˣ} {ζ : ℂ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) : Continuous (iota d hε hζ w) := by
  have hm : Continuous fun y : GR d.n => mR y := Units.continuous_val.comp continuous_subtype_val
  have hz : Continuous fun y : GR d.n => Zm d ζ y := (continuous_const.matrix_mul hm).matrix_mul continuous_const
  have hM : Continuous fun y : GR d.n => MxI d w ζ y :=
    (continuous_const.matrix_mul ((continuous_atM d w).comp hz)).matrix_mul continuous_const
  refine continuous_induced_rng.2 ?_
  refine Units.continuous_iff.2 ⟨hM, ?_⟩
  exact hM.comp continuous_inv

theorem iotaEx : IotaEx := by
  intro F E _ _ _ _ _ σ d ε ζ hε hζ
  refine ⟨iota d hε hζ, continuous_iota d hε hζ, fun w y => ?_, fun w w' y hw => ?_, fun w y => ?_⟩
  · rw [inFrame_iota, cw_atM]
    simp only [fam, if_true, Zm]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, dZ_mul_inv (zeta_ne hζ), Matrix.one_mul]
  · rw [inFrame_iota, cw_atM]
    simp only [fam, if_neg hw]
  · rw [inFrame_iota, fin_atM]

end Iota

end PositivityTheory.SiegelWeilFormula.Krd

end

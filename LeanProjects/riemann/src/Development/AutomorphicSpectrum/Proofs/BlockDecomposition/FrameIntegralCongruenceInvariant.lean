import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

theorem gramQ_mul_right (D : D7) (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E)
    (a : Matrix (Fin r) (Fin r) D.host.E) :
    gramQ V (x * a) = (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ * gramQ V x * a := by
  have hm : (x * a).map (D.sp.cm.sig : D.host.E → D.host.E) =
      x.map (D.sp.cm.sig : D.host.E → D.host.E) * a.map (D.sp.cm.sig : D.host.E → D.host.E) :=
    Matrix.map_mul (f := (D.sp.cm.sig : D.host.E →+* D.host.E))
  unfold gramQ
  rw [hm, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

def congrEquiv (D : D7) (V : HSp D) {r : ℕ} (β : HermE D r) (a : Matrix (Fin r) (Fin r) D.host.E)
    (ha : a.det ≠ 0) :
    {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1} ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = (congrH a β).1} :=
  have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
  have hi : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hu
  have hi' : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a hu
  have hu' : IsUnit (a⁻¹).det := by
    have := congrArg Matrix.det hi
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ (by rwa [mul_comm] at this)
  have hc : ((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
      (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    have hm : (a * a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E) =
        a.map (D.sp.cm.sig : D.host.E → D.host.E) * (a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E) :=
      Matrix.map_mul (f := (D.sp.cm.sig : D.host.E →+* D.host.E))
    rw [← hm, hi, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  { toFun := fun x => ⟨x.1 * a, by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det a x.1 hu]
      exact x.2.1, by
      rw [gramQ_mul_right, x.2.2]; rfl⟩
    invFun := fun x => ⟨x.1 * a⁻¹, by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det a⁻¹ x.1 hu']
      exact x.2.1, by
      rw [gramQ_mul_right, x.2.2]
      change ((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
        ((a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ * β.1 * a) * a⁻¹ = β.1
      calc _ = (((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
              (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ) * β.1 * (a * a⁻¹) := by
            simp only [Matrix.mul_assoc]
        _ = β.1 := by rw [hc, hi, Matrix.one_mul, Matrix.mul_one]⟩
    left_inv := fun x => Subtype.ext (by
      change x.1 * a * a⁻¹ = x.1
      rw [Matrix.mul_assoc, hi, Matrix.mul_one])
    right_inv := fun x => Subtype.ext (by
      change x.1 * a⁻¹ * a = x.1
      rw [Matrix.mul_assoc, hi', Matrix.mul_one]) }

theorem ifrB_congrH : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (r : ℕ) (φ : Mx D V.rank r → ℂ) (β : HermE D r)
    (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 →
    IfrB V ν φ (GlobalTheory.CompanionTheory.WeilSiegel.Deg.congrH a β) = IfrB V ν (pull a φ) β := by
  intro D V ν r φ β a ha
  have key : (fun h : GA D V => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E //
        x.rank = r ∧ gramQ V x = (congrH a β).1},
        φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) =
      (fun h : GA D V => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E //
        x.rank = r ∧ gramQ V x = β.1},
        pull a φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) := by
    funext h
    rw [← (congrEquiv D V β a ha).tsum_eq]
    refine tsum_congr fun x => ?_
    have hm : (x.1 * a).map (incA D) = HMul.hMul (x.1.map (incA D)) (a.map (incA D)) :=
      Matrix.map_mul (f := incA D)
    change φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) ((x.1 * a).map (incA D))) =
      φ (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D))) (a.map (incA D)))
    rw [hm, Matrix.mul_assoc]
  unfold IfrB
  rw [key]

end GlobalTheory.CompanionTheory.WeilSiegel.Deg

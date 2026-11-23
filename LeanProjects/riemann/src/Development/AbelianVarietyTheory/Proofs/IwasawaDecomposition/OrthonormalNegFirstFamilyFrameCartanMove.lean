import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

noncomputable section

namespace GlobalTheory.OneMapRef.Frames

open GlobalTheory.Ker.ONBasis

variable {D : D7} {T : HSp D}

theorem negM_sq (T : HSp D) (q : ℕ) : negM T q * negM T q = 1 := by
  unfold negM
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  unfold sgn
  split_ifs <;> simp

theorem negM_herm (T : HSp D) (q : ℕ) : (negM T q)ᴴ = negM T q := by
  unfold negM
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp

theorem compAt_eq (θ : InfFam D) (ρ : D.what₂.Tau) (h : GA D T) :
    compAt θ ρ (Formalism.L2.Theta.mt T h) = infMat D.sp.cm.sig T.gram (θ ρ) h := rfl

theorem compAt_unitary' {θ : InfFam D} (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (g : GA D T) :
    (compAt θ ρ (Formalism.L2.Theta.mt T g))ᴴ * gramAt D T ρ * compAt θ ρ (Formalism.L2.Theta.mt T g) = gramAt D T ρ := by
  rw [GlobalTheory.FockCompare.RealAction.gramAt_eq hθ]
  exact GlobalTheory.FockCompare.RealAction.unitary_map (cA D) ((θ ρ).comp (infPart D))
    (GlobalTheory.FockCompare.comp_cA hθ ρ) _ _ (mt_rel T g)

theorem isONeg_mvZ {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z : Fam T} (hZ : IsONeg T q Z) (g : GA D T) :
    IsONeg T q (mvZ θ g Z) := by
  intro τ
  unfold mvZ
  rw [Matrix.conjTranspose_mul, ← hZ τ]
  conv_rhs => rw [← compAt_unitary' hθ τ g]
  simp only [Matrix.mul_assoc]

theorem mvZ_mul (θ : InfFam D) (Z : Fam T) (g g' : GA D T) : mvZ θ (g' * g) Z = mvZ θ g' (mvZ θ g Z) := by
  funext τ
  unfold mvZ
  have e : Formalism.L2.Theta.mt T (g' * g) = Formalism.L2.Theta.mt T g' * Formalism.L2.Theta.mt T g := by simp [Formalism.L2.Theta.mt]
  rw [e, ← Matrix.mul_assoc]
  congr 1
  exact Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem mvZ_fin (θ : InfFam D) (Z : Fam T) {g : GA D T} (hg : g ∈ GfC T) : mvZ θ g Z = Z := by
  funext τ
  have h1 : (Formalism.L2.Theta.mt T g).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  have h2 : compAt θ τ (Formalism.L2.Theta.mt T g) = ((Formalism.L2.Theta.mt T g).map (infPart D)).map (θ τ) := rfl
  unfold mvZ
  rw [h2, h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem cartZ_mvZ {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z : Fam T} (hZ : IsONeg T q Z) (g : GA D T)
    (τ : D.what₂.Tau) :
    cartZ T q (mvZ θ g Z) τ * compAt θ τ (Formalism.L2.Theta.mt T g) = compAt θ τ (Formalism.L2.Theta.mt T g) * cartZ T q Z τ := by
  have hu' := isUnit_det (negM_sq T q) (isONeg_mvZ hθ hZ g τ)
  have e : (mvZ θ g Z τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T g) = (Z τ)⁻¹ := by
    symm
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul _ hu'
  unfold cartZ
  rw [Matrix.mul_assoc, e]
  unfold mvZ
  simp only [Matrix.mul_assoc]

theorem fin_of_mvZ {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z : Fam T} (hZ : IsONeg T q Z) {g : GA D T}
    (h : mvZ θ g Z = Z) : g ∈ GfC T := by
  refine (GlobalTheory.SmoothForms.RealPts.glue θ hθ T).1 g fun τ => ?_
  have hu := isUnit_det (negM_sq T q) (hZ τ)
  have h1 : compAt θ τ (Formalism.L2.Theta.mt T g) * Z τ = Z τ := congrFun h τ
  rw [← compAt_eq]
  calc _ = compAt θ τ (Formalism.L2.Theta.mt T g) * Z τ * (Z τ)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = 1 := by rw [h1, Matrix.mul_nonsing_inv _ hu]

theorem exists_move {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z Z' : Fam T} (hZ : IsONeg T q Z)
    (hZ' : IsONeg T q Z') : ∃ a ∈ GinfC T, Z' = mvZ θ a Z := by
  have hu := fun τ => isUnit_det (negM_sq T q) (hZ τ)
  obtain ⟨a, ha, h⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ T).2 (fun τ => Z' τ * (Z τ)⁻¹) (fun τ => by
    show (Z' τ * (Z τ)⁻¹)ᴴ * gramAt D T τ * (Z' τ * (Z τ)⁻¹) = gramAt D T τ
    have h2 := Matrix.mul_nonsing_inv _ (hu τ)
    calc _ = (Z τ)⁻¹ᴴ * ((Z' τ)ᴴ * gramAt D T τ * Z' τ) * (Z τ)⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (Z τ * (Z τ)⁻¹)ᴴ * gramAt D T τ * (Z τ * (Z τ)⁻¹) := by
          rw [hZ' τ, ← hZ τ]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one])
  refine ⟨a, ha, funext fun τ => ?_⟩
  unfold mvZ
  rw [compAt_eq, h τ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hu τ), Matrix.mul_one]

theorem isOrtho_frOf {X : Data D.host.E T.rank} (eT : D.what₂.Tau ≃ X.Ψ) (hM : ModelW T rfl X)
    (he : ∀ ρ, (eT ρ).1 = tauE D ρ) {Z : Fam T} (hZ : IsONeg T X.p0 Z) : X.IsOrtho (frOf rfl eT Z) := by
  intro σ
  obtain ⟨τ, rfl⟩ := eT.surjective σ
  have hm : mat (frOf rfl eT Z) (eT τ) = Z τ := by
    ext a b
    simp [mat, frOf]
  have hG : ∀ a b, tauE D τ (X.Gm a b) = -gramAt D T τ b a := fun a b => by
    rw [hM.1]
    simp [gramAt]
  rw [hm, he]
  ext a b
  have h1 := congrFun (congrFun (hZ τ) b) a
  have h2 : FD.gram (tauE D τ) X.Gm (Z τ) a b = -((Z τ)ᴴ * gramAt D T τ * Z τ) b a := by
    simp only [FD.gram, hermC, FD.col, Matrix.of_apply, hG, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.sum_mul, ← Finset.sum_neg_distrib, RCLike.star_def]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h2, h1, negM]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab), neg_zero]

theorem isUnitFr_of_isOrtho {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (hx : X.IsOrtho x) : IsUnitFr X x := by
  intro τ i
  unfold dmin
  have h : FD.gram τ.1 X.Gm (mat x τ) = sgnM X := hx τ
  rw [h, GlobalTheory.SW.Slab.lminor_sgnM]
  rcases GlobalTheory.SW.Slab.psgn_sq X.p0 i with h | h <;> rw [h] <;> norm_num

end GlobalTheory.OneMapRef.Frames

open GlobalTheory.OneMapRef.Frames GlobalTheory.Ker.ONBasis in

theorem GlobalTheory.OneMapRef.oneg_frames : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ Z : Fam T, IsONeg T X.p0 Z → frOf hr eT Z ∈ X.dom ∧ IsUnitFr X (frOf hr eT Z) ∧ X.IsOrtho (frOf hr eT Z) ∧ (∀ ρ, IsCartanInv (gramAt D T ρ) (cartZ T X.p0 Z ρ)) ∧ ∀ h : GA D T, IsONeg T X.p0 (mvZ θ h Z) ∧ (∀ ρ, cartZ T X.p0 (mvZ θ h Z) ρ * compAt θ ρ (Formalism.L2.Theta.mt T h) = compAt θ ρ (Formalism.L2.Theta.mt T h) * cartZ T X.p0 Z ρ) ∧ (∀ h', mvZ θ (h' * h) Z = mvZ θ h' (mvZ θ h Z)) ∧ (h ∈ GfC T → mvZ θ h Z = Z) ∧ (mvZ θ h Z = Z → h ∈ GfC T) ∧ ∀ Z', IsONeg T X.p0 Z' → ∃ a ∈ GinfC T, Z' = mvZ θ a Z := by
  intro D S T r g hr ψ θ X eT bas idx hS Z hZ
  subst hr
  obtain ⟨-, hθ, -, -, hM, -, he, -⟩ := hS
  have ho := isOrtho_frOf eT hM he hZ
  exact ⟨mem_dom X ho, isUnitFr_of_isOrtho X ho, ho,
    fun ρ => isCartanInv (negM_sq T _) (negM_herm T _) (hZ ρ),
    fun h => ⟨isONeg_mvZ hθ hZ h, cartZ_mvZ hθ hZ h, mvZ_mul θ Z h, mvZ_fin θ Z, fin_of_mvZ hθ hZ,
      fun _ hZ' => exists_move hθ hZ hZ'⟩⟩

end

import Development.WeilBound.CoreStatements.SesquilinearFractions.GLieIntA
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace PositivityTheory.Xgf.isogeny_decomposition_product

variable {R : Type} [CommRing R]

def toR {A : Over (Sp R)} (t : epsAt (𝟙 (Sp R)) ⟶ A) : epsR R ⟶ A :=
  Over.homMk t.left (by simp [Over.w t])

theorem toR_left {A : Over (Sp R)} (t : epsAt (𝟙 (Sp R)) ⟶ A) : (toR t).left = t.left := rfl

theorem toR_tan {A : Over (Sp R)} [GrpObj A] (t : epsAt (𝟙 (Sp R)) ⟶ A) (ht : IsTanAt A (𝟙 (Sp R)) t) :
    IsTangent (toR t) := by
  unfold IsTangent
  rw [toR_left]
  unfold IsTanAt at ht
  rw [ht]
  rw [Hom.one_def]; simp

theorem epsScaleR_eq (c : R) : epsScaleR c = GlobalTheory.CompanionTheory.Ar.epsMul c := rfl

theorem basis_of_lieBasis {A : Over (Sp R)} [GrpObj A] (v : epsR R ⟶ A) (hv : IsLieBasis ![v]) {E : Type}
    [AddCommGroup E] [Module R E] (M : LieModel A (𝟙 (Sp R)) E) :
    ∃ b : Module.Basis (Fin 1) R E, (M.pt (b 0)).left = v.left := by
  obtain ⟨e₀, he₀⟩ := M.onto (toAt v) (toAt_tan v (hv.1 0))
  have key : ∀ e, ∃! c : Fin 1 → R, IsLieComb c ![v] (toR (M.pt e)) :=
    fun e => hv.2 _ (toR_tan _ (M.tan e))
  have hsm : ∀ (c : R) e, (M.pt (c • e)).left = spMap (epsScaleR c) ≫ (M.pt e).left := fun c e => M.smul c e
  have comb : ∀ c : R, IsLieComb ![c] ![v] (toR (M.pt (c • e₀))) := by
    intro c
    refine ⟨![toR (M.pt (c • e₀))], fun i => ?_, ?_⟩
    · fin_cases i
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [toR_left, hsm, he₀, toAt_left]
    · simp
  have hinj : Function.Injective fun c : R => c • e₀ := by
    intro c c' h
    have h1 := (key (c • e₀)).unique (comb c) (by simpa [h] using comb c')
    simpa using congrFun h1 0
  have hsurj : Function.Surjective fun c : R => c • e₀ := by
    intro e
    obtain ⟨c, ⟨u, hu, hw⟩, -⟩ := key e
    refine ⟨c 0, M.inj (Over.OverMorphism.ext ?_)⟩
    have h0 := hu 0
    simp only [Matrix.cons_val_zero] at h0
    have hw' : (toR (M.pt e)).left = (u 0).left := by
      rw [hw]; simp [List.ofFn_succ]
    simp only
    rw [hsm, he₀, toAt_left, ← h0, ← hw', toR_left]
  let eqv : R ≃ₗ[R] E := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R E e₀) ⟨hinj, hsurj⟩
  refine ⟨(Module.Basis.singleton (Fin 1) R).map eqv, ?_⟩
  simp only [eqv, Module.Basis.map_apply, Module.Basis.singleton_apply]
  show (M.pt (LinearMap.toSpanSingleton R E e₀ 1)).left = v.left
  rw [LinearMap.toSpanSingleton_apply, one_smul, he₀, toAt_left]

end PositivityTheory.Xgf.isogeny_decomposition_product

end

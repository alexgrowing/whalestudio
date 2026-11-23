import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinDatumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFramedStratifiedCrystalBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFCrystalHomOfStratifiedPhiModuleHomStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStratifiedPhiModuleHomOfGaloisEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantLatticeMatrixOverBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeExistsBasisEqImageOfBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFramedMatricesOfEtaleRealisationStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem semilinear_square_of_basis {A B N N' Q Q' ι : Type} [CommRing A] [CommRing B] [AddCommGroup N]
    [Module A N] [AddCommGroup N'] [Module A N'] [AddCommGroup Q] [Module B Q] [AddCommGroup Q'] [Module B Q']
    {c : A →+* B} (β : Module.Basis ι A N) (w : N →ₗ[A] N') (j : N →ₛₗ[c] Q) (j' : N' →ₛₗ[c] Q')
    (G : Q →ₗ[B] Q') (h : ∀ k, j' (w (β k)) = G (j (β k))) (x : N) : j' (w x) = G (j x) :=
  LinearMap.congr_fun (β.ext (f₁ := j'.comp w) (f₂ := G.comp j) h) x

theorem sum_smul_column_eq {R B T T' : Type} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup T]
    [Module R T] [AddCommGroup T'] [Module R T'] {d d' : ℕ} (b : Module.Basis (Fin d) R T)
    (b' : Module.Basis (Fin d') R T') (f : T →ₗ[R] T') (U : Matrix (Fin d) (Fin d) B)
    (U' : Matrix (Fin d') (Fin d') B) (Y : Matrix (Fin d') (Fin d) B)
    (h : U' * Y = (LinearMap.toMatrix b b' f).map (algebraMap R B) * U) (k : Fin d) :
    ∑ i, Y i k • ∑ m, U' m i ⊗ₜ[R] b' m = f.baseChange B (∑ i, U i k ⊗ₜ[R] b i) := by
  have h1 : ∀ i, f (b i) = ∑ m, LinearMap.toMatrix b b' f m i • b' m := fun i => by
    conv_lhs => rw [← b'.sum_repr (f (b i))]
    simp only [LinearMap.toMatrix_apply]
  have h2 : ∀ m, ∑ i, Y i k * U' m i = ∑ i, LinearMap.toMatrix b b' f m i • U i k := fun m => by
    have := congrFun (congrFun h m) k
    simp only [Matrix.mul_apply, Matrix.map_apply] at this
    simp only [Algebra.smul_def, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  simp only [map_sum, LinearMap.baseChange_tmul, h1, TensorProduct.tmul_sum, Finset.smul_sum,
    TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.tmul_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← TensorProduct.sum_tmul, ← TensorProduct.sum_tmul, h2]

theorem square_column {S A B P P' N N' Q Q' κ : Type} [CommRing S] [CommRing A] [CommRing B] [AddCommGroup P]
    [Module S P] [AddCommGroup P'] [Module S P'] [AddCommGroup N]
    [Module A N] [AddCommGroup N'] [Module A N'] [AddCommGroup Q] [Module B Q] [AddCommGroup Q'] [Module B Q']
    [Fintype κ] {a : S →+* A} {c : A →+* B} (t : P →ₛₗ[a] N) (t' : P' →ₛₗ[a] N') (v : P →ₗ[S] P')
    (w : N →ₗ[A] N') (j : N →ₛₗ[c] Q) (j' : N' →ₛₗ[c] Q') (G : Q →ₗ[B] Q') (hw : ∀ x, w (t x) = t' (v x))
    {n : N} {p : P} {y : κ → S} {e : κ → P'} {q : Q} {q' : κ → Q'} (hn : n = t p) (hp : v p = ∑ i, y i • e i)
    (hq : j (t p) = q) (hq' : ∀ i, j' (t' (e i)) = q' i) (h : ∑ i, c (a (y i)) • q' i = G q) :
    j' (w n) = G (j n) := by
  rw [hn, hw, hp, hq, ← h, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [t'.map_smulₛₗ, j'.map_smulₛₗ, hq']

theorem exists_fHom_of_equivariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (T' : Type) [AddCommGroup T'] [Module ℤ_[l] T'] (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T')) (M M' : FCrys l ↥(OL K)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)) (j' : M'.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T')), Realises K M (ainfObj K) (ainfId K) T ρ j → Realises K M' (ainfObj K) (ainfId K) T' ρ' j' → ∀ f : T →ₗ[ℤ_[l]] T', (∀ g x, f (ρ g x) = ρ' g (f x)) → ∃ u : FHom M M', ∀ x, j' (u.u (ainfObj K) x) = f.lTensor (WCb l) (j x) := by
  intro l _ K T _ _ ρ T' _ _ ρ' M M' j j' H H' f hf
  obtain ⟨bk⟩ := GlobalTheory.T.nonempty_breuilKisinDatum l K
  obtain ⟨d, S, e, hS⟩ := GlobalTheory.T.exists_framedStratifiedCrystalBasis l K bk M
  obtain ⟨d', S', e', hS'⟩ := GlobalTheory.T.exists_framedStratifiedCrystalBasis l K bk M'
  obtain ⟨b, U, hU, hj⟩ := GlobalTheory.T.exists_framedMatrices_of_etaleRealisation l K bk d S M e hS T ρ j H
  obtain ⟨b', U', hU', hj'⟩ := GlobalTheory.T.exists_framedMatrices_of_etaleRealisation l K bk d' S' M' e' hS' T' ρ' j' H'
  have hF : ∀ g, LinearMap.toMatrix b b' f * LinearMap.toMatrix b b (ρ g) =
      LinearMap.toMatrix b' b' (ρ' g) * LinearMap.toMatrix b b' f := fun g => by
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    congr 1
    exact LinearMap.ext (hf g)
  obtain ⟨Y, hY⟩ := GlobalTheory.T.equivariant_latticeMatrix_over_breuilKisin l K bk d d' S S' _ _ U U' hU hU' _ hF
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_fCrystalHom_of_stratifiedPhiModuleHom l K bk d d' S S' M M' e e' hS hS' Y
    (GlobalTheory.T.isStratifiedPhiModuleHom_of_galois_equivariant l K bk d d' S S' _ _ U U' hU hU' _ hF Y hY)
  obtain ⟨β, hβ⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ (M.tr bk.ι) (M.tr_bc bk.ι) _ e
  refine ⟨u, fun x => ?_⟩
  refine semilinear_square_of_basis β (u.u (ainfObj K)) j j' (f.baseChange (WCb l)) (fun k => ?_) x
  refine square_column (M.tr bk.ι) (M'.tr bk.ι) (u.u bk.prism) (u.u (ainfObj K)) j j' (f.baseChange (WCb l))
    (u.u_tr bk.ι) (hβ k) (hu k) (hj k) hj' ?_
  exact sum_smul_column_eq b b' f U U' _ hY k

end GlobalTheory.BSP

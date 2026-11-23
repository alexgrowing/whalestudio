import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LocAddOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FockDecK

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
theorem tens_add_k (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (Ψ Ψ' : Mx F E d.m d.n → ℂ) :
    R.tens w f (Ψ + Ψ') = R.tens w f Ψ + R.tens w f Ψ' := by
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Pi.add_apply, mul_add]
theorem tens_smul_k (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (a : ℂ) (Ψ : Mx F E d.m d.n → ℂ) :
    R.tens w f (a • Ψ) = a • R.tens w f Ψ := by
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Pi.smul_apply, smul_eq_mul]
  ring
def tensL_k (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) : (Mx F E d.m d.n → ℂ) →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := R.tens w f
  map_add' := _root_.PositivityTheory.SiegelWeilFormula.KFock.tens_add_k R w f
  map_smul' a Ψ := _root_.PositivityTheory.SiegelWeilFormula.KFock.tens_smul_k R w f a Ψ
omit R in
theorem cw_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (X Z : Mx F E d.m d.n) : d.cw w (X + Z) = d.cw w X + d.cw w Z :=
  Matrix.map_add _ (map_add _) X Z
theorem loc_add_of_k (w : InfinitePlace F) (X Z : Mx F E d.m d.n) (h : d.cw w Z = 0) : R.loc w (X + Z) = R.loc w X := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.cw_add_k, h, add_zero]
omit R in
theorem crd_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X Z : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) :
    d.crd (X + Z) k = d.crd X k + d.crd Z k := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd
  rw [Matrix.add_apply, map_add, Finsupp.add_apply]
omit R in
theorem crd_fin_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Z : Mx F E d.m d.n) (h : finOne F • Z = 0) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd Z k).2 = 0 := by
  have e1 : d.crd (finOne F • Z) k = finOne F * d.crd Z k := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd
    rw [Matrix.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have e2 : d.crd (finOne F • Z) k = 0 := by
    rw [h]
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd
    rw [Matrix.zero_apply, map_zero, Finsupp.zero_apply]
  have e3 : (finOne F * d.crd Z k).2 = (d.crd Z k).2 := by
    show (finOne F).2 * (d.crd Z k).2 = _
    rw [show (finOne F).2 = 1 from rfl, one_mul]
  rw [← e3, ← e1, e2]
  rfl
theorem away_inv_k (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) :
    ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X := by
  intro X Z hZ hf
  induction hΨ using Submodule.span_induction generalizing X with
  | mem x hx =>
    obtain ⟨P, g, -, rfl⟩ := hx
    have e1 : ∀ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' (X + Z)) = fP (P w') (R.loc w' X) := fun w' hw' => by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_add_of_k R w' X Z (hZ w' (Finset.ne_of_mem_erase hw'))]
    have e2 : (fun k => (d.crd (X + Z) k).2) = fun k => (d.crd X k).2 := by
      funext k
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_add_k]
      show (d.crd X k).2 + (d.crd Z k).2 = _
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_fin_k d Z hf k, add_zero]
    show (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' (X + Z))) * g (fun k => (d.crd (X + Z) k).2) =
      (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g (fun k => (d.crd X k).2)
    rw [Finset.prod_congr rfl e1, e2]
  | zero => rfl
  | add x y _ _ hx hy => simp only [Pi.add_apply, hx, hy]
  | smul a x _ hx => simp only [Pi.smul_apply, hx]
theorem away_tens_k (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) (P : PX d.m d.n) :
    R.tens w (fP P) Ψ ∈ R.fock := by
  have h : R.away w ≤ R.fock.comap (_root_.PositivityTheory.SiegelWeilFormula.KFock.tensL_k R w (fP P)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨P', g, hg, rfl⟩
    refine Submodule.subset_span ⟨Function.update P' w P, g, hg, ?_⟩
    funext X
    show fP P (R.loc w X) * ((∏ w' ∈ Finset.univ.erase w, fP (P' w') (R.loc w' X)) * g fun k => (d.crd X k).2) =
      (∏ w', fP (Function.update P' w P w') (R.loc w' X)) * g fun k => (d.crd X k).2
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self, mul_assoc]
    congr 2
    exact Finset.prod_congr rfl fun w' hw' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]
  exact h hΨ
theorem fock_dec_k (w : InfinitePlace F) (f : Mx F E d.m d.n → ℂ) (hf : f ∈ R.fock) :
    ∃ (k : ℕ) (P : Fin k → PX d.m d.n) (Ψ : Fin k → Mx F E d.m d.n → ℂ),
      (∀ i, Ψ i ∈ R.away w) ∧ f = ∑ i, R.tens w (fP (P i)) (Ψ i) :=
  by apply _root_.UpperTheory.Reformulated.B.Glb2.fock_dec_k <;> assumption
omit R in
theorem T_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ Φ' : d.Fn) : d.T (Φ + Φ') = d.T Φ + d.T Φ' := by
  funext X
  show d.l (d.dd.rho d.B.ψ _ (Φ + Φ')) = d.l (d.dd.rho d.B.ψ _ Φ) + d.l (d.dd.rho d.B.ψ _ Φ')
  rw [← map_add]
  congr 1
  funext x
  simp only [Darboux.rho, schr, Pi.add_apply, mul_add]
omit R in
theorem T_smul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (a : ℂ) (Φ : d.Fn) : d.T (a • Φ) = a • d.T Φ := by
  funext X
  show d.l (d.dd.rho d.B.ψ _ (a • Φ)) = a • d.l (d.dd.rho d.B.ψ _ Φ)
  rw [← map_smul]
  congr 1
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring
end PositivityTheory.SiegelWeilFormula.KFock
end
end

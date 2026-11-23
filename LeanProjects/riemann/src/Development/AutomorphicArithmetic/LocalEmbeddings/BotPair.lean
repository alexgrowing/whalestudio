import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.BotPure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.Grid (sgn)

noncomputable section

namespace GlobalTheory.BotMatch

open GlobalTheory.LatVac (liftV)
open GlobalTheory.RealDict.FockMap

variable {D : D7}

def mapO (S T : HSp D) : Matrix (Fin S.rank) (Fin T.rank) (AE D) ≃ₗ[AE D] WO S T where
  toFun := toO S.gram
  invFun := GlobalTheory.TripleRead.ptO S.gram (Equiv.refl _)
  left_inv := ptO_toO (Formalism.L2.Theta.gram_det_ne S).isUnit
  right_inv := toO_ptO (Formalism.L2.Theta.gram_det_ne S).isUnit
  map_add' u v := by simp only [toO, transpose_add, Matrix.add_mul]
  map_smul' c u := by simp only [toO, transpose_smul, Matrix.smul_mul, RingHom.id_apply]

theorem localLattice_le_latticeAtPlace {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {Xs : Spc D.host.F D.host.E S.rank} {Ws : Spc D.host.F D.host.E T.rank}
    (hLS : ∀ s ∈ ΛS, star s ∈ Xs.L) (hLT : ∀ y ∈ GlobalTheory.SkewLat.scLat D.host.AA ΛT, y ∈ Ws.L) (v : Pl D.host.F) :
    ∀ u ∈ lattice₂ (mapO S T) (latA ΛS ΛT) v, u ∈ latAtV Xs Ws v := by
  intro u hu
  have e : u = liftV v (1 : Fv D.host.F v) • (mapO S T).symm (mapO S T u) := by
    rw [LinearEquiv.symm_apply_apply, GlobalTheory.BigDatLat.smul_eq_of_at hu.1]
  rw [e]
  refine GlobalTheory.BigDat.map_mem_of_closure ((DistribMulAction.toAddMonoidHom _ (liftV v (1 : Fv D.host.F v))).comp
    (mapO S T).symm.toLinearMap.toAddMonoidHom) ?_ hu.2
  rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
  have e2 : (mapO S T).symm (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) (a • t)) := by
    ext p q
    refine (GlobalTheory.BigDat.divG_gen S (pairA D.host.F 0 α) a s t q p).trans ?_
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, mul_comm]
    rfl
  exact (congrArg (fun z => liftV v (1 : Fv D.host.F v) • z ∈ latAtV Xs Ws v) e2).mpr
    (GlobalTheory.BigDat.one_smul_gen_mem _ _ v hα (hLS s hs) (hLT _ (GlobalTheory.BigDat.smul_mem_scLat_of_mem ha ht)))

set_option maxHeartbeats 800000 in

theorem exists_pure_pair (ε : Bool) (M X : HSp D) {k : ℕ} (hk : k = X.rank) {Xs : Spc D.host.F D.host.E M.rank}
    {Ws : Spc D.host.F D.host.E k} (Mo : Model D.sp.cm.sig Xs Ws) (hJ : Xs.J = GlobalTheory.RealDict.sgE (D := D) ε • M.gram)
    (hJW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (finCongr hk) (finCongr hk))
    {ΛS : Submodule (𝓞 D.host.E) (Fin M.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)}
    (hS : IsSelfDualC (sgn ε M) ΛS) (hT : IsSelfDualC X ΛT) {Bs : Base D.host.F D.host.E}
    (hψ : IsStdChar D Bs.ψ (-1)) (hBs : Bs.IsGood D.sp.cm.sig) {r s r' s' : ℕ}
    (hX : Xs.IsHerm D.sp.cm.sig Bs r s) (hW : Ws.IsSkew D.sp.cm.sig Bs r' s') (hM : Mo.IsGood Bs.ψ)
    (hLS : ∀ s ∈ ΛS, star s ∈ Xs.L)
    (hLT : ∀ y : Fin k → D.host.E, (fun a => y ((finCongr hk).symm a)) ∈ GlobalTheory.SkewLat.scLat D.host.AA ΛT → y ∈ Ws.L)
    {θ : InfFam D} (hθ : IsInfFam θ) {vac : WO (sgn ε M) X → ℂ} (hth : IsThetaFunO Bs.ψ (sgn ε M) X vac) (hv0 : vac ≠ 0)
    (hv : IsLatVac (heisO Bs.ψ (sgn ε M) X) (latA (S := sgn ε M) ΛS ΛT) vac)
    {ι : Type} [Fintype ι] (pl : ι → Pl D.host.F) (hpl : Function.Injective pl) (a : ι → AE D)
    (ha : ∀ i, IsSplitIdem D (a i) ∧ a i + cA D (a i) = algebraMap (AF D.host.F) (AE D) (liftV (pl i) 1))
    {η : AE D} (hη : η = ∑ i, a i) (Z : ι → Type) [∀ i, TopologicalSpace (Z i)] [∀ i, AddCommGroup (Z i)]
    (A A' : ι → Set (Matrix (Fin M.rank) (Fin k) (AE D))) (hA : ∀ i u, u ∈ A i ↔ IsHalf (a i) u)
    (hA' : ∀ i u, u ∈ A' i ↔ IsHalf (cA D (a i)) u) (co : ∀ i, Matrix (Fin M.rank) (Fin k) (AE D) → Z i)
    (hco : ∀ i u x, co i (u + x) = co i u + co i x) (hcoa : ∀ i u, co i (a i • u) = co i u)
    (hcos : ∀ i z, ∃ x, co i x = z) (I : ∀ i, ((Fin M.rank × Fin k → Fv D.host.F (pl i)) → ℂ) →ₗ[ℂ] (Z i → ℂ))
    (hI : ∀ i, IsLagrModel Mo Bs.ψ (pl i) (A i) (A' i) (co i) (I i)) {Φ f : WO (sgn ε M) X → ℂ}
    (hf : IsThetaAt Bs.ψ (symplO (sgn ε M) X) (heisO Bs.ψ (sgn ε M) X) η (latA (S := sgn ε M) ΛS ΛT) 1 vac Φ f)
    (hΦ : ∀ x, Φ x ≠ 0 → IsHalf η x)
    (φ : ∀ v : Pl D.host.F, (Fin M.rank × Fin k → Fv D.host.F v) → ℂ) (hφ : ∀ v, φ v ∈ SB _)
    (hφv : ∀ v, (∀ i, pl i ≠ v) → φ v = Mo.vac v) {κ : ℂ} (hκ : κ ≠ 0)
    (hloc : ∀ x, IsHalf η x →
      ∏ i, I i (φ (pl i)) (co i (GlobalTheory.TripleRead.ptO (sgn ε M).gram (finCongr hk) x)) = κ * Φ x) :
    ∃ f₀, f₀ ≠ 0 ∧ GlobalTheory.TripleRead.thO Mo Bs.ψ (sgn ε M).gram (finCongr hk) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) = f := by
  subst hk
  obtain ⟨t1, -, t3, t4, -⟩ := th_laws Mo hψ hθ hJ hJW hM
  obtain ⟨co', hco'⟩ := exists_co Mo hJ hJW
  have hB : ∀ x y, sy Xs Ws x y = symplO (sgn ε M) X (mapO (sgn ε M) X x) (mapO (sgn ε M) X y) := fun x y => by
    rw [GlobalTheory.ThetaTransform.symplO_eq_symp (ξ := 1) rfl (one_smul _ _), co'.form, hco', hco']
    refine (Mo.co.form x y).trans ?_
    have h1 := (mapO (sgn ε M) X).symm_apply_apply x
    have h2 := (mapO (sgn ε M) X).symm_apply_apply y
    exact congrArg₂ (fun x y => (Mo.co.e x).1 ⬝ᵥ (Mo.co.e y).2 - (Mo.co.e y).1 ⬝ᵥ (Mo.co.e x).2) h1.symm h2.symm
  exact exists_pure (mapO (sgn ε M) X) Mo hS hT hψ hBs hX hW hM hB (localLattice_le_latticeAtPlace hLS hLT) t1 t3 ((t4 vac).1 hth) hv0 hv
    pl hpl a ha hη Z A A' hA hA' co hco hcoa hcos I hI hf hΦ φ hφ hφv hκ hloc

end GlobalTheory.BotMatch

end

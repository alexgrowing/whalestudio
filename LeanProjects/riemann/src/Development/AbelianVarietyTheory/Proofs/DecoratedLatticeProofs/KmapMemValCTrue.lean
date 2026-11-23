import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BuiltCols
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetStepEqZeroExample
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainComplexFormsStabiliserLaw
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Core.Rk
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Rk.ValLaw

open Formalism.L2.Ker
open GlobalTheory.GO.ChSrc (trueWt nuEnd sS sD polFn fnPol)
open Formalism.L2.Forms (fnOf shiftOf ValC CSpan)

variable {X : Fields} {R : Ranks}

theorem fnOf_one_apply {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : Formalism.L2.Forms.Frames G) :
    fnOf G s 1 P y = (∏ τ, (y.1 τ).det ^ s τ) * MvPolynomial.eval (fun x => y.1 x.1 x.2.1 x.2.2) P := by
  simp [fnOf]

theorem jetMap_mem_VV (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m)
    (J : (DVar X.Tau (R.N i) (R.N (i + 1)) →₀ ℕ) → ℂ) (P : Pol ℂ X.Tau (R.N i)) (hP : P ∈ VV ℂ (trueWt hc i)) :
    jetMap J (nuEnd hc i) P ∈ VV ℂ (trueWt hc (i + 1)) := by
  have hN : R.N i < R.N (i + 1) := by unfold Ranks.N; rw [add_mul]; omega
  refine GlobalTheory.JetPoint.jetMap_mem hN.le _ _ _ (fun ap => ?_) J
  refine GlobalTheory.SubstMem.substAdj_sharp_mem ℂ X.Tau _ _ hN _ _ (sD hc i) (sS hc i) _
    ⟨fun τ a => ?_, fun τ j hj => GlobalTheory.GO.ChSrc.trueWt_new hc hi τ j (not_lt.mpr hj), GlobalTheory.GO.ChSrc.nuEnd_cast hc hi⟩ ap _ hP
  have := GlobalTheory.GO.ChSrc.trueWt_old hc hi τ (Fin.castLE hN.le a) a.2
  simp only [Fin.val_castLE, Fin.eta] at this
  omega

theorem jetMap_zero_mul {ι : Type} [Fintype ι] {a b : ℕ} (J : (DVar ι a b →₀ ℕ) → ℂ) (n : ι → ℕ) (P : Pol ℂ ι a) :
    jetMap J 0 (P * ∏ τ, frDet ℂ a τ ^ n τ) = jetMap J n P := by
  simp [jetMap]

end GlobalTheory.Core.Rk.ValLaw

namespace GlobalTheory.Core.Rk.ValLaw

open Formalism.L2.Ker
open GlobalTheory.GO.ChSrc (trueWt nuEnd sS sD polFn fnPol)
open Formalism.L2.Forms (fnOf shiftOf ValC CSpan)

variable {X : Fields} {R : Ranks}

theorem kmap_mem_valC (I : ChainIn X.E X.K X.Tau R) (σ : X.K →+* ℂ) (h : I.Ok) (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m)
    (c : (I.S i).Cl) (c' : (I.S (i + 1)).Cl) (J : (DVar X.Tau (R.N i) (R.N (i + 1)) →₀ ℕ) → ℂ) (hJ : I.jet i c c' = jetMap J 0)
    (f : Fr X.emb σ (R.N i) → ℂ) (hf : f ∈ ValC (Gr X.emb σ (R.N i)) (trueWt hc i)) :
    (I.chain X.emb σ h hc).Kmap i c c' f ∈ ValC (Gr X.emb σ (R.N (i + 1))) (trueWt hc (i + 1)) := by
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.1 hf
  rw [GlobalTheory.Pdv.FormsStd.cSpan_eq_VV] at hP
  have h1 : (I.chain X.emb σ h hc).sharp i (fnOf (Gr X.emb σ (R.N i)) (shiftOf (trueWt hc i)) 1 P) =
      polFn X σ _ (P * ∏ τ, frDet ℂ (R.N i) τ ^ nuEnd hc i τ) := by
    funext (y : Fr X.emb σ (R.N i))
    have hd : ∀ τ, MvPolynomial.eval (fun v : X.Tau × Fin (R.N i) × Fin (R.N i) => y.1 v.1 v.2.1 v.2.2)
        (frDet ℂ (R.N i) τ) = (y.1 τ).det := fun τ => by
      rw [frDet, RingHom.map_det]
      congr 1
      ext a b
      simp
    show (∏ τ, (y.1 τ).det ^ (I.chain X.emb σ h hc).sSharp i τ) * fnOf (Gr X.emb σ (R.N i)) (shiftOf (trueWt hc i)) 1 P y = _
    rw [GlobalTheory.GO.ChSrc.polFn_apply, MvPolynomial.eval_mul, MvPolynomial.eval_prod, fnOf_one_apply, ← mul_assoc,
      ← Finset.prod_mul_distrib, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [MvPolynomial.eval_pow, hd, ← zpow_natCast, GlobalTheory.GO.ChSrc.nuEnd_cast hc hi, zpow_add₀ (isUnit_det_fr y τ).ne_zero,
      (GlobalTheory.LvT.Built.KMap.sSharp_eq I σ h hc hi τ).1, mul_comm]
    rfl
  refine Submodule.mem_map.2 ⟨(I.rho i c * I.rho' i c') • jetMap J (nuEnd hc i) P, ?_, ?_⟩
  · rw [GlobalTheory.Pdv.FormsStd.cSpan_eq_VV]
    exact Submodule.smul_mem _ _ (jetMap_mem_VV hc hi J P hP)
  funext (y : Fr X.emb σ (R.N (i + 1)))
  show _ = (I.rho i c * I.rho' i c') * ((∏ τ, (y.1 τ).det ^ (I.chain X.emb σ h hc).sDiv i τ)⁻¹ *
    polFn X σ _ (I.jet i c c' (fnPol X σ _ ((I.chain X.emb σ h hc).sharp i (fnOf (Gr X.emb σ (R.N i)) (shiftOf (trueWt hc i)) 1 P)))) y)
  rw [h1, GlobalTheory.GO.ChSrc.fnPol_polFn, hJ, jetMap_zero_mul, map_smul, Pi.smul_apply, smul_eq_mul, fnOf_one_apply,
    GlobalTheory.GO.ChSrc.polFn_apply]
  congr 1
  congr 1
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [(GlobalTheory.LvT.Built.KMap.sSharp_eq I σ h hc hi τ).2, ← zpow_neg, ← GlobalTheory.GO.ChSrc.trueWt_detShift_succ hc hi]
  rfl

end GlobalTheory.Core.Rk.ValLaw

namespace GlobalTheory.Core.Rk

end GlobalTheory.Core.Rk

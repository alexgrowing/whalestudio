import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SameCosetOfMemCosetIn
import Formalism.LocalToGlobal.Columns.ChainTwTop
import Formalism.LocalToGlobal.Columns.ChainOneP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizerFormValueStepStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms

noncomputable section

namespace GlobalTheory.AdForm.Keep

section Local

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2
open scoped Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {u : Pr.Word}

theorem res_of_xiAt {n : ℕ} (h : n + 2 = R.m) (hs : cst.sharp = true) (hh : ∀ (al : L.β n) P, P.1 ∈ Pr.vGs → L.h n al P = 1)
    {b : Idx sel mu L n} {b' : Idx sel mu L (n + 1)} {p : PtAt R sel mu cst u n} {p' : PtAt R sel mu cst u (n + 1)}
    (hx : xiAt Ch sel mu cst L u n b b' p p' ≠ 0) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (l : Fin (R.N (n + 1))) :
    IntAt P.1 ((qOf P.1 : X.E) * (frsF sel mu p'.1.1 P).symm (repY p'.1.2) l) ∧
      redP P.1 ((qOf P.1 : X.E) * (frsF sel mu p'.1.1 P).symm (repY p'.1.2) l) = if l.1 = R.k then 1 else 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hx
  rw [xiAt_penultimate_eq_xiCpl1 Ch sel mu cst L h (b.some_get (by omega)).symm] at hx
  have h1 := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) P (Finset.mem_univ _)
  rw [hh _ P hP] at h1
  exact oneYbSym_of_m Ch sel mu cst h.symm hs P hP _ _ h1 l

end Local

section True

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC
open scoped Classical
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem reference_tuple_off_primes_empty : twQOff (Pr := B.primes X) I.sel (I.tup I.mu0) = ∅ := by
  have h := I.twistPrimes_reference_tuple_eq_empty
  unfold ColIn.Q at h
  unfold twQOff
  rw [h]
  exact Finset.empty_sdiff _

theorem idx_eq (ht : I.IsTw) (i : ℕ) (b b' : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i) : b = b' := by
  by_cases hi : i < B.R.m
  · have e : ∀ al al' : (I.idx I.mu0).β i, al = al' := by
      rw [(ht I.mu0).2]
      exact twSt_subsingleton reference_tuple_off_primes_empty i
    rw [← b.of_get hi hi, ← b'.of_get hi hi, e (b.get hi) (b'.get hi)]
  · rw [b.eq_top (not_lt.1 hi), b'.eq_top (not_lt.1 hi)]

open GlobalTheory.GO.ChSrc (trueWt nuEnd sS sD polFn fnPol) in
open Formalism.L2.Forms (fnOf shiftOf ValC) in

theorem kmap_mem_valC {X : Fields} {R : Ranks} (I : ChainIn X.E X.K X.Tau R) (σ : X.K →+* ℂ) (h : I.Ok) (hc : X.Tau → HCParam R) {i : ℕ}
    (hi : i < R.m) (c : (I.S i).Cl) (c' : (I.S (i + 1)).Cl) (J : (DVar X.Tau (R.N i) (R.N (i + 1)) →₀ ℕ) → ℂ)
    (e : I.jet i c c' = jetMap J 0) (f : Fr X.emb σ (R.N i) → ℂ) (hf : f ∈ ValC (Gr X.emb σ (R.N i)) (trueWt hc i)) :
    (I.chain X.emb σ h hc).Kmap i c c' f ∈ ValC (Gr X.emb σ (R.N (i + 1))) (trueWt hc (i + 1)) := by
  obtain ⟨P, hP, rfl⟩ := hf
  rw [ValTie.cspan_eq] at hP
  have hN : R.N i < R.N (i + 1) := by unfold Ranks.N; rw [add_mul]; omega
  have hV : jetMap J (nuEnd hc i) P ∈ Formalism.L2.DIV.VV ℂ (trueWt hc (i + 1)) := by
    refine GlobalTheory.JetPoint.jetMap_mem hN.le _ _ _ (fun ap => ?_) J
    refine GlobalTheory.SubstMem.substAdj_sharp_mem ℂ X.Tau _ _ hN _ _ (sD hc i) (sS hc i) _
      ⟨fun τ a => ?_, fun τ j hj => GlobalTheory.GO.ChSrc.trueWt_new hc hi τ j (not_lt.mpr hj), GlobalTheory.GO.ChSrc.nuEnd_cast hc hi⟩ ap _ hP
    have := GlobalTheory.GO.ChSrc.trueWt_old hc hi τ (Fin.castLE hN.le a) a.2
    simp only [Fin.val_castLE, Fin.eta] at this
    omega
  have ap : ∀ {n : ℕ} (s : X.Tau → ℤ) (Q : Formalism.L2.DIV.Pol ℂ X.Tau n) (y : Fr X.emb σ n),
      fnOf (Gr X.emb σ n) s 1 Q y = (∏ τ, (y.1 τ).det ^ s τ) * MvPolynomial.eval (fun v => y.1 v.1 v.2.1 v.2.2) Q := by
    intro n s Q y
    simp [fnOf]
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
    rw [ap, GlobalTheory.GO.ChSrc.polFn_apply, map_mul, map_prod, ← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, hd, ← zpow_natCast, GlobalTheory.GO.ChSrc.nuEnd_cast hc hi, zpow_add₀ (isUnit_det_fr y τ).ne_zero,
      (GlobalTheory.LvT.Built.KMap.sSharp_eq I σ h hc hi τ).1, mul_comm]
    rfl
  have h2 : jetMap J 0 (P * ∏ τ, frDet ℂ (R.N i) τ ^ nuEnd hc i τ) = jetMap J (nuEnd hc i) P := by
    simp [jetMap]
  refine ⟨(I.rho i c * I.rho' i c') • jetMap J (nuEnd hc i) P, ?_, ?_⟩
  · rw [ValTie.cspan_eq]
    exact Submodule.smul_mem _ _ hV
  funext (y : Fr X.emb σ (R.N (i + 1)))
  show _ = (I.rho i c * I.rho' i c') * ((∏ τ, (y.1 τ).det ^ (I.chain X.emb σ h hc).sDiv i τ)⁻¹ *
    polFn X σ _ (I.jet i c c' (fnPol X σ _ ((I.chain X.emb σ h hc).sharp i
      (fnOf (Gr X.emb σ (R.N i)) (shiftOf (trueWt hc i)) 1 P)))) y)
  rw [h1, GlobalTheory.GO.ChSrc.fnPol_polFn, e, h2, ap, MvPolynomial.smul_eval, GlobalTheory.GO.ChSrc.polFn_apply, mul_left_comm,
    ← Finset.prod_inv_distrib]
  congr 2
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [(GlobalTheory.LvT.Built.KMap.sSharp_eq I σ h hc hi τ).2, ← zpow_neg, ← GlobalTheory.GO.ChSrc.trueWt_detShift_succ hc hi]
  rfl

theorem kmap_val (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) (f : Fr B.fields.emb B.embLL (B.R.N i) → ℂ)
    (hf : f ∈ Formalism.L2.Forms.ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i)) :
    (I.chain l u a).Kmap i c c' f ∈ Formalism.L2.Forms.ValC (Gr B.fields.emb B.embLL (B.R.N (i + 1))) (lamT (B.hcW u) (i + 1)) :=
  kmap_mem_valC (X := B.fields) (I.chIn u a) B.embLL (l.ch u a) (B.hcW u) hi c c' _ rfl f hf

theorem K_mem_Fi (I : TC B X) (h : I.Ok) (hP : TC.Pins B X) (ht : I.IsTw) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (i : ℕ)
    (hi : i < B.R.m) : ∀ φ ∈ (I.stp u I.mu0 i).Fi B.fields.emb B.embLL (lamT (B.hcW u) i),
      (I.chain l u I.mu0).K i φ ∈ (I.stp u I.mu0 (i + 1)).Fi B.fields.emb B.embLL (lamT (B.hcW u) (i + 1)) := by
  intro φ hφ c'
  let _ := (I.chain l u I.mu0).clsFin i
  have hK : (I.chain l u I.mu0).K i φ c' = ∑ c, (I.chain l u I.mu0).wt i c • (I.chain l u I.mu0).Kmap i c c' (φ c) := rfl
  rw [hK]
  refine ⟨Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (kmap_val I l u I.mu0 i hi c c' _ (hφ c).1), fun g => ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, GlobalTheory.T.stabilizer_form_value_step I h hP ht l Z u i hi c c' g _ (hφ c).1]

end True

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.AdForm.Keep

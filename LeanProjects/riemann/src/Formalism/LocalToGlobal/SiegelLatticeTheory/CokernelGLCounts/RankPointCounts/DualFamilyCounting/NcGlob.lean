import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcArithG
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.HasProdFiniteSupport

noncomputable section

open Classical

namespace Formalism.L2.SG.Pf.NcGlob

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField
  Formalism.L2.SG.Pf.HasProdFiniteSupport Formalism.L2.SG.Pf.NcVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {D : D7} (X : HidaSetting D)

def fac (i : ℕ) (v : PlX X) : ℝ :=
  1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i

def tf (k t : ℕ) (v : PlX X) : ℝ :=
  if ((t : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal then fac X k v else 1

theorem absNorm_gt_one (v : PlX X) : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.2 v.isPrime.ne_top
  have : 1 < Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast this

theorem fac_pos (i : ℕ) (hi : 1 ≤ i) (v : PlX X) : 0 < fac X i v := by
  unfold fac
  have hq := absNorm_gt_one X v
  have hq0 : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by linarith
  have habs : |((etaV (E := X.B.I.E) v : ℤ) : ℝ)| = 1 := by
    unfold etaV; split_ifs <;> simp
  have hη : ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i ≤ 1 := by
    calc ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i ≤ |((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i| := le_abs_self _
      _ = 1 := by rw [abs_pow, habs, one_pow]
  have hqi : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i := one_lt_pow₀ hq (by omega)
  have : ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i < 1 :=
    (div_lt_one (by positivity)).mpr (lt_of_le_of_lt hη hqi)
  linarith

theorem tf_pos (k t : ℕ) (hk : 1 ≤ k) (v : PlX X) : 0 < tf X k t v := by
  unfold tf; split_ifs
  · exact fac_pos X k hk v
  · exact one_pos

theorem aP_split (k N t : ℕ) (hk : k + 1 ≤ N) (v : PlX X) :
    aP (E := X.B.I.E) v k N t = (∏ i ∈ Finset.Icc (k + 1) N, fac X i v) * tf X k t v := by
  unfold aP tf
  by_cases ht : ((t : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal
  · rw [if_pos ht, if_pos ht, Finset.Icc_eq_cons_Ioc (show k ≤ N by omega), Finset.prod_cons]
    have hIo : Finset.Ioc k N = Finset.Icc (k + 1) N := by
      ext i; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hIo, mul_comm]
    rfl
  · rw [if_neg ht, if_neg ht, mul_one]
    rfl

theorem aPlus_pos (k N t : ℕ) (hk : 1 ≤ k) (v : PlX X) : 0 < aP (E := X.B.I.E) v k N t := by
  unfold aP
  apply Finset.prod_pos
  intro i hi
  have : 1 ≤ i := by
    simp only [Finset.mem_Icc] at hi
    split_ifs at hi <;> omega
  exact fac_pos X i this v

theorem finite_dvd (t : ℕ) (ht : t ≠ 0) :
    {v : PlX X | ((t : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((t : ℕ) : 𝓞 X.B.I.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast ht
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  exact Ideal.dvd_span_singleton.mpr hv

theorem absV_nonneg (v : PlX X) : 0 ≤ absV v (dV v) := by
  unfold absV; split_ifs
  · exact le_rfl
  · positivity

end Loc

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem normalizing_arithmetic_holds : NcArith := by
  intro D X hb hK FdN FdN' u u' X0 ψ τ Rw I H H₁ i1 i2 i3 i4 i5 T sd C Th F0 what₂ vR Q M δ i0 i0' νq a'
    ha hRR hS hR hχ hstd hcong hVo hVt hIx hOm hDP hRMp hFD hPC hP
  obtain ⟨hd, hfc, hEul, hTfac, hvI, hfE, hn, htδ, htaP, hgprod⟩ := hFD
  obtain ⟨hKc, hFc, -⟩ := Formalism.L2.SG.Pf.Cnt.field_dictionary_holds D
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hm : D.R.m = 2 * (D.R.rS + 1) := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hr : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
    show D.R.k + D.R.m - 1 = D.R.k + 2 * D.R.rS + 1
    omega

  have hLpos : ∀ i, 2 ≤ i → 0 < Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i := by
    intro i hi
    rw [← Formalism.HermitianLattices.Ext.L3.lValEta_eq_lValEtaF hKc hFc i hi]
    exact Formalism.HermitianLattices.Ext.L3.lValEta_pos hKc i hi
  set PiL : ℝ := ∏ i ∈ Finset.Icc (D.R.k + 1) D.R.r, Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i with hPiL
  have hPiLpos : 0 < PiL := by
    apply Finset.prod_pos
    intro i hi
    exact hLpos i (by simp only [Finset.mem_Icc] at hi; omega)
  have hfacHP : HasProd (fun v : PlX X => ∏ i ∈ Finset.Icc (D.R.k + 1) D.R.r, fac X i v) PiL⁻¹ := by
    rw [hPiL, ← Finset.prod_inv_distrib]
    apply hasProd_prod
    intro i hi
    have hi2 : 2 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
    have h1 := hasProd_inv₀' (hEul i hi2) (hLpos i hi2).ne'
    convert h1 using 1
    funext v
    simp only [fac, inv_inv]

  set PT : ℝ := ∏' 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal},
      (if (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ 𝔭.1 then
        1 - Formalism.HermitianLattices.Ext.L3.etaF D.host.E D.host.F 𝔭.1 ^ D.R.k * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(D.R.k : ℤ)) else 1)
    with hPT
  have hTHP : HasProd (tf X D.R.k (Tw u)) PT := by
    convert hTfac using 1
    funext v
    simp only [tf, fac, Tw]
    by_cases hv : (((D.mem u).A.T : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal <;> simp [hv]
  have hT0 : (Tw u) ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have hT0' : (Tw u') ≠ 0 := (D.mem u').A.T_prime.ne_zero
  have hSf := finite_dvd X (Tw u) hT0
  have hSf' := finite_dvd X (Tw u') hT0'
  have hTHPf : HasProd (tf X D.R.k (Tw u)) (∏ v ∈ hSf.toFinset, tf X D.R.k (Tw u) v) :=
    hasProd_of_finite_support _ hSf (fun v hv => by simp only [tf, Set.mem_ofPred_eq] at hv ⊢; rw [if_neg hv])
  have hTHP' : HasProd (tf X D.R.k (Tw u')) (∏ v ∈ hSf'.toFinset, tf X D.R.k (Tw u') v) :=
    hasProd_of_finite_support _ hSf' (fun v hv => by simp only [tf, Set.mem_ofPred_eq] at hv ⊢; rw [if_neg hv])
  have hPTpos : 0 < PT := by
    rw [hTHP.unique hTHPf]
    exact Finset.prod_pos fun v _ => tf_pos X D.R.k (Tw u) (by omega) v
  set PT' : ℝ := ∏ v ∈ hSf'.toFinset, tf X D.R.k (Tw u') v with hPT'
  have hPT'pos : 0 < PT' := Finset.prod_pos fun v _ => tf_pos X D.R.k (Tw u') (by omega) v

  have hn' : X.B.I.n = D.R.r := hn
  have hsplit : ∀ t v, aP (E := X.B.I.E) v D.R.k X.B.I.n t =
      (∏ i ∈ Finset.Icc (D.R.k + 1) D.R.r, fac X i v) * tf X D.R.k t v := by
    intro t v
    rw [aP_split X D.R.k X.B.I.n t (by omega) v, hn']
  set AT : ℝ := PiL⁻¹ * PT with hAT
  set A' : ℝ := PiL⁻¹ * PT' with hA'
  have hATHP : HasProd (fun v : PlX X => aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u)) AT := by
    have := hfacHP.mul hTHP
    convert this using 1
    funext v
    exact hsplit _ v
  have hA'HP : HasProd (fun v : PlX X => aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u')) A' := by
    have := hfacHP.mul hTHP'
    convert this using 1
    funext v
    exact hsplit _ v
  have hATpos : 0 < AT := mul_pos (inv_pos.mpr hPiLpos) hPTpos
  have hA'pos : 0 < A' := mul_pos (inv_pos.mpr hPiLpos) hPT'pos
  set ATyp : ℝ := ∏ p : TypX X, aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u) with hATyp
  have hATyppos : 0 < ATyp := Finset.prod_pos fun p _ => aPlus_pos X D.R.k X.B.I.n (Tw u) (by omega) p.1

  have hG5 : AT * PiL = PT := by rw [hAT]; field_simp

  have hal_def : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).al =
      (∏ p : TypX X, alX X u u' p.1) * ∏' v : OrdX X, alX X u u' v.1 := rfl
  have halT : ∀ v : PlX X, TypAt X v → alX X u u' v = aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u) := by
    intro v hv; unfold alX; rw [if_pos hv]
  have halO : ∀ v : PlX X, ¬ TypAt X v → alX X u u' v =
      aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u) * aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u') := by
    intro v hv; unfold alX; rw [if_neg hv]
  have hordHP := hasProd_compl_of' (typSet X.B.I.F (D.host.g 0) (D.host.g 1)) (hATHP.mul hA'HP)
    (fun v _ => (mul_pos (aPlus_pos X D.R.k X.B.I.n (Tw u) (by omega) v)
      (aPlus_pos X D.R.k X.B.I.n (Tw u') (by omega) v)).ne')
  have hord : ∏' v : OrdX X, alX X u u' v.1 = AT * A' *
      (∏ i : TypX X, (aP (E := X.B.I.E) i.1 D.R.k X.B.I.n (Tw u) *
        aP (E := X.B.I.E) i.1 D.R.k X.B.I.n (Tw u')))⁻¹ := by
    rw [← hordHP.tprod_eq]
    exact tprod_congr (fun v => halO v.1 v.2)
  have hTypProd : (∏ i : TypX X, (aP (E := X.B.I.E) i.1 D.R.k X.B.I.n (Tw u) *
        aP (E := X.B.I.E) i.1 D.R.k X.B.I.n (Tw u'))) = ATyp * ATyp := by
    rw [Finset.prod_mul_distrib, Fintype.prod_congr _ _ (fun p : TypX X => htaP p), hATyp]
  have hG4 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).al * ATyp = AT * A' := by
    rw [hal_def, Fintype.prod_congr _ _ (fun p : TypX X => halT p.1 p.2), ← hATyp, hord, hTypProd]
    field_simp

  have hdX : 0 < |(NumberField.discr X.B.I.F : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero X.B.I.F)
  have hδHP := hasProd_rpow' ((X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2)
    (fun v => absV_nonneg X v) hDP (inv_ne_zero hdX.ne')
  have hωHP := hδHP.mul hA'HP
  have hG3 : (∏' v : PlX X,
        (omAt X.B.I.cm.sig X.B.I.J ψ v
          ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
          {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
            Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal) =
      |(NumberField.discr D.host.F : ℝ)| ^
        (-((D.R.r : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2)) * A' := by
    have hωHP' : HasProd (fun v : PlX X =>
        (omAt X.B.I.cm.sig X.B.I.J ψ v
          ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
          {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
            Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal)
        ((|(NumberField.discr X.B.I.F : ℝ)|⁻¹) ^
          ((X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2) * A') := by
      convert hωHP using 1
      funext v
      exact hOm hχ hstd v
    rw [hωHP'.tprod_eq, Real.inv_rpow (abs_nonneg _), ← Real.rpow_neg (abs_nonneg _), hd, hn']

  have hU_def : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).unitLevelVolume =
      (∏' v : OrdX X, localVolumeUnit X ψ v.1) * ∏ p : TypX X, localVolumeUnit X ψ p.1 := rfl
  have hZ_def : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volZZ =
      ∏' v : PlX X, ZZX X u u' ψ v := rfl
  obtain ⟨-, -, -, hU00m, -, hZZm, hZZpos, -⟩ := hPC
  have hUHP : HasProd (fun v => localVolumeUnit X ψ v)
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).unitLevelVolume := by
    rw [hU_def]
    exact hasProd_of_compl' (typSet X.B.I.F (D.host.g 0) (D.host.g 1)) hU00m.hasProd
  have hZHP : HasProd (fun v => ZZX X u u' ψ v)
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volZZ := by
    rw [hZ_def]
    exact hZZm.hasProd
  have hratHP := hUHP.mul (hasProd_inv₀' hZHP (by rw [hZ_def]; exact hZZpos.ne'))
  have hpp : ∀ v : PlX X, localVolumeUnit X ψ v * (ZZX X u u' ψ v)⁻¹ =
      absV v (dV v) ^ (-(((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3)) *
        (if TypAt X v then (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) else 1) := by
    intro v
    by_cases hv : TypAt X v
    · rw [if_pos hv, ← div_eq_mul_inv, hVt hχ hstd hcong v hv, htδ ⟨v, hv⟩, Real.one_rpow, one_mul]
    · rw [if_neg hv, ← div_eq_mul_inv, hVo hχ hstd v hv, mul_one]
  have hgHP : HasProd (fun v : PlX X => if TypAt X v then (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) else 1)
      (∏ p : TypX X, (gAt X p.1 : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3))) := by
    have h0 := hasProd_of_compl' (typSet X.B.I.F (D.host.g 0) (D.host.g 1))
      (f := fun v : PlX X => if TypAt X v then (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) else 1) (a := 1)
      (by
        convert (hasProd_one : HasProd (fun _ : {i // i ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1)} => (1 : ℝ)) 1)
          using 1
        funext v
        exact if_neg v.2)
    convert h0 using 1
    rw [one_mul]
    exact Fintype.prod_congr _ _ (fun p => (if_pos p.2).symm)
  have hδX := hasProd_rpow' (-(((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3))
    (fun v => absV_nonneg X v) hDP (inv_ne_zero hdX.ne')
  have hval : HasProd (fun v : PlX X => localVolumeUnit X ψ v * (ZZX X u u' ψ v)⁻¹)
      ((|(NumberField.discr X.B.I.F : ℝ)|⁻¹) ^ (-(((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3)) *
        ∏ p : TypX X, (gAt X p.1 : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3))) := by
    convert hδX.mul hgHP using 1
    funext v
    exact hpp v
  have hG1 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).unitLevelVolume /
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volZZ =
      |(NumberField.discr D.host.F : ℝ)| ^ (((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3) *
        ((Lat.gS D : ℕ) : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3) * Module.finrank ℚ D.host.F) := by
    rw [div_eq_mul_inv, hratHP.unique hval, Real.inv_rpow (abs_nonneg _), ← Real.rpow_neg (abs_nonneg _), neg_neg,
      hd, Finset.prod_pow, hgprod, ← pow_mul, mul_comm (Module.finrank ℚ D.host.F)]

  have hKo := hP.2.1
  have hKp : ∀ p, 0 < (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKp p :=
    fun p => (hP.1 p).2.2.2.2.2.1
  have hG2 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnat /
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK =
      ((Lat.gS D : ℕ) : ℝ) ^ (-(((D.R.rS + 1) * (2 * D.R.k + 2 * D.R.rS + 1) * Module.finrank ℚ D.host.F : ℕ) : ℤ)) /
        ATyp := by
    unfold Formalism.FourierDecayAlt.S3.MassData.μKnat Formalism.FourierDecayAlt.S3.MassData.μK
    rw [mul_div_mul_left _ _ hKo.ne', ← Finset.prod_div_distrib, Fintype.prod_congr _ _ hIx,
      Finset.prod_div_distrib, Finset.prod_zpow, hgprod, ← hATyp]
    congr 1
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring

  have hfinE : Module.finrank ℚ D.host.E = 2 * Module.finrank ℚ D.host.F := by
    rw [← Module.finrank_mul_finrank ℚ D.host.F D.host.E, D.sp.cm.deg2]
    ring
  have hng : ngFac D = ((Lat.gS D : ℕ) : ℝ) ^ (D.R.m * Module.finrank ℚ D.host.F * (D.R.k - 1)) := by
    unfold ngFac
    have hcast : (((Lat.gS D : ℕ) : D.host.E)) ^ D.R.m =
        algebraMap ℚ D.host.E (((Lat.gS D : ℕ) : ℚ) ^ D.R.m) := by simp
    rw [hcast, Algebra.norm_algebraMap, hfinE]
    have hg0 : (0 : ℝ) ≤ ((Lat.gS D : ℕ) : ℝ) := Nat.cast_nonneg _
    have hsq : |((((((Lat.gS D : ℕ) : ℚ) ^ D.R.m) ^ (2 * Module.finrank ℚ D.host.F) : ℚ)) : ℝ)| =
        (((Lat.gS D : ℕ) : ℝ) ^ (D.R.m * Module.finrank ℚ D.host.F)) ^ 2 := by
      push_cast
      rw [abs_of_nonneg (by positivity), ← pow_mul, ← pow_mul]
      ring_nf
    rw [hsq, Real.sqrt_sq (by positivity), ← pow_mul]

  rw [hd, hfc] at hR
  exact Formalism.L2.SG.Pf.NcArithG.ncValueC_of_global X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq
    a' _ ATyp A' AT PT hP ha hATyppos hA'pos hPTpos hS hR hG1 hG2 hG3 hG4 hG5
    (hRMp D u u' hcong F0 what₂ hRR) hvI hfE hng

end Formalism.L2.SG.Pf.NcGlob

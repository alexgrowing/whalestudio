import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAddCharPlaceIdempotentDivPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnCharacterReductionEqExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsKilledHeisenbergAverageIsotropic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent
import Formalism.LocalToGlobal.Divisibility.PsiWeilOfAbsNorm
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.SignsG
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.SignsAtTypePrimes

variable {D : D7}

theorem psiV_alg (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (p : ℕ) (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hN : Ideal.absNorm v.asIdeal = p) (hsq : (p : 𝓞 D.host.F) ∉ v.asIdeal ^ 2)
    (b : ℤ) :
    psiV D.host.F ψ v (algebraMap D.host.F (Fv D.host.F v) ((b : D.host.F) / (p : D.host.F))) =
      Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ v 1, fun w hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ v 1 hw⟩
  have h := GlobalTheory.StdCharDegOne.stdChar_placeIdem_div D ψ hψ p hp v hN hsq _ hε (b : 𝓞 D.host.F) b (by simp)
  rw [← h]
  unfold psiV
  congr 1
  refine Prod.ext ?_ ?_
  · show (0 : Ainf D.host.F) = 0 * _
    rw [zero_mul]
  · show singleV D.host.F v _ = singleV D.host.F v 1 * _
    refine GlobalTheory.SplitIdem.af_ext _ fun w => ?_
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.SplitIdem.evalV_singleV_same, GlobalTheory.SplitIdem.evalV_singleV_same, one_mul]
      change _ = evalV D.host.F w (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (((b : 𝓞 D.host.F) : D.host.F) / (p : D.host.F)))
      rw [AlgHom.commutes]
      push_cast
      rfl
    · rw [GlobalTheory.SplitIdem.evalV_singleV_ne _ v _ hw, GlobalTheory.SplitIdem.evalV_singleV_ne _ v _ hw, zero_mul]

theorem psiV_int (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (y : Fv D.host.F v) (hy : y ∈ v.adicCompletionIntegers D.host.F) : psiV D.host.F ψ v y = 1 := by
  have htr : ∀ r : 𝓞 D.host.F, Algebra.trace ℚ D.host.F (r : D.host.F) = ((Algebra.intTrace ℤ (𝓞 D.host.F) r : ℤ) : ℚ) :=
    fun r => (Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := D.host.F) r).symm
  unfold psiV
  refine GlobalTheory.IntDense.mem_of_isClosed D.host.F (C := {y | ψ (pairA D.host.F 0 y) = 1})
    (isClosed_eq (hψ.1.1.comp (Continuous.prodMk continuous_const continuous_id)) continuous_const)
    (fun r => ?_) _ (fun w => ?_)
  · show ψ (pairA D.host.F 0 (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (r : D.host.F))) = 1
    rw [GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, htr, mul_comm]
    push_cast
    exact Complex.exp_int_mul_two_pi_mul_I _
  · show evalV D.host.F w (singleV D.host.F v y) ∈ _
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.SplitIdem.evalV_singleV_same]
      exact hy
    · rw [GlobalTheory.SplitIdem.evalV_singleV_ne _ v _ hw]
      exact zero_mem _

end GlobalTheory.SignsAtTypePrimes

namespace GlobalTheory.SignsAtTypePrimes

variable {D : D7}

theorem val_le_of_lt_one {v : HeightOneSpectrum (𝓞 D.host.F)} (x : Fv D.host.F v) (h : Valued.v x < 1) :
    Valued.v x ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne (Valued.v x) 0 with h0 | h0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem core (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (k : Fin 2) {PP : Pl D.host.E}
    (res : kP PP ≃+* ZMod (D.host.g k)) (χ : AddChar (kP PP) D.what₂.LL)
    (hχ : ∀ c, D.what₂.embLL (χ c) = psiTxt D res c) (hχ1 : χ ≠ 1) {e : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e PP) (c : kP PP) :
    D.what₂.embLL (χ c) = Formalism.IndefR.Mi.psiAt ψ e
      (((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E)⁻¹ * ((Formalism.IndefR.Mi.liftRes PP c : 𝓞 D.host.E) : D.host.E)) := by
  classical
  obtain ⟨t, ht⟩ := GlobalTheory.Mem.TypePrimes.Red.exists_hostXi0_inverse_integer D.host
  have hN : Ideal.absNorm PP.asIdeal = D.host.g k := absNorm_eq_of_res D res
  have hgp := D.host.g_prime k
  have hE0 : ∀ s r : 𝓞 D.host.E, (s : D.host.E) * D.host.xi0 = (r : D.host.E) → s = r * t := fun s r h => by
    apply Subtype.ext
    show (s : D.host.E) = (r : D.host.E) * (t : D.host.E)
    rw [← h, mul_assoc, ht, mul_one]

  have htP : t ∉ PP.asIdeal := by
    intro htP
    apply hχ1
    ext c'
    have hx : xiBar D PP = 0 := by
      unfold xiBar Formalism.L2.Col.redP
      rw [dif_neg]
      rintro ⟨_, r, s, hs, hsa, _⟩
      apply hs
      rw [hE0 s r hsa]
      exact Ideal.mul_mem_left _ _ htP
    have h1 := hχ c'
    rw [psiTxt_apply, hx, zero_mul, map_zero, AddChar.map_zero_eq_one, ← map_one D.what₂.embLL] at h1
    rw [AddChar.one_apply]
    exact D.what₂.embLL.injective h1
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  obtain ⟨c0, hc0⟩ := Ideal.Quotient.exists_inv (I := PP.asIdeal) (a := Ideal.Quotient.mk PP.asIdeal t)
    (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hxi : xiBar D PP = c0 :=
    Formalism.L2.Col.redP_eq PP (r := 1) (s := t) htP (by rw [map_one, mul_comm]; exact ht) (by rw [map_one]; exact hc0)

  set b : ℤ := (((res (xiBar D PP * c)).val : ℕ) : ℤ) with hbdef
  have hb : xiBar D PP * c = (b : kP PP) := by
    apply res.injective
    rw [map_intCast, hbdef, Int.cast_natCast, ZMod.natCast_zmod_val]

  rw [hχ c, psiTxt_apply, hb, map_intCast, ZMod.stdAddChar_coe]

  obtain ⟨v, hv⟩ := (GlobalTheory.IdemModTwo.isSplitIdem_iff e).1 he.1
  have hπ := GlobalTheory.SplitChart.chart_comp hv
  set π := GlobalTheory.SplitChart.comp hv with hπdef
  unfold Formalism.IndefR.Mi.psiAt
  rw [GlobalTheory.ThetaSupport.char_trace ψ hv, ← hπdef]
  set f : D.host.E →+* Fv D.host.F v := π.comp (incA D) with hf
  set L : 𝓞 D.host.E := Formalism.IndefR.Mi.liftRes PP c with hL
  have hLc : Ideal.Quotient.mk PP.asIdeal L = c := Function.surjInv_eq Ideal.Quotient.mk_surjective c

  have hgPP : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have := Ideal.absNorm_mem PP.asIdeal
    rwa [hN] at this
  have hfg : f ((D.host.g k : ℕ) : D.host.E) = algebraMap D.host.F (Fv D.host.F v) ((D.host.g k : 𝓞 D.host.F) : D.host.F) := by
    rw [map_natCast]; simp
  have hgv1 : Valued.v (f ((D.host.g k : ℕ) : D.host.E)) < 1 := by
    have := GlobalTheory.ThetaSupport.val_lt_one_of_mem he hπ hgPP
    simpa using this
  have hgv : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    rw [hfg, Examples₂.adicCompl_val_algebraMap] at hgv1
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.F) v _).1 hgv1
  obtain ⟨hNv, hsq⟩ := GlobalTheory.Mem.TypePrimes.Red.absNorm_and_unram (F := D.host.F) (E := D.host.E) hgp (D.nd.g_split k) v hgv

  have hgFv : ((D.host.g k : ℕ) : Fv D.host.F v) = algebraMap D.host.F (Fv D.host.F v) ((D.host.g k : 𝓞 D.host.F) : D.host.F) := by
    simp
  have hgne : ((D.host.g k : ℕ) : Fv D.host.F v) ≠ 0 := by
    rw [hgFv]
    exact (map_ne_zero _).2 (by exact_mod_cast hgp.ne_zero)
  have hgval : WithZero.exp (-1 : ℤ) ≤ Valued.v ((D.host.g k : ℕ) : Fv D.host.F v) := by
    rw [hgFv, Examples₂.adicCompl_val_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    have hlow : ¬ v.intValuation ((D.host.g k : ℕ) : 𝓞 D.host.F) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
      fun h => hsq ((HeightOneSpectrum.intValuation_le_pow_iff_mem v _ 2).1 h)
    have hne : v.intValuation ((D.host.g k : ℕ) : 𝓞 D.host.F) ≠ 0 :=
      HeightOneSpectrum.intValuation_ne_zero v _ (by exact_mod_cast hgp.ne_zero)
    rw [← WithZero.exp_log hne] at hlow ⊢
    rw [WithZero.exp_le_exp] at hlow ⊢
    push_cast at hlow
    omega

  have ht0 : t ≠ 0 := fun h => by rw [h] at ht; simp at ht
  have hxit : D.host.xi0 = (t : D.host.E)⁻¹ := eq_inv_of_mul_eq_one_left ht
  have hξ : Valued.v (f D.host.xi0) ≤ 1 := by
    have h1 : Formalism.L2.Theta.finPart D (e * incA D ((t : D.host.E)⁻¹)) ∈ intAE D := by
      by_contra hc
      exact htP ((he.2 t ht0).2 hc)
    have h2 := GlobalTheory.SplitHecke.isInt_Ov.1 ((hπ.2.2.2 _).1 h1)
    rw [← hxit] at h2
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).1 h2

  have hy : L - (b : 𝓞 D.host.E) * t ∈ PP.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hLc, map_intCast, ← hb, hxi]
    linear_combination (-c) * hc0
  have hft : f D.host.xi0 * f (t : D.host.E) = 1 := by rw [← map_mul, ht, map_one]
  have hXv : Valued.v (f D.host.xi0 * f (L : D.host.E) - (b : Fv D.host.F v)) < 1 := by
    have h1 := GlobalTheory.ThetaSupport.val_lt_one_of_mem he hπ hy
    have e1 : f D.host.xi0 * f (L : D.host.E) - (b : Fv D.host.F v) =
        f D.host.xi0 * π (incA D ((L - (b : 𝓞 D.host.E) * t : 𝓞 D.host.E) : D.host.E)) := by
      change _ = f D.host.xi0 * f ((L - (b : 𝓞 D.host.E) * t : 𝓞 D.host.E) : D.host.E)
      have hb' : f (((b : 𝓞 D.host.E)) : D.host.E) = (b : Fv D.host.F v) := by
        rw [show (((b : 𝓞 D.host.E)) : D.host.E) = (b : D.host.E) from map_intCast (algebraMap (𝓞 D.host.E) D.host.E) b,
          map_intCast]
      push_cast
      rw [map_sub, map_mul, hb']
      linear_combination (b : Fv D.host.F v) * hft
    rw [e1, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hξ) h1
  have hint : (f D.host.xi0 * f (L : D.host.E) - (b : Fv D.host.F v)) / ((D.host.g k : ℕ) : Fv D.host.F v) ∈
      v.adicCompletionIntegers D.host.F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
    have hpos : 0 < Valued.v ((D.host.g k : ℕ) : Fv D.host.F v) := lt_of_lt_of_le (by simp) hgval
    rw [div_le_one₀ hpos]
    exact (val_le_of_lt_one _ hXv).trans hgval
  have hsplit : π (incA D (D.host.xi0 * (((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E)⁻¹ * (L : D.host.E)))) =
      algebraMap D.host.F (Fv D.host.F v) ((b : D.host.F) / ((D.host.g k : ℕ) : D.host.F)) +
        (f D.host.xi0 * f (L : D.host.E) - (b : Fv D.host.F v)) / ((D.host.g k : ℕ) : Fv D.host.F v) := by
    change f (D.host.xi0 * (((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E)⁻¹ * (L : D.host.E))) = _
    rw [hN, map_mul, map_mul, map_inv₀, map_natCast, map_div₀, map_intCast, map_natCast]
    field_simp
    ring
  rw [hsplit, GlobalTheory.ThetaSupport.psiV_add ψ hv, psiV_alg ψ hψ _ hgp v hNv hsq b, psiV_int ψ hψ v _ hint, mul_one]

end GlobalTheory.SignsAtTypePrimes

namespace GlobalTheory.SignsAtTypePrimes

variable {D : D7}

theorem factor (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (k : Fin 2) {PP PP' : Pl D.host.E}
    (h : PP = PP') (res : kP PP ≃+* ZMod (D.host.g k)) (iso : ZMod (D.host.g k) ≃+* kP PP')
    (χ : AddChar (kP PP) D.what₂.LL) (hχ : ∀ c, D.what₂.embLL (χ c) = psiTxt D res c) (hχ1 : χ ≠ 1) {e : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e PP') (s : ZMod (D.host.g k)) :
    D.what₂.embLL (χ (res.symm s)) = Formalism.IndefR.Mi.psiAt ψ e
      (((Ideal.absNorm PP'.asIdeal : ℕ) : D.host.E)⁻¹ * ((Formalism.IndefR.Mi.liftRes PP' (iso s) : 𝓞 D.host.E) : D.host.E)) := by
  subst h
  have hi : iso = res.symm := by
    have h1 := res_unique iso.symm res
    rw [← h1, RingEquiv.symm_symm]
  subst hi
  exact core ψ hψ k res χ hχ hχ1 he (res.symm s)

theorem edgeSum_eq_supSum {κ : Type} [CommRing κ] {r : ℕ} (g : GL (Fin r) κ) :
    edgeSum supEdge g = Formalism.IndefR.Mi.supSum (g : Matrix (Fin r) (Fin r) κ) := by
  unfold edgeSum Formalism.IndefR.Mi.supSum
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.1 + 1, h⟩]
    · exact if_pos (show supEdge i ⟨i.1 + 1, h⟩ from rfl)
    · intro j _ hj
      exact if_neg (fun hj' => hj (Fin.ext hj'))
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · refine Finset.sum_eq_zero fun j _ => ?_
    refine if_neg (fun hj => ?_)
    have := j.2
    unfold supEdge at hj
    omega

theorem supSum_map {κ κ' : Type} [CommRing κ] [CommRing κ'] (φ : κ →+* κ') {r : ℕ} (x : Matrix (Fin r) (Fin r) κ) :
    Formalism.IndefR.Mi.supSum (x.map φ) = φ (Formalism.IndefR.Mi.supSum x) := by
  unfold Formalism.IndefR.Mi.supSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem parabolicCharacter_eq_prod_superdiagonalSum {Pg : Finset (Pl D.host.E)} {r : ℕ} (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL)
    (x : G0 Pg r) (hx : x ∈ (Formalism.L2.DIV.P0 Pg r ψ).H) :
    (((Formalism.L2.DIV.P0 Pg r ψ).chi ⟨x, hx⟩ : D.what₂.LLˣ) : D.what₂.LL) =
      ∏ PP : ↥Pg, ψ PP.1 (Formalism.IndefR.Mi.supSum ((x PP : GL (Fin r) (kP PP.1)) : Matrix (Fin r) (Fin r) (kP PP.1))) := by
  unfold Formalism.L2.DIV.P0 LevelP.ofLocal
  rw [MonoidHom.finset_prod_apply, Units.coe_prod]
  refine Finset.prod_congr rfl fun PP _ => ?_
  rw [← edgeSum_eq_supSum]
  rfl

end GlobalTheory.SignsAtTypePrimes

namespace GlobalTheory.SignsAtTypePrimes

theorem signsAtG : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), IsStdChar D R.ψ (-1) → PsiPPTie D F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → Mi.SignsAtG R F := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F cG hψ hT hplg
  obtain ⟨plg, iso, hpl, -, heG⟩ := hplg
  obtain ⟨Pg, pl, res, ψ, eC, hL, hW⟩ := hT
  have hχ := (psiWeil_iff D Pg pl res ψ).1 hW
  intro e he u
  have hu : eC u ∈ (Formalism.L2.DIV.P0 Pg D.R.r ψ).H := (hL.p0 u).1 u.2
  rw [hL.chi0 u hu, parabolicCharacter_eq_prod_superdiagonalSum, map_prod, ← Equiv.prod_comp pl, ← Equiv.prod_comp plg]
  refine Finset.prod_congr rfl fun kv _ => ?_
  rw [hL.eC_eq (u : G) kv, heG (u : G) kv]
  have e1 : ((Matrix.GeneralLinearGroup.map (res kv).symm.toRingHom ((R.eG.trans cG) (u : G) kv) :
      GL (Fin D.R.r) (kP (pl kv).1)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP (pl kv).1)) =
      ((((R.eG.trans cG) (u : G) kv) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))).map (res kv).symm.toRingHom := rfl
  have e2 : ((Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) (u : G) kv) :
      GL (Fin D.R.r) (kP (plg kv).1)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP (plg kv).1)) =
      ((((R.eG.trans cG) (u : G) kv) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))).map (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) := rfl
  rw [e1, e2, supSum_map, supSum_map]
  exact factor R.ψ hψ kv.1 ((hL.place kv).trans (hpl kv).symm) (res kv) (iso kv) (ψ (pl kv).1) (hχ kv)
    (hL.gen _ (pl kv).2) (he (plg kv)) _

end GlobalTheory.SignsAtTypePrimes

end

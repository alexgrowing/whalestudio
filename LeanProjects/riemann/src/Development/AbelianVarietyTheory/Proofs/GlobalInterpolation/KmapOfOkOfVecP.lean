import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsRecordDat
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetStepEqZeroExample
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDivLatticeQuotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertAtLeCongN
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubDSharpInDeg
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdDifferent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexLocPNeZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedCompAtDetIdl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameCharacterValuesEqHeckeCharLocalValuesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCharEqHeckeCharLocalComponentOfValues
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntAtOfLocTop
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrdSubEqOrdDet
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TildeQDetPtEqChiId

noncomputable section

namespace GlobalTheory.LvT.Built.KMap

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2
open Formalism.L2.Forms (fnOf shiftOf)
open Formalism.L2.Host (HChar)
open GlobalTheory.GO.ChSrc (trueWt nuEnd sS sD polFn fnPol)
open GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree (InBox)

section Poly

variable {X : Fields} {R : Ranks}

theorem sSharp_eq (I : ChainIn X.E X.K X.Tau R) (σ : X.K →+* ℂ) (h : I.Ok) (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    (I.chain X.emb σ h hc).sSharp i τ = sS hc i τ ∧ (I.chain X.emb σ h hc).sDiv i τ = sD hc i τ := by
  constructor
  · have h1 : ((sS hc i τ : ℤ) : ℚ) = sExp' R ((hc τ).e ⟨i, hi⟩) (i + 1) := by
      rw [sS, dif_pos hi]; exact GlobalTheory.GO.ChSrc.zOf_spec R _ ((hc τ).e_int _) _
    exact_mod_cast ((I.chain X.emb σ h hc).sSharp_eq i hi τ).trans h1.symm
  · have h1 : ((sD hc i τ : ℤ) : ℚ) = sExp R ((hc τ).e ⟨i, hi⟩) (i + 1) := by
      rw [sD, dif_pos hi]; exact GlobalTheory.GO.ChSrc.zOf_spec R _ ((hc τ).e_int _) _
    exact_mod_cast ((I.chain X.emb σ h hc).sDiv_eq i hi τ).trans h1.symm

theorem kmap_of_jet (I : ChainIn X.E X.K X.Tau R) (σ : X.K →+* ℂ) (h : I.Ok) (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m)
    (c : (I.S i).Cl) (c' : (I.S (i + 1)).Cl) (F : Formalism.L2.DIV.VV X.K (trueWt hc i)) (F' : Formalism.L2.DIV.VV X.K (trueWt hc (i + 1)))
    (e : MvPolynomial.map σ F'.1 =
      (I.rho i c * I.rho' i c') • I.jet i c c' (MvPolynomial.map σ (F.1 * ∏ τ, frDet X.K (R.N i) τ ^ nuEnd hc i τ))) :
    (I.chain X.emb σ h hc).Kmap i c c' (evV X.emb 1 (trueWt hc i) σ F) = evV X.emb 1 (trueWt hc (i + 1)) σ F' := by
  have h1 : (I.chain X.emb σ h hc).sharp i (evV X.emb 1 (trueWt hc i) σ F) =
      polFn X σ _ (MvPolynomial.map σ (F.1 * ∏ τ, frDet X.K (R.N i) τ ^ nuEnd hc i τ)) := by
    funext (y : Fr X.emb σ (R.N i))
    have hd : ∀ τ, MvPolynomial.eval₂ σ (fun v : X.Tau × Fin (R.N i) × Fin (R.N i) => y.1 v.1 v.2.1 v.2.2)
        (frDet X.K (R.N i) τ) = (y.1 τ).det := fun τ => by
      rw [← MvPolynomial.coe_eval₂Hom, frDet, RingHom.map_det]
      congr 1
      ext a b
      simp
    show (∏ τ, (y.1 τ).det ^ (I.chain X.emb σ h hc).sSharp i τ) * evFr _ (shiftOf (trueWt hc i)) σ F.1 y = _
    rw [GlobalTheory.GO.ChSrc.polFn_apply, MvPolynomial.eval_map, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_prod, evFr_apply, ← mul_assoc,
      ← Finset.prod_mul_distrib, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [MvPolynomial.eval₂_pow, hd, ← zpow_natCast, GlobalTheory.GO.ChSrc.nuEnd_cast hc hi, zpow_add₀ (isUnit_det_fr y τ).ne_zero,
      (sSharp_eq I σ h hc hi τ).1, mul_comm]
    rfl
  funext (y : Fr X.emb σ (R.N (i + 1)))
  show (I.rho i c * I.rho' i c') * ((∏ τ, (y.1 τ).det ^ (I.chain X.emb σ h hc).sDiv i τ)⁻¹ *
    polFn X σ _ (I.jet i c c' (fnPol X σ _ ((I.chain X.emb σ h hc).sharp i (evV X.emb 1 (trueWt hc i) σ F)))) y) =
      evFr _ (shiftOf (trueWt hc (i + 1))) σ F'.1 y
  rw [h1, GlobalTheory.GO.ChSrc.fnPol_polFn, evFr_apply, ← MvPolynomial.eval_map, e, MvPolynomial.smul_eval, GlobalTheory.GO.ChSrc.polFn_apply,
    mul_left_comm, ← Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [(sSharp_eq I σ h hc hi τ).2, ← zpow_neg, ← GlobalTheory.GO.ChSrc.trueWt_detShift_succ hc hi]
  rfl

theorem jetC_sum {ι : Type} [Fintype ι] {a b : ℕ} (cD : ι → ℂ) {I : Type} [Fintype I] (c : I → ℂ) (G : I → VCx ι a b → ℂ)
    (hG : ∀ i (k : ℕ), ContDiff ℂ k (G i)) (m : DVar ι a b →₀ ℕ) :
    jetC cD (fun z => ∑ i, c i * G i z) m = ∑ i, c i * jetC cD (G i) m := by
  have e : (fun z => ∑ i, c i * G i z) = fun z => ∑ i, (c i • G i) z := by
    funext z; simp
  unfold jetC derivAt0
  rw [e, iteratedFDeriv_sum (f := fun i => c i • G i) (fun i _ => (hG i _).const_smul (c i))]
  simp only [Finset.sum_apply, ContinuousMultilinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_const_smul_apply (hG i _).contDiffAt]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem map_kerOf (A : Amb X) {a b : ℕ} (Sa SB : Finset (HeightOneSpectrum (𝓞 X.E))) {cA cB : ℕ} (hA : 0 < cA) (hB : 0 < cB)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
    (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ) (hV : JetInVV X.K lam lam' n)
    (hL : A.LaHyp a b Sa) (h0 : A.AA ≠ ⊥) (hE : A.ESmooth a b)
    {N : Submodule (𝓞 X.E) (Sp X.E a)} (fr : Frs X.E a SB) {N' : Submodule (𝓞 X.E) (Sp X.E b)} (fr' : Frs X.E b SB)
    (hN : IsSdLat N) (hN' : IsSdLat N') (hJ : GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.JetsIn A Sa cA cB lam n N N')
    {Ξ : HomE X.E a b → X.K} (hΞ : InBox Sa cA cB N N' Ξ) (F : Formalism.L2.DIV.VV X.K lam) :
    MvPolynomial.map A.σ₀ (kerOf (thDistC A Sa SB (cA * cB) sel mU mI lam lam' n) Sa cA cB N fr N' fr' Ξ F).1 =
      (A.σ₀ (muInvDet sel SB mU mI N fr * (muInvDet sel SB mU mI N' fr')⁻¹) * (A.chiF a b N N')⁻¹) •
        jetMap (jetC A.cD (thC (X.embC A.σ₀) A.δ A.d A.sc A.AA Sa N N' (cA * cB) (fun x => A.σ₀ (Ξ x)) (A.e a b N N'))) 0
          (MvPolynomial.map A.σ₀ (F.1 * ∏ τ, frDet X.K a τ ^ n τ)) := by
  classical
  have hfin := GlobalTheory.finite_divLat_quot_mulLat_homAt X.E a b Sa N N' cA cB hN.1 hN'.1 hA hB
  have hth := GlobalTheory.latSum_thInd_eq_thC X A a b Sa N N' cA cB (fun x => A.σ₀ (Ξ x)) (indTieD_of_la A a b Sa _ (Nat.mul_pos hA hB) hL)
    hN hN' hA hB (GlobalTheory.ThetaMove.VolumePos.volC_pos X.E a b A.AA Sa N N' hN.1.fg hN'.1.fg hN.1.span_eq_top hN'.1.span_eq_top
      hL.2.2.2.2.1 h0) hfin (fun x hx => hΞ.1 x ((map_ne_zero A.σ₀).1 hx)) fun x y hy => congrArg A.σ₀ (hΞ.2 x y hy)
  let _ := Fintype.ofFinite (↥(divLat cA (homAt Sa N N')) ⧸ (mulLat cB (homAt Sa N N')).comap (divLat cA (homAt Sa N N')).subtype)
  rw [kerOf_thDistC, ← funext hth]
  unfold latSum
  simp only [finsum_eq_sum_of_fintype]
  set r := Function.surjInv (Submodule.Quotient.mk_surjective
    ((mulLat cB (homAt Sa N N')).comap (divLat cA (homAt Sa N N')).subtype))
  have hs : ∀ q (k : ℕ), ContDiff ℂ k (A.thInd Sa N N' cB (r q)) := fun q =>
    indSmooth_of A a b Sa (cA * cB) hE N N' cB (r q) ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩
  have hj : jetC A.cD (fun z => ∑ q, A.σ₀ (Ξ (r q)) * A.thInd Sa N N' cB (r q) z) =
      ∑ q, A.σ₀ (Ξ (r q)) • jetC A.cD (A.thInd Sa N N' cB (r q)) := by
    funext m
    rw [jetC_sum _ _ _ hs, Finset.sum_apply]
    rfl
  rw [hj, GlobalTheory.GO.jetMap_sum, LinearMap.sum_apply, LinearMap.sum_apply, Submodule.coe_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, Submodule.coe_smul, jetOp_coe lam lam' n hV,
    smul_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul,
    GlobalTheory.GO.map_jetMap A.σ₀ _ (jetC A.cD (A.thInd Sa N N' cB (r q))) (A.chiF a b N N')⁻¹ n F.1, smul_smul, smul_smul, map_mul]
  · congr 1
    ring
  · intro μ hμ
    have h1 : ∃ k : X.K, A.σ₀ k = _ := hJ (r q) (r q).2 (μ.comapDomain Sum.inr Sum.inr_injective.injOn) fun τ => by
      have h1 := GlobalTheory.JetDeg.subD_hom (b := b) τ (GlobalTheory.JetDeg.sharp_hom n τ (GlobalTheory.JetDeg.VV_hom lam τ F.2))
        (MvPolynomial.mem_support_iff.mp hμ)
      rw [GlobalTheory.JetDeg.weight_derW] at h1
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.degAt, GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.degNu, Finsupp.comapDomain_apply]
      rw [h1]
      push_cast
      simp [GlobalTheory.JetDeg.natW_cast, Finset.sum_add_distrib, mul_comm]
    rw [Amb.jetK, desc, dif_pos h1]
    exact h1.choose_spec

end Poly

section Scalar

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {σ : X.K →+* ℂ} {e : Fin R.m → X.Tau → ℚ} {m0 : Fin R.m → HChar X.E} {eta ξ : HChar X.E}

theorem sel_mem_QE (h : Reads σ (mu : Chr X.F X.E X.K) ξ) {P : HeightOneSpectrum (𝓞 X.E)} (hP : ¬ ξ.UnrAt P) :
    sel (P.under (𝓞 X.F)) ∈ QE sel (mu : Chr X.F X.E X.K) := by
  classical
  have hf := GlobalTheory.OpenChrRam.qprime_finite X.F X.E X.K (mu : Chr X.F X.E X.K) mu.2.1.1.1.1.2
  rw [QE, dif_pos hf]
  exact Finset.mem_image_of_mem _ (hf.mem_toFinset.2 ((GlobalTheory.Mem.ReadTwist.mem_qprime_iff h _).2 ⟨P, rfl, hP⟩))

theorem locK_eq_val {L : Type} [Field L] [NumberField L] (χ : HChar L) (Q : HeightOneSpectrum (𝓞 L)) (hu : χ.UnrAt Q) (k : Lˣ)
    (hk : Q.valuation L (k : L) = WithZero.exp (-1 : ℤ)) : χ.locK Q k = χ.val Q := by
  have h1 : Q.valuation L (Formalism.L2.Host.unif Q : L) = WithZero.exp (-1 : ℤ) :=
    (valued_algebraMap Q _).symm.trans (Formalism.L2.Host.unif_spec Q)
  rw [Formalism.L2.Host.HChar.val, ← div_eq_one, ← map_div]
  refine GlobalTheory.NormOneUnit.locK_unr hu ?_
  rw [Units.val_div_eq_div_val, map_div₀, hk, h1, div_self WithZero.exp_ne_zero]

theorem map_muAtT (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : ∀ k, Pr.g k ∈ S) (ht : Ch.Tied σ e m0 eta)
    (hG : MuqTieG (R := R) sel mu cst σ m0) (h : Reads σ (mu : Chr X.F X.E X.K) ξ) (j : Fin R.m) (P : rowSG Pr sel mu) (a : X.Eˣ) :
    σ (muAtT Ch sel mu cst j.1 P (a : X.E)) = (((m0 j * ξ).locK P.1 a : ℂˣ) : ℂ)⁻¹ := by
  classical
  have hlp := GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P
  have hta := GlobalTheory.Mem.ReadTwist.tameAt h fun v => Subgroup.mem_iInf.1 mu.2.1.2 v
  have hq := (GlobalTheory.T.tame_character_values_eq_heckeChar_local_values X.F X.E X.K σ _ ξ h hta P.1).2 hlp.1.2
  have hm : ∀ x, (((m0 j * ξ)⁻¹.locK P.1 x : ℂˣ) : ℂ) = (((m0 j).locK P.1 x : ℂˣ) : ℂ)⁻¹ * ((ξ.locK P.1 x : ℂˣ) : ℂ)⁻¹ := fun x => by
    rw [← mul_inv, ← Units.val_mul, ← Units.val_inv_eq_inv_val]
    rfl
  have hu : ∀ (x : X.Eˣ) (y : 𝓞 X.E) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ), (x : X.E) = (y : X.E) →
      (c : 𝓞 X.E ⧸ P.1.asIdeal) = Ideal.Quotient.mk P.1.asIdeal y → P.1.valuation X.E (x : X.E) = 1 := fun x y c hx hc => by
    rw [hx]
    exact GlobalTheory.NormOneUnit.val_eq_one fun hy => c.ne_zero (hc.trans (Ideal.Quotient.eq_zero_iff_mem.2 hy))
  rw [← Units.val_inv_eq_inv_val]
  refine GlobalTheory.LocCharComp.locChar_eq_locK X.E X.K σ P.1 (m0 j * ξ)⁻¹ _ _ hlp.1.2 (fun q hq' => ?_) (fun x y c hx hc => ?_) a
  · rw [hm, ← hq q hq']
    by_cases hP : P.1 ∈ Pr.vGs
    · rw [if_pos hP, hG j.1 j.2 P hP q hq', Units.val_inv_eq_inv_val, map_inv₀]
    · have hg' : ∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal := fun k =>
        GlobalTheory.ColPeriod.natCast_notMem_of_ne (hPr.g_prime k) hlp.1.1 (fun h => hlp.2 hP (h ▸ hg k)) P.1 (Ideal.absNorm_mem _)
      rw [if_neg hP, muqT, dif_pos j.2, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀,
        ht.muVal j P.1 hg', ← locK_eq_val (m0 j) P.1 ((ht.mu0 j).unr _ hg') q
          (hq' ▸ GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _) hlp.1.2)]
  · rw [hm]
    by_cases hP : P.1 ∈ Pr.vGs
    · have hun : ξ.UnrAt P.1 := by
        by_contra hn
        obtain ⟨k, hk⟩ := GlobalTheory.NormOneUnit.mem_vGs hP
        have gk : ((Pr.g k : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal := hPr.piG_norm k ▸ P.1.asIdeal.mul_mem_left _ hk
        have h1 := (GlobalTheory.NormOneUnit.mem_QE mu hsel (sel_mem_QE (sel := sel) h hn)).2.2.2
        rw [show (sel (P.1.under (𝓞 X.F))).under (𝓞 X.F) = P.1.under (𝓞 X.F) from HeightOneSpectrum.ext (hsel _),
          (GlobalTheory.Mem.ReadTwist.plc_under_eq_iff (F := X.F) P.1 (hPr.g_prime k)).2 gk] at h1
        exact h1 (hg k)
      rw [if_pos hP, GlobalTheory.NormOneUnit.locK_unr hun (hu x y c hx hc), (ht.mu0 j).atg ⟨P.1, hP⟩ x y c hx hc, chiP, dif_pos hP, chiAt, extChi,
        dif_pos j.2, Units.val_inv_eq_inv_val, map_inv₀, inv_inv, Units.val_one, inv_one, mul_one]
    · have hg' : ∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal := fun k =>
        GlobalTheory.ColPeriod.natCast_notMem_of_ne (hPr.g_prime k) hlp.1.1 (fun h => hlp.2 hP (h ▸ hg k)) P.1 (Ideal.absNorm_mem _)
      rw [if_neg hP, GlobalTheory.NormOneUnit.locK_unr ((ht.mu0 j).unr _ hg') (hu x y c hx hc), MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
        map_inv₀, GlobalTheory.NormOneUnit.resChar_eq h hta P.1 c y x hx hc.symm, Units.val_one, inv_one, one_mul]

theorem map_muInvDet (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hg : ∀ k, Pr.g k ∈ S) (ht : Ch.Tied σ e m0 eta)
    (hG : MuqTieG (R := R) sel mu cst σ m0) (h : Reads σ (mu : Chr X.F X.E X.K) ξ) (j : Fin R.m) {n : ℕ}
    {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) (fr : HeightOneSpectrum (𝓞 X.E) → Sp X.E n ≃ₗ[X.E] Sp X.E n) :
    σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu j.1) (muAtT Ch sel mu cst j.1) N fun P => fr P.1) =
      (((m0 j * ξ).1 (detIdl (rowSG Pr sel mu) N fr) : ℂˣ) : ℂ)⁻¹ := by
  classical
  have hta := GlobalTheory.Mem.ReadTwist.tameAt h fun v => Subgroup.mem_iInf.1 mu.2.1.2 v
  rw [GlobalTheory.DetIdlValue.inv_val_detIdl X n sel _ (m0 j * ξ) σ (mUof Ch mu j.1) N fr hX hsel hN
    ((ht.mu0 j).triv.mul (GlobalTheory.Mem.ReadTwist.trivOn h mu.2.1.1.2)) fun w h1 h2 => ?_, muInvDet, map_mul, map_prod]
  · exact congrArg _ (Finset.prod_congr rfl fun P _ => map_muAtT hX hPr hsel hg ht hG h j P _)
  · have hg' := GlobalTheory.MuConj.g_notMem hPr w (fun a => h1 (Finset.mem_union_left _ a)) fun a => h2 (Finset.mem_union_left _ a)
    have hun : ξ.UnrAt w := by
      by_contra hn
      have h3 := sel_mem_QE (sel := sel) h hn
      rcases (GlobalTheory.NormOneUnit.under_eq_iff hX.star_F hX.rankE (GlobalTheory.NormOneUnit.exists_star_ne hX) w _).1
        (HeightOneSpectrum.ext (hsel (w.under (𝓞 X.F)))) with e | e
      exacts [h1 (Finset.mem_union_right _ (e ▸ h3)), h2 (Finset.mem_union_right _ (e ▸ h3))]
    refine ⟨((ht.mu0 j).unr w hg').mul hun, ?_⟩
    rw [mUof, dif_pos j.2, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀,
      ht.muVal j w hg', (GlobalTheory.T.tame_character_values_eq_heckeChar_local_values X.F X.E X.K σ _ ξ h hta w).1 hun, Formalism.L2.Host.HChar.val_mul, Units.val_mul, mul_inv]

end Scalar

section General

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Amb X) (u : Pr.Word)

def RhoIs (i : ℕ) (rho : Idx sel mu L i → PtAt R sel mu cst u i → ℂ) (rho' : Idx sel mu L (i + 1) → PtAt R sel mu cst u (i + 1) → ℂ) : Prop :=
  ∀ b p b' p', rho b p * rho' b' p' =
    A.σ₀ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAtT Ch sel mu cst i) p.1.1.deco.1.N (frsF sel mu p.1.1) *
      (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAtT Ch sel mu cst i) p'.1.1.deco.1.N (frsF sel mu p'.1.1))⁻¹) *
        (A.chiF _ _ p.1.1.deco.1.N p'.1.1.deco.1.N)⁻¹

end General

section True

open GlobalTheory.Mem GlobalTheory.Mem.Chr

local instance starHost (B : Base) : StarRing B.host.E := B.fields.starE

variable {B : Base} {X : PreX B.toPre} (I : ColIn B X)

theorem map_muInvDet_pt (h : I.Ok) (a : I.ι) (u : B.Word) (j : Fin B.R.m) {n : ℕ}
    (p : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u n) :
    B.embLL (muInvDet (X := B.fields) I.sel (rowSG (B.primes X) I.sel (I.tup a)) (mUof (R := B.R) I.Ch (I.tup a) j.1)
      (muAtT (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) j.1) p.deco.1.N (frsF I.sel (I.tup a) p)) =
      (((I.C.mu0 j * I.xi a).1 (ptIdl B.host I.SQ p) : ℂˣ) : ℂ)⁻¹ := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨h1, -, h2⟩ := GlobalTheory.Mem.LevTwist.levOk_twists B X I h
  have hk : KDq B.host (I.Q a) ≤ ((I.C.mu0 j * I.xi a).1.comp (finPartI B.host.E)).ker := fun x hx => by
    have e1 : (I.C.mu0 j).1 (finPartI B.host.E x) = 1 := reference_characters_factor_tame (I.Q a) I.C j hx
    have e2 : (I.xi a).1 (finPartI B.host.E x) = 1 := (h2 a).1 hx
    show (I.C.mu0 j).1 (finPartI B.host.E x) * (I.xi a).1 (finPartI B.host.E x) = 1
    rw [e1, e2, one_mul]
  rw [← xiDet_eq I.SQ ((KDq_anti B.host (I.Q_subset_SQ a)).trans hk), xiDet, ← tildeQ_toDtQ (I.Q_subset_SQ a) hk,
    DetProj.toDtQ_detPt B.R B.host _ _ _ _ _ (I.Q_subset_SQ a) p h1, ← xiDet, xiDet_eq _ hk,
    funext (frsF_eq_ptFr I.sel (I.tup a) p)]
  exact map_muInvDet hX hPr h.sel_ok h.g_mem h.ch_tied (h.idx_ok a).muqG (h.xi_reads a) j ⟨p.deco.2.lat, p.deco.2.uni⟩ (ptFr p)

theorem rhoIs (h : I.Ok) (a : I.ι) (u : B.Word) {i : ℕ} (hi : i < B.R.m) :
    RhoIs (Pr := B.primes X) I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i
      (fun _ p => ((rhoAt I.SQ I.C (I.xi a) i p.1.1 : ℂˣ) : ℂ)) fun _ p => ((rhoAt' I.SQ I.C (I.xi a) i p.1.1 : ℂˣ) : ℂ) := by
  intro b p b' p'
  obtain ⟨h1, -, h2⟩ := GlobalTheory.Mem.LevTwist.levOk_twists B X I h
  have hk := (KDq_anti B.host (I.Q_subset_SQ a)).trans (h2 a).1
  have e1 := rhoAt_eq_hecke I.SQ I.C hk ⟨i, hi⟩ p.1.1
  have e2 := rhoAt'_eq_hecke I.SQ I.C hk ⟨i, hi⟩ p'.1.1
  rw [← xiDet_eq I.SQ (chiPsi_factors I.SQ I.C), xiDet] at e1 e2
  have c1 := GlobalTheory.Mem.ChiDet.tildeQ_detPt_eq_chiId B.R B.host _ I.C _ _ _ _ I.SQ p.1.1 h1
  have c2 := GlobalTheory.Mem.ChiDet.tildeQ_detPt_eq_chiId B.R B.host _ I.C _ _ _ _ I.SQ p'.1.1 h1
  have m1 := map_muInvDet_pt I h a u ⟨i, hi⟩ p.1.1
  have m2 := map_muInvDet_pt I h a u ⟨i, hi⟩ p'.1.1
  show ((rhoAt I.SQ I.C (I.xi a) i p.1.1 : ℂˣ) : ℂ) * ((rhoAt' I.SQ I.C (I.xi a) i p'.1.1 : ℂˣ) : ℂ) =
    B.embLL _ * (Th.chiFac B.host (chiId I.C.chiPsi) _ _ p.1.1.deco.1.N p'.1.1.deco.1.N)⁻¹
  rw [map_mul, map_inv₀, m1, m2, e1, e2, Th.chiFac, ← c1, ← c2]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, zpow_neg, mul_inv, inv_inv]
  ring

abbrev trueIn (a : I.ι) (u : B.Word) (Tp : TopLev B.fields (B.primes X) B.R (I.Q a)) : ChainIn B.fields.E B.fields.K B.fields.Tau B.R :=
  chainAt (Pr := B.primes X) I.sel (I.tup a) (I.cst a) (I.idx a) Tp u (fun i _ p => ((rhoAt I.SQ I.C (I.xi a) i p.1.1 : ℂˣ) : ℂ))
    (fun i _ p => ((rhoAt' I.SQ I.C (I.xi a) i p.1.1 : ℂˣ) : ℂ)) I.A.cD (thAt (Pr := B.primes X) I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u)

def KmapIs {D : D7} {u : D.what₂.Word} (Y : Dat D u) (i : ℕ) (k : Y.Ker i) : Prop :=
  ∀ c c' F, Y.ch.C.Kmap i c c' (Y.ev i F) = Y.ev (i + 1) (k c.1 c'.1 ((Y.I.S i).rep c) ((Y.I.S (i + 1)).rep c') F)

theorem laHyp_of_vecP (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W) (G : GJStage B C)
    (h : I.Ok) (hv : (I.J.toRec B C W V S N G).VecP I.chi) (a : I.ι) (u : B.Word) (i j : ℕ) :
    I.A.LaHyp (B.R.N i) (B.R.N j) (I.Sb a u) ∧ I.A.ESmooth (B.R.N i) (B.R.N j) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have he : ∀ k, Even (B.R.N k) := fun k => by
    obtain ⟨c, hc⟩ := N_even B.R k
    exact ⟨c, by omega⟩
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem
  obtain ⟨hL, hE⟩ := GlobalTheory.ThetaMove.LatticeFacts.laHyp_and_eSmooth _ _ (seamOf B C W V S N G) ⊤ I.J.δ (I.J.toRec B C W V S N G) I.chi I.J.cD
    _ _ hX (seamOf_ok B C W V S N G) ⟨top_ne_bot, by simp⟩ ((I.J.ok_iff B C W V S N G).1 h.amb_ok).1 hv (he i) (he j)
  rw [ColIn.A, AmbIn.amb_eq_ambOf B C W V S N G]
  exact ⟨⟨hL.1, hL.2.1, fun P hP => (bad P hP).1, fun P hP => GlobalTheory.PeriodIdealUnit.locP_AA_eq_one _ _ _ _ _ _ _ _ P (bad P hP).2.1
    (bad P hP).2.2.1 (by simp), hL.2.2.2.2⟩, hE⟩

end True

end GlobalTheory.LvT.Built.KMap

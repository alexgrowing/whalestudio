import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtPosDef
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHermitianFormScaledCoordinateEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameCoordsOfMemTorusLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePointSignEqThetaLawSemicharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualImageOrthonormalFrameLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

noncomputable section
namespace GlobalTheory.ThetaLawMoved
variable {D : D7}

theorem gen_mem {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (a : D.host.E) (ha : a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)) (s : Fin S.rank → D.host.E) (hs : s ∈ Ls)
    (t : Fin T.rank → D.host.E) (ht : t ∈ Lt) :
    GlobalTheory.VacUnique.finRat S T (frT.1 * (a • Matrix.vecMulVec t (star s)) * (frS⁻¹).1) ∈
      latO S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) (fun _ => True) := by
  refine AddSubgroup.subset_closure ⟨1, GlobalTheory.ThetaLawLat.one_mem_intAf', fun v h => (h trivial).elim, a, ha,
    frS.1 *ᵥ s, ⟨s, hs, rfl⟩, frT.1 *ᵥ t, ⟨t, ht, rfl⟩, ?_⟩
  ext i j
  show (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (frT.1 * (a • Matrix.vecMulVec t (star s)) * (frS⁻¹).1) i j = _
  rw [Matrix.of_apply]
  congr 1
  rw [GlobalTheory.ThetaLawLat.inv_frame frS hS]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mulVec,
    dotProduct, Pi.star_apply, star_sum, star_mul', Finset.mul_sum, Finset.sum_mul, smul_eq_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem finRat_frame_mem_latO_sd {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hLs : Formalism.MainNotions.StandardLatticesGL3.SD D Ls) (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (hz : z ∈ GlobalTheory.InertSign.RL D D.host.ccK Ls Lt) :
    GlobalTheory.VacUnique.finRat S T (frT.1 * z * (frS⁻¹).1) ∈
      latO S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) (fun _ => True) := by
  obtain ⟨r, s, u, hs, hu, hsu⟩ := GlobalTheory.T.self_dual_lattice_resolution_of_identity Ls hLs
  have hA : ∀ a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E), ∀ A ∈ Formalism.MainNotions.TaylorLogMetric.homL D Ls Lt,
      GlobalTheory.VacUnique.finRat S T (frT.1 * (a • A) * (frS⁻¹).1) ∈
        latO S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) (fun _ => True) := by
    intro a ha A hA
    have eA : A = ∑ k, Matrix.vecMulVec (A *ᵥ s k) (star (u k)) := by
      conv_lhs => rw [← Matrix.mul_one A, ← hsu]
      ext i j
      simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [eA, Finset.smul_sum, Matrix.mul_sum, Matrix.sum_mul, map_sum]
    exact AddSubgroup.sum_mem _ fun k _ => gen_mem frS frT hS Ls Lt a ha (u k) (hu k) (A *ᵥ s k)
      (GlobalTheory.ThetaLatImage.mem_homL.1 hA _ (hs k))
  have hI : ∀ t ∈ GlobalTheory.InertSign.Iid D D.host.ccK, t ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨c, hc, a, ha, rfl⟩ := ht
      have hc' : ((c : D.host.K) : D.host.E) ∈ (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
        FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) hc)
      exact FractionalIdeal.mul_mem_mul hc' ha
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul o x _ hx => exact Submodule.smul_mem _ o hx
  suffices h : ∀ o : 𝓞 D.host.E, GlobalTheory.VacUnique.finRat S T (frT.1 * (o • z) * (frS⁻¹).1) ∈
      latO S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) (fun _ => True) by
    have := h 1
    rwa [one_smul] at this
  induction hz using Submodule.span_induction with
  | mem z hz =>
    intro o
    obtain ⟨t, ht, A, hA', rfl⟩ := hz
    rw [← smul_assoc]
    exact hA _ (Submodule.smul_mem _ o (hI t ht)) A hA'
  | zero => intro o; rw [smul_zero, Matrix.mul_zero, Matrix.zero_mul, map_zero]; exact zero_mem _
  | add x y _ _ hx hy =>
    intro o
    rw [smul_add, Matrix.mul_add, Matrix.add_mul, map_add]
    exact add_mem (hx o) (hy o)
  | smul o' x _ hx => intro o; rw [smul_smul]; exact hx _

theorem mem_La_frame_sd {D : D7} (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1)
    (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hLs : Formalism.MainNotions.StandardLatticesGL3.SD D Ls) (δ : ℂ) (x : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank)
    (hx : x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt) :
    ∃ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T v ∈
      latO S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) (fun _ => True) ∧
      x = δ • (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) *
        GlobalTheory.FockPos.frAt frS τ) a b) := by
  obtain ⟨z, hz, rfl⟩ := GlobalTheory.ThetaLatImage.La_sub hx
  refine ⟨frT.1 * z * (frS⁻¹).1, finRat_frame_mem_latO_sd frS frT hS Ls Lt hLs z hz, ?_⟩
  have hmap : ∀ τ, Matrix.of (GlobalTheory.VacUnique.infRat S T (frT.1 * z * (frS⁻¹).1) τ) =
      GlobalTheory.FockPos.frAt frT τ * Matrix.of (fun i j => tauE D τ (z i j)) * (GlobalTheory.FockPos.frAt frS τ)⁻¹ := by
    intro τ
    have hi : (GlobalTheory.FockPos.frAt frS τ)⁻¹ = (frS⁻¹).1.map (tauE D τ) := by
      refine Matrix.inv_eq_right_inv ?_
      rw [GlobalTheory.FockPos.frAt, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hi]
    show (frT.1 * z * (frS⁻¹).1).map (tauE D τ) = _
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  funext τ a b
  rw [GlobalTheory.ThetaLatImage.pt_apply]
  show _ = δ * ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T (frT.1 * z * (frS⁻¹).1) τ) *
    GlobalTheory.FockPos.frAt frS τ) a b
  rw [hmap τ, GlobalTheory.ThetaLawOF.coord_back frS frT (fun τ i j => tauE D τ (z i j)) τ]
  rfl

section
open GlobalTheory.ThetaSignLat

theorem sign_eq_alpha_sd : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ δ : ℂ, δ ≠ 0 → ∀ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T v ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∀ ε : ℂ, (∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) g → heisO ψ S T (GlobalTheory.VacUnique.finRat S T (-v)) g = ε • g) → ψ (-symplOH S T (ratW T S v) (GlobalTheory.VacUnique.finRat S T (-v))) * ε = Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b)) := by
  intro D ψ S T frS frT hS hT hψ ΛS ΛT hSd hTd δ hδ v hv ε hε
  set L := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (fun _ => True) with hL
  set u : WO S T := GlobalTheory.VacUnique.finRat S T (-v) with hu
  have huL : u ∈ L := by
    rw [hu, map_neg]; exact L.neg_mem hv

  have hsq := D.host.sqd_sq
  let b : 𝓞 D.host.E := ⟨(1 + D.host.sqrtMinusD) / 2,
    GlobalTheory.NormSum.isIntegral_half_one_add D.host.d D.host.hyp.2.2.2.1 _ hsq⟩
  have hbv : (b : D.host.E) = (1 + D.host.sqrtMinusD) / 2 := rfl
  have h2s : star (2 : D.host.E) = 2 := by
    have := star_natCast (R := D.host.E) 2
    exact_mod_cast this
  have hbs : star (b : D.host.E) = 1 - (b : D.host.E) := by
    rw [hbv, star_div₀, star_add, star_one, h2s, GlobalTheory.FockCompare.RealChart.star_sqrtMinusD]
    ring
  have hb : (b : D.host.E) + star (b : D.host.E) = 1 := by rw [hbs]; ring
  obtain ⟨χ, hχ, hval⟩ := GlobalTheory.ThetaSignLat.semichar_value ψ S T ΛS ΛT hψ hSd hTd b hb
  obtain ⟨f1, -, f3, -⟩ := GlobalTheory.T.homSymplecticHalfForm_algebraic_laws_continuous D S T
  have hz : ∀ w : WO S T, symplOH S T 0 w = 0 := fun w => by
    have := f1 0 0 w
    rw [add_zero] at this
    exact left_eq_add.1 this
  have e1 : ∀ g : WO S T → ℂ, heisO ψ S T u g 0 = g u := fun g => by
    show ψ (symplOH S T 0 u) * g (0 + u) = g u
    rw [hz, AddChar.map_zero_eq_one, one_mul, zero_add]
  have e0 : χ 0 = 1 := by
    rw [hval 0 (zero_mem _)]
    have : ((0 : WO S T).map fun z => incA D (b : D.host.E) * z) = 0 := by
      funext i j; exact mul_zero _
    rw [this, f3, AddChar.map_zero_eq_one]
  have hεu : ε = χ u := by
    have := congrFun (hε χ hχ) 0
    rw [e1] at this
    rw [this, Pi.smul_apply, e0, smul_eq_mul, mul_one]
  have hpm : ε = 1 ∨ ε = -1 := by
    obtain ⟨ε', h1, h2⟩ := (GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hSd hTd).2.2 χ hχ u huL
    have := congrFun (h2 χ hχ) 0
    rw [e1, Pi.smul_apply, e0, smul_eq_mul, mul_one] at this
    rw [hεu, this]; exact h1

  set Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E := (frT⁻¹ : GL (Fin T.rank) D.host.E).1 * v * frS.1 with hY
  set n : D.host.E := ∑ a, ∑ b, star (Y a b) * Y a b with hn
  have hns : star n = n := by
    rw [hn, star_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [star_mul', star_star, mul_comm]
  have hmap : (u.map fun z => incA D (b : D.host.E) * z) =
      GlobalTheory.LatVac.finTens 1 (Matrix.of fun i j => (b : D.host.E) * (-v) i j) := by
    funext i j
    show ((1 : AF D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((-v) i j)) =
      pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((b : D.host.E) * (-v) i j)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hu' : u = GlobalTheory.LatVac.finTens 1 (-v) := rfl
  have hs : symplOH S T (u.map fun z => incA D (b : D.host.E) * z) u = pairA D.host.F 0
      (algebraMap D.host.F (Af D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)))) := by
    rw [hmap, hu', symplOH, GlobalTheory.LatVac.symplO_finTens, hRat_smul_left, hRat_neg_neg,
      GlobalTheory.ThetaSignLat.hRat_frame S T frS frT hS hT v]
    refine Prod.ext (mul_zero _) ?_
    show algebraMap D.host.F (Af D.host.F) (1 / 2) * (1 * 1 * _) = _
    rw [one_mul, one_mul, ← RingHom.map_mul]
    rfl

  have hq := trace_val n (b : D.host.E) hns hbv
  have hχu : χ u = Complex.exp (2 * Real.pi * Complex.I * ∑ τ, tauE D τ
      ((1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)) : D.host.F) : D.host.E)) := by
    rw [hval u huL, hs, GlobalTheory.ThetaSignLat.psi_fin_rat ψ hψ]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ∑ τ, tauE D τ n := ⟨_, rfl⟩
  have hsumq : ∑ τ, tauE D τ
      ((1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)) : D.host.F) : D.host.E) =
        -c / (2 * (Ideal.absNorm D.host.ccK : ℂ)) := by
    have : ∀ τ, tauE D τ
        ((1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)) : D.host.F) : D.host.E) =
          -(tauE D τ n) / (2 * (Ideal.absNorm D.host.ccK : ℂ)) := fun τ => by
      rw [hq, map_div₀, map_neg, map_mul, map_natCast, map_ofNat]
    rw [Finset.sum_congr rfl fun τ _ => this τ, ← Finset.sum_div, Finset.sum_neg_distrib, hc]
  have hcre : ((c.re : ℝ) : ℂ) = c := by
    have : starRingEnd ℂ c = c := by
      rw [hc, map_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← GlobalTheory.FockCompare.tauE_star, hns]
    exact Complex.conj_eq_iff_re.1 this
  obtain ⟨hxi, hN1, hd1⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  have hNC : (Ideal.absNorm D.host.ccK : ℂ) ≠ 0 := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := by
      intro h0; rw [h0, Nat.cast_zero] at hN1; linarith
    exact_mod_cast this
  have hNR : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0 := by linarith
  have hdR : Real.sqrt D.host.d ≠ 0 := by linarith
  have hεt : ε = Complex.exp (-(Real.pi : ℂ) * Complex.I * ((c.re / Ideal.absNorm D.host.ccK : ℝ) : ℂ)) := by
    rw [hεu, hχu, hsumq]
    congr 1
    push_cast
    rw [hcre]
    field_simp
  have hX : (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) *
      GlobalTheory.FockPos.frAt frS τ) a b) = fun τ a b => tauE D τ (Y a b) := by
    funext τ a b
    rw [coord_entry]
    rfl
  have hsum : (∑ τ, ∑ a, ∑ b, tauE D τ (Y a b) * starRingEnd ℂ (tauE D τ (Y a b))) = c := by
    rw [hc]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hn, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, GlobalTheory.FockCompare.tauE_star, mul_comm]
  have h0 := GlobalTheory.RatFinIso.symplOH_ratW_finRat_neg S T v
  rw [← hu] at h0
  rw [h0, neg_zero, AddChar.map_zero_eq_one, one_mul, hX, Formalism.MainNotions.TaylorLogMetric.al, GlobalTheory.ThetaLawOF.torusHermitianForm_scaled_coordinate_eq hδ, hsum]
  have hre : Real.sqrt D.host.d / 2 * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c).re = c.re / Ideal.absNorm D.host.ccK := by
    rw [show (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c) = ((2 * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c by push_cast; ring,
      Complex.re_ofReal_mul, hxi]
    field_simp
  rw [hre, hεt]
  exact (GlobalTheory.ThetaSignLat.sign_of_exp _ (by rw [← hεt]; exact hpm)).symm

end

section
open GlobalTheory.ThetaLawOF

theorem theta_of_vacuum_moved : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Formalism.MainNotions.StandardLatticesGL3.SD D Ls → Formalism.MainNotions.StandardLatticesGL3.SD D Lt → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → (fun Y => Φ (δ⁻¹ • Y)) ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt := by
  intro D ψ θ S T frS frT hS hT δ hC hδ Ls Lt hLs hLt f hf Φ hΦd hΦ
  obtain ⟨ΛS, hΛS, hSd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV S frS hS Ls hLs
  obtain ⟨ΛT, hΛT, hTd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV T frT hT Lt hLt
  rw [← hΛS, ← hΛT] at hf
  have hψ := hf.1
  have hθ := hf.2.inf
  obtain ⟨σ, hch⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, -, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hSd hTd
  refine ⟨hΦd.comp ((differentiable_id).const_smul δ⁻¹), ?_⟩
  intro x hx Y
  obtain ⟨v, hv, rfl⟩ := mem_La_frame_sd S T frS frT hS hT Ls Lt hLs δ x hx
  rw [← hΛS, ← hΛT] at hv
  have hv' : GlobalTheory.VacUnique.finRat S T (-v) ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) := by
    rw [AddMonoidHom.map_neg]; exact neg_mem hv
  obtain ⟨ε, -, hε⟩ := h3 f hf.2.lat _ hv'
  have hsign := sign_eq_alpha_sd ψ S T frS frT hS hT hψ ΛS ΛT hSd hTd δ hδ v hv ε (fun g hg => hε g hg)
  have hlaw := GlobalTheory.VacUnique.apply_add_infRat hch hψ hf.2.theta v (hε f hf.2.lat)
  set X : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b with hX
  set Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := δ⁻¹ • Y with hZ
  have hZY : Y = δ • Z := by rw [hZ, smul_smul, mul_inv_cancel₀ hδ, one_smul]
  set z : GlobalTheory.FockCompare.RW T S := fun τ => GlobalTheory.FockPos.frAt frT τ * Matrix.of (Z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹ with hz
  have hzτ : ∀ τ, (GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (z τ) * GlobalTheory.FockPos.frAt frS τ = Matrix.of (Z τ) :=
    fun τ => coord_back frS frT Z τ
  have hz1 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S z) = Z := by
    rw [zCo_iota hch]; funext τ; exact coord_back frS frT Z τ
  have hz2 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S (z + GlobalTheory.VacUnique.infRat S T v)) = Z + X := by
    rw [zCo_iota hch]; funext τ
    show (GlobalTheory.FockPos.frAt frT τ)⁻¹ * (Matrix.of (z τ) + Matrix.of (GlobalTheory.VacUnique.infRat S T v τ)) * GlobalTheory.FockPos.frAt frS τ = Z τ + X τ
    rw [Matrix.mul_add, Matrix.add_mul, hzτ τ]
    rfl
  have hom : GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T v) z = ∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re := by
    rw [omO_frame frS frT hS hT]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hzτ τ]
    rfl
  have hl := hlaw z
  rw [hΦ _ (hch.real_iota T S _), hΦ _ (hch.real_iota T S _), GlobalTheory.FockPos.gaussO, GlobalTheory.FockPos.gaussO, hz1, hz2, hom, hsign] at hl

  simp only [Formalism.MainNotions.TaylorLogMetric.U]
  have e1 : δ⁻¹ • (Y + δ • X) = Z + X := by rw [smul_add, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  rw [e1, hZY, torusHermitianForm_scaled_coordinate_eq hδ, torusHermitianForm_scaled_coordinate_eq hδ]
  have hZZ : δ⁻¹ • δ • Z = Z := by rw [smul_smul, inv_mul_cancel₀ hδ, one_smul]
  rw [hZZ]
  set a := Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X) with ha
  have kE : Complex.exp (-(Real.pi * Complex.I) * ((-∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re : ℝ) : ℂ)) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) =
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := entry (Z τ i j) (X τ i j) (Formalism.L2.Pj.xiR D)
    push_cast at h ⊢
    linear_combination h
  apply mul_left_cancel₀ (Complex.exp_ne_zero (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)))
  rw [← kE]
  calc _ = a * Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) *
        (Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) * Φ (Z + X)) := by
        rw [kE]; ring
    _ = _ := by
        rw [hl]
        have := al_mul_self (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X)
        rw [← ha] at this
        linear_combination (Complex.exp (-(Real.pi * Complex.I) * ((-∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re : ℝ) : ℂ)) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) * Φ Z) * this

end

end GlobalTheory.ThetaLawMoved

end

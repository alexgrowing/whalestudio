import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.DatumK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutDef
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutLat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutTrace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutProd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FiniteLatticeThetaInvariant
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FiniteLatticeThetaSupport
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FiniteLatticeThetaLevel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LintegralEnormSqLatRepApplyEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutProdA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.StandardAdditiveCharacterSign
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsChartArchimedeanFamily
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutReal

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
namespace UpperTheory.TP.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
variable {η κ χS χT : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}
open GlobalTheory.FinLatSplitF in
theorem splitK_k (hI : IdxSign) (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hL : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hκ : IsKap σ lam κ) {e : AEF F E} (he : IsSplitIdemF σ e) {g k} (hg : SuppAtF σ e JS g) (hk : SuppAtF σ e JT k) {x y}
    (hx : IsDetAtF σ e JS g x) (hy : IsDetAtF σ e JT k y) : ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        ℓ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ f) →
      ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, ℓ (Om (g, k) f) = ((κ x ^ nT * κ y ^ nS : Circle) : ℂ) * ((r : ℂ) * ℓ f) := by
  have hB := C.good
  have hS := C.hS
  have hT := C.hT
  have hξ := C.hξ
  have hσ : ∀ x, σ (σ x) = x := conj_conj_of_cm hB.cm
  have he' : IsSplitIdemF σ (cAF σ e) := isSplitIdemF_conj he
  have hm : ∀ (a b : AEF F E) (x : XFF F E nS nT), mulFF a (mulFF b x) = (a * b) • x := fun a b x => smul_smul a b x
  have hcm : ∀ (a : AEF F E) (x : XFF F E nS nT),
      rhoFF σ JS JT (g, k) (mulFF a x) = mulFF a (rhoFF σ JS JT (g, k) x) :=
    fun a x => XFF.ext (actOF_smul _ _ _ _)
  obtain ⟨n, hn, hℓ⟩ := GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner_eq (isHeis_opFF hσ hS hT hξ hc hL.hw) lam _ hL.sd hL.span (rhoFF σ JS JT (g, k))
    (gamFF_rhoFF hS ξ₀ B.ψ _) (hL.sd' _) (hL.fin _) (Om (g, k)) (hL.op _) (hL.vac _) (mulFF e) (mulFF (cAF σ e))
    (fun x => by rw [hm, he.1]; rfl) (fun x => by rw [hm, he'.1]; rfl)
    (fun x => by rw [hm, he.2.1, zero_smul]) (fun x => by rw [hm, mul_comm, he.2.1, zero_smul])
    (fun x y => by rw [gamFF, gamFF, coe_mulFF, coe_mulFF, symplOF_smul σ JS JT hσ])
    (fun a ha => (hL.splitStab e he a ha).1) (fun a ha => (hL.splitStab e he a ha).2) (hcm e) (hcm _)
    (fun x => XFF.ext (by
      have := off_smul_actOF hg hk (x : WOF F E nS nT)
      rw [sub_smul, sub_smul, add_smul, add_smul, one_smul, one_smul, ← sub_sub, ← sub_sub] at this
      exact this))
  have hi := hL.fin (g, k)
  have hl := hI F E σ hB.cm nS nT JS JT hS hT ξ₀ hξ B.ψ hc w hL.hw Λ hG hL.sd' hL.fin lam hL.good κ hκ e he g k hg hk x y hx hy
  refine ⟨(Real.sqrt (idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, k))) : ℕ))⁻¹ * n,
    mul_pos (inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hi)))) (Nat.cast_pos.2 hn),
    fun ℓ h1 f => ?_⟩
  have := hℓ (ℓ ∘ₗ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ).subtype) (fun u m => by
    have hu : ((mulFF (cAF σ e) u : XFF F E nS nT) : WOF F E nS nT) ∈ GlobalTheory.SplitInvFormF.conjHalf σ e nS nT :=
      fun i j => by
        show cAF σ e * (cAF σ e * (u : WOF F E nS nT) i j) = cAF σ e * (u : WOF F E nS nT) i j
        rw [← mul_assoc, he'.1]
    have hwu : (intAF F w • ((mulFF (cAF σ e) u : XFF F E nS nT) : WOF F E nS nT)) ∈
        GlobalTheory.SplitInvFormF.conjHalf σ e nS nT := fun i j => by
      show cAF σ e * (intAF F w * (cAF σ e * (u : WOF F E nS nT) i j)) =
        intAF F w * (cAF σ e * (u : WOF F E nS nT) i j)
      rw [mul_left_comm, ← mul_assoc (cAF σ e), he'.1]
    show ℓ (opFF hc w (mulFF (cAF σ e) u) m : WOF F E nS nT → ℂ) = ℓ m
    rw [coe_opFF, phaseF, GlobalTheory.SplitInvFormF.symplOHF_half he hwu hu, neg_zero, AddChar.map_zero_eq_one, one_smul]
    exact h1 _ hu _ m.2) f
  have hz : ∀ z : Circle, z * z = 1 → ((z : ℂ))⁻¹ = z := fun z hz => by
    rw [← Circle.coe_inv, inv_eq_of_mul_eq_one_right hz]
  rw [hl, mul_inv, hz _ (by rw [mul_mul_mul_comm, ← mul_pow, ← mul_pow, hκ.sq, hκ.sq, one_pow, one_pow, one_mul])] at this
  refine this.trans ?_
  generalize ((κ x ^ nT * κ y ^ nS : Circle) : ℂ) = c
  push_cast
  show _ * (ℓ (f : WOF F E nS nT → ℂ)) = _
  ring
theorem existsFinK_k (hI : IdxSign) (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (h1 : IsHeckeCharF η) (h2 : ResEtaF η 1) (hκ : IsKap σ lam κ) (hε : IsHalfF σ ε) :
    ∃ of, IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of ∧
      ∀ p (f : thetaSubF σ JS JT ξ₀ B.ψ), of p f = (zF σ JS JT (η * κ) ε hε.idem p : ℂ) • (Om p f : WOF F E nS nT → ℂ) := by
  have hcn : ∀ n : ℕ, Continuous ((η * κ) ^ n : (AEF F E)ˣ →* Circle) := fun n =>
    ((h1.1.mul hκ.cont).pow n).congr fun x => by simp
  have h2' := resEta_mul h2 hκ
  have hB := C.good
  have hreal := _root_.GlobalTheory.T.finite_lattice_theta_invariant F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hheis := _root_.GlobalTheory.T.finite_lattice_theta_support F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hcont := _root_.GlobalTheory.T.finite_lattice_theta_level F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hunit := _root_.GlobalTheory.T.lintegral_enorm_sq_latRep_apply_eq F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  let z : GAF σ JS × GAF σ JT → Circle := zF σ JS JT (η * κ) ε hε.idem
  have z1 : z 1 = 1 := by simp [z, zF]
  have z2 : ∀ p q, z (p * q) = z p * z q := fun p q => by
    simp only [z, zF, Prod.fst_mul, Prod.snd_mul, map_mul, _root_.mul_inv]
    exact mul_mul_mul_comm _ _ _ _
  have z3 : Continuous z := by
    show Continuous fun p : GAF σ JS × GAF σ JT =>
      (((η * κ) ^ nT) (GlobalTheory.SplitDetCharF.cutDet σ JS ε hε.idem p.1))⁻¹ * ((η * κ) ^ nS) (GlobalTheory.SplitDetCharF.cutDet σ JT ε hε.idem p.2)
    exact ((hcn nT).comp ((GlobalTheory.SplitDetCharF.continuous_cutDet ε hε.idem).comp continuous_fst)).inv.mul
      ((hcn nS).comp ((GlobalTheory.SplitDetCharF.continuous_cutDet ε hε.idem).comp continuous_snd))
  obtain ⟨om, hom⟩ := exists_extend (thetaSubF σ JS JT ξ₀ B.ψ)
    ({ toFun := fun p => (z p : ℂ) • Om p
       map_one' := by rw [z1, Circle.coe_one, one_smul, map_one]
       map_mul' := fun p q => by rw [z2, map_mul, Circle.coe_mul, smul_mul_smul_comm] } :
      GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ))
  have ho : ∀ p f (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f),
      om p f = (z p : ℂ) • (Om p ⟨f, hf⟩ : WOF F E nS nT → ℂ) :=
    fun p f hf => hom p ⟨f, hf⟩
  refine ⟨om, ⟨⟨fun p f hf => ?_, fun f hf u => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩, fun g hg k hk f hf => ?_,
    fun g hg k hk u f hf => ?_, fun e he g k hg hk x y hx hy => ?_⟩, fun p f => hom p f⟩
  · rw [ho p f hf]
    exact (thetaSubF σ JS JT ξ₀ B.ψ).smul_mem _ (Om p ⟨f, hf⟩).2
  · simp only [ho _ f hf, Pi.smul_apply, smul_eq_mul]
    exact (continuous_subtype_val.comp z3).mul (hcont ⟨f, hf⟩ u)
  · rw [← hunit μ 𝓕 hμ h𝓕 p ⟨f, hf⟩, ho p f hf]
    refine lintegral_congr fun u => ?_
    rw [Pi.smul_apply, enorm_smul, ← ofReal_norm_eq_enorm (z p : ℂ), Circle.norm_coe, ENNReal.ofReal_one, one_mul]
  · rw [ho _ f hf, hreal g hg k hk, show z (g, k) = 1 by
      simp [z, zF, GlobalTheory.SplitDetCharF.cutDet_real ε hε.idem hε.fin g hg, GlobalTheory.SplitDetCharF.cutDet_real ε hε.idem hε.fin k hk],
      Circle.coe_one, one_smul]
  · have hf' := GlobalTheory.T.heisenbergOperatorF_preserves_isThetaFunction F E σ nS nT JS JT ξ₀ B.ψ hB.std.1 u f hf
    rw [ho _ f hf, ho _ _ hf', heisOF_smul, hheis g hg k hk u ⟨f, hf⟩ ⟨_, hf'⟩ rfl]
  · obtain ⟨r, hr, h1⟩ := _root_.UpperTheory.TP.W.splitK_k hI C hG hO hκ he hg hk hx hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    rw [ho _ f hf, map_smul, h1 ℓ hℓ, smul_eq_mul,
      show z (g, k) = splitFacOF (η ^ nS) (η ^ nT) x y * (κ x ^ nT * κ y ^ nS)⁻¹ by
        simp only [z, zF, splitFacOF, _root_.PositivityTheory.ThKW.cut_char_k hB C.hS (resEtaF_pow h2' nT) hε he hg hx,
          _root_.PositivityTheory.ThKW.cut_char_k hB C.hT (resEtaF_pow h2' nS) hε he hk hy]
        have e1 : (κ y ^ nS)⁻¹ = κ y ^ nS := inv_eq_of_mul_eq_one_right (by rw [← mul_pow, hκ.sq, one_pow])
        simp only [MonoidHom.pow_apply, MonoidHom.mul_apply, mul_pow, _root_.mul_inv, e1]
        exact mul_mul_mul_comm _ _ _ _, Circle.coe_mul, Circle.coe_inv, mul_assoc,
      inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]
    ring
structure PartsK_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hc : HeisClosedF σ JS JT ξ₀ B.ψ) (lam : ℕ →* ℂ)
    (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)) (η χS χT : (AEF F E)ˣ →* Circle) (ε : AEF F E)
    (of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop where
  res : ResEtaF η 1
  half : IsHalfF σ ε
  prod : ∀ (x : E) (k : ℕ), x ≠ 0 → (k : ℚ) = |Algebra.norm ℚ x| → ∀ y : (AEF F E)ˣ,
      (y : AEF F E) = (ε + cAF σ ε) * incAF F E x + (1 - (ε + cAF σ ε)) →
        ∃ r : ℝ, 0 < r ∧ (η y : ℂ) * lam k * ∏ v, tauB B v x = r
  hf : IsFinWeilF σ JS JT ξ₀ B.ψ χS χT of
  hof : ∀ p (f : thetaSubF σ JS JT ξ₀ B.ψ), of p f = (zF σ JS JT η ε half.idem p : ℂ) • (Om p f : WOF F E nS nT → ℂ)
  hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi
  vac : ∀ s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ, s * s = 1 → (HMF JS JT ξ₀ (tauB B) * s).PosDef → ∀ p,
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsVacF σ JS JT ξ₀ B.ψ ι s f →
        oi p f = GlobalTheory.RealWeil.dP s (mMF σ JS JT θ p) • f
theorem PartsK_k.prod' {C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι} (P : _root_.UpperTheory.TP.W.PartsK_k C hc lam Om η χS χT ε of oi) {N x : E} (hN : N ≠ 0) (hx : x ≠ 0)
    {c n : ℕ} (h : ((c * n : ℕ) : ℚ) = |Algebra.norm ℚ (N * x)|) : ∃ r : ℝ, 0 < r ∧
      (η (cutRat _ (_root_.PositivityTheory.ThKW.half_add_k C.good P.half) (Units.mk0 _ hN * Units.mk0 _ hx)) : ℂ) * (lam c * lam n) *
        ((∏ v, tauB B v N) * ∏ v, tauB B v x) = r := by
  obtain ⟨r, p, e⟩ := P.prod _ _ (mul_ne_zero hN hx) h (cutRat _ (_root_.PositivityTheory.ThKW.half_add_k C.good P.half) (Units.mk0 _ hN * Units.mk0 _ hx))
    (by rw [cutRat_val, add_comm, Units.val_mul, Units.val_mk0, Units.val_mk0])
  refine ⟨r, p, ?_⟩
  rw [← e, map_mul lam, ← Finset.prod_mul_distrib]
  simp only [map_mul]
theorem PartsK_k.kappa {C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι} (P : _root_.UpperTheory.TP.W.PartsK_k C hc lam Om η χS χT ε of oi)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) {g : GAF σ JS} {h : GAF σ JT}
    (hcm : s * mMF σ JS JT θ (g, h) = mMF σ JS JT θ (g, h) * s) {c : ℂ} (hc0 : c ≠ 0) (H : IsScalarF B ξ₀ of oi (g, h) c)
    (f : thetaSubF σ JS JT ξ₀ B.ψ) (f1 : Fixes (opFF hc w) (latF F E nS nT Λ) f) (f2 : IsVacF σ JS JT ξ₀ B.ψ ι s f)
    (x : WOF F E nS nT) :
    (f : WOF F E nS nT → ℂ) (actOF σ JS JT g⁻¹ h⁻¹ x) = (c⁻¹ * GlobalTheory.RealWeil.dP s (mMF σ JS JT θ (g, h)) *
      zF σ JS JT η ε P.half.idem (g, h) *
      (lam (idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)))))⁻¹) *
      ((sumOp (opFF hc w) (latF F E nS nT Λ)
        ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) f : thetaSubF σ JS JT ξ₀ B.ψ) : WOF F E nS nT → ℂ) x := by
  have e1 := congrFun (H f f.2) x
  rw [P.vac s hs.sq hs.pos (g, h) hcm f f.2 f2, map_smul, P.hof, hO.vac _ f f1, normOp, Submodule.coe_smul] at e1
  simp only [Pi.smul_apply, smul_eq_mul, substF_apply] at e1
  rw [← one_mul (f.1 _), ← inv_mul_cancel₀ hc0, mul_assoc, ← e1]
  ring
theorem scalar_constK_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) (P : _root_.UpperTheory.TP.W.PartsK_k C hc lam Om η χS χT ε of oi) (hs : CartF σ JS JT ξ₀ B θ s) :
    ∃ e s₀ : ℂ, s₀ ≠ 0 ∧ ∀ g h a b, IsRatF σ JS g a → IsRatF σ JT h⁻¹ b →
      s * mMF σ JS JT θ (g, h) = mMF σ JS JT θ (g, h) * s → (b ⊗ₖ aᵀ - 1).det ≠ 0 →
      ∀ c : ℂ, c ≠ 0 → IsScalarF B ξ₀ of oi (g, h) c → ∃ r : ℝ, 0 < r ∧ c * e = r * s₀ := by
  refine ⟨(-s).det, η (cutRat ε P.half.idem ((-1) ^ Fintype.card (Fin nT × Fin nS))), Circle.coe_ne_zero _,
    fun g h a b ha hb hcm hd c hc0 H => ?_⟩
  obtain ⟨d1, d2⟩ := _root_.PositivityTheory.ThKW.det_kron_k C ha hb
  have hΔ := left_ne_zero_of_mul_eq_one d1
  obtain ⟨hbij, n, t, c₀, N, M, hn, hc₀, hN, t1, t2, g1, g2, i1, i2⟩ := _root_.PositivityTheory.ThKW.finite_data_k C hG hR hO ha hb hΔ hd
  obtain ⟨hI, hδ0, r₂, p₂, h2⟩ := _root_.PositivityTheory.ThKW.real_data_k C hs ha hb hcm hd
  obtain ⟨r₁, p₁, h1⟩ := _root_.PositivityTheory.ThKW.gauss_mul_integral_k C hG hR hO hs ha hb hbij hI _ (P.kappa hO hs hcm hc0 H) n t t1 t2
  rw [g1] at h1
  have hN' : (N : E) ^ M ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hN)
  obtain ⟨r₃, p₃, h3⟩ := P.prod' hN' hd i1
  obtain ⟨r₄, p₄, h4⟩ := P.prod' hN' hΔ i2
  exact GlobalTheory.RatAut.final_algebra p₁ p₂ p₃ p₄ hn hc0 hδ0 (Circle.coe_ne_zero _) h1 h2 h3 h4 g2
    (_root_.PositivityTheory.ThKW.phase_rat_k C P.res P.half hΔ hd hN' d1 d2 (_root_.PositivityTheory.ThKW.zF_rat_k C P.half.idem ha hb hΔ))
set_option maxHeartbeats 1000000 in
theorem isScalar_one_of_commK_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) (P : _root_.UpperTheory.TP.W.PartsK_k C hc lam Om η χS χT ε of oi) (hs : CartF σ JS JT ξ₀ B θ s)
    {g : GAF σ JS} {h : GAF σ JT} (hg : g ∈ GQF σ JS) (hh : h ∈ GQF σ JT)
    (hcm : s * mMF σ JS JT θ (g, h) = mMF σ JS JT θ (g, h) * s) : IsScalarF B ξ₀ of oi (g, h) 1 := by
  obtain ⟨a, ha⟩ := exists_isRatF hg
  obtain ⟨b, hb⟩ := exists_isRatF (inv_mem hh)
  obtain ⟨e, s₀, hs₀, H⟩ := _root_.UpperTheory.TP.W.scalar_constK_k C hG hR hO P hs
  obtain ⟨t, ht, ht'⟩ := (_root_.PositivityTheory.ThKW.infinite_norm_one_k C).exists_notMem_finite
    ((GlobalTheory.RatAut.finite_det_smul_sub_one (b ⊗ₖ aᵀ)).union (GlobalTheory.RatAut.finite_det_smul_sub_one
      ((1 : Matrix (Fin nT) (Fin nT) E) ⊗ₖ (1 : Matrix (Fin nS) (Fin nS) E)ᵀ)))
  rw [Set.mem_union, not_or] at ht'
  obtain ⟨k, rk⟩ := exists_of_unitary (σ := σ) C.hT (a := t • 1) (by
    have e : ((t • (1 : Matrix (Fin nT) (Fin nT) E)).map σ)ᵀ = σ t • 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
    rw [e, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, show t * σ t = 1 from ht, one_smul])
  have hk := rk.mem
  have hcomm := _root_.PositivityTheory.ThKW.fin_inf_comm_k C hO (fun p => ⟨_, P.hof p⟩) P.hi
  have ck : s * mMF σ JS JT θ (1, k⁻¹) = mMF σ JS JT θ (1, k⁻¹) * s := by
    have := comm_inv (mMF σ JS JT θ) (hs.cen k t rk)
    rwa [Prod.inv_mk, inv_one] at this
  obtain ⟨c, hc1, sc⟩ := _root_.PositivityTheory.ThKW.exists_isScalarF_k (p := (g, h)) C P.hf P.hi hg hh
  obtain ⟨c', hc', sc'⟩ := _root_.PositivityTheory.ThKW.exists_isScalarF_k (p := (1, k⁻¹)) C P.hf P.hi (one_mem _) (inv_mem hk)
  have hc0 : c ≠ 0 := norm_ne_zero_iff.1 (hc1 ▸ one_ne_zero)
  have hc0' : c' ≠ 0 := norm_ne_zero_iff.1 (hc' ▸ one_ne_zero)
  obtain ⟨r', p', e'⟩ := H 1 k⁻¹ 1 (t • 1) (isRatF_one JS) (by rwa [inv_inv]) ck
    (by rw [Matrix.smul_kronecker]; exact ht'.2) c' hc0' sc'
  obtain ⟨r, p, e''⟩ := H (g * 1) (h * k⁻¹) a (t • b) (by rwa [mul_one])
    (by
      have := rk.mul hb
      rwa [Matrix.smul_mul, Matrix.one_mul, ← inv_inv k, ← _root_.mul_inv_rev] at this)
    (by rw [← Prod.mk_mul_mk, map_mul, ← mul_assoc, hcm, mul_assoc, ck, mul_assoc])
    (by rw [Matrix.smul_kronecker]; exact ht'.1) (c * c') (mul_ne_zero hc0 hc0')
    (sc.mul_k C P.hi hcomm sc' (one_mem _) (inv_mem hk))
  have q' : (r' : ℂ) ≠ 0 := by exact_mod_cast p'.ne'
  have e1 : c = ((r / r' : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, eq_div_iff q']
    refine mul_right_cancel₀ hs₀ ?_
    rw [← e'', mul_assoc, ← e', mul_assoc]
  have e2 : r / r' = 1 := by
    rw [e1, Complex.norm_real, Real.norm_of_nonneg (div_pos p p').le] at hc1
    exact hc1
  rwa [e1, e2, Complex.ofReal_one] at sc
theorem datumK_of_k (hK : KapEx) (hE : EtaProdK) (hI : IdxSign) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E), GoodLat Λ → RatSD σ JS JT ξ₀ Λ →
      ∀ (hc : HeisClosedF σ JS JT ξ₀ B.ψ) (w : 𝓞 E) (lam : ℕ →* ℂ)
        (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)), _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
      ∀ η : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF η → ResEtaF η 1 → HasExp B.emb η (fun _ => 1) → UnramInert σ η →
        ∃ ω, IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (η ^ nS) (η ^ nT) ω := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hξ Λ hG hR hc w lam Om hO η h1 h2 h3 h4
  obtain ⟨θ, hθ⟩ := (_root_.GlobalTheory.T.standard_additive_character_sign F E σ B hB).2.1
  obtain ⟨ι, hι⟩ := _root_.GlobalTheory.T.exists_chart_archimedean_family F E σ B hB θ hθ
  have C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι := ⟨hB, hS, hT, h0, hξ, hθ, hι⟩
  obtain ⟨κ, hκ⟩ := hK F E σ hB.cm lam hO.good
  obtain ⟨ε, hε, hprod⟩ := hE F E σ B hB.cm hB.unram η h1 h2 h3 h4 lam hO.good κ hκ
  obtain ⟨of, hf, hof⟩ := _root_.UpperTheory.TP.W.existsFinK_k hI C hG hO h1 h2 hκ hε
  obtain ⟨oi, hi, hvac⟩ := _root_.PositivityTheory.ThKW.exists_inf_k C
  have P : _root_.UpperTheory.TP.W.PartsK_k C hc lam Om (η * κ) (η ^ nS) (η ^ nT) ε of oi := ⟨resEta_mul h2 hκ, hε, hprod, hf, hof, hi, hvac⟩
  have hcomm := _root_.PositivityTheory.ThKW.fin_inf_comm_k C hO (fun p => ⟨_, hof p⟩) hi
  refine _root_.PositivityTheory.ThKW.datum_of_aut_k C hG hO h1 h2 hf (fun p => ⟨_, hof p⟩) hi fun γ hγ γ' hγ' f hf' => ?_
  have := _root_.PositivityTheory.ThKW.rat_gen_k C (fun p => IsScalarF B ξ₀ of oi p 1)
    (fun p q _ _ q1 q2 a b => mul_one (1 : ℂ) ▸ a.mul_k C hi hcomm b q1 q2)
    (fun p s p1 p2 hs hcm => _root_.UpperTheory.TP.W.isScalar_one_of_commK_k C hG hR hO P hs p1 p2 hcm) (γ, γ') hγ hγ' f hf'
  rw [this, one_smul]
  show f (actOF σ JS JT γ⁻¹ γ'⁻¹ 0) = f 0
  rw [actOF, Matrix.mul_zero, Matrix.zero_mul]
end UpperTheory.TP.W
end
end

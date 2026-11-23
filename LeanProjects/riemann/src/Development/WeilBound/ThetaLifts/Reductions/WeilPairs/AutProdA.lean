import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SumFourEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointEqRealMulFiniteBothOrdersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFPreservesIsThetaFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepTrivialRealPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepNormalizesHeisenbergFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepContinuousGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqLatticeModelRepFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepSplitPlacePositiveScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCMStatement

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}

variable {η : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}

theorem cut_char (hB : B.IsGood σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {χ : (AEF F E)ˣ →* Circle} {m : ℕ} (hres : ResEtaF χ m) (hε : IsHalfF σ ε) {e : AEF F E} (he : IsSplitIdemF σ e)
    {g : GAF σ J} {x : (AEF F E)ˣ} (hg : SuppAtF σ e J g) (hx : IsDetAtF σ e J g x) :
    χ (GlobalTheory.SplitDetCharF.cutDet σ J ε hε.idem g) = χ x := by
  rcases hε.split e he with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · rw [GlobalTheory.SplitDetCharF.cutDet_same ε hε.idem a1 a2 hg hx]
  · exact GlobalTheory.SplitDetCharF.char_eq_of_mul_conj hB.cm hres _ x
      (GlobalTheory.SplitDetCharF.cutDet_conj hJ ε hε.idem he.1 a1 a2 hg hx)

theorem exists_fin_A (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (h1 : IsHeckeCharF η)
    (h2 : ResEtaF η 1) (hε : IsHalfF σ ε) : ∃ of, IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of ∧
      ∀ p (f : thetaSubF σ JS JT ξ₀ B.ψ), of p f = (zF σ JS JT η ε hε.idem p : ℂ) • (Om p f : WOF F E nS nT → ℂ) := by
  have hB := C.good
  have hreal := GlobalTheory.T.latticeIntertwinerRep_trivial_realPoints F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hheis := GlobalTheory.T.latticeIntertwinerRep_normalizes_heisenberg_finite F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hcont := GlobalTheory.T.latticeIntertwinerRep_continuous_group F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hunit := GlobalTheory.T.lintegral_sq_latticeModelRep_fundamentalDomain F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hsplit := GlobalTheory.T.latticeIntertwinerRep_splitPlace_positive_scalar F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  let z : GAF σ JS × GAF σ JT → Circle := zF σ JS JT η ε hε.idem
  have z1 : z 1 = 1 := by simp [z, zF]
  have z2 : ∀ p q, z (p * q) = z p * z q := fun p q => by
    simp only [z, zF, Prod.fst_mul, Prod.snd_mul, map_mul, _root_.mul_inv]
    exact mul_mul_mul_comm _ _ _ _
  have z3 : Continuous z := by
    show Continuous fun p : GAF σ JS × GAF σ JT =>
      ((η ^ nT) (GlobalTheory.SplitDetCharF.cutDet σ JS ε hε.idem p.1))⁻¹ * (η ^ nS) (GlobalTheory.SplitDetCharF.cutDet σ JT ε hε.idem p.2)
    exact ((isHeckeCharF_pow h1 nT).1.comp ((GlobalTheory.SplitDetCharF.continuous_cutDet ε hε.idem).comp continuous_fst)).inv.mul
      ((isHeckeCharF_pow h1 nS).1.comp ((GlobalTheory.SplitDetCharF.continuous_cutDet ε hε.idem).comp continuous_snd))
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
  · obtain ⟨r, hr, h1⟩ := hsplit e he g k hg hk
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    rw [ho _ f hf, map_smul, h1 ℓ hℓ, smul_eq_mul,
      show z (g, k) = splitFacOF (η ^ nS) (η ^ nT) x y by
        simp only [z, zF, splitFacOF, cut_char hB C.hS (resEtaF_pow h2 nT) hε he hg hx,
          cut_char hB C.hT (resEtaF_pow h2 nS) hε he hk hy]]
    ring

theorem fin_inf_comm_A (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi) (p q : GAF σ JS × GAF σ JT) (f : WOF F E nS nT → ℂ)
    (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) : of p (oi q f) = oi q (of p f) := by
  obtain ⟨z, hz⟩ := hof p
  have hσ : ∀ x, σ (σ x) = x := LatA.sig_sig C.good
  obtain ⟨a, ha, k, hk, e1, -⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders F E σ nS JS q.1
  obtain ⟨b, hb, l, hl, e2, -⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders F E σ nT JT q.2
  have hoi : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → oi q f = oi (a, b) f := fun f h => by
    rw [show q = (a, b) * (k, l) from Prod.ext e1 e2, map_mul, Module.End.mul_apply, hi.triv k hk l hl f h]
  let L : thetaSubF σ JS JT ξ₀ B.ψ →ₗ[ℂ] thetaSubF σ JS JT ξ₀ B.ψ := (oi q).restrict fun f hf => hi.pres q f hf
  have hL : ∀ m, (L m : WOF F E nS nT → ℂ) = oi q m := fun _ => rfl
  have := congrArg Subtype.val ((LatA.rep hO).comm (LatA.sys hσ C.hS C.hT C.hξ hO) L (fun x v => Subtype.ext (by
    have e3 : actOF σ JS JT a b x = x := by
      have := congrArg (fun y : XFF F E nS nT => (y : WOF F E nS nT)) (LatA.rhoFF_real ha hb x)
      rwa [coe_rhoFF] at this
    rw [hL, coe_opFF, coe_opFF, hL, map_smul, hoi _ (hc _ _ v.2), hi.Heisenberg₂ a ha b hb _ _ v.2, e3, ← hoi _ v.2])) p ⟨f, hf⟩)
  rw [hz ⟨f, hf⟩, map_smul, ← hL, ← this]
  exact hz (L ⟨f, hf⟩)

theorem eventually_smul_A (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    {f : WOF F E nS nT → ℂ} (h1 : IsThetaFunOF σ JS JT ξ₀ B.ψ f) :
    ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), ∃ c : ℂ, of p f = c • f := by
  filter_upwards [LatA.eventually_fix (LatA.sig_sig C.good) C.hS C.hT C.hξ hO ⟨f, h1⟩] with p hp
  obtain ⟨c, hc'⟩ := hof p
  exact ⟨c, by rw [hc' ⟨f, h1⟩, hp]⟩

theorem continuous_product_A (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hf : IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi) {f : WOF F E nS nT → ℂ} (h1 : IsThetaFunOF σ JS JT ξ₀ B.ψ f)
    (u : WOF F E nS nT) : Continuous fun p : GAF σ JS × GAF σ JT => of p (oi p f) u := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  haveI : IsTopologicalGroup (GAF σ JS) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ JS))
  haveI : IsTopologicalGroup (GAF σ JT) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ JT))
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h2 : Filter.Tendsto (fun p => p * q⁻¹) (𝓝 q) (𝓝 1) :=
    (continuous_id.mul continuous_const).tendsto' q 1 (mul_inv_cancel q)
  have h3 := hf.pres q f h1
  have h4 : ∀ᶠ p in 𝓝 q, ∃ c : ℂ, of p f = c • of q f := by
    filter_upwards [h2.eventually (eventually_smul_A C hO hof h3)] with p hp
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right] at hp
  by_cases h0 : of q f = 0
  · refine continuousAt_const.congr (f := fun _ => (0 : ℂ)) ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc'⟩ := hp
    rw [fin_inf_comm_A C hO hof hi p p f h1, hc', h0, smul_zero, map_zero]
    rfl
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
    have hx' : of q f x ≠ 0 := hx
    refine (((hf.cont f h1 x).div_const (of q f x)).mul (hi.cont _ h3 u)).continuousAt.congr ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc'⟩ := hp
    show of p f x / of q f x * oi p (of q f) u = _
    rw [fin_inf_comm_A C hO hof hi p p f h1, hc', map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_div_cancel_right₀ _ hx']

theorem datum_of_aut_A (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hη : IsHeckeCharF η) (hres : ResEtaF η 1) (hf : IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    (haut : ∀ γ ∈ GQF σ JS, ∀ γ' ∈ GQF σ JT, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of (γ, γ') (oi (γ, γ') f) 0 = f 0) :
    ∃ ω, IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (η ^ nS) (η ^ nT) ω := by
  have hB := C.good
  have hψ := GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B hB
  have hcomm : ∀ p q f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of p (oi q f) = oi q (of p f) :=
    fun p q f h => fin_inf_comm_A C hO hof hi p q f h
  have hth : ∀ (w₀ : WOF F E nS nT) f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
      IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w₀ f) :=
    fun w₀ f h => GlobalTheory.T.heisenbergOperatorF_preserves_isThetaFunction F E σ nS nT JS JT ξ₀ B.ψ hB.std.1 w₀ f h
  let Th := thetaSubF σ JS JT ξ₀ B.ψ
  let Om2 : GAF σ JS × GAF σ JT →* Module.End ℂ Th :=
    { toFun := fun p => (of p * oi p).restrict (p := Th) (q := Th) fun f h1 => hf.pres p _ (hi.pres p f h1)
      map_one' := LinearMap.ext fun f => Subtype.ext (by
        show of 1 (oi 1 f) = f
        simp only [map_one, Module.End.one_apply])
      map_mul' := fun p q => LinearMap.ext fun f => Subtype.ext (by
        show of (p * q) (oi (p * q) f) = of p (oi p (of q (oi q (f : WOF F E nS nT → ℂ))))
        simp only [map_mul, Module.End.mul_apply]
        rw [hcomm q p _ (hi.pres q _ f.2)]) }
  obtain ⟨om, hom⟩ := exists_extend Th Om2
  have ho : ∀ p f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → om p f = of p (oi p f) := fun p f h1 => hom p ⟨f, h1⟩
  have hp : ∀ p f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (om p f) := fun p f h1 => by
    rw [ho p f h1]
    exact hf.pres p _ (hi.pres p f h1)
  refine ⟨om, hψ, isHeckeCharF_pow hη _, isHeckeCharF_pow hη _, resEtaF_pow hres _, resEtaF_pow hres _, hp,
    fun g h w₀ f h1 => ?_, fun γ hγ γ' hγ' f h1 => ?_, fun f h1 w => ?_, fun μ 𝓕 hμ h𝓕 p f h1 => ?_,
    fun e he g h hg hh x y hx hy => ?_⟩
  · obtain ⟨a, ha, k, hk, e1, e1'⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders F E σ nS JS g
    obtain ⟨b, hb, l, hl, e2, e2'⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders F E σ nT JT h
    have key : ∀ x, IsThetaFunOF σ JS JT ξ₀ B.ψ x → om (g, h) x = of (k, l) (oi (a, b) x) := fun x hx => by
      rw [ho _ x hx]
      have E1 : ((g, h) : GAF σ JS × GAF σ JT) = (a, b) * (k, l) := Prod.ext e1 e2
      have E2 : ((g, h) : GAF σ JS × GAF σ JT) = (k, l) * (a, b) := Prod.ext e1' e2'
      have E3 : oi (g, h) x = oi (a, b) x := by rw [E1, map_mul, Module.End.mul_apply, hi.triv k hk l hl x hx]
      rw [E3, E2, map_mul, Module.End.mul_apply, hf.triv a ha b hb _ (hi.pres _ x hx)]
    rw [key _ (hth w₀ f h1), key f h1, hi.Heisenberg₂ a ha b hb w₀ f h1, hf.Heisenberg₂ k hk l hl _ _ (hi.pres _ f h1),
      ← actOF_mul, ← e1', ← e2']
  · rw [ho _ f h1]
    exact haut γ hγ γ' hγ' f h1
  · have e : (fun p => om p f w) = fun p => of p (oi p f) w := funext fun p => by rw [ho p f h1]
    rw [e]
    exact continuous_product_A C hO hf hof hi h1 w
  · rw [ho p f h1, hf.unit μ 𝓕 hμ h𝓕 p _ (hi.pres p f h1), hi.unit μ 𝓕 hμ h𝓕 p f h1]
  · obtain ⟨r, hr, h2⟩ := hf.split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f h1 => ?_⟩
    rw [ho _ f h1, hi.triv g (mem_GfCF_of_suppAt he hg) h (mem_GfCF_of_suppAt he hh) f h1]
    exact h2 ℓ hℓ f h1

end PositivityTheory.ThKW

end

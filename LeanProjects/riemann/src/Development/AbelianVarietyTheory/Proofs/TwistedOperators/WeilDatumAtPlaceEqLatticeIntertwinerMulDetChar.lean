import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateSplittingUnramifiedHyperspecialFix
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfHeckeCharUnramifi
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalVacuumOfIsLatticeVacuumCoprimeLevel

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO

namespace GlobalTheory.WeilAtPlace

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {lam : ℕ →* ℂ} {w₀ : 𝓞 D.host.E} {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)}

theorem isSelfDualC_frameLat (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V :=
    Submodule.ext fun y => (mem_frameLat V y).trans (GlobalTheory.PlaceModel.mem_latFrame V y).symm
  rw [h]
  exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem fj_one_mul {x : AE D} (h : infPart D x = 0) : GlobalTheory.IdemModTwo.fj D 1 * x = x :=
  GlobalTheory.PlaceIdem.parts_inj D _ _ (by rw [RingHom.map_mul, GlobalTheory.SplitCharTrivial.inf_fj, zero_mul, h])
    (by rw [RingHom.map_mul, GlobalTheory.SplitCharTrivial.fin_fj, ← Algebra.TensorProduct.one_def, one_mul])

theorem fj_one_idem : GlobalTheory.IdemModTwo.fj D 1 * GlobalTheory.IdemModTwo.fj D 1 = GlobalTheory.IdemModTwo.fj D 1 :=
  fj_one_mul (GlobalTheory.SplitCharTrivial.inf_fj 1)

def pFin (V : HSp D) : GA D V →* GA D V :=
  GlobalTheory.SplitCharTrivial.cutA V (GlobalTheory.IdemModTwo.fj D 1) fj_one_idem (GlobalTheory.IdemModTwo.cA_fj D 1)

theorem mt_pFin (V : HSp D) (g : GA D V) :
    Formalism.L2.Theta.mt V (pFin V g) = 1 + GlobalTheory.IdemModTwo.fj D 1 • (Formalism.L2.Theta.mt V g - 1) :=
  GlobalTheory.SplitCharTrivial.mt_cutA V _ _ _ g

theorem pFin_mem (V : HSp D) (g : GA D V) : pFin V g ∈ GfC V := by
  refine GlobalTheory.IdemSupport.mem_GfC_of_suppF V (f := GlobalTheory.IdemModTwo.fj D 1) (GlobalTheory.SplitCharTrivial.inf_fj 1) fun i j => ?_
  rw [mt_pFin, add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, fj_one_idem]

theorem pFin_of_mem {V : HSp D} {g : GA D V} (hg : g ∈ GfC V) : pFin V g = g := by
  refine Subtype.ext (Units.ext ?_)
  change Formalism.L2.Theta.mt V (pFin V g) = Formalism.L2.Theta.mt V g
  rw [mt_pFin]
  have h1 : (Formalism.L2.Theta.mt V g).map (infPart D) = 1 := congrArg Units.val hg
  have h2 : GlobalTheory.IdemModTwo.fj D 1 • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    refine fj_one_mul ?_
    rw [GlobalTheory.SplitCharTrivial.map_sub_one, h1, sub_self, Matrix.zero_apply]
  rw [h2, add_sub_cancel]

theorem om_eq_smul (hψ : IsStdChar D ψ (-1)) (hW : IsWeilDatumO ψ S T χS χT om) (hL : IsLatRep hψ.1 ΛS ΛT w₀ lam Om)
    (hlam : GoodNorm (sgO D) lam) {k : GA D T} (hk : k ∈ GfC T) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f (hf : IsThetaFunO ψ S T f), om (1, k) f = c • (Om (1, k) ⟨f, hf⟩ : WO S T → ℂ) := by
  obtain ⟨o, ho⟩ := exists_extend (thetaSub ψ S T) Om
  have ho' : ∀ p f (hf : IsThetaFunO ψ S T f), o p f = (Om p ⟨f, hf⟩ : WO S T → ℂ) := fun p f hf => ho p ⟨f, hf⟩
  have hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (o p f) := fun p f hf => by
    rw [ho' p f hf]
    exact (Om p ⟨f, hf⟩).2
  have hheis : ∀ (g : GA D S) (k' : GA D T), g ∈ GfC S → k' ∈ GfC T → ∀ u f, IsThetaFunO ψ S T f →
      o (g, k') (heisO ψ S T u f) = heisO ψ S T (actO S T g k' u) (o (g, k') f) := by
    intro g k' hg hk' u f hf
    obtain ⟨f', h1, h2⟩ := hL.Heisenberg₂ hψ hg hk' u ⟨f, hf⟩
    rw [ho' _ f hf, ← h2, ← h1]
    exact ho _ f'
  obtain ⟨c, hc, h⟩ := GlobalTheory.ThetaSchur.schur D ψ hψ S T (om (1, k) * o (1⁻¹, k⁻¹))
    (fun f hf => hW.om_pres _ _ (hpres _ _ hf))
    (fun u f hf => by
      rw [Module.End.mul_apply, Module.End.mul_apply, hheis _ _ (inv_mem (one_mem _)) (inv_mem hk) u f hf,
        hW.om_heis _ _ _ _ (hpres _ _ hf), GlobalTheory.FinWeilForm.actO_actO_inv])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, hW.om_unit μ 𝓕 hμ h𝓕 _ _ (hpres _ _ hf), ho' _ f hf,
        hL.unit hlam μ 𝓕 hμ h𝓕 _ ⟨f, hf⟩])
  refine ⟨c, hc, fun f hf => ?_⟩
  have h1 := h _ (hpres (1, k) f hf)
  rw [Module.End.mul_apply, ← Module.End.mul_apply (o _), ← map_mul,
    show ((1⁻¹, k⁻¹) * (1, k) : GA D S × GA D T) = 1 from inv_mul_cancel ((1 : GA D S), k), map_one,
    Module.End.one_apply] at h1
  rw [h1, ho' _ f hf]

theorem exists_nu (hψ : IsStdChar D ψ (-1)) (hW : IsWeilDatumO ψ S T χS χT om) (hL : IsLatRep hψ.1 ΛS ΛT w₀ lam Om)
    (hlam : GoodNorm (sgO D) lam) :
    ∃ ν : GA D T →* Circle, ∀ k ∈ GfC T, ∀ f (hf : IsThetaFunO ψ S T f),
      om (1, k) f = (ν k : ℂ) • (Om (1, k) ⟨f, hf⟩ : WO S T → ℂ) := by
  have hs := fun g : GA D T => om_eq_smul hψ hW hL hlam (pFin_mem T g)
  choose c hc h using hs
  obtain ⟨f, f0, hf⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
  have hne : ∀ p, (Om p ⟨f, hf⟩ : WO S T → ℂ) ≠ 0 := fun p h0 => f0 (by
    have h1 : Om p ⟨f, hf⟩ = 0 := Subtype.ext h0
    have h2 := congrArg (Om p⁻¹) h1
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at h2
    exact congrArg Subtype.val h2)
  refine ⟨MonoidHom.mk' (fun g => ⟨c g, mem_sphere_zero_iff_norm.2 (hc g)⟩) fun p q => Circle.ext ?_,
    fun k hk f hf => ?_⟩
  · show c (p * q) = c p * c q
    have e1 : ((1 : GA D S), pFin T (p * q)) = (1, pFin T p) * (1, pFin T q) :=
      Prod.ext (one_mul _).symm (map_mul _ _ _)
    have e2 := h (p * q) f hf
    rw [e1, map_mul, Module.End.mul_apply, h q f hf, map_smul, h p _ (Om (1, pFin T q) ⟨f, hf⟩).2, smul_smul, map_mul,
      Module.End.mul_apply] at e2
    have e3 := smul_left_injective ℂ (hne ((1, pFin T p) * (1, pFin T q))) (a₁ := c q * c p) (a₂ := c (p * q)) (by
      simpa only [map_mul, Module.End.mul_apply] using e2)
    rw [← e3, mul_comm]
  · have e := h k f hf
    rwa [pFin_of_mem hk] at e

theorem suppAt_one (V : HSp D) (e : AE D) : SuppAt e V (1 : GA D V) := fun i j => by
  rw [GlobalTheory.FinWeilO.mt_one, sub_self, Matrix.zero_apply, mul_zero]

theorem scalar_split (hψ : IsStdChar D ψ (-1)) (hW : IsWeilDatumO ψ S T χS χT om) (hL : IsLatRep hψ.1 ΛS ΛT w₀ lam Om)
    (hsq : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ))
    {e : AE D} (he : IsSplitIdem D e) {k : GA D T} (hk : SuppAt e T k) {y : (AE D)ˣ} (hy : IsDetAt e T k y) {c : Circle}
    (hc : ∀ f (hf : IsThetaFunO ψ S T f), om (1, k) f = (c : ℂ) • (Om (1, k) ⟨f, hf⟩ : WO S T → ℂ)) : c = χS y := by
  have hx : IsDetAt e S (1 : GA D S) 1 := by
    show ((1 : (AE D)ˣ) : AE D) = e * (Formalism.L2.Theta.mt S 1).det + (1 - e)
    rw [GlobalTheory.FinWeilO.mt_one, Matrix.det_one, Units.val_one]
    ring
  obtain ⟨r, hr, a⟩ := hW.om_split e he 1 k (suppAt_one S e) hk 1 y hx hy
  obtain ⟨r', hr', b⟩ := hL.split hsq he (suppAt_one S e) hk
  obtain ⟨ℓ, hℓ, f₁, hf₁, h0⟩ := GlobalTheory.HalfCoinv.exists_invariant_form D ψ hψ S T e he
  have c1 := a ℓ hℓ f₁ hf₁
  rw [hc f₁ hf₁, map_smul, b ℓ hℓ ⟨f₁, hf₁⟩, smul_eq_mul, splitFacO, map_one, inv_one, one_mul, ← mul_assoc] at c1
  have c2 := mul_right_cancel₀ h0 c1
  have c3 := congrArg norm c2
  rw [norm_mul, norm_mul, Circle.norm_coe, Circle.norm_coe, one_mul, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hr.le, Real.norm_of_nonneg hr'.le] at c3
  rw [c3, mul_comm] at c2
  exact Circle.ext (mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne') c2)

theorem nu_eq_one (hψ : IsStdChar D ψ (-1)) (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) (hL : IsLatRep hψ.1 ΛS ΛT w₀ lam Om) {ν : GA D T →* Circle}
    (hν : ∀ k ∈ GfC T, ∀ f (hf : IsThetaFunO ψ S T f), om (1, k) f = (ν k : ℂ) • (Om (1, k) ⟨f, hf⟩ : WO S T → ℂ))
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hv : NonSplitAt D v ε) (uS : UnramAt ε χS)
    (uT : UnramAt ε χT) {k : GA D T} (hk : SuppPl ε T k) : ν k = 1 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  refine GlobalTheory.T.adelic_unitary_character_trivial_at_nonsplit_place D T ΛT hT v ε hv ν (fun k hk hst => ?_) k hk
  obtain ⟨f₀, f0, hf₀, hvac⟩ := GlobalTheory.FinWeilForm.exists_vacuum hψ hL
  have hfix := hvac v ε hv
  have hst' := GlobalTheory.T.mem_localHomLattice_of_keeps_completedLattices D S T ΛS ΛT hS hT v ε hv.1 1 k
    (fun y => by rw [GlobalTheory.FinWeilForm.finMat_one, Matrix.one_mulVec]) hst
  have s1 : SuppPl ε S (1 : GA D S) := fun i j => by
    rw [GlobalTheory.FinWeilO.mt_one, sub_self, Matrix.zero_apply, mul_zero]
  have a := GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hψ S T ΛS ΛT hS hT χS χT om
    ((GlobalTheory.Mem.EtaTilde.exists_etaTilde D).imp fun _ h => ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩) hW v ε hv uS uT 1 k s1 hk hst'
    f₀ hf₀ hfix
  have b := hL.inert hv s1 hk (fun u hu => (hst' u).1 hu) ⟨f₀, hf₀⟩ hfix
  have hkf : k ∈ GfC T := GlobalTheory.IdemSupport.mem_GfC_of_suppF T (GlobalTheory.IdemSupport.place_comp hΦ hv.1).1 hk
  have c := hν k hkf f₀ hf₀
  rw [a, b] at c
  exact Circle.ext (smul_left_injective ℂ f0 (c.symm.trans (one_smul ℂ f₀).symm))

end GlobalTheory.WeilAtPlace

namespace GlobalTheory.WeilAtPlace

variable {D : D7}

theorem exists_eq_locIdele {w : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D} (hi : infPart D e = 0)
    (hf : finPart D e = singleAt D.host.F w 1) (x : (AE D)ˣ) (hx : e * ((x : AE D) - 1) = (x : AE D) - 1) :
    ∃ y : (w.adicCompletion D.host.E)ˣ, (y : w.adicCompletion D.host.E) = compAt D.host.F w (finPart D x) ∧
      x = locIdele D.host.F w y := by
  refine ⟨Units.map ((compAt D.host.F w).comp (finPart D)).toMonoidHom x, rfl, eq_locIdele ?_ ?_⟩
  · have h1 := congrArg (infPart D) hx
    rw [RingHom.map_mul, hi, zero_mul, RingHom.map_sub, RingHom.map_one, eq_comm, sub_eq_zero] at h1
    exact h1
  · refine FiniteAdeleRing.ext _ fun u => ?_
    by_cases hu : u = w
    · subst hu
      exact (finSingle_self u _).symm
    · have h1 := congrArg (fun z => compAt D.host.F u (finPart D z)) hx
      simp only [RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hf, compAt_singleAt_ne hu, zero_mul] at h1
      exact (sub_eq_zero.1 h1.symm).trans (finSingle_ne hu _).symm

theorem isPrimeIdem_infPart {w : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem w e f) : infPart D e = 0 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  exact (GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h).1.1

theorem unramAt_of_unrAt {w : HeightOneSpectrum (𝓞 D.host.E)} {ε : AF D.host.F} {χ : (AE D)ˣ →* Circle}
    (h : IsPrimeIdem w (algebraMap _ _ ε) (algebraMap _ _ ε)) (hu : UnrAt χ w) : UnramAt ε χ := by
  intro x hx h1 h2
  obtain ⟨y, hy, rfl⟩ := exists_eq_locIdele (isPrimeIdem_infPart h) (finPart_of_isPrimeIdem h) x hx
  have hy' : ((y⁻¹ : (w.adicCompletion D.host.E)ˣ) : w.adicCompletion D.host.E) =
      compAt D.host.F w (finPart D ((locIdele D.host.F w y)⁻¹ : (AE D)ˣ)) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have a1 : Valued.v (y : w.adicCompletion D.host.E) ≤ 1 := by
    rw [hy]; exact (mem_intAE_iff_compAt _).1 h1 w
  have a2 : Valued.v ((y⁻¹ : (w.adicCompletion D.host.E)ˣ) : w.adicCompletion D.host.E) ≤ 1 := by
    rw [hy']; exact (mem_intAE_iff_compAt _).1 h2 w
  have hun : Formalism.L2.Host.IsUnitAt w y :=
    GlobalTheory.UnramOver.val_eq_one_of_unit Valued.v (RingHom.id _) y a1 a2
  have := hu y hun
  exact Circle.ext (congrArg Units.val this)

theorem exists_isIdemAt_of_split {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hs : IsSplit (E := D.host.E) v) (h : w.under (𝓞 D.host.F) = v) : ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨e, f, hp⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ w
  obtain ⟨hd, ε, hε, hf⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hp
  rcases id hp with ⟨h1, -⟩ | ⟨rfl, -, -⟩
  · exact ⟨e, h1⟩
  exfalso
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hs
  have key : ∀ R : HeightOneSpectrum (𝓞 D.host.E), Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) R.asIdeal = v.asIdeal →
      R = w := fun R hR => by
    by_contra hne
    have h1 : Φ (algebraMap _ _ ε) R = 1 :=
      (GlobalTheory.IdemSupport.place_comp hΦ hε).2.1 R (HeightOneSpectrum.ext (hR.trans (congrArg _ h.symm)))
    rw [← hf, hd.2.2 R hne] at h1
    exact zero_ne_one h1
  exact hPQ ((key P hP).trans (key Q hQ).symm)

theorem conjPl_eq_of_inert {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hi : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) : Formalism.DivisionValues.conjPl w = w := by
  have h1 : w.asIdeal ≤ (GlobalTheory.IdemSupport.cP w).asIdeal := by
    rw [← hi]
    refine Ideal.map_le_iff_le_comap.2 ?_
    have h2 := congrArg HeightOneSpectrum.asIdeal ((GlobalTheory.IdemSupport.under_cP w).trans h)
    exact h2.ge
  have h3 : w.asIdeal = (GlobalTheory.IdemSupport.cP w).asIdeal := w.isMaximal.eq_of_le (GlobalTheory.IdemSupport.cP w).isPrime.ne_top h1
  refine GlobalTheory.IdemSupport.eq_of_le (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)
  rw [h3] at hx
  exact hx

theorem exists_nonSplit_of_inert {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hi : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) :
    ∃ ε, NonSplitAt D v ε ∧ IsPrimeIdem w (algebraMap _ _ ε) (algebraMap _ _ ε) := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨v₁, ε, hns, hu⟩ := GlobalTheory.ConjVacFix.exists_nonSplit (conjPl_eq_of_inert hi h)
  obtain ⟨e, f, hp⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ w
  obtain ⟨rfl, rfl⟩ := hu e f hp
  have hd := (GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hp).1
  obtain rfl : w.under (𝓞 D.host.F) = v₁ :=
    GlobalTheory.VacLat.under_eq_of_delta hΦ hns.1 (by rw [hd.2.1]; exact one_ne_zero)
  obtain rfl := h
  exact ⟨ε, hns, hp⟩

theorem compAt_finPart_det (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = v) (g : GA D V) :
    compAt D.host.F w (finPart D (Formalism.L2.Theta.mt V g).det) =
      (locMat D.sp.cm.sig V.gram h (proj D.sp.cm.sig V.gram v g)).1.det := by
  rw [← finMat_map_compAt D.sp.cm.sig V.gram h g]
  have e := RingHom.map_det ((compAt D.host.F w).comp (finPart D)) (Formalism.L2.Theta.mt V g)
  exact e

theorem compAt_cut {w : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D} (hf : finPart D e = singleAt D.host.F w 1) (d : AE D) :
    compAt D.host.F w (finPart D (e * d + (1 - e))) = compAt D.host.F w (finPart D d) := by
  simp only [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hf, compAt_singleAt, one_mul, sub_self,
    add_zero]

theorem isDetAt_eq_locIdele {T : HSp D} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = v) {e f : AE D} (hP : IsPrimeIdem w e f) (hee : e * e = e) (a : Gv T v) {y : (AE D)ˣ}
    (hy : IsDetAt e T (embV T v a) y) :
    y = locIdele D.host.F w (Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h a)) := by
  have hy' : (y : AE D) = e * (Formalism.L2.Theta.mt T (embV T v a)).det + (1 - e) := hy
  obtain ⟨z, hz, e3⟩ := exists_eq_locIdele (isPrimeIdem_infPart hP) (finPart_of_isPrimeIdem hP) y (by
    rw [hy']
    linear_combination ((Formalism.L2.Theta.mt T (embV T v a)).det - 1) * hee)
  have e4 : z = Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h a) := by
    refine Units.ext ?_
    rw [hz, hy', compAt_cut (finPart_of_isPrimeIdem hP), compAt_finPart_det T h, proj_emb_self]
    rfl
  rw [e3, e4]

theorem weilDatum_at_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (hψ : IsStdChar D ψ (-1)) (lam : ℕ →* ℂ) (w₀ : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)), GlobalTheory.FinWeilO.IsLatRep hψ.1 (frameLat S) (frameLat T) w₀ lam Om → GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam → (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (a : Gv T v) (f : GlobalTheory.FinWeilO.thetaSub ψ S T), (IsSplit (E := D.host.E) v → om (1, embV T v a) f = ((locChar χS w (Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h a)) : ℂˣ) : ℂ) • (Om (1, embV T v a) f : WO S T → ℂ)) ∧ (IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → om (1, embV T v a) f = (Om (1, embV T v a) f : WO S T → ℂ)) := by
  intro D ψ S T χS χT om hW hψ lam w₀ Om hL hlam hsq v w h a f
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨ν, hν⟩ := exists_nu hψ hW hL hlam
  refine ⟨fun hs => ?_, fun hi uS uT => ?_⟩
  · obtain ⟨e, he⟩ := exists_isIdemAt_of_split hs h
    have hP : IsPrimeIdem w e (e + cA D e) := Or.inl ⟨he, rfl⟩
    have hsu : SuppAt e T (embV T v a) := (Supp.suppF_iff_of_isPrimeIdem T hP h _).2 ⟨a, rfl⟩
    obtain ⟨-, -, v', ε', hε', hsum⟩ := id he.1
    have hk : embV T v a ∈ GfC T := GlobalTheory.IdemSupport.mem_GfC_of_suppF T (f := e + cA D e)
      (by rw [hsum]; exact (GlobalTheory.IdemSupport.place_comp hΦ hε').1) hsu
    obtain ⟨y, hy⟩ := GlobalTheory.FinWeilForm.exists_isDetAt he.1 T (embV T v a)
    have hc := scalar_split hψ hW hL hsq he.1 hsu hy (hν _ hk)
    have e3 := isDetAt_eq_locIdele h hP he.1.1 a hy
    have e6 := hν _ hk f.1 f.2
    rw [hc, e3] at e6
    exact e6
  · obtain ⟨ε, hns, hp⟩ := exists_nonSplit_of_inert hi h
    have hsu : SuppPl ε T (embV T v a) := (Supp.suppF_iff_of_isPrimeIdem T hp h _).2 ⟨a, rfl⟩
    have hk : embV T v a ∈ GfC T :=
      GlobalTheory.IdemSupport.mem_GfC_of_suppF T (GlobalTheory.IdemSupport.place_comp hΦ hns.1).1 hsu
    have e1 := nu_eq_one hψ hW (isSelfDualC_frameLat S) (isSelfDualC_frameLat T) hL hν hns
      (unramAt_of_unrAt hp uS) (unramAt_of_unrAt hp uT) hsu
    have e2 := hν _ hk f.1 f.2
    rw [e1, Circle.coe_one, one_smul] at e2
    exact e2

end GlobalTheory.WeilAtPlace

end

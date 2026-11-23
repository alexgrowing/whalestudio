import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

noncomputable section

namespace GlobalTheory.TorsionBoundCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem TWact_smul (f : RW →ₐ[O] RW) (T : LocLat G Qp LL O) (g : G) (r : RW) (y : TW RW T) :
    TWact f T g (r • y) = f r • TWact f T g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWact, TensorProduct.smul_tmul']
  | add a b ha hb => simp [ha, hb]

theorem TWmap_smul (f : RW →ₐ[O] RW) (T : LocLat G Qp LL O) (r : RW) (y : TW RW T) :
    TWmap f T (r • y) = f r • TWmap f T y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWmap, TensorProduct.smul_tmul']
  | add a b ha hb => simp [ha, hb]

theorem unit_cancel (hO : Function.Injective (algebraMap O LL)) :
    ∃ (e : W.DD W.one) (e₀ : ↥W.one.L.T), E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      ∀ r r' : RW, r • ((1 : RW) ⊗ₜ[O] e₀) = r' • ((1 : RW) ⊗ₜ[O] e₀) → r = r' := by
  obtain ⟨e, e₀, h1, h2, -⟩ := E.one_e
  obtain ⟨x, hx, hT⟩ := W.one_line
  have h0 : (e₀ : W.one.V) ≠ 0 := by
    intro h
    have hm : (⟨x, by rw [hT]; exact Submodule.mem_span_singleton_self x⟩ : ↥W.one.L.T) ∈
        Submodule.span O {e₀} := by rw [h1]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    have := congrArg Subtype.val hc
    simp only [SetLike.val_smul, h, smul_zero] at this
    exact hx this.symm
  have hb : Function.Bijective (LinearMap.toSpanSingleton O _ e₀) := by
    refine ⟨(injective_iff_map_eq_zero _).mpr fun c hc => ?_, ?_⟩
    · have := congrArg Subtype.val hc
      simp only [LinearMap.toSpanSingleton_apply, SetLike.val_smul, ZeroMemClass.coe_zero] at this
      rw [← algebraMap_smul LL, smul_eq_zero] at this
      exact hO (by rw [this.resolve_right h0, map_zero])
    · rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, h1]
  let lam := (LinearEquiv.ofBijective _ hb).symm
  have hl : lam e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]; simp
  refine ⟨e, e₀, h2, fun r r' h => ?_⟩
  have := congrArg (fun y => TensorProduct.rid O RW (LinearMap.lTensor RW lam.toLinearMap y)) h
  simpa [TensorProduct.smul_tmul', hl] using this

theorem ioE_φ (hO : Function.Injective (algebraMap O LL)) (a : W.EE) :
    E.ioE (W.φE a) = φR (E.ioE a) := by
  obtain ⟨e, e₀, h1, h2⟩ := unit_cancel E hO
  have h3 : TWmap φR W.one ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by simp [TWmap]
  have := E.jD_φ W.one (a • e)
  rw [W.φD_smul, E.jD_smul, E.jD_smul, E.jD_φ, TWmap_smul, h1, h3] at this
  exact h2 _ _ this

theorem ioE_γ (hO : Function.Injective (algebraMap O LL)) (g : G) (a : W.EE) :
    E.ioE (W.γE (W.resΓ g) a) = gR g (E.ioE a) := by
  obtain ⟨e, e₀, h1, h2⟩ := unit_cancel E hO
  have h4 : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g _)
  have h3 : TWact (gR g) W.one g ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by simp [TWact, h4]
  have := E.jD_act W.one g (a • e)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, TWact_smul, h1, h3] at this
  exact h2 _ _ this

def sc : LetA O n →ₐ[O] RW := inclR.comp E.io

theorem sc_φ (hO : Function.Injective (algebraMap O LL)) (a : LetA O n) :
    sc E (W.φA a) = φR (sc E a) := by
  have := ioE_φ E hO (algebraMap _ _ a)
  rwa [W.φE_ext, E.ioE_ext, E.ioE_ext] at this

theorem sc_γ (hO : Function.Injective (algebraMap O LL)) (g : G) (a : LetA O n) :
    sc E (W.γA (W.resΓ g) a) = gR g (sc E a) := by
  have := ioE_γ E hO g (algebraMap _ _ a)
  rwa [W.γE_ext, E.ioE_ext, E.ioE_ext] at this

theorem sc_pow (a : LetA O n) (k : ℕ) : sc E (a ^ k) = sc E a ^ k := map_pow _ _ _

theorem act_π (hO : Function.Injective (algebraMap O LL)) (g : G) :
    ∃ u, inclR πA * sc E u = gR g (inclR πA) := by
  obtain ⟨u, hu⟩ := PowerSeries.X_dvd_iff.mpr (W.γ₀_X (W.resΓ g)).1
  have h1 : W.γA (W.resΓ g) letπ = letπ * fun _ => u := funext fun _ => hu
  have h2 := sc_γ E hO g letπ
  have h3 : sc E letπ = inclR πA := congrArg inclR E.io_π
  rw [h1, map_mul, h3] at h2
  exact ⟨_, h2⟩

theorem sc_X_Q (hO : Function.Injective (algebraMap O LL)) {x : RW} (hx : sc E W.X = x) :
    x * sc E W.Q = φR x := by
  rw [← hx, ← sc_φ E hO, W.φA_X, map_mul]

theorem jD_sc {T : LocLat G Qp LL O} (a : LetA O n) (x : W.DD T) :
    E.jD T (a • x) = sc E a • E.jD T x := by
  rw [← algebraMap_smul W.EE a x, E.jD_smul, E.ioE_ext]
  rfl

theorem φD_smulA {T : LocLat G Qp LL O} (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rwa [algebraMap_smul, W.φE_ext, algebraMap_smul] at this

def cst (c : ZMod n → O) : LetA O n := fun i => PowerSeries.C (c i)

theorem φA_cst (c : ZMod n → O) : W.φA (cst c) = cst fun i => c (i - 1) := by
  funext i
  exact W.φ₀.commutes (c (i - 1))

theorem γA_cst (g : W.Gam) (c : ZMod n → O) : W.γA g (cst c) = cst c := by
  funext i
  exact (W.γ₀ g).commutes (c i)

theorem iter_sc_cst (hO : Function.Injective (algebraMap O LL)) (c : ZMod n → O) (k : ℕ) :
    φR^[k] (sc E (cst c)) = sc E (cst fun i => c (i - k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ← sc_φ E hO, φA_cst]
    congr 2
    funext i
    congr 1
    push_cast
    ring

end Generic

section Comp

variable {Z O R R' : Type} [CommRing Z] [CommRing O] [CommRing R] [CommRing R'] [Algebra Z O]
  [Algebra Z R] [Algebra Z R']

def cf (lam : O →ₗ[Z] Z) : O ⊗[Z] R →ₗ[Z] R :=
  (TensorProduct.lid Z R).toLinearMap ∘ₗ lam.rTensor R

theorem cf_tmul (lam : O →ₗ[Z] Z) (c : O) (w : R) : cf lam (c ⊗ₜ[Z] w) = lam c • w := by simp [cf]

theorem cf_map (lam : O →ₗ[Z] Z) (f : R →ₐ[Z] R') (x : O ⊗[Z] R) :
    cf lam (Algebra.TensorProduct.map (AlgHom.id O O) f x) = f (cf lam x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [cf_tmul]
  | add a b ha hb => simp [ha, hb]

theorem cf_sum {J : Type} [Fintype J] (o : Module.Basis J Z O) (x : O ⊗[Z] R) :
    x = ∑ j, o j ⊗ₜ[Z] cf (o.coord j) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    simp only [cf_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, Module.Basis.coord_apply,
      o.sum_repr]
  | add a b ha hb =>
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, ← ha, ← hb]

theorem cf_basis {J : Type} [Fintype J] (o : Module.Basis J Z O) (w : J → R) (j : J) :
    cf (o.coord j) (∑ k, o k ⊗ₜ[Z] w k) = w j := by
  classical
  simp [map_sum, cf_tmul, Finsupp.single_apply]

end Comp

section Situation

open GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

variable {l : ℕ} [Fact l.Prime]

theorem freeOL (LL : FinExt l) : Module.Free ℤ_[l] ↥(OL LL) :=
  haveI := LL.2
  haveI : Module.IsTorsionFree ℤ_[l] ↥LL.1 := Module.isTorsionFree_iff_algebraMap_injective.mpr (by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
    exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l]))
  IsIntegralClosure.module_free ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

theorem finOL (LL : FinExt l) : Module.Finite ℤ_[l] ↥(OL LL) :=
  haveI := LL.2
  IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

theorem fixed_frob (b : WCb l) (hb : frobW l b = b) : ∃ z : ℤ_[l], b = algebraMap ℤ_[l] (WCb l) z := by
  have h : ∀ n, ∃ a : ZMod l, ZMod.castHom (dvd_refl l) (Cb l) a = b.coeff n := by
    intro n
    have h1 : (b.coeff n) ^ l = b.coeff n := congrArg (fun w => WittVector.coeff w n) hb
    have h2 := (Subfield.mem_bot_iff_pow_eq_self (Cb l) l).2 h1
    have h3 : (⊥ : Subfield (Cb l)) ≤ (ZMod.castHom (dvd_refl l) (Cb l)).fieldRange := bot_le
    exact h3 h2
  choose a ha using h
  refine ⟨WittVector.equiv l (WittVector.mk l a), ?_⟩
  change b = zlW l (Cb l) _
  ext n
  simp [zlW, WittVector.map_coeff, ← ha]

theorem fixed_φRW (LL : FinExt l) (x : RW LL) (hx : φRW LL x = x) :
    ∃ c : ↥(OL LL), x = algebraMap ↥(OL LL) (RW LL) c := by
  haveI := freeOL LL
  haveI := finOL LL
  let o := Module.Free.chooseBasis ℤ_[l] ↥(OL LL)
  have h1 : ∀ j, ∃ z : ℤ_[l], cf (o.coord j) x = algebraMap ℤ_[l] (WCb l) z := fun j =>
    fixed_frob _ (by rw [← cf_map]; exact congrArg _ hx)
  choose z hz using h1
  refine ⟨∑ j, z j • o j, ?_⟩
  rw [cf_sum o x, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hz, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem inclW_frob (a : Ainf l) : inclW l (WittVector.frobenius a) = frobW l (inclW l a) := by
  ext n
  change ((WittVector.map _ _ : WCb l)).coeff n = (WittVector.map (frobenius (Cb l) l) (inclW l a)).coeff n
  simp [inclW, WittVector.map_coeff, frobenius_def]

theorem tmul_iter (LL : FinExt l) (k : ℕ) (x : WCb l) :
    (φRW LL)^[k] ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] x) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (frobW l)^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]; rfl

variable {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
  {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
  (E : EtTie W (RA LL) (RW LL) (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l))
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piS AI s))

theorem sc_π : sc E letπ = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (piS AI s) := by
  change inclR LL (E.io letπ) = _
  rw [E.io_π]
  rfl

theorem frob_teich (x : OCb l) :
    WittVector.frobenius (WittVector.teichmuller l x) = WittVector.teichmuller l (x ^ l) := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

theorem frob_piS (j : ℕ) : WittVector.frobenius (piS AI (j + 1)) = piS AI j := by
  rw [piS, piS, map_sub, map_one, frob_teich, LocAinf.εroot, Function.iterate_succ_apply',
    frobeniusEquiv_symm_pow_p]
  rfl

theorem sc_iter_π (j : ℕ) (hj : j ≤ s) :
    sc E ((W.φA ^ j) letπ) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (piS AI (s - j)) := by
  induction j with
  | zero => exact sc_π E
  | succ j ih =>
    rw [pow_succ', AlgHom.mul_apply, sc_φ E Subtype.val_injective, ih (by omega),
      show s - j = (s - (j + 1)) + 1 by omega, ← frob_piS (s - (j + 1)), inclW_frob]
    rfl

theorem isUnit_piS_one : IsUnit (inclW l (piS AI 1)) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [inclW, WittVector.map_coeff]
  have h0 : (piS AI 1).coeff 0 = AI.ε1 - 1 := by
    change WittVector.constantCoeff (piS AI 1) = _
    rw [piS, map_sub, map_one]
    rfl
  rw [h0]
  intro hz
  have hz' : AI.ε1 - 1 = 0 := (IsFractionRing.injective (OCb l) (Cb l)) (by rw [hz, map_zero])
  apply AI.ε_ne_one
  rw [← frobeniusEquiv_symm_pow_p (OCb l) l AI.ε]
  change AI.ε1 ^ l = 1
  rw [sub_eq_zero.mp hz', one_pow]

theorem sc_Q (hs : W.s = s) : sc E W.Q = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l AI.ξ := by
  have h1 := W.s_pos
  have hX : sc E W.X = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (piS AI 1) := by
    rw [LocWach.X, sc_iter_π E _ (by omega), show s - (W.s - 1) = 1 by omega]
  have h2 := sc_X_Q E Subtype.val_injective hX
  have hu : IsUnit ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (piS AI 1) : RW LL) :=
    isUnit_piS_one.map (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] RW LL)
  have h3 : ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (piS AI 1) : RW LL) * sc E W.Q =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] frobW l (inclW l (piS AI 1)) := h2
  apply hu.mul_left_cancel
  rw [h3, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_mul (inclW l), ← inclW_frob, frob_piS]
  exact congrArg (fun x => ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l x : RW LL)) AI.μ_eq

end Situation

end GlobalTheory.TorsionBoundCompare

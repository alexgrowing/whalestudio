import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicClosed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodOfComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleTwistCoboundaryOnBall
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NearPiSepComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedSubringTensorWittSaturatedComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedTensorWittCompletePiAdicModEll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusConstantsPiAdicFiltrationModEll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltInvariantApproxByEpsilonRootsClosure

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Decompl GlobalTheory.Cyc

namespace GlobalTheory.HWL.Rational

section Letters

variable {R B O : Type} [CommRing R] [CommRing B] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra O B] {p n : ℕ}

theorem const_dvd (ι : B →+* R) (io : LetA O n →ₐ[O] B) (τ : B) (hp : (p : O) ≠ 0) (hu : IsUnit (ι τ))
    (hinj : Function.Injective ι) (hio : Function.Injective io)
    (htf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (hsep : ∀ x : R, (∀ k : ℕ, ∃ r, x = (p : R) ^ k * r) → x = 0)
    (hsat : ∀ (y : B) (x : R), ι y = (p : R) * x → ∃ y', ι y' = x)
    (hnear : ∀ x : R, (∀ m, Near ι p (ι τ) m x) → ∃ r, x = (p : R) * r)
    (c : ZMod n → O) (h : Near ι p (ι τ) 1 (ι (io fun i => PowerSeries.C (c i)))) (i : ZMod n) :
    (p : O) ∣ c i := by
  by_contra hc
  obtain ⟨d, hd⟩ := (ValuationRing.dvd_total (c i) (p : O)).resolve_right hc
  have hdu : ¬ IsUnit d := fun hu => hc (by
    obtain ⟨u, hu⟩ := hu.exists_right_inv
    exact ⟨u, by rw [hd, mul_assoc, hu, mul_one]⟩)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp hϖ
  have h1 : ϖ ∣ d := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hdu
  obtain ⟨w, hw⟩ : (p : O) ∣ d ^ (N + 1) :=
    (hN.dvd.trans (pow_dvd_pow_of_dvd h1 N)).trans (pow_dvd_pow d (Nat.le_succ N))
  have hE : (letE i : LetA O n) * letE i = letE i := by
    rw [letE, ← Pi.single_mul, one_mul]
  have hE' : (letE i : LetA O n) * (fun i => PowerSeries.C (c i)) = algebraMap O _ (c i) * letE i := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [letE, PowerSeries.algebraMap_apply]
    · simp [letE, hk]
  have h2 := h.mul_ι (io (letE i))
  rw [← map_mul, ← map_mul, hE', map_mul io, io.commutes] at h2
  have h4 := idem_eq_zero (p := p) ι τ hu hinj htf hsep hsat hnear (io (letE i))
    (algebraMap O B (c i)) (algebraMap O B d) (algebraMap O B w) N (by rw [← map_mul, hE])
    (by rw [← map_mul, ← hd, map_natCast]) (by rw [← map_pow, hw, map_mul, map_natCast]) h2
  have h5 : (letE i : LetA O n) = 0 := hio (h4.trans (map_zero io).symm)
  simpa [letE] using congrFun h5 i

end Letters

theorem near_of_mul {R B : Type} [CommRing R] [CommRing B] {ι : B →+* R} {p N m : ℕ} {t u y z : R}
    (h : t * u = 1) (hy : Near ι p t (N + m) (t ^ N * y - z)) : Near ι p t m (y - u ^ N * z) := by
  refine Near.cancel (k := N) (IsUnit.of_mul_eq_one _ h) ?_
  rwa [mul_sub, ← mul_assoc, ← mul_pow, h, one_pow, one_mul]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s} {R : WSer Γ} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (I : WIo R RA RW inclR φR gR πA)

theorem ioE_fixed (hO : Function.Injective (algebraMap O LL)) (g : G) (hg : (PD.χ g : Qp) = 1)
    (e : R.EE) : gR g (I.ioE e) = I.ioE e := by
  have h1 : Γ.resΓ g = 1 := by
    apply Γ.χΓ_inj
    rw [map_one]
    apply Units.ext
    apply hO
    rw [Γ.χΓ_res, hg, map_one, Units.val_one, map_one]
  rw [← I.ioE_γ, h1, map_one]
  rfl

theorem ioE_letπ : I.ioE (algebraMap (LetA O n) R.EE letπ) = inclR πA := by
  rw [I.ioE_ext, I.io_π]

include I in
theorem isUnit_pi : IsUnit (inclR πA) := ioE_letπ I ▸ R.EE_π.map I.ioE

theorem exists_inv : ∃ t, inclR πA * I.ioE t = 1 := by
  obtain ⟨t, ht⟩ := R.EE_π.exists_right_inv
  exact ⟨t, by rw [← ioE_letπ I, ← map_mul, ht, map_one]⟩

theorem exists_succ : ∃ e, I.ioE e = inclR πA + 1 :=
  ⟨algebraMap (LetA O n) R.EE letπ + 1, by rw [map_add, map_one, ioE_letπ]⟩

theorem dense (R : WSer Γ) {p : ℕ} (hp : PD.p = p) (e : R.EE) : ∃ (a : LetA O n) (m : ℕ) (r : R.EE),
    e * algebraMap _ R.EE ((letπ : LetA O n) ^ m) - algebraMap _ R.EE a = (p : R.EE) * r := by
  obtain ⟨a, m, h⟩ := R.EE_dense e 1
  rw [pow_one, hp, Ideal.mem_span_singleton] at h
  exact ⟨a, m, h⟩

theorem complete (R : WSer Γ) {p : ℕ} (hp : PD.p = p) : IsAdicComplete (Ideal.span {(p : R.EE)}) R.EE :=
  hp ▸ R.EE_complete

theorem bounded_pole {p : ℕ} (hp : PD.p = p) (e : R.EE) :
    ∃ c : ℕ, Near (inclR : RA →+* RW) p (inclR πA) 0 (inclR πA ^ c * I.ioE e) := by
  obtain ⟨a, m, r, hr⟩ := dense R hp e
  have h1 := congrArg I.ioE hr
  rw [map_sub, map_mul, map_mul, map_natCast, map_pow, map_pow, ioE_letπ, I.ioE_ext] at h1
  refine ⟨m, I.io a, I.ioE r, ?_⟩
  rw [pow_zero, one_mul, ← h1]
  change _ = inclR (I.io a) + _
  ring

theorem closed [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} (hp : PD.p = p) (hp0 : (p : O) ≠ 0)
    (hinj : Function.Injective inclR) (hE : Function.Injective I.ioE)
    (htf : ∀ x : RW, (p : RW) * x = 0 → x = 0)
    (hsep : ∀ x : RW, (∀ k : ℕ, ∃ r, x = (p : RW) ^ k * r) → x = 0)
    (hsat : ∀ (y : RA) (x : RW), inclR y = (p : RW) * x → ∃ y', inclR y' = x)
    (hnear : ∀ x : RW, (∀ m, Near (inclR : RA →+* RW) p (inclR πA) m x) → ∃ r, x = (p : RW) * r)
    (x : RW) (hx : ∀ m, ∃ e, Near (inclR : RA →+* RW) p (inclR πA) m (x - I.ioE e)) :
    ∃ e r, x - I.ioE e = (p : RW) * r := by
  have hio : Function.Injective I.io := fun a b h =>
    R.EE_inj (hE (by rw [I.ioE_ext, I.ioE_ext, h]))
  have hu := isUnit_pi I
  have hπ : inclR πA = inclR (I.io letπ) := congrArg inclR I.io_π.symm
  rw [hπ] at hu hnear hx
  exact near_closed (p := p) (inclR : RA →+* RW) (I.io : LetA O n →+* RA)
    (algebraMap _ R.EE) (I.ioE : R.EE →+* RW) I.ioE_ext hu (dense R hp) hnear
    (const_dvd (inclR : RA →+* RW) I.io _ hp0 hu hinj hio htf hsep hsat hnear) x hx

end Generic

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ}
  {LL : FinExt l}

noncomputable def fW (LL : FinExt l) : Loc.Ainf l →+* RW LL :=
  (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] RW LL).toRingHom.comp (inclW l)

theorem fW_apply (w : Loc.Ainf l) : fW LL w = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l w := rfl

theorem phi_teich (x : OCb l) :
    φRW LL (fW LL (WittVector.teichmuller l x)) = fW LL (WittVector.teichmuller l (x ^ l)) := by
  have h : frobW l (inclW l (WittVector.teichmuller l x)) =
      inclW l (WittVector.teichmuller l (x ^ l)) := by
    change WittVector.map _ (WittVector.map _ _) = WittVector.map _ _
    rw [WittVector.map_teichmuller, WittVector.map_teichmuller, WittVector.map_teichmuller,
      frobenius_def, map_pow (algebraMap (OCb l) (Cb l))]
  rw [fW_apply, fW_apply, ← h]
  rfl

theorem phi_iter_teich (n : ℕ) (x : OCb l) : (φRW LL)^[n] (fW LL (WittVector.teichmuller l x)) =
    fW LL (WittVector.teichmuller l (x ^ l ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, phi_teich, ← pow_mul, ← pow_succ]

theorem eroot_pow (j : ℕ) : AI.εroot j ^ l ^ j = AI.ε := by
  induction j with
  | zero => simp [LocAinf.εroot]
  | succ j ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem piR_succ : piR AI LL s + 1 = fW LL (WittVector.teichmuller l (AI.εroot s)) := by
  have h : piR AI LL s = fW LL (piW AI s) := rfl
  rw [h, ← map_one (fW LL), ← map_add, piW, sub_add_cancel]

theorem phi_iter_eroot (j : ℕ) : (φRW LL)^[j] (fW LL (WittVector.teichmuller l (AI.εroot j))) =
    (piR AI LL s + 1) ^ l ^ s := by
  rw [phi_iter_teich, piR_succ, eroot_pow, ← eroot_pow (AI := AI) s, map_pow, map_pow]

theorem crd_fixed (hG : Good K s LL) (y : RW LL) (hy : FixH AI K y) (i) : ∀ g ∈ Hinf K,
    autCb l (AI.actT g) ((crd (basisO LL) i y).coeff 0) = (crd (basisO LL) i y).coeff 0 := by
  intro g hg
  have h1 : g ∈ GK K := IntermediateField.fixingSubgroup_antitone hG.2.2.1
    (FrameTorsion.hinf_le_gj K s hg)
  rw [← coeff_actWCbHom, ← crd_gRW, hy g h1 (FrameTorsion.chi_hinf P.χQ_cyc K hg)]

theorem sum_mem_subring (T : Subring (RW LL)) (hO : ∀ o : ↥(OL LL), o ⊗ₜ[ℤ_[l]] (1 : WCb l) ∈ T)
    (w : Fin (Module.finrank ℤ_[l] ↥(OL LL)) → Loc.Ainf l) (hw : ∀ i, fW LL (w i) ∈ T) :
    ∑ i, basisO LL i ⊗ₜ[ℤ_[l]] inclW l (w i) ∈ T := by
  refine sum_mem fun i _ => ?_
  have h1 : basisO LL i ⊗ₜ[ℤ_[l]] inclW l (w i) =
      (basisO LL i ⊗ₜ[ℤ_[l]] (1 : WCb l)) * fW LL (w i) := by
    rw [fW_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h1]
  exact mul_mem (hO _) (hw i)

theorem near_of_crd (y : RW LL) (N m : ℕ) (w : Fin (Module.finrank ℤ_[l] ↥(OL LL)) → Loc.Ainf l)
    (v : Fin (Module.finrank ℤ_[l] ↥(OL LL)) → OCb l)
    (h : ∀ i, algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ N) * (crd (basisO LL) i y).coeff 0 =
      algebraMap (OCb l) (Cb l) ((w i).coeff 0 + (AI.εroot s - 1) ^ (N + m) * v i)) :
    NearPi AI LL s (N + m) (piR AI LL s ^ N * y - ∑ i, basisO LL i ⊗ₜ[ℤ_[l]] inclW l (w i)) := by
  refine (nearPi_iff_crd AI LL s _ _).2 fun i => ⟨v i, ?_⟩
  have h1 : piR AI LL s ^ N = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (inclW l (piW AI s) ^ N) := by
    rw [piR_eq, Algebra.TensorProduct.tmul_pow, one_pow]
  have h4 : (inclW l (piW AI s) ^ N).coeff 0 = (inclW l (piW AI s)).coeff 0 ^ N :=
    map_pow (WittVector.constantCoeff : WCb l →+* Cb l) _ _
  rw [LinearMap.map_sub, sub_coeff_zero, h1, crd_mul, crd_sum, WittVector.mul_coeff_zero, h4,
    coeff_zero_piW, coeff_inclW]
  have h5 := h i
  rw [map_add, map_pow] at h5
  exact sub_eq_of_eq_add' h5

theorem approx_subring (hG : Good K s LL) (T : Subring (RW LL))
    (hO : ∀ o : ↥(OL LL), o ⊗ₜ[ℤ_[l]] (1 : WCb l) ∈ T) (t : RW LL) (ht : t ∈ T) (hπ : piR AI LL s * t = 1)
    (hgen : ∀ x ∈ (Set.range AI.εroot ∪
      {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb}),
      fW LL (WittVector.teichmuller l x) ∈ T) (y : RW LL) (hy : FixH AI K y) (m : ℕ) :
    ∃ y0 ∈ T, NearPi AI LL s m (y - y0) := by
  have hle : Subring.closure (Set.range AI.εroot ∪
      {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb}) ≤
      (T.comap (fW LL)).map (WittVector.constantCoeff : Loc.Ainf l →+* OCb l) :=
    Subring.closure_le.2 fun x hx =>
      ⟨WittVector.teichmuller l x, hgen x hx, WittVector.teichmuller_coeff_zero l x⟩
  choose N₀ hN using fun i =>
    GlobalTheory.FlatInvariants.flat_invariant_approx l P AI K s _ (crd_fixed hG y hy i) m
  choose u hu v huv using fun i => hN i (Finset.univ.sup N₀) (Finset.le_sup (Finset.mem_univ i))
  choose w hw hwu using fun i => hle (hu i)
  refine ⟨_, mul_mem (pow_mem ht (Finset.univ.sup N₀)) (sum_mem_subring T hO w hw),
    near_of_mul hπ (near_of_crd y _ m w v fun i => ?_)⟩
  have h5 : (w i).coeff 0 = u i := hwu i
  rw [h5]
  exact huv i

variable {Γ : GamS P K s LL} {R : WSer Γ}

theorem fixH_ioE (I : IoS AI R) (e : R.EE) : FixH AI K (I.ioE e) := fun g hg hχ =>
  ioE_fixed I Subtype.val_injective ⟨g, hg⟩ ((P.PD_χ K ⟨g, hg⟩).trans (congrArg Units.val hχ)) e

theorem tilt_mem (I : IoS AI R) (hW : IoW I) (c : Om l) (hc : c ∈ K0 K) (m : ℕ) (hm : 0 < m)
    (hl : ¬ l ∣ m) (hcm : c ^ m = 1) (x : OCb l) (ht : IsTiltOf c m x) :
    ∃ e, I.ioE e = fW LL (WittVector.teichmuller l x) := by
  have hint : ∀ i, Γ.emb i ⟨c, hc⟩ ∈ OL LL := fun i => by
    refine IsIntegral.of_pow hm ?_
    rw [← map_pow, show (⟨c, hc⟩ : ↥(K0 K)) ^ m = 1 from Subtype.ext hcm, map_one]
    exact isIntegral_one
  have h1 := hW ⟨c, hc⟩ m hm hl hcm x ht (fun i => ⟨_, hint i⟩) fun _ => rfl
  exact ⟨_, (I.ioE_ext _).trans (congrArg (inclR LL) h1)⟩

theorem eroot_mem (I : IoS AI R) (j : ℕ) : ∃ e,
    (φRW LL)^[j] (fW LL (WittVector.teichmuller l (AI.εroot j))) = I.ioE e ^ l ^ s := by
  obtain ⟨e, he⟩ := exists_succ I
  have h1 : I.ioE e = piR AI LL s + 1 := he
  exact ⟨e, by rw [h1, phi_iter_eroot (s := s)]⟩

theorem mem_perf {R E : Type} [CommRing R] [CommRing E] {j : E →+* R} {φ : R →+* R}
    {hφ : ∀ e, ∃ e', φ (j e) = j e'} {p : ℕ} {x : R} (n k : ℕ) (e : E) (h : φ^[n] x = j e ^ k) :
    x ∈ perf j φ hφ p := ⟨n, e ^ k, 0, by rw [h, map_pow, mul_zero, add_zero]⟩

set_option maxHeartbeats 1000000 in

theorem approx (hG : Good K s LL) (I : IoS AI R) (hW : IoW I) (y : RW LL) (hy : FixH AI K y) (m : ℕ) :
    ∃ (n : ℕ) (y0 : RW LL) (e : R.EE) (r : RW LL),
      (φRW LL)^[n] y0 = I.ioE e + (l : RW LL) * r ∧ NearPi AI LL s m (y - y0) := by
  obtain ⟨t, ht⟩ := exists_inv I
  obtain ⟨y0, ⟨n, e, r, h1⟩, h2⟩ := approx_subring hG
    (perf (I.ioE : R.EE →+* RW LL) (φRW LL : RW LL →+* RW LL) (fun e => ⟨_, (I.ioE_φ e).symm⟩) l)
    (fun o => mem_perf 0 1 (algebraMap ↥(OL LL) R.EE o) ((I.ioE.commutes o).symm.trans (pow_one _).symm))
    (I.ioE t) (mem_perf 0 1 t (pow_one _).symm) ht
    (by
      rintro x (⟨j, rfl⟩ | ⟨c, hc, m, hm, hl, hcm, hx⟩)
      · obtain ⟨e, he⟩ := eroot_mem I j
        exact mem_perf j (l ^ s) e he
      · obtain ⟨e, he⟩ := tilt_mem I hW c hc m hm hl hcm x hx
        exact mem_perf 0 1 e (he.symm.trans (pow_one _).symm)) y hy m
  exact ⟨n, y0, e, r, h1, h2⟩

theorem mem_fixSub_iff (x : RW LL) :
    x ∈ fixSub AI LL {g | g ∈ GK K ∧ P.χQ g = 1} ↔ FixH AI K x :=
  mem_fixSub.trans ⟨fun h g h1 h2 => h g ⟨h1, h2⟩, fun h g hg => h g hg.1 hg.2⟩

set_option maxHeartbeats 1000000 in
theorem vec (hG : Good K s LL) (I : IoS AI R) (hW : IoW I) (d : ℕ) (Pm : Matrix (Fin d) (Fin d) R.EE)
    (z : Fin d → RW LL) (hz : ∀ i, FixH AI K (z i))
    (h : ∀ i, ∃ e, ∑ k, I.ioE (Pm i k) * φRW LL (z k) - z i = I.ioE e) : ∀ i, ∃ e, z i = I.ioE e := by
  obtain ⟨hinj, -, hs, -⟩ := GlobalTheory.IoInj.ioE_injective_saturated_inter l P AI K s LL hG Γ R I hW
  obtain ⟨f1, f2, f3⟩ := FixL.fixSub_ladic l P AI LL {g | g ∈ GK K ∧ P.χQ g = 1}
  obtain ⟨p1, p2, -, -⟩ := GlobalTheory.DecomplFrob.frobenius_and_constants l P AI LL s
  obtain ⟨l1, l2, -⟩ := LAdic.ladic_RW l LL
  obtain ⟨_, -, hl0, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨-, -, r2, r3, -⟩ := TensorWitt.main l LL
  have hπ : piR AI LL s ∈ fixSub AI LL {g | g ∈ GK K ∧ P.χQ g = 1} := by
    have h1 : I.ioE _ = piR AI LL s := ioE_letπ I
    rw [← h1]
    exact (mem_fixSub_iff _).2 (fixH_ioE I _)
  exact (GlobalTheory.DecomplMat.matrix_frob_sub_one_bijective (RW LL) R.EE (RA LL)
    (I.ioE : R.EE →+* RW LL) (inclR LL : RA LL →+* RW LL) (φRW LL : RW LL →+* RW LL)
    (fixSub AI LL {g | g ∈ GK K ∧ P.χQ g = 1}) l (piR AI LL s) _ rfl
    (fun e => (mem_fixSub_iff _).2 (fixH_ioE I e)) f2 (fun e => ⟨_, (I.ioE_φ e).symm⟩) p1 p2
    (bounded_pole I (P.PD_p K)) f1 (sat_range (I.ioE : R.EE →+* RW LL) l1 hs)
    (fixSub_nearPi_complete l P AI LL s _ hπ)
    (closed I (P.PD_p K) hl0 r2 hinj l1 l2 r3 (nearPi_sep_complete l P AI LL s).1)
    (fun y hy m => approx hG I hW y ((mem_fixSub_iff _).1 hy) m) f3
    (padic_closed (I.ioE : R.EE →+* RW LL) l1 l2 hs (complete R (P.PD_p K))) d Pm).2 z
    (fun i => (mem_fixSub_iff _).2 (hz i)) h

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) R.EE) (A' : Matrix (Fin q) (Fin q) R.EE) (Y : Matrix (Fin p) (Fin q) R.EE) (U : Matrix (Fin p) (Fin q) (RW LL)), IsUnit A → IsUnit A' → (∀ i j, FixH AI K (U i j)) → A.map I.ioE * U.map (φRW LL) = U * A'.map I.ioE + Y.map I.ioE → ∀ i j, U i j ∈ Set.range I.ioE := by
  intro l _ P AI K s LL hG Γ R I hW p q A A' Y U _ hA' hU h i j
  obtain ⟨C, hC⟩ := hA'.exists_right_inv
  let σ := (finProdFinEquiv : Fin p × Fin q ≃ Fin (p * q)).symm
  obtain ⟨e, he⟩ := vec hG I hW (p * q) (fun a b => A (σ a).1 (σ b).1 * C (σ b).2 (σ a).2)
    (fun a => U (σ a).1 (σ a).2) (fun a => hU _ _) (fun a => ⟨_,
      matrix_eq (I.ioE : R.EE →+* RW LL) (φRW LL : RW LL →+* RW LL) A A' C Y U hC h σ a⟩) (σ.symm (i, j))
  rw [σ.apply_symm_apply] at he
  exact ⟨e, he.symm⟩

end GlobalTheory.HWL.Rational

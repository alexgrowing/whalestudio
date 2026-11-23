import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbWInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CDvdOfMapEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicIntegersEqWittZetaSubOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueUnramifiedIntegersCoordsBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachInclusionPowerSeriesIntoOneTmulAinfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeomSumOneAddPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgHomExtOfConstantCoeffZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceEmb
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.Cyc PowerSeries
open scoped Formalism.Per

namespace GlobalTheory.PrismS

variable {l : ℕ} [hl : Fact l.Prime]

theorem dvd_of_not_isUnit (K : FinExt l) (w : WK K) (hw : ¬ IsUnit w) : (l : WK K) ∣ w := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  rw [GlobalTheory.EmbThroughCompletion.not_isUnit_iff] at hw
  have hl0 : (l : ↥(K0 K)) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hn : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hm : (w : ↥(K0 K)) / (l : ↥(K0 K)) ∈ OL (unr K) := by
    rw [GlobalTheory.EmbThroughCompletion.mem_OL_iff]
    change ‖((w : ↥(K0 K)) : Om l) / (l : Om l)‖ ≤ 1
    by_cases h0 : ((w : ↥(K0 K)) : Om l) = 0
    · simp [h0]
    obtain ⟨n, h⟩ := GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K _ (w : ↥(K0 K)).2 h0
    change ‖((w : ↥(K0 K)) : Om l)‖ < 1 at hw
    rw [h, zpow_lt_one_iff_right₀ hl1] at hw
    rw [norm_div, h, hn, div_inv_eq_mul, ← zpow_add_one₀ (by positivity), zpow_le_one_iff_right₀ hl1]
    omega
  refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
  change (w : ↥(K0 K)) = (l : ↥(K0 K)) * ((w : ↥(K0 K)) / (l : ↥(K0 K)))
  field_simp

def sigW (P : LocPrime l) (K : FinExt l) : WK K →ₐ[ℤ_[l]] WK K := embW (LL := unr K) (P.PD K).σ

theorem sigW_lift (P : LocPrime l) (K : FinExt l) (w : WK K) : ∃ b, sigW P K w = w ^ l + (l : WK K) * b := by
  obtain ⟨b, hb⟩ := dvd_of_not_isUnit K (sigW P K w - w ^ l)
    ((GlobalTheory.EmbThroughCompletion.not_isUnit_iff _ _).2 (P.PD_σ K w (norm_le_one_of_mem_OL (unr K) w)))
  exact ⟨b, by rw [← hb]; ring⟩

variable {P : LocPrime l} {K : FinExt l} {s : ℕ} {LL : FinExt l} {Γ : GamS P K s LL}

theorem ser_eq (R : WSer Γ) (χ : GQ l →* ℤ_[l]ˣ)
    (hχ : ∀ g, (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = (P.χQ g : ℚ_[l])) (g : ↥(GK K)) :
    R.φ₀ = phi l ↥(OL LL) ∧ R.γ₀ (Γ.resΓ g) = act l ↥(OL LL) (χ (g : GQ l) : ℤ_[l]) := by
  obtain ⟨_, _, l0, lu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  refine act_unique l _ l0 lu _ _ _ (by rw [R.φ₀_X, R.q₀_def, P.PD_p]) (R.γ₀_comm _) (R.γ₀_X _).1 ?_
  rw [(R.γ₀_X _).2]
  apply Subtype.ext
  have h := Γ.χΓ_res g
  rw [P.PD_χ, ← hχ] at h
  exact h

theorem letEmb_phiS (x : (WK K)⟦X⟧) :
    letEmb Γ.emb (phiS (sigW P K) x) = letφ (phi l ↥(OL LL)) (letEmb Γ.emb x) := by
  funext i
  change PowerSeries.map (embW (Γ.emb i)).toRingHom (PowerSeries.map (sigW P K).toRingHom (act l _ _ x)) =
    act l _ _ (PowerSeries.map (embW (Γ.emb (i - 1))).toRingHom x)
  rw [← map_act, ← RingHom.comp_apply, ← PowerSeries.map_comp]
  congr 2
  have h := Γ.emb_σ (i - 1)
  rw [sub_add_cancel] at h
  exact RingHom.ext fun w => Subtype.ext (AlgHom.congr_fun h (w : ↥(K0 K)))

theorem letEmb_act (c : ℤ_[l]) (x : (WK K)⟦X⟧) :
    letEmb Γ.emb (act l (WK K) c x) = letγ (act l ↥(OL LL) c) (letEmb Γ.emb x) :=
  funext fun i => map_act (embW (Γ.emb i)) c x

theorem letφ_pow_const {O : Type} [CommRing O] {n : ℕ} (f : O⟦X⟧ →ₐ[O] O⟦X⟧) (k : ℕ) (c : O⟦X⟧) :
    (letφ (n := n) f ^ k) (fun _ => c) = fun _ => (f ^ k) c := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', pow_succ', AlgHom.mul_apply, ih]; rfl

theorem phi_pow_q {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] (l0 : (l : O) ≠ 0) (hs : 1 ≤ s)
    (q : O⟦X⟧) (hq : phi l O X = X * q) : QQ l O s = (phi l O ^ (s - 1)) q := by
  obtain ⟨h2, h3, h4, -⟩ := XX_QQ_properties l O s hs
  have h5 : XX l O s ≠ 0 := fun h0 => by
    have := congrArg (coeff 1) h0
    simp [XX, ← Polynomial.coe_X, ← Polynomial.coe_one, ← Polynomial.coe_add,
      ← Polynomial.coe_pow, Polynomial.coeff_one_add_X_pow, Polynomial.coeff_one, l0] at this
  apply mul_left_cancel₀ h5
  rw [← h2, ← h3, ← map_mul, ← hq, ← AlgHom.mul_apply, ← AlgHom.mul_apply, ← pow_succ, ← pow_succ']

theorem letEmb_QQ (R : WSer Γ) (h : R.φ₀ = phi l ↥(OL LL)) : letEmb Γ.emb (QQ l (WK K) s) = R.Q := by
  obtain ⟨_, _, l0, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have h1 := phi_pow_q l0 Γ.s_pos R.q₀ (h ▸ R.φ₀_X)
  rw [← h] at h1
  have h2 : letEmb Γ.emb (QQ l (WK K) s) = fun _ => (R.φ₀ ^ (s - 1)) R.q₀ :=
    funext fun i => (map_QQ (embW (Γ.emb i)).toRingHom s).trans h1
  exact h2.trans (letφ_pow_const R.φ₀ (s - 1) R.q₀).symm

theorem one_tmul_inj (LL : FinExt l) {a b : Ainf l}
    (h : (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l a = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l b) : a = b := by
  obtain ⟨_, _, -, -, _, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  exact inclW_injective (Module.FaithfullyFlat.tensorProduct_mk_injective (A := ℤ_[l]) (B := ↥(OL LL)) (WCb l) h)

variable {AI : LocAinf l P} {R : WSer Γ} (I : IoS AI R) {io : (WK K)⟦X⟧ →+* Ainf l}

theorem io_phiS (hio : ∀ x, I.io (letEmb Γ.emb x) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] io x)
    (h : R.φ₀ = phi l ↥(OL LL)) (x : (WK K)⟦X⟧) :
    io (phiS (sigW P K) x) = WittVector.frobenius (io x) := by
  apply one_tmul_inj LL
  have h1 : inclR LL (I.io (letφ R.φ₀ (letEmb Γ.emb x))) = φRW LL (inclR LL (I.io (letEmb Γ.emb x))) :=
    ((I.ioE_ext _).symm.trans (congrArg I.ioE (R.φE_ext _).symm)).trans
      ((I.ioE_φ _).trans (congrArg (φRW LL) (I.ioE_ext _)))
  have h2 : letEmb Γ.emb (phiS (sigW P K) x) = letφ R.φ₀ (letEmb Γ.emb x) := h ▸ letEmb_phiS x
  have h3 := (congrArg (inclR LL) ((hio _).symm.trans (congrArg I.io h2))).trans
    (h1.trans (congrArg (fun y => φRW LL (inclR LL y)) (hio x)))
  rw [← frobW_inclW]
  exact h3

theorem io_act (hio : ∀ x, I.io (letEmb Γ.emb x) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] io x)
    (g : ↥(GK K)) (c : ℤ_[l]) (h : R.γ₀ (Γ.resΓ g) = act l ↥(OL LL) c) (x : (WK K)⟦X⟧) :
    io (act l (WK K) c x) = Formalism.Per.σA (g : GQ l) (io x) := by
  apply one_tmul_inj LL
  have h1 : inclR LL (I.io (letγ (R.γ₀ (Γ.resΓ g)) (letEmb Γ.emb x))) =
      AI.gRW LL (g : GQ l) (inclR LL (I.io (letEmb Γ.emb x))) :=
    ((I.ioE_ext _).symm.trans (congrArg I.ioE (R.γE_ext _ _).symm)).trans
      ((I.ioE_γ g _).trans (congrArg (AI.gRW LL (g : GQ l)) (I.ioE_ext _)))
  have h2 : letEmb Γ.emb (act l (WK K) c x) = letγ (R.γ₀ (Γ.resΓ g)) (letEmb Γ.emb x) := h ▸ letEmb_act c x
  have h3 := (congrArg (inclR LL) ((hio _).symm.trans (congrArg I.io h2))).trans
    (h1.trans (congrArg (fun y => AI.gRW LL (g : GQ l) (inclR LL y)) (hio x)))
  rw [← galW_inclW, ← locAinf_actWCbHom_eq AI]
  exact h3

theorem exists_str {R S C : Type} [CommRing R] [CommRing S] [CommRing C] (f : S →+* C) (g : R →+* C)
    (J : Ideal S) (hJ : RingHom.ker f = J) (h : ∀ x, ∃ a, f a = g x) :
    ∃ str : R →+* S ⧸ J, ∀ x a, Ideal.Quotient.mk J a = str x ↔ f a = g x := by
  subst hJ
  refine ⟨(RingHom.quotientKerEquivRange f).symm.toRingHom.comp (g.codRestrict f.range h), fun x a => ?_⟩
  change _ = (RingHom.quotientKerEquivRange f).symm _ ↔ _
  rw [RingEquiv.eq_symm_apply, Subtype.ext_iff]
  rfl

theorem ker_theta_io (AI : LocAinf l P) (hs : 1 ≤ s) (hK : K.1 ≤ Ks K s) (io : (WK K)⟦X⟧ →+* Ainf l)
    (hX : io X = WittVector.teichmuller l (AI.εroot s) - 1)
    (hC : ∀ w : WK K, Formalism.Per.θ l (io (C w)) = intToOC (unr K) w) :
    RingHom.ker ((Formalism.Per.θ l).comp io) = Ideal.span {QQ l (WK K) s} ∧
      ∀ x, ∃ a, (Formalism.Per.θ l).comp io a = intToOC K x := by
  obtain ⟨_, _, -, lu, -⟩ := GlobalTheory.Per.integers_completeDVR l (unr K)
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  generalize hf : (Formalism.Per.θ l).comp io = f
  have hfX : f X = AI.ζ (m + 1) - 1 := by
    rw [← hf, RingHom.comp_apply, hX, map_sub, map_one, WittVector.fontaineTheta_teichmuller, untilt_εroot]
  have hfC : ∀ w, f (C w) = intToOC (unr K) w := fun w => by rw [← hf]; exact hC w
  have hp : ∀ r : Polynomial (WK K), f r = r.eval₂ (intToOC (unr K)) (AI.ζ (m + 1) - 1) := fun r =>
    RingHom.congr_fun (Polynomial.ringHom_ext (f := f.comp Polynomial.coeToPowerSeries.ringHom)
      (g := Polynomial.eval₂RingHom (intToOC (unr K)) (AI.ζ (m + 1) - 1))
      (fun a => by simpa using hfC a) (by simpa using hfX)) r
  obtain ⟨h1, h2⟩ := GlobalTheory.T.cyclotomic_integers_eq_witt_zeta_sub_one l K (m + 1) hs _ (GlobalTheory.MemLoc.FitsEx.zeta_prim P m) (AI.ζ (m + 1) - 1) (by
    have h := AI.ζ_eq (m + 1)
    have h' := map_sub (algebraMap (Om l) ℂ_[l]) (P.ζQ (m + 1)) 1
    rw [map_one] at h'
    exact (congrArg (· - 1) h).trans h'.symm)
  obtain ⟨-, -, -, ⟨b, hb⟩, -⟩ := XX_QQ_properties l (WK K) (m + 1) hs
  refine ⟨ker_eq_span f _ b _ (l : WK K) lu (by rw [map_natCast]; exact hb) ?_
    fun r hr h0 => h1 r hr ((hp r).symm.trans h0), fun x => ?_⟩
  · have h3 : AI.ζ (m + 1) ^ l ^ m = AI.ζ 1 := by rw [add_comm, ζ_add_pow]
    have h4 : f (QQ l (WK K) (m + 1)) = ∑ k ∈ Finset.range l, AI.ζ 1 ^ k := by
      simp [QQ, XX, hfX, h3]
    have h5 := geom_sum_mul (AI.ζ 1) l
    rw [AI.ζ_succ 0, AI.ζ_zero, sub_self] at h5
    rw [h4]
    exact (mul_eq_zero.1 h5).resolve_right (sub_ne_zero.2 AI.ζ_one)
  · obtain ⟨r, hr⟩ := h2 hK x
    exact ⟨r, (hp r).trans hr⟩

theorem series_tf (x : (WK K)⟦X⟧) (h : (l : (WK K)⟦X⟧) * x = 0) : x = 0 := by
  obtain ⟨_, _, l0, -⟩ := GlobalTheory.Per.integers_completeDVR l (unr K)
  refine (mul_eq_zero.1 h).resolve_left fun h0 => l0 ?_
  rw [← map_natCast (constantCoeff (R := WK K)), h0, map_zero]

theorem coeff_tf (x : WK K) (h : (l : WK K) * x = 0) : x = 0 := by
  obtain ⟨_, _, l0, -⟩ := GlobalTheory.Per.integers_completeDVR l (unr K)
  exact (mul_eq_zero.1 h).resolve_left l0

theorem coeff_complete (K : FinExt l) : IsAdicComplete (Ideal.span {(l : WK K)}) (WK K) := by
  obtain ⟨_, hc, -, lu, -⟩ := GlobalTheory.Per.integers_completeDVR l (unr K)
  have h : IsLocalRing.maximalIdeal (WK K) = Ideal.span {(l : WK K)} :=
    le_antisymm (fun w hw => Ideal.mem_span_singleton.2 (dvd_of_not_isUnit K w hw))
      ((Ideal.span_singleton_le_iff_mem _).2 lu)
  rwa [h] at hc

theorem coeff_not_isUnit (K : FinExt l) : ¬ IsUnit (l : WK K) := by
  obtain ⟨_, -, -, lu, -⟩ := GlobalTheory.Per.integers_completeDVR l (unr K)
  exact lu

def prismS (P : LocPrime l) (hs : 1 ≤ s) (f : (WK K)⟦X⟧ →+* OC l) (hf : RingHom.ker f = Ideal.span {QQ l (WK K) s})
    (str : ↥(OL K) →+* (WK K)⟦X⟧ ⧸ Ideal.span {QQ l (WK K) s}) : Obj l ↥(OL K) where
  A := (WK K)⟦X⟧
  D := Delta.ofLift l (phiS (sigW P K)) series_tf (phiS_lift _ (coeff_not_isUnit K) (sigW_lift P K))
  I := Ideal.span {QQ l (WK K) s}
  inv := invertible_span_singleton (mem_nonZeroDivisors_of_ne_zero fun h => coeff_not_isUnit K (by
    have h1 := (XX_QQ_properties l (WK K) s hs).2.2.1
    rw [h, map_zero] at h1
    exact absurd (coeff_tf (K := K) 1 (by rw [← h1, zero_mul])) one_ne_zero))
  complete := by
    obtain ⟨-, -, -, ⟨b, hb⟩, -⟩ := XX_QQ_properties l (WK K) s hs
    have := coeff_complete K
    have h := isAdicComplete_span (l : WK K) (QQ l (WK K) s) b _
      (Nat.mul_pos (pow_pos hl.out.pos (s - 1)) (Nat.sub_pos_of_lt hl.out.one_lt))
      (by rw [map_natCast]; exact hb)
    rwa [map_natCast] at h
  l_mem := by
    obtain ⟨h1, -, -, -, ⟨b, hb⟩, -⟩ := XX_QQ_properties l (WK K) s hs
    have h2 : PowerSeries.map (sigW P K).toRingHom (XX l (WK K) s) = XX l (WK K) s := by simp [XX]
    have h3 : phiS (sigW P K) (QQ l (WK K) s) = l + XX l (WK K) s * QQ l (WK K) s * phiS (sigW P K) b := by
      conv_lhs => rw [hb, map_add, map_natCast, map_mul, phiS_apply _ (XX l (WK K) s), h1, map_mul, h2, map_QQ]
    have h4 : (l : (WK K)⟦X⟧) = QQ l (WK K) s * (-(XX l (WK K) s * phiS (sigW P K) b)) +
        phiS (sigW P K) (QQ l (WK K) s) := by rw [h3]; ring
    rw [h4]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Ideal.mem_map_of_mem (phiS (sigW P K)) (Ideal.mem_span_singleton_self _))
  bdd := ⟨0, fun x ⟨m, hm⟩ => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← hf,
      RingHom.mem_ker, map_mul, map_pow, map_natCast] at hm
    rw [pow_zero, one_mul, Ideal.Quotient.eq_zero_iff_mem, ← hf, RingHom.mem_ker]
    exact (mul_eq_zero.1 hm).resolve_left (pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))⟩
  str := str

def prismW (P : LocPrime l) (str : ↥(OL K) →+* WK K ⧸ Ideal.span {(l : WK K)}) : Obj l ↥(OL K) where
  A := WK K
  D := Delta.ofLift l (sigW P K).toRingHom coeff_tf (sigW_lift P K)
  I := Ideal.span {(l : WK K)}
  inv := invertible_span_singleton (mem_nonZeroDivisors_of_ne_zero fun h =>
    one_ne_zero (coeff_tf (K := K) 1 (by rw [h, zero_mul])))
  complete := by rw [sup_idem]; exact coeff_complete K
  l_mem := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  bdd := ⟨1, fun x _ => by
    have : ((l : ℕ) : WK K ⧸ Ideal.span {(l : WK K)}) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    rw [pow_one, this, zero_mul]⟩
  str := str

theorem span_QQ_le (hs : 1 ≤ s) : Ideal.span {QQ l (WK K) s} ≤
    (Ideal.span {(l : WK K)}).comap (constantCoeff (R := WK K)) := by
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, (XX_QQ_properties l (WK K) s hs).2.2.1]
  exact Ideal.mem_span_singleton_self _

variable {f : (WK K)⟦X⟧ →+* OC l} {str : ↥(OL K) →+* (WK K)⟦X⟧ ⧸ Ideal.span {QQ l (WK K) s}}

def evHom (P : LocPrime l) (hs : 1 ≤ s) (hf : RingHom.ker f = Ideal.span {QQ l (WK K) s})
    (str : ↥(OL K) →+* (WK K)⟦X⟧ ⧸ Ideal.span {QQ l (WK K) s}) :
    Hom (prismS P hs f hf str) (prismW P
      ((Ideal.quotientMap (Ideal.span {(l : WK K)}) constantCoeff (span_QQ_le (K := K) hs)).comp str)) where
  f := constantCoeff (R := WK K)
  f_δ := Delta.map_δ_of_map_φ _ _ (coeff_tf (K := K)) _ fun (a : (WK K)⟦X⟧) => by
    change constantCoeff (PowerSeries.map (sigW P K).toRingHom (act l (WK K) _ a)) =
      (sigW P K).toRingHom (constantCoeff a)
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, constantCoeff_act]
  f_I _ ha := span_QQ_le (K := K) hs ha
  f_str _ _ h :=
    congrArg (Ideal.quotientMap (Ideal.span {(l : WK K)}) constantCoeff (span_QQ_le (K := K) hs)) h

def ioHom (P : LocPrime l) (hs : 1 ≤ s) (io : (WK K)⟦X⟧ →+* Ainf l)
    (hf : RingHom.ker ((Formalism.Per.θ l).comp io) = Ideal.span {QQ l (WK K) s})
    (hstr : ∀ x a, Ideal.Quotient.mk _ a = str x ↔ (Formalism.Per.θ l).comp io a = intToOC K x)
    (hφ : ∀ x, io (phiS (sigW P K) x) = WittVector.frobenius (io x)) :
    Hom (prismS P hs _ hf str) (ainfObj K) where
  f := io
  f_δ := Delta.map_δ_of_map_φ _ _ ainf_torsionFree _ hφ
  f_I _ ha := hf.ge ha
  f_str x a h := ((isAinf_ainfObj K).mk_eq_str_iff x (io a)).2 ((hstr x a).1 h)

theorem act_phiS (c : ℤ_[l]) (x : (WK K)⟦X⟧) :
    act l (WK K) c (phiS (sigW P K) x) = phiS (sigW P K) (act l (WK K) c x) := by
  have h := (act_laws l (WK K)).2.1
  rw [phiS_apply, phiS_apply, ← map_act, phi, h, h, mul_comm]

def actHom (P : LocPrime l) (hs : 1 ≤ s) (hf : RingHom.ker f = Ideal.span {QQ l (WK K) s})
    (hstr : ∀ x a, Ideal.Quotient.mk _ a = str x ↔ f a = intToOC K x) (g : ↥(GK K)) (c : ℤ_[l])
    (hg : ∀ x, f (act l (WK K) c x) = Formalism.Per.σO (g : GQ l) (f x)) :
    Hom (prismS P hs f hf str) (prismS P hs f hf str) where
  f := (act l (WK K) c).toRingHom
  f_δ := Delta.map_δ_of_map_φ (A := (WK K)⟦X⟧) (B := (WK K)⟦X⟧) _ _ (series_tf (K := K))
    (act l (WK K) c).toRingHom (act_phiS (P := P) (K := K) c)
  f_I a ha := hf.le ((hg a).trans (by rw [show f a = 0 from hf.ge ha, map_zero]))
  f_str x a h := (hstr x _).2 ((hg a).trans (by
    rw [(hstr x a).1 h]
    apply Subtype.ext
    refine (GlobalTheory.RingIface.sigO_coe _ _ _).trans ?_
    change Formalism.Per.σC (g : GQ l) (((x : ↥K.1) : Om l) : ℂ_[l]) = (((x : ↥K.1) : Om l) : ℂ_[l])
    rw [GlobalTheory.RingBasics.σC_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (x : ↥K.1).2]))

theorem existsUnique_of_basis {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {d : ℕ}
    (b : Module.Basis (Fin d) A B) (x : B⟦X⟧) :
    ∃! c : Fin d → A⟦X⟧, x = ∑ i, PowerSeries.map (algebraMap A B) (c i) * C (b i) := by
  have h := existsUnique_series (κ := Unit) (fun _ => algebraMap A B) b (fun y =>
    ⟨b.equivFun (y ()), fun k => by
      conv_lhs => rw [← b.sum_equivFun (y ())]
      exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm], fun c hc => by
      rw [← LinearEquiv.symm_apply_eq, b.equivFun_symm_apply, hc ()]
      exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]⟩) fun _ => x
  simpa only [forall_const, mul_comm] using h

theorem exists_coordinates (K : FinExt l) : ∃ (d : ℕ) (w : Fin d → (WK K)⟦X⟧), ∀ x, ∃! c : Fin d → ℤ_[l]⟦X⟧,
    x = ∑ i, PowerSeries.map (algebraMap ℤ_[l] (WK K)) (c i) * w i := by
  obtain ⟨_, -, -, -, _, _, -⟩ := GlobalTheory.Per.integers_completeDVR l (unr K)
  exact ⟨_, _, existsUnique_of_basis (Module.finBasis ℤ_[l] (WK K))⟩

theorem series_isLocalRing (K : FinExt l) : IsLocalRing (WK K)⟦X⟧ := by
  obtain ⟨_, -⟩ := GlobalTheory.Per.integers_completeDVR l (unr K)
  infer_instance

theorem series_isDomain (K : FinExt l) : IsDomain (WK K)⟦X⟧ := inferInstance

end GlobalTheory.PrismS

set_option maxHeartbeats 1000000 in
open GlobalTheory.PrismS in

theorem GlobalTheory.PrismS.exists_prism : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∃ (PS PW : Obj l ↥(OL K)) (ev : Hom PS PW) (ioH : Hom PS (ainfObj K)) (gH : ↥(GK K) → Hom PS PS) (a : PS.A →+* LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) (z : PowerSeries ℤ_[l] →+* PS.A) (π Q : PS.A), Function.Injective a ∧ (∀ x, I.io (a x) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (ainfId K (ioH.f x))) ∧ (∀ x, a (PS.D.φ x) = letφ R.φ₀ (a x)) ∧ (∀ g x, a ((gH g).f x) = letγ (R.γ₀ (Γ.resΓ g)) (a x)) ∧ (∀ g, ioH.comp (gH g) = (ainfHom K g).comp ioH) ∧ (∀ g, ev.comp (gH g) = ev) ∧ a π = letπ ∧ Function.Surjective ev.f ∧ RingHom.ker ev.f = Ideal.span {π} ∧ PS.I = Ideal.span {Q} ∧ a Q = R.Q ∧ a.comp z = zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) ∧ IsLocalRing PS.A ∧ IsDomain PS.A ∧ (∃ (d : ℕ) (w : Fin d → PS.A), ∀ x, ∃! c : Fin d → PowerSeries ℤ_[l], x = ∑ i, z (c i) * w i) ∧ ∀ (d : ℕ) (o : Module.Basis (Fin d) ℤ_[l] ↥(OL LL)) (x : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), ∃! c : Fin d → PS.A, ∀ k, x k = ∑ i, PowerSeries.C (o i) * a (c i) k := by
  intro l _ P AI K s LL hG Γ R I hW
  obtain ⟨hs, -, hK, -⟩ := hG
  refine (GlobalTheory.T.exists_wachInclusion_powerSeries_into_one_tmul_ainf l P AI K s LL Γ R I hW).elim fun io h => ?_
  have hio := h.1
  refine (exists_integral_cyclotomicChar l P).elim fun χ h' => ?_
  have hχ := h'.1
  have hf := (ker_theta_io AI hs hK io h.2.1 h.2.2).1
  refine (exists_str _ (intToOC K) _ hf (ker_theta_io AI hs hK io h.2.1 h.2.2).2).elim fun str hstr => ?_
  have hφ := (ser_eq R χ hχ (1 : ↥(GK K))).1
  have hγ := fun g : ↥(GK K) => (ser_eq R χ hχ g).2
  have hact := fun g : ↥(GK K) => io_act I hio g _ (hγ g)
  have hθ : ∀ (g : ↥(GK K)) x, (Formalism.Per.θ l).comp io (act l (WK K) (χ (g : GQ l) : ℤ_[l]) x) =
      Formalism.Per.σO (g : GQ l) ((Formalism.Per.θ l).comp io x) := fun g x =>
    (congrArg (Formalism.Per.θ l) (hact g x)).trans (GlobalTheory.RingBasics.θ_σA _ _)
  have h1 : Function.Injective (letEmb Γ.emb) := fun x y h =>
    PowerSeries.map_injective _ (embW_injective (Γ.emb 0)) (congrFun h 0)
  have h2 : ∀ x, letEmb Γ.emb (phiS (sigW P K) x) = letφ R.φ₀ (letEmb Γ.emb x) := fun x => hφ ▸ letEmb_phiS x
  have h3 : ∀ (g : ↥(GK K)) x, letEmb Γ.emb (act l (WK K) (χ (g : GQ l) : ℤ_[l]) x) =
      letγ (R.γ₀ (Γ.resΓ g)) (letEmb Γ.emb x) := fun g x => hγ g ▸ letEmb_act _ x
  have h4 : letEmb Γ.emb X = letπ := funext fun i => map_X (embW (Γ.emb i)).toRingHom
  have h5 : RingHom.ker (constantCoeff (R := WK K)) = Ideal.span {X} :=
    Ideal.ext fun x => (X_dvd_iff (R := WK K)).symm.trans Ideal.mem_span_singleton.symm
  have h6 : (letEmb Γ.emb).comp (PowerSeries.map (algebraMap ℤ_[l] (WK K))) =
      zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) := by
    refine RingHom.ext fun x => funext fun i => ?_
    change PowerSeries.map (embW (Γ.emb i)).toRingHom (PowerSeries.map (algebraMap ℤ_[l] (WK K)) x) =
      PowerSeries.map (algebraMap ℤ_[l] ↥(OL LL)) x
    rw [← RingHom.comp_apply, ← PowerSeries.map_comp]
    congr 2
    exact RingHom.ext fun z => (embW (Γ.emb i)).commutes z
  have h9 := fun (d : ℕ) (o : Module.Basis (Fin d) ℤ_[l] ↥(OL LL)) x =>
    existsUnique_series (fun k => (embW (Γ.emb k)).toRingHom) o (GlobalTheory.T.existsUnique_unramifiedIntegers_coords_basis l K LL Γ.emb Γ.emb_bij.1 d o) x
  refine ⟨prismS P hs _ hf str, _, evHom P hs hf str, ioHom P hs io hf hstr (io_phiS I hio hφ),
    fun g => actHom P hs hf hstr g (χ (g : GQ l) : ℤ_[l]) (hθ g),
    letEmb Γ.emb, PowerSeries.map (algebraMap ℤ_[l] (WK K)), (X : (WK K)⟦X⟧), QQ l (WK K) s,
    h1, hio, h2, h3, fun g => ?_, fun g => ?_, h4, constantCoeff_surj (R := WK K), h5, rfl, letEmb_QQ R hφ, h6,
    series_isLocalRing K, series_isDomain K, exists_coordinates K, h9⟩
  · exact Hom.ext' (RingHom.ext (hact g))
  · exact Hom.ext' (RingHom.ext fun x : (WK K)⟦X⟧ => constantCoeff_act (χ (g : GQ l) : ℤ_[l]) x)

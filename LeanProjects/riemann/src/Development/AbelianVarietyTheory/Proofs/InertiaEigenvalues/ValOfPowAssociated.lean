import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FreeAndInvariantsGen

noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.CycFr GlobalTheory.WachTie GlobalTheory.TorsionCard

namespace GlobalTheory.DelParam

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ} [Fact l.Prime]

omit [Fact l.Prime] in

theorem ring_of_const {e : ℕ} (ξ : O⟦X⟧) (hξ : Associated ξ (X ^ W.DelF.card))
    (hs : W.DelF.card ≠ 0) (hinv : ∀ δ ∈ W.DelF, W.γ₀ δ ξ = ξ)
    (hfree : ∀ b : O⟦X⟧, ∃! G : Fin W.DelF.card → O⟦X⟧,
      b = ∑ k : Fin W.DelF.card, X ^ (k : ℕ) * (G k).subst ξ)
    (hrange : ∀ b : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ b = b) ↔ ∃ g : O⟦X⟧, b = g.subst ξ)
    (E : Polynomial O) (hA : EisAt W l e ξ E) (ϖ : Fin e → O)
    (hE : E = ∏ τ, (Polynomial.X - Polynomial.C (ϖ τ)))
    (hv : ∀ τ, v (algebraMap O LL (ϖ τ)) = ((1 / (e : ℚ) : ℚ) : WithTop ℚ))
    (E₁ : Polynomial Qp) (h1 : E.map (algebraMap O LL) = E₁.map (algebraMap Qp LL))
    (x : K) (hx : Polynomial.aeval x E₁ = 0) :
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e W.DelF.card (fun _ => ξ) (fun _ => E) := by
  obtain ⟨-, hd, -, -, hq, ⟨c₁, u₁, hc₁⟩, ⟨c₂, u₂, hc₂⟩⟩ := hA
  have hX : (X : O⟦X⟧) ∣ ξ := (dvd_pow_self X hs).trans hξ.symm.dvd
  have hsub : HasSubst ξ := HasSubst.of_constantCoeff_zero' (X_dvd_iff.1 hX)
  have hun : ∀ c : O⟦X⟧, IsUnit c → IsUnit (c.subst ξ) := fun c hc => by
    rw [← coe_substAlgHom hsub]; exact hc.map _
  have hpi : ∀ c : O⟦X⟧, IsUnit c → ∃ w : (LetA O n)ˣ, (w : LetA O n) = fun _ => c :=
    fun c hc => Pi.isUnit_iff.2 fun _ => hc
  have hinj : ∀ f g : O⟦X⟧, (f.subst ξ : O⟦X⟧) = g.subst ξ → f = g := by
    intro f g hfg
    let k₀ : Fin W.DelF.card := ⟨0, Nat.pos_of_ne_zero hs⟩
    have key : ∀ f : O⟦X⟧, (f.subst ξ : O⟦X⟧) = ∑ k : Fin W.DelF.card,
        X ^ (k : ℕ) * ((Pi.single k₀ f : Fin W.DelF.card → O⟦X⟧) k).subst ξ := by
      intro f
      rw [Finset.sum_eq_single k₀ (fun k _ hk => by
        rw [Pi.single_eq_of_ne hk, ← coe_substAlgHom hsub, map_zero, mul_zero]) (by simp)]
      simp [k₀]
    have := (hfree (f.subst ξ)).unique (key f) (hfg.trans (key g))
    simpa using congrFun this k₀
  refine ⟨fun δ hδ => funext fun _ => hinv δ hδ, fun a ha => ?_, ?_, fun _ => hd, ?_, ?_, ?_,
    E₁.map (algebraMap Qp K₀), fun i => ?_, x, ?_, fun τ => ?_⟩
  · choose f hf using fun i => (hrange (a i)).1 fun δ hδ => congrFun (ha δ hδ) i
    exact ⟨f, hf, fun g hg => funext fun i => hinj _ _ ((hg i).symm.trans (hf i))⟩
  · obtain ⟨u, hu⟩ := hξ.symm
    obtain ⟨w, hw⟩ := hpi u u.isUnit
    exact ⟨w, by rw [hw]; exact funext fun _ => (hu.symm.trans (mul_comm _ _))⟩
  · obtain ⟨u, hu⟩ := hq
    obtain ⟨w, hw⟩ := hpi u u.isUnit
    exact ⟨w, by rw [hw]; exact funext fun _ => (hu.symm.trans (mul_comm _ _))⟩
  · obtain ⟨w, hw⟩ := hpi _ (hun c₁ u₁)
    exact ⟨w, by rw [hw]; exact funext fun _ => hc₁⟩
  · obtain ⟨w, hw⟩ := hpi _ (hun c₂ u₂)
    exact ⟨w, by rw [hw]; exact funext fun _ => hc₂⟩
  · rw [h1, Polynomial.map_map]
    congr 1
    exact RingHom.ext fun c => ((W.emb i).commutes c).symm
  · rw [Polynomial.aeval_map_algebraMap, hx]
  · have h2 : Polynomial.eval (τ x) (E.map (algebraMap O LL)) = 0 := by
      rw [h1, Polynomial.eval_map_algebraMap, Polynomial.aeval_algHom_apply, hx, map_zero]
    rw [hE, Polynomial.map_prod, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h2
    obtain ⟨τ', -, h3⟩ := h2
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at h3
    rw [h3, hv]

variable (χ : W.Gam →* ℤ_[l]ˣ)

def resid (g : W.Gam) : ℕ := (red l (χ g) : ZMod l).val

def nrm {R : Type} [CommRing R] (ζ : R) : R := ∏ δ ∈ W.DelF, (ζ ^ resid W χ δ - 1)

theorem map_nrm {R S F : Type} [CommRing R] [CommRing S] [FunLike F R S] [RingHomClass F R S]
    (f : F) (ζ : R) : f (nrm W χ ζ) = nrm W χ (f ζ) := by
  simp [nrm, map_prod]

theorem nrm_pow {R : Type} [CommRing R] (ζ : R) (hζ : ζ ^ l = 1) (d : W.Gam) (hd : d ∈ W.DelF) :
    nrm W χ (ζ ^ resid W χ d) = nrm W χ ζ := by
  rw [nrm, nrm, ← prod_DelF_mul W (fun δ => ζ ^ resid W χ δ - 1) d hd]
  refine Finset.prod_congr rfl fun δ _ => ?_
  simp only [resid, map_mul, Units.val_mul, ZMod.val_mul]
  rw [← pow_eq_pow_mod _ hζ, pow_mul]

theorem exists_torsion_resid (hl : l ≠ 2) (hχ : Function.Injective χ)
    (hk : ∀ x, red l x = 1 → ∃ g, χ g = x) (g : W.Gam) :
    ∃ d ∈ W.DelF, resid W χ d = resid W χ g := by
  obtain ⟨x, hx, hxu⟩ := exists_lift hl (red l (χ g))
  obtain ⟨h, hh⟩ := hk (x * (χ g)⁻¹) (by rw [map_mul, map_inv, hxu, mul_inv_cancel])
  have e : χ (h * g) = x := by rw [map_mul, hh, inv_mul_cancel_right]
  exact ⟨h * g, (mem_DelF_iff W _).2 (hχ.isOfFinOrder_iff.1 (e ▸ hx)), by rw [resid, e, hxu, resid]⟩

variable [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] (hp : PD.p = l)
  (hχ : ∀ g, algebraMap ℤ_[l] O (χ g : ℤ_[l]) = (W.χΓ g : O))
include hp hχ

theorem dvd_piNorm_sub (ζ : O) (hζ : ζ ^ l = 1) :
    (X - C (ζ - 1) : O⟦X⟧) ∣ piNorm W - C (nrm W χ ζ) := by
  have h0 : ∀ k : ℕ, (X - C (ζ - 1) : O⟦X⟧) ∣ (1 + X) ^ k - C ζ ^ k := fun k => by
    convert sub_dvd_pow_sub_pow (1 + X : O⟦X⟧) (C ζ) k using 1
    rw [map_sub, map_one]; ring
  have h1 : (X - C (ζ - 1) : O⟦X⟧) ∣ (1 + X) ^ l ^ 1 - 1 := by
    have := h0 l
    rwa [← map_pow, hζ, map_one, ← pow_one l] at this
  rw [piNorm, nrm, map_prod, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, map_prod, map_prod]
  refine Finset.prod_congr rfl fun δ _ => ?_
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, γ₀_eq W hp χ hχ, act_X]
  have h2 : (l : ℤ_[l]) ^ 1 ∣ (χ δ : ℤ_[l]) - (resid W χ δ : ℕ) := by
    rw [pow_one, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
      RingHom.mem_ker, map_sub, map_natCast, resid, ZMod.natCast_zmod_val, red_val, sub_self]
  have h3 := (h1.trans (dvd_bin_sub (O := O) 1 _ _ h2)).add (h0 (resid W χ δ))
  rw [bin_nat] at h3
  convert h3 using 1
  rw [map_sub, map_pow, map_one]; ring

theorem roots_eq_nrm [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hu : ¬ IsUnit (l : O)) {e : ℕ} (E : Polynomial O) (ϖ : Fin e → O)
    (hE : E = ∏ τ, (Polynomial.X - Polynomial.C (ϖ τ)))
    (hr : ∀ τ, ∃ ζ : O, IsPrimitiveRoot ζ l ∧ X - C (ζ - 1) ∣ piNorm W - C (ϖ τ))
    (hq : Associated (Polynomial.aeval (piNorm W) E) W.q₀) :
    (∀ τ, ∃ ζ : O, IsPrimitiveRoot ζ l ∧ ϖ τ = nrm W χ ζ) ∧
      ∀ ζ : O, IsPrimitiveRoot ζ l → ∃ τ, ϖ τ = nrm W χ ζ := by
  have key : ∀ (ζ x : O), IsPrimitiveRoot ζ l → X - C (ζ - 1) ∣ piNorm W - C x → x = nrm W χ ζ := by
    intro ζ x hζ hd
    refine sub_eq_zero.1 ((prime_X_sub_C _ (sub_one_mem_max hu ζ hζ.pow_eq_one)).2 _ ?_)
    convert (dvd_piNorm_sub W χ hp hχ ζ hζ.pow_eq_one).sub hd using 1
    rw [map_sub]; ring
  refine ⟨fun τ => ?_, fun ζ hζ => ?_⟩
  · obtain ⟨ζ, hζ, hd⟩ := hr τ
    exact ⟨ζ, hζ, key ζ _ hζ hd⟩
  · have h4 : X - C (ζ - 1) ∣ lvl l O 0 := by
      have h5 : lvl l O 0 = ∑ i ∈ Finset.range l, ((1 + X) ^ i - C ζ ^ i) := by
        rw [Finset.sum_sub_distrib]
        simp only [← map_pow]
        rw [← map_sum, hζ.geom_sum_eq_zero (Fact.out : l.Prime).one_lt]
        simp [lvl]
      rw [h5]
      refine Finset.dvd_sum fun i _ => ?_
      convert sub_dvd_pow_sub_pow (1 + X) (C ζ) i using 1
      rw [map_sub, map_one]; ring
    rw [← (φ₀_eq W hp).2] at h4
    have h6 := h4.trans hq.symm.dvd
    rw [hE, map_prod, (prime_X_sub_C _ (sub_one_mem_max hu ζ hζ.pow_eq_one)).1.dvd_finsetProd_iff] at h6
    obtain ⟨τ, -, hτ⟩ := h6
    rw [map_sub (Polynomial.aeval _), Polynomial.aeval_X, Polynomial.aeval_C] at hτ
    exact ⟨τ, key ζ _ hζ hτ⟩

omit [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] hp hχ in

theorem exists_lift_base {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
    (f : O →+* Ω) (hf : Function.Injective f) {e : ℕ} (ϖ : Fin e → O) (hϖ : Function.Injective ϖ)
    (h1 : ∀ τ, ∃ ζ : O, IsPrimitiveRoot ζ l ∧ ϖ τ = nrm W χ ζ)
    (h2 : ∀ ζ : O, IsPrimitiveRoot ζ l → ∃ τ, ϖ τ = nrm W χ ζ) :
    ∃ E₁ : Polynomial F, E₁.map (algebraMap F Ω) =
      (∏ τ, (Polynomial.X - Polynomial.C (ϖ τ))).map f := by
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  intro k
  refine (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 fun g => ?_
  have h3 : ∀ τ, ∃ τ', f (ϖ τ') = g (f (ϖ τ)) := by
    intro τ
    obtain ⟨ζ, hζ, hτ⟩ := h1 τ
    have hz := hζ.map_of_injective hf
    have hg := hz.map_of_injective g.injective
    have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
    obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one hg.pow_eq_one
    rw [← map_pow] at ha
    obtain ⟨τ', hτ'⟩ := h2 (ζ ^ a) (IsPrimitiveRoot.of_map_of_injective (ha ▸ hg) hf)
    exact ⟨τ', by rw [hτ', hτ, map_nrm, map_nrm, map_nrm, ha]⟩
  choose σ hσ using h3
  have hσi : Function.Injective σ := fun a b hab =>
    hϖ (hf (g.injective (by rw [← hσ, ← hσ, hab])))
  have h4 : ((∏ τ, (Polynomial.X - Polynomial.C (ϖ τ))).map f).map (g : Ω →+* Ω) =
      (∏ τ, (Polynomial.X - Polynomial.C (ϖ τ))).map f := by
    simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    refine Fintype.prod_bijective σ (Finite.injective_iff_bijective.1 hσi) _ _ fun τ => ?_
    rw [hσ]; rfl
  have h5 := congrArg (fun p => p.coeff k) h4
  simp only [Polynomial.coeff_map (g : Ω →+* Ω)] at h5
  exact h5

end Generic

variable {l : ℕ} [Fact l.Prime]

theorem val_of_pow_associated (P : LocPrime l) (LL : FinExt l) (x : ↥(OL LL)) (e : ℕ)
    (h : Associated (x ^ e) (l : ↥(OL LL))) :
    P.v LL (algebraMap ↥(OL LL) ↥LL.1 x) = ((1 / (e : ℚ) : ℚ) : WithTop ℚ) := by
  obtain ⟨u, hu⟩ := h
  have h0 : ∀ y : ↥(OL LL), 0 ≤ P.v LL (algebraMap ↥(OL LL) ↥LL.1 y) := fun y => (P.v_O LL _).2 y.2
  have h1 : P.v LL (algebraMap ↥(OL LL) ↥LL.1 u) = 0 := by
    have h2 := congrArg (fun y => P.v LL (algebraMap ↥(OL LL) ↥LL.1 y)) u.mul_inv
    simp only [map_mul, AddValuation.map_mul, map_one, AddValuation.map_one] at h2
    exact le_antisymm (h2 ▸ le_add_of_nonneg_right (h0 _)) (h0 _)
  have h3 := congrArg (fun y => P.v LL (algebraMap ↥(OL LL) ↥LL.1 y)) hu
  simp only [map_mul, AddValuation.map_mul, map_pow, AddValuation.map_pow, map_natCast, P.v_l, h1,
    add_zero] at h3
  generalize P.v LL (algebraMap ↥(OL LL) ↥LL.1 x) = a at h3
  have he : e ≠ 0 := by
    rintro rfl
    simp at h3
  induction a using WithTop.recTopCoe with
  | top =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
    rw [succ_nsmul, add_top] at h3
    exact absurd h3 WithTop.top_ne_one
  | coe a =>
    rw [← WithTop.coe_nsmul, ← WithTop.coe_one, WithTop.coe_inj, nsmul_eq_mul] at h3
    rw [WithTop.coe_inj, eq_div_iff (Nat.cast_ne_zero.2 he), mul_comm, h3]

theorem act_root (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (χ : W.Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) (g : ↥(GK K))
    (z : Om l) (hz : z ^ l = 1) : (g : GQ l) z = z ^ resid W χ (W.resΓ g) := by
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc g 1 z (by rwa [pow_one])
  have hr := W.χΓ_res g
  rw [P.PD_χ, ← hχ] at hr
  have h1 : ((χ (W.resΓ g) : ℤ_[l]) : ℚ_[l]) = (P.χQ g : ℚ_[l]) :=
    (algebraMap ℚ_[l] ↥LL.1).injective hr
  have h2 : (χ (W.resΓ g) : ℤ_[l]) - a ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, ← pow_one (l : ℤ_[l]),
      ← PadicInt.norm_le_pow_iff_mem_span_pow]
    rw [← h1] at ha
    exact ha
  rw [RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h2
  rw [hga, resid, red_val, h2, ZMod.val_natCast, ← pow_eq_pow_mod _ hz]

variable {P : LocPrime l} (H : LocHW l P) {K LL : FinExt l} (h : Good K 1 LL) (hl : l ≠ 2)
include hl

theorem card_ne_zero : (H.W K 1 LL h).DelF.card ≠ 0 := fun h0 => by
  have hc := card_torsion_mul_finrank P K LL (H.W K 1 LL h) hl h.2.2.1
  have h2l := (Fact.out : l.Prime).two_le
  rw [h0] at hc; omega

set_option maxHeartbeats 800000 in

theorem norm_ring (χ : (H.W K 1 LL h).Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = ((H.W K 1 LL h).χΓ g : ↥(OL LL)))
    (hk : ∀ x, red l x = 1 → ∃ g, χ g = x) :
    ∃ π' E', Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations (H.W K 1 LL h) (Module.finrank ↥(K0 K) ↥K.1)
      (H.W K 1 LL h).DelF.card π' E' := by
  have hA := exists_eisenstein H h hl _ (piNorm_spec _).1 (piNorm_spec _).2
  have hF := free_and_invariants H h _ (piNorm_spec _).1 (piNorm_spec _).2
  have hs := card_ne_zero H h hl
  have he : 0 < Module.finrank ↥(K0 K) ↥K.1 := Nat.pos_of_ne_zero fun h0 => by
    have hc := card_torsion_mul_finrank P K LL (H.W K 1 LL h) hl h.2.2.1
    have h2l := (Fact.out : l.Prime).two_le
    rw [h0] at hc; omega
  generalize Module.finrank ↥(K0 K) ↥K.1 = e at hA he
  generalize H.W K 1 LL h = W at *
  obtain ⟨E, ϖ, hE, hv, hr, hϖ, hA⟩ := hA
  obtain ⟨_, _, hu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨r1, r2⟩ := roots_eq_nrm W χ (P.PD_p K) hχ hu E ϖ hE hr hA.2.2.2.2.1
  let f₀ : ↥LL.1 →+* Om l := algebraMap _ _
  let f : ↥(OL LL) →+* Om l := f₀.comp (algebraMap ↥(OL LL) ↥LL.1)
  have hf : Function.Injective f := f₀.injective.comp Subtype.val_injective
  obtain ⟨E₁, hE₁⟩ := exists_lift_base (F := ℚ_[l]) W χ f hf ϖ hϖ r1 r2
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  have hx : f (ϖ ⟨0, he⟩) ∈ K.1 := by
    obtain ⟨ζ, hζ, hτ⟩ := r1 ⟨0, he⟩
    have hz := (hζ.map_of_injective hf).pow_eq_one
    rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
    intro g hg
    obtain ⟨d, hd, hdg⟩ := exists_torsion_resid W χ hl hχi hk (W.resΓ ⟨g, hg⟩)
    have h1 : g (f ζ) = f ζ ^ resid W χ d := hdg ▸ act_root P K LL W χ hχ ⟨g, hg⟩ _ hz
    rw [hτ, map_nrm, map_nrm, h1, nrm_pow W χ _ hz d hd]
  refine ⟨_, _, ring_of_const W _ (piNorm_spec W).1 hs (piNorm_spec W).2 hF.1 hF.2 E hA ϖ hE
    (fun τ => val_of_pow_associated P LL _ e (hv τ)) E₁ ?_ ⟨_, hx⟩ ?_⟩
  · apply Polynomial.map_injective f₀ f₀.injective
    rw [Polynomial.map_map, Polynomial.map_map, hE, ← hE₁]
    rfl
  · apply (algebraMap ↥K.1 (Om l)).injective
    rw [← Polynomial.aeval_algebraMap_apply, map_zero, ← Polynomial.eval_map_algebraMap, hE₁,
      Polynomial.map_prod, Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨0, he⟩) ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    exact sub_self _

set_option maxHeartbeats 800000 in

theorem trace_ring (h1 : Module.finrank ↥(K0 K) ↥K.1 = 1) :
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations (H.W K 1 LL h) 1 (l - 1) (H.W K 1 LL h).π₀
      (fun _ => Polynomial.X + Polynomial.C ((l : ℕ) : ↥(OL LL))) := by
  obtain ⟨hc, p2, p3, hA⟩ := trace_param H h hl h1
  have hF := free_and_invariants H h _ p2 p3
  have hs := card_ne_zero H h hl
  generalize H.W K 1 LL h = W at *
  rw [← hc]
  refine ring_of_const W _ p2 hs p3 hF.1 hF.2 _ hA (fun _ => -(l : ↥(OL LL))) ?_
    (fun _ => ?_) (Polynomial.X + Polynomial.C (l : ℚ_[l])) ?_ (-(l : ↥K.1)) ?_
  · rw [Fin.prod_univ_one, map_neg, sub_neg_eq_add]
  · exact val_of_pow_associated P LL _ 1 (by rw [pow_one]; exact Associated.rfl.neg_left)
  · simp
  · simp

end GlobalTheory.DelParam

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices in

theorem GlobalTheory.DelParam.torsion_parameters : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; W.s = 1 → l ≠ 2 → W.DelF.card = (l - 1) / Module.finrank ↥(K0 K) ↥K.1 ∧ (∃ π' E', wachRingRelations W (Module.finrank ↥(K0 K) ↥K.1) ((l - 1) / Module.finrank ↥(K0 K) ↥K.1) π' E') ∧ (Module.finrank ↥(K0 K) ↥K.1 = 1 → wachRingRelations W 1 (l - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((l : ℕ) : ↥(OL LL)))) := by
  intro D HW l _ K s LL h W hs hl
  obtain rfl : 1 = s := hs.symm.trans ((HW l).W_s K s LL h)
  obtain ⟨χ, hχ, -, -, -, -, -, hk⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K 1 LL h
  have hc := GlobalTheory.DelParam.card_eq (HW l) h hl
  refine ⟨hc, ?_, GlobalTheory.DelParam.trace_ring (HW l) h hl⟩
  rw [← hc]
  refine GlobalTheory.DelParam.norm_ring (HW l) h hl χ hχ fun x hx => hk x ?_
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, pow_one, ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, ← GlobalTheory.TorsionCard.red_val, hx]
  simp

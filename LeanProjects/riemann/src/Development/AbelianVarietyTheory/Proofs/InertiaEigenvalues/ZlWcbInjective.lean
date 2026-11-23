import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeNhds

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.Cyc.UnitGen

theorem gen {O R P : Type*} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup P] [Module O P]
    (f : R →ₐ[O] R) (hinj : Function.Injective (algebraMap O R))
    (hf : ∀ b, f b = b → ∃ x : O, b = algebraMap O R x) (e₀ t t' : P)
    (h0 : Submodule.span O {e₀} = ⊤) (htf : ∀ c : O, c • e₀ = 0 → c = 0)
    (ht : Submodule.span O {t} = ⊤) (r : R)
    (hr : r • ((1 : R) ⊗ₜ[O] t') = (1 : R) ⊗ₜ[O] e₀) :
    ∃ u : Oˣ, (1 : R) ⊗ₜ[O] t' = algebraMap O R u ⊗ₜ[O] t := by
  have hb : Function.Bijective (LinearMap.toSpanSingleton O P e₀) := by
    refine ⟨(injective_iff_map_eq_zero _).2 htf, ?_⟩
    rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton, h0]
  let φ : O ≃ₗ[O] P := LinearEquiv.ofBijective _ hb
  have hφ : ∀ c, φ c = c • e₀ := fun _ => rfl
  have h1 : φ.symm e₀ = 1 := by rw [LinearEquiv.symm_apply_eq, hφ, one_smul]
  obtain ⟨c, rfl⟩ := φ.surjective t'
  obtain ⟨w, rfl⟩ := φ.surjective t
  have hrc : r * algebraMap O R c = 1 := by
    have := congrArg (fun y => TensorProduct.rid O R (φ.symm.toLinearMap.lTensor R y)) hr
    simpa [TensorProduct.smul_tmul', h1, Algebra.smul_def, mul_comm] using this
  have hfr : f r = r := by
    have h2 : f r * algebraMap O R c = 1 := by
      rw [← f.commutes c, ← map_mul, hrc, map_one]
    calc f r = f r * (r * algebraMap O R c) := by rw [hrc, mul_one]
      _ = r * (f r * algebraMap O R c) := by ring
      _ = r := by rw [h2, mul_one]
  obtain ⟨c', rfl⟩ := hf r hfr
  have hc : c' * c = 1 := hinj (by rw [map_mul, hrc, map_one])
  obtain ⟨w', hw'⟩ := Submodule.mem_span_singleton.1 (ht ▸ Submodule.mem_top : e₀ ∈ Submodule.span O {φ w})
  have hw : w' * w = 1 := by
    apply φ.injective
    rw [← smul_eq_mul, map_smul, hw', hφ, one_smul]
  refine ⟨⟨c * w', c' * w, ?_, ?_⟩, ?_⟩
  · linear_combination (w' * w) * hc + hw
  · linear_combination (w' * w) * hc + hw
  · rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← map_smul, smul_eq_mul,
      mul_assoc, hw, mul_one]

variable {l : ℕ} [Fact l.Prime]

theorem zl_wcb_injective : Function.Injective (algebraMap ℤ_[l] (WCb l)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
  rcases mul_eq_zero.1 hx with h | h
  · exact ((PadicInt.unitCoeff h0).isUnit.map _).ne_zero h
  · exact WittVector.p_nonzero l (Cb l) (eq_zero_of_pow_eq_zero h)

theorem ol_rw_injective (LL : FinExt l) : Function.Injective (algebraMap ↥(OL LL) (RW LL)) :=
  haveI := GlobalTheory.Cyc.FontW.free_OL LL
  Algebra.TensorProduct.includeLeft_injective (S := ↥(OL LL)) zl_wcb_injective

theorem fixed_RW (LL : FinExt l) (b : RW LL) (hb : φRW LL b = b) :
    ∃ x : ↥(OL LL), b = algebraMap ↥(OL LL) (RW LL) x :=
  haveI := GlobalTheory.Cyc.FontW.free_OL LL
  (GlobalTheory.Cyc.FontW.as_one (O := ↥(OL LL)) (frobW l) (GlobalTheory.ArtinSchreierWitt.main l).1
    (GlobalTheory.ArtinSchreierWitt.main l).2.1).2 b hb

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem of_tie {W : LocWach PD LL O v n} {RA R : Type} [CommRing RA] [CommRing R] [Algebra O RA]
    [Algebra O R] {inclR : RA →ₐ[O] R} {φR : R →ₐ[O] R} {gR : G → (R →ₐ[O] R)} {πA : RA}
    (E : EtTie W RA R inclR φR gR πA) (hO : Function.Injective (algebraMap O LL))
    (hinj : Function.Injective (algebraMap O R))
    (hf : ∀ b, φR b = b → ∃ x : O, b = algebraMap O R x)
    (hT : ∀ b, TWmap φR W.one b = b → ∃ t : ↥W.one.L.T, b = (1 : R) ⊗ₜ[O] t)
    (e : W.DD W.one) (t : ↥W.one.L.T) (hN : W.N W.one = Submodule.span (LetA O n) {e})
    (hφ : W.φD W.one e = e) (ht : Submodule.span O {(t : W.one.V)} = W.one.L.T) :
    ∃ u : Oˣ, E.jD W.one e = algebraMap O R u ⊗ₜ[O] t := by
  obtain ⟨e', e₀, h0, hj, hN'⟩ := E.one_e
  obtain ⟨t', ht'⟩ := hT (E.jD W.one e) (by rw [← E.jD_φ, hφ])
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1
    (show e' ∈ Submodule.span (LetA O n) {e} by
      rw [← hN, hN']; exact Submodule.mem_span_singleton_self _)
  have hne : (e₀ : W.one.V) ≠ 0 := by
    obtain ⟨x, hx, hxT⟩ := W.one_line
    intro h
    have hxm : x ∈ W.one.L.T := by rw [hxT]; exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
      (h0 ▸ Submodule.mem_top : (⟨x, hxm⟩ : ↥W.one.L.T) ∈ Submodule.span O {e₀})
    have := congrArg Subtype.val hc
    rw [Submodule.coe_smul, h, smul_zero] at this
    exact hx this.symm
  rw [ht']
  refine gen φR hinj hf e₀ t t' h0 (fun c hc => ?_) ?_ (E.ioE (algebraMap _ W.EE a)) ?_
  · have := congrArg Subtype.val hc
    rw [Submodule.coe_smul, ← algebraMap_smul LL] at this
    exact hO (((smul_eq_zero.1 this).resolve_right hne).trans (map_zero _).symm)
  · rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
      (show x ∈ Submodule.span O {(t : W.one.V)} from ht.ge hx)
    exact Submodule.mem_span_singleton.2 ⟨c, Subtype.ext hc⟩
  · rw [← ht', ← E.jD_smul, algebraMap_smul, ha, hj]

end Gen

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ (e : W.DD W.one) (t : ↥W.one.L.T), W.N W.one = Submodule.span (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) {e} → W.φD W.one e = e → Submodule.span ↥(OL LL) {(t : W.one.V)} = W.one.L.T → ∃ u : (↥(OL LL))ˣ, E.jD W.one e = ((u : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (1 : WCb l) : RW LL) ⊗ₜ[↥(OL LL)] t := by
  intro D HW F l _ K s LL h W E e t hN hφ ht
  exact of_tie E Subtype.val_injective (ol_rw_injective LL) (fixed_RW LL)
    (GlobalTheory.Cyc.FontW.as_TW LL W.one).2 e t hN hφ ht

end GlobalTheory.Cyc.UnitGen

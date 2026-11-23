import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusCompatibleLiftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductHomEqOfAgreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfEnvelopeModPrimePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjOfTeichmullerCongrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorEqTeichmullerOfFrobeniusEqPowSelfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEisensteinImageTeichmullerPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorTeichmullerIsAdicCompleteOfPerfectStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorRingHomEqMapOfCoeffZeroStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isHausdorff_of_le_ideal {R : Type} [CommRing R] {I J : Ideal R} (h : I ≤ J) (hJ : IsHausdorff J R) :
    IsHausdorff I R := by
  refine ⟨fun x hx => hJ.haus x fun n => ?_⟩
  have h1 := hx n
  rw [SModEq.sub_mem] at h1 ⊢
  exact Submodule.smul_mono_left (Ideal.pow_right_mono h n) h1

theorem map_frobenius_charP {l : ℕ} [Fact l.Prime] {R O : Type} [CommRing R] [CharP R l] [CommRing O] [CharP O l]
    (ψ : R →+* O) (x : WittVector l R) :
    WittVector.map ψ (WittVector.frobenius x) = WittVector.frobenius (WittVector.map ψ x) := by
  ext n
  rw [WittVector.map_coeff, WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP,
    WittVector.map_coeff, map_pow]

theorem hom_comp_apply {l : ℕ} {R : Type} [CommRing R] {P P' P'' : Obj l R} (g : Hom P' P'') (f : Hom P P')
    (a : P.A) : (g.comp f).f a = g.f (f.f a) := rfl

theorem hom_eq_id_apply {l : ℕ} {R : Type} [CommRing R] {P P' : Obj l R} (g : Hom P' P) (f : Hom P P')
    (h : g.comp f = Hom.id P) (a : P.A) : g.f (f.f a) = a := by
  rw [← hom_comp_apply, h]; rfl

theorem hom_eq_comp_apply {l : ℕ} {R : Type} [CommRing R] {P P' P'' Q : Obj l R} (g : Hom P' P'') (f : Hom P P')
    (g' : Hom Q P'') (f' : Hom P Q) (h : g.comp f = g'.comp f') (a : P.A) : g.f (f.f a) = g'.f (f'.f a) := by
  rw [← hom_comp_apply, h]; rfl

theorem mapE_facts {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (O : Type) [CommRing O] [IsDomain O]
    [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O) (hx0 : ψ bk.flat ≠ 0)
    (hxu : ¬ IsUnit (ψ bk.flat)) (hxc : IsAdicComplete (Ideal.span {ψ bk.flat}) O) :
    WittVector.map ψ (bk.ev bk.E) ∈ nonZeroDivisors (WittVector l O) ∧
    IsHausdorff ((Ideal.span {((l : ℕ) : WittVector l (OCb l))} ⊔ Ideal.span {bk.ev bk.E}).map (WittVector.map ψ))
      (WittVector l O) := by
  obtain ⟨w, -, hwE⟩ := GlobalTheory.T.breuilKisin_eisenstein_image_teichmuller_pow l K bk O ψ hxu
  have hE0 : WittVector.map ψ (bk.ev bk.E) ≠ 0 := fun h => by
    have h1 := congrArg (WittVector.constantCoeff (p := l) (R := O)) h
    rw [hwE, map_add, map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, map_zero] at h1
    exact hx0 ((pow_eq_zero_iff bk.deg_pos.ne').1 h1)
  refine ⟨mem_nonZeroDivisors_of_ne_zero hE0, isHausdorff_of_le_ideal ?_
    (GlobalTheory.T.wittVector_teichmuller_isAdicComplete_of_perfect l O (ψ bk.flat) hx0 hxc).2.toIsHausdorff⟩
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast]
  refine sup_le le_sup_left ?_
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hwE]
  exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ bk.deg_pos))
    (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

theorem isHausdorff_map_congr {A B : Type} [CommRing A] [CommRing B] {I J : Ideal A} {g h : A →+* B} (hIJ : I = J)
    (hgh : g = h) (H : IsHausdorff (J.map h) B) : IsHausdorff (I.map g) B := by
  subst hIJ; subst hgh; exact H

theorem envPoint_eq {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X))
    (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O)
    (hx0 : ψ bk.flat ≠ 0) (hxu : ¬ IsUnit (ψ bk.flat)) (hxc : IsAdicComplete (Ideal.span {ψ bk.flat}) O)
    (F : En.Q.A →+* WittVector l O) (hFφ : ∀ a, F (En.Q.D.φ a) = WittVector.frobenius (F a))
    (hFinl : F.comp En.inl.f = WittVector.map ψ) (s : Hom En.Q (ainfObj K)) (hs1 : s.comp En.inl = Hom.id _)
    (hinr : F (BK.hf En.inr X) = WittVector.map ψ (s.f (BK.hf En.inr X))) (a : En.Q.A) :
    F a = WittVector.map ψ (s.f a) := by
  have hFi : ∀ b : WittVector l (OCb l), F (En.inl.f b) = WittVector.map ψ b := fun b => RingHom.congr_fun hFinl b
  have htfW : ∀ c : WittVector l O, ((l : ℕ) : WittVector l O) * c = 0 → c = 0 := fun c hc =>
    WittVector.eq_zero_of_p_mul_eq_zero c (by rw [mul_comm, hc])
  obtain ⟨F', hF'a⟩ : ∃ F' : En.Q.A →+* WittVector l O, ∀ a, F' a = WittVector.map ψ (s.f a) :=
    ⟨(WittVector.map ψ).comp s.f, fun _ => rfl⟩
  have hF'φ : ∀ a, F' (En.Q.D.φ a) = WittVector.frobenius (F' a) := fun a =>
    ((hF'a _).trans (congrArg (WittVector.map ψ) (Hom.f_φ s a))).trans
      ((map_frobenius_charP ψ (s.f a)).trans (congrArg WittVector.frobenius (hF'a a).symm))
  have hinl : ∀ b, F (En.inl.f b) = F' (En.inl.f b) := fun b =>
    (hFi b).trans ((congrArg (WittVector.map ψ) (hom_eq_id_apply s En.inl hs1 b).symm).trans (hF'a _).symm)
  have hE := (mapE_facts bk O ψ hx0 hxu hxc).1
  have hH := (mapE_facts bk O ψ hx0 hxu hxc).2
  have hnzd : F (En.inl.f (bk.ev bk.E)) ∈ nonZeroDivisors (WittVector l O) := by
    rw [hFi]; exact hE
  have hI : (ainfObj K).I = Ideal.span {bk.ev bk.E} := bk.span_ev.symm
  have hhaus : IsHausdorff ((Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I).map (F.comp En.inl.f))
      (WittVector l O) :=
    isHausdorff_map_congr (congrArg (Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ ·) hI) hFinl hH
  have hFF : F = F' :=
    GlobalTheory.T.breuilKisinPrismCoproduct_hom_eq_of_agree l K bk (ainfObj K) (bk.ev bk.E) (bk.ev X) En (WittVector l O) WittVector.frobenius F F'
      htfW hFφ hF'φ hinl (hinr.trans (hF'a _).symm) hnzd hhaus
  rw [hFF, hF'a]

theorem envPoint_factors : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K)
    (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharP O l] [PerfectRing O l] (f : En.Q.A →+* O), f (En.inl.f (bk.ev X)) ≠ 0 →
    ¬ IsUnit (f (En.inl.f (bk.ev X))) → IsAdicComplete (Ideal.span {f (En.inl.f (bk.ev X))}) O →
    ∃ (g : ↥(GK K)) (s : Hom En.Q (ainfObj K)) (ψ : OCb l →+* O), s.comp En.inl = Hom.id _ ∧
      s.comp En.inr = (ainfHom K g).comp bk.ι ∧
      ∀ a, f a = ψ (WittVector.coeff (p := l) (R := OCb l) (s.f a) 0) := by
  intro l _ K bk En O _ _ _ _ _ f hx0 hxu hxc
  have hcc : Function.Surjective (WittVector.constantCoeff (p := l) (R := OCb l)) := fun y =>
    ⟨WittVector.teichmuller l y, by rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩
  let f0 : WittVector l (OCb l) →+* O := f.comp En.inl.f
  have hker : RingHom.ker (WittVector.constantCoeff (p := l) (R := OCb l)) ≤ RingHom.ker f0 := by
    rw [WittVector.ker_constantCoeff, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      map_natCast, CharP.cast_eq_zero]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : OCb l →+* O, ∀ a : WittVector l (OCb l), f (En.inl.f a) = ψ (a.coeff 0) :=
    ⟨RingHom.liftOfSurjective _ hcc ⟨f0, hker⟩, fun a =>
      (RingHom.liftOfSurjective_comp_apply _ hcc ⟨f0, hker⟩ a).symm⟩
  have hflat : f (En.inl.f (bk.ev X)) = ψ bk.flat := by
    rw [hψ, bk.ev_X, WittVector.teichmuller_coeff_zero]
  rw [hflat] at hx0 hxu hxc
  obtain ⟨htf, -, -⟩ := GlobalTheory.T.ainf_envelope_mod_prime_properties l K bk En
  obtain ⟨F, hF0, hFφ⟩ := GlobalTheory.T.exists_frobenius_compatible_wittVector_lift l En.Q.A En.Q.D.φ
    (fun a => ⟨En.Q.D.δ a, by rw [En.Q.D.φ_eq]; ring⟩) htf O f
  have hFinl : F.comp En.inl.f = WittVector.map ψ :=
    GlobalTheory.T.wittVector_ringHom_eq_map_of_coeff_zero l (OCb l) O (F.comp En.inl.f) ψ (fun a => (hF0 (En.inl.f a)).trans (hψ a))
  have hFi : ∀ b : WittVector l (OCb l), F (En.inl.f b) = WittVector.map ψ b := fun b => RingHom.congr_fun hFinl b

  have hφX : En.Q.D.φ (BK.hf En.inr X) = BK.hf En.inr X ^ l :=
    calc En.Q.D.φ (BK.hf En.inr X) = BK.hf En.inr (frobS l bk.a X) := (Hom.f_φ En.inr X).symm
      _ = BK.hf En.inr (X ^ l) := by rw [frobS_X]
      _ = _ := map_pow _ _ _
  set v := F (BK.hf En.inr X) with hvdef
  have hv : WittVector.frobenius v = v ^ l := by
    rw [hvdef, ← hFφ, hφX, map_pow]
  have hvt := GlobalTheory.T.wittVector_eq_teichmuller_of_frobenius_eq_pow_self l O v hv
  have e1 : F (En.inl.f (bk.ev X)) = WittVector.teichmuller l (ψ bk.flat) := by
    rw [hFi, bk.ev_X, WittVector.map_teichmuller]
  have e2 : F (En.inl.f (bk.ev bk.E)) = WittVector.map ψ (bk.ev bk.E) := hFi _
  have h1 : v = F (En.inl.f (bk.ev X)) + F (En.inl.f (bk.ev bk.E)) * F En.w := by
    have := congrArg F En.w_eq
    rwa [map_add, map_mul] at this
  rw [e1, e2] at h1
  have hdvd : WittVector.map ψ (bk.ev bk.E) ∣
      WittVector.teichmuller l (v.coeff 0) - WittVector.teichmuller l (ψ bk.flat) :=
    ⟨F En.w, by rw [← hvt]; linear_combination h1⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_conj_of_teichmuller_congr l K bk O ψ hx0 hxu hxc (v.coeff 0) hdvd
  obtain ⟨s, ⟨hs1, hs2⟩, -⟩ := En.univ (ainfObj K) (Hom.id _) ((ainfHom K g).comp bk.ι)

  have hinr : F (BK.hf En.inr X) = WittVector.map ψ (s.f (BK.hf En.inr X)) := by
    have h2 : s.f (BK.hf En.inr X) = Per.σA (g : GQ l) (bk.ev X) :=
      hom_eq_comp_apply s En.inr _ _ hs2 X
    have h3 : WittVector.map ψ (Per.σA (g : GQ l) (bk.ev X)) =
        WittVector.teichmuller l (ψ (Per.σF (g : GQ l) bk.flat)) := by
      rw [bk.ev_X, GlobalTheory.RingIface.sigA_teich, WittVector.map_teichmuller]
    refine Eq.trans ?_ ((congrArg (WittVector.map ψ) h2).trans h3).symm
    exact hvdef.symm.trans (hvt.trans (congrArg (WittVector.teichmuller l) hg))
  refine ⟨g, s, ψ, hs1, hs2, fun a => ?_⟩
  rw [← hF0, envPoint_eq bk En O ψ hx0 hxu hxc F hFφ hFinl s hs1 hinr a]
  exact WittVector.map_coeff ψ (s.f a) 0

end GlobalTheory.BSP

import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OneMemOev

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

theorem sigR_oev {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : sigR (Fv F v) σ x ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨o, _, rfl⟩ := hx
    rw [sigR_inclR]
    exact incl_mem (F := F) v (⟨σ (o : E), (RingOfIntegers.isIntegral_coe o).map (σ : E →+* E).toIntAlgHom⟩ : 𝓞 E)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ h1 h2 => rw [map_add]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    change sigR (Fv F v) σ ((c : Fv F v) • x) ∈ _
    rw [Algebra.smul_def, map_mul, sigR_alg, ← Algebra.smul_def]
    exact Submodule.smul_mem _ c h

theorem unit_of_notMem (t : 𝓞 F) (ht : t ∉ v.asIdeal) :
    (algebraMap F (Fv F v) (t : F))⁻¹ ∈ v.adicCompletionIntegers F ∧ algebraMap F (Fv F v) (t : F) ≠ 0 := by
  have hv : Valued.v (algebraMap F (Fv F v) (t : F)) = (1 : WithZero (Multiplicative ℤ)) := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (t : F)
    rw [show algebraMap F (Fv F v) (t : F) = ((t : F) : Fv F v) from rfl, this,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v t).2 ht
  refine ⟨?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
  · intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv

theorem hR_sub_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (y - y') = hR (Fv F v) σ J x y - hR (Fv F v) σ J x y' := by
  rw [eq_sub_iff_add_eq, ← hR_add_right, sub_add_cancel]

theorem exists_int_smul_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨N1, h1, m1⟩ := hy
    obtain ⟨N2, h2, m2⟩ := hz
    refine ⟨N1 * N2, mul_ne_zero h1 h2, ?_⟩
    have e1 : (N1 * N2) • y = N2 • (N1 • y) := by rw [mul_comm, mul_smul]
    have e2 : (N1 * N2) • z = N1 • (N2 • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact L.add_mem (zsmul_mem m1 N2) (zsmul_mem m2 N1)
  | smul e y _ hy =>
    obtain ⟨N, hN, m⟩ := hy
    obtain ⟨c, hc, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
    have hi : IsIntegral ℤ (c • e) := hint e (Finset.mem_singleton_self e)
    refine ⟨c * N, mul_ne_zero hc hN, ?_⟩
    have e3 : (c * N) • (e • y) = (c • e) • (N • y) := by
      rw [mul_smul, smul_comm N e y, smul_assoc]
    rw [e3]
    have e4 : (c • e) • (N • y) = (⟨c • e, hi⟩ : 𝓞 E) • (N • y) := by
      rw [← algebraMap_smul E (⟨c • e, hi⟩ : 𝓞 E) (N • y)]; rfl
    rw [e4]
    exact L.smul_mem _ m

end Gen

variable {D : D7} (X : HidaSetting D)

theorem fixed_ex (a : X.B.I.E) (ha : star a = a) : ∃ f : X.B.I.F, algebraMap X.B.I.F X.B.I.E f = a := by
  obtain ⟨f, hf⟩ := (X.B.I.cm.fixed a).1 ha
  exact ⟨f, hf⟩

theorem val_le (v : PlX X) (f : X.B.I.F)
    (hf : inclR (F := X.B.I.F) (Fv X.B.I.F v) (algebraMap X.B.I.F X.B.I.E f) ∈ OEv (E := X.B.I.E) v) :
    v.valuation X.B.I.F f ≤ 1 := by
  rw [← alg_alg] at hf
  have := int_of_alg v _ hf
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, show algebraMap X.B.I.F (Fv X.B.I.F v) f = (f : Fv X.B.I.F v) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  exact this

open Polynomial in

theorem denom (v : PlX X) (e : X.B.I.E) (he : inclR (F := X.B.I.F) (Fv X.B.I.F v) e ∈ OEv (E := X.B.I.E) v) :
    ∃ s : 𝓞 X.B.I.F, s ∉ v.asIdeal ∧ ∃ c : 𝓞 X.B.I.E, (c : X.B.I.E) = algebraMap X.B.I.F X.B.I.E s * e := by
  have hse : inclR (F := X.B.I.F) (Fv X.B.I.F v) (star e) ∈ OEv (E := X.B.I.E) v := by
    have := sigR_oev X.B.I.cm.sig v he
    rwa [sigR_inclR] at this
  obtain ⟨fT, hfT⟩ := fixed_ex X (e + star e) (by rw [star_add, star_star, add_comm])
  obtain ⟨fN, hfN⟩ := fixed_ex X (e * star e) (by rw [star_mul, star_star])
  have vT : v.valuation X.B.I.F fT ≤ 1 := val_le X v fT (by rw [hfT, map_add]; exact Submodule.add_mem _ he hse)
  have vN : v.valuation X.B.I.F fN ≤ 1 := val_le X v fN (by rw [hfN, map_mul]; exact oev_mul v he hse)
  obtain ⟨nT, ⟨dT, hdT⟩, hT⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v fT vT
  obtain ⟨nN, ⟨dN, hdN⟩, hN⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v fN vN
  refine ⟨dT * dN, ?_, ?_⟩
  · exact (Ideal.primeCompl v.asIdeal).mul_mem hdT hdN
  · let φ := algebraMap X.B.I.F X.B.I.E
    let ψ := algebraMap (𝓞 X.B.I.F) X.B.I.F
    have hy_eq : (φ (ψ (dT * dN)) * e) ^ 2 - φ (ψ (dN * nT)) * (φ (ψ (dT * dN)) * e) +
        φ (ψ (dT * dT * dN * nN)) = 0 := by
      simp only [map_mul ψ]
      rw [← hT, ← hN]
      simp only [map_mul φ]
      rw [hfT, hfN]
      ring
    have h𝓞 : IsIntegral (𝓞 X.B.I.F) (φ (ψ (dT * dN)) * e) := by
      refine ⟨Polynomial.X ^ 2 - C (dN * nT) * Polynomial.X + C (dT * dT * dN * nN), ?_, ?_⟩
      · monicity!
      · simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X]
        rw [IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) X.B.I.F X.B.I.E (dN * nT),
          IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) X.B.I.F X.B.I.E (dT * dT * dN * nN)]
        exact hy_eq
    exact ⟨⟨_, isIntegral_trans _ h𝓞⟩, rfl⟩

def liftE (r : 𝓞 X.B.I.F) : 𝓞 X.B.I.E :=
  ⟨algebraMap X.B.I.F X.B.I.E (r : X.B.I.F),
    (RingOfIntegers.isIntegral_coe r).map (IsScalarTower.toAlgHom ℤ X.B.I.F X.B.I.E)⟩

theorem liftE_coe (r : 𝓞 X.B.I.F) : ((liftE X r : 𝓞 X.B.I.E) : X.B.I.E) = algebraMap X.B.I.F X.B.I.E (r : X.B.I.F) :=
  rfl

def starE (a : 𝓞 X.B.I.E) : 𝓞 X.B.I.E :=
  ⟨star (a : X.B.I.E), (RingOfIntegers.isIntegral_coe a).map (starRingEnd X.B.I.E).toIntAlgHom⟩

theorem hform_zero_left (x : Fin X.B.I.n → X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J 0 x = 0 := by
  simp [Formalism.UG.hform]

theorem hform_add_left (y y' x : Fin X.B.I.n → X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (y + y') x =
      Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y x + Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y' x := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_smul_left (a : 𝓞 X.B.I.E) (y x : Fin X.B.I.n → X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (a • y) x =
      star (a : X.B.I.E) * Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y x := by
  simp only [Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, map_mul, starRingEnd_apply (algebraMap (𝓞 X.B.I.E) X.B.I.E a)]
  ring

theorem hform_smul_right (y x : Fin X.B.I.n → X.B.I.E) (c : X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y (c • x) = c * Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y x := by
  simp only [Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem locGlob (v : PlX X) (x : Fin X.B.I.n → X.B.I.E)
    (hx : ∀ l ∈ X.B.I.L, inclR (F := X.B.I.F) (Fv X.B.I.F v) (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l x) ∈
      OEv (E := X.B.I.E) v) :
    ∃ t : 𝓞 X.B.I.F, t ∉ v.asIdeal ∧ algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) • x ∈ X.B.I.L := by
  classical
  obtain ⟨S, hS⟩ := X.B.I.L_fg
  have hSL : ∀ g ∈ S, g ∈ X.B.I.L := fun g hg => hS ▸ Submodule.subset_span hg
  have hg : ∀ g ∈ S, ∃ s : 𝓞 X.B.I.F, s ∉ v.asIdeal ∧ ∃ c : 𝓞 X.B.I.E,
      (c : X.B.I.E) = algebraMap X.B.I.F X.B.I.E s * Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J g x :=
    fun g hgS => denom X v _ (hx g (hSL g hgS))
  choose! s hs c hc using hg
  set t : 𝓞 X.B.I.F := ∏ g ∈ S, s g with ht_def
  have ht : t ∉ v.asIdeal := by
    intro h
    have := v.isPrime
    obtain ⟨g, hgS, hg⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hs g hgS hg
  set T : X.B.I.E := algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) with hT
  have hkey : ∀ g ∈ S, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J g (T • x) ∈
      (algebraMap (𝓞 X.B.I.E) X.B.I.E).range := by
    intro g hgS
    rw [hform_smul_right]
    refine ⟨liftE X (∏ h ∈ S.erase g, s h) * c g, ?_⟩
    rw [map_mul]
    show ((liftE X (∏ h ∈ S.erase g, s h) : 𝓞 X.B.I.E) : X.B.I.E) * ((c g : 𝓞 X.B.I.E) : X.B.I.E) = _
    rw [hc g hgS, liftE_coe, hT, ht_def, ← Finset.mul_prod_erase S s hgS]
    have hm : ((s g * ∏ x ∈ S.erase g, s x : 𝓞 X.B.I.F) : X.B.I.F) =
        (s g : X.B.I.F) * ((∏ x ∈ S.erase g, s x : 𝓞 X.B.I.F) : X.B.I.F) := map_mul (algebraMap _ _) _ _
    rw [hm, map_mul]
    ring
  refine ⟨t, ht, ?_⟩
  refine (X.B.I.L_dual _).2 fun y hy => ?_
  rw [← hS] at hy
  induction hy using Submodule.span_induction with
  | mem g hg => exact hkey g hg
  | zero => rw [hform_zero_left]; exact ⟨0, map_zero _⟩
  | add y y' _ _ h1 h2 =>
      obtain ⟨c1, e1⟩ := h1
      obtain ⟨c2, e2⟩ := h2
      exact ⟨c1 + c2, by rw [map_add, e1, e2, hform_add_left]⟩
  | smul a y _ h1 =>
      obtain ⟨c1, e1⟩ := h1
      exact ⟨starE X a * c1, by rw [map_mul, e1, hform_smul_left]; rfl⟩

theorem cube (v : PlX X) : ∃ M : ℤ, M ≠ 0 ∧ ∀ u : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E,
    (∀ i, u i ∈ OEv (E := X.B.I.E) v) → (M : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) • u ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
  classical
  have h : ∀ j : Fin X.B.I.n, ∃ N : ℤ, N ≠ 0 ∧ N • (Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) ∈ X.B.I.L :=
    fun j => exists_int_smul_mem X.B.I.L X.B.I.L_span _
  choose N hN0 hNL using h
  set M : ℤ := ∏ j, N j with hM
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hN0 j
  have hML : ∀ j, M • (Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) ∈ X.B.I.L := by
    intro j
    rw [hM, ← Finset.mul_prod_erase Finset.univ N (Finset.mem_univ j), mul_comm, mul_smul]
    exact zsmul_mem (hNL j) _
  refine ⟨M, hM0, fun u hu => ?_⟩
  have hsingle : ∀ j, ∀ t ∈ OEv (E := X.B.I.E) v,
      (Pi.single j ((M : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) * t) : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ∈
        latLoc (E := X.B.I.E) v (abelian₂ X) := by
    intro j t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨o, _, rfl⟩ := ht
      refine Submodule.subset_span ⟨o • (M • Pi.single j (1 : X.B.I.E)), X.B.I.L.smul_mem o (hML j), ?_⟩
      funext i
      simp only [ratV, Pi.smul_apply, Pi.single_apply]
      split_ifs with hij
      · simp [Algebra.smul_def, map_mul, mul_comm]
      · simp
    | zero => rw [mul_zero, Pi.single_zero]; exact Submodule.zero_mem _
    | add t t' _ _ h1 h2 => rw [mul_add, Pi.single_add]; exact Submodule.add_mem _ h1 h2
    | smul c t _ h1 =>
      have e : (Pi.single j ((M : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) * (c • t)) : Fin X.B.I.n → _) =
          c • (Pi.single j ((M : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) * t) : Fin X.B.I.n → _) := by
        funext i
        simp only [Pi.single_apply, Pi.smul_apply]
        split_ifs <;> simp
      rw [e]; exact Submodule.smul_mem _ c h1
  have hs : (M : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) • u =
      ∑ j, (Pi.single j ((M : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) * u j) : Fin X.B.I.n → _) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hs]
  exact Submodule.sum_mem _ fun j _ => hsingle j (u j) (hu j)

theorem omVSDBwd_holds : OmVSDBwd X := by
  intro v y hy
  obtain ⟨M, hM, hcube⟩ := cube X v
  choose e w hw he using fun j => approx v M hM (y j)
  have hd : y - ratV (F := X.B.I.F) (Fv X.B.I.F v) e ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
    have : y - ratV (F := X.B.I.F) (Fv X.B.I.F v) e = (M : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) • w :=
      funext fun j => he j
    rw [this]; exact hcube w hw
  have hpair : ∀ l ∈ X.B.I.L, inclR (F := X.B.I.F) (Fv X.B.I.F v)
      (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l e) ∈ OEv (E := X.B.I.E) v := by
    intro l hl
    have h1 : inclR (F := X.B.I.F) (Fv X.B.I.F v) (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l e) =
        hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) l)
          (ratV (F := X.B.I.F) (Fv X.B.I.F v) e) :=
      (hR_ratTup (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J ![l, e] 0 1).symm
    rw [h1]
    have hl' : ratV (F := X.B.I.F) (Fv X.B.I.F v) l ∈ latLoc (E := X.B.I.E) v (abelian₂ X) :=
      Submodule.subset_span ⟨l, hl, rfl⟩
    have e2 : ratV (F := X.B.I.F) (Fv X.B.I.F v) e = y - (y - ratV (F := X.B.I.F) (Fv X.B.I.F v) e) := by abel
    rw [e2, hR_sub_right]
    exact Submodule.sub_mem _ (hy _ hl') (omVSD_fwd X v hl' hd)
  obtain ⟨s, hs, hsL⟩ := locGlob X v e hpair
  have hre : ratV (F := X.B.I.F) (Fv X.B.I.F v) e ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
    obtain ⟨hinv, hne⟩ := unit_of_notMem v s hs
    have hm : ratV (F := X.B.I.F) (Fv X.B.I.F v) (algebraMap X.B.I.F X.B.I.E (s : X.B.I.F) • e) ∈
        latLoc (E := X.B.I.E) v (abelian₂ X) := Submodule.subset_span ⟨_, hsL, rfl⟩
    have heq : ratV (F := X.B.I.F) (Fv X.B.I.F v) e =
        (⟨(algebraMap X.B.I.F (Fv X.B.I.F v) (s : X.B.I.F))⁻¹, hinv⟩ : v.adicCompletionIntegers X.B.I.F) •
          ratV (F := X.B.I.F) (Fv X.B.I.F v) (algebraMap X.B.I.F X.B.I.E (s : X.B.I.F) • e) := by
      funext j
      show inclR (F := X.B.I.F) (Fv X.B.I.F v) (e j) = (algebraMap X.B.I.F (Fv X.B.I.F v) (s : X.B.I.F))⁻¹ •
        inclR (F := X.B.I.F) (Fv X.B.I.F v) (algebraMap X.B.I.F X.B.I.E (s : X.B.I.F) * e j)
      rw [map_mul, ← alg_alg, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [heq]; exact Submodule.smul_mem _ _ hm
  have e3 : y = (y - ratV (F := X.B.I.F) (Fv X.B.I.F v) e) + ratV (F := X.B.I.F) (Fv X.B.I.F v) e := by abel
  rw [e3]; exact Submodule.add_mem _ hd hre

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

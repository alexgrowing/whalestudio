import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowEqSpan
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DetIntOfLevel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevMuDet

open GlobalTheory.Mem.Col2 GlobalTheory.Mem.ReadEx GlobalTheory.Mem.LocTriv Formalism.L2.Host

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_mem_only (P : HeightOneSpectrum (𝓞 E)) :
    ∃ s : 𝓞 E, s ∈ P.asIdeal ∧ (s : E) ≠ 0 ∧ ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → s ∉ Q.asIdeal := by
  obtain ⟨n, s, hn, hs⟩ := GlobalTheory.TwU.MuUnr.exists_pow_eq_span P
  refine ⟨s, Ideal.pow_le_self hn.ne' (hs ▸ Ideal.mem_span_singleton_self s), fun h0 => ?_, fun w hw h => ?_⟩
  · have : s = 0 := by exact_mod_cast h0
    subst this
    rw [Ideal.span_singleton_eq_bot.2 rfl] at hs
    exact P.ne_bot (pow_eq_zero_iff hn.ne' |>.1 hs)
  · have h1 : P.asIdeal ^ n ≤ w.asIdeal := by rw [hs, Ideal.span_le, Set.singleton_subset_iff]; exact h
    exact hw (HeightOneSpectrum.ext (P.isMaximal.eq_of_le w.isPrime.ne_top (w.isPrime.le_of_pow_le h1))).symm

theorem component_tmul_one (P : HeightOneSpectrum (𝓞 E)) (b : E) :
    evP F P (b ⊗ₜ[F] 1) = algebraMap E (P.adicCompletion E) b := by
  change afIso F E (b ⊗ₜ[F] 1) P = _
  rw [afIso_tmul_one]
  rfl

theorem ext_evP {a b : AfE F E} (h : ∀ P, evP F P a = evP F P b) : a = b :=
  (afIso F E).injective (FiniteAdeleRing.ext _ h)

theorem component_map_eq_zero {F' E' : Type} [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E']
    (φ : AfE F E →+* AfE F' E') (hφ : ∀ y ∈ RInt F E, φ y ∈ RInt F' E') {P : HeightOneSpectrum (𝓞 E)} {P' : HeightOneSpectrum (𝓞 E')}
    (hP : ∀ b ∈ P.asIdeal, ∃ b' ∈ P'.asIdeal, φ ((b : E) ⊗ₜ[F] 1) = (b' : E') ⊗ₜ[F'] 1) {z : AfE F E} (hz : evP F P z = 0) :
    evP F' P' (φ z) = 0 := by
  obtain ⟨s, hs, hs0, hsQ⟩ := exists_mem_only P
  obtain ⟨s', hs', e⟩ := hP s hs
  set ε : AfE F E := (afIso F E).symm (1 - Formalism.UG.P.afsplitI P 1) with hε
  have hεv : ∀ Q, evP F Q ε = 1 - Formalism.UG.P.afsplitI P 1 Q := fun Q => by
    change afIso F E ε Q = _
    rw [hε, RingEquiv.apply_symm_apply]
    rfl
  have h0 : evP F P ε = 0 := by rw [hεv, Formalism.UG.P.afsplitI_self, sub_self]
  have h1 : ∀ Q, Q ≠ P → evP F Q ε = 1 := fun Q hQ => by rw [hεv, Formalism.UG.P.afsplitI_ne P Q hQ, sub_zero]
  have hmul : ∀ w : AfE F E, evP F P w = 0 → ε * w = w := fun w hw => ext_evP fun Q => by
    rw [map_mul]
    by_cases hQ : Q = P
    · subst hQ
      rw [hw, mul_zero]
    · rw [h1 Q hQ, one_mul]
  have hc : ((s : E)⁻¹ ⊗ₜ[F] 1) * ε ∈ RInt F E := by
    refine (mem_rInt_iff F E _).2 fun Q => ?_
    change Valued.v (evP F Q (((s : E)⁻¹ ⊗ₜ[F] 1) * ε)) ≤ 1
    rw [map_mul, component_tmul_one]
    by_cases hQ : Q = P
    · subst hQ
      rw [h0, mul_zero, map_zero]
      exact zero_le'
    · rw [h1 Q hQ, mul_one, Formalism.UG.P.levelaf_valued_algebraMap, map_inv₀, GlobalTheory.NormOneUnit.val_eq_one (hsQ Q hQ), inv_one]
  have hεs : ε = ((s : E) ⊗ₜ[F] 1) * (((s : E)⁻¹ ⊗ₜ[F] 1) * ε) := by
    rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hs0, one_mul, ← Algebra.TensorProduct.one_def, one_mul]
  have hlt : Valued.v (evP F' P' (φ ε)) < 1 := by
    rw [hεs, map_mul, map_mul, map_mul, e, component_tmul_one, Formalism.UG.P.levelaf_valued_algebraMap]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' ((mem_rInt_iff F' E' _).1 (hφ _ hc) P'))
      ((HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hs')
  have hid : evP F' P' (φ ε) * evP F' P' (φ ε) = evP F' P' (φ ε) := by
    rw [← map_mul, ← map_mul, hmul ε h0]
  have hz0 : evP F' P' (φ ε) = 0 := by
    by_contra hne
    rw [mul_eq_left₀ hne] at hid
    rw [hid, map_one] at hlt
    exact lt_irrefl _ hlt
  rw [← hmul z hz, map_mul, map_mul, hz0, zero_mul]

theorem prV_eq_one {v : HeightOneSpectrum (𝓞 F)} {z : AfE F E}
    (h : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → evP F P z = 1) : Formalism.UG.prV (E := E) v z = 1 := by
  have e : Formalism.UG.P.afsplitEps E v * (z - 1) = 0 := ext_evP fun P => by
    rw [map_mul, map_zero]
    by_cases hP : P.under (𝓞 F) = v
    · rw [map_sub, h P hP, map_one, sub_self, mul_zero]
    · have h2 := afIso_one_tmul (E := E) (P := P) (k := (0 : F)) (a := Formalism.UG.P.afsplitI v 1)
        (by rw [Formalism.UG.P.afsplitI_ne v _ hP, map_zero])
      rw [map_zero, map_zero] at h2
      have h3 : evP F P (Formalism.UG.P.afsplitEps E v) = 0 := by
        rw [Formalism.UG.P.afsplitEps, show (1 : E ⊗[F] HeightOneSpectrum.adicCompletion F v) = 1 ⊗ₜ[F] 1 from rfl,
          Formalism.UG.P.afsplitIE_tmul]
        exact h2
      rw [h3, zero_mul]
  have e2 := congrArg (Formalism.UG.prV (E := E) v) e
  rwa [map_mul, Formalism.UG.P.afsplit_prV_eps, one_mul, map_zero, map_sub, map_one, sub_eq_zero] at e2

omit [NumberField F] [Algebra F E] [Field F] in

theorem exists_int_congr {P : HeightOneSpectrum (𝓞 E)} {a : E} (ha : P.valuation E a = 1) :
    ∃ b : 𝓞 E, b ∉ P.asIdeal ∧ redP P a = Ideal.Quotient.mk P.asIdeal b ∧ P.valuation E (a - b) < 1 := by
  obtain ⟨r, s, hrs⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer P a ha.le
  have hs : (s : 𝓞 E) ∉ P.asIdeal := s.2
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (redP P a)
  have h1 := reduction_spec P hs ((mul_comm _ _).trans hrs)
  rw [← hb, ← map_mul, Ideal.Quotient.eq] at h1
  have hlt : P.valuation E (a - b) < 1 := by
    have h2 : P.valuation E (((s : 𝓞 E) : E) * (a - b)) < 1 := by
      have e : ((s : 𝓞 E) : E) * (a - b) = -algebraMap (𝓞 E) E ((s : 𝓞 E) * b - r) := by
        rw [map_sub, map_mul, ← hrs]
        ring
      rw [e, Valuation.map_neg]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 h1
    rwa [map_mul, GlobalTheory.NormOneUnit.val_eq_one hs, one_mul] at h2
  refine ⟨b, fun hm => ?_, hb.symm, hlt⟩
  have h3 := Valuation.map_add_lt _ hlt ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) P b).2 hm)
  rw [sub_add_cancel, ha] at h3
  exact lt_irrefl _ h3

theorem loc_eq_locK {χ : HChar E} {P : HeightOneSpectrum (𝓞 E)} (h : χ.TameAt P) {x : (P.adicCompletion E)ˣ} {k : Eˣ}
    (hk : P.valuation E (k : E) = 1) (hx : Valued.v ((x : P.adicCompletion E) - algebraMap E _ (k : E)) < 1) :
    χ.loc P x = χ.locK P k := by
  have hk' : Valued.v (algebraMap E (P.adicCompletion E) (k : E)) = 1 := by rw [Formalism.UG.P.levelaf_valued_algebraMap, hk]
  have h1 : Valued.v (x : P.adicCompletion E) = 1 := by
    rw [← hk'] at hx ⊢
    exact Valuation.map_eq_of_sub_lt _ hx
  have h0 : algebraMap E (P.adicCompletion E) (k : E) ≠ 0 := by simp
  change χ.loc P x = χ.loc P (atFin P k)
  have e : ((x / atFin P k : (P.adicCompletion E)ˣ) : P.adicCompletion E) = x / algebraMap E _ (k : E) :=
    Units.val_div_eq_div_val _ _
  rw [← div_eq_one, ← map_div]
  refine h _ ?_ (le_exp_neg_one ?_)
  · unfold IsUnitAt
    rw [e, map_div₀, h1, hk', div_one]
  · rw [e, div_sub_one h0, map_div₀, hk', div_one]
    exact hx

theorem sigR_mem_rInt (σ : E →ₐ[F] E) {y : AfE F E} (hy : y ∈ RInt F E) :
    Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) y ∈ RInt F E := by
  have hle : RInt F E ≤ (RInt F E).comap (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F)) := by
    refine (Subring.closure_le).2 ?_
    rintro g (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨c, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨⟨σ (algebraMap (𝓞 E) E b), ⟨RingOfIntegers.mapRingHom (σ : E →+* E) b, ?_⟩⟩, ?_⟩)
      · rfl
      · simp [Formalism.UG.sigR]
    · refine Subring.subset_closure (Or.inr ⟨c, ?_⟩)
      simp [Formalism.UG.sigR]
  exact hle hy

theorem h90_mem_U1_of_involutive (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (k : (AfE F E)ˣ) : h90 σ k ∈ U1 σ := by
  have h : conjId σ (conjId σ k) = k := by
    apply Units.ext
    show Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) (k : AfE F E)) = k
    induction (k : AfE F E) using TensorProduct.induction_on with
    | zero => simp
    | tmul e c => simp [Formalism.UG.sigR, hσ]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  show k / conjId σ k * conjId σ (k / conjId σ k) = 1
  rw [map_div, h, div_mul_div_cancel, div_self']

theorem div_h90_mul_eq_mul_sigR (σ : E →ₐ[F] E) (a b : (AfE F E)ˣ) :
    ((a / h90 σ b : (AfE F E)ˣ) : AfE F E) * b = a * Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) b := by
  have e : a / h90 σ b * b = a * conjId σ b := by
    rw [show h90 σ b = b / conjId σ b from rfl, div_div_eq_mul_div, div_mul_cancel]
  exact congrArg Units.val e

theorem evP_div_h90_eq_one (σ : E →ₐ[F] E) (a b : (AfE F E)ˣ) (Q : HeightOneSpectrum (𝓞 E))
    (key : evP F Q (a : AfE F E) * evP F Q (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) b) = evP F Q (b : AfE F E)) :
    evP F Q ((a / h90 σ b : (AfE F E)ˣ) : AfE F E) = 1 := by
  have e2 := congrArg (evP F Q) (div_h90_mul_eq_mul_sigR σ a b)
  rw [map_mul, map_mul, key] at e2
  exact (mul_eq_right₀ (b.isUnit.map (evP F Q)).ne_zero).1 e2

variable (F) in

def partAf (y : (AfE F E)ˣ) (S : Finset (HeightOneSpectrum (𝓞 E))) : (AfE F E)ˣ := finAf F E (part (toIdl F E y) S)

theorem component_mulIndicator_of_mem (y : (AfE F E)ˣ) {S : Finset (HeightOneSpectrum (𝓞 E))} {P : HeightOneSpectrum (𝓞 E)} (h : P ∈ S) :
    evP F P (partAf F y S : AfE F E) = evP F P (y : AfE F E) :=
  (GlobalTheory.Mem.ReadTwist.afIso_finAf_apply _ P).trans (ev_part_mem _ h)

theorem component_mulIndicator_of_notMem (y : (AfE F E)ˣ) {S : Finset (HeightOneSpectrum (𝓞 E))} {P : HeightOneSpectrum (𝓞 E)} (h : P ∉ S) :
    evP F P (partAf F y S : AfE F E) = 1 :=
  (GlobalTheory.Mem.ReadTwist.afIso_finAf_apply _ P).trans (ev_part_not_mem _ h)

theorem partAf_mem_intU {y : (AfE F E)ˣ} (hy : y ∈ intU F E) (S : Finset (HeightOneSpectrum (𝓞 E))) : partAf F y S ∈ intU F E := by
  refine (mem_intU_iff _).2 fun P => ?_
  change Valued.v (evP F P (partAf F y S : AfE F E)) = 1
  by_cases h : P ∈ S
  · rw [component_mulIndicator_of_mem y h]
    exact (mem_intU_iff _).1 hy P
  · rw [component_mulIndicator_of_notMem y h, map_one]

theorem map_part {χ : HChar E} (h : ∀ P, χ.TameAt P) (y : (AfE F E)ˣ) (S : Finset (HeightOneSpectrum (𝓞 E))) (k : S → Eˣ)
    (hk : ∀ P : S, P.1.valuation E (k P : E) = 1)
    (hx : ∀ P : S, Valued.v (evP F P.1 (y : AfE F E) - algebraMap E _ (k P : E)) < 1) :
    χ.1 (part (toIdl F E y) S) = ∏ P : S, χ.locK P.1 (k P) := by
  rw [part, map_prod, ← Finset.prod_coe_sort]
  exact Finset.prod_congr rfl fun P _ => loc_eq_locK (h P.1) (hk P) (hx P)

end General

section Columns

open GlobalTheory.NormOneUnit

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem g_notMem_of_goodPl (hPr : Pr.Ok) (hS : ∀ i, Pr.g i ∈ S) {P : HeightOneSpectrum (𝓞 X.E)}
    (h : GoodPl X.E S (P.under (𝓞 X.F))) (i : Fin 2) : ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun gi => by
  refine h.2.2 ?_
  rw [(GlobalTheory.Mem.ReadTwist.plc_under_eq_iff (F := X.F) P (hPr.g_prime i)).2 gi]
  exact hS i

theorem g_mem_of_vGs (hPr : Pr.Ok) {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vGs) : ∃ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
  obtain ⟨i, hi⟩ := mem_vGs h
  exact ⟨i, hPr.piG_norm i ▸ P.asIdeal.mul_mem_left _ hi⟩

theorem conjP_notMem_rowSG (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S) {P : HeightOneSpectrum (𝓞 X.E)}
    (h : P ∈ rowSG Pr sel mu) : conjPrime₂ P ∉ rowSG Pr sel mu := fun h' => by
  classical
  have hn : ∀ (Q : HeightOneSpectrum (𝓞 X.E)) (n : ℕ), (n : 𝓞 X.E) ∈ (conjPrime₂ Q).asIdeal ↔ (n : 𝓞 X.E) ∈ Q.asIdeal := fun Q n => by
    rw [mem_conjP, map_natCast]
  rcases Finset.mem_union.1 h with h | h <;> rcases Finset.mem_union.1 h' with h' | h'
  · exact conjP_notMem_vGs hPr h h'
  · obtain ⟨i, hi⟩ := g_mem_of_vGs hPr h
    exact g_notMem_of_goodPl hPr hS (mem_QE mu hsel h').2 i ((hn _ _).2 hi)
  · obtain ⟨i, hi⟩ := g_mem_of_vGs hPr h'
    exact g_notMem_of_goodPl hPr hS (mem_QE mu hsel h).2 i ((hn _ _).1 hi)
  · exact conjP_notMem_QE mu hX hsel h h'

theorem rhoT_mul_rhoS (i : ℕ) (P : rowSG Pr sel mu) {a : X.E} (h : IsUnit (redP P.1 a)) :
    rhoT Ch sel mu i P a * rhoS Ch sel mu i P a = 1 := by
  rw [rhoT, rhoS, LocE.unitV, LocE.unitV, dif_pos h, dif_pos h, ← Units.val_mul]
  split_ifs <;> simp

theorem value_part (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S) {σ₀ : X.K →+* ℂ} {ee : X.Tau → ℚ} {j : Fin R.m}
    {χ : HChar X.E} (hμ : Formalism.L2.Col.IsMu0 Ch σ₀ ee j χ) {y : (AfE X.F X.E)ˣ} (hy : y ∈ intU X.F X.E) (e : rowSG Pr sel mu → X.E)
    (he : ∀ P : rowSG Pr sel mu,
      Valued.v (evP X.F P.1 ((y⁻¹ : (AfE X.F X.E)ˣ) : AfE X.F X.E) * algebraMap X.E _ (e P) - 1) < 1) :
    ((χ.1 (part (toIdl X.F X.E y) (rowSG Pr sel mu)) : ℂˣ) : ℂ) *
        σ₀ (((mu : Chr X.F X.E X.K) (partAf X.F y (rowSG Pr sel mu)) : X.Kˣ) : X.K) = σ₀ (∏ P, rhoT Ch sel mu j.1 P (e P)) ∧
      ∀ P : rowSG Pr sel mu, IsUnit (redP P.1 (e P)) := by
  classical
  obtain ⟨ξ, hξ⟩ := exists_reads σ₀ (mu : Chr X.F X.E X.K) mu.2.1.1.1.1.1 mu.2.1.1.1.1.2
  have hξt := GlobalTheory.Mem.ReadTwist.tameAt hξ fun v => Subgroup.mem_iInf.1 mu.2.1.2 v
  have hyv : ∀ P, Valued.v (evP X.F P (y : AfE X.F X.E)) = 1 := (mem_intU_iff _).1 hy
  have h1 : ∀ P : rowSG Pr sel mu, Valued.v (evP X.F P.1 (y : AfE X.F X.E) - algebraMap X.E _ (e P)) < 1 := fun P => by
    have e1 : evP X.F P.1 (y : AfE X.F X.E) * evP X.F P.1 ((y⁻¹ : (AfE X.F X.E)ˣ) : AfE X.F X.E) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have e2 : evP X.F P.1 (y : AfE X.F X.E) - algebraMap X.E _ (e P) = -(evP X.F P.1 (y : AfE X.F X.E) *
        (evP X.F P.1 ((y⁻¹ : (AfE X.F X.E)ˣ) : AfE X.F X.E) * algebraMap X.E _ (e P) - 1)) := by
      linear_combination (algebraMap X.E (P.1.adicCompletion X.E) (e P)) * e1
    rw [e2, Valuation.map_neg, map_mul, hyv, one_mul]
    exact he P
  have h2 : ∀ P : rowSG Pr sel mu, P.1.valuation X.E (e P) = 1 := fun P => by
    have h3 := h1 P
    rw [← Formalism.UG.P.levelaf_valued_algebraMap, ← hyv P.1]
    rw [← hyv P.1, ← Valuation.map_neg, neg_sub] at h3
    exact Valuation.map_eq_of_sub_lt _ h3
  choose b hb hr hv using fun P : rowSG Pr sel mu => exists_int_congr (h2 P)
  have h0 : ∀ P, (b P : X.E) ≠ 0 := fun P e0 => hb P ((RingOfIntegers.coe_eq_zero_iff.1 e0) ▸ zero_mem _)
  have hun : ∀ P : rowSG Pr sel mu, IsUnit (redP P.1 (e P)) := fun P => by
    have := P.1.isMaximal
    obtain ⟨c, hc⟩ := Ideal.Quotient.exists_inv (I := P.1.asIdeal) (a := Ideal.Quotient.mk _ (b P))
      (fun h => hb P (Ideal.Quotient.eq_zero_iff_mem.1 h))
    rw [hr]
    exact IsUnit.of_mul_eq_one _ hc
  refine ⟨?_, hun⟩
  have hk : ∀ P : rowSG Pr sel mu, P.1.valuation X.E ((Units.mk0 _ (h0 P) : X.Eˣ) : X.E) = 1 := fun P => val_eq_one (hb P)
  have hx : ∀ P : rowSG Pr sel mu,
      Valued.v (evP X.F P.1 (y : AfE X.F X.E) - algebraMap X.E _ ((Units.mk0 _ (h0 P) : X.Eˣ) : X.E)) < 1 := fun P => by
    have h4 := hv P
    rw [← Formalism.UG.P.levelaf_valued_algebraMap, map_sub] at h4
    have h5 := Valuation.map_add_lt _ (h1 P) h4
    rwa [sub_add_sub_cancel] at h5
  rw [partAf, ← hξ, map_part hμ.tame y _ _ hk hx, map_part hξt y _ _ hk hx, ← Units.val_mul, ← Finset.prod_mul_distrib,
    Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [rhoT, LocE.unitV, dif_pos (hun P), Units.val_mul]
  by_cases hP : P.1 ∈ Pr.vGs
  · have hu : ξ.UnrAt P.1 := by
      by_contra hn
      obtain ⟨i, hi⟩ := g_mem_of_vGs hPr hP
      refine g_notMem_of_goodPl hPr hS (by_contra fun hg => ?_) i hi
      exact (GlobalTheory.Mem.ReadTwist.mem_qprime_iff hξ _).2 ⟨P.1, rfl, hn⟩ (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 mu.2.2 _) hg)
    rw [if_pos hP, locK_unr hu (hk P), Units.val_one, mul_one, hμ.atg ⟨P.1, hP⟩ _ (b P) (hun P).unit rfl (hr P), chiP, dif_pos hP,
      chiAt, extChi, dif_pos j.2]
    rfl
  · have hQ := (Finset.mem_union.1 P.2).resolve_left hP
    rw [if_neg hP, locK_unr (hμ.unr P.1 (g_notMem_of_goodPl hPr hS (mem_QE mu hsel hQ).2)) (hk P), Units.val_one, one_mul,
      resChar_eq hξ hξt P.1 (hun P).unit (b P) (Units.mk0 _ (h0 P)) rfl (hr P).symm]

end Columns

section Host

open Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

variable {D : D7} {X : Fields} (s : Seam D X)

theorem conjP_seamP (hs : s.Ok) (P : HeightOneSpectrum (𝓞 X.E)) : conjPrime₂ (seamP s P) = seamP s (conjPrime₂ P) := by
  ext y
  obtain ⟨x, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective y
  rw [mem_conjP, mem_seamP, mem_conjP]
  have h : cO D.host.E (RingOfIntegers.mapRingEquiv s.iE x) = RingOfIntegers.mapRingEquiv s.iE (cO X.E x) := by
    apply RingOfIntegers.ext
    show star (s.iE (x : X.E)) = s.iE (star (x : X.E))
    rw [hs.2, star_eq_conj]
  rw [h, mem_seamP]

theorem eq_map_or_eq_map_conj_of_liesOver (hs : s.Ok) {P : HeightOneSpectrum (𝓞 X.E)} {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : IsOver v (seamP s P))
    {Q : HeightOneSpectrum (𝓞 D.host.E)} (hQ : Q.under (𝓞 D.host.F) = v) : Q = seamP s P ∨ Q = seamP s (conjPrime₂ P) := by
  have hc : ∃ a : D.host.E, star a ≠ a := by
    by_contra hn
    push Not at hn
    have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun e => (D.sp.cm.fixed e).1 (hn e)
    have h1 : Module.finrank D.host.F D.host.E = 1 :=
      (LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E)
        ⟨(algebraMap D.host.F D.host.E).injective, hs⟩)).symm.trans (Module.finrank_self _)
    have h2 := D.sp.cm.deg2
    omega
  rw [← conjP_seamP s hs]
  exact (GlobalTheory.NormOneUnit.under_eq_iff (fun x => (D.sp.cm.fixed _).2 ⟨x, rfl⟩) D.sp.cm.deg2 hc _ Q).1
    (hQ.trans (HeightOneSpectrum.ext hv))

variable {s} (ι : AfE X.F X.E ≃+* AfE D.host.F D.host.E) (hrat : ∀ x : X.E, ι (x ⊗ₜ[X.F] 1) = s.iE x ⊗ₜ[D.host.F] 1)
  (hint : ∀ y, ι y ∈ RInt D.host.F D.host.E ↔ y ∈ RInt X.F X.E)

include hrat hint

theorem component_transport_eq_zero {P : HeightOneSpectrum (𝓞 X.E)} {z : AfE X.F X.E} (hz : evP X.F P z = 0) : evP D.host.F (seamP s P) (ι z) = 0 :=
  component_map_eq_zero ι.toRingHom (fun y hy => (hint y).2 hy)
    (fun b hb => ⟨RingOfIntegers.mapRingEquiv s.iE b, (mem_seamP s P b).2 hb, hrat b⟩) hz

theorem component_transport_conj_eq_zero (hs : s.Ok) {P : HeightOneSpectrum (𝓞 X.E)} {z : AfE X.F X.E} (hz : evP X.F (conjPrime₂ P) z = 0) :
    evP D.host.F (seamP s P) (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ι z)) = 0 := by
  refine component_map_eq_zero ((Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).comp ι.toRingHom)
    (fun y hy => sigR_mem_rInt _ ((hint y).2 hy))
    (fun b hb => ⟨RingOfIntegers.mapRingEquiv s.iE (cO X.E b), (mem_seamP s P _).2 ((mem_conjP P b).1 hb), ?_⟩) hz
  change Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ι ((b : X.E) ⊗ₜ[X.F] 1)) =
    s.iE (star (b : X.E)) ⊗ₜ[D.host.F] 1
  rw [hrat, hs.2, ← star_eq_conj]
  rfl

theorem valued_lt_of_intAtA {P : HeightOneSpectrum (𝓞 X.E)} {z : AfE X.F X.E}
    (h : IntAtA (F := D.host.F) (seamP s P) (iA D.host.F D.host.E ((qOf (seamP s P) : D.host.E))⁻¹ * ι z)) :
    Valued.v (evP X.F P z) < 1 := by
  obtain ⟨r', hr', hm⟩ := h
  obtain ⟨r, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective r'
  rw [mem_seamP] at hr'
  set q : ℕ := qOf (seamP s P) with hq
  have hqP : (q : 𝓞 X.E) ∈ P.asIdeal := by
    rw [← mem_seamP s, map_natCast]
    exact Ideal.absNorm_mem _
  have hq0 : (q : X.E) ≠ 0 := by
    have : q ≠ 0 := fun h0 => (seamP s P).ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  have e : iA D.host.F D.host.E (algebraMap (𝓞 D.host.E) D.host.E (RingOfIntegers.mapRingEquiv s.iE r)) *
      (iA D.host.F D.host.E ((q : D.host.E))⁻¹ * ι z) = ι (((r : X.E) ⊗ₜ[X.F] 1) * (((q : X.E)⁻¹ ⊗ₜ[X.F] 1) * z)) := by
    rw [map_mul, map_mul, hrat, hrat, map_inv₀ s.iE, map_natCast s.iE]
    rfl
  have h1 : Valued.v (evP X.F P (((r : X.E) ⊗ₜ[X.F] 1) * (((q : X.E)⁻¹ ⊗ₜ[X.F] 1) * z))) ≤ 1 :=
    (mem_rInt_iff _ _ _).1 ((hint _).1 (e ▸ hm)) P
  rw [map_mul, map_mul, map_mul, map_mul, component_tmul_one, component_tmul_one, Formalism.UG.P.levelaf_valued_algebraMap, Formalism.UG.P.levelaf_valued_algebraMap,
    GlobalTheory.NormOneUnit.val_eq_one hr', one_mul, map_inv₀, inv_mul_le_one₀ (zero_lt_iff.2 (by simpa using hq0))] at h1
  refine lt_of_le_of_lt h1 ?_
  rw [← map_natCast (algebraMap (𝓞 X.E) X.E)]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hqP

set_option maxHeartbeats 800000 in

theorem normOne_idele_eq_hilbert90_part_at_primes (hs : s.Ok) {S : Finset (HeightOneSpectrum (𝓞 X.E))} (hS : ∀ P ∈ S, conjPrime₂ P ∉ S) {y : (AfE X.F X.E)ˣ}
    (hy : Units.map ι.toRingHom.toMonoidHom y ∈ U1 (sigD D)) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ S)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : IsOver v (seamP s P)) :
    Formalism.UG.prV (E := D.host.E) v ((Units.map ι.toRingHom.toMonoidHom y /
      h90 (sigD D) (Units.map ι.toRingHom.toMonoidHom (partAf X.F y S)) : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) = 1 := by
  refine prV_eq_one fun Q hQ => ?_
  set σ := Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) with hσ
  set x := partAf X.F y S with hx
  have hn : ι y * σ (ι y) = 1 := congrArg Units.val (show _ * _ = 1 from hy)
  have key : evP D.host.F Q (ι y) * evP D.host.F Q (σ (ι x)) = evP D.host.F Q (ι x) := by
    rcases eq_map_or_eq_map_conj_of_liesOver s hs hv hQ with rfl | rfl
    · have a1 := component_transport_eq_zero ι hrat hint (P := P) (z := x - y) (by rw [map_sub, component_mulIndicator_of_mem y hP, sub_self])
      have a2 := component_transport_conj_eq_zero ι hrat hint hs (P := P) (z := x - 1) (by rw [map_sub, component_mulIndicator_of_notMem y (hS P hP), map_one, sub_self])
      rw [map_sub, map_sub, sub_eq_zero] at a1
      rw [map_sub, map_sub, map_sub, map_one, map_one, map_one, sub_eq_zero] at a2
      rw [a1, a2, mul_one]
    · have a1 := component_transport_eq_zero ι hrat hint (P := conjPrime₂ P) (z := x - 1) (by rw [map_sub, component_mulIndicator_of_notMem y (hS P hP), map_one, sub_self])
      have a2 := component_transport_conj_eq_zero ι hrat hint hs (P := conjPrime₂ P) (z := x - y)
        (by rw [GlobalTheory.MuConj.conjP_involutive, map_sub, component_mulIndicator_of_mem y hP, sub_self])
      rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at a1
      rw [map_sub, map_sub, map_sub, sub_eq_zero] at a2
      rw [a1, a2, ← map_mul, hn, map_one]
  exact evP_div_h90_eq_one _ _ _ Q key

end Host

end GlobalTheory.LevMuDet

open GlobalTheory.LevMuDet GlobalTheory.Mem.Col2 GlobalTheory.Mem.ReadEx GlobalTheory.Mem.LocTriv Formalism.L2.Forms in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LevMuDet.muOf_det_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    MuLaw t u μ dtU → ∀ i, i < D.R.m → ∀ j (hj : j ≤ D.R.m) (β : (St j hj).Ch) (κ : ((St j hj).K β).lev.U) (e : SB t μ → t.X.E),
      (∀ P : SB t μ, IntAtA (F := D.host.F) (seamP t.seam P.1)
        (iA D.host.F D.host.E ((qOf (seamP t.seam P.1) : D.host.E))⁻¹ *
          ((((Matrix.GeneralLinearGroup.det κ.1)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
            iA D.host.F D.host.E (t.seam.iE (e P)) - 1))) →
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (∏ P, rhoS t.Ch t.sel (t.tup μ) i P (e P)) = 1 ∧
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) = t.seam.σ₀ (∏ P, rhoT t.Ch t.sel (t.tup μ) i P (e P))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _ hMu i hi j hj β κ e he
  letI := D.host.cmStar
  obtain ⟨h1, ⟨-, h2⟩, -, h4, -⟩ := hMu i hi
  set d := Matrix.GeneralLinearGroup.det κ.1 with hd
  have hdU : d ∈ U1 (sigD D) := by
    have h := GlobalTheory.Port.det_norm_one (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D j hj) κ.1 ((((St j hj).K β).lev.U_eq κ.1).1 κ.2).1
    rw [mul_comm] at h
    exact Units.ext h
  have hdI : d ∈ intU D.host.F D.host.E := by
    refine ⟨GlobalTheory.Port.det_int_of_level _ κ.1 κ.2, ?_⟩
    have h := GlobalTheory.Port.det_int_of_level _ κ.1⁻¹ (inv_mem κ.2)
    rw [← Matrix.GeneralLinearGroup.val_det_apply, map_inv] at h
    exact h
  obtain ⟨y, hy⟩ : ∃ y : (AfE t.X.F t.X.E)ˣ, Units.map A.iA.toRingHom.toMonoidHom y = d :=
    ⟨Units.map A.iA.symm.toRingHom.toMonoidHom d, Units.ext (A.iA.apply_symm_apply _)⟩
  have hmap : ∀ z : (AfE t.X.F t.X.E)ˣ, Units.map A.iA.toRingHom.toMonoidHom z ∈ intU D.host.F D.host.E ↔ z ∈ intU t.X.F t.X.E := fun z =>
    and_congr (hP.iA_int z) (hP.iA_int ((z⁻¹ : (AfE t.X.F t.X.E)ˣ) : AfE t.X.F t.X.E))
  have hyI : y ∈ intU t.X.F t.X.E := (hmap y).1 (hy ▸ hdI)
  have hS := hP.avoid.1
  obtain ⟨hval, hun⟩ := value_part (t.tup μ) t.pr_ok hP.sel hS (hP.mu0 ⟨i, hi⟩) hyI e fun P => by
    have h := valued_lt_of_intAtA A.iA hP.iA_rat hP.iA_int (P := P.1)
      (z := ((y⁻¹ : (AfE t.X.F t.X.E)ˣ) : AfE t.X.F t.X.E) * (e P ⊗ₜ[t.X.F] 1) - 1) (by
        have h3 := he P
        rw [← hy] at h3
        rw [map_sub, map_mul, map_one, hP.iA_rat]
        exact h3)
    rwa [map_sub, map_mul, map_one, component_tmul_one] at h
  set x := partAf t.X.F y (SB t μ) with hx
  set x' := Units.map A.iA.toRingHom.toMonoidHom x with hx'
  have hxI : x' ∈ intU D.host.F D.host.E := (hmap x).2 (partAf_mem_intU hyI _)
  have hhU : h90 (sigD D) x' ∈ U1 (sigD D) := h90_mem_U1_of_involutive _ (fun b => star_star b) x'
  have hhI : h90 (sigD D) x' ∈ intU D.host.F D.host.E :=
    div_mem hxI ⟨sigR_mem_rInt _ hxI.1, sigR_mem_rInt _ hxI.2⟩
  have hw : muOf t u μ dtU (i + 1) (d / h90 (sigD D) x') = 1 := by
    refine h4 _ (div_mem hdU hhU) (div_mem hdI hhI) ?_
    rintro v ⟨P, hPS, hv⟩
    rw [← hy] at hdU ⊢
    exact normOne_idele_eq_hilbert90_part_at_primes A.iA hP.iA_rat hP.iA_int t.seam_ok
      (fun Q hQ => conjP_notMem_rowSG (t.tup μ) hP.fields.ok t.pr_ok hP.sel hS hQ) hdU hPS hv
  have hsc := GlobalTheory.Port.scalar_mem_U1Af (D := D) (h90 (sigD D) x') (by
    rw [mul_comm]
    exact congrArg Units.val (show _ * _ = 1 from hhU))
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) (h90 (sigD D) x')) = h90 (sigD D) x' := by
    rw [Matrix.GeneralLinearGroup.det_scalar]
    simp
  have hq : A.q x = dtU ⟨_, hsc⟩ := hP.q_dt x ⟨_, hsc⟩ hdet
  have hι : IsAdIso (afIso t.X.F t.X.E) := ⟨afIso_tmul_one _ _, mem_rInt_iff _ _⟩
  have hmu : D.muTil (i + 1) (A.q x) = (t.glob.mu0 ⟨i, hi⟩).1 (part (toIdl t.X.F t.X.E y) (SB t μ)) :=
    hP.muTil _ hι ⟨i, hi⟩ _ x (fun w => congrFun (part_fst _ _) w) (afIso_finAf _ _ _)
  have hT2 : muOf t u μ dtU (i + 1) d = t.seam.σ₀ (∏ P, rhoT t.Ch t.sel (t.tup μ) i P (e P)) := by
    have e1 := h2 _ (div_mem hdU hhU) _ hhU
    have e2 := h1 ⟨_, hsc⟩
    rw [div_mul_cancel, hw, one_mul] at e1
    rw [e1, ← hval, ← hmu]
    refine (congrArg _ hdet.symm).trans (e2.trans ?_)
    rw [← hq]
    by_cases hμ : μ = D.what₂.mu0
    · rw [(hP.ref hμ).2, (hP.ref hμ).1]
      simp
    · obtain ⟨ξ, hξ, hmt⟩ := hP.tw μ hμ rfl
      rw [hmt u, twMt, if_pos ⟨by omega, by omega⟩, MonoidHom.mul_apply, Units.val_mul, hξ x]
      rfl
  refine ⟨?_, hT2⟩
  rw [hT2, ← map_mul, ← Finset.prod_mul_distrib, Finset.prod_eq_one fun P _ => rhoT_mul_rhoS (t.tup μ) i P (hun P), map_one]

end

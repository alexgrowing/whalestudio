import Formalism.LocalToGlobal.UnitaryNorms.CharHost

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

section General

variable {L : Type} [Field L] [NumberField L] {F : Type} [Field F] [NumberField F] [Algebra F L]

namespace HChar

theorem resFin_apply (χ : HChar L) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    χ.resFin v k = ∏ P ∈ aboveF (L := L) F v, χ.locK P (upF F k) := by
  simp [HChar.resFin]

theorem resInf_apply (χ : HChar L) (w : InfinitePlace F) (k : Fˣ) :
    χ.resInf w k = ∏ w' ∈ aboveInf (L := L) F w, χ.locInf w' (atInf w' (upF F k)) := by
  simp [HChar.resInf]

theorem resFin_mul (χ χ' : HChar L) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    (χ * χ').resFin v k = χ.resFin v k * χ'.resFin v k := by
  rw [resFin_apply, resFin_apply, resFin_apply, ← Finset.prod_mul_distrib]; rfl

theorem resFin_inv (χ : HChar L) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    (χ⁻¹).resFin v k = (χ.resFin v k)⁻¹ := by
  rw [resFin_apply, resFin_apply, ← Finset.prod_inv_distrib]; rfl

theorem resInf_mul (χ χ' : HChar L) (w : InfinitePlace F) (k : Fˣ) :
    (χ * χ').resInf w k = χ.resInf w k * χ'.resInf w k := by
  rw [resInf_apply, resInf_apply, resInf_apply, ← Finset.prod_mul_distrib]; rfl

theorem resInf_inv (χ : HChar L) (w : InfinitePlace F) (k : Fˣ) :
    (χ⁻¹).resInf w k = (χ.resInf w k)⁻¹ := by
  rw [resInf_apply, resInf_apply, ← Finset.prod_inv_distrib]; rfl

theorem TrivOn.mul {χ χ' : HChar L} (h : χ.TrivOn F) (h' : χ'.TrivOn F) : (χ * χ').TrivOn F :=
  ⟨fun v k => by rw [resFin_mul, h.1, h'.1, one_mul], fun w k => by rw [resInf_mul, h.2, h'.2, one_mul]⟩

theorem TrivOn.inv {χ : HChar L} (h : χ.TrivOn F) : (χ⁻¹).TrivOn F :=
  ⟨fun v k => by rw [resFin_inv, h.1, inv_one], fun w k => by rw [resInf_inv, h.2, inv_one]⟩

theorem ResEta.mul {χ ξ : HChar L} (h : χ.ResEta F) (h' : ξ.TrivOn F) : (χ * ξ).ResEta F :=
  ⟨fun v k => by rw [resFin_mul, h.1, h'.1, mul_one], fun w k => by rw [resInf_mul, h.2, h'.2, mul_one]⟩

theorem ResEta.div {χ χ' : HChar L} (h : χ.ResEta F) (h' : χ'.ResEta F) : (χ' * χ⁻¹).TrivOn F :=
  ⟨fun v k => by rw [resFin_mul, resFin_inv, h.1, h'.1, mul_inv_cancel],
    fun w k => by rw [resInf_mul, resInf_inv, h.2, h'.2, mul_inv_cancel]⟩

theorem LevelLe.mul {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)} {n : ℕ} (h : χ.LevelLe v n) (h' : χ'.LevelLe v n) :
    (χ * χ').LevelLe v n := fun x hx hx' => by rw [loc_mul, h x hx hx', h' x hx hx', one_mul]

theorem LevelLe.inv {χ : HChar L} {v : HeightOneSpectrum (𝓞 L)} {n : ℕ} (h : χ.LevelLe v n) :
    (χ⁻¹).LevelLe v n := fun x hx hx' => by rw [loc_inv, h x hx hx', inv_one]

theorem UnrAt.mul {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v) (h' : χ'.UnrAt v) :
    (χ * χ').UnrAt v := fun x hx => by rw [loc_mul, h x hx, h' x hx, one_mul]

theorem UnrAt.inv {χ : HChar L} {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v) :
    (χ⁻¹).UnrAt v := fun x hx => by rw [loc_inv, h x hx, inv_one]

theorem UnrAt.levelLe {χ : HChar L} {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v) (n : ℕ) : χ.LevelLe v n :=
  fun x hx _ => h x hx

theorem IsUnitary.mul {χ χ' : HChar L} (h : χ.IsUnitary) (h' : χ'.IsUnitary) : (χ * χ').IsUnitary := fun x => by
  show ‖((χ.1 x * χ'.1 x : ℂˣ) : ℂ)‖ = 1
  rw [Units.val_mul, norm_mul, h x, h' x, one_mul]

theorem IsUnitary.inv {χ : HChar L} (h : χ.IsUnitary) : (χ⁻¹).IsUnitary := fun x => by
  show ‖(((χ.1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
  rw [Units.val_inv_eq_inv_val, norm_inv, h x, inv_one]

theorem HasInf.mul_triv {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n : I → ℤ} {χ ξ : HChar L}
    (h : χ.HasInf φ n) (h' : ∀ k, ξ.inf k = 1) : (χ * ξ).HasInf φ n := fun k => by
  rw [inf_mul, h' k, mul_one]; exact h k

theorem HasInf.div {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n : I → ℤ} {χ χ' : HChar L}
    (h : χ.HasInf φ n) (h' : χ'.HasInf φ n) (k : Lˣ) : (χ' * χ⁻¹).inf k = 1 := by
  rw [inf_mul, inf_inv, mul_inv_eq_one]
  exact Units.ext ((h' k).trans (h k).symm)

theorem HasInfQ.mul_triv {I : Type} [Fintype I] {φ : I → L →+* ℂ} {a : I → ℚ} {χ ξ : HChar L}
    (h : χ.HasInfQ φ a) (h' : ∀ k, ξ.inf k = 1) : (χ * ξ).HasInfQ φ a := by
  obtain ⟨n, hn, h⟩ := h
  exact ⟨n, hn, h.mul_triv h'⟩

theorem HasInfQ.div {I : Type} [Fintype I] {φ : I → L →+* ℂ} {a : I → ℚ} {χ χ' : HChar L}
    (h : χ.HasInfQ φ a) (h' : χ'.HasInfQ φ a) (k : Lˣ) : (χ' * χ⁻¹).inf k = 1 := by
  obtain ⟨n, hn, h⟩ := h
  obtain ⟨n', hn', h'⟩ := h'
  have e : n' = n := funext fun i => by exact_mod_cast (hn' i).trans (hn i).symm
  subst e
  exact h.div h' k

end HChar

end General

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

theorem isClsF_one : IsClsF H (1 : HChar H.E) :=
  ⟨fun _ => by show ‖((1 : ℂˣ) : ℂ)‖ = 1; simp, fun _ _ _ => rfl, fun _ => rfl,
    fun v k => by rw [HChar.resFin_apply]; exact Finset.prod_eq_one fun _ _ => rfl,
    fun w k => by rw [HChar.resInf_apply]; exact Finset.prod_eq_one fun _ _ => rfl⟩

theorem IsEtaT.mul_cls {χ ξ : HChar H.E} (h : IsEtaT H χ) (hξ : IsClsF H ξ) : IsEtaT H (χ * ξ) :=
  ⟨h.unitary.mul hξ.unitary, fun v => (h.unr v).mul (hξ.unr v), h.res.mul hξ.triv, h.inf.mul_triv hξ.inf⟩

theorem IsEtaT.div_cls {χ χ' : HChar H.E} (h : IsEtaT H χ) (h' : IsEtaT H χ') : IsClsF H (χ' * χ⁻¹) :=
  ⟨h'.unitary.mul h.unitary.inv, fun v => (h'.unr v).mul (h.unr v).inv, h.inf.div h'.inf, h.res.div h'.res⟩

theorem IsChiPsi.mul_cls {χ ξ : HChar H.E} (h : IsChiPsi H χ) (hξ : IsClsF H ξ) : IsChiPsi H (χ * ξ) :=
  ⟨h.unitary.mul hξ.unitary, fun v => (h.unr v).mul (hξ.unr v), h.triv.mul hξ.triv, h.inf.mul_triv hξ.inf⟩

theorem IsChiPsi.div_cls {χ χ' : HChar H.E} (h : IsChiPsi H χ) (h' : IsChiPsi H χ') : IsClsF H (χ' * χ⁻¹) :=
  ⟨h'.unitary.mul h.unitary.inv, fun v => (h'.unr v).mul (h.unr v).inv, h.inf.div h'.inf, h'.triv.mul h.triv.inv⟩

theorem IsEtaT.sq_chiPsi {χ : HChar H.E} (h : IsEtaT H χ) : IsChiPsi H (χ * χ) where
  unitary := h.unitary.mul h.unitary
  unr v := (h.unr v).mul (h.unr v)
  triv := by
    refine ⟨fun v k => ?_, fun w k => ?_⟩
    · rw [HChar.resFin_mul, h.res.1]
      unfold etaFin
      split_ifs
      · rw [← mul_zpow]; simp
      · simp
    · rw [HChar.resInf_mul, h.res.2]
      unfold etaInf
      split_ifs <;> simp
  inf k := by
    rw [HChar.inf_mul, Units.val_mul, h.inf k, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [← zpow_add' (by right; left; norm_num)]
    norm_num

theorem PiBar.overP (P : PiBar H) {k : Fin 2} {w : HeightOneSpectrum (𝓞 H.E)} (hw : P.Div k w) : OverP H (H.g k) w := by
  have h := P.pb_over k
  rw [← hw] at h
  have h2 : algebraMap (𝓞 H.K) (𝓞 H.E) ((H.g k : ℕ) : 𝓞 H.K) ∈ w.asIdeal := h
  rwa [map_natCast] at h2

theorem isUnitAt_nat {p a : ℕ} {w : HeightOneSpectrum (𝓞 H.E)} (hw : OverP H p w) (ha : a.Coprime p) {x : H.Eˣ}
    (hx : (x : H.E) = (a : H.E)) : IsUnitAt w (atFin w x) := by
  have hna : ((a : ℕ) : 𝓞 H.E) ∉ w.asIdeal := by
    intro hmem
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr ha)
    have h1 : (1 : 𝓞 H.E) ∈ w.asIdeal := by
      have e : (1 : 𝓞 H.E) = (u : 𝓞 H.E) * ((a : ℕ) : 𝓞 H.E) + (v : 𝓞 H.E) * ((p : ℕ) : 𝓞 H.E) := by
        have := congrArg (fun z : ℤ => (z : 𝓞 H.E)) huv
        push_cast at this
        exact this.symm
      rw [e]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hmem) (w.asIdeal.mul_mem_left _ hw)
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have h := valued_algebraMap_eq_one H.E w _ hna
  show Valued.v (algebraMap H.E (w.adicCompletion H.E) (x : H.E)) = 1
  rw [hx]
  simpa using h

theorem IsMu0.mul_cls {P : PiBar H} {W : Omg H} {e : R.Psi → ℚ} {j : ℕ} {χ ξ : HChar H.E}
    (h : IsMu0 P W e j χ) (hξ : IsClsF H ξ) : IsMu0 P W e j (χ * ξ) where
  unitary := h.unitary.mul hξ.unitary
  triv := h.triv.mul hξ.triv
  inf := h.inf.mul_triv hξ.inf
  unr v hv := (h.unr v hv).mul (hξ.unr v)
  tame v := (h.tame v).mul ((hξ.unr v).levelLe 1)
  atg k w hw a ha x hx := by
    have h1 : ξ.locK w x = 1 := hξ.unr w _ (isUnitAt_nat (P.overP hw) ha hx)
    show χ.locK w x * ξ.locK w x = _
    rw [h1, mul_one, h.atg k w hw a ha x hx]

theorem IsMu0.div_cls {P : PiBar H} {W : Omg H} {e : R.Psi → ℚ} {j : ℕ} {χ χ' : HChar H.E}
    (h : IsMu0 P W e j χ) (h' : IsMu0 P W e j χ')
    (hg : ∀ k v, OverP H (H.g k) v → (χ' * χ⁻¹).UnrAt v) : IsClsF H (χ' * χ⁻¹) where
  unitary := h'.unitary.mul h.unitary.inv
  unr v := by
    by_cases hv : ∀ k, ¬ OverP H (H.g k) v
    · exact (h'.unr v hv).mul (h.unr v hv).inv
    · push Not at hv
      obtain ⟨k, hk⟩ := hv
      exact hg k v hk
  inf := h.inf.div h'.inf
  triv := h'.triv.mul h.triv.inv

def Mu0Unique (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ) : Prop :=
  (∀ k, {v : HeightOneSpectrum (𝓞 H.E) | OverP H (H.g k) v}.ncard = Module.finrank ℚ H.E) →
    ∀ χ χ' : HChar H.E, IsMu0 P W e j χ → IsMu0 P W e j χ' → IsClsF H (χ' * χ⁻¹)

theorem isPsi_one (l : ℕ) : IsPsi (H := H) l ∅ (1 : HChar H.E) where
  ord := ⟨0, one_pow _⟩
  triv := isClsF_one.triv
  tame := fun _ _ _ _ => rfl
  ram := fun v => ⟨fun _ => Finset.notMem_empty v, fun _ _ _ => rfl⟩
  atl := fun _ _ _ => rfl
  split := fun _ hv => absurd hv (Finset.notMem_empty _)

theorem HChar.isUnitary_of_order {L : Type} [Field L] [NumberField L] {χ : HChar L} {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) :
    χ.IsUnitary := fun x => by
  have h1 : (χ.1 x) ^ n = 1 := by
    have := congrArg (fun ξ : HChar L => ξ.1 x) h
    exact this
  have h2 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1]; simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h2

theorem IsDelta.unitary {p : ℕ} {χ : HChar H.E} (h : IsDelta (H := H) p χ) : χ.IsUnitary := by
  obtain ⟨n, hn, ho⟩ := h.fin
  exact HChar.isUnitary_of_order hn ho

end Formalism.L2.Host

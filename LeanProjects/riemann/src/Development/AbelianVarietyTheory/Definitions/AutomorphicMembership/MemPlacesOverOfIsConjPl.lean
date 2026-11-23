import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LabConj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LpUnrNegOneSpec

noncomputable section

namespace GlobalTheory.HeightCounting.LabConjModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne Pointwise

section General

variable {Ω : Type} [Field Ω]

theorem val_lt_iff {A B : ValuationSubring Ω} (c : Ω ≃+* Ω) (hc : ∀ x, x ∈ A ↔ c x ∈ B) (y : Ω) :
    B.valuation (c y) < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← hc, ← map_inv₀, ← hc, map_eq_zero_iff _ c.injective]

variable {E : Type} [Field E] [NumberField E] [Algebra E Ω]

theorem mem_Ine_of_transport {A B : ValuationSubring Ω} (c : Ω ≃+* Ω) (hc : ∀ x, x ∈ A ↔ c x ∈ B) {t γ : G E Ω}
    (hγ : ∀ x, γ (c x) = c (t x)) (ht : t ∈ Ine (F := E) A) : γ ∈ Ine (F := E) B := by
  have key : ∀ y, γ y ∈ B ↔ y ∈ B := fun y => by
    obtain ⟨x, rfl⟩ := c.surjective y
    rw [hγ, ← hc, ← hc, apply_mem_iff_of_mem_Dec ht.1]
  refine ⟨?_, fun y hy => ?_⟩
  · show γ • B = B
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← key, mul_inv_apply]
  · obtain ⟨x, rfl⟩ := c.surjective y
    rw [hγ, ← map_sub, val_lt_iff c hc]
    exact ht.2 x ((A.valuation_le_one_iff x).2 ((hc x).2 ((B.valuation_le_one_iff _).1 hy)))

theorem exists_transport_elt (s : E ≃+* E) (c : Ω ≃+* Ω) (hs : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (s x))
    (t : G E Ω) : ∃ γ : G E Ω, ∀ x, γ (c x) = c (t x) := by
  refine ⟨{ (c.symm.trans (t.toRingEquiv.trans c)) with commutes' := fun y => ?_ }, fun x => ?_⟩
  · obtain ⟨x, rfl⟩ := s.surjective y
    show c (t (c.symm _)) = _
    rw [← hs, c.symm_apply_apply, t.commutes]
  · show c (t (c.symm (c x))) = _
    rw [c.symm_apply_apply]

end General

section Host

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def conjInt (H : Host R) : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

theorem coe_conjInt (x : 𝓞 H.E) : ((conjInt H x : 𝓞 H.E) : H.E) = H.conj (x : H.E) := rfl

theorem isConjPl_iff {w w' : PlE H} : IsConjPl H w w' ↔ ∀ x, x ∈ w.asIdeal ↔ conjInt H x ∈ w'.asIdeal := by
  refine ⟨fun h x => h x _ (coe_conjInt x), fun h x y hy => ?_⟩
  have : y = conjInt H x := RingOfIntegers.ext (hy.trans (coe_conjInt x).symm)
  rw [this]; exact h x

theorem exists_isConjPl (w : PlE H) : ∃ w', IsConjPl H w w' :=
  ⟨w.comap (conjInt H).symm.toRingHom (conjInt H).symm.surjective, isConjPl_iff.2 fun x => by
    simp [HeightOneSpectrum.comap]⟩

theorem eq_of_isConjPl {w₀ w₁ w : PlE H} (h₀ : IsConjPl H w₀ w) (h₁ : IsConjPl H w₁ w) : w₀ = w₁ := by
  apply HeightOneSpectrum.ext
  ext x
  rw [isConjPl_iff.1 h₀, isConjPl_iff.1 h₁]

theorem mem_placesOver_of_isConjPl {w₀ w : PlE H} (h : IsConjPl H w₀ w) {p : ℕ} (hp : w₀ ∈ placesOver H.E p) :
    w ∈ placesOver H.E p := by
  have := (isConjPl_iff.1 h _).1 hp
  rwa [map_natCast] at this

theorem exists_ext (N : NData R H what₂) {w₀ w : PlE H} (h : IsConjPl H w₀ w) : ∃ c : N.Om ≃+* N.Om,
    (∀ x : H.E, c (algebraMap H.E N.Om x) = algebraMap H.E N.Om (H.conj x)) ∧
    ∀ x, x ∈ N.plOm.1 w₀ ↔ c x ∈ N.plOm.1 w := by
  let c₀ : N.Om ≃+* N.Om := IsAlgClosure.equivOfEquiv N.Om N.Om H.conj.toRingEquiv
  have h₀ : ∀ x : H.E, c₀ (algebraMap H.E N.Om x) = algebraMap H.E N.Om (H.conj x) := fun x =>
    IsAlgClosure.equivOfEquiv_algebraMap N.Om N.Om H.conj.toRingEquiv x
  let B : ValuationSubring N.Om := (N.plOm.1 w₀).comap c₀.symm.toRingHom
  have hB : ∀ x, x ∈ N.plOm.1 w₀ ↔ c₀ x ∈ B := fun x => by
    simp [B, ValuationSubring.mem_comap]
  have hBw : IsPlaceOver (F := H.E) B w := fun y => by
    obtain ⟨x, rfl⟩ := (conjInt H).surjective y
    rw [coe_conjInt, ← h₀, val_lt_iff c₀ hB, ← isConjPl_iff.1 h]
    exact N.plOm.2 w₀ x
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hBw (N.plOm.2 w)
  refine ⟨c₀.trans σ.toRingEquiv, fun x => ?_, fun x => ?_⟩
  · show σ (c₀ _) = _
    rw [h₀, σ.commutes]
  · show _ ↔ σ (c₀ x) ∈ _
    rw [hB, ← hσ, ← AlgEquiv.smul_def]
    exact ValuationSubring.smul_mem_pointwise_smul_iff.symm

end Host

theorem exists_place (D : D7) (k : Fin 2) :
    ∃ v w, IsConjPl D.host (D.naut.plGw k v) w ∧ ∀ v', w ≠ D.naut.plGw k v' := by
  have hpos : 0 < Fintype.card (D.nd.PlG k) := by
    rw [D.nd.card_PlG]; unfold Ranks.f Ranks.n; positivity
  obtain ⟨v⟩ := Fintype.card_pos_iff.1 hpos
  obtain ⟨w, hw⟩ := exists_isConjPl (D.naut.plGw k v)
  exact ⟨v, w, hw, fun v' e => D.naut.plGw_nconj k v v' (e ▸ hw)⟩

theorem natDegree_labLP {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (hL : LabConj D T) (k v) (w : PlE D.host)
    (hw : IsConjPl D.host (D.naut.plGw k v) w) (a : D.naut.LP w) :
    (D.naut.items₂ k w a).natDegree = (T.e w a).lpTame.lpDim := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨c, γ, -, h2, h3, h4⟩ := hL k v w hw
  rw [h4 a]
  exact WD.natDegree_lab ⟨GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
    (mem_placesOver_of_isConjPl hw (D.naut.plGw_over k v)),
    mem_Ine_of_transport c h2 h3 (D.ntypes.tg_mem k v), D.ntypes.teichC_inj k⟩ _

theorem roots_labLP {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (hL : LabConj D T) (k v) (w : PlE D.host)
    (hw : IsConjPl D.host (D.naut.plGw k v) w) : ∃ (c : D.nd.Om ≃+* D.nd.Om) (γ : G D.host.E D.nd.Om),
      γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) ∧ (∀ x, γ (c x) = c (D.ntypes.tg k v x)) ∧ ∀ a : D.naut.LP w,
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      (Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w a)).map (D.ntypes.teichC k) = (T.e w a).tameEig γ := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨c, γ, -, h2, h3, h4⟩ := hL k v w hw
  have hγ := mem_Ine_of_transport c h2 h3 (D.ntypes.tg_mem k v)
  refine ⟨c, γ, hγ, h3, fun a => ?_⟩
  rw [h4 a]
  exact WD.map_rootsBar_lab ⟨GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
    (mem_placesOver_of_isConjPl hw (D.naut.plGw_over k v)), hγ, D.ntypes.teichC_inj k⟩ _

theorem exists_gamma (D : D7) (k : Fin 2) : ∃ γ : PlE D.host → G D.host.E D.nd.Om,
    (∀ v, γ (D.naut.plGw k v) = D.ntypes.tg k v) ∧
    ∀ v w, IsConjPl D.host (D.naut.plGw k v) w → ∃ c : D.nd.Om ≃+* D.nd.Om,
      (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
      (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ ∀ x, γ w (c x) = c (D.ntypes.tg k v x) := by
  have key : ∀ w : PlE D.host, ∃ γ : G D.host.E D.nd.Om, (∀ v, w = D.naut.plGw k v → γ = D.ntypes.tg k v) ∧
      ∀ v, IsConjPl D.host (D.naut.plGw k v) w → ∃ c : D.nd.Om ≃+* D.nd.Om,
      (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
      (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ ∀ x, γ (c x) = c (D.ntypes.tg k v x) := by
    intro w
    by_cases h : ∃ v, IsConjPl D.host (D.naut.plGw k v) w
    · obtain ⟨v, hv⟩ := h
      obtain ⟨c, h1, h2⟩ := exists_ext D.nd hv
      obtain ⟨γ, hγ⟩ := exists_transport_elt D.host.conj.toRingEquiv c h1 (D.ntypes.tg k v)
      refine ⟨γ, fun v' e => absurd (e ▸ hv) (D.naut.plGw_nconj k v v'), fun v' hv' => ?_⟩
      obtain rfl : v = v' := D.naut.plGw_inj k (eq_of_isConjPl hv hv')
      exact ⟨c, h1, h2, hγ⟩
    · refine ⟨Function.extend (D.naut.plGw k) (D.ntypes.tg k) (fun _ => 1) w, fun v e => ?_, fun v hv => absurd ⟨v, hv⟩ h⟩
      rw [e]; exact (D.naut.plGw_inj k).extend_apply _ _ v
  choose γ h1 h2 using key
  exact ⟨γ, fun v => h1 _ v rfl, fun v w hw => h2 w v hw⟩

set_option maxHeartbeats 1000000 in

theorem exists_labTrue_labConj : ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (Rw : RowWD D), ∃ lab h A C tm tg hl,
    (∀ k v, A.plGw k v = D.naut.plGw k v) ∧
    ∃ T : GlobalTheory.RowTie.WDTie (setAut D hE lab h A C tm tg hl).nd (setAut D hE lab h A C tm tg hl).naut,
      LabTrue (setAut D hE lab h A C tm tg hl) T ∧ LabConj (setAut D hE lab h A C tm tg hl) T ∧
      ∃ Rs : RowSide (setAut D hE lab h A C tm tg hl),
        (∀ σ w, T.e w (Rs.locR σ w) = Rw.par σ w) ∧ ∀ σ w, Rs.satR σ w = Rw.sat σ w := by
  intro D hE Rw
  have hS : ∀ k v, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) :=
    fun k v => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
      (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
  let lab : ∀ k, D.what₂.FT → D.nd.PlG k → Polynomial (ZMod (D.host.g k)) := fun k σ v =>
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (Rw.par σ (D.naut.plGw k v))
  have h : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = D.R.r := fun k σ v =>
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ⟨WD.lab_monic _ _ _, ((WD.natDegree_lab_eq_iff (hS k v) _).2 (Rw.tame σ k v)).trans (Rw.dim σ _)⟩
  choose γ hγ1 hγ2 using exists_gamma D
  let A : NAut (ndLab D.nd lab h) := nAutWD (ndLab D.nd lab h) hE D.naut.plGw D.naut.plGw_over D.naut.plGw_inj
    D.naut.plGw_nconj D.ntypes.teichC γ
  have hA : ∀ k v (a : A.LP (A.plGw k v)), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.items₂ k (A.plGw k v) a = WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) a := fun k v a => by
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exact congrArg (fun x => WD.lab (h := D.nd.plOm.2 (D.naut.plGw k v)) (D.ntypes.teichC k) x a) (hγ1 k v)
  have hl : ∀ k v (L : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) L).natDegree = A.lpDim L →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.inePol L (D.ntypes.tg k v) =
        ((Formalism.CyclotomicNorms.rootsBar (A.items₂ k (A.plGw k v) L)).map fun x => X - Polynomial.C (D.ntypes.teichC k x)).prod := by
    intro k v L hL
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    rw [hA k v L] at hL ⊢
    exact WD.inePol_eq_of_natDegree_lab _ _ _ hL
  obtain ⟨C⟩ := GlobalTheory.MemN.nonempty_nbc_of_isEmpty_loc _ _ _ _ A hE
  refine ⟨lab, h, A, C, D.ntypes.tg_mem, D.ntypes.tg_gen, hl, fun _ _ => rfl,
    wdTieWD (ndLab D.nd lab h) hE D.naut.plGw D.naut.plGw_over D.naut.plGw_inj D.naut.plGw_nconj D.ntypes.teichC γ,
    fun k v a => hA k v a, fun k v w hw => ?_, ⟨Rw.par, Rw.sat, fun k σ v => (hA k v _).symm⟩, fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨c, h1, h2, h3⟩ := hγ2 k v w hw
  exact ⟨c, γ k w, h1, h2, h3, fun _ => rfl⟩

end GlobalTheory.HeightCounting.LabConjModel

end

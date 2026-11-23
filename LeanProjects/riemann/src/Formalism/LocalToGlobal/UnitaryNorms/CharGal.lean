import Formalism.LocalRingCardinality.DataNChTie
import Formalism.LocalToGlobal.UnitaryNorms.CharTied

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.ConjugateSelfDual ReciprocityTheory.Gal

def toC (D : D7) (i : D.nd.Loc) : D.nd.O i →+* ℂ :=
  ((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).comp (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))

def IsGalOf (D : D7) (i : D.nd.Loc) (U : Set (PlE D.host)) (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.nd.O i)ˣ) (χ : HChar D.host.E)
    (s : ℝ) : Prop :=
  ∀ w ∈ U, w ∉ placesOver D.host.E (D.nd.l i) → χ.UnrAt w →
    ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) σ →
      toC D i ((r σ : (D.nd.O i)ˣ) : D.nd.O i) = ((χ.val w)⁻¹ : ℂˣ).1 * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)

theorem NCharTied.chi_one {D : D7} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch} (T : NCharTied D C nch Tp)
    (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) :
    IsGalOf D i {w | SplitOut D.nd i w} (D.nd.chi i 1) (Tp.tup (D.nd.mu i) j * C.eta⁻¹)
      (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) := by
  intro w hw _ hU B σ hB hσ
  have hπ : (T.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 = Tp.tup (D.nd.mu i) j * C.eta⁻¹ := by
    rw [T.tw, T.muC i j hj, T.etaTinv]
  have hU' : (T.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1.UnrAt w := by
    rw [hπ]
    exact hU
  have hunr : D.naut.unr (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) := (T.unr_iff _ w).2 hU'

  have hc := (D.naut.chi_mu i w hw).2 B σ hB hσ
  rw [D.naut.frobEig_tw _ _ hunr, T.frob _ w hU', Multiset.map_singleton, hπ] at hc
  exact (Multiset.singleton_inj.1 hc).symm

theorem delta_side (D : D7) (a : D.nd.Loc) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (x x' : D.LL0)
    (hx' : (x' : D.what₂.LL) = star (x : D.what₂.LL))
    (h : algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a)))
      ((D.ntw.delta (D.ntw.twOf a) σ : (D.ntw.O0 (D.ntw.twOf a))ˣ) : D.ntw.O0 (D.ntw.twOf a)) = D.ntw.emb0 (D.ntw.twOf a) x) :
    toC D a (D.ntw.twist₂ a ((D.ntw.delta (D.ntw.twOf a) σ : (D.ntw.O0 (D.ntw.twOf a))ˣ) : D.ntw.O0 (D.ntw.twOf a))) =
      if D.ntw.twSide a then D.what₂.embLL (x : D.what₂.LL) else D.what₂.embLL (x' : D.what₂.LL) := by
  by_cases hs : D.ntw.twSide a = true
  · rw [if_pos hs]
    have he := D.ntw.twO_emb a x _ (by rw [if_pos hs]; exact h)
    exact (congrArg (fun t => D.naut.iotaQC a (D.naut.iotaQ a t)) he.symm).trans (D.naut.iota_LL a x)
  · rw [if_neg hs]

    have he := D.ntw.twO_emb a x' _ (by
      rw [if_neg hs, h]
      exact (D.ntw.restX_coefficientEmbedding_conj _ x' x (by rw [hx', star_star])).symm)
    exact (congrArg (fun t => D.naut.iotaQC a (D.naut.iotaQ a t)) he.symm).trans (D.naut.iota_LL a x')

def DeltaRead (D : D7) (C : CharFrame D) : Prop :=
  ∀ (s : D.ntw.Tw) (w : PlE D.host), w ∉ placesOver D.host.E (D.ntw.l s) → (C.delAt (D.ntw.l s)).UnrAt w →
    ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) σ →
      ∃ x : D.LL0, D.what₂.embLL (x : D.what₂.LL) = (((C.delAt (D.ntw.l s)).val w)⁻¹ : ℂˣ).1 ∧
        algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s)) ((D.ntw.delta s σ : (D.ntw.O0 s)ˣ) : D.ntw.O0 s) = D.ntw.emb0 s x

theorem CharFrame.delAt_unitary {D : D7} (C : CharFrame D) (l : ℕ) : (C.delAt l).IsUnitary := by

  have key : ∀ χ : HChar D.host.E, (∃ n : ℕ, 0 < n ∧ χ.OrderDvd n) → χ.IsUnitary := by
    rintro χ ⟨n, hn, hχ⟩ x
    have hχ' : χ ^ n = 1 := hχ
    have h1 : (χ.1 x) ^ n = 1 := by
      have := congrArg (fun ψ : HChar D.host.E => ψ.1 x) hχ'
      exact this
    have h2 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2
  unfold CharFrame.delAt
  split
  · exact key _ C.isDel'.fin
  · exact key _ C.isDel.fin

theorem isGalOf_delta_of_deltaRead (D : D7) (C : CharFrame D) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (hrd : DeltaRead D C) (a : D.nd.Loc) :
    IsGalOf D a Set.univ ((Units.map (D.ntw.twist₂ a).toMonoidHom).comp (D.ntw.delta (D.ntw.twOf a)))
      (if D.ntw.twSide a then C.delAt (D.nd.l a) else (C.delAt (D.nd.l a))⁻¹) 0 := by
  intro w _ hw hU B σ hB hσ
  have hl : D.ntw.l (D.ntw.twOf a) = D.nd.l a := D.ntw.twOf_l a

  have conj_inv : ∀ u : ℂˣ, ‖(u : ℂ)‖ = 1 → starRingEnd ℂ ((u⁻¹ : ℂˣ) : ℂ) = (u : ℂ) := by
    intro u hu
    have hn : Complex.normSq (u : ℂ) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hu, one_pow]
    rw [Units.val_inv_eq_inv_val, map_inv₀, Complex.inv_def, Complex.normSq_conj, hn]
    simp
  have hinv : ((C.delAt (D.nd.l a))⁻¹).val w = ((C.delAt (D.nd.l a)).val w)⁻¹ := rfl
  have hU' : (C.delAt (D.nd.l a)).UnrAt w := by
    by_cases hs : D.ntw.twSide a = true
    · rw [if_pos hs] at hU
      exact hU
    · rw [if_neg hs] at hU
      intro y hy
      have h1 : (((C.delAt (D.nd.l a)).loc w) y)⁻¹ = 1 := hU y hy
      exact inv_eq_one.1 h1
  obtain ⟨x, hxv, hxd⟩ := hrd (D.ntw.twOf a) w (by rw [hl]; exact hw) (by rw [hl]; exact hU') B σ hB hσ
  rw [hl] at hxv
  have hd := delta_side D a σ x ⟨star (x : D.what₂.LL), hstar x⟩ rfl hxd
  show toC D a (D.ntw.twist₂ a ((D.ntw.delta (D.ntw.twOf a) σ : (D.ntw.O0 (D.ntw.twOf a))ˣ) :
    D.ntw.O0 (D.ntw.twOf a))) = _
  rw [hd, Complex.ofReal_zero, Complex.cpow_zero, mul_one]
  by_cases hs : D.ntw.twSide a = true
  · rw [if_pos hs, if_pos hs]
    exact hxv
  · rw [if_neg hs, if_neg hs]
    show D.what₂.embLL (star (x : D.what₂.LL)) = _
    rw [D.starLL_cx, hxv, hinv, inv_inv]
    apply conj_inv
    exact C.delAt_unitary _ _

structure NGalChrTied (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch) where

  psi_is : ∀ a, IsPsi (D.nd.l a) (D.nd.Q a) (Tp.psi (D.nd.w a))

  psiL : ∀ a, IsGalOf D a Set.univ (D.ntw.psiL a) (Tp.psi (D.nd.w a)) 0

  deltaRead : DeltaRead D C

theorem NGalChrTied.delta {D : D7} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch} (T : NGalChrTied D C nch Tp)
    (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (a : D.nd.Loc) :
    IsGalOf D a Set.univ ((Units.map (D.ntw.twist₂ a).toMonoidHom).comp (D.ntw.delta (D.ntw.twOf a)))
      (if D.ntw.twSide a then C.delAt (D.nd.l a) else (C.delAt (D.nd.l a))⁻¹) 0 :=
  isGalOf_delta_of_deltaRead D C hstar T.deltaRead a

def PsiChoiceCompatible (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ v : PlE D.host, v ∉ nch.Q w → v ∉ placesOver D.host.E (D.what₂.places.resChar w) →
    ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B v →
      IsFrob (F := D.host.E) B (normV v) σ → ∀ y : D.what₂.LL, D.what₂.embLL y = (((Tp.psi w).val v)⁻¹ : ℂˣ).1 →
      nch.embW w y = algebraMap (nch.Oe w) (FractionRing (nch.Oe w)) (algebraMap (D.ntw.Ok (nch.twI w) (nch.k' w)) (nch.Oe w)
        ((nch.psi' w (D.ntw.art (nch.twI w) (nch.Q w) σ) : (D.ntw.Ok (nch.twI w) (nch.k' w))ˣ) : D.ntw.Ok (nch.twI w) (nch.k' w)))

theorem NGalChrTied.psiChoice {D : D7} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch} (T : NGalChrTied D C nch Tp)
    (h : NChTie D nch) (a : D.nd.Loc) (v : PlE D.host) (hQ : v ∉ nch.Q (D.nd.w a))
    (hl : v ∉ placesOver D.host.E (D.what₂.places.resChar (D.nd.w a)))
    (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (hB : IsPlaceOver (F := D.host.E) B v)
    (hσ : IsFrob (F := D.host.E) B (normV v) σ) (y : D.what₂.LL)
    (hy : D.what₂.embLL y = (((Tp.psi (D.nd.w a)).val v)⁻¹ : ℂˣ).1) :
    nch.embW (D.nd.w a) y = algebraMap (nch.Oe (D.nd.w a)) (FractionRing (nch.Oe (D.nd.w a)))
      (algebraMap (D.ntw.Ok (nch.twI (D.nd.w a)) (nch.k' (D.nd.w a))) (nch.Oe (D.nd.w a))
      ((nch.psi' (D.nd.w a) (D.ntw.art (nch.twI (D.nd.w a)) (nch.Q (D.nd.w a)) σ) :
        (D.ntw.Ok (nch.twI (D.nd.w a)) (nch.k' (D.nd.w a)))ˣ) : D.ntw.Ok (nch.twI (D.nd.w a)) (nch.k' (D.nd.w a)))) := by
  obtain ⟨ψ0, -, hW, hK⟩ := h.psi_eq
  have hU : (Tp.psi (D.nd.w a)).UnrAt v := by
    rw [(T.psi_is a).ram, h.Q_eq a]
    exact hQ
  have hl' : v ∉ placesOver D.host.E (D.nd.l a) := by
    rw [← D.nd.w_l a]
    exact hl
  have hg := T.psiL a v (Set.mem_univ v) hl' hU B σ hB hσ

  have hg' : D.what₂.embLL ((ψ0 (D.nd.w a) σ : (D.what₂.LL)ˣ) : D.what₂.LL) =
      (((Tp.psi (D.nd.w a)).val v)⁻¹ : ℂˣ).1 := by
    rw [← D.naut.iota_LL a, hK a σ]
    simpa [toC] using hg
  have hyy : y = ((ψ0 (D.nd.w a) σ : (D.what₂.LL)ˣ) : D.what₂.LL) :=
    D.what₂.embLL.injective (hy.trans hg'.symm)
  rw [hyy]
  exact hW (D.nd.w a) σ

structure CharacterChoiceData' (D : D7) (nch : NChoice D) where
  C : CharFrame D
  val : ValLL0 D C
  tp : TupTied D C nch
  dt : DtTied D C
  n : NCharTied D C nch tp
  gal : NGalChrTied D C nch tp
  psi' : PsiChoiceCompatible D C nch tp

theorem HChar.ValuesIn.qb {D : D7} (T : HostTied D) {χ : HChar D.host.E} {s : ℝ} (h : χ.ValuesIn s D.what₂.embLL)
    (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : χ.UnrAt v) : ∃ y : D.what₂.LL, T.fr.ι (T.jLL y) = χ.valTw s v := by
  obtain ⟨y, hy⟩ := h v hv
  exact ⟨y, by rw [T.embLL, hy]⟩

end Formalism.L2.Host

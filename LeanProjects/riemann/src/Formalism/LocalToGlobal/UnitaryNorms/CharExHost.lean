import Formalism.LocalToGlobal.UnitaryNorms.CharExGen
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

namespace CharEx

section Sub

variable {L : Type} [Field L] [NumberField L] (F : Type) [Field F] [NumberField F] [Algebra F L]

def aF (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : Ideles L :=
  ∏ P ∈ aboveF (L := L) F v, localIdele L P (atFin P (upF F k))

def aFi (w : InfinitePlace F) (k : Fˣ) : Ideles L :=
  ∏ w' ∈ aboveInf (L := L) F w, infIdele L w' (atInf w' (upF F k))

def idF : Subgroup (Ideles L) :=
  Subgroup.closure (Set.range (fun p : HeightOneSpectrum (𝓞 F) × Fˣ => (aF F p.1 p.2 : Ideles L)) ∪
    Set.range (fun p : InfinitePlace F × Fˣ => (aFi F p.1 p.2 : Ideles L)))

def unitF : Subgroup (Ideles L) := unitIdeles L ⊔ idF (L := L) F

theorem aF_mem (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : (aF F v k : Ideles L) ∈ unitF (L := L) F :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_union_left _ ⟨(v, k), rfl⟩))

theorem aFi_mem (w : InfinitePlace F) (k : Fˣ) : (aFi F w k : Ideles L) ∈ unitF (L := L) F :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_union_right _ ⟨(w, k), rfl⟩))

theorem resFin_eq (χ : HChar L) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ.resFin v k = χ.1 (aF F v k) := by
  unfold HChar.resFin aF
  rw [map_prod, MonoidHom.finset_prod_apply]
  exact Finset.prod_congr rfl fun P _ => rfl

theorem resInf_eq (χ : HChar L) (w : InfinitePlace F) (k : Fˣ) : χ.resInf w k = χ.1 (aFi F w k) := by
  unfold HChar.resInf aFi
  rw [map_prod, MonoidHom.finset_prod_apply]
  exact Finset.prod_congr rfl fun w' _ => rfl

end Sub

section Loc

variable {L : Type} [Field L] [NumberField L]

theorem localIdele_mem {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) :
    localIdele L v x ∈ unitIdeles L := by
  show ∀ v' : HeightOneSpectrum (𝓞 L), Valued.v (((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v') = 1
  intro v'
  by_cases h : v' = v
  · subst h
    rw [localIdele_snd_self]
    exact hx
  · rw [(localIdele_isSupportedAt L v x).2 v' h]
    exact map_one _

theorem infDiag_mem (k : Lˣ) : infDiag k ∈ unitIdeles L := by
  unfold infDiag
  rw [MonoidHom.finset_prod_apply]
  refine Subgroup.prod_mem _ fun w _ => ?_
  show ∀ v : HeightOneSpectrum (𝓞 L),
    Valued.v (((infIdele L w (atInf w k) : Ideles L) : AdeleRing (𝓞 L) L).2 v) = 1
  intro v
  have h1 : ((infIdele L w (atInf w k) : Ideles L) : AdeleRing (𝓞 L) L).2 = 1 := rfl
  rw [h1]
  show Valued.v (1 : v.adicCompletion L) = 1
  exact map_one _

end Loc

variable {R : Formalism.BasicNotions.Ranks} {H : Formalism.BasicNotions.Host R}

structure EtaTQ (Φ : Ideles H.E →* ℂˣ) : Prop where
  cont : Continuous Φ
  unitU : ∀ u ∈ unitIdeles H.E, ‖((Φ u : ℂˣ) : ℂ)‖ = 1
  unr : ∀ v x, IsUnitAt v x → Φ (localIdele H.E v x) = 1
  resFin : ∀ v k, Φ (aF H.F v k) = etaFin (L := H.E) H.F v k
  resInf : ∀ w k, Φ (aFi H.F w k) = etaInf H.F w k
  inf : ∀ k : H.Eˣ, ((Φ (infDiag k) : ℂˣ) : ℂ) =
    ∏ τ ∈ @Finset.univ R.Psi (Fintype.ofFinite _), (embPsi H τ (k : H.E) / ((‖embPsi H τ (k : H.E)‖ : ℝ) : ℂ)) ^ (1 : ℤ)
  glob : ∀ k : H.Eˣ, diagUnits H.E k ∈ unitF (L := H.E) H.F → Φ (diagUnits H.E k) = 1

structure Mu0Q (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ) (Φ : Ideles H.E →* ℂˣ) : Prop where
  cont : Continuous Φ
  unitU : ∀ u ∈ unitIdeles H.E, ‖((Φ u : ℂˣ) : ℂ)‖ = 1
  trivFin : ∀ v k, Φ (aF H.F v k) = 1
  trivInf : ∀ w k, Φ (aFi H.F w k) = 1
  inf : ∃ n : R.Psi → ℤ, (∀ τ, (n τ : ℚ) = 2 * (-e τ)) ∧ ∀ k : H.Eˣ, ((Φ (infDiag k) : ℂˣ) : ℂ) =
    ∏ τ ∈ @Finset.univ R.Psi (Fintype.ofFinite _), (embPsi H τ (k : H.E) / ((‖embPsi H τ (k : H.E)‖ : ℝ) : ℂ)) ^ n τ
  unr : ∀ v, (∀ k, ¬ OverP H (H.g k) v) → ∀ x, IsUnitAt v x → Φ (localIdele H.E v x) = 1
  tame : ∀ v x, IsUnitAt v x → Valued.v ((x : v.adicCompletion H.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) →
    Φ (localIdele H.E v x) = 1
  atg : ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (a : ℕ) (ha : a.Coprime (H.g k)) (x : H.Eˣ),
    (x : H.E) = (a : H.E) → Φ (localIdele H.E w (atFin w x)) = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹
  glob : ∀ k : H.Eˣ, diagUnits H.E k ∈ unitF (L := H.E) H.F → Φ (diagUnits H.E k) = 1

structure DeltaQ (p : ℕ) (Φ : Ideles H.E →* ℂˣ) : Prop where
  cont : Continuous Φ
  finU : ∃ n : ℕ, 0 < n ∧ ∀ u ∈ unitIdeles H.E, Φ u ^ n = 1
  trivFin : ∀ v k, Φ (aF H.F v k) = 1
  trivInf : ∀ w k, Φ (aFi H.F w k) = 1
  tame : ∀ v x, IsUnitAt v x → Valued.v ((x : v.adicCompletion H.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) →
    Φ (localIdele H.E v x) = 1
  unr : ∀ v, ¬ OverP H p v → ∀ x, IsUnitAt v x → Φ (localIdele H.E v x) = 1
  ine : ∀ v, OverP H p v → ∀ n : ℕ, (∀ x, IsUnitAt v x → Φ (localIdele H.E v x) ^ n = 1) ↔ 15 ∣ n
  glob : ∀ k : H.Eˣ, diagUnits H.E k ∈ unitF (L := H.E) H.F → Φ (diagUnits H.E k) = 1

private theorem unitary_lemma {L : Type} [Field L] [NumberField L] (χ : HChar L)
    (h : ∀ u ∈ unitIdeles L, ‖((χ.1 u : ℂˣ) : ℂ)‖ = 1) : χ.IsUnitary := by
  obtain ⟨n, hn, hx⟩ := classExp L
  intro x
  obtain ⟨k, hk⟩ := hx x
  have hc : Continuous χ.1 ∧ ∀ k : Lˣ, χ.1 (diagUnits L k) = 1 := χ.2
  have h1 := h _ hk
  rw [map_mul, hc.2 k, mul_one, map_pow, Units.val_pow_eq_pow_val, norm_pow] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1

theorem etaTExists_of (hD : DivExtC) (hO : OpenUnits H.E) {Φ : Ideles H.E →* ℂˣ} (hq : EtaTQ (H := H) Φ) :
    EtaTExists H := by
  obtain ⟨χ, hχ⟩ := exists_hchar_eq_on hD hO (unitF (L := H.E) H.F)
    (le_sup_left : unitIdeles H.E ≤ unitIdeles H.E ⊔ idF (L := H.E) H.F) Φ hq.cont hq.glob
  have hU : ∀ u ∈ unitIdeles H.E, χ.1 u = Φ u := fun u hu => hχ u (Subgroup.mem_sup_left hu)
  refine ⟨χ, ⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩⟩
  · exact unitary_lemma χ fun u hu => by rw [hU u hu]; exact hq.unitU u hu
  · intro v x hx
    show χ.1 (localIdele H.E v x) = 1
    rw [hU _ (localIdele_mem hx)]
    exact hq.unr v x hx
  · intro v k
    rw [resFin_eq H.F χ v k, hχ _ (aF_mem H.F v k)]
    exact hq.resFin v k
  · intro w k
    rw [resInf_eq H.F χ w k, hχ _ (aFi_mem H.F w k)]
    exact hq.resInf w k
  · intro k
    show ((χ.1 (infDiag k) : ℂˣ) : ℂ) = _
    rw [hU _ (infDiag_mem k)]
    convert hq.inf k using 2

theorem mu0Exists_of (hD : DivExtC) (hO : OpenUnits H.E) {P : PiBar H} {W : Omg H} {e : R.Psi → ℚ} {j : ℕ}
    {Φ : Ideles H.E →* ℂˣ} (hq : Mu0Q P W e j Φ) : Mu0Exists P W e j := by
  obtain ⟨χ, hχ⟩ := exists_hchar_eq_on hD hO (unitF (L := H.E) H.F)
    (le_sup_left : unitIdeles H.E ≤ unitIdeles H.E ⊔ idF (L := H.E) H.F) Φ hq.cont hq.glob
  have hU : ∀ u ∈ unitIdeles H.E, χ.1 u = Φ u := fun u hu => hχ u (Subgroup.mem_sup_left hu)
  refine ⟨χ, ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
  · exact unitary_lemma χ fun u hu => by rw [hU u hu]; exact hq.unitU u hu
  · intro v k
    rw [resFin_eq H.F χ v k, hχ _ (aF_mem H.F v k)]
    exact hq.trivFin v k
  · intro w k
    rw [resInf_eq H.F χ w k, hχ _ (aFi_mem H.F w k)]
    exact hq.trivInf w k
  · obtain ⟨n, hn, hk⟩ := hq.inf
    refine ⟨n, hn, fun k => ?_⟩
    show ((χ.1 (infDiag k) : ℂˣ) : ℂ) = _
    rw [hU _ (infDiag_mem k)]
    convert hk k using 2
  · intro v hv x hx
    show χ.1 (localIdele H.E v x) = 1
    rw [hU _ (localIdele_mem hx)]
    exact hq.unr v hv x hx
  · intro v x hx hle
    show χ.1 (localIdele H.E v x) = 1
    rw [hU _ (localIdele_mem hx)]
    exact hq.tame v x hx hle
  · intro k w hw a ha x hxa
    show χ.1 (localIdele H.E w (atFin w x)) = _
    rw [hU _ (localIdele_mem (isUnitAt_nat (P.overP hw) ha hxa))]
    exact hq.atg k w hw a ha x hxa

theorem deltaExists_of (hD : DivExtC) (hO : OpenUnits H.E) {p : ℕ} {Φ : Ideles H.E →* ℂˣ} (hq : DeltaQ (H := H) p Φ) :
    DeltaExists (H := H) p := by
  obtain ⟨χ, hχ⟩ := exists_hchar_eq_on hD hO (unitF (L := H.E) H.F)
    (le_sup_left : unitIdeles H.E ≤ unitIdeles H.E ⊔ idF (L := H.E) H.F) Φ hq.cont hq.glob
  have hU : ∀ u ∈ unitIdeles H.E, χ.1 u = Φ u := fun u hu => hχ u (Subgroup.mem_sup_left hu)
  refine ⟨χ, ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩⟩
  · obtain ⟨n, hn, hu⟩ := hq.finU
    obtain ⟨h, hh, hx⟩ := classExp H.E
    refine ⟨h * n, Nat.mul_pos hh hn, ?_⟩
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    obtain ⟨k, hk⟩ := hx x
    have hc : Continuous χ.1 ∧ ∀ k : H.Eˣ, χ.1 (diagUnits H.E k) = 1 := χ.2
    have e1 : χ.1 (x ^ h * diagUnits H.E k) = Φ (x ^ h * diagUnits H.E k) := hU _ hk
    rw [map_mul, hc.2 k, mul_one, map_pow] at e1
    have e2 : (χ.1 x) ^ (h * n) = 1 := by rw [pow_mul, e1, hu _ hk]
    simpa using e2
  · intro v k
    rw [resFin_eq H.F χ v k, hχ _ (aF_mem H.F v k)]
    exact hq.trivFin v k
  · intro w k
    rw [resInf_eq H.F χ w k, hχ _ (aFi_mem H.F w k)]
    exact hq.trivInf w k
  · intro v x hx hle
    show χ.1 (localIdele H.E v x) = 1
    rw [hU _ (localIdele_mem hx)]
    exact hq.tame v x hx hle
  · intro v hv x hx
    show χ.1 (localIdele H.E v x) = 1
    rw [hU _ (localIdele_mem hx)]
    exact hq.unr v hv x hx
  · intro v hv n
    have hloc : ∀ x, IsUnitAt v x → χ.loc v x = Φ (localIdele H.E v x) :=
      fun x hx => hU _ (localIdele_mem hx)
    constructor
    · intro h
      apply (hq.ine v hv n).1
      intro x hx
      rw [← hloc x hx]
      exact h x hx
    · intro h x hx
      rw [hloc x hx]
      exact (hq.ine v hv n).2 h x hx

end CharEx

end Formalism.L2.Host

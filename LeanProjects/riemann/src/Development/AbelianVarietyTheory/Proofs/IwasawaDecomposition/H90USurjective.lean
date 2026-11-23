import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemKDSupUnitIdlIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TildeCharacterOnUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeLatticeDeterminantClassLawsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H90RangeEqNormOneOfIsQuad

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2

section Factor

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E)))

theorem KDq_le_ker {χ : HChar H.E} (hF : χ.TrivOn H.F) (ht : ∀ v, χ.TameAt v)
    (hu : ∀ v, (∀ k, ¬ OverP H (H.g k) v) → ¬ AtQ H SQ v → χ.UnrAt v) :
    KDq H SQ ≤ (χ.1.comp (finPartI H.E)).ker := by
  refine (KDq_le_iff H SQ).2 ⟨fun a ha => ?_, fun v k => ?_⟩
  · refine GlobalTheory.Mem.LocTriv.eq_one_of_local H.E χ.1 χ.2.1 (finPartI H.E a) ha.1 (fun _ => rfl) fun v x hx => ?_
    have hx' : (x : v.adicCompletion H.E) = (a : AdeleRing (𝓞 H.E) H.E).2 v := hx
    have hunit : IsUnitAt v x := by
      unfold IsUnitAt
      rw [hx']
      exact ha.1 v
    by_cases h : (∃ k, OverP H (H.g k) v) ∨ AtQ H SQ v
    · have hlt : Valued.v ((x : v.adicCompletion H.E) - 1) < 1 := by
        rw [hx']
        rcases h with ⟨k, hk⟩ | h
        exacts [ha.2.1 k v hk, ha.2.2 v h]
      refine ht v x hunit ?_
      by_cases h0 : Valued.v ((x : v.adicCompletion H.E) - 1) = 0
      · rw [h0]; exact zero_le
      · rw [← WithZero.exp_log h0] at hlt ⊢
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
        rw [WithZero.exp_le_exp]
        omega
    · rw [not_or, not_exists] at h
      exact hu v h.1 h.2 x hunit
  · have e : finPartI H.E (locF H.F v k) = locF H.F v k := by
      unfold locF
      rw [map_prod]
      exact Finset.prod_congr rfl fun Q _ => finPartI_eq_self fun _ => rfl
    show χ.1 (finPartI H.E (locF H.F v k)) = 1
    rw [e, ← hF.1 v k]
    unfold locF HChar.resFin
    rw [map_prod, MonoidHom.finset_prod_apply]
    rfl

theorem tildeQ_mk_of_tame {χ : HChar H.E} (hF : χ.TrivOn H.F) (ht : ∀ v, χ.TameAt v)
    (hu : ∀ v, (∀ k, ¬ OverP H (H.g k) v) → ¬ AtQ H SQ v → χ.UnrAt v) (a : Ideles H.E) :
    tildeQ H SQ χ (QuotientGroup.mk a) = χ.1 (finPartI H.E a) :=
  tildeQ_mk H SQ (KDq_le_ker H SQ hF ht hu) a

theorem KD_le_ker {χ : HChar H.E} (hF : χ.TrivOn H.F) (ht : ∀ v, χ.TameAt v)
    (hu : ∀ v, (∀ k, ¬ OverP H (H.g k) v) → χ.UnrAt v) : KD H ≤ (χ.1.comp (finPartI H.E)).ker :=
  KDq_empty H ▸ KDq_le_ker H ∅ hF ht fun v h _ => hu v h

variable {H} in

theorem KD_le_ker_of_isChiPsi {χ : HChar H.E} (h : IsChiPsi H χ) : KD H ≤ (χ.1.comp (finPartI H.E)).ker :=
  KD_le_ker H h.triv (fun v x hx _ => h.unr v x hx) fun v _ => h.unr v

variable {H} in

theorem KD_le_ker_of_isMu0 {P : PiBar H} {W : Omg H} {e : R.Psi → ℚ} {j : ℕ} {χ : HChar H.E} (h : IsMu0 P W e j χ) :
    KD H ≤ (χ.1.comp (finPartI H.E)).ker :=
  KD_le_ker H h.triv h.tame h.unr

theorem norm_muTilQ {mu : Fin R.m → HChar H.E} (hu : ∀ j, (mu j).IsUnitary) (j : ℕ) (x : DtQ H SQ) :
    ‖((muTilQ H SQ mu j x : ℂˣ) : ℂ)‖ = 1 := by
  unfold muTilQ
  split_ifs
  · exact norm_tildeQ H SQ (hu _) x
  · simp

end Factor

section Pack

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) {e : Fin R.m → R.Psi → ℚ}

def trueDtPackQ (C : HFrame H e) : DtPack H :=
  letI := H.cmStar
  { Dt := DtQ H SQ
    instDt := inferInstance
    muTil := muTilQ H SQ C.mu0
    chiD := tildeQ H SQ C.chiPsi
    UO := UOQ H SQ
    chiD_UO := fun x hx => by
      rw [tildeQ_eq_comp H SQ (KD_le_ker_of_isChiPsi C.isChi)]
      rw [← comap_UOT] at hx
      exact (GlobalTheory.Mem.ChiLaws.chi_laws R H C.chiPsi C.isChi).1 _ hx
    e1Dt := e1Q H SQ
    rest_detCharacter_on_unitary_eq := fun z => by
      rw [tildeQ_eq_comp H SQ (KD_le_ker_of_isChiPsi C.isChi), MonoidHom.comp_apply, toDtT_e1Q]
      exact (GlobalTheory.Mem.ChiLaws.chi_laws R H C.chiPsi C.isChi).2 z
    relDet := fun N L L' => relDetQ H SQ N L.1 L'.1
    relDet_self := fun N L => relDetQ_self H SQ N L.1
    relDet_mul := fun N L L' L'' => (toDtTMod_bijective H SQ).1 (by
      rw [map_mul, toDtTMod_relDetQ, toDtTMod_relDetQ, toDtTMod_relDetQ]
      exact (GlobalTheory.T.relativeLatticeDeterminantClass_laws R H N).2.1 L L' L'')
    relDet_smul := fun N L L' γ h => (toDtTMod_bijective H SQ).1 (by
      rw [toDtTMod_relDetQ, toDtTMod_mk, toDtT_e1Q]
      exact (GlobalTheory.T.relativeLatticeDeterminantClass_laws R H N).2.2 L L' γ h) }

theorem trueDtPackQ_relDet (C : HFrame H e) : letI := H.cmStar
    ∀ (N : ℕ) (L L' : SDLat H.E N), (trueDtPackQ SQ C).relDet N L L' = relDetQ H SQ N L.1 L'.1 :=
  fun _ _ _ => rfl

theorem norm_muTilQ_frame (C : HFrame H e) (j : ℕ) (x : DtQ H SQ) : ‖((muTilQ H SQ C.mu0 j x : ℂˣ) : ℂ)‖ = 1 :=
  norm_muTilQ H SQ (fun j => (C.isMu0 j).unitary) j x

theorem norm_tildeQ_chiPsi (C : HFrame H e) (x : DtQ H SQ) : ‖((tildeQ H SQ C.chiPsi x : ℂˣ) : ℂ)‖ = 1 :=
  norm_tildeQ H SQ C.isChi.unitary x

end Pack

def dtIsoRational (D : D7) (C : CharFrame D) (SQ : Finset (HeightOneSpectrum (𝓞 D.host.E))) (ε : DtQ D.host SQ ≃* D.Dt)
    (hmu : ∀ j, (D.muTil j).comp ε.toMonoidHom = muTilQ D.host SQ C.mu0 j)
    (hchi : D.chiD.comp ε.toMonoidHom = tildeQ D.host SQ C.chiPsi)
    (hUO : D.UO = (UOQ D.host SQ).map ε.toMonoidHom) (he : ∀ z, D.e1Dt z = ε (e1Q D.host SQ z)) : DtTied D C :=
  have hk : ∀ a, (ε.toMonoidHom.comp (QuotientGroup.mk' (KDq D.host SQ))) a = 1 ↔ a ∈ KDq D.host SQ := fun a => by
    show ε (QuotientGroup.mk a) = 1 ↔ _
    rw [EmbeddingLike.map_eq_one_iff, QuotientGroup.eq_one_iff]
  { eDt := ε.toMonoidHom.comp (QuotientGroup.mk' (KDq D.host SQ))
    surj := ε.surjective.comp (QuotientGroup.mk'_surjective _)
    ker_open := by
      have : (ε.toMonoidHom.comp (QuotientGroup.mk' (KDq D.host SQ))).ker = KDq D.host SQ := Subgroup.ext hk
      rw [this]
      exact isOpen_KDq D.host SQ
    inf := fun w y => (hk _).2 (infIdele_mem_KDq D.host SQ w y)
    onF := fun v k => (hk _).2 (locF_mem_KDq D.host SQ v k)
    ker_le := fun a ha => (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff _ D.host a).1 (Subgroup.mem_sup_left (KDq_le_KD D.host SQ ((hk a).1 ha)))
    rat := fun k z hz => by
      rw [he, ← isUnitaryPointsMap_unitaryRationalPointsFiner D.host SQ k z hz]
      rfl
    UO_eq := fun x => by
      rw [hUO]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    muTil_eq := fun j a ha => by
      have h := DFunLike.congr_fun (hmu (j.1 + 1)) (QuotientGroup.mk a)
      rw [muTilQ_succ, tildeQ_mk _ _ ((KDq_le_KD _ _).trans (KD_le_ker_of_isMu0 (C.isMu0 j))), finPartI_eq_self ha] at h
      exact h
    chiD_eq := fun a ha => by
      have h := DFunLike.congr_fun hchi (QuotientGroup.mk a)
      rw [tildeQ_mk _ _ ((KDq_le_KD _ _).trans (KD_le_ker_of_isChiPsi C.isChi)), finPartI_eq_self ha] at h
      exact h }

section Fixed

open Formalism.L2.DIV Formalism.UG Formalism.UG.P GlobalTheory.AdeleBaseChange

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_one_tmul {ι : AfE F E →+* FiniteAdeleRing (𝓞 E) E} (h1 : ∀ x : E, ι (x ⊗ₜ[F] 1) = algebraMap E _ x)
    (h2 : ∀ z ∈ RInt F E, ι z ∈ intAd E) (b : FiniteAdeleRing (𝓞 F) F) : ι (1 ⊗ₜ[F] b) = adMap F E b := by
  rw [← sub_eq_zero]
  refine (GlobalTheory.AdLat.integral_finiteAdele_complete_separated E).1 _ fun N hN => ?_
  obtain ⟨k, a, ha, rfl⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).1 b
  have hi : (1 : E) ⊗ₜ[F] a ∈ RInt F E := by simpa using levelaf_tmul_mem (F := F) (1 : 𝓞 E) ha
  refine ⟨ι (1 ⊗ₜ[F] a) - adMap F E a, sub_mem (h2 _ hi) (adMap_int ha), ?_⟩
  have e : (1 : E) ⊗ₜ[F] (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) = algebraMap F E k ⊗ₜ[F] 1 := by
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  rw [TensorProduct.tmul_add, map_add, map_add, e, h1, adMap_algebraMap, TensorProduct.tmul_smul, map_nsmul, map_nsmul,
    smul_sub]
  abel

theorem exists_eq_one_tmul {σ : E →ₐ[F] E} (hσ : ∀ x, ∃ t : F, algebraMap F E t = x + σ x) {z : AfE F E}
    (hz : sigR σ (FiniteAdeleRing (𝓞 F) F) z = z) : ∃ b, z = 1 ⊗ₜ[F] b := by
  have h : ∀ y : AfE F E, ∃ b, y + sigR σ (FiniteAdeleRing (𝓞 F) F) y = 1 ⊗ₜ[F] b := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add y y' hy hy' =>
      obtain ⟨b, hb⟩ := hy
      obtain ⟨b', hb'⟩ := hy'
      exact ⟨b + b', by rw [map_add, TensorProduct.tmul_add, ← hb, ← hb']; abel⟩
    | tmul x a =>
      obtain ⟨t, ht⟩ := hσ x
      refine ⟨t • a, ?_⟩
      have e : sigR σ (FiniteAdeleRing (𝓞 F) F) (x ⊗ₜ[F] a) = σ x ⊗ₜ[F] a := by simp [sigR]
      rw [e, ← TensorProduct.add_tmul, ← ht, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  obtain ⟨b, hb⟩ := h z
  refine ⟨(2 : F)⁻¹ • b, ?_⟩
  rw [TensorProduct.tmul_smul, ← hb, hz, ← two_smul F z, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem exists_mul_congr_one (v : HeightOneSpectrum (𝓞 F)) {b : v.adicCompletion F} (hb : b ≠ 0) :
    ∃ k : Fˣ, Valued.v (algebraMap F (v.adicCompletion F) k * b - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  have hc : Continuous fun y : v.adicCompletion F => y * b - 1 := (continuous_mul_const b).sub continuous_const
  have ho : IsOpen {y : v.adicCompletion F | Valued.v (y * b - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ))} :=
    (GlobalTheory.Idele.isOpen_valued_le (K := F) v (-((1 : ℕ) : ℤ))).preimage hc
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := F) v).exists_mem_open ho
    ⟨b⁻¹, by simp [inv_mul_cancel₀ hb]⟩
  have h0 : k ≠ 0 := by
    rintro rfl
    simp only [map_zero, Set.mem_setOf_eq, zero_mul, zero_sub, Valuation.map_neg, map_one] at hk
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at hk
    omega
  exact ⟨Units.mk0 k h0, hk⟩

theorem exists_locF_mul {a : Ideles E} {b : FiniteAdeleRing (𝓞 F) F} (hab : (a : AdeleRing (𝓞 E) E).2 = adMap F E b)
    {T : Set (HeightOneSpectrum (𝓞 E))} (hT : T.Finite) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (k : HeightOneSpectrum (𝓞 F) → Fˣ),
      (∏ v ∈ S, locF F v (k v)) * a ∈ unitIdl E ∧
        ∀ w ∈ T, Valued.v (compAt w ((∏ v ∈ S, locF F v (k v)) * a) - 1) < 1 := by
  classical
  have hk : ∀ v : HeightOneSpectrum (𝓞 F), ∃ k : Fˣ, b v ≠ 0 →
      Valued.v (algebraMap F (v.adicCompletion F) k * b v - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := fun v => by
    by_cases h : b v = 0
    · exact ⟨1, fun h' => absurd h h'⟩
    · obtain ⟨k, hk⟩ := exists_mul_congr_one v h
      exact ⟨k, fun _ => hk⟩
  choose k hk using hk
  have hfin := hT.union (IdlFact.finite_valAt_ne_one a)
  set S := hfin.toFinset.image fun w => w.under (𝓞 F) with hS
  set P := ∏ v ∈ S, locF (L := E) F v (k v) with hP
  have hc : ∀ w, compAt w P =
      if w.under (𝓞 F) ∈ S then compAt w (diagUnits E (upF F (k (w.under (𝓞 F))))) else 1 := fun w => by
    rw [hP, map_prod, Finset.prod_congr rfl fun v _ => compAt_locF F w v (k v), Finset.prod_ite_eq]
  have ha : ∀ w, compAt w a = locMap F w (b (w.under (𝓞 F))) := fun w => by
    rw [← adMap_apply, ← hab]
    rfl
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have h1 : ∀ w, w.under (𝓞 F) ∈ S → Valued.v (compAt w (P * a) - 1) < 1 := fun w hw => by
    have hb : b (w.under (𝓞 F)) ≠ 0 := fun h0 => by
      have hu : IsUnit (compAt w a) := (Group.isUnit a).map (compAt w)
      rw [ha, h0, map_zero] at hu
      exact not_isUnit_zero hu
    have e : compAt w (diagUnits E (upF F (k (w.under (𝓞 F))))) =
        locMap F w (algebraMap F _ (k (w.under (𝓞 F)) : F)) := by
      rw [locMap_algebraMap]
      rfl
    rw [map_mul, hc, if_pos hw, e, ha, ← map_mul, ← map_one (locMap F w), ← map_sub]
    exact (locMap_valued w 1 _ (hk _ hb)).trans_lt hlt
  have hmem : ∀ w, w ∈ T ∪ {v | IdlFact.valAt v a ≠ 1} → w.under (𝓞 F) ∈ S := fun w hw =>
    Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hw)
  refine ⟨S, k, fun w => ?_, fun w hw => h1 w (hmem w (Or.inl hw))⟩
  show Valued.v (compAt w (P * a)) = 1
  by_cases hw : w.under (𝓞 F) ∈ S
  · have h := Valuation.map_eq_of_sub_lt (Valued.v) (x := (1 : w.adicCompletion E)) (y := compAt w (P * a))
      (by rw [map_one]; exact h1 w hw)
    rw [h, map_one]
  · rw [map_mul, hc, if_neg hw, one_mul]
    by_contra hne
    exact hw (hmem w (Or.inr hne))

def finIdele (ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E) : (AfE F E)ˣ →* Ideles E :=
  Units.map ((MonoidHom.inr (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)).comp ι.toRingHom.toMonoidHom)

end Fixed

section NormOne

open Formalism.L2.DIV Formalism.UG

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E)))

theorem mk_eq_of_snd_eq {a a' : Ideles H.E} (h : (a : AdeleRing (𝓞 H.E) H.E).2 = (a' : AdeleRing (𝓞 H.E) H.E).2) :
    (QuotientGroup.mk a : DtQ H SQ) = QuotientGroup.mk a' := by
  have e : ∀ w, compAt w (a⁻¹ * a') = 1 := fun w => by
    have e' : compAt w a' = compAt w a := congrArg (fun z : FiniteAdeleRing (𝓞 H.E) H.E => z w) h.symm
    rw [map_mul, e', ← map_mul, inv_mul_cancel, map_one]
  refine QuotientGroup.eq.2 (mem_KDq_of_congQ H SQ (mem_congQ_of_eq_one H SQ (fun w => ?_) fun w _ => e w))
  show Valued.v (compAt w (a⁻¹ * a')) = 1
  rw [e, map_one]

theorem mem_KDq_of_adMap {a : Ideles H.E} {b : FiniteAdeleRing (𝓞 H.F) H.F}
    (hab : (a : AdeleRing (𝓞 H.E) H.E).2 = GlobalTheory.AdeleBaseChange.adMap H.F H.E b) : a ∈ KDq H SQ := by
  obtain ⟨S, k, hu, h1⟩ := exists_locF_mul hab (finite_level H SQ)
  exact (Subgroup.mul_mem_cancel_left _ (prod_mem fun v _ => locF_mem_KDq H SQ v (k v))).1
    (mem_KDq_of_congQ H SQ ⟨hu, fun j v hv => h1 v (Or.inl ⟨j, hv⟩), fun v hv => h1 v (Or.inr hv)⟩)

variable (σ : H.E →ₐ[H.F] H.E) (hσ : ∀ x, σ x = H.conj x) (ι : AfE H.F H.E ≃+* FiniteAdeleRing (𝓞 H.E) H.E)
  (h1 : ∀ x : H.E, ι (x ⊗ₜ[H.F] 1) = algebraMap H.E _ x)
  (h2 : ∀ z, z ∈ RInt H.F H.E ↔ ∀ Q : HeightOneSpectrum (𝓞 H.E), Valued.v (ι z Q) ≤ 1)

include hσ h1 h2 in

theorem finIdele_mem_KDq {x : (AfE H.F H.E)ˣ} (hx : h90 σ x = 1) : finIdele ι x ∈ KDq H SQ := by
  have hcm : IsCMField H.E := H.isCMField_hostE
  have hc : ∀ x, IsCMField.complexConj H.E x = H.conj x := fun x => bridge_star_holds R H x
  have ht : ∀ y : H.E, ∃ t : H.F, algebraMap H.F H.E t = y + σ y := fun y =>
    ⟨⟨y + σ y, (IsCMField.complexConj_eq_self_iff H.E _).1 (by
      rw [hσ, ← hc, map_add, IsCMField.complexConj_apply_apply, add_comm])⟩, rfl⟩
  have hfix : conjId σ x = x := (div_eq_one.1 hx).symm
  obtain ⟨b, hb⟩ := exists_eq_one_tmul ht (z := (x : AfE H.F H.E)) (congrArg Units.val hfix)
  refine mem_KDq_of_adMap H SQ (b := b) ?_
  show ι (x : AfE H.F H.E) = _
  rw [hb]
  exact map_one_tmul (ι := ι.toRingHom) h1 (fun z hz => (h2 z).1 hz) b

def h90U : (AfE H.F H.E)ˣ →* U1 σ :=
  (h90 σ).codRestrict (U1 σ) fun x => (GlobalTheory.Mem.DetClass.exists_detClass R H σ hσ ι h1 h2).1 ▸ ⟨x, rfl⟩

theorem h90U_surjective : Function.Surjective (h90U H σ hσ ι h1 h2) := fun y => by
  obtain ⟨x, hx⟩ : (y : (AfE H.F H.E)ˣ) ∈ (h90 σ).range := (GlobalTheory.Mem.DetClass.exists_detClass R H σ hσ ι h1 h2).1.ge y.2
  exact ⟨x, Subtype.ext hx⟩

def normOneIdeleToFinerDeterminantClass : U1 σ →* DtQ H SQ :=
  (h90U H σ hσ ι h1 h2).liftOfSurjective (h90U_surjective H σ hσ ι h1 h2)
    ⟨(QuotientGroup.mk' (KDq H SQ)).comp (finIdele ι), fun _ hx =>
      (QuotientGroup.eq_one_iff _).2 (finIdele_mem_KDq H SQ σ hσ ι h1 h2 (congrArg Subtype.val hx))⟩

theorem normOneIdeleToFinerDeterminantClass_eq_mk (x : (AfE H.F H.E)ˣ) (h : h90 σ x ∈ U1 σ) (a : Ideles H.E)
    (ha : (a : AdeleRing (𝓞 H.E) H.E).2 = ι (x : AfE H.F H.E)) :
    normOneIdeleToFinerDeterminantClass H SQ σ hσ ι h1 h2 ⟨_, h⟩ = QuotientGroup.mk a :=
  (MonoidHom.liftOfRightInverse_comp_apply (h90U H σ hσ ι h1 h2) _ _ _ x).trans (mk_eq_of_snd_eq H SQ ha.symm)

theorem u1ToDtQ_surjective : Function.Surjective (normOneIdeleToFinerDeterminantClass H SQ σ hσ ι h1 h2) := fun y => by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
  let x : (AfE H.F H.E)ˣ := Units.map (ι.symm.toRingHom.toMonoidHom.comp
    (MonoidHom.snd (InfiniteAdeleRing H.E) (FiniteAdeleRing (𝓞 H.E) H.E))) a
  exact ⟨h90U H σ hσ ι h1 h2 x, normOneIdeleToFinerDeterminantClass_eq_mk H SQ σ hσ ι h1 h2 x _ a (ι.apply_symm_apply _).symm⟩

theorem eq_u1ToDtQ {f : U1 σ →* DtQ H SQ} (hf : ∀ (x : (AfE H.F H.E)ˣ) (h : h90 σ x ∈ U1 σ) (a : Ideles H.E),
    (a : AdeleRing (𝓞 H.E) H.E).2 = ι (x : AfE H.F H.E) → f ⟨_, h⟩ = QuotientGroup.mk a) :
    f = normOneIdeleToFinerDeterminantClass H SQ σ hσ ι h1 h2 := by
  refine MonoidHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := h90U_surjective H σ hσ ι h1 h2 y
  exact (hf x _ (finIdele ι x) rfl).trans (normOneIdeleToFinerDeterminantClass_eq_mk H SQ σ hσ ι h1 h2 x _ (finIdele ι x) rfl).symm

theorem tildeQ_u1ToDtQ {χ : HChar H.E} (hχ : KDq H SQ ≤ (χ.1.comp (finPartI H.E)).ker) (x : (AfE H.F H.E)ˣ)
    (h : h90 σ x ∈ U1 σ) : tildeQ H SQ χ (normOneIdeleToFinerDeterminantClass H SQ σ hσ ι h1 h2 ⟨_, h⟩) = χ.1 (finIdele ι x) := by
  rw [normOneIdeleToFinerDeterminantClass_eq_mk H SQ σ hσ ι h1 h2 x h (finIdele ι x) rfl, tildeQ_mk H SQ hχ, finPartI_eq_self fun _ => rfl]

end NormOne

theorem dtQ_main :
    (∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (e : Fin R.m → R.Psi → ℚ)
      (C : HFrame H e), ∃ X : DtPack H, X.Dt = DtQ H SQ ∧ HEq X.instDt (inferInstance : CommGroup (DtQ H SQ)) ∧
        HEq X.muTil (muTilQ H SQ C.mu0) ∧ HEq X.chiD (tildeQ H SQ C.chiPsi) ∧ HEq X.UO (UOQ H SQ) ∧
        HEq X.e1Dt (e1Q H SQ) ∧
        HEq X.relDet (letI := H.cmStar; fun N (L L' : SDLat H.E N) => relDetQ H SQ N L.1 L'.1)) ∧
    (∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (σ : H.E →ₐ[H.F] H.E),
      (∀ x, σ x = H.conj x) → ∀ ι : Formalism.L2.DIV.AfE H.F H.E ≃+* FiniteAdeleRing (𝓞 H.E) H.E,
      (∀ x : H.E, ι (x ⊗ₜ[H.F] 1) = algebraMap H.E _ x) →
      (∀ z, z ∈ Formalism.L2.DIV.RInt H.F H.E ↔ ∀ Q : HeightOneSpectrum (𝓞 H.E), Valued.v (ι z Q) ≤ 1) →
      ∃ f : Formalism.L2.DIV.U1 σ →* DtQ H SQ, Function.Surjective f ∧
        ∀ (x : (Formalism.L2.DIV.AfE H.F H.E)ˣ) (h : Formalism.L2.DIV.h90 σ x ∈ Formalism.L2.DIV.U1 σ) (a : Ideles H.E),
          (a : AdeleRing (𝓞 H.E) H.E).2 = ι (x : Formalism.L2.DIV.AfE H.F H.E) → f ⟨_, h⟩ = QuotientGroup.mk a) ∧
    (∀ (D : D7) (C : CharFrame D) (SQ : Finset (HeightOneSpectrum (𝓞 D.host.E))) (ε : DtQ D.host SQ ≃* D.Dt),
      (∀ j, (D.muTil j).comp ε.toMonoidHom = muTilQ D.host SQ C.mu0 j) →
      D.chiD.comp ε.toMonoidHom = tildeQ D.host SQ C.chiPsi → D.UO = (UOQ D.host SQ).map ε.toMonoidHom →
      (∀ z, D.e1Dt z = ε (e1Q D.host SQ z)) →
      ∃ T : DtTied D C, ∀ a, T.eDt a = ε (QuotientGroup.mk a)) ∧
    (∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (χ : HChar H.E),
      χ.TrivOn H.F → (∀ v, χ.TameAt v) → (∀ v, (∀ k, ¬ OverP H (H.g k) v) → ¬ AtQ H SQ v → χ.UnrAt v) →
      KDq H SQ ≤ (χ.1.comp (finPartI H.E)).ker ∧
        ∀ a, tildeQ H SQ χ (QuotientGroup.mk a) = χ.1 (finPartI H.E a)) ∧
    (∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (e : Fin R.m → R.Psi → ℚ)
      (C : HFrame H e) (x : DtQ H SQ),
      (∀ j, ‖((muTilQ H SQ C.mu0 j x : ℂˣ) : ℂ)‖ = 1) ∧ ‖((tildeQ H SQ C.chiPsi x : ℂˣ) : ℂ)‖ = 1) :=
  ⟨fun _ _ SQ _ C => ⟨trueDtPackQ SQ C, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩,
    fun _ H SQ σ hσ ι h1 h2 => ⟨normOneIdeleToFinerDeterminantClass H SQ σ hσ ι h1 h2, u1ToDtQ_surjective H SQ σ hσ ι h1 h2,
      normOneIdeleToFinerDeterminantClass_eq_mk H SQ σ hσ ι h1 h2⟩,
    fun D C SQ ε hmu hchi hUO he => ⟨dtIsoRational D C SQ ε hmu hchi hUO he, fun _ => rfl⟩,
    fun _ H SQ _ hF ht hu => ⟨KDq_le_ker H SQ hF ht hu, tildeQ_mk_of_tame H SQ hF ht hu⟩,
    fun _ _ SQ _ C x => ⟨fun j => norm_muTilQ_frame SQ C j x, norm_tildeQ_chiPsi SQ C x⟩⟩

end GlobalTheory.Mem.Col2

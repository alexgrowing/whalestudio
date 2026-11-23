import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowEqOneOfUnitary

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.Mem.Chr.DetGroupModel

section General

variable {L : Type} [Field L] [NumberField L]

theorem loc_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
  classical
  show Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) v (x : v.adicCompletion L) v = _
  simp

theorem loc_ne {v w : HeightOneSpectrum (𝓞 L)} (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
  classical
  show Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) v (x : v.adicCompletion L) w = _
  exact Function.update_of_ne h _ _

def valAt (w : HeightOneSpectrum (𝓞 L)) : Ideles L →* WithZero (Multiplicative ℤ) where
  toFun a := Valued.v ((a : AdeleRing (𝓞 L) L).2 w)
  map_one' := by
    show Valued.v (1 : w.adicCompletion L) = 1
    exact map_one _
  map_mul' a b := by
    show Valued.v ((a : AdeleRing (𝓞 L) L).2 w * (b : AdeleRing (𝓞 L) L).2 w) = _
    exact map_mul _ _ _

theorem valAt_loc_self (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    valAt v (localIdele L v (atFin v k)) = v.valuation L (k : L) := by
  show Valued.v (((localIdele L v _ : Ideles L) : AdeleRing (𝓞 L) L).2 v) = _
  rw [loc_self]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _

theorem valAt_loc_ne {v w : HeightOneSpectrum (𝓞 L)} (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    valAt w (localIdele L v x) = 1 := by
  show Valued.v (((localIdele L v _ : Ideles L) : AdeleRing (𝓞 L) L).2 w) = _
  rw [loc_ne h, map_one]

theorem valuation_unif (v : HeightOneSpectrum (𝓞 L)) : v.valuation L (unif v : L) = WithZero.exp (-1 : ℤ) := by
  have h : Valued.v (((unif v : Lˣ) : L) : v.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec v
  rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h

theorem unif_not_mem_unitIdl (v : HeightOneSpectrum (𝓞 L)) : localIdele L v (atFin v (unif v)) ∉ unitIdl L := by
  intro h
  have h1 : valAt v (localIdele L v (atFin v (unif v))) = 1 := h v
  rw [valAt_loc_self, valuation_unif, ← WithZero.exp_zero, WithZero.exp_inj] at h1
  omega

theorem eq_refl_of_isConjI_id {c : L ≃+* L} (h : IsConjI c (MonoidHom.id (Ideles L))) : c = RingEquiv.refl L := by
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · have h1 := congrArg Units.val (h.diag (Units.mk0 x hx))
    exact ((AdeleRing.algebraMap_injective (𝓞 L) L) h1).symm

theorem diag_eq (k : Lˣ) : diagUnits L k = infDiag k * finPartI L (diagUnits L k) := by
  classical
  apply Units.ext
  have h1 : ∀ s : Finset (InfinitePlace L), ((∏ w ∈ s, infIdele L w (atInf w k) : Ideles L) : AdeleRing (𝓞 L) L).2 = 1 ∧
      ∀ w', ((∏ w ∈ s, infIdele L w (atInf w k) : Ideles L) : AdeleRing (𝓞 L) L).1 w' =
        if w' ∈ s then algebraMap L w'.Completion (k : L) else 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨rfl, fun _ => rfl⟩
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      refine ⟨?_, fun w' => ?_⟩
      · show (1 : FiniteAdeleRing (𝓞 L) L) * _ = 1
        rw [one_mul]; exact ih.1
      · show (Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) a (algebraMap L a.Completion (k : L)) w') * _ = _
        rw [ih.2 w']
        by_cases h : w' = a
        · subst h; simp [ha]
        · simp [h]
  have h2 : infDiag k = ∏ w, infIdele L w (atInf w k) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply]; rfl
  rw [h2]
  refine Prod.ext (funext fun w => ?_) ?_
  · show _ = ((∏ w, infIdele L w (atInf w k) : Ideles L) : AdeleRing (𝓞 L) L).1 w * 1
    rw [(h1 _).2 w, if_pos (Finset.mem_univ _), mul_one]; rfl
  · show _ = ((∏ w, infIdele L w (atInf w k) : Ideles L) : AdeleRing (𝓞 L) L).2 * _
    rw [(h1 _).1, one_mul]; rfl

theorem fin_diag (χ : HChar L) (k : Lˣ) : χ.1 (finPartI L (diagUnits L k)) = (χ.inf k)⁻¹ := by
  have h := χ.2.2 k
  rw [diag_eq, map_mul] at h
  exact eq_inv_of_mul_eq_one_right h

theorem detSub_rank_one (u : L) :
    detSub (Submodule.span (𝓞 L) {(fun _ => u : Fin 1 → L)}) = Submodule.span (𝓞 L) {u} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hx 0)
    refine Submodule.mem_span_singleton.2 ⟨a, ?_⟩
    rw [Matrix.det_fin_one]
    exact congrFun ha 0
  · refine Submodule.span_le.2 ?_
    rintro z rfl
    have := det_mem_detSub (M := Submodule.span (𝓞 L) {(fun _ => z : Fin 1 → L)}) (fun _ _ => z)
      (fun _ => Submodule.mem_span_singleton_self _)
    rwa [Matrix.det_fin_one] at this

theorem detSub_rank_zero (M : Submodule (𝓞 L) (Fin 0 → L)) : detSub M = Submodule.span (𝓞 L) {1} := by
  unfold detSub
  congr 1
  ext z
  constructor
  · rintro ⟨x, -, rfl⟩; simp
  · rintro rfl; exact ⟨fun i => i.elim0, fun i => i.elim0, by simp⟩

theorem not_splitsC_one : ¬ SplitsC L 1 := by
  unfold SplitsC
  have : {v : HeightOneSpectrum (𝓞 L) | ((1 : ℕ) : 𝓞 L) ∈ v.asIdeal} = ∅ := by
    ext v
    simpa using (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top
  rw [this, Set.ncard_empty]
  exact Module.finrank_pos.ne

end General

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem emb_conj (σ : H.E →+* ℂ) (z : H.E) : σ (H.conj z) = star (σ z) :=
  H.conjE_apply σ z

theorem conj_F (k : H.F) : H.conj (k : H.E) = k := (H.conjE_mem_hostF_iff _).1 k.2

def pack : DtPack H :=
  letI := H.cmStar
  { Dt := ℂˣ
    muTil := fun _ => MonoidHom.id _
    chiD := MonoidHom.id _
    UO := ⊥
    chiD_UO := fun _ hx => Subgroup.mem_bot.1 hx
    e1Dt := (GlobalTheory.MemberDetLaws.det_laws R H).choose
    rest_detCharacter_on_unitary_eq := fun z => by
      have h := (GlobalTheory.MemberDetLaws.det_laws R H).choose_spec.choose_spec.1 z
      rw [finprod_eq_prod_of_fintype] at h
      exact h
    relDet := (GlobalTheory.MemberDetLaws.det_laws R H).choose_spec.choose
    relDet_self := (GlobalTheory.MemberDetLaws.det_laws R H).choose_spec.choose_spec.2.1
    relDet_mul := (GlobalTheory.MemberDetLaws.det_laws R H).choose_spec.choose_spec.2.2.1
    relDet_smul := (GlobalTheory.MemberDetLaws.det_laws R H).choose_spec.choose_spec.2.2.2 }

theorem pack_chiD_injective : Function.Injective (pack H).chiD := fun _ _ h => h

theorem infIdele_mem_KD (w : InfinitePlace H.E) (y : (w.Completion)ˣ) : infIdele H.E w y ∈ KD H := by
  refine mem_KD_of_congG H ⟨fun v => ?_, fun k v _ => ?_⟩
  · show Valued.v (1 : v.adicCompletion H.E) = 1
    exact map_one _
  · show Valued.v ((1 : v.adicCompletion H.E) - 1) < 1
    simp

theorem determinantCharacter_unitary_apply {χ : HChar H.E} (hχ : IsChiPsi H χ) (h : KD H ≤ (χ.1.comp (finPartI H.E)).ker)
    (f : (letI := H.cmStar; unitary H.E) →* DtT H) (hf : IsRationalUnitaryDeterminantMap H f) (k : H.Eˣ) (z : (letI := H.cmStar; unitary H.E))
    (hz : (z.1 : H.E) * H.conj (k : H.E) = k) :
    ((tildeD H χ (f z) : ℂˣ) : ℂ) = ∏ τ : R.Psi, (H.emb (τ : R.GG) (z.1 : H.E))⁻¹ := by
  rw [← hf k z hz, tildeD_mk H h, fin_diag, Units.val_inv_eq_inv_val, hχ.inf k, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  congr 1
  have h1 := congrArg (embPsi H τ) hz
  rw [map_mul, emb_conj] at h1
  have h0 : embPsi H τ (k : H.E) ≠ 0 := by simp
  show _ = embPsi H τ z.1
  generalize embPsi H τ (k : H.E) = a at *
  generalize embPsi H τ z.1 = b at *
  have hn : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0
  have h2 : a * star a = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  rw [zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ hn), ← h2]
  linear_combination (-a) * h1

theorem valAt_locF (w : HeightOneSpectrum (𝓞 H.E)) (v : HeightOneSpectrum (𝓞 H.F)) (k : (H.F)ˣ) :
    open Classical in valAt w (locF H.F v k) = if w.under (𝓞 H.F) = v then w.valuation H.E ((k : H.F) : H.E) else 1 := by
  classical
  unfold locF
  rw [map_prod]
  have hm : ∀ Q, Q ∈ aboveF (L := H.E) H.F v ↔ Q.under (𝓞 H.F) = v := fun Q => by
    unfold aboveF; rw [Set.Finite.mem_toFinset]; rfl
  split_ifs with hw
  · rw [Finset.prod_eq_single w (fun Q _ hQ => valAt_loc_ne hQ.symm _) (fun h => absurd ((hm w).2 hw) h), valAt_loc_self]
    rfl
  · refine Finset.prod_eq_one fun Q hQ => valAt_loc_ne ?_ _
    rintro rfl
    exact hw ((hm _).1 hQ)

theorem under_eq {w w' : HeightOneSpectrum (𝓞 H.E)} (h : ConjPl H.conj.toRingEquiv w w') :
    w.under (𝓞 H.F) = w'.under (𝓞 H.F) := by
  ext x
  show algebraMap (𝓞 H.F) (𝓞 H.E) x ∈ w.asIdeal ↔ algebraMap (𝓞 H.F) (𝓞 H.E) x ∈ w'.asIdeal
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := H.E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := H.E), ← h]
  have : H.conj.toRingEquiv (algebraMap (𝓞 H.E) H.E (algebraMap (𝓞 H.F) (𝓞 H.E) x)) =
      algebraMap (𝓞 H.E) H.E (algebraMap (𝓞 H.F) (𝓞 H.E) x) := conj_F H (x : H.F)
  exact this ▸ Iff.rfl

theorem val_eq_of_mem_KD {w w' : HeightOneSpectrum (𝓞 H.E)} (h : ConjPl H.conj.toRingEquiv w w') {a : Ideles H.E}
    (ha : a ∈ KD H) : valAt w a = valAt w' a := by
  have : KD H ≤ MonoidHom.eqLocus (valAt w) (valAt w') := by
    refine (Subgroup.closure_le _).2 ?_
    rintro b (hb | ⟨v, k, rfl⟩)
    · exact (hb.1 w).trans (hb.1 w').symm
    · show valAt w _ = valAt w' _
      rw [valAt_locF, valAt_locF, under_eq H h]
      split_ifs
      · rw [← h, show H.conj.toRingEquiv ((k : H.F) : H.E) = ((k : H.F) : H.E) from conj_F H _]
      · rfl
  exact this ha

theorem val_eq_of_mem_UOT {w w' : HeightOneSpectrum (𝓞 H.E)} (h : ConjPl H.conj.toRingEquiv w w') {a : Ideles H.E}
    (ha : (QuotientGroup.mk a : DtT H) ∈ UOT H) : valAt w a = valAt w' a := by
  obtain ⟨u, hu, e⟩ := (mem_UOT H).1 ha
  have h1 := val_eq_of_mem_KD H h (QuotientGroup.eq.1 e)
  have hu' : u⁻¹ ∈ unitIdl H.E := (unitIdl H.E).inv_mem hu
  have e1 : valAt w u⁻¹ = 1 := hu' w
  have e2 : valAt w' u⁻¹ = 1 := hu' w'
  rwa [map_mul, map_mul, e1, e2, one_mul, one_mul] at h1

theorem infinite_of_split {w w' : HeightOneSpectrum (𝓞 H.E)} (h : ConjPl H.conj.toRingEquiv w w') (hne : w' ≠ w) :
    Infinite (DtT H ⧸ UOT H) := by
  refine Infinite.of_injective (fun n : ℤ => (QuotientGroup.mk (QuotientGroup.mk
    (localIdele H.E w (atFin w (unif w)) ^ n)) : DtT H ⧸ UOT H)) fun m n e => ?_
  have h1 := QuotientGroup.eq.1 e
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← zpow_neg, ← zpow_add] at h1
  have h2 := val_eq_of_mem_UOT H h h1
  rw [map_zpow, map_zpow, valAt_loc_self, valAt_loc_ne hne, valuation_unif, one_zpow, ← WithZero.exp_zsmul,
    ← WithZero.exp_zero, WithZero.exp_inj] at h2
  simp at h2
  omega

theorem valAt_finprod {L : Type} [Field L] [NumberField L] (n : HeightOneSpectrum (𝓞 L) → ℤ) (hn : {w | n w ≠ 0}.Finite)
    (w : HeightOneSpectrum (𝓞 L)) :
    valAt w (∏ᶠ v : HeightOneSpectrum (𝓞 L), localIdele L v (atFin v (unif v)) ^ (n v).toNat) =
      WithZero.exp (-((n w).toNat : ℤ)) := by
  rw [MonoidHom.map_finprod _ (hn.subset fun v hv h0 => hv (by simp [h0])), finprod_eq_single _ w]
  · rw [map_pow, valAt_loc_self, valuation_unif, ← WithZero.exp_nsmul]; simp
  · intro v hv
    rw [map_pow, valAt_loc_ne hv.symm, one_pow]

theorem valuation_eq_exp {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    w.valuation L (k : L) = WithZero.exp (-ordF w k) := by
  unfold ordF
  rw [neg_neg, WithZero.exp_log (by simp)]

theorem relDet_sign (u k : H.Eˣ) (hu : (u : H.E) * H.conj (k : H.E) = k) (hu1 : (u : H.E) * H.conj (u : H.E) = 1)
    (hfin : {w | ordF w u ≠ 0}.Finite) {w w' : HeightOneSpectrum (𝓞 H.E)} (h : ConjPl H.conj.toRingEquiv w w') :
    ∃ x : Ideles H.E, relDetT H 1 (Submodule.span _ {fun _ => ((1 : H.Eˣ) : H.E)}) (Submodule.span _ {fun _ => (u : H.E)}) =
      QuotientGroup.mk (QuotientGroup.mk x) ∧
      valAt w' x * w.valuation H.E (k : H.E) = valAt w x * w'.valuation H.E (k : H.E) := by
  refine ⟨_, rfl, ?_⟩
  have o1 : ∀ v : HeightOneSpectrum (𝓞 H.E), ordF v (1 : H.Eˣ) = 0 := fun v => by simp [ordF]
  simp only [detSub_rank_one, ordSub_span_singleton, o1, sub_zero]
  rw [valAt_finprod _ hfin, valAt_finprod _ hfin]
  have a1 := congrArg (w'.valuation H.E) hu
  have a2 := congrArg (w'.valuation H.E) hu1
  rw [map_mul, show w'.valuation H.E (H.conj (k : H.E)) = _ from h _] at a1
  rw [map_mul, show w'.valuation H.E (H.conj (u : H.E)) = _ from h _, map_one] at a2
  simp only [valuation_eq_exp, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at a1 a2 ⊢
  omega

end GlobalTheory.Mem.Chr.DetGroupModel

import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdInfMulFinPart

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.HeckeGal Filter Topology

namespace GlobalTheory.RingCls

section Idelic

theorem dvd_pow_pow_sub_one {O : Type} [CommRing O] {t x : O} {M : ℕ} (hM : t ∣ (M : O)) (hx : t ∣ x - 1) (k : ℕ) :
    t ^ (k + 1) ∣ x ^ (M ^ k) - 1 := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ M, pow_mul, ← mul_geom_sum, pow_succ t]
    refine mul_dvd_mul ih ?_
    have h1 : t ∣ x ^ (M ^ k) - 1 := hx.trans (sub_one_dvd_pow_sub_one _ _)
    have e : ∑ i ∈ Finset.range M, (x ^ (M ^ k)) ^ i = (M : O) + ∑ i ∈ Finset.range M, ((x ^ (M ^ k)) ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [e]
    exact dvd_add hM (Finset.dvd_sum fun i _ => h1.trans (sub_one_dvd_pow_sub_one _ _))

variable {E : Type} [Field E] [NumberField E]

theorem tendsto_pow_pow (v : HeightOneSpectrum (𝓞 E)) {M : ℕ} (hM : Valued.v ((M : ℕ) : v.adicCompletion E) < 1)
    {x : v.adicCompletion E} (hx : Valued.v (x - 1) < 1) :
    Tendsto (fun k : ℕ => x ^ (M ^ k)) atTop (𝓝 1) := by
  have hx1 : Valued.v x ≤ 1 := by
    have := Valuation.map_add_le (Valued.v : Valuation (v.adicCompletion E) _) hx.le (le_of_eq (map_one _))
    rwa [sub_add_cancel] at this
  let y : v.adicCompletionIntegers E := ⟨x, hx1⟩
  have hI := Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion E) _)
  obtain ⟨t, ht, h1, h2⟩ : ∃ t : v.adicCompletionIntegers E, Valued.v (t : v.adicCompletion E) < 1 ∧
      t ∣ (M : v.adicCompletionIntegers E) ∧ t ∣ y - 1 := by
    rcases le_total (Valued.v ((M : ℕ) : v.adicCompletion E)) (Valued.v (x - 1)) with h | h
    · exact ⟨y - 1, hx, hI.dvd_of_le h, dvd_rfl⟩
    · exact ⟨M, hM, dvd_rfl, hI.dvd_of_le h⟩
  have h0 : Tendsto (fun k : ℕ => (t : v.adicCompletion E) ^ (k + 1)) atTop (𝓝 0) :=
    (Valued.tendsto_zero_pow_of_v_lt_one ht).comp (tendsto_add_atTop_nat 1)
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (fun k => ?_) (tendsto_zero_iff_norm_tendsto_zero.1 h0)
  obtain ⟨c, hc⟩ := dvd_pow_pow_sub_one h1 h2 k
  have e : x ^ (M ^ k) - 1 = (t : v.adicCompletion E) ^ (k + 1) * c := congrArg Subtype.val hc
  rw [e, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (Valued.toNormedField.norm_le_one_iff.2 c.2)

theorem exists_nat_coprime {l : ℕ} (hl : l.Prime) {v : HeightOneSpectrum (𝓞 E)} (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) :
    ∃ M : ℕ, l.Coprime M ∧ Valued.v ((M : ℕ) : v.adicCompletion E) < 1 := by
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  obtain ⟨a, M, hM, hNM⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN l hl.ne_one
  have hmem : ((M : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    have h := Ideal.absNorm_mem v.asIdeal
    rw [hNM, Nat.cast_mul, Nat.cast_pow] at h
    exact (v.isPrime.mem_or_mem h).resolve_left fun h' => hv (v.isPrime.mem_of_pow_mem a h')
  refine ⟨M, hl.coprime_iff_not_dvd.mpr hM, ?_⟩
  have h : Valued.v (((algebraMap (𝓞 E) E (M : 𝓞 E) : E)) : v.adicCompletion E) =
      v.valuation E (algebraMap (𝓞 E) E (M : 𝓞 E)) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have h2 : v.valuation E (algebraMap (𝓞 E) E (M : 𝓞 E)) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hmem
  rw [← h] at h2
  have e : (((algebraMap (𝓞 E) E (M : 𝓞 E) : E)) : v.adicCompletion E) = ((M : ℕ) : v.adicCompletion E) := by
    rw [map_natCast]
    exact map_natCast (algebraMap E (v.adicCompletion E)) M
  rwa [e] at h2

variable {B : Type} [CommGroup B]

theorem tame {l : ℕ} (hl : l.Prime) (hB : ∀ x : B, ∃ n : ℕ, x ^ (l ^ n) = 1) {v : HeightOneSpectrum (𝓞 E)}
    (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (θ : (v.adicCompletion E)ˣ →* B)
    (hθ : IsOpen (θ.ker : Set (v.adicCompletion E)ˣ)) (x : (v.adicCompletion E)ˣ)
    (hx : Valued.v ((x : v.adicCompletion E) - 1) < 1) : θ x = 1 := by
  obtain ⟨M, hc, hM⟩ := exists_nat_coprime hl hv
  have ht : Tendsto (fun k : ℕ => x ^ (M ^ k)) atTop (𝓝 1) := by
    rw [Units.isEmbedding_val₀.tendsto_nhds_iff]
    simpa [Function.comp_def] using tendsto_pow_pow v hM hx
  obtain ⟨k, hk⟩ := (ht.eventually (hθ.mem_nhds θ.ker.one_mem)).exists
  have hk' : θ x ^ (M ^ k) = 1 := by rw [← map_pow]; exact hk
  obtain ⟨n, hn⟩ := hB (θ x)
  have := pow_gcd_eq_one.2 ⟨hn, hk'⟩
  rwa [(hc.pow n k).gcd_eq_one, pow_one] at this

theorem map_finPartI [IsTotallyComplex E] [Finite B] (ψ : Ideles E →* B) (a : Ideles E) :
    ψ (finPartI E a) = ψ a := by
  have hm : 0 < Nat.card B := Nat.card_pos
  have h2 : ∀ w : InfinitePlace E, ∃ y : w.Completion, y ^ Nat.card B = (a : AdeleRing (𝓞 E) E).1 w := fun w => by
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e ((a : AdeleRing (𝓞 E) E).1 w)) hm
    exact ⟨e.symm z, e.injective (by rw [map_pow, e.apply_symm_apply, hz])⟩
  choose y hy using h2
  let b : AdeleRing (𝓞 E) E := (y, 1)
  have hb : b ^ Nat.card B * (finPartI E a : AdeleRing (𝓞 E) E) = a :=
    Prod.ext (funext fun w => (mul_one _).trans (hy w)) (by
      show (1 : FiniteAdeleRing (𝓞 E) E) ^ Nat.card B * (a : AdeleRing (𝓞 E) E).2 = _
      rw [one_pow, one_mul])
  obtain ⟨u, hu⟩ : IsUnit b := (isUnit_pow_iff hm.ne').1 (isUnit_of_mul_isUnit_left (hb ▸ a.isUnit))
  have e : u ^ Nat.card B * finPartI E a = a := Units.ext (by rw [Units.val_mul, Units.val_pow_eq_pow_val, hu, hb])
  conv_rhs => rw [← e, map_mul, map_pow, pow_card_eq_one', one_mul]

theorem map_congr_unit [IsTotallyComplex E] [Finite B] {l : ℕ} (hl : l.Prime) (hB : ∀ x : B, ∃ n : ℕ, x ^ (l ^ n) = 1)
    (Q : Finset (HeightOneSpectrum (𝓞 E))) (ψ : Ideles E →* B) (hψ : IsOpen (ψ.ker : Set (Ideles E)))
    (hu : ∀ v, v ∉ Q ∨ v ∈ placesOver E l → ∀ x, IsUnitAt v x → ψ (localIdele E v x) = 1)
    {a : Ideles E} (ha : a ∈ unitIdl E) (hQ : ∀ v ∈ Q, Valued.v ((a : AdeleRing (𝓞 E) E).2 v - 1) < 1) :
    ψ a = 1 := by
  rw [← map_finPartI]
  refine (ψ.ker.isClosed_of_isOpen hψ).mem_of_tendsto
    (GlobalTheory.Mem.LocTriv.tendsto_part (finPartI_mem_unitIdl.2 ha) fun _ => rfl) (Eventually.of_forall fun S => ?_)
  refine Subgroup.prod_mem _ fun v _ => ?_
  by_cases h : v ∉ Q ∨ v ∈ placesOver E l
  · exact hu v h _ (ha v)
  · rw [not_or, not_not] at h
    exact tame hl hB h.2 (ψ.comp (localIdele E v)) (hψ.preimage (Determ.continuous_localIdele v)) _ (hQ v h.1)

def red (v : HeightOneSpectrum (𝓞 E)) : unitIdl E →* IsLocalRing.ResidueField (v.adicCompletionIntegers E) where
  toFun a := IsLocalRing.residue _ ⟨((a : Ideles E) : AdeleRing (𝓞 E) E).2 v, (a.2 v).le⟩
  map_one' := map_one (IsLocalRing.residue _)
  map_mul' a b := by
    rw [← map_mul]
    exact congrArg _ (Subtype.ext rfl)

theorem red_eq_one {v : HeightOneSpectrum (𝓞 E)} {a : unitIdl E} (h : red v a = 1) :
    Valued.v (((a : Ideles E) : AdeleRing (𝓞 E) E).2 v - 1) < 1 := by
  have h1 : IsLocalRing.residue (v.adicCompletionIntegers E)
      (⟨((a : Ideles E) : AdeleRing (𝓞 E) E).2 v, (a.2 v).le⟩ - 1) = 0 := by
    rw [map_sub, map_one, sub_eq_zero]; exact h
  rw [IsLocalRing.residue_eq_zero_iff] at h1
  exact (Valuation.mem_maximalIdeal_iff _ _).1 h1

theorem finiteIndex_of_congr (Q : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (Ideles E))
    (hD : ∀ k, diagUnits E k ∈ K)
    (hU : ∀ a ∈ unitIdl E, (∀ v ∈ Q, Valued.v ((a : AdeleRing (𝓞 E) E).2 v - 1) < 1) → a ∈ K) :
    K.FiniteIndex := by
  have := fun v : Q => Formalism.UG.P.glint_finite_residueField (F := E) v.1
  let ρ := (MonoidHom.pi fun v : Q => red (E := E) v.1).toHomUnits
  have h1 : ρ.ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have h2 : (K.subgroupOf (unitIdl E)).FiniteIndex := by
    refine Subgroup.finiteIndex_of_le (H := ρ.ker) fun a ha => hU a a.2 fun v hv => red_eq_one ?_
    exact congrFun (congrArg Units.val (MonoidHom.mem_ker.1 ha)) ⟨v, hv⟩
  have := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup E
  have h3 : (unitIdl E ⊔ K).FiniteIndex :=
    Subgroup.finiteIndex_of_le (H := unitIdl E ⊔ (diagUnits E).range)
      (sup_le_sup_left (by rintro _ ⟨k, rfl⟩; exact hD k) _)
  refine ⟨?_⟩
  rw [← Subgroup.relIndex_mul_index (le_sup_right : K ≤ unitIdl E ⊔ K), Subgroup.relIndex_sup_right]
  exact mul_ne_zero h2.1 h3.1

end Idelic

section Galois

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def IsRingKer (c : Ω ≃+* Ω) (l : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (G E Ω)) : Prop :=
  ∃ (B : Type) (_ : CommGroup B) (_ : Finite B) (φ : G E Ω →* B), (∀ x : B, ∃ n : ℕ, x ^ (l ^ n) = 1) ∧
    IsOpen (φ.ker : Set (G E Ω)) ∧ AntiHom c φ ∧
    (∀ v, v ∉ Q ∨ v ∈ placesOver E l → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := E) A, φ σ = 1) ∧
    φ.ker = K

def ringKer (c : Ω ≃+* Ω) (l : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 E))) : Subgroup (G E Ω) :=
  sInf {K | IsRingKer c l Q K}

variable (c : Ω ≃+* Ω) (l : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 E)))

theorem mem_ringKer {g : G E Ω} : g ∈ ringKer c l Q ↔ ∀ K, IsRingKer c l Q K → g ∈ K := Subgroup.mem_sInf

instance ringKer_normal : (ringKer c l Q).Normal :=
  ⟨fun g hg h => (mem_ringKer c l Q).2 fun K hK => by
    have := (mem_ringKer c l Q).1 hg K hK
    obtain ⟨B, _, _, φ, -, -, -, -, rfl⟩ := hK
    exact φ.normal_ker.conj_mem g this h⟩

def RingClass : Type := G E Ω ⧸ ringKer c l Q

instance : CommGroup (RingClass c l Q) :=
  { (inferInstance : Group (G E Ω ⧸ ringKer c l Q)) with
    mul_comm := fun x y => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective (s := ringKer c l Q) x
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective (s := ringKer c l Q) y
      refine QuotientGroup.eq.2 ((mem_ringKer c l Q).2 ?_)
      rintro _ ⟨B, _, _, φ, -, -, -, -, rfl⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, mul_comm (φ h), inv_mul_cancel] }

def art : G E Ω →* RingClass c l Q := QuotientGroup.mk' (ringKer c l Q)

theorem ker_art : (art c l Q).ker = ringKer c l Q := QuotientGroup.ker_mk' _

theorem art_eq_one {g : G E Ω} : art c l Q g = 1 ↔ g ∈ ringKer c l Q := QuotientGroup.eq_one_iff g

theorem art_surjective : Function.Surjective (art c l Q) := QuotientGroup.mk'_surjective _

theorem art_anti : AntiHom c (art c l Q) := fun g g' h => by
  rw [eq_inv_iff_mul_eq_one, ← map_mul, art_eq_one, mem_ringKer]
  rintro _ ⟨B, _, _, φ, -, -, ha, -, rfl⟩
  rw [MonoidHom.mem_ker, map_mul, ha g g' h, inv_mul_cancel]

theorem art_unram {v : HeightOneSpectrum (𝓞 E)} (hv : v ∉ Q ∨ v ∈ placesOver E l) (A : ValuationSubring Ω)
    (hA : IsPlaceOver A v) (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) : art c l Q σ = 1 := by
  rw [art_eq_one, mem_ringKer]
  rintro _ ⟨B, _, _, φ, -, -, -, hu, rfl⟩
  exact hu v hv A hA σ hσ

theorem art_universal (hQ : ∀ v ∈ Q, v ∉ placesOver E l) (B : Type) [CommGroup B] [Finite B]
    (hB : ∀ x : B, ∃ n : ℕ, x ^ (l ^ n) = 1) (φ : G E Ω →* B) (ho : IsOpen (φ.ker : Set (G E Ω))) (ha : AntiHom c φ)
    (hu : ∀ v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := E) A, φ σ = 1) :
    ∃ f : RingClass c l Q →* B, f.comp (art c l Q) = φ :=
  ⟨QuotientGroup.lift (ringKer c l Q) φ (sInf_le ⟨B, inferInstance, inferInstance, φ, hB, ho, ha,
    fun v hv => hu v (hv.elim id fun h h' => hQ v h' h), rfl⟩), MonoidHom.ext fun _ => rfl⟩

theorem ringKer_anti {Q Q' : Finset (HeightOneSpectrum (𝓞 E))} (h : Q' ⊆ Q) : ringKer c l Q ≤ ringKer c l Q' :=
  sInf_le_sInf fun _ ⟨B, i, j, φ, hB, ho, ha, hu, e⟩ =>
    ⟨B, i, j, φ, hB, ho, ha, fun v hv => hu v (hv.imp_left fun h1 h2 => h1 (h h2)), e⟩

def res (Q Q' : Finset (HeightOneSpectrum (𝓞 E))) (h : Q' ⊆ Q) : RingClass c l Q →* RingClass c l Q' :=
  QuotientGroup.lift (ringKer c l Q) (art c l Q') ((ringKer_anti c l h).trans (ker_art c l Q').ge)

theorem res_comp_art (Q Q' : Finset (HeightOneSpectrum (𝓞 E))) (h : Q' ⊆ Q) :
    (res c l Q Q' h).comp (art c l Q) = art c l Q' := MonoidHom.ext fun _ => rfl

theorem isRingKer_top : IsRingKer c l Q ⊤ :=
  ⟨PUnit, inferInstance, inferInstance, 1, fun _ => ⟨0, rfl⟩, by simp, fun _ _ _ => rfl,
    fun _ _ _ _ _ _ => rfl, MonoidHom.ker_one⟩

variable {c l Q} in
theorem IsRingKer.inf {K K' : Subgroup (G E Ω)} (h : IsRingKer c l Q K) (h' : IsRingKer c l Q K') :
    IsRingKer c l Q (K ⊓ K') := by
  obtain ⟨B, _, _, φ, hB, ho, ha, hu, rfl⟩ := h
  obtain ⟨B', _, _, φ', hB', ho', ha', hu', rfl⟩ := h'
  refine ⟨B × B', inferInstance, inferInstance, φ.prod φ', fun x => ?_, ?_,
    fun g g' e => Prod.ext (ha g g' e) (ha' g g' e),
    fun v hv A hA σ hσ => Prod.ext (hu v hv A hA σ hσ) (hu' v hv A hA σ hσ), MonoidHom.ker_prod _ _⟩
  · obtain ⟨n, hn⟩ := hB x.1
    obtain ⟨m, hm⟩ := hB' x.2
    refine ⟨n + m, Prod.ext ?_ ?_⟩
    · show x.1 ^ l ^ (n + m) = 1
      rw [pow_add, pow_mul, hn, one_pow]
    · show x.2 ^ l ^ (n + m) = 1
      rw [add_comm, pow_add, pow_mul, hm, one_pow]
  · rw [MonoidHom.ker_prod]
    exact ho.inter ho'

theorem isRingKer_ringKer [(ringKer c l Q).FiniteIndex] : IsRingKer c l Q (ringKer c l Q) := by
  have hfin : {K | IsRingKer c l Q K}.Finite := by
    refine Set.Finite.of_finite_image (f := Subgroup.map (QuotientGroup.mk' (ringKer c l Q))) (Set.toFinite _) ?_
    intro K hK K' hK' e
    have h1 := Subgroup.comap_map_eq_self (f := QuotientGroup.mk' (ringKer c l Q)) (H := K)
      (by rw [QuotientGroup.ker_mk']; exact sInf_le hK)
    have h2 := Subgroup.comap_map_eq_self (f := QuotientGroup.mk' (ringKer c l Q)) (H := K')
      (by rw [QuotientGroup.ker_mk']; exact sInf_le hK')
    rw [← h1, e, h2]
  obtain ⟨K, hK, hmin⟩ := hfin.exists_minimal ⟨⊤, isRingKer_top c l Q⟩
  have e : ringKer c l Q = K :=
    le_antisymm (sInf_le hK) (le_sInf fun K' hK' => (hmin (hK.inf hK') inf_le_left).trans inf_le_right)
  rwa [e]

theorem finiteIndex_ringKer [IsTotallyComplex E] {a : Ideles E →* Gab E Ω} (ha : IsGlobalArtin a) (hl : l.Prime) :
    (ringKer c l Q).FiniteIndex := by
  have hc : (commutator (G E Ω)).topologicalClosure ≤ (art c l Q).ker := by
    rw [ker_art]
    refine le_sInf ?_
    rintro _ ⟨B, _, _, φ, -, ho, -, -, rfl⟩
    exact Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker φ) (φ.ker.isClosed_of_isOpen ho)
  let π : Gab E Ω →* RingClass c l Q := QuotientGroup.lift _ (art c l Q) hc
  have hπ : ∀ σ, π (toAb E Ω σ) = art c l Q σ := fun _ => rfl
  have hs : Function.Surjective (π.comp a) := fun x => by
    obtain ⟨σ, rfl⟩ := art_surjective c l Q x
    obtain ⟨y, hy⟩ := ha.quot.surjective (toAb E Ω σ)
    exact ⟨y, by rw [MonoidHom.comp_apply, hy, hπ]⟩
  have hi : (π.comp a).ker.FiniteIndex := by
    refine finiteIndex_of_congr Q _ (fun k => ?_) fun x hx hQ => ?_
    · have hk : diagUnits E k ∈ a.ker := by
        rw [ha.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hk, map_one]
    · obtain ⟨σ, hσ⟩ := toAb_surjective (a x)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← hσ, hπ, art_eq_one, mem_ringKer]
      rintro _ ⟨B, _, _, φ, hB, ho, -, hu, rfl⟩
      let _ : TopologicalSpace B := ⊥
      have : DiscreteTopology B := ⟨rfl⟩
      have hφ : Continuous φ := continuous_of_isOpen_ker' φ ho
      have hψ : Continuous ((liftAb φ hφ).comp a) := (continuous_liftAb φ hφ).comp ha.quot.continuous
      have := map_congr_unit hl hB Q ((liftAb φ hφ).comp a) ((isOpen_discrete {1}).preimage hψ)
        (fun v hv y hy => by
          obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
          obtain ⟨τ, hτ, e⟩ := (ha.ine v A hA _).1 ⟨y, hy, rfl⟩
          rw [MonoidHom.comp_apply, ← e, liftAb_toAb, hu v hv A hA τ hτ]) hx hQ
      rwa [MonoidHom.comp_apply, ← hσ, liftAb_toAb] at this
  have : Finite (π.comp a).range := by
    have := Subgroup.finite_quotient_of_finiteIndex (H := (π.comp a).ker)
    exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange (π.comp a)).toEquiv
  have : Finite (G E Ω ⧸ ringKer c l Q) :=
    Finite.of_surjective (fun x : (π.comp a).range => (x.1 : RingClass c l Q)) fun x => ⟨⟨x, hs x⟩, rfl⟩
  exact Subgroup.finiteIndex_of_finite_quotient

theorem finite_ringClass [(ringKer c l Q).FiniteIndex] : Finite (RingClass c l Q) :=
  Subgroup.finite_quotient_of_finiteIndex

theorem isOpen_ker_art [(ringKer c l Q).FiniteIndex] : IsOpen ((art c l Q).ker : Set (G E Ω)) := by
  obtain ⟨B, _, _, φ, -, ho, -, -, e⟩ := isRingKer_ringKer c l Q
  rwa [ker_art, ← e]

theorem pow_eq_one [(ringKer c l Q).FiniteIndex] (x : RingClass c l Q) : ∃ n : ℕ, x ^ (l ^ n) = 1 := by
  obtain ⟨B, _, _, φ, hB, -, -, -, e⟩ := isRingKer_ringKer c l Q
  obtain ⟨g, rfl⟩ := art_surjective c l Q x
  obtain ⟨n, hn⟩ := hB (φ g)
  exact ⟨n, by rw [← map_pow, art_eq_one, ← e, MonoidHom.mem_ker, map_pow, hn]⟩

end Galois

theorem ringClass_laws (hA : GlobalTheory.Published.GlobalArtinReciprocity) (E Ω : Type) [Field E] [NumberField E]
    [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (c : Ω ≃+* Ω) (l : ℕ) (hl : l.Prime) :
    (∀ Q : Finset (HeightOneSpectrum (𝓞 E)), Finite (RingClass c l Q)) ∧
    (∀ (Q : Finset (HeightOneSpectrum (𝓞 E))) (x : RingClass c l Q), ∃ n : ℕ, x ^ (l ^ n) = 1) ∧
    (∀ Q : Finset (HeightOneSpectrum (𝓞 E)), Function.Surjective (art c l Q)) ∧
    (∀ Q : Finset (HeightOneSpectrum (𝓞 E)), IsOpen ((art c l Q).ker : Set (G E Ω))) ∧
    (∀ Q : Finset (HeightOneSpectrum (𝓞 E)), AntiHom c (art c l Q)) ∧
    (∀ (Q : Finset (HeightOneSpectrum (𝓞 E))) v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
      ∀ σ ∈ Ine (F := E) A, art c l Q σ = 1) ∧
    (∀ Q : Finset (HeightOneSpectrum (𝓞 E)), (∀ v ∈ Q, v ∉ placesOver E l) → ∀ (B : Type) [CommGroup B] [Finite B],
      (∀ x : B, ∃ n : ℕ, x ^ (l ^ n) = 1) → ∀ φ : G E Ω →* B, IsOpen (φ.ker : Set (G E Ω)) → AntiHom c φ →
      (∀ v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := E) A, φ σ = 1) →
      ∃ f : RingClass c l Q →* B, f.comp (art c l Q) = φ) ∧
    ∀ (Q Q' : Finset (HeightOneSpectrum (𝓞 E))) (h : Q' ⊆ Q), (res c l Q Q' h).comp (art c l Q) = art c l Q' := by
  obtain ⟨a, ha⟩ := hA E Ω
  have := fun Q : Finset (HeightOneSpectrum (𝓞 E)) => finiteIndex_ringKer c l Q ha hl
  exact ⟨fun Q => finite_ringClass c l Q, fun Q => pow_eq_one c l Q, art_surjective c l, fun Q => isOpen_ker_art c l Q,
    art_anti c l, fun Q v hv => art_unram c l Q (Or.inl hv), fun Q hQ B _ _ => art_universal c l Q hQ B,
    res_comp_art c l⟩

theorem exists_ringClass_host (hA : GlobalTheory.Published.GlobalArtinReciprocity) (R : Ranks) (H : Host R) (what₂ : Rows.Data R)
    (N : NData R H what₂) (cc : N.Om ≃+* N.Om) (Tw : Type) (l : Tw → ℕ) [lPrime : ∀ i, Fact (l i).Prime] :
    ∃ (C : Tw → Finset (HeightOneSpectrum (𝓞 H.E)) → Type) (_ : ∀ i Q, CommGroup (C i Q))
      (_ : ∀ i Q, Fintype (C i Q)) (art : ∀ i Q, G H.E N.Om →* C i Q)
      (res : ∀ i (Q Q' : Finset (HeightOneSpectrum (𝓞 H.E))), Q' ⊆ Q → (C i Q →* C i Q')),
      (∀ i Q (x : C i Q), ∃ n : ℕ, x ^ (l i ^ n) = 1) ∧
      (∀ i Q, Function.Surjective (art i Q)) ∧
      (∀ i Q, IsOpen ((art i Q).ker : Set (G H.E N.Om))) ∧
      (∀ i Q, AntiHom cc (art i Q)) ∧
      (∀ i Q v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, art i Q σ = 1) ∧
      (∀ i Q, (∀ v ∈ Q, v ∉ placesOver H.E (l i)) → ∀ (A' : Type) [CommGroup A'] [Finite A'],
        (∀ x : A', ∃ n : ℕ, x ^ (l i ^ n) = 1) → ∀ φ : G H.E N.Om →* A',
        IsOpen (φ.ker : Set (G H.E N.Om)) → AntiHom cc φ →
        (∀ v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, φ σ = 1) →
        ∃ f : C i Q →* A', f.comp (art i Q) = φ) ∧
      ∀ i Q Q' (h : Q' ⊆ Q), (res i Q Q' h).comp (art i Q) = art i Q' := by
  have : IsCMField H.E := H.isCMField_hostE
  have h := fun i => ringClass_laws hA H.E N.Om cc (l i) (lPrime i).out
  exact ⟨fun i Q => RingClass cc (l i) Q, inferInstance, fun i Q => @Fintype.ofFinite _ ((h i).1 Q),
    fun i Q => art cc (l i) Q, fun i => res cc (l i), fun i => (h i).2.1, fun i => (h i).2.2.1,
    fun i => (h i).2.2.2.1, fun i => (h i).2.2.2.2.1, fun i => (h i).2.2.2.2.2.1,
    fun i => (h i).2.2.2.2.2.2.1, fun i => (h i).2.2.2.2.2.2.2⟩

end GlobalTheory.RingCls

end

import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws
import GroundTheory.GlobalFields.SemilocalAlgebras.LocalDegree
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTwoPlacesOverOfIsSquareLocal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSquareOneAddFourMul

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical
open GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

namespace UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations

private theorem sq_of_near {K : Type} [Field K] [NumberField K] (v : P K) (δ c : Kv v)
    (h2 : Valued.v (2 : Kv v) = 1) (hc : Valued.v c = 1) (hd : Valued.v (δ - c ^ 2) < 1) :
    IsSquare δ := by
  haveI := GlobalTheory.HenselSquare.isAdicComplete_integers K v
  have h20 : (2 : Kv v) ≠ 0 := fun h => by simp [h] at h2
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  set z : Kv v := (δ - c ^ 2) / (4 * c ^ 2) with hz
  have h4 : Valued.v (4 * c ^ 2 : Kv v) = 1 := by
    rw [show (4 : Kv v) = 2 * 2 by norm_num, map_mul, map_mul, map_pow, h2, hc]; simp
  have hzv : Valued.v z < 1 := by
    rw [hz, map_div₀, h4, div_one]; exact hd
  let zo : v.adicCompletionIntegers K := ⟨z, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).2 hzv.le⟩
  have hzm : zo ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hzv.ne
  obtain ⟨s, hs⟩ := GlobalTheory.HenselSquare.exists_sq_add_eq _ _ hzm
  have hs' : (s : Kv v) ^ 2 + s = z := congrArg Subtype.val hs
  refine ⟨c * (1 + 2 * s), ?_⟩
  have : δ = c ^ 2 + z * (4 * c ^ 2) := by
    rw [hz]; field_simp; ring
  rw [this, ← hs']; ring

section Ext
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem finrank_two (D : Dat F E) : Module.finrank F E = 2 := by
  rw [Module.finrank_eq_card_basis D.b, Fintype.card_fin]

private theorem isQuad (D : Dat F E) : GlobalTheory.QNorm.IsQuad D.δ D.θ D.σ where
  nonsq := by
    rintro ⟨s, hs⟩
    have h1 : (D.θ - algebraMap F E s) * (D.θ + algebraMap F E s) = 0 := by
      have := D.sq
      rw [hs, map_mul] at this
      linear_combination this
    have hind := D.b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hind
    rcases mul_eq_zero.1 h1 with h | h
    · have := hind ![-s, 1] (by
        simp [Fin.sum_univ_two, D.b0, D.b1, Algebra.smul_def]
        linear_combination h) 1
      simp at this
    · have := hind ![s, 1] (by
        simp [Fin.sum_univ_two, D.b0, D.b1, Algebra.smul_def]
        linear_combination h) 1
      simp at this
  sq := D.sq
  conj := D.conj
  span x := by
    refine ⟨D.b.repr x 0, D.b.repr x 1, ?_⟩
    conv_lhs => rw [← D.b.sum_repr x]
    simp [Fin.sum_univ_two, D.b0, D.b1, Algebra.smul_def]

variable (D : Dat F E) (v : P F) (w : P E) [hl : w.asIdeal.LiesOver v.asIdeal]

private theorem notSq (hu : ∀ w' : P E, w'.asIdeal.LiesOver v.asIdeal → w' = w) :
    ¬ IsSquare (algebraMap F (Kv v) D.δ) := by
  intro h
  obtain ⟨a, b, hab, ha, hb⟩ := GlobalTheory.QNorm.two_places_of_isSquare F E D.δ D.θ D.σ (isQuad D) v h
  exact hab ((hu a ((below_eq_iff a v).1 ha)).trans (hu b ((below_eq_iff b v).1 hb)).symm)

local notation "ι" => completionMap v w
local notation "θw" => algebraMap E (Kv w) D.θ

private theorem iota_delta : ι (algebraMap F (Kv v) D.δ) = θw ^ 2 := by
  rw [completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (Kv w), ← D.sq, map_pow]

private theorem val_iota (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) (x : Kv v) :
    Valued.v (ι x) = Valued.v x := by
  rw [valued_completionMap, he, pow_one]

private theorem val_c_add (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) (h2 : Valued.v (2 : Kv v) = 1)
    (hθ : Valued.v θw = 1) (hu : ∀ w' : P E, w'.asIdeal.LiesOver v.asIdeal → w' = w)
    (c : Kv v) (hc : Valued.v c ≤ 1) : Valued.v (ι c + θw) = 1 := by
  have hv := val_iota v w he
  have hle : Valued.v (ι c + θw) ≤ 1 := by
    refine (Valuation.map_add _ _ _).trans (max_le ?_ hθ.le)
    rw [hv]; exact hc
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  have hc1 : Valued.v c = 1 := by
    refine le_antisymm hc (not_lt.1 fun h => ?_)
    have : Valued.v (ι c) < Valued.v θw := by rw [hv, hθ]; exact h
    rw [add_comm, Valuation.map_add_eq_of_lt_left _ this, hθ] at hlt
    exact lt_irrefl _ hlt
  refine notSq D v w hu (sq_of_near v _ c h2 hc1 ?_)
  rw [← hv, map_sub, iota_delta, map_pow,
    show θw ^ 2 - ι c ^ 2 = (ι c + θw) * (θw - ι c) by ring, map_mul]
  refine mul_lt_one_of_lt_of_le hlt ?_
  refine (Valuation.map_sub _ _ _).trans (max_le hθ.le ?_)
  rw [hv]; exact hc

private theorem val_coord (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) (h2 : Valued.v (2 : Kv v) = 1)
    (hθ : Valued.v θw = 1) (hu : ∀ w' : P E, w'.asIdeal.LiesOver v.asIdeal → w' = w)
    (u t : Kv v) : Valued.v (ι u + ι t * θw) = max (Valued.v u) (Valued.v t) := by
  have hv := val_iota v w he
  by_cases ht : t = 0
  · subst ht; simp [hv]
  have ht' : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 ht
  by_cases hut : Valued.v u ≤ Valued.v t
  · have h1 : Valued.v (u / t) ≤ 1 := by
      rw [map_div₀]; exact div_le_one_of_le₀ hut zero_le'
    have h3 := val_c_add D v w he h2 hθ hu (u / t) h1
    have h4 : ι u + ι t * θw = ι t * (ι (u / t) + θw) := by
      rw [mul_add, ← map_mul, show t * (u / t) = u by field_simp]
    rw [h4, map_mul, h3, hv, mul_one, max_eq_right hut]
  · have hlt : Valued.v t < Valued.v u := not_le.1 hut
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hlt
    have h1 : Valued.v (t / u) < 1 := by
      rw [map_div₀]
      exact (div_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hu0))).2 hlt
    have h4 : ι u + ι t * θw = ι u * (1 + ι (t / u) * θw) := by
      rw [mul_add, mul_one, ← mul_assoc, ← map_mul, show u * (t / u) = t by field_simp]
    have h5 : Valued.v (ι (t / u) * θw) < Valued.v (1 : Kv w) := by
      rw [map_mul, hθ, mul_one, hv, map_one]; exact h1
    rw [h4, map_mul, Valuation.map_add_eq_of_lt_left _ h5, map_one, mul_one, hv, max_eq_left hlt.le]

private theorem aniso_of (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) (h2 : Valued.v (2 : Kv v) = 1)
    (hθ : Valued.v θw = 1) (hu : ∀ w' : P E, w'.asIdeal.LiesOver v.asIdeal → w' = w) :
    Aniso D.δ v := by
  intro u t
  have hv := val_iota v w he
  rw [← hv, map_sub, map_pow, map_mul, iota_delta, map_pow,
    show ι u ^ 2 - θw ^ 2 * ι t ^ 2 = (ι u + ι t * θw) * (ι u + ι (-t) * θw) by rw [map_neg]; ring,
    map_mul, val_coord D v w he h2 hθ hu, val_coord D v w he h2 hθ hu, Valuation.map_neg, sq]

end Ext

section Fin2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (D : Dat F E) (v : P F) (w : P E) [hl : w.asIdeal.LiesOver v.asIdeal]

local notation "ι" => completionMap v w
local notation "θw" => algebraMap E (Kv w) D.θ

private theorem normV_eq : normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  have e : v = below F w := ((below_eq_iff w v).2 hl).symm
  subst e
  have := w.isMaximal
  have := (below F w).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (below F w).asIdeal ^ _
  rw [← Ideal.absNorm_relNorm (𝓞 F) (𝓞 E) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (below F w).asIdeal, map_pow]

private theorem adeleMap_sg (hu : ∀ w' : P E, w'.asIdeal.LiesOver v.asIdeal → w' = w) (x : Kv v) :
    adeleMap F E (sg v x) = sg w (ι x) := by
  obtain ⟨-, -, hc, -, -, -, -, hs, -, -⟩ := sgLaws F v
  obtain ⟨-, -, hc', -, -, -, -, hs', -, -⟩ := sgLaws E w
  refine Prod.ext ?_ (FiniteAdeleRing.ext E fun w' => ?_)
  · change InfinitePlace.infiniteAdeleRingMap (sg v x).1 = (sg w _).1
    rw [(hs x).1, (hs' _).1, map_zero]
  · change completionMap (below F w') w' ((sg v x).2 (below F w')) = (sg w _).2 w'
    by_cases h : w' = w
    · subst h
      have hb : below F w' = v := (below_eq_iff _ _).2 hl
      subst hb
      exact (congrArg _ (hc x)).trans (hc' _).symm
    · have hb : below F w' ≠ v := fun hb => h (hu w' ((below_eq_iff _ _).1 hb))
      rw [(hs x).2 _ hb, map_zero, (hs' _).2 _ h]

private theorem inert_of (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) (h2 : Valued.v (2 : Kv v) = 1)
    (hθ : Valued.v θw = 1) (hu : ∀ w' : P E, w'.asIdeal.LiesOver v.asIdeal → w' = w)
    (hf : w.asIdeal.inertiaDeg (𝓞 F) = 2) : Inert D v w := by
  obtain ⟨hadd, hmul, -, hidl, -, -, -, -, -, -⟩ := sgLaws E w
  obtain ⟨-, -, -, hidl', -, -, -, -, -, -⟩ := sgLaws F v
  have hv := val_iota v w he
  have hval := val_coord D v w he h2 hθ hu
  have hr : Module.finrank (Kv v) (Kv w) = 2 := by
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg, he, hf, one_mul]
  haveI : Module.Finite (Kv v) (Kv w) := Module.finite_of_finrank_pos (by omega)
  let L : (Kv v × Kv v) →ₗ[Kv v] Kv w :=
    { toFun := fun p => ι p.1 + ι p.2 * θw
      map_add' := fun p q => by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring
      map_smul' := fun c p => by
        change ι (c * p.1) + ι (c * p.2) * θw = c • (ι p.1 + ι p.2 * θw)
        rw [Algebra.smul_def, algebraMap_completion_eq, map_mul, map_mul]
        ring }
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun p hp => ?_
    have h := hval p.1 p.2
    rw [show ι p.1 + ι p.2 * θw = 0 from hp, map_zero] at h
    have h1 : Valued.v p.1 = 0 := le_antisymm (h ▸ le_max_left _ _) zero_le'
    have h3 : Valued.v p.2 = 0 := le_antisymm (h ▸ le_max_right _ _) zero_le'
    exact Prod.ext ((Valuation.zero_iff _).1 h1) ((Valuation.zero_iff _).1 h3)
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_prod, Module.finrank_self, hr])).1 hinj
  have hmk : ∀ u t : A F, D.mkE u t = adeleMap F E u + adeleMap F E t * rt D.θ := fun _ _ => rfl
  refine ⟨?_, aniso_of D v w he h2 hθ hu, ⟨(AddEquiv.ofBijective L.toAddMonoidHom ⟨hinj, hsurj⟩), ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [normV_eq v w, hf]
  · intro u t
    change sg w (ι u + ι t * θw) = _
    rw [hmk, adeleMap_sg v w hu, adeleMap_sg v w hu, hadd, mul_comm (sg w (ι t)), hmul, mul_comm]
    rfl
  · intro u t
    exact hval u t
  · intro c u t
    change (ι c + ι 0 * θw) * (ι u + ι t * θw) = ι (c * u) + ι (c * t) * θw
    simp only [map_zero, zero_mul, add_zero, map_mul]
    ring
  · change ι 1 + ι 0 * θw = 1
    simp
  · intro ϖ hϖ
    let ϖ' : (Kv w)ˣ := Units.map (ι : Kv v →* Kv w) ϖ
    have hco : ((idl w ϖ' : (A E)ˣ) : A E) = adeleMap F E ((idl v ϖ : (A F)ˣ) : A F) := by
      rw [hidl, hidl', map_add, map_one, adeleMap_sg v w hu, map_sub, map_one]
      rfl
    refine ⟨ϖ', ?_, ?_, ?_⟩
    · change Valued.v (ι (ϖ : Kv v)) = _
      rw [hv]
      exact hϖ
    · rw [hco, hmk, map_zero, zero_mul, add_zero]
    · have : idl w ϖ' = ideleEmbedding F E (idl v ϖ) := Units.ext hco
      rw [this, ideleNorm_ideleEmbedding, finrank_two D]

private theorem split_of (he : w.asIdeal.ramificationIdx (𝓞 F) = 1)
    (hf : w.asIdeal.inertiaDeg (𝓞 F) = 1) : SplitAt v w := by
  have hr : Module.finrank (Kv v) (Kv w) = 1 := by
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg, he, hf, one_mul]
  have hs : Function.Surjective ι := fun y => by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : Kv w) one_ne_zero).1 hr y
    exact ⟨c, by rw [← hc, Algebra.smul_def, mul_one]; rfl⟩
  refine ⟨by rw [normV_eq v w, hf, pow_one], RingEquiv.ofBijective ι ⟨(completionMap v w).injective, hs⟩,
    continuous_completionMap v w, fun x => ?_, fun x => val_iota v w he x⟩
  change ι _ = _
  rw [completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (Kv w)]

end Fin2

section Final
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem ev_val (x : E) (hx : x ≠ 0) : ∀ᶠ w : P E in cofinite, w.valuation E x = 1 := by
  have h1 := HeightOneSpectrum.Support.finite (𝓞 E) x
  have h3 := HeightOneSpectrum.Support.finite (𝓞 E) x⁻¹
  filter_upwards [h1.compl_mem_cofinite, h3.compl_mem_cofinite] with w hw hw'
  have a1 : w.valuation E x ≤ 1 := not_lt.1 hw
  have a2 : (w.valuation E x)⁻¹ ≤ 1 := by
    rw [← map_inv₀]; exact not_lt.1 hw'
  have h0 : w.valuation E x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  exact le_antisymm a1 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 a2)

variable (F E) in
private theorem ev_unram : ∀ᶠ w : P E in cofinite, w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
  have h1 : differentIdeal (𝓞 F) (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have h3 := Ideal.finite_factors h1
  filter_upwards [h3.compl_mem_cofinite] with w hw
  haveI : Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal := not_dvd_differentIdeal_iff.1 hw
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

end Final

end UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations

open UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations in
theorem UpperTheory.ConvolutionTheory.R2.H.placeAe :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E), ∀ᶠ w : P E in cofinite, ∀ v : P F, Below v w → SplitAt v w ∨ Inert D v w := by
  intro F E _ _ _ _ _ D
  have hθ0 : D.θ ≠ 0 := by
    rw [← D.b1]; exact D.b.ne_zero 1
  filter_upwards [ev_unram F E, ev_val (2 : E) two_ne_zero, ev_val D.θ hθ0] with w he h2 hθ v hb
  haveI hl : w.asIdeal.LiesOver v.asIdeal := ⟨hb⟩
  have hθ' : Valued.v (algebraMap E (Kv w) D.θ) = 1 := by
    rw [valued_algebraMap_field]; exact hθ
  have h2' : Valued.v (2 : Kv v) = 1 := by
    rw [← val_iota v w he, map_ofNat, ← map_ofNat (algebraMap E (Kv w)) 2, valued_algebraMap_field]
    exact h2
  have hs := sum_ramificationIdx_mul_inertiaDeg E v
  rw [finrank_two D] at hs
  have hpos : ∀ x : PlacesOver E v, 1 ≤ x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F) := fun x =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  let W0 : PlacesOver E v := ⟨w, hl⟩
  have hW := Finset.add_sum_erase Finset.univ
    (fun x : PlacesOver E v => x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F)) (Finset.mem_univ W0)
  rw [hs] at hW
  set R := ∑ x ∈ Finset.univ.erase W0, x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F) with hR
  have hW' : w.asIdeal.inertiaDeg (𝓞 F) + R = 2 := by
    simpa only [W0, he, one_mul] using hW
  have hf1 : 1 ≤ w.asIdeal.inertiaDeg (𝓞 F) := by
    have := hpos W0
    simpa only [W0, he, one_mul] using this
  by_cases hf : w.asIdeal.inertiaDeg (𝓞 F) = 1
  · exact Or.inl (split_of v w he hf)
  · have hf2 : w.asIdeal.inertiaDeg (𝓞 F) = 2 := by omega
    refine Or.inr (inert_of D v w he h2' hθ' (fun w' hw' => ?_) hf2)
    by_contra hne
    have hmem : (⟨w', hw'⟩ : PlacesOver E v) ∈ Finset.univ.erase W0 :=
      Finset.mem_erase.2 ⟨fun h => hne (congrArg Subtype.val h), Finset.mem_univ _⟩
    have h3 : (⟨w', hw'⟩ : PlacesOver E v).1.asIdeal.ramificationIdx (𝓞 F) *
        (⟨w', hw'⟩ : PlacesOver E v).1.asIdeal.inertiaDeg (𝓞 F) ≤ R :=
      Finset.single_le_sum (f := fun x : PlacesOver E v =>
        x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F)) (fun _ _ => Nat.zero_le _) hmem
    have h1 := hpos ⟨w', hw'⟩
    omega

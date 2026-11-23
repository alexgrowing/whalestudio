import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousInfIdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitsCOfModEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsPrimitiveRootTorsionOrder

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.PsiExist

section General

variable {L : Type} [Field L] [NumberField L]

def cFin (v : HeightOneSpectrum (𝓞 L)) : Ideles L →* (v.adicCompletion L)ˣ :=
  Units.map { toFun := fun a : AdeleRing (𝓞 L) L => a.2 v, map_one' := rfl, map_mul' := fun _ _ => rfl }

def cInf (w : InfinitePlace L) : Ideles L →* (w.Completion)ˣ :=
  Units.map { toFun := fun a : AdeleRing (𝓞 L) L => a.1 w, map_one' := rfl, map_mul' := fun _ _ => rfl }

open Classical in

def cut (a : FiniteAdeleRing (𝓞 L) L) (T : Finset (HeightOneSpectrum (𝓞 L))) : FiniteAdeleRing (𝓞 L) L :=
  ⟨fun v => if v ∈ T then a v else 1, by
    refine Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun w hw => ?_)
    by_contra h
    apply hw
    have h' : w ∉ T := h
    simp only [h', if_false]
    exact one_mem _⟩

theorem tendsto_cut (a : FiniteAdeleRing (𝓞 L) L) : Filter.Tendsto (cut a) Filter.atTop (nhds a) := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 L)) := {v | a v ∈ v.adicCompletionIntegers L}
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 L))) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]; exact a.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal S)
  let f : Finset (HeightOneSpectrum (𝓞 L)) → P := fun T => ⟨fun v => if v ∈ T then a v else 1, by
    rw [Filter.eventually_principal]
    intro w hw
    by_cases h : w ∈ T
    · simp only [h, if_true]; exact hw
    · simp only [h, if_false]; exact one_mem _⟩
  let a' : P := ⟨fun v => a v, by rw [Filter.eventually_principal]; exact fun w hw => hw⟩
  have hf : Filter.Tendsto f Filter.atTop (nhds a') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change a v = if v ∈ T then a v else 1
    rw [if_pos this]
  exact ((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf

theorem prod_inf (a : Ideles L) :
    ((∏ w, infIdele L w (cInf w a) : Ideles L) : AdeleRing (𝓞 L) L) = ((a : AdeleRing (𝓞 L) L).1, 1) := by
  classical
  rw [Units.coe_prod]
  let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
    MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
  let f : ∀ w : InfinitePlace L, w.Completion := fun w => (a : AdeleRing (𝓞 L) L).1 w
  change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (f w)) = ι f
  rw [← map_prod, Finset.univ_prod_mulSingle]

theorem prod_fin (a : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    ((∏ v ∈ T, localIdele L v (cFin v a) : Ideles L) : AdeleRing (𝓞 L) L) = (1, cut (a : AdeleRing (𝓞 L) L).2 T) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact Prod.ext rfl (Subtype.ext (funext fun v => by simp [cut]; rfl))
  | insert u T hu ih =>
    rw [Finset.prod_insert hu, Units.val_mul, ih]
    refine Prod.ext (mul_one (1 : InfiniteAdeleRing L)) (Subtype.ext (funext fun v => ?_))
    change ((localIdele L u (cFin u a) : Ideles L) : AdeleRing (𝓞 L) L).2 v * (if v ∈ T then _ else 1) =
      if v ∈ insert u T then _ else 1
    by_cases h : v = u
    · subst h
      rw [AntiExist.loc_self, if_neg hu, if_pos (Finset.mem_insert_self _ _), mul_one]; rfl
    · rw [AntiExist.loc_ne h, one_mul]; simp [h]

theorem tendsto_prod_local (a : Ideles L) :
    Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 L)) =>
      (∏ w, infIdele L w (cInf w a)) * ∏ v ∈ T, localIdele L v (cFin v a)) Filter.atTop (nhds a) := by
  have h : ∀ a : Ideles L, Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 L)) =>
      (((∏ w, infIdele L w (cInf w a)) * ∏ v ∈ T, localIdele L v (cFin v a) : Ideles L) : AdeleRing (𝓞 L) L))
      Filter.atTop (nhds (a : AdeleRing (𝓞 L) L)) := fun a => by
    have e : ∀ T : Finset (HeightOneSpectrum (𝓞 L)),
        (((∏ w, infIdele L w (cInf w a)) * ∏ v ∈ T, localIdele L v (cFin v a) : Ideles L) : AdeleRing (𝓞 L) L) =
          ((a : AdeleRing (𝓞 L) L).1, cut (a : AdeleRing (𝓞 L) L).2 T) := fun T => by
      rw [Units.val_mul, prod_inf, prod_fin]
      exact Prod.ext (mul_one _) (one_mul _)
    simp only [e]
    exact tendsto_const_nhds.prodMk_nhds (tendsto_cut _)
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h a).prodMk_nhds ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  have h2 := h a⁻¹
  simp only [map_inv, Finset.prod_inv_distrib, ← mul_inv] at h2
  exact h2

theorem eq_one_of_unr (χ : HChar L) (hi : ∀ k, χ.inf k = 1) (hu : ∀ v, χ.UnrAt v) {a : Ideles L} (ha : a ∈ unitIdl L) :
    χ.1 a = 1 := by
  have key : (fun u : ∀ w : InfinitePlace L, (w.Completion)ˣ => χ.1 (∏ w, infIdele L w (u w))) = fun _ => 1 := by
    refine (GlobalTheory.InfTypeLocal.denseRange_atInf L).equalizer ?_ continuous_const ?_
    · exact χ.2.1.comp (continuous_finsetProd _ fun w _ =>
        (GlobalTheory.InfTypeLocal.continuous_infIdele L w).comp (continuous_apply w))
    · funext k
      have h1 : χ.1 (infDiag k) = 1 := hi k
      unfold infDiag at h1
      rw [MonoidHom.finsetProd_apply] at h1
      exact h1
  have h1 := (χ.2.1.tendsto _).comp (tendsto_prod_local a)
  have h2 : ∀ T : Finset (HeightOneSpectrum (𝓞 L)),
      χ.1 ((∏ w, infIdele L w (cInf w a)) * ∏ v ∈ T, localIdele L v (cFin v a)) = 1 := fun T => by
    have h3 : χ.1 (∏ w, infIdele L w (cInf w a)) = 1 := congrFun key fun w => cInf w a
    have h4 : ∀ v, χ.1 (localIdele L v (cFin v a)) = 1 := fun v => hu v (cFin v a) (ha v)
    rw [map_mul, h3, one_mul, map_prod]
    exact Finset.prod_eq_one fun v _ => h4 v
  exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr fun T => (h2 T).symm)

theorem exists_exponent (L : Type) [Field L] [NumberField L] :
    ∃ h : ℕ, 0 < h ∧ ∀ χ : HChar L, (∀ k, χ.inf k = 1) → (∀ v, χ.UnrAt v) → χ ^ h = 1 := by
  have hf := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup L
  refine ⟨_, Nat.pos_of_ne_zero hf.index_ne_zero, fun χ hi hu => ?_⟩
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  obtain ⟨u, hu', _, ⟨k, rfl⟩, e⟩ := Subgroup.mem_sup.1 ((unitIdl L ⊔ (diagUnits L).range).pow_index_mem x)
  change χ.1 x ^ _ = 1
  rw [← map_pow, ← e, map_mul, χ.2.2 k, eq_one_of_unr χ hi hu hu', mul_one]

theorem loc_eq_one (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) (hu : χ.UnrAt v) (hv : χ.val v = 1)
    (x : (v.adicCompletion L)ˣ) : χ.loc v x = 1 := by
  set p := atFin v (unif v) with hp
  have hpv : Valued.v (p : v.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec v
  have hx0 : Valued.v (x : v.adicCompletion L) ≠ 0 := by simp
  set n : ℤ := WithZero.log (Valued.v (x : v.adicCompletion L)) with hn
  have hxn : Valued.v (x : v.adicCompletion L) = WithZero.exp n := (WithZero.exp_log hx0).symm
  have hunit : IsUnitAt v (x * p ^ n) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hpv, hxn, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp
  have h1 := hu _ hunit
  have hp1 : χ.loc v p = 1 := hv
  rw [map_mul, map_zpow, hp1, one_zpow, mul_one] at h1
  exact h1

theorem loc_pow (χ : HChar L) (n : ℕ) (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    (χ ^ n).loc v x = χ.loc v x ^ n := rfl

theorem trivOn_pow {F : Type} [Field F] [NumberField F] [Algebra F L] {χ : HChar L} (h : χ.TrivOn F) (n : ℕ) :
    (χ ^ n).TrivOn F := by
  induction n with
  | zero => rw [pow_zero, ← mul_inv_cancel χ]; exact h.mul h.inv
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem exists_char_of_dvd {G : Type} [Group G] [IsCyclic G] {m : ℕ} (hm : m ≠ 0) (h : m ∣ Nat.card G) :
    ∃ θ : G →* ℂˣ, ∀ n : ℕ, θ ^ n = 1 ↔ m ∣ n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hζ := Complex.isPrimitiveRoot_exp m hm
  have hζ' := hζ.isUnit_unit hm
  set ζ : ℂˣ := (hζ.isUnit hm).unit
  have ho : orderOf ζ ∣ orderOf g := by
    rw [← hζ'.eq_orderOf, orderOf_eq_card_of_forall_mem_zpowers hg]
    exact h
  refine ⟨monoidHomOfForallMemZpowers hg ho, fun n => ?_⟩
  rw [MonoidHom.eq_iff_eq_on_generator hg, MonoidHom.pow_apply, monoidHomOfForallMemZpowers_apply_gen,
    MonoidHom.one_apply]
  exact hζ'.pow_eq_one_iff_dvd n

private theorem exists_residue_char_pow (v : HeightOneSpectrum (𝓞 L)) {p l W : ℕ}
    (hp : p.Prime) (hl : l ≠ 0) (hW : W ≠ 0) (hpl : W * l ∣ p - 1) (hv : Ideal.absNorm v.asIdeal = p) :
    ∃ θ : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ, (∀ x, x ^ W = 1 → θ x = 1) ∧ ∀ n : ℕ, θ ^ n = 1 ↔ l ∣ n := by
  have hc : Nat.card (𝓞 L ⧸ v.asIdeal) = p := by
    rw [← hv, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 L ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  have := v.isPrime
  have : IsCyclic (𝓞 L ⧸ v.asIdeal)ˣ := inferInstance
  have hmax := v.isMaximal
  have hu : Nat.card (𝓞 L ⧸ v.asIdeal)ˣ = p - 1 := by
    let _ := Ideal.Quotient.field v.asIdeal
    rw [← hc]
    exact Nat.card_units _
  obtain ⟨θ, hθ⟩ := exists_char_of_dvd (G := (𝓞 L ⧸ v.asIdeal)ˣ) (m := W * l)
    (mul_ne_zero hW hl) (by rw [hu]; exact hpl)
  refine ⟨θ ^ W, fun x hx => ?_, fun n => ?_⟩
  · rw [MonoidHom.pow_apply, ← map_pow, hx, map_one]
  · rw [← pow_mul, hθ, Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hW)]

theorem exists_place_over (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ Q : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ Q.asIdeal := by
  have hne : Ideal.span {((p : ℕ) : 𝓞 K)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 : IsUnit (algebraMap ℤ (𝓞 K) (p : ℤ)) := by simpa using hu
    have h2 : IsUnit (p : ℤ) := isUnit_of_map_unit _ _ h1
    exact (Nat.prime_iff_prime_int.1 hp).not_isUnit h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : ((p : ℕ) : 𝓞 K) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hmem))

omit [NumberField L] in

theorem not_mem_of_coprime {a b : ℕ} (h : a.Coprime b) {v : HeightOneSpectrum (𝓞 L)} (ha : (a : 𝓞 L) ∈ v.asIdeal) :
    (b : 𝓞 L) ∉ v.asIdeal := fun hb => by
  obtain ⟨x, y, e⟩ := Nat.Coprime.cast (R := 𝓞 L) h
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left x ha) (v.asIdeal.mul_mem_left y hb)))

theorem finite_over {p : ℕ} (hp : p ≠ 0) : {v : HeightOneSpectrum (𝓞 L) | (p : 𝓞 L) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {(p : 𝓞 L)} ≠ 0 := by simpa using hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

end General

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

open Classical in

theorem exists_basic {l q : ℕ} (hl : l ≠ 0) (hq : q.Prime) (hql : H.w * l ∣ q - 1) (hs : SplitsC H.E q) :
    ∃ χ : HChar H.E, χ.TrivOn H.F ∧ (∀ k, χ.inf k = 1) ∧ (∀ v, χ.TameAt v) ∧ (∀ v, ¬ OverP H q v → χ.UnrAt v) ∧
      (∀ v, (χ ^ l).UnrAt v) ∧ ∃ w, OverP H q w ∧ ∀ n : ℕ, (χ ^ n).UnrAt w → l ∣ n := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hce : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
  have hsp := GlobalTheory.Mem.Chr.splitsC_main R H q hq hs
  obtain ⟨w, hw⟩ := exists_place_over H.E hq
  have hQ : ((q : ℕ) : 𝓞 H.K) ∈ (w.under (𝓞 H.K)).asIdeal := by
    show algebraMap (𝓞 H.K) (𝓞 H.E) ((q : ℕ) : 𝓞 H.K) ∈ w.asIdeal
    rwa [map_natCast]
  have hθ : ∀ v : HeightOneSpectrum (𝓞 H.E), ∃ θ : (𝓞 H.E ⧸ v.asIdeal)ˣ →* ℂˣ, (∀ x, x ^ H.w = 1 → θ x = 1) ∧
      (OverP H q v → ∀ n : ℕ, θ ^ n = 1 ↔ l ∣ n) := by
    intro v
    by_cases h : OverP H q v
    · obtain ⟨θ, h1, h2⟩ := exists_residue_char_pow v hq hl H.w_pos.ne' hql (hsp v h).1
      exact ⟨θ, h1, fun _ => h2⟩
    · exact ⟨1, fun _ _ => rfl, fun h' => absurd h' h⟩
  choose θ hθ1 hθ2 using hθ
  obtain ⟨χ, -, ht, hi, htame, hunr, -, hord⟩ :=
    GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn H.F H.E c (R.Psi) (embPsi H) hcm (fun _ => 0) {w} θ
    (by
      intro w1 hw1 w' hcj hw'
      rw [Finset.mem_singleton] at hw1 hw'
      subst hw1 hw'
      rw [hce] at hcj
      exact ((hsp _ hw).2.2.2 _ hQ _ hcj).2.1 rfl rfl)
    (by
      intro ζ hζ
      have h1 : ζ ^ H.w = 1 := by
        have h0 : ((ζ : 𝓞 H.E) : H.E) ^ H.w = 1 := (H.isMu_iff _).1 hζ
        apply Units.ext
        apply RingOfIntegers.ext
        simpa using h0
      have h2 : θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) = 1 :=
        hθ1 w _ (by rw [← map_pow, h1, map_one])
      simp only [neg_zero, zpow_zero, Finset.prod_const_one, one_mul, Finset.prod_singleton]
      rw [h2]
      rfl)
  obtain ⟨hord1, hord2⟩ := forall_and.1 (hord w (Finset.mem_singleton_self w))
  refine ⟨χ, ht, fun k => ?_, htame, fun v hv => hunr v (fun h => hv ?_) fun w1 hw1 hcj => hv ?_, fun v => ?_,
    w, hw, fun n hn => (hθ2 w hw n).1 ((hord1 n).1 hn)⟩
  · apply Units.ext
    rw [hi k]
    simp
  · rw [Finset.mem_singleton.1 h]
    exact hw
  · rw [Finset.mem_singleton.1 hw1, hce] at hcj
    exact ((hsp w hw).2.2.2 _ hQ v hcj).1
  · by_cases h1 : v = w
    · subst h1
      exact (hord1 l).2 ((hθ2 _ hw l).2 dvd_rfl)
    · by_cases h2 : ConjPl c.toRingEquiv w v
      · exact (hord2 l v h2).2 ((hθ2 _ hw l).2 dvd_rfl)
      · intro x hx
        rw [loc_pow, hunr v (fun h => h1 (Finset.mem_singleton.1 h))
          (fun w1 hw1 => by rwa [Finset.mem_singleton.1 hw1]) x hx, one_pow]

open Classical in

theorem psi_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (l : ℕ), l.Prime → ∀ T : Finset ℕ, 0 ∉ T → ∃ (Q : Finset (HeightOneSpectrum (𝓞 H.E))) (ψ : HChar H.E), Q.Nonempty ∧ IsPsi (H := H) l Q ψ ∧ SplitsCompletely (H := H) Q ∧ ∀ v ∈ Q, ∀ p ∈ T, ¬ OverP H p v := by
  intro R H l hl T hT
  have hN : H.w * l * (H.QS * H.q * H.d) ≠ 0 :=
    mul_ne_zero (mul_ne_zero H.w_pos.ne' hl.ne_zero) H.condN_ne_zero
  let P : Set ℕ := {q | q.Prime ∧ q ≡ 1 [MOD H.w * l * (H.QS * H.q * H.d)]} \ Set.Iic (l + T.sup id)
  have hP : P.Infinite := (Nat.infinite_setOfPred_prime_modEq_one hN).sdiff (Set.finite_Iic _)
  have hPp : ∀ q : P, q.1.Prime := fun q => q.2.1.1
  have hPs : ∀ q : P, SplitsC H.E q.1 := fun q =>
    GlobalTheory.Mem.Chr.splitsC_of_modEq_one R H q.1 (hPp q) (q.2.1.2.of_mul_left _)
  have hPc : ∀ (q : P) (p : ℕ), p ≠ 0 → p ≤ l + T.sup id → q.1.Coprime p := fun q p h0 hp =>
    Nat.coprime_of_lt_prime h0 (lt_of_le_of_lt hp (not_le.1 q.2.2)) (hPp q)
  choose χ ht hi htame hunr hpow w hw hord using fun q : P => exists_basic H hl.ne_zero (hPp q)
    ((Nat.modEq_iff_dvd' (hPp q).one_le).1 (q.2.1.2.of_mul_right _).symm) (hPs q)
  obtain ⟨h, hh, hexp⟩ := exists_exponent H.E
  have hlh : l * h ≠ 0 := mul_ne_zero hl.ne_zero hh.ne'
  have hχ : ∀ q, χ q ^ (l * h) = 1 := fun q => by
    rw [pow_mul]
    refine hexp _ (fun k => ?_) (hpow q)
    show (χ q).inf k ^ l = 1
    rw [hi, one_pow]
  have : NeZero (l * h) := ⟨hlh⟩
  have : Finite {v : HeightOneSpectrum (𝓞 H.E) | (l : 𝓞 H.E) ∈ v.asIdeal} := finite_over hl.ne_zero
  have : Infinite P := hP.to_subtype
  let f : P → {v : HeightOneSpectrum (𝓞 H.E) | (l : 𝓞 H.E) ∈ v.asIdeal} → rootsOfUnity (l * h) ℂ := fun q v =>
    ⟨(χ q).val v.1, congrArg (fun ξ : HChar H.E => ξ.val v.1) (hχ q)⟩
  obtain ⟨q, q', hne, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_pow_mul_and_not_dvd hlh l hl.ne_one
  have hcop : q.1.Coprime q'.1 := (Nat.coprime_primes (hPp q) (hPp q')).2 fun e => hne (Subtype.ext e)
  have hu : ∀ v, ¬ OverP H q.1 v → ¬ OverP H q'.1 v → ((χ q * (χ q')⁻¹) ^ m).UnrAt v := fun v h1 h2 x hx => by
    rw [loc_pow, (hunr q v h1).mul (hunr q' v h2).inv x hx, one_pow]
  have hov : ∀ v, ¬ ((χ q * (χ q')⁻¹) ^ m).UnrAt v → ∃ r : P, OverP H r.1 v := fun v hv => by
    by_contra hc
    exact hv (hu v (fun h => hc ⟨q, h⟩) fun h => hc ⟨q', h⟩)
  have hfin : {v | ¬ ((χ q * (χ q')⁻¹) ^ m).UnrAt v}.Finite := by
    refine ((finite_over (L := H.E) (hPp q).ne_zero).union (finite_over (hPp q').ne_zero)).subset fun v hv => ?_
    by_contra hc
    exact hv (hu v (fun h => hc (Or.inl h)) fun h => hc (Or.inr h))
  refine ⟨hfin.toFinset, (χ q * (χ q')⁻¹) ^ m, ⟨w q, hfin.mem_toFinset.2 fun hc => hm (hord q m fun x hx => ?_)⟩,
    ⟨⟨a, ?_⟩, trivOn_pow ((ht q).mul (ht q').inv) m, fun v x hx hx' => ?_, fun v => ?_, fun v hv x => ?_, fun v hv => ?_⟩,
    fun v hv p hp hpv v' hv' => ?_, fun v hv p hp => ?_⟩
  · have h1 := hc x hx
    rwa [loc_pow, HChar.loc_mul, HChar.loc_inv, hunr q' _ (not_mem_of_coprime hcop (hw q)) x hx, inv_one, mul_one] at h1
  · unfold HChar.OrderDvd
    rw [← pow_mul, mul_comm m, ← ham, mul_pow, inv_pow, hχ, hχ, inv_one, mul_one]
  · rw [loc_pow, (htame q v).mul (htame q' v).inv x hx hx', one_pow]
  · rw [hfin.mem_toFinset]
    exact not_not.symm
  · have h1 : ∀ r : P, (χ r).UnrAt v := fun r => hunr r v
      (not_mem_of_coprime (hPc r l hl.ne_zero (Nat.le_add_right _ _)).symm hv)
    have h2 : (χ q).val v = (χ q').val v := congrArg Subtype.val (congrFun hf ⟨v, hv⟩)
    rw [loc_pow, loc_eq_one _ v ((h1 q).mul (h1 q').inv) (by rw [HChar.val_mul, HChar.val_inv, h2, mul_inv_cancel]),
      one_pow]
  · obtain ⟨r, hr⟩ := hov v (hfin.mem_toFinset.1 hv)
    exact (GlobalTheory.Mem.Chr.splitsC_main R H r.1 (hPp r) (hPs r) v hr).2.2.1
  · obtain ⟨r, hr⟩ := hov v (hfin.mem_toFinset.1 hv)
    have e : r.1 = p := by
      by_contra e
      exact not_mem_of_coprime ((Nat.coprime_primes (hPp r) hp).2 e) hr hpv
    subst e
    have h1 := GlobalTheory.Mem.Chr.splitsC_main R H r.1 (hPp r) (hPs r) v' hv'
    exact ⟨h1.1, h1.2.1⟩
  · obtain ⟨r, hr⟩ := hov v (hfin.mem_toFinset.1 hv)
    exact not_mem_of_coprime (hPc r p (fun e => hT (e ▸ hp))
      ((Finset.le_sup (f := id) hp).trans (Nat.le_add_left _ _))) hr

end GlobalTheory.Mem.PsiExist

import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolT
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnifVSpec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.FiniteNeighbourhoodSecond
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensSAChar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensSA

noncomputable section

namespace PI.VolStabSW

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW

variable {F : Type} [Field F] [NumberField F]

theorem af_add (y z : Af F) (w : HeightOneSpectrum (𝓞 F)) : (y + z) w = y w + z w := rfl
theorem af_sub (y z : Af F) (w : HeightOneSpectrum (𝓞 F)) : (y - z) w = y w - z w := rfl
theorem af_neg (y : Af F) (w : HeightOneSpectrum (𝓞 F)) : (-y) w = -y w := rfl
theorem af_zero (w : HeightOneSpectrum (𝓞 F)) : (0 : Af F) w = 0 := rfl

theorem adele_pairing_zero_add (y z : Af F) : pairA F 0 (y + z) = pairA F 0 y + pairA F 0 z := by
  exact Prod.ext (show (0 : Ainf F) = 0 + 0 from (add_zero 0).symm) rfl

theorem pairA_nsmul0 (m : ℕ) (y : Af F) : pairA F 0 (m • y) = m • pairA F 0 y := by
  exact Prod.ext (show (0 : Ainf F) = m • (0 : Ainf F) from (smul_zero m).symm) rfl

open Classical in
theorem singleV_self (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) : singleV F v t v = t := by
  show (Pi.single v t : ∀ w : HeightOneSpectrum (𝓞 F), Fv F w) v = t
  exact Pi.single_eq_same v t

open Classical in
theorem singleV_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (t : Fv F v) : singleV F v t w = 0 := by
  show (Pi.single v t : ∀ w : HeightOneSpectrum (𝓞 F), Fv F w) w = 0
  exact Pi.single_eq_of_ne h t

theorem ev_pow_mul_sub (v : HeightOneSpectrum (𝓞 F)) {W : Set (Fv F v)} (hW : W ∈ 𝓝 (0 : Fv F v)) :
    ∃ n : ℕ, ∀ s ∈ v.adicCompletionIntegers F, unifV v ^ n * s ∈ W := by
  obtain ⟨γ, hγ⟩ := (Valued.is_topological_valuation W).mp hW
  obtain ⟨n, hn⟩ := ((unifV_spec v).2.1.eventually
    ((Valued.is_topological_valuation _).mpr ⟨γ, subset_rfl⟩)).exists
  refine ⟨n, fun s hs => hγ ?_⟩
  have hs' : Valued.v s ≤ 1 := hs
  have hs'' : Valued.v.restrict s ≤ 1 := by
    first
      | simpa using hs'
      | exact_mod_cast hs'
      | (rw [← map_one Valued.v.restrict]; simpa [Valuation.restrict_le_iff] using hs')
  show Valued.v.restrict (unifV v ^ n * s) < _
  rw [map_mul]
  have h1 : Valued.v.restrict (unifV v ^ n) * Valued.v.restrict s ≤ Valued.v.restrict (unifV v ^ n) := by
    first
      | exact mul_le_of_le_one_right' hs''
      | exact (mul_le_mul' le_rfl hs'').trans (mul_one _).le
      | exact mul_le_of_le_one_right (zero_le _) hs''
  exact lt_of_le_of_lt h1 hn

def U0 (I : Finset (HeightOneSpectrum (𝓞 F))) (n : HeightOneSpectrum (𝓞 F) → ℕ) :
    AddSubgroup (Af F) where
  carrier := {y | (∀ w, y w ∈ w.adicCompletionIntegers F) ∧
    ∀ w ∈ I, (unifV w ^ n w)⁻¹ * y w ∈ w.adicCompletionIntegers F}
  zero_mem' := ⟨fun w => by rw [af_zero]; exact zero_mem _, fun w _ => by rw [af_zero, mul_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro y z ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
    refine ⟨fun w => ?_, fun w hw => ?_⟩
    · rw [af_add]; exact add_mem (hy1 w) (hz1 w)
    · rw [af_add, mul_add]; exact add_mem (hy2 w hw) (hz2 w hw)
  neg_mem' := by
    rintro y ⟨hy1, hy2⟩
    refine ⟨fun w => ?_, fun w hw => ?_⟩
    · rw [af_neg]; exact neg_mem (hy1 w)
    · rw [af_neg, mul_neg]; exact neg_mem (hy2 w hw)

theorem isOpen_adelic_neighbourhood (I : Finset (HeightOneSpectrum (𝓞 F))) (n : HeightOneSpectrum (𝓞 F) → ℕ) :
    IsOpen (U0 I n : Set (Af F)) := by
  have hO : ∀ w : HeightOneSpectrum (𝓞 F), IsOpen (w.adicCompletionIntegers F : Set (Fv F w)) := by
    intro w
    first
      | exact Valued.isOpen_valuationSubring _
      | exact Valued.valuationSubring_isOpen _
      | exact (w.adicCompletionIntegers F).isOpen
  have hev : ∀ w : HeightOneSpectrum (𝓞 F), Continuous fun y : Af F => y w := by
    intro w
    first
      | exact RestrictedProduct.continuous_eval w
      | exact RestrictedProduct.continuous_apply w
  have h1 : IsOpen {y : Af F | ∀ w, y w ∈ w.adicCompletionIntegers F} := by
    first
      | exact RestrictedProduct.isOpen_forall_mem hO
      | exact RestrictedProduct.isOpen_forall_mem (fun w => hO w)
  have h2 : IsOpen {y : Af F | ∀ w ∈ I, (unifV w ^ n w)⁻¹ * y w ∈ w.adicCompletionIntegers F} := by
    have e : {y : Af F | ∀ w ∈ I, (unifV w ^ n w)⁻¹ * y w ∈ w.adicCompletionIntegers F} =
        ⋂ w ∈ I, {y : Af F | (unifV w ^ n w)⁻¹ * y w ∈ w.adicCompletionIntegers F} := by
      ext y
      simp
    rw [e]
    exact isOpen_biInter_finset fun w _ => (hO w).preimage (continuous_const.mul (hev w))
  exact h1.inter h2

theorem adele_character_trivial_open (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∃ (I : Finset (HeightOneSpectrum (𝓞 F))) (n : HeightOneSpectrum (𝓞 F) → ℕ),
      ∀ y ∈ U0 I n, ψ (pairA F 0 y) = 1 := by
  classical
  set U : Set (AF F) := {x | 1 / 2 < (ψ x).re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp hψ.1)
  let Φ : (∀ v : HeightOneSpectrum (𝓞 F),
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))) → AF F :=
    fun x => pairA F 0 (RestrictedProduct.structureMap _ _ Filter.cofinite x)
  have hΦ : Continuous Φ :=
    continuous_const.prodMk RestrictedProduct.isEmbedding_structureMap.continuous
  let x0 : ∀ v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => ⟨0, zero_mem _⟩
  have hx0 : Φ x0 = 0 := by
    show pairA F 0 _ = 0
    have : (RestrictedProduct.structureMap _ _ Filter.cofinite x0 : Af F) = 0 := by
      apply RestrictedProduct.ext
      intro j
      rfl
    rw [this]
    rfl
  have hx0U : x0 ∈ Φ ⁻¹' U := by
    simp only [Set.mem_preimage, hx0, hUdef, Set.mem_setOf_eq, AddChar.map_zero_eq_one,
      Complex.one_re]
    norm_num
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 (hU.preimage hΦ) x0 hx0U
  have hn : ∀ w : HeightOneSpectrum (𝓞 F), ∃ m : ℕ, w ∈ I → ∀ s ∈ w.adicCompletionIntegers F,
      ∃ h : unifV w ^ m * s ∈ ((w.adicCompletionIntegers F : Set (w.adicCompletion F))),
        (⟨unifV w ^ m * s, h⟩ : ((w.adicCompletionIntegers F : Set (w.adicCompletion F)))) ∈ u w := by
    intro w
    by_cases hw : w ∈ I
    · obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.1 (hu w hw).1
      have h0 : (0 : Fv F w) ∈ t := by
        have := (hu w hw).2
        rw [← hte] at this
        exact this
      obtain ⟨m, hm⟩ := ev_pow_mul_sub w (ht.mem_nhds h0)
      refine ⟨m, fun _ s hs => ⟨mul_mem (pow_mem (unifV_spec w).2.2 m) hs, ?_⟩⟩
      rw [← hte]
      exact hm s hs
    · exact ⟨0, fun h => absurd h hw⟩
  choose n hn using hn
  refine ⟨I, n, ?_⟩
  have hbig : ∀ y ∈ U0 I n, 1 / 2 < (ψ (pairA F 0 y)).re := by
    intro y hy
    let x : ∀ v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
      fun w => ⟨y w, hy.1 w⟩
    have hx : x ∈ (I : Set _).pi u := by
      intro w hw
      have hne : unifV w ^ n w ≠ 0 := pow_ne_zero _ (unifV_spec w).1
      obtain ⟨h, hmem⟩ := hn w hw _ (hy.2 w hw)
      have e : (⟨unifV w ^ n w * ((unifV w ^ n w)⁻¹ * y w), h⟩ :
          ((w.adicCompletionIntegers F : Set (w.adicCompletion F)))) = x w := by
        apply Subtype.ext
        show unifV w ^ n w * ((unifV w ^ n w)⁻¹ * y w) = y w
        rw [mul_inv_cancel_left₀ hne]
      rw [← e]
      exact hmem
    have e : Φ x = pairA F 0 y := by
      show pairA F 0 _ = _
      congr 1
    have := hsub hx
    simp only [Set.mem_preimage, e, hUdef, Set.mem_setOf_eq] at this
    exact this
  intro y hy
  apply eq_one_of_pow _ (hψ.2.1 _)
  intro k
  rw [← AddChar.map_nsmul_eq_pow, ← pairA_nsmul0]
  exact hbig _ (AddSubgroup.nsmul_mem _ hy _)

def lamPsi (ψ : AddChar (AF F) ℂ) : Submodule (𝓞 F) F where
  carrier := {a | ∀ r : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((r : F) * a))) = 1}
  add_mem' := by
    intro a b ha hb r
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_add, map_add, adele_pairing_zero_add, AddChar.map_add_eq_mul, ha r, hb r, one_mul]
  zero_mem' := by
    intro r
    rw [mul_zero, map_zero]
    exact AddChar.map_zero_eq_one ψ
  smul_mem' := by
    intro c a ha r
    simp only [Set.mem_setOf_eq] at ha ⊢
    have := ha (r * c)
    rw [Algebra.smul_def]
    convert this using 4
    push_cast
    rw [mul_assoc]

def chiInf (ψ : AddChar (AF F) ℂ) : AddChar (InfiniteAdeleRing F) ℂ where
  toFun x := ψ (pairA F x 0)
  map_zero_eq_one' := by
    show ψ (pairA F 0 0) = 1
    exact AddChar.map_zero_eq_one ψ
  map_add_eq_mul' x y := by
    show ψ (pairA F (x + y) 0) = ψ (pairA F x 0) * ψ (pairA F y 0)
    rw [← AddChar.map_add_eq_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · show x + y = x + y
      rfl
    · show (0 : Af F) = 0 + 0
      rw [add_zero]

theorem algebraMap_AF (a : F) :
    algebraMap F (AF F) a = pairA F (algebraMap F (Ainf F) a) 0 + pairA F 0 (algebraMap F (Af F) a) := by
  exact Prod.ext (show algebraMap F (Ainf F) a = algebraMap F (Ainf F) a + 0 from (add_zero _).symm)
    (show algebraMap F (Af F) a = 0 + algebraMap F (Af F) a from (zero_add _).symm)

theorem psi_fin_of_char (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (a : F) (h : ψ (pairA F 0 (algebraMap F (Af F) a)) = 1) :
    chiInf ψ (algebraMap F (InfiniteAdeleRing F) a) = 1 := by
  have h1 : ψ (algebraMap F (AF F) a) = 1 := hψ.2.2.1 a
  rw [algebraMap_AF, AddChar.map_add_eq_mul, h, mul_one] at h1
  exact h1

theorem condExact_of (hS : SAf) (hC : ChInf) : CondExact := by
  intro F _ _ ψ hψ
  classical
  obtain ⟨I, n, hU⟩ := adele_character_trivial_open ψ hψ
  by_contra hne
  rw [Filter.not_eventually, Filter.frequently_cofinite_iff_infinite] at hne
  set X := {v : HeightOneSpectrum (𝓞 F) | ¬∀ t : Fv F v,
    (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (s * t) = 1) → t ∈ v.adicCompletionIntegers F}
    with hX

  have key : ∀ v ∈ X, v ∉ I → ∃ a : F, 1 < Valued.v (algebraMap F (Fv F v) a) ∧ a ∈ lamPsi ψ := by
    intro v hvX hvI
    simp only [hX, Set.mem_setOf_eq, not_forall] at hvX
    obtain ⟨t, ht, htO⟩ := hvX
    have ht1 : 1 < Valued.v t := (HeightOneSpectrum.notMem_adicCompletionIntegers (𝓞 F) F v).1 htO
    obtain ⟨a, ha⟩ := hS F (U0 I n) (isOpen_adelic_neighbourhood I n) (singleV F v t)
    have hdv : (singleV F v t - algebraMap F (Af F) a) v = t - algebraMap F (Fv F v) a := by
      rw [af_sub, singleV_self]
      rfl
    have hdw : ∀ w, w ≠ v → (singleV F v t - algebraMap F (Af F) a) w = - algebraMap F (Fv F w) a := by
      intro w hw
      rw [af_sub, singleV_ne v w hw, zero_sub]
      rfl
    have hta : Valued.v (t - algebraMap F (Fv F v) a) < Valued.v t := by
      have := ha.1 v
      rw [hdv, HeightOneSpectrum.mem_adicCompletionIntegers] at this
      exact lt_of_le_of_lt this ht1
    have hav : Valued.v (algebraMap F (Fv F v) a) = Valued.v t := by
      have := Valuation.map_sub_eq_of_lt_left Valued.v hta
      rwa [sub_sub_cancel] at this
    refine ⟨a, hav ▸ ht1, ?_⟩
    intro r
    have hrint : ∀ w : HeightOneSpectrum (𝓞 F),
        algebraMap F (Fv F w) (r : F) ∈ w.adicCompletionIntegers F := by
      intro w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have e : Valued.v (((r : F) : w.adicCompletion F)) = w.valuation F (r : F) :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (r : F)
      exact (e ▸ w.valuation_le_one r : Valued.v (((r : F) : w.adicCompletion F)) ≤ 1)
    set y : Af F := algebraMap F (Af F) ((r : F) * a) with hy
    have hyw : ∀ w, y w = algebraMap F (Fv F w) (r : F) * algebraMap F (Fv F w) a := by
      intro w
      rw [hy, map_mul]
      rfl
    have hz : y - singleV F v (y v) ∈ U0 I n := by
      refine ⟨fun w => ?_, fun w hw => ?_⟩
      · rw [af_sub]
        by_cases hwv : w = v
        · subst hwv
          rw [singleV_self, sub_self]
          exact zero_mem _
        · rw [singleV_ne v w hwv, sub_zero, hyw]
          refine mul_mem (hrint w) ?_
          have := neg_mem (ha.1 w)
          rwa [hdw w hwv, neg_neg] at this
      · have hwv : w ≠ v := fun h => hvI (h ▸ hw)
        rw [af_sub, singleV_ne v w hwv, sub_zero, hyw, mul_left_comm]
        refine mul_mem (hrint w) ?_
        have := neg_mem (ha.2 w hw)
        rwa [hdw w hwv, mul_neg, neg_neg] at this
    have hsplit : pairA F 0 y = pairA F 0 (y - singleV F v (y v)) + pairA F 0 (singleV F v (y v)) := by
      rw [← adele_pairing_zero_add, sub_add_cancel]
    show ψ (pairA F 0 y) = 1
    rw [hsplit, AddChar.map_add_eq_mul, hU _ hz, one_mul]
    show psiV F ψ v (y v) = 1
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp at ht1
    have hq : y v / t ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hyw, map_mul, hav,
        mul_div_assoc, div_self ((Valuation.ne_zero_iff _).2 ht0), mul_one]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (hrint v)
    have := ht _ hq
    rwa [div_mul_cancel₀ _ ht0] at this

  have hne' : ∀ c : F, ∃ v, v ∈ X ∧ v ∉ I ∧ v ∉ HeightOneSpectrum.Support (𝓞 F) c := by
    intro c
    obtain ⟨v, hv⟩ := ((hne.diff I.finite_toSet).diff (HeightOneSpectrum.Support.finite (𝓞 F) c)).nonempty
    exact ⟨v, hv.1.1, hv.1.2, hv.2⟩
  have h0 : ∃ c : F, c ≠ 0 ∧ c ∈ lamPsi ψ := by
    obtain ⟨v, hvX, hvI, -⟩ := hne' 1
    obtain ⟨a, ha1, ha⟩ := key v hvX hvI
    refine ⟨a, ?_, ha⟩
    rintro rfl
    simp at ha1
  have hb : ∀ c : F, c ≠ 0 → ¬ ∀ a ∈ lamPsi ψ, ∃ r : 𝓞 F, a = c * r := by
    intro c _ hall
    obtain ⟨v, hvX, hvI, hvc⟩ := hne' c
    obtain ⟨a, ha1, ha⟩ := key v hvX hvI
    obtain ⟨r, rfl⟩ := hall a ha
    simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hvc
    have hc : Valued.v (algebraMap F (Fv F v) c) ≤ 1 := by
      have e : Valued.v ((c : v.adicCompletion F)) = v.valuation F c :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v c
      exact (e ▸ hvc : Valued.v ((c : v.adicCompletion F)) ≤ 1)
    have hr : Valued.v (algebraMap F (Fv F v) (r : F)) ≤ 1 := by
      have e : Valued.v (((r : F) : v.adicCompletion F)) = v.valuation F (r : F) :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (r : F)
      exact (e ▸ v.valuation_le_one r : Valued.v (((r : F) : v.adicCompletion F)) ≤ 1)
    rw [map_mul, map_mul] at ha1
    have : Valued.v (algebraMap F (Fv F v) c) * Valued.v (algebraMap F (Fv F v) (r : F)) ≤ 1 :=
      mul_le_one' hc hr
    exact absurd ha1 (not_lt.2 this)
  have hχc : Continuous (chiInf ψ) := hψ.1.comp (continuous_id.prodMk continuous_const)
  have hΛ : ∀ a ∈ lamPsi ψ, chiInf ψ (algebraMap F (InfiniteAdeleRing F) a) = 1 := by
    intro a ha
    apply psi_fin_of_char ψ hψ a
    have := ha 1
    simpa using this
  have hall := hC F (lamPsi ψ) h0 hb (chiInf ψ) hχc hΛ
  obtain ⟨x, hx⟩ := hψ.2.2.2
  apply hx
  obtain ⟨a, ha⟩ := hS F (U0 I n) (isOpen_adelic_neighbourhood I n) x.2
  have e : x = algebraMap F (AF F) a + pairA F (x.1 - algebraMap F (Ainf F) a) 0 +
      pairA F 0 (x.2 - algebraMap F (Af F) a) := by
    rw [algebraMap_AF]
    refine Prod.ext ?_ ?_
    · show x.1 = algebraMap F (Ainf F) a + 0 + (x.1 - algebraMap F (Ainf F) a) + 0
      abel
    · show x.2 = 0 + algebraMap F (Af F) a + 0 + (x.2 - algebraMap F (Af F) a)
      abel
  rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψ.2.2.1 a, hU _ ha, one_mul, mul_one]
  exact hall _

end VolAAW

end PI.VolStabSW

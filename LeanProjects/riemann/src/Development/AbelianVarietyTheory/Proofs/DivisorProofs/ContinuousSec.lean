import Mathlib

open MeasureTheory Measure Topology
open scoped Pointwise

noncomputable section
namespace GlobalTheory.SectionProjectionFormula

variable {ι : Type} [Fintype ι] {A : Type} {B : ι → Type} {G : Type}
  [Group G] [Group A] [∀ i, Group (B i)]

def secB (jB : (i : ι) → B i → G) (b : (i : ι) → B i) : G :=
  ((Finset.univ : Finset ι).toList.map (fun i => jB i (b i))).prod

def sec (jA : A → G) (jB : (i : ι) → B i → G) (y : A × ((i : ι) → B i)) : G :=
  jA y.1 * secB jB y.2

def proj (πA : G →* A) (πB : (i : ι) → G →* B i) : G →* A × ((i : ι) → B i) :=
  πA.prod (Pi.monoidHom πB)

lemma proj_apply (πA : G →* A) (πB : (i : ι) → G →* B i) (x : G) :
    proj πA πB x = (πA x, fun i => πB i x) := rfl

lemma list_inv {X : Type} (l : List X) (φ : X → G) (R : G → ℂ)
    (h : ∀ a x, R (φ a * x) = R x) (x : G) : R ((l.map φ).prod * x) = R x := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.prod_cons, mul_assoc, h, ih]

lemma list_ite {X M : Type} [Monoid M] [DecidableEq X] (l : List X) (hl : l.Nodup) (j : X) (c : M) :
    (l.map (fun i => if i = j then c else 1)).prod = if j ∈ l then c else 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, ih hl.2]
    by_cases ha : a = j
    · subst ha; simp [hl.1]
    · simp [ha, Ne.symm ha]

lemma R_sec (jA : A → G) (jB : (i : ι) → B i → G) (R : G → ℂ)
    (hRA : ∀ (a : A) (x : G), R (jA a * x) = R x)
    (hRB : ∀ (i : ι) (b : B i) (x : G), R (jB i b * x) = R x)
    (y : A × ((i : ι) → B i)) (x : G) : R (sec jA jB y * x) = R x := by
  unfold sec secB
  rw [mul_assoc, hRA]
  exact list_inv _ (fun i => jB i (y.2 i)) R (fun a x => hRB a _ x) x

lemma proj_sec (πA : G →* A) (πB : (i : ι) → G →* B i) (jA : A → G) (jB : (i : ι) → B i → G)
    (h1 : ∀ (a : A), πA (jA a) = a) (h2 : ∀ (i : ι) (b : B i), πA (jB i b) = (1 : A))
    (h3 : ∀ (i : ι) (a : A), πB i (jA a) = (1 : B i))
    (h4 : ∀ (i : ι) (b : B i), πB i (jB i b) = b)
    (h5 : ∀ (i i' : ι) (b : B i'), i' ≠ i → πB i (jB i' b) = (1 : B i))
    (y : A × ((i : ι) → B i)) : proj πA πB (sec jA jB y) = y := by
  classical
  rw [proj_apply]
  unfold sec secB
  ext
  · simp only [map_mul, h1, MonoidHom.map_list_prod, List.map_map]
    rw [List.prod_eq_one, mul_one]
    intro z hz
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
    exact h2 i _
  · rename_i j
    simp only [map_mul, h3, MonoidHom.map_list_prod, List.map_map, one_mul]
    have : ((Finset.univ : Finset ι).toList.map ((πB j) ∘ fun i => jB i (y.2 i))) =
        (Finset.univ : Finset ι).toList.map (fun i => if i = j then y.2 j else 1) := by
      apply List.map_congr_left
      intro i _
      by_cases hij : i = j
      · subst hij; simp [h4]
      · simp [hij, h5 j i _ hij]
    rw [this, list_ite _ (Finset.nodup_toList _)]
    simp

lemma continuous_sec [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace A]
    [∀ i, TopologicalSpace (B i)] (jA : A → G) (jB : (i : ι) → B i → G) (hA : Continuous jA)
    (hB : ∀ i, Continuous (jB i)) : Continuous (sec jA jB) := by
  unfold sec secB
  exact (hA.comp continuous_fst).mul (continuous_list_prod _ fun i _ =>
    (hB i).comp ((continuous_apply i).comp continuous_snd))

theorem finiteRing_sq_sub_mul_sq_eq_of_card {G A ι : Type} [Fintype ι] {B : ι → Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
    [BorelSpace A] [(i : ι) → Group (B i)] [(i : ι) → TopologicalSpace (B i)]
    [∀ (i : ι), IsTopologicalGroup (B i)] [∀ (i : ι), LocallyCompactSpace (B i)]
    [∀ (i : ι), SecondCountableTopology (B i)] [∀ (i : ι), T2Space (B i)]
    [(i : ι) → MeasurableSpace (B i)] [∀ (i : ι), BorelSpace (B i)]
    (μ : Measure G) [IsHaarMeasure μ] (μA : Measure A) [IsHaarMeasure μA]
    (μB : (i : ι) → Measure (B i)) [∀ (i : ι), IsHaarMeasure (μB i)]
    (πA : G →* A) (hπA : Continuous (⇑πA : G → A)) (πB : (i : ι) → G →* B i)
    (hπB : ∀ (i : ι), Continuous (⇑(πB i) : G → B i))
    (jA : A → G) (hjA : Continuous jA) (jB : (i : ι) → B i → G) (hjB : ∀ (i : ι), Continuous (jB i))
    (h1 : ∀ (a : A), (πA : G → A) (jA a) = a)
    (h2 : ∀ (i : ι) (b : B i), (πA : G → A) (jB i b) = (1 : A))
    (h3 : ∀ (i : ι) (a : A), (πB i : G → B i) (jA a) = (1 : B i))
    (h4 : ∀ (i : ι) (b : B i), (πB i : G → B i) (jB i b) = b)
    (h5 : ∀ (i i' : ι) (b : B i'), i' ≠ i → (πB i : G → B i) (jB i' b) = (1 : B i))
    (R : G → ℂ) (hRA : ∀ (a : A) (x : G), R (jA a * x) = R x)
    (hRB : ∀ (i : ι) (b : B i) (x : G), R (jB i b * x) = R x) :
    ∃ (c : ℂ), ∀ (f : A → ℂ) (g : (i : ι) → B i → ℂ),
      ∫ (x : G), (f ((πA : G → A) x) * ∏ i : ι, g i ((πB i : G → B i) x)) * R x ∂μ =
        c * ((∫ (a : A), f a ∂μA) * ∏ i : ι, ∫ (b : B i), g i b ∂μB i) := by
  classical
  let p : G →* A × ((i : ι) → B i) := proj πA πB
  have hp : Continuous p := hπA.prodMk (continuous_pi hπB)
  let N : Subgroup G := p.ker
  have hNc : IsClosed (N : Set G) := by
    rw [MonoidHom.coe_ker]; exact isClosed_singleton.preimage hp
  haveI : LocallyCompactSpace N := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨ν, hν⟩ : ∃ ν : Measure N, ν = Measure.haar := ⟨_, rfl⟩
  haveI : IsHaarMeasure ν := hν ▸ inferInstance
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
  haveI : SigmaCompactSpace N := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite ν := IsHaarMeasure.sigmaFinite ν
  let lam : Measure (A × ((i : ι) → B i)) := μA.prod (Measure.pi μB)
  haveI : IsHaarMeasure lam := (inferInstance : IsHaarMeasure (μA.prod (Measure.pi μB)))
  haveI : SigmaFinite lam := (inferInstance : SigmaFinite (μA.prod (Measure.pi μB)))
  let s := sec jA jB
  have hs : Continuous s := continuous_sec jA jB hjA hjB
  have hps : ∀ y, p (s y) = y := proj_sec πA πB jA jB h1 h2 h3 h4 h5
  have hpN : ∀ n : N, p n = 1 := fun n => n.2
  let U : (A × ((i : ι) → B i)) × N → G := fun z => s z.1 * (z.2 : G)
  have hUc : Continuous U := (hs.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hpU : ∀ z, p (U z) = z.1 := by
    intro z; simp only [U, map_mul, hps, hpN, mul_one]
  have memV : ∀ x : G, (s (p x))⁻¹ * x ∈ N := by
    intro x; rw [MonoidHom.mem_ker, map_mul, map_inv, hps, inv_mul_cancel]
  let V : G → (A × ((i : ι) → B i)) × N := fun x => (p x, ⟨(s (p x))⁻¹ * x, memV x⟩)
  have hVc : Continuous V :=
    hp.prodMk (((hs.comp hp).inv.mul continuous_id).subtype_mk _)
  have hUemb : MeasurableEmbedding U := by
    refine MeasurableEmbedding.of_measurable_inverse hUc.measurable ?_ hVc.measurable ?_
    · have : Set.range U = Set.univ := by
        refine Set.eq_univ_of_forall fun x => ⟨V x, ?_⟩
        simp only [U, V, mul_inv_cancel_left]
      rw [this]; exact MeasurableSet.univ
    · rintro ⟨y, n⟩
      have e1 : p (U (y, n)) = y := hpU _
      refine Prod.ext e1 (Subtype.ext ?_)
      show (s (p (U (y, n))))⁻¹ * U (y, n) = (n : G)
      rw [e1]; simp only [U, inv_mul_cancel_left]
  let m := lam.prod ν
  let μt := m.map U
  haveI : IsMulLeftInvariant μt := by
    refine ⟨fun g => ?_⟩
    have memγ : ∀ y, (s (p g * y))⁻¹ * g * s y ∈ N := by
      intro y; rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hps, hps]; group
    let γ : (A × ((i : ι) → B i)) → N := fun y => ⟨(s (p g * y))⁻¹ * g * s y, memγ y⟩
    have hγ : Continuous γ :=
      (((hs.comp (continuous_const.mul continuous_id)).inv.mul continuous_const).mul hs).subtype_mk _
    have hΦ : MeasurePreserving (fun z : (A × ((i : ι) → B i)) × N => (p g * z.1, γ z.1 * z.2)) m m :=
      MeasurePreserving.skew_product (measurePreserving_mul_left lam (p g))
        (show Measurable (Function.uncurry fun y (n : N) => γ y * n) from
          ((hγ.comp continuous_fst).mul continuous_snd).measurable)
        (Filter.Eventually.of_forall fun y => map_mul_left_eq_self ν (γ y))
    have hcomp : (fun x => g * x) ∘ U =
        U ∘ (fun z : (A × ((i : ι) → B i)) × N => (p g * z.1, γ z.1 * z.2)) := by
      funext z; simp only [Function.comp, U, γ, Subgroup.coe_mul, mul_assoc, mul_inv_cancel_left]
    show Measure.map (fun x => g * x) (Measure.map U m) = Measure.map U m
    rw [Measure.map_map (measurable_const_mul g) hUc.measurable, hcomp,
      ← Measure.map_map hUc.measurable hΦ.measurable, hΦ.map_eq]
  haveI : IsFiniteMeasureOnCompacts μt := by
    refine ⟨fun K hK => ?_⟩
    show Measure.map U m K < ⊤
    rw [Measure.map_apply hUc.measurable hK.isClosed.measurableSet]
    have hK1 : IsCompact (p '' K) := hK.image hp
    have hK2' : IsCompact ((s '' (p '' K))⁻¹ * K) := (hK1.image hs).inv.mul hK
    have hK2 : IsCompact (Subtype.val ⁻¹' ((s '' (p '' K))⁻¹ * K) : Set N) :=
      hNc.isClosedEmbedding_subtypeVal.isCompact_preimage hK2'
    have hsub : U ⁻¹' K ⊆ (p '' K) ×ˢ (Subtype.val ⁻¹' ((s '' (p '' K))⁻¹ * K) : Set N) := by
      rintro ⟨y, n⟩ hz
      simp only [Set.mem_preimage] at hz
      have hy : y ∈ p '' K := ⟨U (y, n), hz, hpU _⟩
      refine ⟨hy, ?_⟩
      show (n : G) ∈ (s '' (p '' K))⁻¹ * K
      refine ⟨(s y)⁻¹, ?_, U (y, n), hz, ?_⟩
      · rw [Set.mem_inv, inv_inv]; exact ⟨y, hy, rfl⟩
      · simp only [U, inv_mul_cancel_left]
    calc m (U ⁻¹' K) ≤ m ((p '' K) ×ˢ (Subtype.val ⁻¹' ((s '' (p '' K))⁻¹ * K) : Set N)) :=
          measure_mono hsub
      _ = lam (p '' K) * ν (Subtype.val ⁻¹' ((s '' (p '' K))⁻¹ * K) : Set N) := Measure.prod_prod _ _
      _ < ⊤ := ENNReal.mul_lt_top hK1.measure_lt_top hK2.measure_lt_top
  have hk : μt = haarScalarFactor μt μ • μ := isMulLeftInvariant_eq_smul μt μ
  set k := haarScalarFactor μt μ with hkdef
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hk
    have h' : μt Set.univ = 0 := by rw [hk]; rfl
    have h'' : m Set.univ = 0 := by
      rw [← Set.preimage_univ (f := U), ← Measure.map_apply hUc.measurable MeasurableSet.univ]
      exact h'
    rw [← Set.univ_prod_univ, Measure.prod_prod] at h''
    rcases mul_eq_zero.1 h'' with h | h
    · exact (isOpen_univ.measure_ne_zero lam ⟨1, Set.mem_univ _⟩) h
    · exact (isOpen_univ.measure_ne_zero ν ⟨1, Set.mem_univ _⟩) h
  have hkc : ((k : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, NNReal.coe_eq_zero]; exact hk0
  refine ⟨((k : ℝ) : ℂ)⁻¹ * ∫ n, R (n : G) ∂ν, fun f g => ?_⟩
  set H : G → ℂ := fun x => (f (πA x) * ∏ i : ι, g i (πB i x)) * R x with hH
  have hint : ∫ x, H x ∂μt = ((k : ℝ) : ℂ) * ∫ x, H x ∂μ := by
    rw [hk, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hHU : (fun z => H (U z)) = fun z : (A × ((i : ι) → B i)) × N =>
      (fun y : A × ((i : ι) → B i) => f y.1 * ∏ i, g i (y.2 i)) z.1 * (fun n : N => R n) z.2 := by
    funext z
    have ha : πA (U z) = z.1.1 := congrArg Prod.fst (hpU z)
    have hb : ∀ i, πB i (U z) = z.1.2 i := fun i => congrFun (congrArg Prod.snd (hpU z)) i
    simp only [H, ha, hb]
    congr 1
    exact R_sec jA jB R hRA hRB z.1 z.2
  have hmain : ∫ x, H x ∂μt = ((∫ (a : A), f a ∂μA) * ∏ i : ι, ∫ (b : B i), g i b ∂μB i) *
      ∫ n, R (n : G) ∂ν := by
    show ∫ x, H x ∂(Measure.map U ((μA.prod (Measure.pi μB)).prod ν)) = _
    rw [hUemb.integral_map, hHU]
    rw [integral_prod_mul (μ := μA.prod (Measure.pi μB)) (ν := ν)
      (fun y : A × ((i : ι) → B i) => f y.1 * ∏ i, g i (y.2 i)) (fun n : N => R n)]
    rw [integral_prod_mul (μ := μA) (ν := Measure.pi μB) (fun a => f a)
      (fun b : (i : ι) → B i => ∏ i, g i (b i)), integral_fintype_prod_eq_prod]
  have : ∫ x, H x ∂μ = ((k : ℝ) : ℂ)⁻¹ * ∫ x, H x ∂μt := by
    rw [hint, ← mul_assoc, inv_mul_cancel₀ hkc, one_mul]
  rw [this, hmain]
  ring

theorem main : ∀ {G A ι : Type} [inst : Fintype ι] {B : ι → Type} [inst_1 : Group G] [inst_2 : TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [inst_7 : MeasurableSpace G] [BorelSpace G] [inst_9 : Group A] [inst_10 : TopologicalSpace A] [IsTopologicalGroup A] [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [inst_15 : MeasurableSpace A] [BorelSpace A] [inst_17 : (i : ι) → Group (B i)] [inst_18 : (i : ι) → TopologicalSpace (B i)] [∀ (i : ι), IsTopologicalGroup (B i)] [∀ (i : ι), LocallyCompactSpace (B i)] [∀ (i : ι), SecondCountableTopology (B i)] [∀ (i : ι), T2Space (B i)] [inst_23 : (i : ι) → MeasurableSpace (B i)] [∀ (i : ι), BorelSpace (B i)] (μ : MeasureTheory.Measure G) [MeasureTheory.Measure.IsHaarMeasure μ] (μA : MeasureTheory.Measure A) [MeasureTheory.Measure.IsHaarMeasure μA] (μB : (i : ι) → MeasureTheory.Measure (B i)) [∀ (i : ι), MeasureTheory.Measure.IsHaarMeasure (μB i)] (πA : G →* A), Continuous (⇑πA : G → A) → ∀ (πB : (i : ι) → G →* B i), (∀ (i : ι), Continuous (⇑(πB i) : G → B i)) → ∀ (jA : A → G), Continuous jA → ∀ (jB : (i : ι) → B i → G), (∀ (i : ι), Continuous (jB i)) → (∀ (a : A), (πA : G → A) (jA a) = a) → (∀ (i : ι) (b : B i), (πA : G → A) (jB i b) = (1 : A)) → (∀ (i : ι) (a : A), (πB i : G → B i) (jA a) = (1 : B i)) → (∀ (i : ι) (b : B i), (πB i : G → B i) (jB i b) = b) → (∀ (i i' : ι) (b : B i'), i' ≠ i → (πB i : G → B i) (jB i' b) = (1 : B i)) → ∀ (R : G → ℂ), (∀ (a : A) (x : G), R (jA a * x) = R x) → (∀ (i : ι) (b : B i) (x : G), R (jB i b * x) = R x) → ∃ (c : ℂ), ∀ (f : A → ℂ) (g : (i : ι) → B i → ℂ), ∫ (x : G), (f ((πA : G → A) x) * ∏ i : ι, g i ((πB i : G → B i) x)) * R x ∂μ = c * ((∫ (a : A), f a ∂μA) * ∏ i : ι, ∫ (b : B i), g i b ∂μB i) := @finiteRing_sq_sub_mul_sq_eq_of_card

end GlobalTheory.SectionProjectionFormula
end

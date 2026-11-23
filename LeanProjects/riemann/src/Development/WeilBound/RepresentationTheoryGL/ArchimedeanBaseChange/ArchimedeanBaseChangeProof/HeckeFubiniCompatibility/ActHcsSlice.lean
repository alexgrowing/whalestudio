import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PActPi
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PActLoc
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PActEq

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open PositivityTheory.RgBcC.Bridge (along)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

section Side
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  {Ma : Mods E a} {Mb : Mods E b} {κ : Type} [Fintype κ]

theorem actSide_b (hMA : MultAlg) (μb : Measure (G b)) [μb.IsHaarMeasure] (f : Io Ma Mb κ → H E a b → ℂ)
    (kb' : Kers Mb) vb' (T' : ℝ) (hkb' : IsMults μb kb' vb' T') (χb : InfinitePlace E → Inf b)
    (hf : ∀ i, Continuous (f i)) (hsm : ∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x))
    (heq : ∀ v (u : Matrix.unitaryGroup (Fin b) ℂ) I x, f I (x * (1, infP b (Pi.mulSingle v (Unitary.toUnits u)))) =
      ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l * f ((I.1.1, Function.update I.1.2 v l), I.2) x)
    (heig : ∀ i v g m₁, IsEig (χb v) (along v g fun x => f i (m₁, x)))
    (j₁ : IxA Ma) (i₂ : IxA Mb) (z : κ) (x : H E a b) :
    ∫ yb, ∑ J, (∏ v, ent (Mb v) (kb' v (yb v).val) (i₂ v) (J v)) * f ((j₁, J), z) (x * (1, infP b yb))
      ∂(Measure.pi fun _ => μb) = valA vb' χb * f ((j₁, i₂), z) x := by
  have h1 : infP (E := E) b 1 = 1 := by simp [infP]
  have key := pi_iter μb (fun v => Ix (Mb v)) (fun v t p q => ent (Mb v) (kb' v t.val) p q) (fun v => vb' v (χb v))
    (fun J yb => f ((j₁, J), z) (x * (1, infP b yb))) i₂ (fun v p q => mult_ent (hkb' v) p q)
    (fun J => (hf _).comp (continuous_const.mul (continuous_const.prodMk (continuous_infP b)))) ?_
  · simp only [h1, Prod.mk_one_one, mul_one] at key
    exact key
  intro v J y
  set m₁ := (x * (1, infP b (Function.update y v 1))).1
  set g₀ := (x * (1, infP b (Function.update y v 1))).2
  have hsplit : ∀ t : G b, x * (1, infP b (Function.update y v t)) = (m₁, g₀ * infP b (Pi.mulSingle v t)) := by
    intro t
    have e : Function.update y v t = Function.update y v 1 * Pi.mulSingle v t := by
      funext w
      by_cases h : w = v
      · subst h; simp
      · simp [Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]
    rw [e, infinitePart_mul]
    exact Prod.ext (by simp [m₁]) (by simp [g₀, mul_assoc])
  simp only [hsplit, Pi.mulSingle_one, h1, mul_one]
  have := loc_act hMA μb (Mb v) (kb' v) (vb' v) T' (hkb' v) (χb v) v
    (fun j g => f ((j₁, Function.update J v j), z) (m₁, g)) ?_ ?_ ?_ g₀ (J v)
  · simpa only [Function.update_eq_self] using this
  · intro j
    obtain ⟨φ, hφ⟩ := hsm ((j₁, Function.update J v j), z) m₁
    rw [← hφ]; exact φ.2
  · intro h u l
    have := heq v u ((j₁, Function.update J v l), z) (m₁, h)
    simpa only [Prod.mk_mul_mk, mul_one, Function.update_self, Function.update_idem] using this
  · intro j g
    exact heig ((j₁, Function.update J v j), z) v g m₁

end Side

section SideA
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
  [MeasurableSpace (G a)] [BorelSpace (G a)]
  {Ma : Mods E a} {Mb : Mods E b} {κ : Type}

theorem actSide_a (hMA : MultAlg) (μa : Measure (G a)) [μa.IsHaarMeasure] (f : Io Ma Mb κ → H E a b → ℂ)
    (ka' : Kers Ma) va' (T' : ℝ) (hka' : IsMults μa ka' va' T') (χa : InfinitePlace E → Inf a)
    (hf : ∀ i, Continuous (f i)) (hsm : ∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂))
    (heq : ∀ v (u : Matrix.unitaryGroup (Fin a) ℂ) I x, f I (x * (infP a (Pi.mulSingle v (Unitary.toUnits u)), 1)) =
      ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l * f ((Function.update I.1.1 v l, I.1.2), I.2) x)
    (heig : ∀ i v g m₂, IsEig (χa v) (along v g fun x => f i (x, m₂)))
    (i₁ : IxA Ma) (i₂ : IxA Mb) (z : κ) (x : H E a b) :
    ∫ ya, ∑ J, (∏ v, ent (Ma v) (ka' v (ya v).val) (i₁ v) (J v)) * f ((J, i₂), z) (x * (infP a ya, 1))
      ∂(Measure.pi fun _ => μa) = valA va' χa * f ((i₁, i₂), z) x := by
  have h1 : infP (E := E) a 1 = 1 := by simp [infP]
  have key := pi_iter μa (fun v => Ix (Ma v)) (fun v t p q => ent (Ma v) (ka' v t.val) p q) (fun v => va' v (χa v))
    (fun J ya => f ((J, i₂), z) (x * (infP a ya, 1))) i₁ (fun v p q => mult_ent (hka' v) p q)
    (fun J => (hf _).comp (continuous_const.mul ((continuous_infP a).prodMk continuous_const))) ?_
  · simp only [h1, Prod.mk_one_one, mul_one] at key
    exact key
  intro v J y
  set g₀ := (x * (infP a (Function.update y v 1), 1)).1
  set m₂ := (x * (infP a (Function.update y v 1), 1)).2
  have hsplit : ∀ t : G a, x * (infP a (Function.update y v t), 1) = (g₀ * infP a (Pi.mulSingle v t), m₂) := by
    intro t
    have e : Function.update y v t = Function.update y v 1 * Pi.mulSingle v t := by
      funext w
      by_cases h : w = v
      · subst h; simp
      · simp [Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]
    rw [e, infinitePart_mul]
    exact Prod.ext (by simp [g₀, mul_assoc]) (by simp [m₂])
  simp only [hsplit, Pi.mulSingle_one, h1, mul_one]
  have := loc_act hMA μa (Ma v) (ka' v) (va' v) T' (hka' v) (χa v) v
    (fun j g => f ((Function.update J v j, i₂), z) (g, m₂)) ?_ ?_ ?_ g₀ (J v)
  · simpa only [Function.update_eq_self] using this
  · intro j
    obtain ⟨φ, hφ⟩ := hsm ((Function.update J v j, i₂), z) m₂
    rw [← hφ]; exact φ.2
  · intro h u l
    have := heq v u ((Function.update J v l, i₂), z) (h, m₂)
    simpa only [Prod.mk_mul_mk, mul_one, Function.update_self, Function.update_idem] using this
  · intro j g
    exact heig ((Function.update J v j, i₂), z) v g m₂

end SideA

section Lin

theorem actLin2 {Y Z J : Type} [Fintype Z] [Fintype J] [MeasurableSpace Y] (μ : Measure Y) (c : Z → ℂ) (d : J → ℂ)
    (g : Z → J → Y → ℂ) (hg : ∀ z j, Integrable (g z j) μ) :
    ∫ y, ∑ z, c z * ∑ j, d j * g z j y ∂μ = ∑ z, c z * ∑ j, d j * ∫ y, g z j y ∂μ := by
  rw [integral_finsetSum _ fun z _ => (integrable_finsetSum _ fun j _ => (hg z j).const_mul _).const_mul _]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun j _ => (hg z j).const_mul _]
  congr 1
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

theorem actHcsSlice {P Q : Type} [TopologicalSpace P] [T2Space P] [TopologicalSpace Q] {F : P × Q → ℂ}
    (hF : HasCompactSupport F) (q : Q) : HasCompactSupport fun p => F (p, q) := by
  refine HasCompactSupport.intro (hF.image continuous_fst) fun p hp => ?_
  by_contra h
  exact hp ⟨(p, q), subset_tsupport _ h, rfl⟩

end Lin

section Main

theorem actVal (hMA : MultAlg) (hCF : CompatFub) (hTT : TensTest) : ActVal := by
  intro E _ _ _ a b D _ _ _ _ _ _ μa _ μb _ ν _ Ma Mb κ _ ka ka' kb kb' va va' vb vb' T T' ψ ψ' f χa χb hC hka hkb hψ
    hR hsm hEig hka' hkb' hψ'
  haveI : BorelSpace (H E a b) := ⟨rfl⟩
  haveI : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
  haveI : IsFiniteMeasureOnCompacts D.μ := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  have hf : ∀ i, Continuous (f i) := hR.1
  have hTm := (hTT E a b μa μb Ma Mb κ ka' kb' va' vb' T' ψ' hka' hkb' hψ').1
  have heqa := fun v u I x => equiv_a D hka hkb hψ hR v u I x
  have heqb := fun v u I x => equiv_b D hka hkb hψ hR v u I x
  funext i x
  simp only [PositivityTheory.Rg.BcB.E.conv, convF, Pi.smul_apply, smul_eq_mul]
  set F : H E a b → ℂ := fun g => ∑ j, tens ka' kb' ψ' i j g * f j (x * g) with hFdef
  have hterm : ∀ j, Continuous (fun g => tens ka' kb' ψ' i j g * f j (x * g)) ∧
      HasCompactSupport (fun g => tens ka' kb' ψ' i j g * f j (x * g)) := fun j =>
    ⟨(hTm i j).1.mul ((hf j).comp (continuous_const.mul continuous_id)), (hTm i j).2.mul_right⟩
  have hFc : Continuous F := continuous_finsetSum _ fun j _ => (hterm j).1
  have hFs : HasCompactSupport F := by
    have e : F = ∑ j, fun g => tens ka' kb' ψ' i j g * f j (x * g) := by
      funext g; simp [hFdef, Finset.sum_apply]
    rw [e]
    exact Finset.sum_induction _ HasCompactSupport (fun _ _ h h' => h.add h') HasCompactSupport.zero
      fun j _ => (hterm j).2
  rw [← integral_finsetSum _ fun j _ => (hterm j).1.integrable_of_hasCompactSupport (hterm j).2]
  change ∫ g, F g ∂D.μ = _
  rw [hCF E a b D μa μb ν hC F hFc hFs]
  change ∫ ya, ∫ yb, ∫ h, F (splitH a b (ya, yb, h)) ∂ν ∂_ ∂_ = _

  set K : Set (Hf E a b) := ⋃ p, ⋃ q, tsupport (ψ' p q) with hKdef
  have hK : IsCompact K := isCompact_iUnion fun p => isCompact_iUnion fun q => (hψ' p q).2
  have hψK : ∀ p q h, h ∉ K → ψ' p q h = 0 := fun p q h hh =>
    image_eq_zero_of_notMem_tsupport fun hm => hh (Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨q, hm⟩⟩)
  have hQK : ∀ ya yb h, h ∉ K → F (splitH a b (ya, yb, h)) = 0 := by
    intro ya yb h hh
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [tens, hFin_splitH, hψK _ _ _ hh, mul_zero, zero_mul]
  set ν' := ν.restrict K
  haveI : IsFiniteMeasure ν' := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hres : ∀ ya yb, ∫ h, F (splitH a b (ya, yb, h)) ∂ν = ∫ h, F (splitH a b (ya, yb, h)) ∂ν' :=
    fun ya yb => (setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => hQK ya yb h hh).symm
  simp_rw [hres]
  let A := Measure.pi fun _ : InfinitePlace E => μa
  let B := Measure.pi fun _ : InfinitePlace E => μb
  haveI : SigmaFinite A := inferInstanceAs (SigmaFinite (Measure.pi fun _ : InfinitePlace E => μa))
  haveI : SigmaFinite B := inferInstanceAs (SigmaFinite (Measure.pi fun _ : InfinitePlace E => μb))
  haveI : IsFiniteMeasureOnCompacts A :=
    inferInstanceAs (IsFiniteMeasureOnCompacts (Measure.pi fun _ : InfinitePlace E => μa))
  haveI : IsFiniteMeasureOnCompacts B :=
    inferInstanceAs (IsFiniteMeasureOnCompacts (Measure.pi fun _ : InfinitePlace E => μb))
  set Q : ((InfinitePlace E → G a) × (InfinitePlace E → G b)) × Hf E a b → ℂ :=
    fun q => F (splitH a b (q.1.1, q.1.2, q.2)) with hQdef
  have hQc : Continuous Q := hFc.comp ((splitH a b).continuous.comp (by fun_prop))
  have hQs : HasCompactSupport Q :=
    hFs.comp_homeomorph ((Homeomorph.prodAssoc _ _ _).trans (splitH a b).toHomeomorph)
  have hQi : Integrable Q ((A.prod B).prod ν') := hQc.integrable_of_hasCompactSupport hQs
  have hQh : ∀ h, Integrable (fun p => Q (p, h)) (A.prod B) := fun h =>
    (hQc.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport (actHcsSlice hQs h)
  have step1 : ∫ ya, ∫ yb, ∫ h, F (splitH a b (ya, yb, h)) ∂ν' ∂B ∂A =
      ∫ h, ∫ ya, ∫ yb, Q ((ya, yb), h) ∂B ∂A ∂ν' := by
    rw [← integral_prod (fun p => ∫ h, Q (p, h) ∂ν') hQi.integral_prod_left,
      integral_integral_swap (f := fun p h => Q (p, h)) hQi]
    exact integral_congr_ae (Filter.Eventually.of_forall fun h => integral_prod _ (hQh h))
  rw [step1]
  have hpt : ∀ (h : Hf E a b) ya yb, x * splitH a b (ya, yb, h) = x * finH h * (infP a ya, 1) * (1, infP b yb) := by
    intro h ya yb
    have hc : ∀ (n : ℕ) (y : InfinitePlace E → G n) (k : GL (Fin n) (Af E)), infP n y * finGL E n k = finGL E n k * infP n y :=
      fun n y k => infGL_comm _ _
    rw [splitH_apply]
    exact Prod.ext (by simp [finH, hc, mul_assoc]) (by simp [finH, hc, mul_assoc])
  have hX : ∀ (X₀ : H E a b) z (j₁ : IxA Ma), ∀ J, Continuous fun yb : InfinitePlace E → G b => f ((j₁, J), z) (X₀ * (1, infP b yb)) :=
    fun X₀ z j₁ J => (hf _).comp (continuous_const.mul (continuous_const.prodMk (continuous_infP b)))
  have hXa : ∀ (X₀ : H E a b) z (j₂ : IxA Mb), ∀ J, Continuous fun ya : InfinitePlace E → G a => f ((J, j₂), z) (X₀ * (infP a ya, 1)) :=
    fun X₀ z j₂ J => (hf _).comp (continuous_const.mul ((continuous_infP a).prodMk continuous_const))
  have per_h : ∀ h, ∫ ya, ∫ yb, Q ((ya, yb), h) ∂B ∂A =
      (valA va' χa * valA vb' χb) * ∑ z, ψ' i.2 z h * f (i.1, z) (x * finH h) := by
    intro h
    have hQexp : ∀ ya yb, Q ((ya, yb), h) = ∑ z, ψ' i.2 z h * ∑ j₁,
        (∏ v, ent (Ma v) (ka' v (ya v).val) (i.1.1 v) (j₁ v)) * ∑ j₂,
          (∏ v, ent (Mb v) (kb' v (yb v).val) (i.1.2 v) (j₂ v)) *
            f ((j₁, j₂), z) (x * finH h * (infP a ya, 1) * (1, infP b yb)) := by
      intro ya yb
      simp only [hQdef, hFdef, tens, entA, gInf_splitH₁, gInf_splitH₂, hFin_splitH, hpt, Fintype.sum_prod_type,
        Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j₁ _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun j₂ _ => by ring
    have inner : ∀ ya, ∫ yb, Q ((ya, yb), h) ∂B = ∑ z, ψ' i.2 z h * (valA vb' χb * ∑ j₁,
        (∏ v, ent (Ma v) (ka' v (ya v).val) (i.1.1 v) (j₁ v)) * f ((j₁, i.1.2), z) (x * finH h * (infP a ya, 1))) := by
      intro ya
      rw [integral_congr_ae (Filter.Eventually.of_forall (hQexp ya))]
      refine (actLin2 B (fun z => ψ' i.2 z h) (fun j₁ => ∏ v, ent (Ma v) (ka' v (ya v).val) (i.1.1 v) (j₁ v))
        (fun z j₁ yb => ∑ j₂, (∏ v, ent (Mb v) (kb' v (yb v).val) (i.1.2 v) (j₂ v)) *
            f ((j₁, j₂), z) (x * finH h * (infP a ya, 1) * (1, infP b yb)))
        (fun z j₁ => pi_integrable μb (fun v t p q => ent (Mb v) (kb' v t.val) p q)
          (fun J yb => f ((j₁, J), z) (x * finH h * (infP a ya, 1) * (1, infP b yb))) i.1.2
          (fun v p q => mult_ent (hkb' v) p q) (hX _ z j₁))).trans ?_
      refine Finset.sum_congr rfl fun z _ => ?_
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j₁ _ => ?_
      rw [actSide_b hMA μb f kb' vb' T' hkb' χb hf hsm.2 heqb hEig.2 j₁ i.1.2 z (x * finH h * (infP a ya, 1))]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall inner),
      integral_finsetSum _ fun z _ => ((pi_integrable μa (fun v t p q => ent (Ma v) (ka' v t.val) p q)
        (fun J ya => f ((J, i.1.2), z) (x * finH h * (infP a ya, 1))) i.1.1
        (fun v p q => mult_ent (hka' v) p q) (hXa _ z i.1.2)).const_mul _).const_mul _]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [integral_const_mul, integral_const_mul,
      actSide_a hMA μa f ka' va' T' hka' χa hf hsm.1 heqa hEig.1 i.1.1 i.1.2 z (x * finH h)]
    simp only [Prod.mk.eta]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall per_h), integral_const_mul]
  have hcf : Continuous fun h : Hf E a b => finH h :=
    ((continuous_finGL' a).comp continuous_fst).prodMk ((continuous_finGL' b).comp continuous_snd)
  have hzi : ∀ z, Continuous (fun h => ψ' i.2 z h * f (i.1, z) (x * finH h)) ∧
      HasCompactSupport (fun h => ψ' i.2 z h * f (i.1, z) (x * finH h)) := fun z =>
    ⟨(hψ' _ _).1.mul ((hf _).comp (continuous_const.mul hcf)), (hψ' _ _).2.mul_right⟩
  rw [integral_finsetSum _ fun z _ => (hzi z).1.integrable_of_hasCompactSupport (hzi z).2]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => by simp [hψK _ _ _ hh]

end Main

end PositivityTheory.Rg.BcB.CG

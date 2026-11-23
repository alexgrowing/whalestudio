import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.MultHasCompactSupport
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntryLeOfLg

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH TypeH)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

namespace prime_not_mem_section_base_place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

def evV (v : InfinitePlace E) : Cinf E →+* ℂ := Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v

def uAt (v : InfinitePlace E) (k : Kinf E n) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨(k : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v), by
    rw [Matrix.mem_unitaryGroup_iff]
    have h := Matrix.mem_unitaryGroup_iff.1 k.2
    have e : star ((k : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v)) =
        (star (k : Matrix (Fin n) (Fin n) (Cinf E))).map (evV v) := by
      ext i j; rfl
    rw [e, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]⟩

def coef (M : Mods E n) (I L : IxA M) (k : Kinf E n) : ℂ := ∏ v, ent (M v) ((M v).ρ (uAt v k⁻¹)) (I v) (L v)

def Wsp (M : Mods E n) : Submodule ℂ (Kinf E n → ℂ) :=
  Submodule.span ℂ (Set.range fun p : IxA M × IxA M => coef M p.1 p.2)

theorem fd_Wsp (M : Mods E n) : FiniteDimensional ℂ (Wsp M) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

theorem gInf_inv_val (v : InfinitePlace E) (k : Kinf E n) :
    (gInf v ((infGL E n (Unitary.toUnits k))⁻¹)).val = (uAt v k⁻¹).1 := by
  rw [← map_inv (infGL E n), ← map_inv (Unitary.toUnits (R := Matrix (Fin n) (Fin n) (Cinf E))) k]
  ext i j
  exact gInf_infGL n v _ i j

theorem entA_inf [MeasurableSpace (G n)] {μ : Measure (G n)} {M : Mods E n} {k : Kers M}
    {val : InfinitePlace E → Inf n → ℂ} {T : ℝ} (hk : IsMults μ k val T) (K : Kinf E n) (I J : IxA M) (y : GA E n) :
    entA k I J ((infGL E n (Unitary.toUnits K))⁻¹ * y) = ∑ L : IxA M, coef M I L K * entA k L J y := by
  have h1 : ∀ v, ent (M v) (k v (gInf v ((infGL E n (Unitary.toUnits K))⁻¹ * y)).val) (I v) (J v) =
      ∑ l, ent (M v) ((M v).ρ (uAt v K⁻¹)) (I v) l * ent (M v) (k v (gInf v y).val) l (J v) := by
    intro v
    have h2 := mult_equivariant_val (hk v) (gInf v y) (uAt v K⁻¹) 1
    simp only [OneMemClass.coe_one, map_one, mul_one] at h2
    have e : (gInf v ((infGL E n (Unitary.toUnits K))⁻¹ * y)).val = (uAt v K⁻¹).1 * (gInf v y).val := by
      rw [map_mul, Units.val_mul, gInf_inv_val]
    rw [e, h2, PMul.ent_mul]
  simp only [entA, coef]
  rw [Finset.prod_congr rfl fun v _ => h1 v, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [Finset.prod_mul_distrib]

theorem gInf_fin_mul (v : InfinitePlace E) (u : GL (Fin n) (Af E)) (z : GA E n) :
    gInf v ((finGL E n u)⁻¹ * z) = gInf v z := by
  rw [map_mul, map_inv, gInf_finGL, inv_one, one_mul]

theorem entA_fin {M : Mods E n} (k : Kers M) (I J : IxA M) (u : GL (Fin n) (Af E)) (z : GA E n) :
    entA k I J ((finGL E n u)⁻¹ * z) = entA k I J z := by
  simp only [entA, gInf_fin_mul]

theorem hFin_fin (u₁ : GL (Fin a) (Af E)) (u₂ : GL (Fin b) (Af E)) (y : H E a b) :
    hFin ((finGL E a u₁, finGL E b u₂)⁻¹ * y) = (u₁⁻¹, u₂⁻¹) * hFin y := by
  show (gFin ((finGL E a u₁)⁻¹ * y.1), gFin ((finGL E b u₂)⁻¹ * y.2)) = (u₁⁻¹ * gFin y.1, u₂⁻¹ * gFin y.2)
  rw [map_mul, map_mul, map_inv, map_inv, gFin_finGL, gFin_finGL]

theorem hFin_inf (A : GL (Fin a) (Cinf E)) (B : GL (Fin b) (Cinf E)) (y : H E a b) :
    hFin ((infGL E a A, infGL E b B)⁻¹ * y) = hFin y := by
  show (gFin ((infGL E a A)⁻¹ * y.1), gFin ((infGL E b B)⁻¹ * y.2)) = (gFin y.1, gFin y.2)
  have h1 : gFin (infGL E a A) = 1 := pFin_infGL A
  have h2 : gFin (infGL E b B) = 1 := pFin_infGL B
  rw [map_mul, map_mul, map_inv, map_inv, h1, h2, inv_one, inv_one, one_mul, one_mul]

theorem f_mul (D : Dom E a b) {ι : Type} [Fintype ι] (Φ : Matrix ι ι (H E a b → ℂ)) (f : ι → H E a b → ℂ) {c : ℂ}
    (h : PositivityTheory.Rg.BcB.E.conv D.μ Φ f = c • f) (i : ι) (x g : H E a b) :
    c * f i (x * g) = ∑ j, ∫ y, Φ i j (g⁻¹ * y) * f j (x * y) ∂D.μ := by
  have : BorelSpace (H E a b) := ⟨rfl⟩
  have : D.μ.IsMulLeftInvariant := D.haar.1
  have h1 := congrFun (congrFun h i) (x * g)
  simp only [PositivityTheory.Rg.BcB.E.conv, Pi.smul_apply, smul_eq_mul] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 := integral_mul_left_eq_self (μ := D.μ) (fun y => Φ i j (g⁻¹ * y) * f j (x * y)) g
  simp only [← mul_assoc, inv_mul_cancel, one_mul] at h2
  exact h2

theorem cs_pi {ι X : Type} [Fintype ι] [TopologicalSpace X] [T2Space X] {g : ι → X → ℂ}
    (hg : ∀ v, HasCompactSupport (g v)) : HasCompactSupport fun y : ι → X => ∏ v, g v (y v) := by
  refine HasCompactSupport.intro (isCompact_univ_pi fun v => (hg v).isCompact) fun y hy => ?_
  simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hy
  obtain ⟨v, hv⟩ := hy
  exact Finset.prod_eq_zero (Finset.mem_univ v) (image_eq_zero_of_notMem_tsupport hv)

theorem cs_prod3 {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space X]
    [T2Space Y] [T2Space Z] {f : X → ℂ} {g : Y → ℂ} {h : Z → ℂ} (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hh : HasCompactSupport h) : HasCompactSupport fun z : X × (Y × Z) => f z.1 * g z.2.1 * h z.2.2 := by
  refine HasCompactSupport.intro (hf.isCompact.prod (hg.isCompact.prod hh.isCompact)) fun z hz => ?_
  simp only [Set.mem_prod, not_and_or] at hz
  rcases hz with h1 | h1 | h1
  · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h1, mul_zero, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h1, mul_zero]

theorem continuous_entA [MeasurableSpace (G n)] {μ : Measure (G n)} {M : Mods E n} {k : Kers M}
    {val : InfinitePlace E → Inf n → ℂ} {T : ℝ} (hk : IsMults μ k val T) (I J : IxA M) : Continuous (entA k I J) := by
  have e : entA k I J = fun g => ∏ v, ent (M v) (k v (gInf v g).val) (I v) (J v) := rfl
  rw [e]
  exact continuous_finsetProd _ fun v _ => (mult_ent (hk v) (I v) (J v)).1.comp (continuous_gInf n v)

theorem tens_cs [MeasurableSpace (G a)] [MeasurableSpace (G b)] {μa : Measure (G a)} {μb : Measure (G b)}
    {Ma : Mods E a} {Mb : Mods E b} {κ : Type} {ka : Kers Ma} {kb : Kers Mb} {va : InfinitePlace E → Inf a → ℂ}
    {vb : InfinitePlace E → Inf b → ℂ} {T : ℝ} {ψ : Matrix κ κ (Hf E a b → ℂ)} (ha : IsMults μa ka va T)
    (hb : IsMults μb kb vb T) (hψ : IsFinM ψ) (i j : Io Ma Mb κ) :
    Continuous (tens ka kb ψ i j) ∧ HasCompactSupport (tens ka kb ψ i j) := by
  have hh : Continuous (hFin : H E a b → Hf E a b) :=
    ((continuous_gFin a).comp continuous_fst).prodMk ((continuous_gFin b).comp continuous_snd)
  have hcont : Continuous (tens ka kb ψ i j) :=
    (((continuous_entA ha _ _).comp continuous_fst).mul ((continuous_entA hb _ _).comp continuous_snd)).mul
      ((hψ i.2 j.2).1.comp hh)
  have hQ := cs_prod3 (cs_pi fun v => (mult_ent (ha v) (i.1.1 v) (j.1.1 v)).2)
    (cs_pi fun v => (mult_ent (hb v) (i.1.2 v) (j.1.2 v)).2) (hψ i.2 j.2).2
  have hpt : ∀ z, tens ka kb ψ i j (splitH a b z) =
      (∏ v, ent (Ma v) (ka v (z.1 v).val) (i.1.1 v) (j.1.1 v)) *
        (∏ v, ent (Mb v) (kb v (z.2.1 v).val) (i.1.2 v) (j.1.2 v)) * ψ i.2 j.2 z.2.2 := fun z => by
    simp only [tens, entA, gInf_splitH₁, gInf_splitH₂, hFin_splitH]
  have e : tens ka kb ψ i j = (fun z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b) =>
      (∏ v, ent (Ma v) (ka v (z.1 v).val) (i.1.1 v) (j.1.1 v)) *
        (∏ v, ent (Mb v) (kb v (z.2.1 v).val) (i.1.2 v) (j.1.2 v)) * ψ i.2 j.2 z.2.2) ∘
      (splitH a b).toHomeomorph.symm := by
    funext g
    obtain ⟨z, rfl⟩ := (splitH a b).surjective g
    rw [Function.comp_apply, show (splitH a b).toHomeomorph.symm (splitH a b z) = z from
      (splitH a b).toHomeomorph.symm_apply_apply z]
    exact hpt z
  refine ⟨hcont, ?_⟩
  rw [e]
  exact hQ.comp_homeomorph _

theorem integrable_tens (D : Dom E a b) [MeasurableSpace (G a)] [MeasurableSpace (G b)] {μa : Measure (G a)}
    {μb : Measure (G b)} {Ma : Mods E a} {Mb : Mods E b} {κ : Type} {ka : Kers Ma} {kb : Kers Mb}
    {va : InfinitePlace E → Inf a → ℂ} {vb : InfinitePlace E → Inf b → ℂ} {T : ℝ} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    (ha : IsMults μa ka va T) (hb : IsMults μb kb vb T) (hψ : IsFinM ψ) {F : H E a b → ℂ} (hF : Continuous F)
    (i j : Io Ma Mb κ) (x : H E a b) : Integrable (fun y => tens ka kb ψ i j y * F (x * y)) D.μ := by
  have : BorelSpace (H E a b) := ⟨rfl⟩
  have : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
  have : IsFiniteMeasureOnCompacts D.μ := ⟨fun K hK => hK.measure_lt_top_of_nhdsWithin fun x _ =>
    (D.μ.finiteAt_nhds x).filter_mono nhdsWithin_le_nhds⟩
  obtain ⟨h1, h2⟩ := tens_cs ha hb hψ i j
  exact (h1.mul (hF.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
    (h2.mul_right (f' := fun y => F (x * y)))

end prime_not_mem_section_base_place

open prime_not_mem_section_base_place in

theorem typeOf : TypeOf := by
  intro E _ _ _ a b Ma Mb
  refine ⟨Wsp Ma, Wsp Mb, fd_Wsp Ma, fd_Wsp Mb, ?_⟩
  intro D _ _ μa μb κ _ ka kb va vb T ψ K₁ K₂ f hka hkb hψ hlev hrep i
  obtain ⟨hfc, c, hc, hconv⟩ := hrep
  have hint : ∀ i j x, Integrable (fun y => tens ka kb ψ i j y * f j (x * y)) D.μ := fun i j x =>
    integrable_tens D hka hkb hψ (hfc j) i j x
  have hR : ∀ (L : Io Ma Mb κ) x, c * f L x = ∑ j, ∫ y, tens ka kb ψ L j y * f j (x * y) ∂D.μ := fun L x => by
    have h0 := f_mul D _ f hconv L x 1
    simpa only [mul_one, inv_one, one_mul] using h0
  refine ⟨fun u₁ hu₁ u₂ hu₂ x => ?_, fun x => ?_⟩
  · have h1 := f_mul D _ f hconv i x (finGL E a u₁, finGL E b u₂)
    have hΦ : ∀ j y, tens ka kb ψ i j ((finGL E a u₁, finGL E b u₂)⁻¹ * y) = tens ka kb ψ i j y := by
      intro j y
      show entA ka i.1.1 j.1.1 ((finGL E a u₁)⁻¹ * y.1) * entA kb i.1.2 j.1.2 ((finGL E b u₂)⁻¹ * y.2) *
          ψ i.2 j.2 (hFin ((finGL E a u₁, finGL E b u₂)⁻¹ * y)) =
        entA ka i.1.1 j.1.1 y.1 * entA kb i.1.2 j.1.2 y.2 * ψ i.2 j.2 (hFin y)
      rw [entA_fin, entA_fin, hFin_fin, hlev _ _ _ (K₁.inv_mem hu₁) _ (K₂.inv_mem hu₂)]
    simp only [hΦ] at h1
    exact mul_left_cancel₀ hc (h1.trans (hR i x).symm)
  · have hexp : ∀ k : Kinf E a × Kinf E b,
        f i (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))) =
          ∑ L₁ : IxA Ma, ∑ L₂ : IxA Mb, f ((L₁, L₂), i.2) x * (coef Ma i.1.1 L₁ k.1 * coef Mb i.1.2 L₂ k.2) := by
      intro k
      apply mul_left_cancel₀ hc
      have hΦ : ∀ j y, tens ka kb ψ i j ((infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))⁻¹ * y) =
          ∑ L₁ : IxA Ma, ∑ L₂ : IxA Mb,
            (coef Ma i.1.1 L₁ k.1 * coef Mb i.1.2 L₂ k.2) * tens ka kb ψ ((L₁, L₂), i.2) j y := by
        intro j y
        show entA ka i.1.1 j.1.1 ((infGL E a (Unitary.toUnits k.1))⁻¹ * y.1) *
            entA kb i.1.2 j.1.2 ((infGL E b (Unitary.toUnits k.2))⁻¹ * y.2) *
            ψ i.2 j.2 (hFin ((infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))⁻¹ * y)) = _
        rw [entA_inf hka, entA_inf hkb, hFin_inf, Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun L₁ _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun L₂ _ => ?_
        simp only [tens]
        ring
      rw [f_mul D _ f hconv i x]
      calc ∑ j, ∫ y, tens ka kb ψ i j
              ((infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))⁻¹ * y) * f j (x * y) ∂D.μ
          = ∑ j, ∫ y, ∑ L₁ : IxA Ma, ∑ L₂ : IxA Mb, (coef Ma i.1.1 L₁ k.1 * coef Mb i.1.2 L₂ k.2) *
              (tens ka kb ψ ((L₁, L₂), i.2) j y * f j (x * y)) ∂D.μ := by
            refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            simp only [hΦ, Finset.sum_mul, mul_assoc]
        _ = ∑ j, ∑ L₁ : IxA Ma, ∑ L₂ : IxA Mb, (coef Ma i.1.1 L₁ k.1 * coef Mb i.1.2 L₂ k.2) *
              ∫ y, tens ka kb ψ ((L₁, L₂), i.2) j y * f j (x * y) ∂D.μ := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [integral_finsetSum _ fun L₁ _ => integrable_finsetSum _ fun L₂ _ => (hint _ j x).const_mul _]
            refine Finset.sum_congr rfl fun L₁ _ => ?_
            rw [integral_finsetSum _ fun L₂ _ => (hint _ j x).const_mul _]
            exact Finset.sum_congr rfl fun L₂ _ => integral_const_mul _ _
        _ = ∑ L₁ : IxA Ma, ∑ L₂ : IxA Mb, (coef Ma i.1.1 L₁ k.1 * coef Mb i.1.2 L₂ k.2) *
              (c * f ((L₁, L₂), i.2) x) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun L₁ _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun L₂ _ => ?_
            rw [hR, Finset.mul_sum]
        _ = c * ∑ L₁ : IxA Ma, ∑ L₂ : IxA Mb, f ((L₁, L₂), i.2) x * (coef Ma i.1.1 L₁ k.1 * coef Mb i.1.2 L₂ k.2) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun L₁ _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun L₂ _ => ?_
            ring
    have e : (fun k : Kinf E a × Kinf E b =>
        f i (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2)))) =
          ∑ L₁ : IxA Ma, ∑ L₂ : IxA Mb,
            f ((L₁, L₂), i.2) x • fun k : Kinf E a × Kinf E b => coef Ma i.1.1 L₁ k.1 * coef Mb i.1.2 L₂ k.2 := by
      funext k
      rw [hexp k]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact Submodule.sum_mem _ fun L₁ _ => Submodule.sum_mem _ fun L₂ _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, Submodule.subset_span ⟨(i.1.1, L₁), rfl⟩, _,
        Submodule.subset_span ⟨(i.1.2, L₂), rfl⟩, rfl⟩)

end PositivityTheory.Rg.BcB.CG

end

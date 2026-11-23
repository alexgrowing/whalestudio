import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.IntegrableTens

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

namespace ActEq

open prime_not_mem_section_base_place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

theorem gInf_infP_inv_mul (y : InfinitePlace E → G n) (w : InfinitePlace E) (z : GA E n) :
    gInf w ((infP n y)⁻¹ * z) = (y w)⁻¹ * gInf w z := by
  rw [map_mul, map_inv, gInf_infP]

theorem gFin_infP_inv_mul (y : InfinitePlace E → G n) (z : GA E n) : gFin ((infP n y)⁻¹ * z) = gFin z := by
  rw [map_mul, map_inv, gFin_infP, inv_one, one_mul]

theorem entA_place [MeasurableSpace (G n)] {μ : Measure (G n)} {M : Mods E n} {k : Kers M}
    {val : InfinitePlace E → Inf n → ℂ} {T : ℝ} (hk : IsMults μ k val T) (v : InfinitePlace E)
    (u : Matrix.unitaryGroup (Fin n) ℂ) (I J : IxA M) (z : GA E n) :
    entA k I J ((infP n (Pi.mulSingle v (Unitary.toUnits u)))⁻¹ * z) =
      ∑ l, ent (M v) ((M v).ρ u⁻¹) (I v) l * entA k (Function.update I v l) J z := by
  simp only [entA, gInf_infP_inv_mul]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ v]
  have hv : ent (M v) (k v (((Pi.mulSingle v (Unitary.toUnits u) : InfinitePlace E → G n) v)⁻¹ * gInf v z).val) (I v) (J v) =
      ∑ l, ent (M v) ((M v).ρ u⁻¹) (I v) l * ent (M v) (k v (gInf v z).val) l (J v) := by
    rw [Pi.mulSingle_eq_same]
    have h2 := mult_equivariant_val (hk v) (gInf v z) u⁻¹ 1
    simp only [OneMemClass.coe_one, map_one, mul_one] at h2
    have e : ((Unitary.toUnits u)⁻¹ * gInf v z).val = (u⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 * (gInf v z).val := by
      rw [Units.val_mul]
      rfl
    rw [e, h2, PMul.ent_mul]
  have hw : ∀ w : {w // w ≠ v}, ent (M w) (k w (((Pi.mulSingle v (Unitary.toUnits u) : InfinitePlace E → G n) w)⁻¹ * gInf w z).val) (I w) (J w) =
      ent (M w) (k w (gInf w z).val) (I w) (J w) := by
    intro w
    rw [Pi.mulSingle_eq_of_ne w.2, inv_one, one_mul]
  rw [hv, Finset.prod_congr rfl fun w _ => hw w, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ v, Function.update_self]
  have hw' : ∀ w : {w // w ≠ v}, ent (M w) (k w (gInf w z).val) (Function.update I v l w) (J w) =
      ent (M w) (k w (gInf w z).val) (I w) (J w) := fun w => by
    rw [Function.update_of_ne w.2]
  rw [Finset.prod_congr rfl fun w _ => hw' w]
  ring

end ActEq

open prime_not_mem_section_base_place ActEq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem equiv_a (D : Dom E a b) [MeasurableSpace (G a)] [MeasurableSpace (G b)] {μa : Measure (G a)}
    {μb : Measure (G b)} {Ma : Mods E a} {Mb : Mods E b} {κ : Type} [Fintype κ] {ka : Kers Ma} {kb : Kers Mb}
    {va : InfinitePlace E → Inf a → ℂ} {vb : InfinitePlace E → Inf b → ℂ} {T : ℝ} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    {f : Io Ma Mb κ → H E a b → ℂ} (hka : IsMults μa ka va T) (hkb : IsMults μb kb vb T) (hψ : IsFinM ψ)
    (hR : Repr D ka kb ψ f) (v : InfinitePlace E) (u : Matrix.unitaryGroup (Fin a) ℂ) (I : Io Ma Mb κ)
    (x : H E a b) :
    f I (x * (infP a (Pi.mulSingle v (Unitary.toUnits u)), 1)) =
      ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l * f ((Function.update I.1.1 v l, I.1.2), I.2) x := by
  obtain ⟨hfc, c, hc, hconv⟩ := hR
  have hint : ∀ i j x, Integrable (fun y => tens ka kb ψ i j y * f j (x * y)) D.μ := fun i j x =>
    integrable_tens D hka hkb hψ (hfc j) i j x
  have hRx : ∀ (L : Io Ma Mb κ) x, c * f L x = ∑ j, ∫ y, tens ka kb ψ L j y * f j (x * y) ∂D.μ := fun L x => by
    have h0 := f_mul D _ f hconv L x 1
    simpa only [mul_one, inv_one, one_mul] using h0
  set p : H E a b := (infP a (Pi.mulSingle v (Unitary.toUnits u)), 1) with hp
  have hΦ : ∀ j y, tens ka kb ψ I j (p⁻¹ * y) =
      ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l * tens ka kb ψ ((Function.update I.1.1 v l, I.1.2), I.2) j y := by
    intro j y
    have hF : hFin (p⁻¹ * y) = hFin y :=
      Prod.ext (gFin_infP_inv_mul _ y.1) (by show gFin (1⁻¹ * y.2) = gFin y.2; rw [inv_one, one_mul])
    show entA ka I.1.1 j.1.1 ((infP a (Pi.mulSingle v (Unitary.toUnits u)))⁻¹ * y.1) *
        entA kb I.1.2 j.1.2 (1⁻¹ * y.2) * ψ I.2 j.2 (hFin (p⁻¹ * y)) = _
    rw [hF, inv_one, one_mul, entA_place hka, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [tens]
    ring
  apply mul_left_cancel₀ hc
  rw [f_mul D _ f hconv I x p]
  calc ∑ j, ∫ y, tens ka kb ψ I j (p⁻¹ * y) * f j (x * y) ∂D.μ
      = ∑ j, ∫ y, ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l *
          (tens ka kb ψ ((Function.update I.1.1 v l, I.1.2), I.2) j y * f j (x * y)) ∂D.μ := by
        refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [hΦ, Finset.sum_mul, mul_assoc]
    _ = ∑ j, ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l *
          ∫ y, tens ka kb ψ ((Function.update I.1.1 v l, I.1.2), I.2) j y * f j (x * y) ∂D.μ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_finsetSum _ fun l _ => (hint _ j x).const_mul _]
        exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
    _ = ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l * (c * f ((Function.update I.1.1 v l, I.1.2), I.2) x) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hRx, Finset.mul_sum]
    _ = c * ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l * f ((Function.update I.1.1 v l, I.1.2), I.2) x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

theorem equiv_b (D : Dom E a b) [MeasurableSpace (G a)] [MeasurableSpace (G b)] {μa : Measure (G a)}
    {μb : Measure (G b)} {Ma : Mods E a} {Mb : Mods E b} {κ : Type} [Fintype κ] {ka : Kers Ma} {kb : Kers Mb}
    {va : InfinitePlace E → Inf a → ℂ} {vb : InfinitePlace E → Inf b → ℂ} {T : ℝ} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    {f : Io Ma Mb κ → H E a b → ℂ} (hka : IsMults μa ka va T) (hkb : IsMults μb kb vb T) (hψ : IsFinM ψ)
    (hR : Repr D ka kb ψ f) (v : InfinitePlace E) (u : Matrix.unitaryGroup (Fin b) ℂ) (I : Io Ma Mb κ)
    (x : H E a b) :
    f I (x * (1, infP b (Pi.mulSingle v (Unitary.toUnits u)))) =
      ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l * f ((I.1.1, Function.update I.1.2 v l), I.2) x := by
  obtain ⟨hfc, c, hc, hconv⟩ := hR
  have hint : ∀ i j x, Integrable (fun y => tens ka kb ψ i j y * f j (x * y)) D.μ := fun i j x =>
    integrable_tens D hka hkb hψ (hfc j) i j x
  have hRx : ∀ (L : Io Ma Mb κ) x, c * f L x = ∑ j, ∫ y, tens ka kb ψ L j y * f j (x * y) ∂D.μ := fun L x => by
    have h0 := f_mul D _ f hconv L x 1
    simpa only [mul_one, inv_one, one_mul] using h0
  set p : H E a b := (1, infP b (Pi.mulSingle v (Unitary.toUnits u))) with hp
  have hΦ : ∀ j y, tens ka kb ψ I j (p⁻¹ * y) =
      ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l * tens ka kb ψ ((I.1.1, Function.update I.1.2 v l), I.2) j y := by
    intro j y
    have hF : hFin (p⁻¹ * y) = hFin y :=
      Prod.ext (by show gFin (1⁻¹ * y.1) = gFin y.1; rw [inv_one, one_mul]) (gFin_infP_inv_mul _ y.2)
    show entA ka I.1.1 j.1.1 (1⁻¹ * y.1) *
        entA kb I.1.2 j.1.2 ((infP b (Pi.mulSingle v (Unitary.toUnits u)))⁻¹ * y.2) * ψ I.2 j.2 (hFin (p⁻¹ * y)) = _
    rw [hF, inv_one, one_mul, entA_place hkb, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [tens]
    ring
  apply mul_left_cancel₀ hc
  rw [f_mul D _ f hconv I x p]
  calc ∑ j, ∫ y, tens ka kb ψ I j (p⁻¹ * y) * f j (x * y) ∂D.μ
      = ∑ j, ∫ y, ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l *
          (tens ka kb ψ ((I.1.1, Function.update I.1.2 v l), I.2) j y * f j (x * y)) ∂D.μ := by
        refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [hΦ, Finset.sum_mul, mul_assoc]
    _ = ∑ j, ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l *
          ∫ y, tens ka kb ψ ((I.1.1, Function.update I.1.2 v l), I.2) j y * f j (x * y) ∂D.μ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_finsetSum _ fun l _ => (hint _ j x).const_mul _]
        exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
    _ = ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l * (c * f ((I.1.1, Function.update I.1.2 v l), I.2) x) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hRx, Finset.mul_sum]
    _ = c * ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l * f ((I.1.1, Function.update I.1.2 v l), I.2) x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

end PositivityTheory.Rg.BcB.CG

end

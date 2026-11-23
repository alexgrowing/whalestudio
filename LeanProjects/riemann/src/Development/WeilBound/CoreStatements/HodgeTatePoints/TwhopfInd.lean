import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace PositivityTheory.HtPt.Twhopf

theorem translate_mem : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A := by
  intro R _ T _ A hA f hf t
  have key : ∀ g ∈ prodSpan A, (fun h => g (t, h)) ∈ A := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      have e : (fun h => a (t, h).1 * b (t, h).2) = a t • b := by
        funext h
        simp [smul_eq_mul]
      rw [e]
      exact A.smul_mem hb _
    | zero => exact A.zero_mem
    | add x y _ _ hx hy => exact A.add_mem hx hy
    | smul r x _ hx => exact A.smul_mem hx r
  exact key _ (hA.comul f hf)

theorem exists_coset_coord {T H : Type} [CommGroup T] [CommGroup H] (ι : H →* T) :
    ∃ κ : T → H, ∀ t, (QuotientGroup.mk t : T ⧸ ι.range).out * ι (κ t) = t := by
  have key : ∀ t : T, ∃ h : H, ι h = ((QuotientGroup.mk t : T ⧸ ι.range).out)⁻¹ * t := fun t =>
    MonoidHom.mem_range.mp (QuotientGroup.eq.mp (QuotientGroup.out_eq' _))
  choose κ hκ using key
  exact ⟨κ, fun t => by rw [hκ, mul_inv_cancel_left]⟩

theorem ind_hopf : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (H : Type) [CommGroup H] (ι : H →* T), Function.Injective ι → ∀ A : Subalgebra R (H → R), IsHopfOrder A → IsHopfOrder (indOrder ι A) := by
  classical
  intro R _ _ T _ _ H _ ι hι A hA
  have : Fintype (T ⧸ ι.range) := Fintype.ofFinite _
  have : Module.Finite R A := hA.finite
  have : Module.Projective R A := hA.projective
  obtain ⟨κ, hκ⟩ := exists_coset_coord ι
  have hmk : ∀ t h, (QuotientGroup.mk (t * ι h) : T ⧸ ι.range) = QuotientGroup.mk t := by
    intro t h
    rw [QuotientGroup.eq]
    exact MonoidHom.mem_range.mpr ⟨h⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
  have hκmul : ∀ t h, κ (t * ι h) = κ t * h := by
    intro t h
    apply hι
    have e1 := hκ (t * ι h)
    have e2 := hκ t
    rw [hmk] at e1
    rw [map_mul]
    apply mul_left_cancel (a := (QuotientGroup.mk t : T ⧸ ι.range).out)
    rw [e1, ← mul_assoc, e2]
  let ext : T ⧸ ι.range → (H → R) → T → R := fun c a x =>
    if (QuotientGroup.mk x : T ⧸ ι.range) = c then a (κ x) else 0
  have hext_mem : ∀ c a, a ∈ A → ext c a ∈ indOrder ι A := by
    intro c a ha
    rw [OrderApi.mem_indOrder]
    intro t
    have e : (fun h => ext c a (t * ι h)) =
        if (QuotientGroup.mk t : T ⧸ ι.range) = c then (fun h => a (κ t * h)) else 0 := by
      funext h
      simp only [ext, hmk, hκmul]
      split_ifs <;> rfl
    rw [e]
    split_ifs
    · exact translate_mem R H A hA a ha (κ t)
    · exact A.zero_mem
  have hdecomp : ∀ f : T → R, ∑ c, ext c (fun h => f (c.out * ι h)) = f := by
    intro f
    funext x
    rw [Finset.sum_apply, Finset.sum_eq_single (QuotientGroup.mk x)]
    · simp only [ext, ↓reduceIte, hκ]
    · intro c _ hc
      simp only [ext]
      rw [if_neg (fun h => hc h.symm)]
    · intro h
      exact absurd (Finset.mem_univ _) h
  let extL : T ⧸ ι.range → (H → R) →ₗ[R] (T → R) := fun c =>
    { toFun := ext c
      map_add' := fun a b => by
        funext x
        simp only [ext, Pi.add_apply]
        split_ifs <;> simp
      map_smul' := fun r a => by
        funext x
        simp only [ext, Pi.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }
  let Φ : indOrder ι A →ₗ[R] (T ⧸ ι.range → A) :=
    { toFun := fun f c => ⟨fun h => (f : T → R) (c.out * ι h),
        (OrderApi.mem_indOrder ι A f).mp f.2 c.out⟩
      map_add' := fun f g => by
        funext c
        exact Subtype.ext rfl
      map_smul' := fun r f => by
        funext c
        exact Subtype.ext rfl }
  let Ψ : (T ⧸ ι.range → A) →ₗ[R] indOrder ι A :=
    { toFun := fun a => ⟨∑ c, extL c (a c),
        Subalgebra.sum_mem _ (fun c _ => hext_mem c (a c) (a c).2)⟩
      map_add' := fun a b => by
        apply Subtype.ext
        simp only [Pi.add_apply, Subalgebra.coe_add, map_add, Finset.sum_add_distrib]
      map_smul' := fun r a => by
        apply Subtype.ext
        simp only [Pi.smul_apply, Subalgebra.coe_smul, map_smul, Finset.smul_sum,
          RingHom.id_apply] }
  have hΨΦ : Ψ.comp Φ = LinearMap.id := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact hdecomp (f : T → R)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Module.Finite.of_surjective Ψ (fun f => ⟨Φ f, by
      rw [← LinearMap.comp_apply, hΨΦ, LinearMap.id_apply]⟩)
  · have : Module.Projective R (T ⧸ ι.range → A) :=
      Module.Projective.of_equiv
        (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun _ : T ⧸ ι.range => A))
    exact Module.Projective.of_split Φ Ψ hΨΦ
  · obtain ⟨d, hd, hdf⟩ := hA.full
    refine ⟨d, hd, fun f => ?_⟩
    rw [OrderApi.mem_indOrder]
    intro t
    exact hdf _
  · intro f hf
    have hg : ∀ c c' : T ⧸ ι.range,
        (fun z : H × H => f (c.out * c'.out * ι (z.1 * z.2))) ∈ prodSpan A := fun c c' =>
      hA.comul _ ((OrderApi.mem_indOrder ι A f).mp hf (c.out * c'.out))
    have hlift : ∀ (c c' : T ⧸ ι.range) (G : H × H → R), G ∈ prodSpan A →
        (fun z : T × T => if (QuotientGroup.mk z.1 : T ⧸ ι.range) = c ∧
          (QuotientGroup.mk z.2 : T ⧸ ι.range) = c' then G (κ z.1, κ z.2) else 0) ∈
          prodSpan (indOrder ι A) := by
      intro c c' G hG
      induction hG using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨a, ha, b, hb, rfl⟩ := hg
        have e : (fun z : T × T => if (QuotientGroup.mk z.1 : T ⧸ ι.range) = c ∧
            (QuotientGroup.mk z.2 : T ⧸ ι.range) = c' then a (κ z.1, κ z.2).1 * b (κ z.1, κ z.2).2
            else 0) = fun z => ext c a z.1 * ext c' b z.2 := by
          funext z
          by_cases h1 : (QuotientGroup.mk z.1 : T ⧸ ι.range) = c <;>
            by_cases h2 : (QuotientGroup.mk z.2 : T ⧸ ι.range) = c' <;> simp [ext, h1, h2]
        rw [e]
        exact OrderApi.mul_mem_prodSpan (hext_mem c a ha) (hext_mem c' b hb)
      | zero =>
        convert (prodSpan (indOrder ι A)).zero_mem using 1
        funext z
        simp
      | add x y _ _ hx hy =>
        convert (prodSpan (indOrder ι A)).add_mem hx hy using 1
        funext z
        simp only [Pi.add_apply]
        split_ifs <;> simp
      | smul r x _ hx =>
        convert (prodSpan (indOrder ι A)).smul_mem r hx using 1
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
        split_ifs <;> simp
    have hsum : (fun z : T × T => f (z.1 * z.2)) = ∑ c : T ⧸ ι.range, ∑ c' : T ⧸ ι.range,
        (fun z : T × T => if (QuotientGroup.mk z.1 : T ⧸ ι.range) = c ∧
          (QuotientGroup.mk z.2 : T ⧸ ι.range) = c' then
          (fun w : H × H => f (c.out * c'.out * ι (w.1 * w.2))) (κ z.1, κ z.2) else 0) := by
      funext z
      rw [Finset.sum_apply, Finset.sum_eq_single (QuotientGroup.mk z.1)]
      · rw [Finset.sum_apply, Finset.sum_eq_single (QuotientGroup.mk z.2)]
        · simp only [and_self, ↓reduceIte]
          calc f (z.1 * z.2) = f ((QuotientGroup.mk z.1 : T ⧸ ι.range).out * ι (κ z.1) *
                ((QuotientGroup.mk z.2 : T ⧸ ι.range).out * ι (κ z.2))) := by rw [hκ, hκ]
            _ = _ := by rw [map_mul, mul_mul_mul_comm]
        · intro c' _ hc'
          rw [if_neg (fun h => hc' h.2.symm)]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · intro c _ hc
        rw [Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro c' _
        rw [if_neg (fun h => hc h.1.symm)]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum]
    exact Submodule.sum_mem _ (fun c _ => Submodule.sum_mem _ (fun c' _ => hlift c c' _ (hg c c')))
  · intro f hf
    rw [OrderApi.mem_indOrder] at hf ⊢
    intro t
    have e : (fun h => f ((t * ι h)⁻¹)) = fun x => (fun h => f (t⁻¹ * ι h)) x⁻¹ := by
      funext h
      rw [mul_inv]
      simp only [map_inv]
    rw [e]
    exact hA.inv _ (hf t⁻¹)

theorem res_ind {R T : Type} [CommRing R] [CommGroup T] (H : Subgroup T) (A : Subalgebra R (H → R))
    (hA : IsHopfOrder A) : resOrder H.subtype (indOrder H.subtype A) = A := by
  classical
  apply le_antisymm
  · intro x hx
    obtain ⟨f, hf, rfl⟩ := Subalgebra.mem_map.mp hx
    have h1 := (OrderApi.mem_indOrder _ A f).mp hf 1
    convert h1 using 1
    funext h
    simp [GlobalTheory.CompanionTheory.Ar.BT.pullFun]
  · intro a ha
    let f : T → R := fun x => if hx : x ∈ H then a ⟨x, hx⟩ else 0
    have hf : f ∈ indOrder H.subtype A := by
      rw [OrderApi.mem_indOrder]
      intro t
      by_cases ht : t ∈ H
      · have e : (fun h : H => f (t * H.subtype h)) = fun h => a (⟨t, ht⟩ * h) := by
          funext h
          simp only [f, Subgroup.coe_subtype]
          rw [dif_pos (H.mul_mem ht h.2)]
          rfl
        rw [e]
        exact translate_mem R H A hA a ha ⟨t, ht⟩
      · have e : (fun h : H => f (t * H.subtype h)) = 0 := by
          funext h
          simp only [f, Subgroup.coe_subtype, Pi.zero_apply]
          rw [dif_neg]
          intro hm
          exact ht (by simpa using H.mul_mem hm (H.inv_mem h.2))
        rw [e]
        exact A.zero_mem
    exact Subalgebra.mem_map.mpr ⟨f, hf, by
      funext h
      simp [GlobalTheory.CompanionTheory.Ar.BT.pullFun, f]⟩

end PositivityTheory.HtPt.Twhopf

import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.OrthBasisLatOf

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial

def OrthMin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])),
    p ≠ 2 → FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) → L.FG →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) → (∃ u ∈ L, ∃ v ∈ L, B u v ≠ 0) →
    ∃ x ∈ L, B x x ≠ 0 ∧ ∀ u ∈ L, ∃ c : ℤ_[p], B u x = (c : ℚ_[p]) * B x x

def SplitRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (L L' : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (x : MvPolynomial σ ℚ_[p]),
    FiniteDimensional ℚ_[p] W → (∀ y ∈ L, y ∈ W) → L.FG → L' ≤ L → x ∈ L → x ≠ 0 →
    Submodule.span ℤ_[p] {x} ⊔ L' = L → (∀ (c : ℤ_[p]) (y : MvPolynomial σ ℚ_[p]), y ∈ L' → c • x + y = 0 → c = 0) →
    Module.finrank ℤ_[p] L' < Module.finrank ℤ_[p] L

theorem zsmul_eq' {p : ℕ} [Fact p.Prime] {σ : Type} (c : ℤ_[p]) (u : MvPolynomial σ ℚ_[p]) :
    c • u = (c : ℚ_[p]) • u := rfl

theorem orthSplit_of (hM : OrthMin) (hR : SplitRank) : OrthSplit := by
  intro p _ σ B L W hp hW hLW hfg hsm hadd hsym hne
  obtain ⟨x, hxL, hxx, hdiv⟩ := hM p σ B L W hp hW hLW hfg hsm hadd hsym hne
  have hB0 : ∀ v, B 0 v = 0 := by
    intro v
    have h := hsm 0 0 v
    rwa [zero_smul, zero_mul] at h
  have hsub : ∀ u v w, B (u - v) w = B u w - B v w := by
    intro u v w
    have h := hadd (u - v) v w
    rw [sub_add_cancel] at h
    rw [h]
    ring
  let K : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]) :=
    { carrier := {u | u ∈ L ∧ B u x = 0}
      add_mem' := fun {u v} hu hv => ⟨L.add_mem hu.1 hv.1, by rw [hadd, hu.2, hv.2, add_zero]⟩
      zero_mem' := ⟨L.zero_mem, hB0 x⟩
      smul_mem' := fun c u hu => ⟨L.smul_mem c hu.1, by
        rw [zsmul_eq' c u, hsm, hu.2, mul_zero]⟩ }
  have hKL : K ≤ L := fun u hu => hu.1
  have hx0 : x ≠ 0 := by
    intro h
    apply hxx
    rw [h, hB0]
  have hdirect : ∀ (c : ℤ_[p]) (y : MvPolynomial σ ℚ_[p]), y ∈ K → c • x + y = 0 → c = 0 := by
    intro c y hy hcy
    have h1 : B (c • x + y) x = 0 := by
      rw [hcy, hB0]
    rw [hadd, zsmul_eq' c x, hsm, hy.2, add_zero] at h1
    have h2 : (c : ℚ_[p]) = 0 := (mul_eq_zero.mp h1).resolve_right hxx
    first
    | exact PadicInt.coe_eq_zero.mp h2
    | exact Subtype.ext h2
  have hsup : Submodule.span ℤ_[p] {x} ⊔ K = L := by
    apply le_antisymm
    · exact sup_le ((Submodule.span_le).mpr (Set.singleton_subset_iff.mpr hxL)) hKL
    · intro u hu
      obtain ⟨c, hc⟩ := hdiv u hu
      refine Submodule.mem_sup.mpr ⟨c • x, Submodule.mem_span_singleton.mpr ⟨c, rfl⟩, u - c • x, ⟨?_, ?_⟩, ?_⟩
      · exact L.sub_mem hu (L.smul_mem c hxL)
      · rw [hsub, zsmul_eq' c x, hsm, hc, sub_self]
      · abel
  refine ⟨x, hxL, K, hKL, hfg.of_le hKL, hR p σ L K W x hW hLW hfg hKL hxL hx0 hsup hdirect, ?_, hsup, hdirect⟩
  intro u hu
  rw [hsym x hxL u hu.1]
  exact hu.2

theorem splitRank_proved : SplitRank := by
  intro p _ σ L L' W x hW hLW hfg hL'L hxL hx0 hsup hdirect
  haveI : NoZeroSMulDivisors ℤ_[p] (MvPolynomial σ ℚ_[p]) := by
    constructor
    intro c y h
    rw [zsmul_eq'] at h
    rcases smul_eq_zero.mp h with h | h
    · left
      first
      | exact PadicInt.coe_eq_zero.mp h
      | exact Subtype.ext h
    · right
      exact h
  haveI : Module.Finite ℤ_[p] L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Finite ℤ_[p] L' := Module.Finite.iff_fg.mpr (hfg.of_le hL'L)
  haveI : Module.Free ℤ_[p] L' := Module.free_of_finite_type_torsion_free'
  haveI : Module.Free ℤ_[p] L := Module.free_of_finite_type_torsion_free'
  let f : (ℤ_[p] × L') →ₗ[ℤ_[p]] L :=
    { toFun := fun q => ⟨q.1 • x + (q.2 : MvPolynomial σ ℚ_[p]), L.add_mem (L.smul_mem _ hxL) (hL'L q.2.2)⟩
      map_add' := fun q q' => by
        apply Subtype.ext
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
        abel
      map_smul' := fun c q => by
        apply Subtype.ext
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_eq_mul, RingHom.id_apply, smul_add,
          mul_smul] }
  have hbij : Function.Bijective f := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨c, y⟩ hq
      have h1 : c • x + (y : MvPolynomial σ ℚ_[p]) = 0 := congrArg Subtype.val hq
      have hc : c = 0 := hdirect c y y.2 h1
      subst hc
      rw [zero_smul, zero_add] at h1
      exact Prod.ext rfl (Subtype.ext h1)
    · rintro ⟨u, hu⟩
      rw [← hsup] at hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      exact ⟨(c, ⟨b, hb⟩), rfl⟩
  have he := (LinearEquiv.ofBijective f hbij).finrank_eq
  rw [Module.finrank_prod, Module.finrank_self] at he
  omega

theorem orthSplit_of_min (hM : OrthMin) : OrthSplit := by
  exact orthSplit_of hM splitRank_proved

end Formalism.MainNotions.G.SymmetricFormBlocks

end

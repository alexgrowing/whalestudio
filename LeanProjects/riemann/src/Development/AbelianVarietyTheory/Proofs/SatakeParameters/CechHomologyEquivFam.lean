import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

universe v

namespace GlobalTheory.CechFam

variable {R : Type} [Field R] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module R E]
  {C : GlobalTheory.Cube.{v} ι R} (g : ∀ s, C.obj s →ₗ[R] E)

def famMap (p : ℕ) : Cube.Term C p →ₗ[R] (Finset ι → E) where
  toFun x s := g s (Cube.extend C p x s)
  map_add' x y := by funext s; simp
  map_smul' r x := by funext s; simp

theorem famMap_apply (p : ℕ) (x : Cube.Term C p) (s : Finset ι) :
    famMap g p x s = g s (Cube.extend C p x s) := rfl

theorem famMap_of_eq {p : ℕ} (x : Cube.Term C p) {s : Finset ι} (h : s.card = p) :
    famMap g p x s = g s (x ⟨s, h⟩) := by
  rw [famMap_apply, Cube.extend_apply_of_eq]

theorem famMap_of_ne {p : ℕ} (x : Cube.Term C p) {s : Finset ι} (h : s.card ≠ p) :
    famMap g p x s = 0 := by
  rw [famMap_apply, Cube.extend_apply_of_ne C x h, map_zero]

variable {g}

theorem famMap_d (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x)
    (m : ℕ) (x : Cube.Term C (m + 1)) :
    famMap g (m + 1 + 1) (Cube.d C (m + 1) x) = deltaL R ι E (famMap g (m + 1) x) := by
  funext t
  change _ = GlobalTheory.DI.delta (famMap g (m + 1) x) t
  unfold GlobalTheory.DI.delta
  by_cases ht : t.card = m + 1 + 1
  · rw [famMap_of_eq g _ ht, Cube.d_apply_extend, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hn : (t.erase i).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hi, ht]; omega
    rw [map_zsmul, famMap_apply, hres _ _ _ hn]
  · rw [famMap_of_ne g _ ht]
    symm
    refine Finset.sum_eq_zero fun i hi => ?_
    have h1 : 0 < t.card := Finset.card_pos.2 ⟨i, hi⟩
    rw [famMap_of_ne g _ (by rw [Finset.card_erase_of_mem hi]; omega), smul_zero]

theorem famMap_injective (hinj : ∀ s, s.Nonempty → Function.Injective (g s)) (m : ℕ) :
    Function.Injective (famMap g (m + 1)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  funext s
  have h := congrFun hx s.1
  rw [famMap_of_eq g x s.2] at h
  exact hinj s.1 (Finset.card_pos.1 (by rw [s.2]; omega)) (h.trans (map_zero _).symm)

variable {A : Finset ι → Submodule R E}

theorem cechC_apply_mem {n : ℕ} {w : Finset ι → E} (hw : w ∈ cechC A (n : ℤ)) {s : Finset ι}
    (h : s.card = n + 1) : w s ∈ A s := by
  have := (Submodule.mem_pi.1 hw) s (Set.mem_univ _)
  rwa [if_pos ⟨Finset.card_pos.1 (by omega), by omega⟩] at this

theorem cechC_apply_eq_zero {n : ℕ} {w : Finset ι → E} (hw : w ∈ cechC A (n : ℤ)) {s : Finset ι}
    (h : s.card ≠ n + 1) : w s = 0 := by
  have := (Submodule.mem_pi.1 hw) s (Set.mem_univ _)
  rw [if_neg (fun h' => h (by omega))] at this
  exact (Submodule.mem_bot R).1 this

theorem famMap_mem (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s) (n : ℕ)
    (x : Cube.Term C (n + 1)) : famMap g (n + 1) x ∈ cechC A (n : ℤ) := by
  refine Submodule.mem_pi.2 fun s _ => ?_
  split_ifs with h
  · rw [famMap_of_eq g x (by omega : s.card = n + 1), ← hrange s h.1]
    exact LinearMap.mem_range_self _ _
  · rw [famMap_of_ne g x (fun h' => h ⟨Finset.card_pos.1 (by omega), by omega⟩)]
    exact Submodule.zero_mem _

theorem famMap_eq_of_agree {n : ℕ} (x : Cube.Term C (n + 1)) {w : Finset ι → E}
    (hw : w ∈ cechC A (n : ℤ)) (h : ∀ t : {s : Finset ι // s.card = n + 1}, w t.1 = g t.1 (x t)) :
    famMap g (n + 1) x = w := by
  funext s
  by_cases hs : s.card = n + 1
  · rw [famMap_of_eq g x hs]; exact (h ⟨s, hs⟩).symm
  · rw [famMap_of_ne g x hs, cechC_apply_eq_zero hw hs]

theorem famMap_surj (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s) {n : ℕ}
    {w : Finset ι → E} (hw : w ∈ cechC A (n : ℤ)) : ∃ x, famMap g (n + 1) x = w := by
  have : ∀ s : {s : Finset ι // s.card = n + 1}, ∃ y, g s.1 y = w s.1 := fun s => by
    have h := cechC_apply_mem hw s.2
    rw [← hrange _ (Finset.card_pos.1 (by rw [s.2]; omega))] at h
    exact h
  choose x hx using this
  exact ⟨x, famMap_eq_of_agree x hw fun t => (hx t).symm⟩

end GlobalTheory.CechFam

namespace GlobalTheory.CechFam

variable {R : Type} [Field R] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module R E]
  {C : GlobalTheory.Cube.{v} ι R} {g : ∀ s, C.obj s →ₗ[R] E} {A : Finset ι → Submodule R E}

theorem famMap_mem_Z (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s)
    (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) (n : ℕ)
    (z : LinearMap.ker (Cube.d C (n + 1))) : famMap g (n + 1) z.1 ∈ (GlobalTheory.PD.cech A).Z (n : ℤ) := by
  refine Submodule.mem_inf.2 ⟨famMap_mem hrange n z.1, ?_⟩
  rw [LinearMap.mem_ker]
  change deltaL R ι E (famMap g (n + 1) z.1) = 0
  rw [← famMap_d hres, LinearMap.mem_ker.1 z.2, map_zero]

def cocMap (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s)
    (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) (n : ℕ) :
    LinearMap.ker (Cube.d C (n + 1)) →ₗ[R] (GlobalTheory.PD.cech A).H (n : ℤ) :=
  Submodule.mkQ (((GlobalTheory.PD.cech A).B (n : ℤ)).submoduleOf ((GlobalTheory.PD.cech A).Z (n : ℤ))) ∘ₗ
    LinearMap.codRestrict ((GlobalTheory.PD.cech A).Z (n : ℤ)) (famMap g (n + 1) ∘ₗ (LinearMap.ker _).subtype)
      (famMap_mem_Z hrange hres n)

theorem cocMap_apply (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s)
    (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) (n : ℕ)
    (z : LinearMap.ker (Cube.d C (n + 1))) :
    cocMap hrange hres n z = Submodule.Quotient.mk ⟨famMap g (n + 1) z.1, famMap_mem_Z hrange hres n z⟩ :=
  rfl

theorem cocMap_surjective (hinj : ∀ s, s.Nonempty → Function.Injective (g s))
    (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s)
    (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) (n : ℕ) :
    Function.Surjective (cocMap hrange hres n) := by
  intro c
  obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨x, hx⟩ := famMap_surj hrange (Submodule.mem_inf.1 hw).1
  have hd : Cube.d C (n + 1) x = 0 := by
    apply famMap_injective hinj (n + 1)
    rw [famMap_d hres, hx, map_zero]
    exact LinearMap.mem_ker.1 (Submodule.mem_inf.1 hw).2
  refine ⟨⟨x, LinearMap.mem_ker.2 hd⟩, ?_⟩
  rw [cocMap_apply]
  congr 1
  exact Subtype.ext hx

theorem ker_cocMap (hinj : ∀ s, s.Nonempty → Function.Injective (g s))
    (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s)
    (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) (n : ℕ) :
    LinearMap.ker (cechClass C n) = LinearMap.ker (cocMap hrange hres n) := by
  ext z
  rw [LinearMap.mem_ker, LinearMap.mem_ker, cocMap_apply, Submodule.Quotient.mk_eq_zero]
  change _ ↔ famMap g (n + 1) z.1 ∈ ((GlobalTheory.PD.cech A).C ((n : ℤ) - 1)).map (deltaL R ι E)
  rw [Submodule.mem_map]
  cases n with
  | zero =>
    rw [cechClass_zero_eq_zero_iff]
    constructor
    · rintro rfl
      exact ⟨0, Submodule.zero_mem _, by rw [map_zero, ZeroMemClass.coe_zero, map_zero]⟩
    · rintro ⟨y, hy, hyz⟩
      have hy0 : y = 0 := by
        funext s
        have := (Submodule.mem_pi.1 hy) s (Set.mem_univ _)
        rw [if_neg (fun h => by
          have := Finset.card_pos.2 h.1
          push_cast at h
          omega)] at this
        exact (Submodule.mem_bot R).1 this
      rw [hy0, map_zero] at hyz
      exact Subtype.ext (famMap_injective hinj 0 (hyz.symm.trans (map_zero _).symm))
  | succ m =>
    rw [cechClass_succ_eq_zero_iff]
    have hc : (GlobalTheory.PD.cech A).C (((m + 1 : ℕ) : ℤ) - 1) = cechC A (m : ℤ) := by
      change cechC A _ = _
      congr 1
      push_cast
      ring
    rw [hc]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨famMap g (m + 1) y, famMap_mem hrange m y, ?_⟩
      rw [← famMap_d hres, hy]
    · rintro ⟨y, hy, hyz⟩
      obtain ⟨x, rfl⟩ := famMap_surj hrange hy
      refine ⟨x, famMap_injective hinj (m + 1) ?_⟩
      rw [famMap_d hres]
      exact hyz

end GlobalTheory.CechFam

open GlobalTheory.CechFam in

theorem GlobalTheory.cechHomologyEquivFam : ∀ (R : Type) [Field R] (ι : Type) [LinearOrder ι] (E : Type) [AddCommGroup E] [Module R E]
    (A : Finset ι → Submodule R E) (C : GlobalTheory.Cube ι R) (g : ∀ s, C.obj s →ₗ[R] E),
    (∀ s, s.Nonempty → Function.Injective (g s)) → (∀ s, s.Nonempty → LinearMap.range (g s) = A s) →
    (∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) →
    ∀ n : ℕ, ∃ e : (cechComplex C).homology n ≃ₗ[R] (GlobalTheory.PD.cech A).H (n : ℤ),
      (∀ (z : LinearMap.ker (Cube.d C (n + 1))) (w : (GlobalTheory.PD.cech A).Z (n : ℤ)),
        (∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (z.1 t)) →
        e (cechClass C n z) = Submodule.Quotient.mk w) ∧
      (∀ z : LinearMap.ker (Cube.d C (n + 1)), ∃ w : (GlobalTheory.PD.cech A).Z (n : ℤ),
        ∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (z.1 t)) ∧
      (∀ (x : Cube.Term C (n + 1)) (w : (GlobalTheory.PD.cech A).Z (n : ℤ)),
        (∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (x t)) →
        Cube.d C (n + 1) x = 0) := by
  intro R _ ι _ E _ _ A C g hinj hrange hres n
  let e : (cechComplex C).homology n ≃ₗ[R] (GlobalTheory.PD.cech A).H (n : ℤ) :=
    ((cechClass C n).quotKerEquivOfSurjective (cechClass_surjective C n)).symm.trans
      ((Submodule.quotEquivOfEq _ _ (ker_cocMap hinj hrange hres n)).trans
        ((cocMap hrange hres n).quotKerEquivOfSurjective (cocMap_surjective hinj hrange hres n)))
  have he : ∀ z, e (cechClass C n z) = cocMap hrange hres n z := by
    intro z
    have h1 : ((cechClass C n).quotKerEquivOfSurjective (cechClass_surjective C n)).symm
        (cechClass C n z) = Submodule.Quotient.mk z := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [e, LinearEquiv.trans_apply, h1, Submodule.quotEquivOfEq_mk]
    rfl
  refine ⟨e, fun z w hw => ?_, fun z => ⟨⟨_, famMap_mem_Z hrange hres n z⟩, fun t => ?_⟩,
    fun x w hw => ?_⟩
  · rw [he, cocMap_apply]
    congr 1
    exact Subtype.ext (famMap_eq_of_agree z.1 (Submodule.mem_inf.1 w.2).1 hw)
  · exact famMap_of_eq g z.1 t.2
  · have hx := famMap_eq_of_agree x (Submodule.mem_inf.1 w.2).1 hw
    apply famMap_injective hinj (n + 1)
    rw [famMap_d hres, hx, map_zero]
    exact LinearMap.mem_ker.1 (Submodule.mem_inf.1 w.2).2

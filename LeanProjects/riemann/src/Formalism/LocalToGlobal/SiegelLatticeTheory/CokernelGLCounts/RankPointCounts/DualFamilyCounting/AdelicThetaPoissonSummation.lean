import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOrthTransfer

noncomputable section

open Module

namespace Formalism.L2.SG.Pf.G4

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}

def NondegOn (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) : Prop :=
  ∀ ξ ∈ W, ξ ≠ 0 → ∃ w ∈ W, h w ξ ≠ 0

theorem exists_primitive' (hS : IsHermSemilocal S) (hM : IsLatIn S h W M) {ξ w : V} (hξ : ξ ∈ W)
    (hw : w ∈ W) (hn : h w ξ ≠ 0) :
    ∃ l : K, l ≠ 0 ∧ l • ξ ∈ M ∧ ∀ c : K, c • ξ ∈ M → c * l⁻¹ ∈ S := by
  obtain ⟨t, ht0, htM⟩ := hM.span w hw
  have hsp := hM.span ξ hξ
  let A : AddSubgroup K :=
    { carrier := {c | c • ξ ∈ M}
      add_mem' := fun {a b} ha hb => by
        show (a + b) • ξ ∈ M
        rw [add_smul]
        exact M.add_mem ha hb
      zero_mem' := by
        show (0 : K) • ξ ∈ M
        rw [zero_smul]
        exact M.zero_mem
      neg_mem' := fun {a} ha => by
        show (-a) • ξ ∈ M
        rw [neg_smul]
        exact M.neg_mem ha }
  have hA : ∀ c, c ∈ A ↔ c • ξ ∈ M := fun c => Iff.rfl
  obtain ⟨α, hαA, hα0, hα⟩ := hS.principal A
    (fun s hs a ha => by
      rw [hA] at ha ⊢
      rw [mul_smul]
      exact hM.smul_mem s hs _ ha)
    (by
      obtain ⟨t', ht'0, ht'M⟩ := hsp
      exact ⟨t', (hA t').2 ht'M, ht'0⟩)
    ⟨star t * h w ξ, mul_ne_zero (star_ne_zero.2 ht0) hn, fun a ha => by
      rw [hA] at ha
      have hi := hM.int _ htM _ ha
      have e : h (t • w) (a • ξ) = star t * h w ξ * a := by
        rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, starRingEnd_apply]
        ring
      rw [← e]
      exact hi⟩
  exact ⟨α, hα0, (hA α).1 hαA, fun c hc => hα c ((hA c).2 hc)⟩

theorem exists_primitive_norm' (hS : IsHermSemilocal S) (hM : IsLatIn S h W M) {ξ : V} (hξ : ξ ∈ W)
    {u : K} (hu : IsUnitIn S u) (hξu : h ξ ξ = u) :
    ∃ y ∈ M, y ≠ 0 ∧ (∃ l : K, y = l • ξ) ∧ (∀ c : K, c • y ∈ M → c ∈ S) ∧
      ∃ a ∈ S, h y y = star a * a * u := by
  have hu0 : u ≠ 0 := hu.1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    apply hu0
    rw [← hξu]
    simp
  obtain ⟨l, hl0, hlM, hprim⟩ := exists_primitive' hS hM hξ hξ (by rw [hξu]; exact hu0)
  have hyy : h (l • ξ) (l • ξ) = star l * l * u := by
    rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, starRingEnd_apply, hξu]
    ring
  have hN : star l * l ∈ S := by
    have hi := hM.int _ hlM _ hlM
    rw [hyy] at hi
    have e := S.mul_mem hi hu.2.2
    rwa [mul_assoc, mul_inv_cancel₀ hu0, mul_one] at e
  obtain ⟨b, hb1, hbS⟩ := Formalism.HermitianLattices.Ext.L3.WA.exists_norm_one_mul_mem hS hN
  refine ⟨l • ξ, hlM, smul_ne_zero hl0 hξ0, ⟨l, rfl⟩, fun c hc => ?_, l * b, hbS, ?_⟩
  · have e := hprim (c * l) (by rwa [mul_smul])
    rwa [mul_assoc, mul_inv_cancel₀ hl0, mul_one] at e
  · rw [hyy, star_mul]
    linear_combination (-(star l * l * u)) * hb1

theorem IsSD.exists_norm' (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hM : IsSD S h W M) {ξ : V} (hξ : ξ ∈ W) {u : K}
    (hu : IsUnitIn S u) (hξu : h ξ ξ = u) : ∃ X ∈ M, h X X = u := by
  obtain ⟨y, hy, -, -, hprim, a, ha, hyy⟩ := exists_primitive_norm' hS hM.toIsLatIn hξ hu hξu
  obtain ⟨w, hw, hn⟩ := hM.exists_not_dv hπ hy hprim
  have huf : star u = u := by
    have e : starRingEnd K (h ξ ξ) = h ξ ξ := by
      first
        | exact hs ξ ξ
        | exact hs.eq ξ ξ
    rw [hξu, starRingEnd_apply] at e
    exact e
  exact exists_norm_of_not_dv hS hπ hs hM.smul_mem hM.int hy hw ha hu huf hyy hn

theorem IsSD.exists_unit_norm' (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hnd : NondegOn h W) (hM : IsSD S h W M) {ξ : V} (hξ : ξ ∈ W) (hξ0 : ξ ≠ 0) :
    ∃ x ∈ M, IsUnitIn S (h x x) := by
  obtain ⟨w, hw, hn⟩ := hnd ξ hξ hξ0
  obtain ⟨l, hl0, hlM, hprim⟩ := exists_primitive' hS hM.toIsLatIn hξ hw hn
  have hprim' : ∀ c : K, c • (l • ξ) ∈ M → c ∈ S := by
    intro c hc
    have e := hprim (c * l) (by rwa [mul_smul])
    rwa [mul_assoc, mul_inv_cancel₀ hl0, mul_one] at e
  obtain ⟨w', hw', hn'⟩ := hM.exists_not_dv hπ hlM hprim'
  exact exists_unit_norm hS hπ hs hM.smul_mem hM.int hlM hw' hn'

theorem nondegOn_cut (hnd : NondegOn h W) {x : V} (hx : x ∈ W) (hxx : h x x ≠ 0) :
    NondegOn h (cutW h W x) := by
  intro ξ hξ hξ0
  rw [mem_cutW] at hξ
  obtain ⟨w, hw, hwξ⟩ := hnd ξ hξ.1 hξ0
  refine ⟨w - (h x w * (h x x)⁻¹) • x, ?_, ?_⟩
  · rw [mem_cutW]
    refine ⟨W.sub_mem hw (W.smul_mem _ hx), ?_⟩
    rw [map_sub, map_smul, smul_eq_mul, inv_mul_cancel_right₀ hxx, sub_self]
  · rw [map_sub, LinearMap.sub_apply, map_smulₛₗ, LinearMap.smul_apply, hξ.2, smul_zero, sub_zero]
    exact hwξ

end Formalism.L2.SG.Pf.G4

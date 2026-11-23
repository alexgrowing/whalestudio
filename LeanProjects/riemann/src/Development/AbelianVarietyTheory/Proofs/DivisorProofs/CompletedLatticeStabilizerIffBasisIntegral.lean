import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatStab

section Core

variable {B : Type} [CommRing B] {n : ℕ}

theorem mulVec_mem_iff (S : Subring B) (y : Matrix (Fin n) (Fin n) B) :
    (∀ v : Fin n → B, (∀ i, v i ∈ S) → ∀ i, y.mulVec v i ∈ S) ↔ ∀ i j, y i j ∈ S := by
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      rcases eq_or_ne k j with rfl | hk
      · simp
      · simp [hk]) i
    simpa using this
  · intro h v hv i
    show ∑ j, y i j * v j ∈ S
    exact S.sum_mem fun j _ => S.mul_mem (h i j) (hv j)

theorem exists_int_iff (S : Subring B) (y : GL (Fin n) B) :
    (∃ u : GL (Fin n) S, u.val.map S.subtype = y.val) ↔
      (∀ i j, y.val i j ∈ S) ∧ ∀ i j, (y⁻¹).val i j ∈ S := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : Units.map (S.subtype.mapMatrix (m := Fin n)).toMonoidHom u = y := Units.ext hu
    subst h1
    refine ⟨fun i j => (u.val i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((u⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    have inj : Function.Injective (S.subtype.mapMatrix (m := Fin n)) :=
      Matrix.map_injective S.subtype_injective
    let a : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h1 i j⟩
    let b : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h2 i j⟩
    have ha : S.subtype.mapMatrix a = y.val := rfl
    have hb : S.subtype.mapMatrix b = (y⁻¹).val := rfl
    refine ⟨⟨a, b, inj ?_, inj ?_⟩, rfl⟩
    · rw [map_mul, ha, hb, map_one, Units.mul_inv]
    · rw [map_mul, ha, hb, map_one, Units.inv_mul]

theorem image_eq_iff {A : Type} [CommRing A] (e : A →+* B) (he : Function.Bijective e) (S : Subring B)
    (β x : GL (Fin n) B) (k : GL (Fin n) A) (hx : x.val = k.val.map e) (L : Set (Fin n → A))
    (hL : ∀ z, z ∈ L ↔ ∀ i, (β⁻¹).val.mulVec (fun a => e (z a)) i ∈ S) :
    k.val.mulVec '' L = L ↔ ∃ u : GL (Fin n) S, u.val.map S.subtype = (β⁻¹ * x * β).val := by
  have key : ∀ (x : GL (Fin n) B) (k : GL (Fin n) A), x.val = k.val.map e →
      ((∀ z ∈ L, k.val.mulVec z ∈ L) ↔ ∀ i j, (β⁻¹ * x * β).val i j ∈ S) := by
    intro x k hx
    have hm : ∀ z : Fin n → A, (β⁻¹).val.mulVec (fun a => e (k.val.mulVec z a)) =
        (β⁻¹ * x * β).val.mulVec ((β⁻¹).val.mulVec (fun a => e (z a))) := by
      intro z
      have : (fun a => e (k.val.mulVec z a)) = x.val.mulVec (fun a => e (z a)) := by
        funext a
        rw [hx, RingHom.map_mulVec]; rfl
      rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
        mul_inv_cancel_right]
    rw [← mulVec_mem_iff]
    constructor
    · intro h v hv
      choose z hz using fun a => he.2 (β.val.mulVec v a)
      have hz' : (β⁻¹).val.mulVec (fun a => e (z a)) = v := by
        rw [show (fun a => e (z a)) = β.val.mulVec v from funext hz, Matrix.mulVec_mulVec, Units.inv_mul,
          Matrix.one_mulVec]
      have := (hL _).1 (h z ((hL z).2 (by rw [hz']; exact hv)))
      rwa [hm, hz'] at this
    · intro h z hz
      rw [hL, hm]
      exact h _ ((hL z).1 hz)
  have hx' : (x⁻¹).val = (k⁻¹).val.map e := by
    have h1 : Units.map (e.mapMatrix (m := Fin n)).toMonoidHom k = x := Units.ext hx.symm
    rw [← h1, ← map_inv]; rfl
  have hi : (β⁻¹ * x * β)⁻¹ = β⁻¹ * x⁻¹ * β := by group
  rw [exists_int_iff, hi, ← key x k hx, ← key x⁻¹ k⁻¹ hx']
  constructor
  · intro h
    refine ⟨fun z hz => h ▸ ⟨z, hz, rfl⟩, fun z hz => ?_⟩
    rw [← h] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  · rintro ⟨h1, h2⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact h1 z hz
    · intro z hz
      exact ⟨_, h2 z hz, by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩

end Core

theorem mem_St_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    x ∈ Formalism.L2.DIV.St β ↔ ∃ u : GL (Fin n) (Formalism.L2.Herm.intAf F E),
      u.val.map (Formalism.L2.Herm.intAf F E).subtype = (β⁻¹ * x * β).val := by
  refine exists_congr fun u => ?_
  show β * Formalism.L2.DIV.intGL F E n u * β⁻¹ = x ↔ (Formalism.L2.DIV.intGL F E n u).val = _
  rw [← Units.ext_iff]
  constructor
  · rintro rfl; group
  · intro h; rw [h]; group

theorem gLat_eq_latHat_iff : ∀ (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)), LatticeBasisLifts.IsLatBasis V hr β → ∀ κ : GA D V, gLat V κ = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) ↔ LatticeBasisLifts.finR V hr κ ∈ Formalism.L2.DIV.St β := by
  intro D V r hr β hβ κ
  subst hr
  rw [mem_St_iff]
  exact image_eq_iff (swapAE D) (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).bijective
    (LatticeBasisLifts.OAf D) β _ (finHom V κ) rfl _ hβ

end GlobalTheory.LatStab

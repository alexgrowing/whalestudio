import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogDerLoc

def dualHom {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (D : Derivation ℤ A A) :
    A →+* TrivSqZeroExt B B where
  toFun r := TrivSqZeroExt.inl (φ r) + TrivSqZeroExt.inr (φ (D r))
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · simp
    · simp [D.leibniz, mul_comm, -DualNumber.inr_eq_smul_eps]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [-DualNumber.inr_eq_smul_eps]

theorem exists_extension {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (f : A) [IsLocalization.Away f B]
    (D : Derivation ℤ A A) : ∃ E : Derivation ℤ B B, ∀ r, E (algebraMap A B r) = algebraMap A B (D r) := by
  have hu : IsUnit (dualHom (algebraMap A B) D f) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
      simpa [dualHom] using IsLocalization.Away.algebraMap_isUnit (S := B) f)
  let L : B →+* TrivSqZeroExt B B := IsLocalization.Away.lift f hu
  have hfst : ∀ x, (L x).fst = x := fun x => by
    have : (TrivSqZeroExt.fstHom B _ _).toRingHom.comp L = RingHom.id _ := by
      refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun r => ?_)
      simp [L, dualHom]
    exact congr($this x)
  let e : B →+ B :=
    { toFun := fun x => (L x).snd
      map_zero' := by rw [map_zero, TrivSqZeroExt.snd_zero]
      map_add' := fun x y => by rw [map_add, TrivSqZeroExt.snd_add] }
  refine ⟨Derivation.mk' e.toIntLinearMap fun x y => ?_, fun r => ?_⟩
  · change (L (x * y)).snd = x • (L y).snd + y • (L x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [mul_comm]
  · change (L (algebraMap A B r)).snd = _
    simp [L, dualHom, -DualNumber.inr_eq_smul_eps]

theorem map_mem_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (D : Derivation ℤ A A)
    (E : Derivation ℤ B B) (h : ∀ r, E (φ r) = φ (D r)) (J : Ideal A) (hJ : ∀ g ∈ J, D g ∈ J) :
    ∀ x ∈ J.map φ, E x ∈ J.map φ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [h]
    exact Ideal.mem_map_of_mem φ (hJ g hg)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x hx hE =>
    rw [smul_eq_mul, E.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ a hE) (Ideal.mul_mem_right _ _ hx)

theorem exists_logDer_basicOpen : ∀ (X : Scheme.{0}) (K : Type) [CommRing K] (s : X ⟶ Sp K) (I : X.IdealSheafData) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ Dl ∈ GlobalTheory.LogKS.logDer s I U, ∃ DlW ∈ GlobalTheory.LogKS.logDer s I W, ∀ r, DlW ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (Dl r) := by
  intro X K _ s I U W hW f hf Dl hD
  obtain rfl : W = X.affineBasicOpen f := Subtype.ext hf
  haveI : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  obtain ⟨E, hE⟩ := exists_extension (B := Γ(X, X.basicOpen f)) f Dl
  have hE' : ∀ r, E ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (Dl r) := hE
  refine ⟨E, ⟨fun a => ?_, ?_⟩, hE'⟩
  · have hc : (X.presheaf.map (homOfLE hW).op).hom (constFn s U.1 a) = constFn s (X.affineBasicOpen f).1 a := by
      exact congr(($(Scheme.Hom.appLE_map s (U := ⊤) (V := U.1) (fun _ _ => trivial) (homOfLE hW).op)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    have := hE' (constFn s U.1 a)
    rw [hc, hD.1 a, map_zero] at this
    exact this
  · rw [← I.map_ideal_basicOpen U f]
    exact map_mem_map _ Dl E hE' _ hD.2

end GlobalTheory.LogDerLoc

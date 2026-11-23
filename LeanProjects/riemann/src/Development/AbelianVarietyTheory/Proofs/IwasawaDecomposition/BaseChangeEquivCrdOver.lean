import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.GeoFW

open GlobalTheory.Mem.R3.Rw

variable {LL LL' Ks : Type} [Field LL] [Field LL'] [Field Ks] [Algebra Ks LL] [Algebra Ks LL']

def crdMap (ι : LL →+* LL') {n n' : ℕ} (hn : n = n') (x : Fin n → LL) : Fin n' → LL' := fun k' => ι (x (Fin.cast hn.symm k'))

theorem crdOver_crdMap (ι : LL →+* LL') {n n' : ℕ} (hn : n = n') (x : Fin n → LL) : CrdOver ι x (crdMap ι hn x) :=
  ⟨hn, fun k k' hk => by
    unfold crdMap
    congr 2
    exact Fin.ext (by simp [hk])⟩

theorem crdMap_eq_of_crdOver (ι : LL →+* LL') {n n' : ℕ} (hn : n = n') {x : Fin n → LL} {x' : Fin n' → LL'}
    (h : CrdOver ι x x') : crdMap ι hn x = x' := by
  funext k'
  exact (h.2 (Fin.cast hn.symm k') k' rfl).symm

def crdLin (ι : LL →+* LL') (hι : ∀ y, ι (algebraMap Ks LL y) = algebraMap Ks LL' y) {n n' : ℕ} (hn : n = n') :
    (Fin n → LL) →ₗ[Ks] (Fin n' → LL') where
  toFun := crdMap ι hn
  map_add' x y := by funext k; simp [crdMap]
  map_smul' c x := by funext k; simp [crdMap, Algebra.smul_def, hι]

theorem crdMap_injective (ι : LL →+* LL') {n n' : ℕ} (hn : n = n') : Function.Injective (crdMap ι hn) := by
  intro x y h
  funext k
  have := congrFun h (Fin.cast hn k)
  simp only [crdMap, Fin.cast_cast, Fin.cast_eq_self] at this
  exact ι.injective this

def baseChangeEquiv (ι : LL →+* LL') (hι : ∀ y, ι (algebraMap Ks LL y) = algebraMap Ks LL' y) {n n' : ℕ} (hn : n = n')
    (WK : Submodule Ks (Fin n → LL)) (WK' : Submodule Ks (Fin n' → LL'))
    (hmem : ∀ x x', CrdOver ι x x' → (x' ∈ WK' ↔ x ∈ WK)) (honto : ∀ x' ∈ WK', ∃ x : Fin n → LL, CrdOver ι x x') : WK ≃ₗ[Ks] WK' :=
  LinearEquiv.ofBijective
    (((crdLin ι hι hn).comp WK.subtype).codRestrict WK' fun x => (hmem _ _ (crdOver_crdMap ι hn x.1)).2 x.2)
    ⟨fun x y h => Subtype.ext (crdMap_injective ι hn (congrArg Subtype.val h)), fun x' => by
      obtain ⟨x, hx⟩ := honto x'.1 x'.2
      exact ⟨⟨x, (hmem _ _ hx).1 x'.2⟩, Subtype.ext (crdMap_eq_of_crdOver ι hn hx)⟩⟩

theorem baseChangeEquiv_crdOver (ι : LL →+* LL') (hι : ∀ y, ι (algebraMap Ks LL y) = algebraMap Ks LL' y) {n n' : ℕ}
    (hn : n = n') (WK : Submodule Ks (Fin n → LL)) (WK' : Submodule Ks (Fin n' → LL'))
    (hmem : ∀ x x', CrdOver ι x x' → (x' ∈ WK' ↔ x ∈ WK)) (honto : ∀ x' ∈ WK', ∃ x : Fin n → LL, CrdOver ι x x') (x : WK) :
    CrdOver ι x.1 (baseChangeEquiv ι hι hn WK WK' hmem honto x).1 :=
  crdOver_crdMap ι hn x.1

end GlobalTheory.Mem.R3.Rw.GeoFW

end

import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.SmoothColumnLifts.SmoothCol
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.BesselAbs

noncomputable section

open Matrix GlobalTheory.SplitWeil GlobalTheory.BZMir
open scoped Topology

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

theorem lat_gmap (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (hA : Lat A) : Lat (gmap g A) :=
  AvA.lat_gmap' g A hA

theorem av_conj (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v)) (hsm : ∀ v, IsOpen {x | col x v = v})
    (gl : GL (Fin n) k →* (V →ₗ[ℂ] V))
    (hconj : ∀ g x v, gl g (col x v) = col ((g : Matrix (Fin n) (Fin n) k) *ᵥ x) (gl g v))
    (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (hA : Lat A) (ξ : Fin n → k) (v : V) :
    gl g (av φ col ξ A v) = av φ col (ξ ᵥ* ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (gmap g A) (gl g v) :=
  AvA.av_conj' φ hφ col hc0 hca hsm gl hconj g A hA ξ v

theorem av_bessel (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v)) (hsm : ∀ v, IsOpen {x | col x v = v})
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : Psd B) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
    (A : AddSubgroup (Fin n → k)) (hA : Lat A) (s : Finset (Fin n → k))
    (hs : ∀ ξ ∈ s, ∀ ξ' ∈ s, ξ - ξ' ∈ perp φ A → ξ = ξ') (v : V) :
    ∑ ξ ∈ s, (B (av φ col ξ A v) v).re ≤ (B v v).re :=
  AvA.av_bessel' φ hφ col hc0 hca hsm B hB hBc A hA s hs v

end PositivityTheory.RgUd.Form.U.Lift2

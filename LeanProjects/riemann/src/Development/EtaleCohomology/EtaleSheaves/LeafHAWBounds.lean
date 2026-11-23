import Development.EtaleCohomology.EtaleSheaves.LeafTwPairUniquePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafHtpyAWPf

abbrev HFam (R : Type) [CommRing R] (I J K : Cx R) : Type 1 :=
  ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w + 1 →
    Sec (I.X s) U →ₗ[ULift.{1} R] Sec (J.X t) U →ₗ[ULift.{1} R] Sec (K.X w) U

def IsHAW {R : Type} [CommRing R] {I J K : Cx R} (h : HFam R I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (η : Cochain ((chains R).obj E) K (k - 1)) :
    Prop :=
  ∀ (N : ℕ) (w : ℤ) (hw : -(N : ℤ) + (k - 1) = w) (U : Scheme.{0}) (x : Sx E N U), ev η N w hw U x =
    ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow • h U (-((p : ℕ) : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev α p _ rfl U (x.sub 0 p (by omega))) (ev β (N - p) _ rfl U (x.sub p (N - p) (by omega)))

def LeafHAWExists : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (h : HFam R I J K),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (hw : s + t = w + 1) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.res g (h U s t w hw a b) = h V s t w hw (Sec.res g a) (Sec.res g b)) →
  ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m),
    ∃ η : Cochain ((chains R).obj E) K (k - 1), IsHAW h hk α β η

def LeafHAWBounds : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ μ' : Pair I J K) (h : HFam R I J K),
  (∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    μ.mul U s t w hw a b - μ'.mul U s t w hw a b =
      Sec.map (K.d (w - 1) w) (h U s t (w - 1) (by omega) a b) +
        h U (s + 1) t w (by omega) (Sec.map (I.d s (s + 1)) a) b +
        s.negOnePow • h U s (t + 1) w (by omega) a (Sec.map (J.d t (t + 1)) b)) →
  ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ γ' : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ'.IsAW hk α.1 β.1 γ'.1 →
    ∀ η : Cochain ((chains R).obj E) K (k - 1), IsHAW h hk α.1 β.1 η → δ (k - 1) k η = γ.1 - γ'.1

end LateralTheory.E.LeafHtpyAWPf

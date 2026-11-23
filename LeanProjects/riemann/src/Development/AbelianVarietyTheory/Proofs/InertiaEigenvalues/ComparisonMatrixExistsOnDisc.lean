import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTwoHomsERegularAssociatedStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.RelEx

theorem map_smul_ring {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m n : Type} (a : R)
    (M : Matrix m n R) : (a • M).map φ = φ a • M.map φ := by
  ext i j; simp

theorem alg {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (N : ℕ)
    (A Zf Zfi G Y Zg : Matrix n n R) (gE fE wi c lam : R) (hZ : Zf * Zfi = 1) (hAG : A * G = lam • Y)
    (hw : gE * wi = fE) (hc : c * lam = 1) :
    gE ^ N • (A * Zf * ((wi ^ N * c) • (Zfi * G * Zg))) = fE ^ N • (Y * Zg) := by
  have h1 : A * Zf * (Zfi * G * Zg) = lam • (Y * Zg) := by
    rw [Matrix.mul_assoc A Zf, ← Matrix.mul_assoc Zf, ← Matrix.mul_assoc Zf, hZ, Matrix.one_mul,
      ← Matrix.mul_assoc, hAG, Matrix.smul_mul]
  rw [Matrix.mul_smul, h1, smul_smul, smul_smul]
  congr 1
  calc gE ^ N * (wi ^ N * c) * lam = (gE * wi) ^ N * (c * lam) := by ring
    _ = fE ^ N := by rw [hw, hc, mul_one]

theorem cancel {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (Xf X'f Y G : Matrix n n R)
    (e lk lc : R) (he : e ∈ nonZeroDivisors R) (hXX : Xf * X'f = (lc * e) • 1) (hG : e • G = lk • (X'f * Y)) :
    Xf * G = (lk * lc) • Y := by
  have h2 : e • (Xf * G) = e • ((lk * lc) • Y) := by
    rw [← Matrix.mul_smul, hG, Matrix.mul_smul, ← Matrix.mul_assoc, hXX, Matrix.smul_mul, Matrix.one_mul,
      smul_smul, smul_smul]
    congr 1; ring
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h3
  exact (mul_cancel_left_mem_nonZeroDivisors he).1 h3

theorem map_unit_eq {R S : Type} [CommRing R] [CommRing S] (T : R →+* S) (a b : R) (w : Rˣ) (hw : a * w = b) :
    T b * T (↑w⁻¹ : R) = T a := by
  rw [← hw, ← map_mul, mul_assoc, Units.mul_inv, mul_one]

theorem inv_pow_map {R S : Type} [CommRing R] [CommRing S] (T : R →+* S) (x : R) (li : S) (h : li * T x = 1)
    (m : ℕ) : li ^ m * T (x ^ m) = 1 := by
  rw [map_pow, ← mul_pow, h, one_pow]

end GlobalTheory.BSP.RelEx

namespace GlobalTheory.BSP.Height

open GlobalTheory.BSP.RelEx

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}
  {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {τ : Ainf l} {s : Seed bk d ρ τ} (ht : Height s)

theorem bas_map_disc {B : Obj l ↥(OL K)} (u : B.A) (h : Hom bk.prism B) (F : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀)
    (hF : IsDiscMap (BK.hf h) F) :
    ht.bas.map F = (s.X.map (BK.hf h)).map (toDisc l u bk.ρ₀) * ht.Z.map F := by
  rw [Height.bas, Matrix.map_mul]
  congr 1
  ext i j
  simp only [Matrix.map_apply]
  exact hF.ext _

theorem rel_exists_of {B : Obj l ↥(OL K)} (u : B.A) (f g : Hom bk.prism B)
    (Ff Fg : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀) (hF : IsDiscMap (BK.hf f) Ff) (hG : IsDiscMap (BK.hf g) Fg)
    (w : B.Aˣ) (hw : BK.hf f bk.E * w = BK.hf g bk.E) (G : Matrix (Fin d) (Fin d) B.A) (m : ℕ)
    (hAG : s.X.map (BK.hf f) * G = (l : B.A) ^ m • s.X.map (BK.hf g)) :
    ∃ ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀), ht.Rel u f g ε := by
  obtain ⟨Z', hZ'⟩ : ∃ Z', ht.Z * Z' = 1 := by
    obtain ⟨U, hU⟩ := ht.Z_unit
    exact ⟨↑U⁻¹, by rw [← hU]; exact U.mul_inv⟩
  obtain ⟨li, hli⟩ : ∃ li : Disc l u bk.ρ₀, li * toDisc l u bk.ρ₀ (l : B.A) = 1 :=
    ((IsLocalization.Away.algebraMap_isUnit (S := PreDisc l u bk.ρ₀) (l : B.A)).map (ofPre l u bk.ρ₀)).exists_left_inv
  have key : toDisc l u bk.ρ₀ (BK.hf g bk.E) ^ s.N • (ht.bas.map Ff *
      ((toDisc l u bk.ρ₀ (↑w⁻¹ : B.A) ^ s.N * li ^ m) •
        (Z'.map Ff * G.map (toDisc l u bk.ρ₀) * ht.Z.map Fg))) =
      toDisc l u bk.ρ₀ (BK.hf f bk.E) ^ s.N • ht.bas.map Fg := by
    have e1 := ht.bas_map_disc u f Ff hF
    have e2 := ht.bas_map_disc u g Fg hG
    have h4 := alg s.N ((s.X.map (BK.hf f)).map (toDisc l u bk.ρ₀)) (ht.Z.map Ff) (Z'.map Ff)
      (G.map (toDisc l u bk.ρ₀)) ((s.X.map (BK.hf g)).map (toDisc l u bk.ρ₀)) (ht.Z.map Fg)
      (toDisc l u bk.ρ₀ (BK.hf g bk.E)) (toDisc l u bk.ρ₀ (BK.hf f bk.E))
      (toDisc l u bk.ρ₀ (↑w⁻¹ : B.A)) (li ^ m) (toDisc l u bk.ρ₀ ((l : B.A) ^ m))
      (by rw [← Matrix.map_mul, hZ', Matrix.map_one _ (map_zero _) (map_one _)])
      (by rw [← Matrix.map_mul, hAG, map_smul_ring])
      (map_unit_eq _ _ _ w hw)
      (inv_pow_map _ _ li hli m)
    exact (congrArg (fun M => toDisc l u bk.ρ₀ (BK.hf g bk.E) ^ s.N • (M *
      ((toDisc l u bk.ρ₀ (↑w⁻¹ : B.A) ^ s.N * li ^ m) • (Z'.map Ff * G.map (toDisc l u bk.ρ₀) * ht.Z.map Fg)))) e1).trans
      (h4.trans (congrArg (fun M => toDisc l u bk.ρ₀ (BK.hf f bk.E) ^ s.N • M) e2.symm))
  refine ⟨(toDisc l u bk.ρ₀ (↑w⁻¹ : B.A) ^ s.N * li ^ m) •
    (Z'.map Ff * G.map (toDisc l u bk.ρ₀) * ht.Z.map Fg), ?_⟩
  unfold Height.Rel
  intro Ff' Fg' hF' hG'
  have e1 : Ff' = Ff := (hF.unique hF').symm
  have e2 : Fg' = Fg := (hG.unique hG').symm
  subst e1 e2
  exact key

end GlobalTheory.BSP.Height

namespace GlobalTheory.BSP.Height

open GlobalTheory.BSP.RelEx

theorem rel_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (B : Obj l ↥(OL K)) (u : B.A) (f g : Hom bk.prism B),
    ∃ ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀), ht.Rel u f g ε := by
  intro l _ K bk d ρ τ s ht B u f g
  by_cases hex : ∃ Ff Fg : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀, IsDiscMap (BK.hf f) Ff ∧ IsDiscMap (BK.hf g) Fg
  swap
  · refine ⟨0, ?_⟩
    unfold Height.Rel
    intro Ff Fg hF hG
    exact (hex ⟨Ff, Fg, hF, hG⟩).elim
  obtain ⟨Ff, Fg, hF, hG⟩ := hex
  obtain ⟨hreg, ⟨w, hw⟩, -⟩ := GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f g
  obtain ⟨k, hk⟩ := s.nopole f g
  choose G hGc using hk
  have hXX : s.X.map (BK.hf f) * s.X'.map (BK.hf f) = ((l : B.A) ^ s.c₂ * BK.hf f bk.E ^ (2 * s.N)) • 1 := by
    rw [← Matrix.map_mul, s.X_mul, map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _)]
    simp
  have hGm : BK.hf f bk.E ^ (2 * s.N) • Matrix.of G = (l : B.A) ^ k • (s.X'.map (BK.hf f) * s.X.map (BK.hf g)) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    exact (hGc i j).symm
  have hAG : s.X.map (BK.hf f) * Matrix.of G = (l : B.A) ^ (k + s.c₂) • s.X.map (BK.hf g) := by
    rw [pow_add]
    exact cancel _ _ _ _ _ _ _ (pow_mem hreg _) (by rw [hXX, mul_comm]) hGm
  exact ht.rel_exists_of u f g Ff Fg hF hG w hw (Matrix.of G) (k + s.c₂) hAG

end GlobalTheory.BSP.Height

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEqAevalOfCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormConjNormalizeAndDegreeOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormProductIterateTwistedConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleFrobeniusTwistOrderFixedPointsStatement

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.CarryCent

theorem commute_of_commute_sep {K : Type} [Field K] {n : ℕ} (N A B : Matrix (Fin n) (Fin n) K)
    (hN : N.charpoly.Separable) (hA : Commute A N) (hB : Commute B N) : Commute A B := by
  obtain ⟨q, rfl⟩ := GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute n N A hN hA
  obtain ⟨q', rfl⟩ := GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute n N B hN hB
  change _ * _ = _ * _
  rw [← map_mul, ← map_mul, mul_comm]

theorem map_coord_commute {K R : Type} [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) (Fin n) R)
    (hX : Commute X (N.map (algebraMap K R))) (f : R →ₗ[K] K) : Commute (X.map f) N := by
  have k1 : (X * N.map (algebraMap K R)).map f = X.map f * N := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have k2 : (N.map (algebraMap K R) * X).map f = N * X.map f := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have h := congrArg (fun Y => Y.map f) hX.eq
  simp only [k1, k2] at h
  exact h

theorem commute_of_commute_map {K R : Type} [Field K] [CommRing R] [Algebra K R] [Module.Finite K R] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K) (hN : N.charpoly.Separable) (X Y : Matrix (Fin n) (Fin n) R)
    (hX : Commute X (N.map (algebraMap K R))) (hY : Commute Y (N.map (algebraMap K R))) : Commute X Y := by
  let b := Module.Free.chooseBasis K R
  have dec : ∀ Z : Matrix (Fin n) (Fin n) R, Z = ∑ k, b k • (Z.map (b.coord k)).map (algebraMap K R) := by
    intro Z
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, Module.Basis.coord_apply, smul_eq_mul]
    conv_lhs => rw [← b.sum_repr (Z i j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, mul_comm]
  rw [dec X, dec Y]
  refine Commute.sum_left _ _ _ fun k _ => Commute.sum_right _ _ _ fun l _ => ?_
  refine ((Commute.map ?_ (algebraMap K R).mapMatrix).smul_left _).smul_right _
  exact commute_of_commute_sep N _ _ hN (map_coord_commute N X hX _) (map_coord_commute N Y hY _)

variable {p : ℕ} [Fact p.Prime]

theorem commute_of_commute_reg (G : HTGroup p) (r : ℕ) (hr : 0 < r) (γ : Gp G) (hγ : regular₂ G γ) (a b : Gr G r)
    (ha : Commute a (inclG G r γ)) (hb : Commute b (inclG G r γ)) : Commute a b := by
  refine Prod.ext ?_ (funext fun w => ?_)
  · change a.1 * b.1 = b.1 * a.1
    apply Units.ext
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Matrix.mul_apply, mul_comm]
  · change a.2 w * b.2 w = b.2 w * a.2 w
    letI : Algebra (G.Fw w) (KQ p (G.Fw w) r) := Algebra.TensorProduct.leftAlgebra
    haveI : FiniteDimensional ℚ_[p] (Qr p r) :=
      ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr
    haveI : Module.Finite (G.Fw w) (KQ p (G.Fw w) r) :=
      inferInstanceAs (Module.Finite (G.Fw w) ((G.Fw w) ⊗[ℚ_[p]] Qr p r))
    have hw : ∀ x : Gr G r, Commute x (inclG G r γ) →
        Commute (x.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r))
          (((γ.2 w : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)).map
            (algebraMap (G.Fw w) (KQ p (G.Fw w) r))) := by
      intro x hx
      have := congrArg (fun y : Gr G r => ((y.2 w : GL (Fin G.n) (KQ p (G.Fw w) r)) :
        Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r))) hx.eq
      exact this
    exact Units.ext (commute_of_commute_map _ (hγ w) _ _ (hw a ha) (hw b hb)).eq

end GlobalTheory.CarryCent

namespace GlobalTheory.CarryCent

variable {p : ℕ} [Fact p.Prime]

theorem map_centralizer_carry : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (γ : Gp G) (δ z : Gr G r),
    0 < r → regular₂ G γ → IsNrm G r γ δ z →
    (Subgroup.centralizer {γ}).map (carry G r z) = GlobalTheory.BCT.twCent (sigG G r) δ := by
  intro p _ G r γ δ z hr hγ hN
  set δ' := z * δ * (sigG G r z)⁻¹ with hδ'
  have hN' : nrmG (sigG G r) r δ' = inclG G r γ := by
    have h := (GlobalTheory.T.twistedNormConj_normalize_and_degree_one p G).1 r γ δ z hr hN
    simpa [IsNrm] using h
  obtain ⟨hit, hfix, hinj, hrange⟩ := GlobalTheory.T.hermitianTripleFrobeniusTwist_order_fixed_points p G r hr
  have hδc : Commute δ' (inclG G r γ) := by
    have h2 := (GlobalTheory.T.twistedNormProductIterate_twistedConj (sigG G r) r δ' 1).2
    rw [hN', hfix, hit] at h2
    exact h2
  have memT : ∀ h, h ∈ GlobalTheory.BCT.twCent (sigG G r) δ' ↔ ∃ g ∈ Subgroup.centralizer {γ}, inclG G r g = h := by
    intro h
    constructor
    · intro hh
      change h * δ' = δ' * sigG G r h at hh
      have hc : Commute h (inclG G r γ) := by
        have h1 := (GlobalTheory.T.twistedNormProductIterate_twistedConj (sigG G r) r δ' h).1
        have e : h⁻¹ * δ' * sigG G r h = δ' := by rw [mul_assoc, ← hh, inv_mul_cancel_left]
        rw [e, hN', hit] at h1
        change h * inclG G r γ = inclG G r γ * h
        calc h * inclG G r γ = h * (h⁻¹ * inclG G r γ * h) := by rw [← h1]
          _ = inclG G r γ * h := by group
      have hcd : Commute h δ' := commute_of_commute_reg G r hr γ hγ h δ' hc hδc
      have hs : sigG G r h = h := mul_left_cancel (hh.symm.trans hcd.eq)
      obtain ⟨g, rfl⟩ := hrange h hs
      refine ⟨g, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hinj
      rw [map_mul, map_mul]
      exact hc.eq
    · rintro ⟨g, hg, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hg
      have hc : Commute (inclG G r g) (inclG G r γ) := by
        change inclG G r g * inclG G r γ = inclG G r γ * inclG G r g
        rw [← map_mul, ← map_mul, hg]
      have hcd := commute_of_commute_reg G r hr γ hγ _ δ' hc hδc
      change inclG G r g * δ' = δ' * sigG G r (inclG G r g)
      rw [hfix]
      exact hcd.eq
  have conjT : ∀ x, x ∈ GlobalTheory.BCT.twCent (sigG G r) δ ↔ z * x * z⁻¹ ∈ GlobalTheory.BCT.twCent (sigG G r) δ' := by
    intro x
    change x * δ = δ * sigG G r x ↔ z * x * z⁻¹ * δ' = δ' * sigG G r (z * x * z⁻¹)
    rw [hδ', map_mul, map_mul, map_inv]
    have e1 : z * x * z⁻¹ * (z * δ * (sigG G r z)⁻¹) = z * (x * δ) * (sigG G r z)⁻¹ := by group
    have e2 : z * δ * (sigG G r z)⁻¹ * (sigG G r z * sigG G r x * (sigG G r z)⁻¹) =
        z * (δ * sigG G r x) * (sigG G r z)⁻¹ := by group
    rw [e1, e2, mul_left_inj, mul_right_inj]
  ext x
  rw [conjT, memT, Subgroup.mem_map]
  refine exists_congr fun g => and_congr_right fun _ => ?_
  change z⁻¹ * inclG G r g * z⁻¹⁻¹ = x ↔ inclG G r g = z * x * z⁻¹
  constructor
  · rintro rfl; group
  · intro e; rw [e]; group

end GlobalTheory.CarryCent

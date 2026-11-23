import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvSelfTwo
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CovariantDerivativeValueCharacterGermsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CanonicalGaugeEigenvectorPairingIntegralStatement

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharValue

def ballIdeal {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
    (hv : v.Integers O) (t : NNReal) (ht : 0 < t) : Ideal O where
  carrier := {y | v (algebraMap O C y) < t}
  zero_mem' := by simpa using ht
  add_mem' := by
    intro a b ha hb
    show v (algebraMap O C (a + b)) < t
    rw [map_add]
    exact v.map_add_lt ha hb
  smul_mem' := by
    intro c a ha
    show v (algebraMap O C (c * a)) < t
    rw [map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv.map_le_one c)) ha

def letterEquiv (Ty : Type) (r : Ty → ℕ) (n : ℕ) : (Σ τ : Ty, Fin (r τ)) × Fin n ≃ Letter Ty r n where
  toFun p := ⟨p.1.1, (p.1.2, p.2)⟩
  invFun l := (⟨l.1, l.2.1⟩, l.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem dAct_mulVec {R : Type} [CommRing R] {d : ℕ} {OE : Type} [CommRing OE] [StarRing OE] (k : Type) [CommRing k]
    [Algebra ℚ k] [Algebra R k] (B : FB R d OE) (a : OE) (u : Fin d → R) (s : R)
    (hu : (linPart (B.A.act a)).mulVec u = s • u) :
    (TB.dAct k B a).mulVec (fun i => algebraMap R k (u i)) = algebraMap R k s • (fun i => algebraMap R k (u i)) := by
  funext i
  have h := congrArg (algebraMap R k) (congrFun hu i)
  simp only [Matrix.mulVec, dotProduct, linPart, Matrix.of_apply, map_sum, map_mul, Pi.smul_apply,
    smul_eq_mul] at h
  simp only [Matrix.mulVec, dotProduct, TB.dAct, FB.actK, MvPowerSeries.coeff_map, Pi.smul_apply, smul_eq_mul]
  exact h

theorem map_boxSer {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {n d : ℕ} (g : Fin n → PS R 1 d) :
    MvPowerSeries.map φ (PowGerm.boxSer g) = PowGerm.boxSer (fun b => MvPowerSeries.map φ (g b)) := by
  unfold PowGerm.boxSer
  rw [map_prod]
  exact Finset.prod_congr rfl fun b _ => (MvPowerSeries.rename_map _ φ (g b)).symm

theorem exists_germ_valuation_eq : ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (d : ℕ) (OE : Type) [CommRing OE] [StarRing OE] (B : FB O d OE) (h : PS C 2 d), B.IsCanonGauge C h → ∀ (w0 : OE) (k n : ℕ) (Ty : Type) [Fintype Ty] (r : Ty → ℕ) [Fintype (Letter Ty r n)] (σ : Ty → (OE →+* O)) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → O), (∀ ℓ a, (linPart (B.A.act a)).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → (∀ τ, ∃ a0, IsUnit (σ τ a0 - σ τ (star a0))) → (∀ x : O, x ≠ 0 → ∃ N : ℕ, v (N : C) < v (algebraMap O C x) ∧ ∀ τ, ∃ a : OE, star a * a = (N : OE) ∧ v (algebraMap O C (σ τ a - 1)) < v (algebraMap O C x)) → ∀ (ty : Fin n → Ty) (P : MvPolynomial (Letter Ty r n) O), (∀ mo ∈ P.support, ∀ ℓ, mo ℓ ≠ 0 → ℓ.1 = ty ℓ.2.2) → ∀ χ : Fin n → PS O 1 d, (∀ b, IsCh B.G.F (χ b)) → MvPolynomial.eval (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) P ≠ 0 → ∃ f : PS O n d, v (nabValN B C h w0 k (MvPowerSeries.map (algebraMap O C) f) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun (ℓ : Letter Ty r n) i => algebraMap O C (u ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map (algebraMap O C) P)) = v (algebraMap O C (MvPolynomial.eval (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) P)) := by
  intro C _ _ v O _ _ hv d OE _ _ B h hg w0 k n Ty _ r _ σ u hu h0 hN ty P hP χ hχ hx
  classical
  obtain ⟨P', rfl⟩ : ∃ P', P = MvPolynomial.rename (letterEquiv Ty r n) P' :=
    ⟨MvPolynomial.rename (letterEquiv Ty r n).symm P, by simp [MvPolynomial.rename_rename]⟩
  rw [MvPolynomial.eval_rename] at hx ⊢
  set y : (Σ τ : Ty, Fin (r τ)) × Fin n → O :=
    (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) ∘ (letterEquiv Ty r n) with hy
  set x : O := MvPolynomial.eval y P' with hxdef
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have hx0 : 0 < v (algebraMap O C x) := by
    rw [pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact fun e => hx (hinj (by rw [e, map_zero]))
  obtain ⟨N, hNlt, ha⟩ := hN x hx
  choose a ha1 ha2 using ha
  have hh : MvPowerSeries.constantCoeff h = 0 := by
    have := congrArg MvPowerSeries.constantCoeff hg.ax0
    rwa [TB.WickVanishing.gt_const_ev_eq _ (TB.WickVanishing.pair_points_zero_constant TB.WickVanishing.gp_zero₂ (TB.WickVanishing.gp_pt 0)), map_zero] at this
  obtain ⟨g, ρ, hρ, hsum⟩ := GlobalTheory.T.covariantDerivative_value_character_germs O d OE C B h hg hinj w0 N k n (ballIdeal hv _ hx0)
    (by show v (algebraMap O C (N : O)) < _; rwa [map_natCast]) (fun b => a (ty b)) (fun _ => 1)
    (fun b => by rw [ha1, mul_one]) (Σ τ : Ty, Fin (r τ)) u (fun b => {l | l.1 = ty b})
    (fun b l => σ l.1 (a (ty b)))
    (fun b l hl => by
      have hl' : l.1 = ty b := hl
      have h2 : v (algebraMap O C (σ l.1 (a (ty b)) - 1)) < v (algebraMap O C x) := by
        rw [hl']; exact ha2 _
      refine ⟨h2, ?_, dAct_mulVec C B _ _ _ (hu l _)⟩
      apply hv.isUnit_of_one'
      have h3 := v.map_one_add_of_lt (lt_of_lt_of_le h2 (hv.map_le_one x))
      rwa [map_sub, map_one, add_sub_cancel] at h3)
    (fun b l hl l' hl' => by
      have e1 : l.1 = ty b := hl
      have e2 : l'.1 = ty b := hl'
      obtain ⟨a0, ha0⟩ := h0 (ty b)
      exact GlobalTheory.T.canonicalGauge_eigenvector_pairing_integral O d OE C B h hg (σ (ty b)) a0 ha0 (u l) (u l') (fun c => e1 ▸ hu l c)
        (fun c => e2 ▸ hu l' c) _)
    χ y (fun b => (hχ b).1)
    (fun b l _ => GlobalTheory.MultiplicativeSeries.main O d B.G (χ b) (hχ b).2 (u l))
    P' (fun mo hmo l b hne => by
      have hmem : Finsupp.mapDomain (letterEquiv Ty r n) mo ∈
          (MvPolynomial.rename (letterEquiv Ty r n) P').support := by
        rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_rename_mapDomain _ (letterEquiv Ty r n).injective]
        exact MvPolynomial.mem_support_iff.1 hmo
      exact hP _ hmem (letterEquiv Ty r n (l, b))
        (by rwa [Finsupp.mapDomain_apply (letterEquiv Ty r n).injective]))
  refine ⟨PowGerm.boxSer g, ?_⟩
  rw [map_boxSer, MvPolynomial.map_rename,
    GlobalTheory.nabValN_boxSer O d OE B C h w0 hh k n _ (Σ τ : Ty, Fin (r τ)) (Letter Ty r n) (letterEquiv Ty r n) _
      (fun l i => algebraMap O C (u l i)) _ (fun _ => rfl) (fun _ => rfl),
    MvPolynomial.support_map_of_injective _ hinj]
  simp only [MvPolynomial.coeff_map]
  rw [hsum, map_add]
  exact v.map_add_eq_of_lt_left hρ

end GlobalTheory.CharValue

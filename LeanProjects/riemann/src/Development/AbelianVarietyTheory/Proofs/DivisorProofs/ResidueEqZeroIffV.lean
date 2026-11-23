import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TypedPartSplitPrimes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

section Hom

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem subst_sum_smul {σ τ ι : Type} [Fintype ι] {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (m : ι → C)
    (f : ι → MvPowerSeries σ C) : subst a (∑ i, m i • f i) = ∑ i, m i • (subst a (f i) : MvPowerSeries τ C) := by
  rw [← substAlgHom_apply ha, map_sum]
  simp only [map_smul, substAlgHom_apply]

theorem isIntHom_comp {d d' d'' : ℕ} {G : LogFGL v d} {G' : LogFGL v d'} {G'' : LogFGL v d''}
    {φ : Fin d' → MvPowerSeries (Fin d) C} {ψ : Fin d'' → MvPowerSeries (Fin d') C}
    {M : Matrix (Fin d') (Fin d) C} {N : Matrix (Fin d'') (Fin d') C}
    (hφ : IsIntHom G G' φ M) (hψ : IsIntHom G' G'' ψ N) :
    IsIntHom G G'' (fun b => subst φ (ψ b)) (N * M) := by
  obtain ⟨hφ0, hφi, hφl⟩ := hφ
  obtain ⟨hψ0, hψi, hψl⟩ := hψ
  have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ0
  have hψs : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  refine ⟨fun b => constantCoeff_subst_eq_zero hφs hφ0 (hψ0 b), fun b => ?_, fun c => ?_⟩
  · exact ptIntSer_subst hφs (fun s => hφi s) (hψi b)
  · rw [← subst_comp_subst_apply hψs hφs, hψl c, subst_sum_smul hφs]
    simp_rw [hφl, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm

end Hom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

section Labels

variable {c : Coeff l} {T : CDVR} (io : c.F →+* T.Fr) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def embO (σ : E →+* ℂ) : 𝓞 E →+* X.O where
  toFun a := (X.ints.exists_of_le_one (v_embX_le_one io X σ a)).choose
  map_one' := X.ints.hom_inj (by rw [(X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_one, map_one])
  map_zero' := X.ints.hom_inj (by
    rw [(X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_zero, map_zero])
  map_mul' a b := X.ints.hom_inj (by
    rw [map_mul (algebraMap X.O X.C), (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_mul])
  map_add' a b := X.ints.hom_inj (by
    rw [map_add (algebraMap X.O X.C), (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_add])

theorem algebraMap_embO (σ : E →+* ℂ) (a : 𝓞 E) : algebraMap X.O X.C (embO io X σ a) = embX io X σ a :=
  (X.ints.exists_of_le_one (v_embX_le_one io X σ a)).choose_spec

def red (σ : E →+* ℂ) : 𝓞 E →+* ResidueField X.O := (residue X.O).comp (embO io X σ)

theorem residue_eq_zero_iff_v (x : X.O) : residue X.O x = 0 ↔ X.v (algebraMap X.O X.C x) < 1 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, X.ints.isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne (X.ints.map_le_one x) h, fun h => h.ne⟩

theorem residue_eq_iff_v (x y : X.O) :
    residue X.O x = residue X.O y ↔ X.v (algebraMap X.O X.C x - algebraMap X.O X.C y) < 1 := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff_v, map_sub]

theorem primeBelow_eq_ker (σ : E →+* ℂ) : primeBelow io X σ = RingHom.ker (red io X σ) := by
  ext a
  rw [RingHom.mem_ker]
  show X.v (embX io X σ a) < 1 ↔ residue X.O (embO io X σ a) = 0
  rw [residue_eq_zero_iff_v, algebraMap_embO]

theorem red_eq_pow_iff (σ σ' : E →+* ℂ) (a : 𝓞 E) (n : ℕ) :
    red io X σ' a = red io X σ a ^ n ↔ X.v (embX io X σ' a - embX io X σ a ^ n) < 1 := by
  show residue X.O (embO io X σ' a) = residue X.O (embO io X σ a) ^ n ↔ _
  rw [← map_pow, residue_eq_iff_v, map_pow, algebraMap_embO, algebraMap_embO]

theorem charP_residueField_of_irreducible : CharP (ResidueField X.O) p := by
  have h : ((p : ℕ) : ResidueField X.O) = 0 := by
    rw [← map_natCast (residue X.O), residue_eq_zero_iff]
    exact X.nonunit.out
  exact (CharP.charP_iff_prime_eq_zero Fact.out).2 h

theorem vX_vp_pos_iff (x : X.C) : 0 < vX_vp X x ↔ X.v x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hpO : ¬ IsUnit (p : X.O) := X.nonunit.out
  have hp1 : X.v (p : X.C) < 1 := by
    have h := X.ints.map_le_one (p : X.O)
    rw [map_natCast] at h
    refine lt_of_le_of_ne h fun h1 => hpO ?_
    apply X.ints.isUnit_of_one'
    rw [map_natCast]
    exact h1
  have hp0 : (0 : NNReal) < X.v (p : X.C) := by
    rw [pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hx0 : (0 : NNReal) < X.v x := by
    rw [pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact hx
  have hlp : Real.log (X.v (p : X.C) : ℝ) < 0 :=
    Real.log_neg (by exact_mod_cast hp0) (by exact_mod_cast hp1)
  have hi : (Real.log (X.v (p : X.C) : ℝ))⁻¹ < 0 := inv_lt_zero.mpr hlp
  rw [vX_vp_apply X hx, show (0 : WithTop ℝ) = ((0 : ℝ) : WithTop ℝ) from rfl, WithTop.coe_lt_coe,
    mul_pos_iff]
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · exact absurd h1 (not_lt.mpr hi.le)
    · have h3 := (Real.log_neg_iff (by exact_mod_cast hx0)).mp h2
      exact_mod_cast h3
  · intro h
    right
    exact ⟨hi, Real.log_neg (by exact_mod_cast hx0) (by exact_mod_cast h)⟩

end Labels

variable {Dw : Datum H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr}
  {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def tanX (a : 𝓞 E) : Matrix (Fin (chD Ch.ch)) (Fin (chD Ch.ch)) X.C :=
  Matrix.of fun i j => jX X (coeff (Finsupp.single ((0 : Fin 1), j) 1) (Ch.actT a i))

end GlobalTheory.PrimePart

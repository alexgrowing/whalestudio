import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

namespace GlobalTheory.GalTw

section

open GlobalTheory.LevelPairing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem exists_zetaM_pow (c : Coeff l) (ta : c.F ≃+* c.F) :
    ∃ a a' : ℕ, ta (zetaM c) = zetaM c ^ a ∧ a * a' ≡ 1 [MOD l.M] := by
  have h3 := l.three_le
  haveI : NeZero l.M := ⟨by omega⟩
  have hp := zetaM_prim c
  have hp' : IsPrimitiveRoot (ta (zetaM c)) l.M := hp.map_of_injective ta.injective
  obtain ⟨a, -, ha⟩ := hp.eq_pow_of_pow_eq_one hp'.pow_eq_one
  have hco : a.Coprime l.M := (hp.pow_iff_coprime (by omega) a).1 (ha ▸ hp')
  obtain ⟨a', -, h⟩ := Nat.exists_mul_mod_eq_one_of_coprime hco (by omega)
  refine ⟨a, a', ha.symm, ?_⟩
  unfold Nat.ModEq
  rw [h, Nat.mod_eq_of_lt (by omega)]

theorem mk_qRep {K : Submodule (𝓞 E) Dw.La} (x : Dw.La ⧸ K) : (Submodule.Quotient.mk (qRep x) : Dw.La ⧸ K) = x :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective _ x)

theorem level_nsmul (x : LevQc Dw l) : l.M • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h : (l.M : 𝓞 E) ∈ l.Mb * Mfr l := by
    rw [Mfr, l.prod]; exact Ideal.mem_span_singleton_self _
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul (Submodule.mem_inf.1 (Ideal.mul_le_inf h)).2 Submodule.mem_top

theorem nsmul_nsmul_of_modEq {n a a' : ℕ} (h : a * a' ≡ 1 [MOD l.M]) (x : Fin n → LevQc Dw l) :
    a • a' • x = x := by
  have h3 := l.three_le
  have hM : l.M • x = 0 := funext fun b => level_nsmul (x b)
  have e : a * a' = l.M * (a * a' / l.M) + 1 := by
    have := Nat.div_add_mod (a * a') l.M
    rw [h, Nat.mod_eq_of_lt (show 1 < l.M by omega)] at this
    exact this.symm
  rw [← mul_smul, e, add_smul, one_smul, mul_comm, mul_smul, hM, smul_zero, zero_add]

theorem pairL_nsmul {n : ℕ} (a : ℕ) (x : Fin n → LevQc Dw l) (y : Fin n → Dw.La) :
    (l.M : ℤ) ∣ (a : ℤ) * pairL (l := l) (fun b => qRep (x b)) y -
      pairL (l := l) (fun b => qRep ((a • x) b)) y := by
  have e : (a : ℤ) * pairL (l := l) (fun b => qRep (x b)) y = pairL (l := l) (fun b => a • qRep (x b)) y := by
    unfold pairL
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  rw [e]
  refine pairL_congr _ _ _ _ (fun b => ?_) (fun b => by simp)
  rw [← Submodule.Quotient.eq, mk_qRep, ← Nat.cast_smul_eq_nsmul (𝓞 E), Submodule.Quotient.mk_smul, mk_qRep,
    Nat.cast_smul_eq_nsmul]
  rfl

theorem map_phiHat (c : Coeff l) {n : ℕ} (ta : c.F ≃+* c.F) {a a' : ℕ} (ha : ta (zetaM c) = zetaM c ^ a)
    (h : a * a' ≡ 1 [MOD l.M]) (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l) :
    ta (phiHat c φ q) = phiHat c (fun x => ta (φ (a' • x))) q := by
  have h' : a' * a ≡ 1 [MOD l.M] := mul_comm a a' ▸ h
  let e : (Fin n → LevQc Dw l) ≃ (Fin n → LevQc Dw l) :=
    ⟨fun x => a • x, fun x => a' • x, nsmul_nsmul_of_modEq h', nsmul_nsmul_of_modEq h⟩
  unfold phiHat
  refine (ta.toAddEquiv.map_finsum _).trans (Eq.trans (finsum_congr fun x => ?_) (finsum_comp_equiv e))
  change ta _ = ta (φ (a' • a • x)) * zetaM c ^ pairL (l := l) (fun b => qRep ((a • x) b)) _
  rw [nsmul_nsmul_of_modEq h', map_mul, map_zpow₀, ha, ← zpow_natCast, ← zpow_mul,
    zpow_congr c (pairL_nsmul a x _)]

theorem phiHat_mul (c : Coeff l) {n : ℕ} (u : c.F) (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l) :
    phiHat c (fun x => u * φ x) q = u * phiHat c φ q := by
  unfold phiHat
  rw [← smul_eq_mul u, smul_finsum]
  refine finsum_congr fun x => ?_
  rw [smul_eq_mul, mul_assoc]

theorem shortValAt_mul {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (nab : NabV Xo c)
    (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b u : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) (h : ShortValAt Xo c nab w Λ b N P y v) :
    ShortValAt Xo c nab (fun q => u * w q) Λ b N P y (algebraMap c.F S u * v) := by
  obtain ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, ?_⟩
  rw [map_mul, h7, AlgHom.commutes, mul_left_comm]
  congr 1
  rw [← Algebra.smul_def, smul_finsum]
  refine finsum_congr fun q => ?_
  rw [Algebra.smul_def, map_mul, mul_assoc]

end

theorem phiHat_aut_and_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ), (∀ ta : c.F ≃+* c.F, (∃ a a' : ℕ, ta (zetaM c) = zetaM c ^ a ∧ a * a' ≡ 1 [MOD l.M]) ∧ ∀ a a' : ℕ, ta (zetaM c) = zetaM c ^ a → a * a' ≡ 1 [MOD l.M] → ∀ (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l), ta (phiHat c φ q) = phiHat c (fun x => ta (φ (a' • x))) q) ∧ (∀ (u : c.F) (φ : (Fin n → LevQc Dw l) → c.F) q, phiHat c (fun x => u * φ x) q = u * phiHat c φ q) ∧ ∀ (nab : NabV Xo c) (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b u : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S), ShortValAt Xo c nab w Λ b N P y v → ShortValAt Xo c nab (fun q => u * w q) Λ b N P y (algebraMap c.F S u * v) := by
  intro E _ _ _ H Dw l Xo c n
  exact ⟨fun ta => ⟨exists_zetaM_pow c ta, fun _ _ ha h φ q => map_phiHat c ta ha h φ q⟩,
    fun u φ q => phiHat_mul c u φ q,
    fun nab w Λ b u N P S _ _ y v h => shortValAt_mul nab w Λ b u N P S y v h⟩

end GlobalTheory.GalTw

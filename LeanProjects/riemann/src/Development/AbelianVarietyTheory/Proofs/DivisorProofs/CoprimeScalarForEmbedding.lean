import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrAtEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Definitions.Divisors.ConstantUniqueOfEqProduct
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaCharacterUnramified

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

theorem pairL_levRep_zsmul {n : ℕ} (x : Fin n → Dw.La) (m : ℤ) (q : Fin n → LevQ Dw l) :
    (l.M : ℤ) ∣ pairL (l := l) x (fun b => levRep ((m • q) b)) - m * pairL (l := l) x (fun b => levRep (q b)) := by
  have hrep : ∀ q : LevQ Dw l, (Submodule.Quotient.mk (levRep q) : LevQ Dw l) = q := fun q =>
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  have e : m * pairL (l := l) x (fun b => levRep (q b)) = pairL (l := l) x (fun b => m • levRep (q b)) := by
    unfold pairL
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_comm, map_zsmul, smul_eq_mul]
  rw [e]
  refine GlobalTheory.LevelPairing.pairL_congr _ _ _ _ (fun b => by simp) fun b => ?_
  rw [← Submodule.Quotient.eq, hrep]
  refine Eq.trans ?_ (map_zsmul (Submodule.mkQ _) m (levRep (q b))).symm
  rw [Submodule.mkQ_apply, hrep, Pi.smul_apply]

theorem map_phiHat (c : Coeff l) (τ : c.F →+* ℂ) : ∃ m : ℤ, IsCoprime m (l.M : ℤ) ∧
    ∀ (n : ℕ) (φ : (Fin n → LevQc Dw l) → c.F), (∀ x, φ x = 0 ∨ φ x = 1) → ∀ q,
      τ (phiHat c φ q) = c.F.val.toRingHom (phiHat c φ (m • q)) := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  haveI : NeZero l.M := ⟨hM⟩
  have h0 := GlobalTheory.LevelPairing.zetaM_prim c
  have h1 : IsPrimitiveRoot (c.F.val.toRingHom (zetaM c)) l.M := h0.map_of_injective c.F.val.toRingHom.injective
  have h2 : IsPrimitiveRoot (τ (zetaM c)) l.M := h0.map_of_injective τ.injective
  obtain ⟨m, -, hm⟩ := h1.eq_pow_of_pow_eq_one h2.pow_eq_one
  have hc : m.Coprime l.M := (h1.pow_iff_coprime (Nat.pos_of_ne_zero hM) m).1 (hm ▸ h2)
  refine ⟨m, Nat.isCoprime_iff_coprime.2 hc, fun n φ hφ q => ?_⟩
  haveI := GlobalTheory.AdTh.PairModel.finite_levQc Dw l
  haveI := Fintype.ofFinite (Fin n → LevQc Dw l)
  rw [phiHat, phiHat, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [GlobalTheory.LevelPairing.zpow_congr c (pairL_levRep_zsmul _ (m : ℤ) q), map_mul, map_mul, map_zpow₀, map_zpow₀, ← hm,
    _root_.zpow_mul, zpow_natCast]
  congr 1
  rcases hφ x with h | h <;> simp [h]

end Gen

end GlobalTheory.GalOne

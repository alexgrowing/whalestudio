import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateLiftSL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open Formalism.L2.JoinChr
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnramCharUnique

theorem eq_one_of_loc {D : D7} {χ : (AE D)ˣ →* Circle} (h : ChrEq χ 1) (x : (AE D)ˣ) : χ x = 1 := by
  refine HeckeFinTrivial.eq_one_of_trivial_on_finite D χ h.1 (fun y hy => ?_) x
  obtain ⟨j, h1, h2, h3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j h1 h2 (PlaceIdem.exists_isPlIdem D j h1 h2 h3) χ 1 h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom y)
  exact Subtype.ext ((hprod y hy S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS').trans
    (Finset.prod_eq_one fun P _ => rfl))

theorem loc_parts {D : D7} {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsPlIdem D e P) (k : D.host.E)
    (hk : P.valuation D.host.E k ≤ 1) : infPart D (locE D e k) = 1 ∧ finPart D (locE D e k) ∈ intAE D := by
  obtain ⟨ι, hι, hint, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨h1, h2, h3⟩ := HeckeTensorRead.isPlIdem_parts D ι hι hint he
  refine ⟨(HeckeTensorRead.map_loc (infPart D) e _).trans (by rw [h1, zero_mul, add_zero]), (hint _).2 fun Q => ?_⟩
  have h4 : ι (finPart D (incA D k)) = algebraMap D.host.E _ k := hι k
  have h5 : ι (finPart D (locE D e k)) = 1 + ι (finPart D e) * (algebraMap D.host.E _ k - 1) := by
    rw [← h4]
    exact HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _
  rw [h5]
  change Valued.v (1 + ι (finPart D e) Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) k - 1)) ≤ 1
  by_cases hQ : Q = P
  · subst hQ
    rw [h2, one_mul, add_sub_cancel, GlobalTheory.CharLocProd.val_algebraMap]
    exact hk
  · rw [h3 Q hQ, zero_mul, add_zero, map_one]

noncomputable def locHom {D : D7} {e : AE D} (he : e * e = e) : D.host.Eˣ →* (AE D)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun k => locE D e (k : D.host.E)
      map_one' := by simp [locE]
      map_mul' := fun k l => (locE_mul_locE he k l).symm }

theorem eq_one_of_unif {D : D7} {c : (AE D)ˣ →* Circle} (hc : IsHeckeChar D c) (hu : UnramEverywhere D c)
    (h : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ x : (AE D)ˣ,
      (x : AE D) = locE D e (Formalism.L2.Host.unif P : D.host.Eˣ) → c x = 1) (x : (AE D)ˣ) : c x = 1 := by
  refine eq_one_of_loc ⟨hc, fun P e he k y hy => ?_⟩ x
  obtain rfl : y = locHom he.1 k := Units.ext hy
  have hπ : P.valuation D.host.E ((Formalism.L2.Host.unif P : D.host.Eˣ) : D.host.E) = WithZero.exp (-1 : ℤ) :=
    (GlobalTheory.CharLocProd.val_algebraMap P _).symm.trans (Formalism.L2.Host.unif_spec P)
  have h0 : P.valuation D.host.E (k : D.host.E) ≠ 0 := by simp
  obtain ⟨n, hn⟩ : ∃ n : ℤ, P.valuation D.host.E (k : D.host.E) = WithZero.exp n := ⟨_, (WithZero.exp_log h0).symm⟩
  let u : D.host.Eˣ := k * Formalism.L2.Host.unif P ^ n
  have hv : P.valuation D.host.E (u : D.host.E) = 1 := by
    simp only [u, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hn, hπ]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hv' : P.valuation D.host.E ((u⁻¹ : D.host.Eˣ) : D.host.E) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  have h1 : c (locHom he.1 u) = 1 :=
    hu _ (loc_parts he _ hv.le).1 (loc_parts he _ hv.le).2 (by
      rw [← map_inv]
      exact (loc_parts he _ hv'.le).2)
  rw [map_mul, map_mul, map_zpow, map_zpow, h P e he (locHom he.1 (Formalism.L2.Host.unif P)) rfl, one_zpow, mul_one] at h1
  rw [h1]
  rfl

theorem isEtaConj_unique : ∀ (D : D7) (σ : D.what₂.LL →+* ℂ) (η η' η'' : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ η η' → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ η η'' → η' = η'' := by
  rintro D σ η η' η'' ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
  refine MonoidHom.ext fun x => mul_inv_eq_one.1 (eq_one_of_unif (c := η' * η''⁻¹)
    ⟨h1.1.mul g1.1.inv, fun k => mul_inv_eq_one.2 ((h1.2 k).trans (g1.2 k).symm)⟩
    (fun y a b c => mul_inv_eq_one.2 ((h2 y a b c).trans (g2 y a b c).symm))
    (fun P e he y hy => mul_inv_eq_one.2 ?_) x)
  obtain ⟨a, ha, ha'⟩ := h3 P e he y hy
  obtain ⟨b, hb, hb'⟩ := g3 P e he y hy
  obtain rfl : a = b := D.what₂.embLL.injective (ha.trans hb.symm)
  have : Finite (kP P) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  have hpos : (0 : ℝ) < (Nat.card (kP P) : ℝ) := Nat.cast_pos.2 Nat.card_pos
  exact Subtype.ext (mul_right_cancel₀ (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 hpos).ne'))
    (ha'.symm.trans hb'))

end GlobalTheory.UnramCharUnique

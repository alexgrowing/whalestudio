import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmLatticeEmbeddingDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeLatticeSymplecticBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenbasisEquationDataPrimePowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelationFlagsDualAdelesStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical

private theorem dualAt_neg {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)
    {C : GlobalTheory.TrueGeo.CxSt F} (hm : Mets Y C) {g : ℕ} (w w' : Fin g → Sym E →₀ ℤ) (h : ∀ k, w' k = -w (Fin.rev k)) (p : ℕ) :
    DualAt (fun k => adlOf Y hm (w k)) (fun k => adlOf Y hm (w' k)) p := by
  have key : ∀ (k : Fin g) (x : Y.Y.X),
      genAt (adlOf Y hm (w' k)).D x * genAt (adlOf Y hm (w (Fin.rev k))).D x =
        ((GlobalTheory.TrueGeo.eqn (divOf Y (expo Dw (w k.rev))) x *
          GlobalTheory.TrueGeo.eqn (divOf Y (expo Dw (-w k.rev))) x : Y.Y.Fnˣ) : Y.Y.Fn)⁻¹ := by
    intro k x
    rw [h k]
    simp only [genAt, adlOf, Units.val_inv_eq_inv_val, Units.val_mul, mul_inv]
    exact mul_comm _ _
  refine ⟨fun k x => ?_, fun k v _ ε y => ?_⟩
  · beta_reduce
    rw [key]
    exact (GlobalTheory.CombInd.DualComb.unitAt_eqn_mul Y _ x).inv
  · beta_reduce
    rw [key, GlobalTheory.LineNorm.Neg.valAt_inv (GlobalTheory.CombInd.DualComb.unitAt_eqn_mul Y _ _), map_inv₀, Real.log_inv, h k]
    exact (GlobalTheory.CombInd.DualComb.lgOf_neg Y _ v ε y).trans (sub_eq_add_neg _ _)

private theorem eigAt_neg {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (a : ℕ → Bool) (R : Option ℝ) (k : ℕ) : eigAt Dw a R (-1) k = -eigAt Dw a R 1 k := by
  unfold eigAt
  cases (letters Dw)[k]? with
  | none => simp
  | some z => exact Finsupp.single_neg _ _

theorem _root_.GlobalTheory.T.relative_flag_whole_symbol_multiple : Hypotheses2 → HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonnePerfd → ∀ (D : D7) (O : Setup D), O.Core → ∀ (T : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → p ∈ T → ∀ c : O.s.Comp, ∃ n : ℕ, n ≠ 0 ∧ ∀ k : ℕ, RelFlag (fun i : Fin (D.R.f * O.N + D.R.f * O.N) => adlOf (O.Φ.C c) (O.met.hm c) (wholeSym (ArIn.ind T) (some R) (finSumFinEquiv.symm i))) (fun i => adlOf (O.Φ.C c) (O.met.hm c) (eigSym O.S.Dw (ArIn.ind T) (some R) (finSumFinEquiv.symm i))) p n k := by
  intro h2 hH hR hS hP D O hO T R hR2 p hp hT c
  obtain ⟨bar, Φ, β, ρ, J, hΦ, hJ, hρ, hEq⟩ := GlobalTheory.T.exists_cm_lattice_embedding_data h2 hH hR hS hP D O hO T R hR2 p hp hT c
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  obtain ⟨n, P, Q, hn, hB⟩ := GlobalTheory.T.cm_type_lattice_symplectic_basis D.host.E D.what₂.LL ⟨D.embE⟩ bar Φ hΦ ρ J hJ hρ p hp
  have hrel := GlobalTheory.T.eigenbasis_equation_data_prime_power _ _ β _ ρ J p n P Q hp hn hJ hB hEq
  have hA := dualAt_neg (O.Φ.C c) (O.met.hm c)
    (fun i : Fin (D.R.f * O.N) => wholeSym (ArIn.ind T) (some R) (Sum.inl i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)))
    (fun i : Fin (D.R.f * O.N) => wholeSym (ArIn.ind T) (some R) (Sum.inr i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)))
    (fun k => Finsupp.single_neg _ _) p
  have hA' := dualAt_neg (O.Φ.C c) (O.met.hm c)
    (fun i : Fin (D.R.f * O.N) => eigSym O.S.Dw (ArIn.ind T) (some R) (Sum.inl i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)))
    (fun i : Fin (D.R.f * O.N) => eigSym O.S.Dw (ArIn.ind T) (some R) (Sum.inr i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)))
    (fun k => eigAt_neg _ _ _ _) p
  refine ⟨n, hn, fun k => ?_⟩
  have h := GlobalTheory.T.relation_flags_dual_adeles _ _ _ _ p n hp hn hA hA' hrel k
  convert h using 2 with i i <;> cases finSumFinEquiv.symm i <;> rfl

import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.DualLattices.SurjectiveAinfTowerZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TeichmullerQuot
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ModPToValuationResidueFieldSurjective
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DualTowerMapExists
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateBasisMatrix
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateBasisGram
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEndDifferentialRingHom
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicEndApply
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTateMatricesLink
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftOfNil
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilpotentCoordinates
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSeriesOfNaturalOnNilpotent
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GroupLawPowerSeries
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalChart
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FiniteAlgebraSplitLocal
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinEtaleFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinRepExistsIsPullbackSpec
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinOfLocalAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvBasicNEvalSubCoeffMem

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodDatum

theorem exists_basis_of_card (p : ℕ) [hp : Fact p.Prime] (g : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (hcV : Nat.card V = p ^ (2 * g)) :
    ∃ f : Ix g → V, ∀ x : V, ∃! t : Ix g → ZMod p, x = ∑ j, (t j).val • f j := by
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcV]; exact pow_ne_zero _ hp.out.ne_zero)
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hrk : Module.finrank (ZMod p) V = Fintype.card (Ix g) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hcV, Nat.card_zmod] at h
    have h2 := Nat.pow_right_injective hp.out.two_le h
    rw [← h2, Fintype.card_sum, Fintype.card_fin, two_mul]
  let b : Module.Basis (Ix g) (ZMod p) V :=
    (Module.finBasisOfFinrankEq (ZMod p) V hrk).reindex (Fintype.equivFin (Ix g)).symm
  have hsm : ∀ (t : ZMod p) (y : V), t.val • y = t • y := fun t y => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  refine ⟨b, fun x => ⟨b.equivFun x, ?_, fun t ht => ?_⟩⟩
  · simp only [hsm]
    rw [← b.equivFun_symm_apply, LinearEquiv.symm_apply_apply]
  · simp only [hsm] at ht
    rw [← b.equivFun_symm_apply] at ht
    rw [ht, LinearEquiv.apply_symm_apply]

theorem exists_compatible_basis (p : ℕ) [hp : Fact p.Prime] (g : ℕ) (Γ : Type) [AddCommGroup Γ]
    (hdiv : ∀ x : Γ, ∃ y, p • y = x) (hcard : Nat.card {x : Γ // p • x = 0} = p ^ (2 * g)) :
    ∃ τ : Ix g → ℕ → Γ, (∀ i n, (p ^ (n + 1)) • τ i n = 0) ∧ (∀ i n, τ i n = p • τ i (n + 1)) ∧
      ∀ x : Γ, p • x = 0 → ∃! t : Ix g → ZMod p, x = ∑ j, (t j).val • τ j 0 := by
  obtain ⟨V, hV⟩ : ∃ V : AddSubgroup Γ, ∀ x : Γ, x ∈ V ↔ p • x = 0 :=
    ⟨(nsmulAddMonoidHom p : Γ →+ Γ).ker, fun x => Iff.rfl⟩
  have hcV : Nat.card V = p ^ (2 * g) :=
    (Nat.card_congr (Equiv.subtypeEquivRight hV)).trans hcard
  obtain ⟨b, hb⟩ := @exists_basis_of_card p _ g V _
    (AddCommGroup.zmodModule (fun x => Subtype.ext ((hV _).1 x.2))) hcV
  choose d hd using hdiv
  let τ : Ix g → ℕ → Γ := fun i n => d^[n] (b i : Γ)
  have hτp : ∀ i n, τ i n = p • τ i (n + 1) := fun i n => by
    simp only [τ, Function.iterate_succ_apply', hd]
  have hsum : ∀ t : Ix g → ZMod p, ((∑ j, (t j).val • b j : V) : Γ) = ∑ j, (t j).val • τ j 0 :=
    fun t => by
      rw [AddSubmonoidClass.coe_finset_sum]
      rfl
  refine ⟨τ, fun i n => ?_, hτp, fun x hx => ?_⟩
  · induction n with
    | zero => rw [zero_add, pow_one]; exact (hV _).1 (b i).2
    | succ n ih => rw [pow_succ, mul_smul, ← hτp i n, ih]
  · obtain ⟨t, ht, hu⟩ := hb ⟨x, (hV x).2 hx⟩
    refine ⟨t, ?_, fun t' ht' => hu t' (Subtype.ext ?_)⟩
    · exact (congrArg Subtype.val ht).trans (hsum t)
    · exact ht'.trans (hsum t').symm

theorem main :
  (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) (g : ℕ)
    (G : Over (Spec (CommRingCat.of (Ainf.R0 p O ε)))) [GrpObj G] [IsCommMonObj G] (B : BX (Ainf.R0 p O ε))
    (e : ∀ R : LAlg (Ainf.R0 p O ε), B.G R → (sp (R₀ := (Ainf.R0 p O ε)) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg (Ainf.R0 p O ε)} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    SmoothOfRelativeDimension g G.hom → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : B.G (Ainf.ainfTowerL p O hv ε hε).O, ∃ y, p • y = x) → Nat.card {x : B.G (Ainf.ainfTowerL p O hv ε hε).O // p • x = 0} = p ^ (2 * g) →
    (∀ x : B.G (Ainf.ainfTowerL p O hv ε hε).O, p • x = 0 → (∀ y : B.G (Ainf.ainfTowerL p O hv ε hε).O, p • y = 0 → B.IsPairing p x y 1) → x = 0) →
    ∀ [Algebra ℤ_[p] ((Ainf.ainfTowerL p O hv ε hε).O : Type)] (O₀ : Type) [CommRing O₀] (cj : O₀ ≃ₐ[ℤ] O₀) (Ad : O₀ → OAdj B (Ainf.ainfTowerL p O hv ε hε).O),
    (∀ a, (Ad a).ab = (Ad (cj a)).a) → (∀ a, cj (cj a) = a) →
    (∀ {R : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (x : B.G R), (Ad 1).a.f s x = x ∧ ∀ a b, (Ad (a + b)).a.f s x = (Ad a).a.f s x + (Ad b).a.f s x ∧
      (Ad (a * b)).a.f s x = (Ad a).a.f s ((Ad b).a.f s x)) →
    ∃ (Dt : DualTower (Ainf.ainfTowerL p O hv ε hε)) (D : Dat p g B (Ainf.ainfTowerL p O hv ε hε) Dt (ℤ_[p] ⊗[ℤ] O₀) (Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p]) cj) (Ainf.ainfTowerL p O hv ε hε).c),
      D.H.P = 0 ∧ D.H.PL = 0 ∧
      (∀ a {R S : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) →
      (Ad a).a.f s (B.tg π hπ (D.ch.gb l ⊗ₜ[(Ainf.R0 p O ε)] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[(Ainf.R0 p O ε)] m k)) ∧
      ∀ a j n, (Ad a).a.f (LHom.id (Ainf.ainfTowerL p O hv ε hε).O) (D.L.τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (D.H.ρ (1 ⊗ₜ[ℤ] a) k j)).val • D.L.τ k n) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε g G _ _ B e hbij hadd hnat hsm hfin hflat hdiv hcard hperf
    _ O₀ _ cj Ad hab hcj hAd
  haveI : IsLocalRing (Ainf.R0 p O ε) := WdAinf.ainf_thetaQuotRing_isLocalRing p O hv ε hε
  haveI : IsDomain ((Ainf.ainfTowerL p O hv ε hε).O : Type) := Ainf.ainfTower_isDomain p O hv ε hε
  have hsm' : Smooth G.hom := SmoothOfRelativeDimension.smooth g G.hom
  obtain ⟨K, wd, hnil, hK, hKl⟩ :=
    GlobalTheory.wData_ainfTower_exists GlobalTheory.WittQuot.teichmuller_quot p O hv ε hε
  obtain ⟨ch⟩ := GlobalTheory.FormalChartOf.exists_formalChart GlobalTheory.NilCoord.nilpotent_coordinates
    (GlobalTheory.ChLaw.groupLaw_powerSeries GlobalTheory.nEval_basic
      (GlobalTheory.exists_series_of_natural_on_nilpotent GlobalTheory.nEval_basic))
    G g B e hbij hadd hnat hsm K hK hKl
  have sm := GlobalTheory.SmoothNilLift.main G B e hbij hadd hnat hsm' K wd.W wd.ρW hnil
  obtain ⟨fin⟩ := @GlobalTheory.FinOf.main GlobalTheory.finRep_kernel_mul_finite_free GlobalTheory.finite_algebra_split_local
    GlobalTheory.finEtale_main _ _ G _ _ (Ainf.ainfTowerL p O hv ε hε).O p B e hbij hadd hnat hfin hflat hsm'
    C _ _ _ v (inferInstanceAs (Algebra O C)) hv (Fact.out : p.Prime).ne_zero
  obtain ⟨Dt⟩ := GlobalTheory.exists_dualTower (Ainf.ainfTowerL p O hv ε hε)
  obtain ⟨τ, hτ, hτp, hbas⟩ := exists_compatible_basis p g _ hdiv hcard
  obtain ⟨dL, hdL⟩ := GlobalTheory.exists_endDifferential_ringHom B _ ch.gb O₀ (fun a => (Ad a).a) hAd
  obtain ⟨A, H, L, hP, hPL, hL, hρL, hρ⟩ := GlobalTheory.exists_tateMatrices_link GlobalTheory.tate_basis_matrix
    GlobalTheory.tateBasis_gram GlobalTheory.PadicOrderAction.main B (Ainf.ainfTowerL p O hv ε hε) Dt ch.gb O₀ cj Ad dL
    (WdAinf.thetaBar_surj p O hv ε hε) hab hcj hAd hdL
    (fun n => Ideal.mk_ker (I := Ideal.span {(p : O) ^ (n + 1)}))
    (fun n => IsPrimitiveRoot.coe_units_iff.1 (Ainf.zeta_primitive p O hv ε hε n))
    (fun n => Units.ext (Ainf.zeta_succ_pow p O ε n))
    τ hτ hτp hbas hperf
  refine ⟨Dt,
    { K := K
      ρO := wd.ρ1.comp ((Ainf.ainfTowerL p O hv ε hε).q 0)
      ch := ch
      wd := wd
      ρO_eq := rfl
      sm := sm
      fin := fin
      A := A
      H := H
      L := L
      tower_zero_surjective := surjective_ainfTower_zero p O hv ε hε
      tower_zero_ker := ker_ainfTower_zero p O hv ε hε
      zeta0 := ainf_zeta0 p O hv ε hε }, hP, hPL, ?_, ?_⟩
  · intro a R S s π hπ l i m hm
    exact hdL a s π hπ l i m (fun k => by rw [hm k]; exact congrArg (fun M => s.1 (M k l) * (i : (R : Type))) (hρL a))
  · intro a j n
    subst hL
    exact hρ a j n

end GlobalTheory.PeriodDatum

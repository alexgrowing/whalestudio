import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedFamilyTripleExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SmallTriple
open GlobalTheory.Grid MeasureTheory
variable {D : D7}
private theorem eta_sq_eq_one_alt {η : (AF D.host.F)ˣ →* Circle} (h : IsEta D η) (a : (AF D.host.F)ˣ) : η a ^ 2 = 1 := by
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have e := h.2.2.1 (idF D a)
  have e2 : Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := by
    ext1
    show Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) (a : AF D.host.F)) = ((a ^ 2 : (AF D.host.F)ˣ) : AF D.host.F)
    let b := (Module.finBasis D.host.F D.host.E).baseChange (AF D.host.F)
    rw [Algebra.norm_algebraMap_of_basis b, Fintype.card_fin, h2, Units.val_pow_eq_pow_val]
  rwa [e2, map_pow] at e
private theorem restriction_eta_add_two {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ (n + 2)) : ResEta D χ n :=
  ⟨h.1, fun η hη a => by rw [h.2 η hη a, pow_add, eta_sq_eq_one_alt hη, mul_one]⟩
private theorem exists_weil_representation (hP : GlobalTheory.Published.WeilRepresentationUnitaryPair) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (ε : Bool) (S W : HSp D) {χS χW : (AE D)ˣ →* Circle} (h1 : IsHeckeChar D χS) (h2 : IsHeckeChar D χW)
    (h3 : ResEta D χS S.rank) (h4 : ResEta D χW W.rank) : ∃ ω : WRep S W, IsWeil ψ ε S W χS χW ω := by
  obtain ⟨om, h⟩ := hP D ψ (sgn ε S) W χS χW hψ h1 h2 h3 h4
  exact ⟨om.comp ((ofSgn ε S).symm.toMonoidHom.prodMap (MonoidHom.id _)), h⟩
private theorem exists_vacuum_vector (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) : ∃ f, IsVacO ψ θ S T sS sT ΛS ΛT f := by
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T sS sT hS hT ΛS ΛT dS dT
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  let _ : MeasurableSpace (WO S T) := measMx _ _
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have h1 := (hf 1).1
  simp only [one_mul] at h1
  obtain ⟨⟨μ, 𝓕, hμ⟩, c, hc⟩ := GlobalTheory.T.exists_normalise_meanSquare_of_cocompact' (WO S T) (ratL T S) K hK hcov f h1.cont f0 (by
    rintro _ ⟨g, rfl⟩ w
    have e := h1.quasi g w
    have e' := congrArg norm e
    rw [norm_mul, hψ.1.2.1, one_mul] at e'
    exact e')
  exact ⟨fun w => c * f w, hψ, hθ, (hf c).1, (hf c).2.1, (hf c).2.2, ⟨(μ, 𝓕), hμ⟩,
    fun p hp => hc p.1 p.2 hp.1 hp.2.1 hp.2.2⟩
theorem exists_small_triple : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (T : Type) (A A' WW B' WW₁ : HSp D) (X : Tri T A A' WW)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E)
    (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)) (rB : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig B') (rW : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig WW₁),
    IsInfFam θ → X.Is ψ θ α β νH S → rB.Is → rW.Is → B'.rank + 2 = A'.rank → WW₁.rank + 2 = WW.rank →
    ∃ Y : Tri T A B' WW₁, Y.rA = X.rA ∧ Y.rA' = rB ∧ Y.rW = rW ∧ Y.Is ψ θ α β νH S := by
  intro hP D T A A' WW B' WW₁ X ψ θ α β νH S rB rW hθ hX hB hW eB eW
  have hψ : IsStdChar D ψ (-1) := hX.isVac.1
  have hA := hX.rigA
  choose ω hω using fun t => exists_weil_representation hP.weilRepresentationUnitaryPair hψ true A WW₁ (hX.weil t).hecS (hX.weil t).hecT
    (hX.weil t).resS (restriction_eta_add_two (eW ▸ (hX.weil t).resT))
  choose ω' hω' using fun t => exists_weil_representation hP.weilRepresentationUnitaryPair hψ false B' WW₁ (hX.weil' t).hecS (hX.weil' t).hecT
    (restriction_eta_add_two (eB ▸ (show ResEta D (α t) A'.rank from (hX.weil' t).resS))) (restriction_eta_add_two (eW ▸ (hX.weil' t).resT))
  have hneg : IsSelfDualC (neg A) X.rA.Λ := by
    refine ⟨hA.1.1, fun y => (hA.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
    · simp [neg_gram, hc]
    · simp [neg_gram] at hc ⊢
      exact neg_eq_iff_eq_neg.2 hc
  obtain ⟨vac, hv⟩ := exists_vacuum_vector ψ θ hψ hθ (neg A) WW₁ (fun τ => -X.rA.s τ) rW.s
    (fun τ => isCartanInv_sgn true _ τ (hA.2.2 τ).1) (fun τ => (hW.2.2 τ).1) X.rA.Λ rW.Λ hneg hW.1
  obtain ⟨vac', hv'⟩ := exists_vacuum_vector ψ θ hψ hθ B' WW₁ rB.s rW.s
    (fun τ => (hB.2.2 τ).1) (fun τ => (hW.2.2 τ).1) rB.Λ rW.Λ hB.1 hW.1
  have hν : ∀ t, IsHeckeChar D (α t / β t) := fun t => (hX.weil' t).hecT
  choose f hf _ using fun t => GlobalTheory.T.first_standard_pair_member_has_theta_function D ψ θ A WW₁ X.rA rW _ _ _ _ _ hA hW (hν t) (hX.idem t)
    (GlobalTheory.ConstRatio.ideal_ne_bot X S t) hv
  choose f' hf' _ using fun t => GlobalTheory.T.exists_thetaFunction_standardPairSecond D ψ θ B' WW₁ rB rW _ _ _ _ A.rank _ hB hW (hν t) (hX.idem t)
    (GlobalTheory.ConstRatio.ideal_ne_bot X S t) hv'
  obtain ⟨m', fd', hm'⟩ := GlobalTheory.ConstRatio.exists_meas B'
  have hr := hX.rank
  exact ⟨⟨X.rA, rB, rW, ω, ω', vac, vac', X.e, X.c, f, f', X.m, X.fd, m', fd'⟩, rfl, rfl, rfl,
    ⟨by omega, hA, hB, hW, hω, hω', hv, hv', hX.idem, hX.expo, hf, hf', hX.meas, hm'⟩⟩
end GlobalTheory.SmallTriple
end
theorem _root_.GlobalTheory.T.exists_small_triple_of_weil_vacuum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (T : Type) (A A' WW B' WW₁ : HSp D) (X : Tri T A A' WW)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E)
    (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)) (rB : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig B') (rW : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig WW₁),
    IsInfFam θ → X.Is ψ θ α β νH S → rB.Is → rW.Is → B'.rank + 2 = A'.rank → WW₁.rank + 2 = WW.rank →
    ∃ Y : Tri T A B' WW₁, Y.rA = X.rA ∧ Y.rA' = rB ∧ Y.rW = rW ∧ Y.Is ψ θ α β νH S := _root_.GlobalTheory.SmallTriple.exists_small_triple
end

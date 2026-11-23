import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.ConjTorusSubApply
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.FiniteCuspidalOfIsCuspidal
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoKO
import Development.DiscreteGroups.GlobalIrreducibility.DzTwChar
import Development.DiscreteGroups.GlobalIrreducibility.DzKSchur
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularLocalOfDepthZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralCharacterSubquotientProductIrreduciblesStatement
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.GreenCuspLabels.GreenCuspidal

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace UpperTheory.Gal.InertialTypesAlt.TypeCharacters

open Matrix GlobalTheory.GLq GlobalTheory.SerSys GlobalTheory.IwahoriInj GlobalTheory.DepthZeroJac

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

include hi

private def resE : 𝓀[w.adicCompletion E] ≃+* ZMod g :=
  RingEquiv.ofBijective (DiscreteGroups.sglob.DzTw.resMap i hi) ⟨RingHom.injective _, fun a => by
    obtain ⟨y, rfl⟩ := DiscreteGroups.sglob.DzIso.redO_surjective i hi a
    exact ⟨IsLocalRing.residue _ y, rfl⟩⟩

private theorem resE_redK {n : ℕ} (x : KO (w.adicCompletion E) (Fin n)) (κ : GL (Fin n) ℤ_[g])
    (hκ : GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n κ) = x) :
    GeneralLinearGroup.map (resE i hi).toRingHom (redK (w.adicCompletion E) (Fin n) x) = GlobalTheory.GLp.red g n κ := by
  ext a b
  have hx : ((x : GL (Fin n) (w.adicCompletion E)) : Matrix _ _ _) a b = i (κ a b : ℚ_[g]) := by
    rw [← hκ]; rfl
  simp only [GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply, redK_apply]
  have key : ∀ y : 𝒪[w.adicCompletion E], (y : w.adicCompletion E) = i (κ a b : ℚ_[g]) →
      (resE i hi).toRingHom (IsLocalRing.residue _ y) = PadicInt.toZMod (κ a b) := by
    intro y hy
    show PadicInt.toZMod (DiscreteGroups.sglob.DzIso.toInt i hi y) = _
    congr 1
    apply Subtype.ext
    rw [DiscreteGroups.sglob.DzIso.coe_toInt, hy, RingEquiv.symm_apply_apply]
  exact key _ hx

private theorem finCusp_comp {n : ℕ} (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character) :
    PositivityTheory.Rg.DzCount.FinCusp (τ.ρ.comp (GeneralLinearGroup.map (n := Fin n) (resE i hi).toRingHom)) := by
  intro s d e hne v hv
  have hF : PositivityTheory.Rg.DzCount.FinCusp τ.ρ :=
    PositivityTheory.Rg.DzCount.finite_cuspidal_of_isCuspidal τ (PositivityTheory.GreenCharacters.isCuspidal_of_isCusp τ hτ)
  refine hF s d e (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.mpr (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.mp hne)) v ?_
  intro u hu
  have hback : GeneralLinearGroup.map (resE i hi).toRingHom
      (GeneralLinearGroup.map (resE i hi).symm.toRingHom u) = u := by
    ext a b
    simp
  rw [← hback]
  apply hv
  rw [GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries] at hu ⊢
  intro a b hab
  have h1 := hu a b hab
  simp only [GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply, h1]
  by_cases hab' : a = b
  · subst hab'; simp
  · simp [Matrix.one_apply_ne hab']

private theorem fixed_eq_range {n : ℕ} (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character)
    (σ : IrrRep (GL (Fin n) (w.adicCompletion E))) (ω : (w.adicCompletion E)ˣ →* ℂˣ) (hω : HasCentralChar σ.ρ ω)
    (φ : τ →ₗ[ℂ] σ.V) (h0 : φ ≠ 0)
    (hφ : ∀ (k : GL (Fin n) ℤ_[g]) (u : τ), φ (τ.ρ (GlobalTheory.GLp.red g n k) u) =
      σ.ρ (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k)) (φ u)) :
    Function.Injective φ ∧ fixed σ.ρ (KOne (w.adicCompletion E) (Fin n)) = LinearMap.range φ := by
  haveI hirr : Representation.IsIrreducible τ.ρ :=
    GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple τ (DiscreteGroups.sglob.DzType.Kon.simple_of_isIrr τ hτ.2.1)
  let U : Subrepresentation τ.ρ := ⟨LinearMap.ker φ, fun x v hv => by
    obtain ⟨k, rfl⟩ := GlobalTheory.GLp.Model.red_surjective n x
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hφ, hv, map_zero]⟩
  have hinj : Function.Injective φ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top U with h | h
    · have hk : LinearMap.ker φ = ⊥ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.ker_eq_bot.1 hk
    · exfalso
      have hk : LinearMap.ker φ = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact h0 (LinearMap.ker_eq_top.1 hk)
  obtain ⟨u0, hu0⟩ : ∃ u, φ u ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact h0 (LinearMap.ext hcon)
  haveI : Nontrivial τ := ⟨⟨u0, 0, fun e => hu0 (by rw [e, map_zero])⟩⟩
  have hT : PositivityTheory.Rg.DzCount.IsTypeMap (τ.ρ.comp (GeneralLinearGroup.map (n := Fin n) (resE i hi).toRingHom)) σ.ρ φ :=
    ⟨hinj, fun x v => by
      obtain ⟨κ, hκ⟩ := DiscreteGroups.sglob.DzIso.exists_of_mem_KO i hi x.2
      rw [MonoidHom.comp_apply, resE_redK i hi x κ hκ, hφ, hκ]⟩
  exact ⟨hinj, PositivityTheory.Rg.DzCount.B.st6 (w.adicCompletion E) τ n _ (finCusp_comp i hi τ hτ) σ ω hω φ hT⟩

omit hi in
private theorem ringEquiv_eq {F : Type} [Field F] (r r' : F ≃+* ZMod g) : r = r' := by
  have h : (r.symm : ZMod g →+* F) = (r'.symm : ZMod g →+* F) := Subsingleton.elim _ _
  have hs : r.symm = r'.symm := RingEquiv.ext fun y => RingHom.congr_fun h y
  rw [← RingEquiv.symm_symm r, ← RingEquiv.symm_symm r', hs]

omit hi in
private theorem central (y : IrrGL (w.adicCompletion E)) : ∃ ω : (w.adicCompletion E)ˣ →* ℂˣ, HasCentralChar y.rep ω :=
  (GlobalTheory.T.centralCharacter_subquotient_productIrreducibles (w.adicCompletion E)).1 y

private theorem trace_eq {n : ℕ} (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character)
    (σ : IrrRep (GL (Fin n) (w.adicCompletion E))) (ω : (w.adicCompletion E)ˣ →* ℂˣ) (hω : HasCentralChar σ.ρ ω)
    (φ : τ →ₗ[ℂ] σ.V) (h0 : φ ≠ 0)
    (hφ : ∀ (k : GL (Fin n) ℤ_[g]) (u : τ), φ (τ.ρ (GlobalTheory.GLp.red g n k) u) =
      σ.ρ (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k)) (φ u))
    (γ : GL (Fin n) 𝓀[w.adicCompletion E]) :
    τ.character (GeneralLinearGroup.map (resE i hi).toRingHom γ) = LinearMap.trace ℂ _ (levelZero σ.ρ γ) := by
  obtain ⟨hinj, hfix⟩ := fixed_eq_range i hi τ hτ σ ω hω φ h0 hφ
  obtain ⟨x, rfl⟩ := GlobalTheory.LocGL.redK_surjective γ
  obtain ⟨κ, hκ⟩ := DiscreteGroups.sglob.DzIso.exists_of_mem_KO i hi x.2
  rw [resE_redK i hi x κ hκ]
  let e : τ ≃ₗ[ℂ] fixed σ.ρ (KOne (w.adicCompletion E) (Fin n)) :=
    (LinearEquiv.ofInjective φ hinj).trans (LinearEquiv.ofEq _ _ hfix.symm)
  have he : ∀ u : τ, ((e u : fixed σ.ρ (KOne (w.adicCompletion E) (Fin n))) : σ.V) = φ u := fun u => rfl
  have hc : e.conj (τ.ρ (GlobalTheory.GLp.red g n κ)) = levelZero σ.ρ (redK (w.adicCompletion E) (Fin n) x) := by
    ext v
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [he, hφ, hκ, levelZero_apply]
    congr 1
    have := he (e.symm v)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  show LinearMap.trace ℂ τ (τ.ρ (GlobalTheory.GLp.red g n κ)) = _
  rw [← hc, LinearMap.trace_conj']

end UpperTheory.Gal.InertialTypesAlt.TypeCharacters

open UpperTheory.Gal.InertialTypesAlt.TypeCharacters Matrix in
theorem UpperTheory.Gal.InertialTypesAlt.typeChar :
    TypeChar := by
  intro E _ _ v g _ i hi r y τ hτ hinf γ
  obtain ⟨φ, h0, hφ⟩ := hinf
  obtain ⟨ω, hω⟩ := central y
  have hr : r = resE i hi := ringEquiv_eq _ _
  rw [hr]
  exact trace_eq i hi τ hτ y.2.rep ω hω φ h0 hφ γ

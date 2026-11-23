import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.NonemptyUnitaryHeckeParts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocDataT

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem UpperTheory.V.Hi.module_structure_of_commuting {A R P G : Type} [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] [Group G]
    (ρ : Representation A G P) (α : R →+* Module.End A P) (hc : ∀ t g z, α t (ρ g z) = ρ g (α t z)) :
    ∃ (_ : Module R P) (ρR : Representation R G P), (∀ (t : R) (z : P), t • z = α t z) ∧ ∀ g z, ρR g z = ρ g z := by
  letI : Module R P := Module.compHom P α
  have hs : ∀ (t : R) (z : P), t • z = α t z := fun _ _ => rfl
  refine ⟨inferInstance,
    { toFun := fun g =>
        { toFun := fun z => ρ g z
          map_add' := fun x y => map_add _ x y
          map_smul' := fun t z => by rw [hs, RingHom.id_apply, hs, hc] }
      map_one' := by ext z; simp
      map_mul' := fun g h => by ext z; simp }, hs, fun _ _ => rfl⟩
theorem UpperTheory.V.Hi.levelUR2ModPack_alt :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V₀ : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V₀.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : Pa.TWBase (Pa.pairOf B.u) J Empty D) (V : s.Lev) (h : (Pa.globOf r V).Hom (Pa.globOf r V₀)) (q : ℕ) (w : Fin q → Plc L) (rN : Resid (Pa.globOf r V).frame O n), Pa.Glob.Compat h rN (Pa.residOf r) → ∀ (R : Type) [CommRing R] [Algebra O R] [Alg.IsCO O R] (p : Pair rN R) (A : Type) [CommRing A] [Algebra O A] (e : Pa.abelian₂ O Empty D ≃ₐ[O] A) (lam : A →ₐ[O] R), (∀ k, lam (e (MvPowerSeries.X (.inr k))) = algebraMap O R (b.wt.c k) * (p.ψ (b.wt.v k) (b.wt.i k) (b.wt.γ k) : R) - 1) → ∀ β : R →ₐ[O] B.B, p.Maps β.toRingHom ((Pa.pairOf B.u).D.comap h.p₀) (Pa.pairOf B.u).ψ → ∀ (P : Type) [AddCommGroup P] [Module A P] (ρ : Representation A (GV n w) P) (α : R →+* Module.End A P), (∀ a z, α (lam a) z = a • z) → (∀ t g z, α t (ρ g z) = ρ g (α t z)) → Module.Finite A (fixd ρ (Pa.UIw1 l n w)) → ∀ [((Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)).Normal] (ρ' : Representation A (Pa.UIw n w ⧸ (Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)) (fixd ρ (Pa.UIw1 l n w))), (∀ (u : Pa.UIw n w) f, (ρ' (u : Pa.UIw n w ⧸ (Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)) f).1 = ρ u f) → Module.Projective (MonoidAlgebra A (Pa.UIw n w ⧸ (Pa.UIw1 l n w).subgroupOf (Pa.UIw n w))) ρ'.asModule → ∀ eM : fixd ρ (Pa.UK n w) ≃+ b.M, (∀ (t : R) (m m' : fixd ρ (Pa.UK n w)), (m' : P) = α t m → eM m' = β t • eM m) → ∀ ι : Qbar l ≃+* ℂ, (∀ z : P, z ≠ 0 → ∃ (x : R →+* Qbar l) (ρx : (Pa.globOf r V).G₀ →* GL (Fin n) (Qbar l)) (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (π : Representation ℂ (GV n w) Y) (sp : P →+ Y) (σ : ∀ j, SmIrr (GLw n (w j))), sp z ≠ 0 ∧ Continuous ρx ∧ p.D.map x = W.GDet.ofRep (W.mat ρx) ∧ (∀ t y, sp (α t y) = ι (x t) • sp y) ∧ (∀ g y, sp (ρ g y) = π g (sp y)) ∧ (∀ j, IsoSum (π.comp (Pa.atJ n w j)) ⊤ (σ j)) ∧ ∀ j (Bq : ValuationSubring Ω) (hB : IsPlaceOver Bq (w j)) (rc : IrrGL ((w j).adicCompletion L) → WD hB), _root_.UpperTheory.Zero.LLC.IsRecT hB rc → _root_.UpperTheory.V.Z.Win.WOT ι (ρx.comp V.pr) (rc (algNorm (σ j)))) → ∃ M : Pa.LevMod b h w, M.ClassicalAlt := by
  intro l _ L Ω _ _ _ _ _ _ s V₀ O _ _ _ n r B J D b V h q w rN hcomp R _ _ _ p A _ _ e lam hlam β hβ P _ _ ρ α hα hc hfin
    hN ρ' hρ' hproj eM heM ι hcl
  obtain ⟨modR, ρR, hs, hρR⟩ := UpperTheory.V.Hi.module_structure_of_commuting ρ α hc
  letI algL : Algebra (Pa.abelian₂ O Empty D) R := (lam.toRingHom.comp e.toRingEquiv.toRingHom).toAlgebra
  have halg : ∀ a : Pa.abelian₂ O Empty D, algebraMap (Pa.abelian₂ O Empty D) R a = lam (e a) := fun _ => rfl
  haveI towO : IsScalarTower O (Pa.abelian₂ O Empty D) R := IsScalarTower.of_algebraMap_eq fun x => by
    rw [halg, e.commutes, lam.commutes]
  letI modL : Module (Pa.abelian₂ O Empty D) P := Module.compHom P e.toRingEquiv.toRingHom
  have hL : ∀ (a : Pa.abelian₂ O Empty D) (z : P), a • z = e.toRingEquiv a • z := fun _ _ => rfl
  haveI tow : IsScalarTower (Pa.abelian₂ O Empty D) R P := ⟨fun a t z => by
    rw [Algebra.smul_def, halg, mul_smul, hs, hα, hL]; rfl⟩
  obtain ⟨hF, hP⟩ := UpperTheory.V.Hi.levelUR2ProjTr (Pa.abelian₂ O Empty D) A R P (GV n w) e.toRingEquiv hL ρ ρR hρR
    (Pa.UIw n w) (Pa.UIw1 l n w)
  obtain ⟨ρ'', h1, h2⟩ := hP ρ' hρ' hproj
  have hmem : ∀ z : P, z ∈ fixd ρR (Pa.UK n w) ↔ z ∈ fixd ρ (Pa.UK n w) := fun z =>
    forall_congr' fun u => forall_congr' fun _ => by rw [hρR]
  let φ : fixd ρR (Pa.UK n w) ≃+ fixd ρ (Pa.UK n w) :=
    { toFun := fun v => ⟨v.1, (hmem _).1 v.2⟩
      invFun := fun v => ⟨v.1, (hmem _).2 v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let M : Pa.LevMod b h w :=
    { rN := rN
      compat := hcomp
      R := R
      p := p
      segmentWeightExponent := fun k => (halg _).trans (hlam k)
      β := β
      β_pair := hβ
      P := P
      ρ := ρR
      fin := hF hfin
      proj := ⟨hN, ρ'', h1, h2⟩
      eM := φ.trans eM
      eM_smul := fun t m => heM t (φ m) (φ (t • m)) (hs t m.1) }
  refine ⟨M, ι, fun m hm => ?_⟩
  by_contra h0
  obtain ⟨x, ρx, Y, iY, mY, π, sp, σ, hne, hcont, hdet, hsm, hact, hiso, hlg⟩ := hcl m h0
  exact hne (hm
    { θ := x
      rep := ρx
      cont := hcont
      det := hdet
      Y := Y
      π := π
      sp := sp
      sp_smul := fun t y => (congrArg sp (hs t y)).trans (hsm t y)
      sp_act := fun g y => (congrArg sp (hρR g y)).trans (hact g y)
      σ := σ
      iso := hiso
      lg := hlg })
end

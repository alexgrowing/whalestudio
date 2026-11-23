import Formalism.SharpRestriction.LevelLetterCocycles.CongruenceSingleEndomorphism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

noncomputable section

namespace GlobalTheory.Pass

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Polynomial Module TensorProduct
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

variable {D : D7}

def EigSpan (P : PairedCharacterCondition.Pend D) : Prop :=
  ∀ (i : D.nd.Loc) (z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
    (x : D.nd.X i) (c : D.nd.O i),
    (∀ PI : D.naut.AV i, D.naut.ptV i PI = some x → ∀ F ∈ D.naut.typeV i PI,
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) F =
        iotaO D.nd D.naut i c • F) →
    ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, (P.zO i z).baseChange (FractionRing (D.nd.O i)) u = c • u

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

def LocBoundP (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (e : ℕ) : Prop :=
  BlochKatoDuality.lenMod (Submodule.span (Br.OLL D.nbr i w hw) (cutCoc i w hw r Xs M))
                   (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)) ≤
    (e : ℕ∞) * lenOl (Br.PD D.loc D.nbr i w hw) (O := Br.OLL D.nbr i w hw)

def TypeLocus (P : PairedCharacterCondition.Pend D) (i : D.nd.Loc) (k : Fin 2) (Xs : Set (D.nd.X i)) : Prop :=
  ∃ s : D.nd.PlG k → (ZMod (D.host.g k))[X],
    (∀ v, Squarefree (s v) ∧ ∀ u : (ZMod (D.host.g k))ˣ, u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ →
      ¬ (s v).IsRoot (u : ZMod (D.host.g k))) ∧
    ∀ x ∈ Xs, ∃ PI : D.naut.AV i, D.naut.ptV i PI = some x ∧ ∀ v, ∃ τ ∈ P.kty i PI k v, (P.lz k).lab τ = s v

def TypeLGC (P : PairedCharacterCondition.Pend D) : Prop :=
  ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
  ∀ (x : D.nd.X i) (PI : D.naut.AV i), D.naut.ptV i PI = some x → ∀ (v : D.nd.PlG k), ∀ τ ∈ P.kty i PI k v,
    Squarefree ((P.lz k).lab τ) →
    (∀ u : (ZMod (D.host.g k))ˣ, u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ →
      ¬ ((P.lz k).lab τ).IsRoot (u : ZMod (D.host.g k))) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ u : (ZMod (D.host.g k))ˣ, (u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹) ∧
      ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (M : Multiset (Formalism.CyclotomicNorms.Fbar (D.host.g k))),
        (w = D.naut.plGw k v ∧
          M = Formalism.CyclotomicNorms.rootsBar ((P.lz k).lab τ * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)) ∨
        (IsConjPl D.host (D.naut.plGw k v) w ∧
          M = (Formalism.CyclotomicNorms.rootsBar ((P.lz k).lab τ * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)).map (·⁻¹)) →
        D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
        D.naut.mono0 (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) ∧
        ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
          D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) σ =
            (M.map fun y => X - C (P.om k w y σ)).prod

def CentralElt (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (s : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))[X]),
    ∃ (z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
      (L : List (Σ k : Fin 2, D.nd.PlG k)), L.Nodup ∧ (∀ kv, kv ∈ L) ∧
      mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
        (D.what₂.restRowsFiniteGroupCard : ℂ) • (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv))).prod

def StepCut : Prop :=
  ∀ (D : D7) (P : Pend D), DeligneLusztigSeriesSupport (D := D) → admBC (D := D) → LocalGlobalCompatibilityAlt (D := D) → SumRepresentations.tie0 D → tiePar (D := D) →
    SumRepresentations.adm5 D → EigSpan P → CentralElt D →
    ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∀ π ∈ D.nd.Zgood i,
      ∃ (Xs : Set (D.nd.X i)) (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i),
        CutAt i k π Xs β b ∧ TypeLocus P i k Xs

def StepDeg : Prop :=
  ∀ D : D7, tieBr (D := D) → ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k →
    (placesOver D.host.E (D.nd.l i)).ncard = 2 * D.R.f ∧
    ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1

def StepLGC : Prop :=
  ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → IneLGC D

def StepType : Prop :=
  ∀ (D : D7) (P : Pend D), admDZ P → SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → TypeLGC P

def StepPotDirect : Prop :=
  ∀ (D : D7) (P : Pend D), TypeLGC P → FontaineAtPlacesOverL (D := D) → SumRepresentations.tie0 D → tieBr (D := D) → tiePH (D := D) →
    tieChi (D := D) → InertEq D → ElementDenominator.adm12 D → PcrisTensorL D.loc → TieInePoly D →
    ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k →
    ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i r →
    ∀ π ∈ D.nd.Z i, TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → ∀ Xs : Set (D.nd.X i), π ∈ Xs → TypeLocus P i k Xs →
    ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) (D.R.nV + 1)

def StepJumpDirect : Prop :=
  ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (eta s S : ℕ)
    (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ),
    eta + D.R.t + 1 < s → HostJ i r eta s S sg U →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      sg w = true →
      JumpFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) (D.R.nV + 1) (eta + D.R.t + 1) (s + S)

def StepJumpDual : Prop :=
  ∀ D : D7, DualJumpL D.loc → PotDRL D.loc →
    ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (eta s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool)
      (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), eta + D.R.t + 1 < s → HostJ i r eta s S sg U →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ),
      sg w = false → PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
      JumpFam i w hw (fun x : ↥Xs => rDuO D.nd i r x) (D.R.nV + 1) (eta + D.R.t + 1) (s + S)

def StepLift : Prop :=
  ∀ (D : D7) (CT : ℕ), admT (D := D) CT → FontaineAtPlacesOverL (D := D) →
    ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
    ∀ (ι : Type) (Ms : ι → (GE D.nd →* Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i))),
      (∀ x, Continuous fun g => Ms x g) → ∀ eta H : ℕ, eta + D.R.t + 1 < H →
      CT * (H * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.nd.l i →
      PotFam i w hw Ms (D.R.nV + 1) → JumpFam i w hw Ms (D.R.nV + 1) (eta + D.R.t + 1) H →
      LiftFamW i w hw Ms (eMax D CT eta)

def StepSub : Prop :=
  ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i r →
    ∀ π, TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → ∀ Xs : Set (D.nd.X i), π ∈ Xs →
      SubTw i r Xs (WpO D.nd i ρ π) ∧ ∀ c ∈ Finset.Icc 1 D.R.t, SubTw i r Xs (chiRatO D.nd i c)

def StepLocDirect : Prop :=
  ∀ D : D7, LocalPushoutProposition (D := D) → admBK (D := D) → FontaineAtPlacesOverL (D := D) → PotDRL D.loc →
    ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
    ∀ n e : ℕ, PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
      LiftFamW i w hw (fun x : ↥Xs => rTwO D.nd i r x) e →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), SubTw i r Xs M →
      LocBoundP i w hw r Xs M (2 * k * e)

def StepLocDual : Prop :=
  ∀ D : D7, LocalPushoutProposition (D := D) → admBK (D := D) → FontaineAtPlacesOverL (D := D) → PotDRL D.loc →
    ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
    ∀ n e : ℕ, PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
      LiftFamW i w hw (fun x : ↥Xs => rDuO D.nd i r x) e →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), SubTw i r Xs M →
      LocBoundP i w hw r Xs M (2 * k * e)

def StepHfChar : Prop :=
  ∀ (D : D7) (_ : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admTB (D := D) HW F → InertEq D →
    ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → D.nd.l i ≠ 2 →
    ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
      HfChar i w hw

def StepGlobal : Prop :=
  ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (eρ eχ : ℕ),
    GoodR D.nd i r → TruncatedSeriesCountingIdentities.admG1 i r → ResSpan i ρ π → TruncatedSeriesCountingIdentities.admG4 i r → TruncatedSeriesCountingIdentities.admG5 i r →
    TruncatedSeriesCountingIdentities.TameGeneratorConditions i → TruncatedSeriesCountingIdentities.admG6 i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i → SetSQ i r →
    (∃ S : IdempotentChoiceData D.nd i, GoodCongruenceObjects D.nd r ρ π S) → π ∈ D.nd.Z i → π ∈ Xs →
    (∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), HfChar i w hw ∧
      LocBoundP i w hw r Xs (WpO D.nd i ρ π) eρ ∧
      ∀ c ∈ Finset.Icc 1 D.R.t, LocBoundP i w hw r Xs (chiRatO D.nd i c) eχ) →
    Br.sFin D.loc D.nbr i ρ π →
    (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
    vccCut i Xs π ≤
      (((placesOver D.host.E (D.nd.l i)).ncard * (eρ + D.R.t * eχ) : ℕ) : ℚ) +
      Br.sPi D.loc D.nbr i ρ π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) +
      (padicValNat (D.nd.l i) (hE D.host) : ℚ) + 4 * (D.R.nV : ℚ) * D.nd.vdel i +
      (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, vZeta i q

def StepCentral : Prop := CentralIdemCoeff → ∀ (D : D7) (_ : Pend D), CentralElt D

def StepRes : Prop :=
  ∀ D : D7, ResidualAbsIrreducible (D := D) → GaloisFamilyConditions (D := D) →
    ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i r →
      ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → ResSpan i ρ π

def WDAbove (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (x : D.nd.X i) (PI : D.naut.AV i), D.naut.ptV i PI = some x →
    ∀ w ∈ placesOver D.host.E (D.nd.l i), IsSplitPl D.host w →
      D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
      D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w =
        D.naut.lpTw (D.naut.locV i PI w) ((1 - (D.R.nV : ℝ)) / 2)

def StepsNoCut : Prop :=
  CentralIdemCoeff ∧ StepCentral ∧ StepDeg ∧ StepType ∧ StepPotDirect ∧ StepPotDual ∧ StepJumpDirect ∧
    StepJumpDual ∧ StepLift ∧ StepSub ∧ StepCont ∧ StepLocDirect ∧ StepLocDual ∧ StepHfChar ∧ StepRes ∧ StepGlobal

def Steps : Prop :=
  CentralIdemCoeff ∧ StepCentral ∧ StepCut ∧ StepDeg ∧ StepType ∧ StepPotDirect ∧ StepPotDual ∧ StepJumpDirect ∧
    StepJumpDual ∧ StepLift ∧ StepSub ∧ StepCont ∧ StepLocDirect ∧ StepLocDual ∧ StepHfChar ∧ StepRes ∧ StepGlobal

theorem steps_iff : Steps ↔ StepCut ∧ StepsNoCut :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨c, a, b, d⟩, fun ⟨c, a, b, d⟩ => ⟨a, b, c, d⟩⟩

end GlobalTheory.Pass

end

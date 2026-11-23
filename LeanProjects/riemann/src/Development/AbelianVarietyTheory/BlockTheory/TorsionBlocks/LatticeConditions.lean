import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

def nlen {O : Type} [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M] : WithTop ℚ :=
  if Module.length O M = ⊤ then ⊤ else ((lenUnit (O := O) l M : ℚ) : WithTop ℚ)

def addOneIfEqTwo (l : ℕ) (e : ℚ) : ℚ := (if l = 2 then 1 else 0) + e

section Ext

variable {O₀ O' : Type} [CommRing O₀] [IsDomain O₀] [CommRing O'] [IsDomain O']
  (f : O₀ →+* O') (hf : Function.Injective f)

def fracMap : FractionRing O₀ →+* FractionRing O' :=
  IsFractionRing.map (A := O₀) (B := O') (K := FractionRing O₀) (L := FractionRing O') hf

theorem fracMap_alg (c : O₀) :
    fracMap f hf (algebraMap O₀ (FractionRing O₀) c) = algebraMap O' (FractionRing O') (f c) := by
  simp [fracMap, IsFractionRing.map]

def vecMap (k : ℕ) : (Fin k → FractionRing O₀) →ₛₗ[f] (Fin k → FractionRing O') where
  toFun v j := fracMap f hf (v j)
  map_add' u v := by
    funext j
    simp
  map_smul' c v := by
    funext j
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, fracMap_alg]

def pushKO (k : ℕ) : KOG O₀ k →ₛₗ[f] KOG O' k :=
  Submodule.mapQ _ _ (vecMap f hf k) (by
    rintro _ ⟨u, rfl⟩
    refine ⟨fun j => f (u j), ?_⟩
    funext j
    exact (fracMap_alg f hf (u j)).symm)

def extCond {Γ : Type} [Group Γ] [TopologicalSpace Γ] {k : ℕ}
    (ρ₀ : Representation O₀ Γ (KOG O₀ k)) (L₀ : Submodule O₀ (H1 ρ₀))
    (ρ' : Representation O' Γ (KOG O' k)) : Submodule O' (H1 ρ') :=
  ((Submodule.span O' {c : Γ → KOG O' k | ∃ c₀ : Z1 ρ₀, Submodule.Quotient.mk c₀ ∈ L₀ ∧
      c = fun g => pushKO f hf k ((c₀ : Γ → KOG O₀ k) g)}).comap (Z1 ρ').subtype).map
    (Submodule.mkQ _)

end Ext

def SameChar {O₀ O₁ O₂ Γ : Type} [CommRing O₀] [CommRing O₁] [CommRing O₂] [Group Γ]
    (f₁ : O₀ →+* O₁) (f₂ : O₀ →+* O₂) (ψ₁ : Γ →* O₁ˣ) (ψ₂ : Γ →* O₂ˣ) : Prop :=
  ∀ F : Γ →₀ O₀, (F.sum fun g c => f₁ c * ((ψ₁ g : O₁ˣ) : O₁)) = 0 ↔
    (F.sum fun g c => f₂ c * ((ψ₂ g : O₂ˣ) : O₂)) = 0

def atSide {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) : Γ →* A :=
  if b then ψ else ψ⁻¹

section Tw

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} (tw : NTw R H what₂ LL0 N)

def latT (i : tw.Tw) (s : tw.Sig i) : GE N →* Matrix (Fin R.r) (Fin R.r) (tw.O0 i) :=
  twistM ((Units.coeHom _).comp (tw.rhoS i s)) (tw.chi1 i (tw.jS i s) (tw.side i s))⁻¹

def setS (i : tw.Tw) : Set (PlE H) :=
  {v | ((∃ k, v ∈ placesOver H.E (H.g k)) ∨ v ∈ tw.pD i) ∧ v ∉ placesOver H.E (tw.l i)}

def latTpsi (i : tw.Tw) (s : tw.Sig i) {O' : Type} [CommRing O'] (f : tw.O0 i →+* O')
    (ψ : GE N →* O'ˣ) : GE N →* Matrix (Fin R.r) (Fin R.r) O' :=
  twistM (mapM f (latT tw i s)) ψ⁻¹

variable {tw} (L : LocTheory) (nbt : Br.NBrTw tw) (i : tw.Tw) (s : tw.Sig i)
  (Q : Finset (PlE H)) {O' : Type} [CommRing O'] [IsDomain O'] (f : tw.O0 i →+* O')
  (hf : Function.Injective f) (ψ : GE N →* O'ˣ)

open Classical in

def condL : ∀ v, Submodule O'
    (H1 ((WKG (latTpsi tw i s f ψ)).comp (Dec (F := H.E) (N.plOm.1 v)).subtype)) :=
  fun v => if h : v ∈ placesOver H.E (tw.l i) then
    extCond f hf ((WKG (latT tw i s)).comp (decS N v)) (Br.bkTw L nbt i v h (latT tw i s))
      ((WKG (latTpsi tw i s f ψ)).comp (Dec (F := H.E) (N.plOm.1 v)).subtype)
  else ⊤

def selT : Submodule O' (H1 (WKG (latTpsi tw i s f ψ))) :=
  Formalism.GaloisCohomology.SelAll (WKG (latTpsi tw i s f ψ)) N.plOm
    (Formalism.GaloisCohomology.bkCond (WKG (latTpsi tw i s f ψ)) N.plOm (tw.l i) (setS tw i ∪ ↑Q)
      (condL L nbt i s f hf ψ))

def sT : WithTop ℚ := nlen (O := O') (tw.l i) ↥(selT L nbt i s Q f hf ψ)

variable (tw)

def toOk (i : tw.Tw) (k : ℕ) : tw.O0 i →+* tw.Ok i k :=
  (algebraMap (tw.O i) (tw.Ok i k)).comp (algebraMap (tw.O0 i) (tw.O i))

theorem toOk_inj (i : tw.Tw) (k : ℕ) : Function.Injective (toOk tw i k) :=
  (tw.Ok_inj i k).comp (tw.O_inj i)

theorem twO_inj (a : N.Loc) : Function.Injective (tw.twist₂ a) := by
  haveI : CharZero (FractionRing (N.O a)) := (N.embK a).charZero_iff (N.embK a).injective |>.1 inferInstance
  haveI : CharZero (N.O a) := (algebraMap (N.O a) (FractionRing (N.O a))).charZero
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hp : (RingHom.ker (tw.twist₂ a)).IsPrime := RingHom.ker_isPrime _
  have hm : (RingHom.ker (tw.twist₂ a)).IsMaximal := hp.isMaximal hne
  have he := IsLocalRing.eq_maximalIdeal hm
  haveI := tw.twistBaseCoefficientRing_residueField_finite (tw.twOf a)
  haveI := Fintype.ofFinite (IsLocalRing.ResidueField (tw.O0 (tw.twOf a)))
  have h0 : ((Fintype.card (IsLocalRing.ResidueField (tw.O0 (tw.twOf a))) : ℕ) :
      IsLocalRing.ResidueField (tw.O0 (tw.twOf a))) = 0 := FiniteField.cast_card_eq_zero _
  have h1 : ((Fintype.card (IsLocalRing.ResidueField (tw.O0 (tw.twOf a))) : ℕ) :
      tw.O0 (tw.twOf a)) ∈ RingHom.ker (tw.twist₂ a) := by
    rw [he, ← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact h0
  rw [RingHom.mem_ker, map_natCast, Nat.cast_eq_zero] at h1
  exact Fintype.card_ne_zero h1

end Tw

section Rec

variable (D : D7)

def sPiTop (a : D.nd.Loc) (ρ : D.nd.X a → (GE D.nd →* GL (Fin D.R.r) (D.nd.O a))) (π : D.nd.X a) :
    WithTop ℚ :=
  nlen (O := D.nd.O a) (D.nd.l a) ↥(Br.selPi D.loc D.nbr a ρ π)

def sTLoc (a : D.nd.Loc) (s : D.ntw.Sig (D.ntw.twOf a)) : WithTop ℚ :=
  sT D.loc D.ntwbr (D.ntw.twOf a) s (D.nd.Q a) (D.ntw.twist₂ a) (twO_inj D.ntw a) (D.ntw.psiL a)

def sTBig (i : D.ntw.Tw) (s : D.ntw.Sig i) (Q : Finset (PlE D.host)) (k : ℕ)
    (ψ : GE D.nd →* (D.ntw.Ok i k)ˣ) : WithTop ℚ :=
  sT D.loc D.ntwbr i s Q (toOk D.ntw i k) (toOk_inj D.ntw i k) (atSide (D.ntw.side i s) ψ)

def IsTwistOf (a : D.nd.Loc) (k : ℕ) (ψ : GE D.nd →* (D.ntw.Ok (D.ntw.twOf a) k)ˣ) : Prop :=
  (∀ g, ψ g ∈ Subgroup.zpowers (D.ntw.zk (D.ntw.twOf a) k)) ∧
  SameChar (D.ntw.twist₂ a) (toOk D.ntw (D.ntw.twOf a) k) (D.ntw.psiL a) (atSide (D.ntw.twSide a) ψ)

def IsRhoPt (a : D.nd.Loc) (π : D.nd.X a) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a))) ∧
  ∃ r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O a), IsHeckeGalois D.nd a π r ∧
    ∃ e : (Fin D.R.nV → KK D.nd a) ≃ₗ[KK D.nd a] ((Fin D.R.r → KK D.nd a) × (Fin D.R.t → KK D.nd a)),
      ∀ g u, e ((mapM (toK D.nd a) ((Units.coeHom _).comp r) g).mulVec u) =
        ((mapM (toK D.nd a) ((Units.coeHom _).comp ρ) g).mulVec (e u).1,
          fun c : Fin D.R.t =>
            toK D.nd a ((D.nd.chi a ((c : ℕ) + 1) g : (D.nd.O a)ˣ) : D.nd.O a) * (e u).2 c)

def GoodRowOf (j : ℕ) (σ : D.what₂.FT) : Prop := D.nd.goodRow σ ∧ D.what₂.isot j σ ≠ ⊥

def IsTriple (a : D.nd.Loc) (s : D.ntw.Sig (D.ntw.twOf a)) (Sg : List (Part D.naut.CG)) : Prop :=
  D.ntw.jS _ s = D.nd.j a ∧ D.ntw.side _ s = D.ntw.twSide a ∧
  IsSSRep (mapRep (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a))))
    (D.ntw.rhoS _ s)) ∧
  ∀ᶠ w in Filter.cofinite, SplitOut D.nd a w →
    ∀ (B : ValuationSubring D.nd.Om) (γ : GE D.nd), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) γ →
      ((D.ntw.rhoS _ s γ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly.map
          ((iotaO D.nd D.naut a).comp (D.ntw.twist₂ a)) =
        galPol D.naut (D.naut.lpTw (isoLoc D.nd D.naut (twistIso D.nd D.naut Sg D.naut.etaTinv) w)
          ((1 - (D.R.nV : ℝ)) / 2))

def AllTriples : Prop :=
  ∀ (a : D.nd.Loc) (σ : D.what₂.FT) (Sg : List (Part D.naut.CG)), GoodRowOf D (D.nd.j a) σ →
    HasParamW D.nd D.naut a σ Sg → ∃ s, IsTriple D a s Sg

def Attached (a : D.nd.Loc) (π : D.nd.X a) (s : D.ntw.Sig (D.ntw.twOf a)) : Prop :=
  ∃ (σ : D.what₂.FT) (Sg : List (Part D.naut.CG)), GoodRowOf D (D.nd.j a) σ ∧
    HasParamW D.nd D.naut a σ Sg ∧ HasParamX D.nd D.naut a π Sg ∧ IsTriple D a s Sg

def TwistA : Prop :=
  ∀ a : D.nd.Loc, ∃ (k : ℕ) (ψ : GE D.nd →* (D.ntw.Ok (D.ntw.twOf a) k)ˣ), IsTwistOf D a k ψ ∧
    ∃ ε : D.ntw.Sig (D.ntw.twOf a) → ℚ, (∀ s, 0 ≤ ε s) ∧ ∑ s, ε s ≤ ((D.nd.l a : ℚ) ^ 2)⁻¹ ∧
      ∀ s, sTBig D _ s (D.nd.Q a) k ψ ≤ ((addOneIfEqTwo (D.nd.l a) (ε s) : ℚ) : WithTop ℚ)

def Corr : Prop :=
  ∀ (a : D.nd.Loc) (π : D.nd.X a), π ∈ D.nd.Zgood a →
    (∃ s, Attached D a π s) ∧
    ∀ s, Attached D a π s →
      ∀ ρ : D.nd.X a → (GE D.nd →* GL (Fin D.R.r) (D.nd.O a)), IsRhoPt D a π (ρ π) →
        (∃ P : GL (Fin D.R.r) (D.nd.O a), ∀ g,
          WpO D.nd a ρ π g * (P : Matrix _ _ _) =
            (P : Matrix _ _ _) * latTpsi D.ntw _ s (D.ntw.twist₂ a) (D.ntw.psiL a) g) ∧
        sPiTop D a ρ π = sTLoc D a s ∧
        ∀ k ψ, IsTwistOf D a k ψ → sPiTop D a ρ π = sTBig D _ s (D.nd.Q a) k ψ

def Bound : Prop :=
  ∀ (a : D.nd.Loc) (π : D.nd.X a), π ∈ D.nd.Zgood a →
    ∀ ρ : D.nd.X a → (GE D.nd →* GL (Fin D.R.r) (D.nd.O a)), IsRhoPt D a π (ρ π) →
      Br.sFin D.loc D.nbr a ρ π ∧
      Br.sPi D.loc D.nbr a ρ π ≤ addOneIfEqTwo (D.nd.l a) ((D.nd.l a : ℚ) ^ 2)⁻¹

def selmerTie_at : Prop := AllTriples D → Corr D ∧ (TwistA D → Bound D)

end Rec

def selmerTieF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, selmerTie_at (Fm.D x i)

def selmerTie (𝒞 : FamClass) : Prop := Closed 𝒞 (fun Fm _ => selmerTieF Fm)

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

end

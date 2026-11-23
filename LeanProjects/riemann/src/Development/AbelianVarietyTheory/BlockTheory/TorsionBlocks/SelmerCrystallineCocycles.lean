import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.GaloisCohomology.Statement
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.WeaklyAdmissibleFiltrations.Statement
import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open scoped ENNReal Matrix

def len_vp (O : Type) [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M] : ℝ≥0∞ :=
  (Module.length O M : ℝ≥0∞) / (Module.length O (O ⧸ Ideal.span {(l : O)}) : ℝ≥0∞)

def val_vp {O : Type} [CommRing O] (l : ℕ) (x : O) : ℝ≥0∞ :=
  len_vp O l (O ⧸ Ideal.span {x})

section Rep

variable {Γ A : Type} [Group Γ] [CommRing A] {m : ℕ}

def twist (ρ : Γ →* GL (Fin m) A) (χ : Γ →* Aˣ) : Γ →* GL (Fin m) A where
  toFun g := Matrix.GeneralLinearGroup.scalar (Fin m) (χ g) * ρ g
  map_one' := by simp
  map_mul' g h := by
    have hc : ρ g * Matrix.GeneralLinearGroup.scalar (Fin m) (χ h) =
        Matrix.GeneralLinearGroup.scalar (Fin m) (χ h) * ρ g := by
      apply Units.ext
      exact ((Matrix.scalar_commute ((χ h : Aˣ) : A) (fun _ => Commute.all _ _)
        ((ρ g : GL (Fin m) A) : Matrix (Fin m) (Fin m) A)).eq).symm
    rw [map_mul, map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (ρ g), hc]
    simp only [mul_assoc]

def dualMat (ρ : Γ →* GL (Fin m) A) (g : Γ) : Matrix (Fin m) (Fin m) A :=
  ((ρ g⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A)ᵀ

end Rep

section Div

variable {Γ O' : Type} [Group Γ] [CommRing O'] [IsDomain O'] {m : ℕ}

def actDiv (ρ : Γ →* GL (Fin m) O') (g : Γ) : (Fin m → KmodO O') →ₗ[O'] (Fin m → KmodO O') :=
  LinearMap.pi fun i => ∑ j, ((ρ g : GL (Fin m) O') : Matrix (Fin m) (Fin m) O') i j •
    (LinearMap.proj j : (Fin m → KmodO O') →ₗ[O'] KmodO O')

def cobOn (ρ : Γ →* GL (Fin m) O') (J : Subgroup Γ) : Submodule O' (Γ → Fin m → KmodO O') where
  carrier := {c | ∃ x, ∀ g ∈ J, c g = actDiv ρ g x - x}
  zero_mem' := ⟨0, fun g _ => by simp⟩
  add_mem' := by
    rintro a b ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨x + y, fun g hg => ?_⟩
    simp only [Pi.add_apply, hx g hg, hy g hg, map_add]
    abel
  smul_mem' := by
    rintro c a ⟨x, hx⟩
    refine ⟨c • x, fun g hg => ?_⟩
    rw [Pi.smul_apply, hx g hg, map_smul, smul_sub]

def cocDiv [TopologicalSpace Γ] (ρ : Γ →* GL (Fin m) O') : Submodule O' (Γ → Fin m → KmodO O') where
  carrier := {c | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + actDiv ρ g (c h)}
  zero_mem' := ⟨IsLocallyConstant.const 0, fun g h => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨ha.add hb, fun g h => ?_⟩
    simp only [Pi.add_apply, ha', hb', map_add]
    abel
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨ha.comp (c • ·), fun g h => ?_⟩
    rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, ha', map_smul, smul_add]

end Div

section BK

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

def IsCrysCocycle (T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀) (f : ↥Gw → Fin m → O₀) : Prop :=
  (fun (g : ↥(Loc.GK Bw.Kw)) (j : Fin m) => Bw.toLL (f (Bw.e.symm g) j)) ∈
    Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep (T.comp Gw.subtype))

variable {O' : Type} [CommRing O'] [IsDomain O'] (ι : O₀ →+* O')

def crysSpan (T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀) : Submodule O' (↥Gw → Fin m → KmodO O') :=
  Submodule.span O' {c | ∃ (a : FractionRing O') (f : ↥Gw → Fin m → O₀), IsCrysCocycle Bw P T f ∧
    ∀ g j, c g j = Submodule.Quotient.mk (a * algebraMap O' (FractionRing O') (ι (f g j)))}

def bkAt (T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀) : Submodule O' ((Ω ≃ₐ[E] Ω) → Fin m → KmodO O') :=
  (crysSpan Bw P ι T ⊔ cobOn ((mapRep ι T).comp Gw.subtype) ⊤).comap
    (LinearMap.funLeft O' (Fin m → KmodO O') (Subtype.val : ↥Gw → (Ω ≃ₐ[E] Ω)))

end BK

def IsWildAt {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (σ : G E Ω) : Prop :=
  ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1

section HidaSetting

variable (D : D7) (i : D.ntw.Tw)

abbrev GE : Type := G D.host.E D.nd.Om

abbrev decAt (v : PlE D.host) : Subgroup (GE D) := Dec (F := D.host.E) (D.nd.plOm.1 v)

abbrev ineAt (v : PlE D.host) : Subgroup (GE D) := Ine (F := D.host.E) (D.nd.plOm.1 v)

def cyc : GE D →* (D.ntw.O0 i)ˣ :=
  (Units.map (algebraMap ℤ_[D.ntw.l i] (D.ntw.O0 i)).toMonoidHom).comp
    (cycZ (F := D.host.E) (Ω := D.nd.Om) (D.ntw.l i))

def chiOf (s : D.ntw.Sig i) : GE D →* (D.ntw.O0 i)ˣ :=
  D.ntw.chi1 i (D.ntw.jS i s) (D.ntw.side i s)

def latT (s : D.ntw.Sig i) : GE D →* GL (Fin D.R.r) (D.ntw.O0 i) :=
  twist (D.ntw.rhoS i s) (chiOf D i s)⁻¹

def setS : Set (PlE D.host) :=
  {v | (v ∈ placesOver D.host.E (D.host.g 0) ∨ v ∈ placesOver D.host.E (D.host.g 1) ∨ v ∈ D.ntw.pD i) ∧
    v ∉ placesOver D.host.E (D.ntw.l i)}

def toOk (k : ℕ) : D.ntw.O0 i →+* D.ntw.Ok i k :=
  (algebraMap (D.ntw.O i) (D.ntw.Ok i k)).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))

def twistedT (s : D.ntw.Sig i) (k : ℕ) (ψ : GE D →* (D.ntw.Ok i k)ˣ) :
    GE D →* GL (Fin D.R.r) (D.ntw.Ok i k) :=
  twist (mapRep (toOk D i k) (latT D i s)) ψ⁻¹

def selCoc (s : D.ntw.Sig i) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : GE D →* (D.ntw.Ok i k)ˣ) :
    Submodule (D.ntw.Ok i k) (GE D → Fin D.R.r → KmodO (D.ntw.Ok i k)) :=
  cocDiv (twistedT D i s k ψ) ⊓
    (⨅ (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.ntw.l i)),
      bkAt (D.ntwbr i w hw) (D.loc (D.ntw.l i)) (toOk D i k) (latT D i s)) ⊓
    ⨅ (v : PlE D.host) (_ : v ∉ placesOver D.host.E (D.ntw.l i)) (_ : v ∉ setS D i) (_ : v ∉ Q),
      cobOn (twistedT D i s k ψ) (ineAt D v)

abbrev Selmer (s : D.ntw.Sig i) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : GE D →* (D.ntw.Ok i k)ˣ) : Type :=
  ↥(selCoc D i s k Q ψ) ⧸ (cobOn (twistedT D i s k ψ) ⊤).comap (selCoc D i s k Q ψ).subtype

def selLen_vp (s : D.ntw.Sig i) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : GE D →* (D.ntw.Ok i k)ˣ) : ℝ≥0∞ :=
  len_vp (D.ntw.Ok i k) (D.ntw.l i) (Selmer D i s k Q ψ)

def readAt (s : D.ntw.Sig i) {k : ℕ} (ψ : GE D →* (D.ntw.Ok i k)ˣ) : GE D →* (D.ntw.Ok i k)ˣ :=
  if D.ntw.side i s then ψ else ψ⁻¹

def Unram (s : D.ntw.Sig i) : Prop :=
  ∀ v : PlE D.host, v ∉ placesOver D.host.E (D.ntw.l i) → v ∉ setS D i → ∀ σ ∈ ineAt D v, latT D i s σ = 1

def SelfDual (s : D.ntw.Sig i) : Prop :=
  ∃ U : GL (Fin D.R.r) (D.ntw.O0 i), ∀ g g' : GE D, (∀ x, g' x = D.ntw.cc (g (D.ntw.cc.symm x))) →
    (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)) *
        ((((cyc D i g) ^ D.R.t : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) •
          ((latT D i s g : GL (Fin D.R.r) (D.ntw.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i))) =
      (((cyc D i g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) • dualMat (latT D i s) g') *
        (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i))

def ResAbsIrr (s : D.ntw.Sig i) : Prop :=
  AbsIrrSub (mapRep (IsLocalRing.residue (D.ntw.O0 i)) (latT D i s)) ⊤

def repV (s : D.ntw.Sig i) : GE D →* GL (Fin D.R.r) (FractionRing (D.ntw.O0 i)) :=
  mapRep (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))) (latT D i s)

def NoLocalInv (s : D.ntw.Sig i) : Prop :=
  ∀ v : PlE D.host,
    (∀ x : Fin D.R.r → FractionRing (D.ntw.O0 i),
      (∀ σ ∈ decAt D v, ((repV D i s σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _) *ᵥ x = x) → x = 0) ∧
    ∀ x : Fin D.R.r → FractionRing (D.ntw.O0 i),
      (∀ σ ∈ decAt D v, algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))
        ((cyc D i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) • (dualMat (repV D i s) σ *ᵥ x) = x) → x = 0

def DeRhamGap (s : D.ntw.Sig i) : Prop :=
  ∀ (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.ntw.l i)),
    (D.ntwbr i w hw).IsdRW (D.loc (D.ntw.l i)) ((latT D i s).comp (decAt D w).subtype) ∧
    ∀ (τ : ↥(D.ntwbr i w hw).Kw.1 →ₐ[ℚ_[D.ntw.l i]] ↥(D.ntwbr i w hw).LL.1) (a : ℤ),
      (D.ntwbr i w hw).IsJumpW (D.loc (D.ntw.l i)) ((latT D i s).comp (decAt D w).subtype) τ a →
        a < -1 ∨ (D.R.t : ℤ) < a

def InertiaOverG (s : D.ntw.Sig i) : Prop :=
  ∀ (k : Fin 2) (v : PlE D.host), v ∈ placesOver D.host.E (D.host.g k) →
    v ∉ placesOver D.host.E (D.ntw.l i) →
    (∀ σ : GE D, IsWildAt (D.nd.plOm.1 v) σ → D.ntw.rhoS i s σ = 1 ∧ chiOf D i s σ = 1) ∧
    ∀ γ : GE D, TameGenAt (D.nd.plOm.1 v) γ →
      ¬ (((mapRep (IsLocalRing.residue (D.ntw.O0 i)) (D.ntw.rhoS i s) γ : GL _ _) :
          Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.ntw.O0 i))).charpoly).IsRoot
        (IsLocalRing.residue (D.ntw.O0 i) ((chiOf D i s γ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i))

def InertiaOverP (s : D.ntw.Sig i) : Prop :=
  ∀ v ∈ D.ntw.pD i, ∀ σ ∈ ineAt D v, D.ntw.rhoS i s σ = 1

def NonCyclotomic : Prop :=
  D.ntw.l i = 2 ∨
  (∀ v : PlE D.host, ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal ^ 2) ∨
  D.R.t * D.R.r < Module.finrank D.host.E
    ↥(IntermediateField.adjoin D.host.E {x : D.nd.Om | x ^ D.ntw.l i = 1})

def Hyps : Prop :=
  (∀ v ∈ setS D i, IsSplitPl D.host v) ∧ True ∧
  ∀ s : D.ntw.Sig i, Unram D i s ∧ SelfDual D i s ∧ ResAbsIrr D i s ∧ NoLocalInv D i s ∧
    DeRhamGap D i s ∧ InertiaOverG D i s ∧ InertiaOverP D i s

def IsConjStableSplitPlaces (A Q : Finset (PlE D.host)) : Prop :=
  (∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q) ∧
  ∀ P ∈ Q, IsSplitPl D.host P ∧ (Ideal.absNorm P.asIdeal).Prime ∧ P ∉ D.ntw.S0 i ∧ P ∉ A

def TwistShape (k : ℕ) (Q : Finset (PlE D.host)) (ζ : (D.ntw.Ok i k)ˣ) (ψ : GE D →* (D.ntw.Ok i k)ˣ) :
    Prop :=
  IsOpen (ψ.ker : Set (GE D)) ∧ AntiHom D.ntw.cc ψ ∧ (∀ g, ψ g ∈ Subgroup.zpowers ζ) ∧
  RamExactly ψ (↑Q : Set (PlE D.host)) ∧
  (∀ P ∈ Q, ∀ B : ValuationSubring D.nd.Om, IsPlaceOver B P → ∀ σ : GE D, IsWildAt B σ → ψ σ = 1) ∧
  ∀ w ∈ placesOver D.host.E (D.ntw.l i), ∀ B : ValuationSubring D.nd.Om, IsPlaceOver B w →
    ∀ σ ∈ Dec (F := D.host.E) B, ψ σ = 1

def cycCost : ℕ∞ :=
  ⨅ g : GE D, emultiplicity ((D.ntw.l i : ℕ) : ℤ_[D.ntw.l i])
    (((ReciprocityTheory.Gal.cycZ D.host.E D.nd.Om (D.ntw.l i) g : ℤ_[D.ntw.l i]ˣ) : ℤ_[D.ntw.l i]) ^ (D.R.t * D.R.r) - 1)

def SelmerBound (ε' : ℝ) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : GE D →* (D.ntw.Ok i k)ˣ) : Prop :=
  ∃ ε : D.ntw.Sig i → ℝ, (∀ s, 0 ≤ ε s) ∧ ∑ s, ε s ≤ ε' ∧
    ∀ s, selLen_vp D i s k Q (readAt D i s ψ) ≤
      ENNReal.ofReal (((cycCost D i).toNat : ℝ) + ε s)

def InertiaBound (ε' : ℝ) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : GE D →* (D.ntw.Ok i k)ˣ) : Prop :=
  ∀ γ : PlE D.host → GE D, (∀ P ∈ Q, TameGenAt (D.nd.plOm.1 P) (γ P)) →
    (D.R.t : ℝ≥0∞) * ∑ P ∈ Q, val_vp (D.ntw.l i) (((ψ (γ P) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) - 1) ≤
      ENNReal.ofReal ε'

def TwistExists : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ∀ A : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k : ℕ) (ψ : (D.ntw.Ok i k)ˣ → (GE D →* (D.ntw.Ok i k)ˣ)),
      IsConjStableSplitPlaces D i A Q ∧
      (∀ ζ : (D.ntw.Ok i k)ˣ, IsPrimitiveRoot ζ (D.ntw.l i ^ k) →
        ∀ a : ℕ, a.Coprime (D.ntw.l i) → ψ (ζ ^ a) = ψ ζ ^ a) ∧
      ∀ ζ : (D.ntw.Ok i k)ˣ, IsPrimitiveRoot ζ (D.ntw.l i ^ k) →
        TwistShape D i k Q ζ (ψ ζ) ∧ SelmerBound D i ε' k Q (ψ ζ) ∧ InertiaBound D i ε' k Q (ψ ζ)

end HidaSetting

def TwistKillsSelmer (D : D7) : Prop :=
  ∀ i : D.ntw.Tw, D.ntw.NonzeroIndexPlace i → Hyps D i → TwistExists D i

example (D : D7) (i : D.ntw.Tw) (k : ℕ) : IsPrimitiveRoot (D.ntw.zk i k) (D.ntw.l i ^ k) :=
  IsPrimitiveRoot.coe_units_iff.mp (D.ntw.zk_prim i k)

example (D : D7) (i : D.ntw.Tw) (ε' : ℝ) (k : ℕ) (ψ : GE D →* (D.ntw.Ok i k)ˣ) :
    InertiaBound D i ε' k ∅ ψ := fun _ _ => by simp

example {O : Type} [CommRing O] (l : ℕ) : val_vp l (1 : O) = 0 := by
  haveI : Subsingleton (O ⧸ Ideal.span {(1 : O)}) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
  simp [val_vp, len_vp, Module.length_eq_zero]

end GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions ReciprocityTheory.Gal

namespace GlobalTheory.IndefiniteRowSideFullHecke.LengthValuationTwists

section Val

variable (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

def ordFrac (x : FractionRing A) : ℤ :=
  - WithZero.log ((IsDiscreteValuationRing.maximalIdeal A).valuation (FractionRing A) x)

open Classical in

def val_vp (l : ℕ) (x : FractionRing A) : EReal :=
  if x = 0 then ⊤ else (((ordFrac A x : ℝ) / (ordFrac A (l : FractionRing A) : ℝ) : ℝ) : EReal)

def len_vp (l : ℕ) (n : ℕ∞) : EReal :=
  if n = ⊤ then ⊤ else (((n.toNat : ℝ) / (ordFrac A (l : FractionRing A) : ℝ) : ℝ) : EReal)

example (l : ℕ) : val_vp A l 0 = ⊤ := by simp [val_vp]

example (l : ℕ) : val_vp A l 1 = 0 := by simp [val_vp, ordFrac]

end Val

section Mat

variable {Γ : Type} [Group Γ] {A : Type} [CommRing A] {n : ℕ}

def twistGL (ρ : Γ →* GL (Fin n) A) (χ : Γ →* Aˣ) : Γ →* GL (Fin n) A where
  toFun g := χ g • ρ g
  map_one' := by simp
  map_mul' g h := by
    apply Units.ext
    simp [Units.smul_def, smul_smul, mul_comm]

def matRepOn (N : Type) [AddCommGroup N] [Module A N] (ρ : Γ →* GL (Fin n) A) :
    Representation A Γ (Fin n → N) where
  toFun g :=
    { toFun := fun m i => ∑ j, (ρ g : Matrix (Fin n) (Fin n) A) i j • m j
      map_add' := fun m m' => by
        funext i
        simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun c m => by
        funext i
        simp [Finset.smul_sum, smul_smul, mul_comm] }
  map_one' := by
    apply LinearMap.ext
    intro m
    funext i
    simp [Matrix.one_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro m
    funext i
    simp only [map_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_smul, LinearMap.coe_mk,
      AddHom.coe_mk, Module.End.mul_apply, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm

end Mat

def DivMod (A : Type) [CommRing A] [IsDomain A] (n : ℕ) : Type := Fin n → KmodO A

section DivInst

variable (A : Type) [CommRing A] [IsDomain A] (n : ℕ)

instance : AddCommGroup (DivMod A n) := inferInstanceAs (AddCommGroup (Fin n → KmodO A))
instance : Module A (DivMod A n) := inferInstanceAs (Module A (Fin n → KmodO A))
instance : TopologicalSpace (DivMod A n) := ⊥
instance : DiscreteTopology (DivMod A n) := ⟨rfl⟩
instance : IsTopologicalAddGroup (DivMod A n) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

def divRep {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin n) A) : Representation A Γ (DivMod A n) :=
  matRepOn (KmodO A) ρ

end DivInst

def wildSet (E : Type) {Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) :
    Set (G E Ω) :=
  {σ | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}

def TLoc : Prop := LocalFiniteness ∧ LocalTateDuality ∧ LocalEulerChar ∧ UnramifiedOrthogonality

def TGlob : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
    0 < r → ContainsAbove S l → ContAction ρ →
      Finite (H0 ρ) ∧ Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ (∀ n, 3 ≤ n → Subsingleton (Hn ρ n)) ∧
      Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M ^ InfinitePlace.nrComplexPlaces F =
        Nat.card (H1 ρ)

section PT

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)

def IsInvMap (ζ : Ω) (v : S)
    (inv : H2 ((charRep μ).comp (locFam S Av v)) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) : Prop :=
  ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) (Av v) → ZMod (l ^ r))
    (z : Z2 ((charRep μ).comp (locFam S Av v))),
    ϖ ∈ v.1.asIdeal → ϖ ∉ v.1.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) →
    (∀ g : Dec (F := F) (Av v), (g : G F Ω) y = ζ ^ (κ g).val * y) →
    (∀ g h, χ (g * h) = χ g + χ h) →
    (∀ g : Dec (F := F) (Av v), (g : G F Ω) ∈ Ine (F := F) (Av v) → χ g = 0) →
    (∀ g : Dec (F := F) (Av v), IsFrob (F := F) (Av v) (normV v.1) (g : G F Ω) → χ g = 1) →
    (∀ g h, z.1 (g, h) = κ g * χ h) →
    inv (Submodule.Quotient.mk z) = 1

variable (inv : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)

def loc0 : H0 ρ →ₗ[ZMod (l ^ r)] ∀ v : S, H0 (ρ.comp (locFam S Av v)) :=
  LinearMap.pi fun v => resH0 ρ (locFam S Av v)

def loc1 : H1 ρ →ₗ[ZMod (l ^ r)] ∀ v : S, H1 (ρ.comp (locFam S Av v)) :=
  LinearMap.pi fun v => ReciprocityTheory.Gal.resH1 ρ (locFam S Av v) (continuous_locFam S Av v)

def loc2 : H2 ρ →ₗ[ZMod (l ^ r)] ∀ v : S, H2 (ρ.comp (locFam S Av v)) :=
  LinearMap.pi fun v => resH2 ρ (locFam S Av v) (continuous_locFam S Av v)

def tr0 : (∀ v : S, H0 (ρ.comp (locFam S Av v))) →ₗ[ZMod (l ^ r)]
    Module.Dual (ZMod (l ^ r)) (H2 (twDual μ ρ)) :=
  ∑ v : S, (((cupH0H2TwistedDual μ ρ (locFam S Av v)).compr₂ (inv v).toLinearMap).compl₁₂ (LinearMap.proj v)
    (resH2 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v)))

def tr1 (hρ : ContAction ρ) : (∀ v : S, H1 (ρ.comp (locFam S Av v))) →ₗ[ZMod (l ^ r)]
    Module.Dual (ZMod (l ^ r)) (H1 (twDual μ ρ)) :=
  ∑ v : S, (((cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v))).flip.compr₂
    (inv v).toLinearMap).compl₁₂ (LinearMap.proj v)
    (ReciprocityTheory.Gal.resH1 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v)))

def tr2 : (∀ v : S, H2 (ρ.comp (locFam S Av v))) →ₗ[ZMod (l ^ r)]
    Module.Dual (ZMod (l ^ r)) (H0 (twDual μ ρ)) :=
  ∑ v : S, (((cup20 μ ρ (locFam S Av v)).compr₂ (inv v).toLinearMap).compl₁₂ (LinearMap.proj v)
    (resH0 (twDual μ ρ) (locFam S Av v)))

def NineTermExact (hρ : ContAction ρ) : Prop :=
  ∃ (δ₁ : Module.Dual (ZMod (l ^ r)) (H2 (twDual μ ρ)) →ₗ[ZMod (l ^ r)] H1 ρ)
    (δ₂ : Module.Dual (ZMod (l ^ r)) (H1 (twDual μ ρ)) →ₗ[ZMod (l ^ r)] H2 ρ),
    Function.Injective (loc0 S Av ρ) ∧
    Function.Exact (loc0 S Av ρ) (tr0 S Av μ inv ρ) ∧
    Function.Exact (tr0 S Av μ inv ρ) δ₁ ∧
    Function.Exact δ₁ (loc1 S Av ρ) ∧
    Function.Exact (loc1 S Av ρ) (tr1 S Av μ inv ρ hρ) ∧
    Function.Exact (tr1 S Av μ inv ρ hρ) δ₂ ∧
    Function.Exact δ₂ (loc2 S Av ρ) ∧
    Function.Exact (loc2 S Av ρ) (tr2 S Av μ inv ρ) ∧
    Function.Surjective (tr2 S Av μ inv ρ)

end PT

def PoitouTate : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l →
  ∀ (Av : S → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v.1) →
  ∀ μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ,
    μ.comp (toGS Ω _) = cycMod F Ω l r →
  ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) →
  ∃ inv : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r),
    (∀ v, IsInvMap S Av μ ζ v (inv v)) ∧
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
      [DiscreteTopology M]
      (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
      (hρ : ContAction ρ), NineTermExact S Av μ inv ρ hρ

section HidaSetting

variable (D : D7) (i : D.ntw.Tw)

abbrev GE : Type := G D.host.E D.nd.Om

abbrev DecAt (w : PlE D.host) : Subgroup (GE D) := Dec (F := D.host.E) (D.nd.plOm.1 w)

abbrev PlL : Set (PlE D.host) := placesOver D.host.E (D.ntw.l i)

def Sset : Set (PlE D.host) :=
  {v | ((∃ k, v ∈ placesOver D.host.E (D.host.g k)) ∨ v ∈ D.ntw.pD i) ∧ v ∉ PlL D i}

def eps : GE D →* (D.ntw.O0 i)ˣ :=
  (Units.map (algebraMap ℤ_[D.ntw.l i] (D.ntw.O0 i)).toMonoidHom).comp
    (cycZ D.host.E D.nd.Om (D.ntw.l i))

def chiS (s : D.ntw.Sig i) : GE D →* (D.ntw.O0 i)ˣ :=
  D.ntw.chi1 i (D.ntw.jS i s) (D.ntw.side i s)

def Trep (s : D.ntw.Sig i) : GE D →* GL (Fin D.R.r) (D.ntw.O0 i) :=
  twistGL (D.ntw.rhoS i s) (chiS D i s)⁻¹

def Vmat (s : D.ntw.Sig i) (g : GE D) :
    Matrix (Fin D.R.r) (Fin D.R.r) (FractionRing (D.ntw.O0 i)) :=
  ((Trep D i s g : GL (Fin D.R.r) (D.ntw.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)).map
    (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)))

def VdualMat (s : D.ntw.Sig i) (a : ℤ) (g : GE D) :
    Matrix (Fin D.R.r) (Fin D.R.r) (FractionRing (D.ntw.O0 i)) :=
  algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) ((eps D i g ^ a : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) •
    (Vmat D i s g⁻¹).transpose

def Tloc (s : D.ntw.Sig i) (w : PlE D.host) : DecAt D w →* GL (Fin D.R.r) (D.ntw.O0 i) :=
  (Trep D i s).comp (DecAt D w).subtype

def latticeFiniteCocycles (s : D.ntw.Sig i) (w : PlE D.host) (hw : w ∈ PlL D i) :
    Submodule (D.ntw.O0 i) (DecAt D w → Fin D.R.r → D.ntw.O0 i) where
  carrier := {z | (fun g j => (D.ntwbr i w hw).toLL (z ((D.ntwbr i w hw).e.symm g) j)) ∈
    Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((D.loc (D.ntw.l i)).PD (D.ntwbr i w hw).Kw) ((D.ntwbr i w hw).rep (Tloc D i s w))}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
    exact Submodule.zero_mem _
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Pi.add_apply, map_add] at ha hb ⊢
    exact Submodule.add_mem _ ha hb
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, map_mul] at ha ⊢
    exact Submodule.smul_mem _ ((D.ntwbr i w hw).toLL c) ha

def latticeFiniteCohomology (s : D.ntw.Sig i) (w : PlE D.host) (hw : w ∈ PlL D i) :
    Submodule (D.ntw.O0 i) (H1 (matRepOn (D.ntw.O0 i) (Tloc D i s w))) :=
  ((latticeFiniteCocycles D i s w hw).comap (Z1 (matRepOn (D.ntw.O0 i) (Tloc D i s w))).subtype).map
    (Submodule.mkQ _)

def toOk (k : ℕ) : D.ntw.O0 i →+* D.ntw.Ok i k :=
  (algebraMap (D.ntw.O i) (D.ntw.Ok i k)).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))

def toKk (k : ℕ) : FractionRing (D.ntw.O i) →+* FractionRing (D.ntw.Ok i k) :=
  IsFractionRing.map (A := D.ntw.O i) (B := D.ntw.Ok i k) (K := FractionRing (D.ntw.O i))
    (L := FractionRing (D.ntw.Ok i k)) (D.ntw.Ok_inj i k)

def Drep (s : D.ntw.Sig i) (k : ℕ) (ψ : GE D →* (D.ntw.Ok i k)ˣ) :
    Representation (D.ntw.Ok i k) (GE D) (DivMod (D.ntw.Ok i k) D.R.r) :=
  divRep (D.ntw.Ok i k) D.R.r (twistGL (Formalism.MainNotions.N.mapRep (toOk D i k) (Trep D i s)) ψ⁻¹)

def bkLoc (s : D.ntw.Sig i) (k : ℕ) (ψ : GE D →* (D.ntw.Ok i k)ˣ) (w : PlE D.host)
    (hw : w ∈ PlL D i) :
    Submodule (D.ntw.Ok i k) (H1 ((Drep D i s k ψ).comp (DecAt D w).subtype)) :=
  Submodule.span (D.ntw.Ok i k)
    {x | ∃ z ∈ latticeFiniteCocycles D i s w hw, ∃ a : KmodO (D.ntw.Ok i k),
      ∃ c : Z1 ((Drep D i s k ψ).comp (DecAt D w).subtype),
        (∀ g j, (show Fin D.R.r → KmodO (D.ntw.Ok i k) from c.1 g) j = toOk D i k (z g j) • a) ∧
          Submodule.Quotient.mk c = x}

open Classical in

def selS (s : D.ntw.Sig i) (Q : Finset (PlE D.host)) (k : ℕ) (ψ : GE D →* (D.ntw.Ok i k)ˣ) :
    EReal :=
  len_vp (D.ntw.Ok i k) (D.ntw.l i)
    (Formalism.GaloisCohomology.selLen (Drep D i s k ψ) D.nd.plOm (D.ntw.l i) (Sset D i ∪ ↑Q)
      (fun w => if hw : w ∈ PlL D i then bkLoc D i s k ψ w hw else ⊤))

def evTh (Q : Finset (PlE D.host)) (lam : D.ntw.abelian₂ i) (k : ℕ)
    (φ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) : FractionRing (D.ntw.Ok i k) :=
  ∑ x : D.ntw.RCG i Q,
    algebraMap (D.ntw.Ok i k) (FractionRing (D.ntw.Ok i k)) ((φ x : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) *
      toKk D i k (D.ntw.th i Q lam x)

def c0 (lam : D.ntw.abelian₂ i) : EReal :=
  val_vp (D.ntw.O i) (D.ntw.l i) (∑ x : D.ntw.RCG i ∅, D.ntw.th i ∅ lam x)

def eq_factor {K : Type} [Field K] (q : ℕ) (s : ℤ) (Y : K) : K :=
  (1 - Y * (q : K) ^ (-s)) * (1 - Y⁻¹ * (q : K) ^ (-s)) + ((q : K) - 1) * (q : K) ^ (-(2 * s))

def AdmQ (Q : Finset (PlE D.host)) : Prop :=
  (∀ P ∈ Q, IsSplitPl D.host P ∧ P ∉ D.ntw.S0 i) ∧
    ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q

def UnramifiedOutsideLS : Prop := ∀ (s : D.ntw.Sig i) (v : PlE D.host), v ∉ PlL D i → v ∉ Sset D i →
  ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, Trep D i s σ = 1

def ConjugateDualTwist : Prop := ∀ s : D.ntw.Sig i, ∃ P : GL (Fin D.R.r) (FractionRing (D.ntw.O0 i)),
  ∀ g g' : GE D, (∀ x, g' x = D.ntw.cc (g (D.ntw.cc.symm x))) →
    Vmat D i s g' * (P : Matrix _ _ _) = (P : Matrix _ _ _) * VdualMat D i s (1 - (D.R.t : ℤ)) g

def ResidualAbsIrreducibleAlt : Prop := ∀ s : D.ntw.Sig i,
  Formalism.MainNotions.N.IsIrrSub (Formalism.MainNotions.N.mapRep
    ((algebraMap (IsLocalRing.ResidueField (D.ntw.O0 i))
      (AlgebraicClosure (IsLocalRing.ResidueField (D.ntw.O0 i)))).comp
        (IsLocalRing.residue (D.ntw.O0 i))) (Trep D i s)) ⊤

def NoInvariantsAtFinitePlaces : Prop := ∀ (s : D.ntw.Sig i) (v : PlE D.host) (x : Fin D.R.r → FractionRing (D.ntw.O0 i)),
  ((∀ g ∈ DecAt D v, (Vmat D i s g).mulVec x = x) → x = 0) ∧
  ((∀ g ∈ DecAt D v, (VdualMat D i s 1 g).mulVec x = x) → x = 0)

def DeRhamJumpsOutsideInterval : Prop := ∀ (s : D.ntw.Sig i) (w : PlE D.host) (hw : w ∈ PlL D i),
  (D.ntwbr i w hw).IsdRW (D.loc (D.ntw.l i)) (Tloc D i s w) ∧
  ∀ (τ : ↥(D.ntwbr i w hw).Kw.1 →ₐ[ℚ_[D.ntw.l i]] ↥(D.ntwbr i w hw).LL.1) (a : ℤ),
    (D.ntwbr i w hw).IsJumpW (D.loc (D.ntw.l i)) (Tloc D i s w) τ a → a < -1 ∨ (D.R.t : ℤ) < a

def CrystallineAboveResidueChar : Prop := ∀ (s : D.ntw.Sig i) (w : PlE D.host) (hw : w ∈ PlL D i),
  ((∀ k, D.ntw.l i ≠ D.host.g k) → (D.ntwbr i w hw).IsCrysW (D.loc (D.ntw.l i)) (Tloc D i s w)) ∧
  (D.ntwbr i w hw).IsPotCrysW (D.loc (D.ntw.l i)) (Tloc D i s w)

def WildInertiaTrivialAwayFromL : Prop := ∀ (s : D.ntw.Sig i) (k : Fin 2) (v : PlE D.host),
  v ∈ placesOver D.host.E (D.host.g k) → v ∉ PlL D i →
  ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
    (∀ σ ∈ wildSet D.host.E A, D.ntw.rhoS i s σ = 1 ∧ chiS D i s σ = 1) ∧
    ∀ γ : GE D, TameGenAt A γ →
      ¬ ((((D.ntw.rhoS i s γ : GL (Fin D.R.r) (D.ntw.O0 i)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)).map
            (IsLocalRing.residue (D.ntw.O0 i))).charpoly.IsRoot
        (IsLocalRing.residue (D.ntw.O0 i) ((chiS D i s γ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)))

def InertiaTrivialOverDeltaPrime : Prop := ∀ (s : D.ntw.Sig i), ∀ v ∈ D.ntw.pD i,
  ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A,
    D.ntw.rhoS i s σ = 1

def CountT : Prop := ∀ s : D.ntw.Sig i,
  Cardinal.sum (fun w : PlL D i => Module.rank (D.ntw.O0 i) (latticeFiniteCohomology D i s w.1 w.2)) =
    ((D.R.f * D.R.r : ℕ) : Cardinal)

def ThmBK : Prop := ∀ (w : PlE D.host) (hw : w ∈ PlL D i),
  Formalism.MainNotions.LocalSituation.bkAll ((D.loc (D.ntw.l i)).PD (D.ntwbr i w hw).Kw)

def JInvariantIntegrality (N₀ : ℕ) : Prop := ∀ Q : Finset (PlE D.host), AdmQ D i Q →
  ∀ (lam : D.ntw.abelian₂ i) (x : D.ntw.RCG i Q), ∃ y : D.ntw.O i,
    ((D.ntw.l i : ℕ) : FractionRing (D.ntw.O i)) ^ N₀ * D.ntw.th i Q lam x =
      algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) y

open Classical in

def CM2 : Prop := ∀ lam : D.ntw.abelian₂ i, ∃ s : ℤ, D.ntw.s2 i lam = 2 * s ∧
  ∀ Q : Finset (PlE D.host), AdmQ D i Q → ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' →
  ∀ (k : ℕ) (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ)
    (ψ' : D.ntw.RCG i ((Q.erase P).erase P') →* (D.ntw.Ok i k)ˣ),
    ψ.comp (D.ntw.art i Q) = ψ'.comp (D.ntw.art i ((Q.erase P).erase P')) →
  ∀ σ : GE D, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
    evTh D i Q lam k ψ =
      eq_factor (Ideal.absNorm P.asIdeal) s
        (algebraMap (D.ntw.Ok i k) (FractionRing (D.ntw.Ok i k))
          (algebraMap (D.ntw.O i) (D.ntw.Ok i k) (D.ntw.Xv i lam P) *
            ((ψ (D.ntw.art i Q σ) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))) *
      evTh D i ((Q.erase P).erase P') lam k ψ'

def IsDel (Q₁ : Finset (PlE D.host)) (M : ℕ)
    (del : GE D →* Multiplicative (↥Q₁ → ZMod (D.ntw.l i ^ M))) : Prop :=
  IsOpen (del.ker : Set (GE D)) ∧ AntiHom D.ntw.cc del ∧
  (∀ v ∈ PlL D i, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
    ∀ σ ∈ Dec (F := D.host.E) A, del σ = 1) ∧
  ∀ (P : ↥Q₁) (v : PlE D.host) (A : ValuationSubring D.nd.Om), IsPlaceOver A v →
    ((v = P.1 ∨ IsConjPl D.host P.1 v) → ∀ a : ZMod (D.ntw.l i ^ M),
      ∃ σ ∈ Ine (F := D.host.E) A, Multiplicative.toAdd (del σ) P = a) ∧
    (¬ (v = P.1 ∨ IsConjPl D.host P.1 v) →
      ∀ σ ∈ Ine (F := D.host.E) A, Multiplicative.toAdd (del σ) P = 0)

def atSide {k : ℕ} (b : Bool) (ψ : GE D →* (D.ntw.Ok i k)ˣ) : GE D →* (D.ntw.Ok i k)ˣ :=
  if b then ψ else ψ⁻¹

def Shape (Q : Finset (PlE D.host)) (k : ℕ) (ζ : (D.ntw.Ok i k)ˣ)
    (ψ : GE D →* (D.ntw.Ok i k)ˣ) : Prop :=
  (∀ g, ψ g ∈ Subgroup.zpowers ζ) ∧ AntiHom D.ntw.cc ψ ∧ RamExactly ψ (↑Q : Set (PlE D.host)) ∧
  (∀ v ∈ Q, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ wildSet D.host.E A, ψ σ = 1) ∧
  ∀ v ∈ PlL D i, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
    ∀ σ ∈ Dec (F := D.host.E) A, ψ σ = 1

def PartA (ε' : ℝ) (Q : Finset (PlE D.host)) (k : ℕ) (ψ : GE D →* (D.ntw.Ok i k)ˣ) : Prop :=
  ∃ ε : D.ntw.Sig i → ℝ, (∀ s, 0 ≤ ε s) ∧ ∑ s, ε s ≤ ε' ∧
    ∀ s, selS D i s Q k (atSide D i (D.ntw.side i s) ψ) ≤
      (((if D.ntw.l i = 2 then 1 else 0) + ε s : ℝ) : EReal)

def PartC (N₀ : ℕ) (ε' : ℝ) (Q : Finset (PlE D.host)) (k : ℕ) (ψ : GE D →* (D.ntw.Ok i k)ˣ) :
    Prop :=
  ∀ lam : D.ntw.abelian₂ i, ∃ φ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ,
    φ.comp (D.ntw.art i Q) = atSide D i (D.ntw.sideL i lam) ψ ∧
    ((-(N₀ : ℝ) : ℝ) : EReal) ≤ val_vp (D.ntw.Ok i k) (D.ntw.l i) (evTh D i Q lam k φ) ∧
    val_vp (D.ntw.Ok i k) (D.ntw.l i) (evTh D i Q lam k φ) ≤ c0 D i lam + (ε' : EReal)

def PartD (ε' : ℝ) (Q : Finset (PlE D.host)) (k : ℕ) (ψ : GE D →* (D.ntw.Ok i k)ˣ) : Prop :=
  ∀ γ : PlE D.host → GE D, (∀ P ∈ Q, TameGenAt (D.nd.plOm.1 P) (γ P)) →
    ((D.R.t : ℝ) : EReal) * ∑ P ∈ Q, val_vp (D.ntw.Ok i k) (D.ntw.l i)
      (algebraMap (D.ntw.Ok i k) (FractionRing (D.ntw.Ok i k))
        (((ψ (γ P) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) - 1)) ≤ (ε' : EReal)

def ThmACD (N₀ : ℕ) : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ∀ B : Finset (PlE D.host),
  ∃ (Q Q₁ : Finset (PlE D.host)) (M k : ℕ)
    (del : GE D →* Multiplicative (↥Q₁ → ZMod (D.ntw.l i ^ M)))
    (ψ₀ : (D.ntw.Ok i k)ˣ → (Multiplicative (↥Q₁ → ZMod (D.ntw.l i ^ M)) →* (D.ntw.Ok i k)ˣ)),
    (∀ P, P ∈ Q ↔ P ∈ Q₁ ∨ ∃ P₁ ∈ Q₁, IsConjPl D.host P₁ P) ∧
    (∀ P ∈ Q₁, ∀ P' ∈ Q₁, ¬ IsConjPl D.host P P') ∧
    (∀ P ∈ Q, IsSplitPl D.host P ∧ (Ideal.absNorm P.asIdeal).Prime ∧ P ∉ D.ntw.S0 i ∧ P ∉ B) ∧
    1 ≤ M ∧ IsDel D i Q₁ M del ∧
    ∀ ζ : (D.ntw.Ok i k)ˣ, IsPrimitiveRoot ζ (D.ntw.l i ^ k) →
      (∀ a : ℤ, IsPrimitiveRoot (ζ ^ a) (D.ntw.l i ^ k) →
        (ψ₀ (ζ ^ a)).comp del = ((ψ₀ ζ).comp del) ^ a) ∧
      Shape D i Q k ζ ((ψ₀ ζ).comp del) ∧
      PartA D i ε' Q k ((ψ₀ ζ).comp del) ∧
      PartC D i N₀ ε' Q k ((ψ₀ ζ).comp del) ∧
      PartD D i ε' Q k ((ψ₀ ζ).comp del)

def InputsT : Prop :=
  UnramifiedOutsideLS D i ∧ ConjugateDualTwist D i ∧ ResidualAbsIrreducibleAlt D i ∧ NoInvariantsAtFinitePlaces D i ∧ DeRhamJumpsOutsideInterval D i ∧ WildInertiaTrivialAwayFromL D i ∧ CountT D i

end HidaSetting

def SelmerBoundFromLocalInputs (D : D7) : Prop :=
  ∀ (N₀ : ℕ) (i : D.ntw.Tw), D.ntw.NonzeroIndexPlace i →
    InputsT D i → ThmBK D i → TLoc → TGlob → PoitouTate → JInvariantIntegrality D i N₀ → CM2 D i →
    ThmACD D i N₀

def SelmerBoundWithInertiaCondition (D : D7) : Prop :=
  ∀ (N₀ : ℕ) (i : D.ntw.Tw), D.ntw.NonzeroIndexPlace i →
    InputsT D i → InertiaTrivialOverDeltaPrime D i → ThmBK D i → TLoc → TGlob → PoitouTate → JInvariantIntegrality D i N₀ → CM2 D i →
    ThmACD D i N₀

theorem SelmerBoundFromLocalInputs.full {D : D7} (h : SelmerBoundFromLocalInputs D) : SelmerBoundWithInertiaCondition D :=
  fun N₀ i hi hT _ => h N₀ i hi hT

end GlobalTheory.IndefiniteRowSideFullHecke.LengthValuationTwists

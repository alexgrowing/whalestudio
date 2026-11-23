import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial MeasureTheory
open GlobalTheory.CuspRep UpperTheory.V.Sd CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Af.Nf

def nsl (k : ℕ) (f : ℍ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) (z : ℍ) : ℂ :=
  ((|x.det| ^ ((k : ℝ) / 2) : ℝ) : ℂ) * ((x 1 0 : ℂ) * z + x 1 1) ^ (-(k : ℤ)) *
    f (ofComplex (((SignType.sign x.det : ℝ) : ℂ) * (((x 0 0 : ℂ) * z + x 0 1) / ((x 1 0 : ℂ) * z + x 1 1))))

def arch (k : ℕ) (f : ℍ → ℂ) (x : Fin 2 → Fin 2 → ℝ) : ℂ := nsl k f (Matrix.of x) UpperHalfPlane.I

def eps : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, 1]

def ev : TR.Rinf ℚ →+* ℝ := Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) Rat.infinitePlace

def upR : GL (Fin 2) ℝ →* GA ℚ 2 := (TR.infGL ℚ 2).comp (Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)))

def toR : GL (Fin 2) ℚ →* GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.map (Rat.castHom ℝ)

def toF : GL (Fin 2) ℚ →* GL (Fin 2) (Af ℚ) := Matrix.GeneralLinearGroup.map (algebraMap ℚ (Af ℚ))

theorem upR_ev (h : GL (Fin 2) (TR.Rinf ℚ)) : upR (Matrix.GeneralLinearGroup.map ev h) = TR.infGL ℚ 2 h := by
  refine congrArg (TR.infGL ℚ 2) (Units.ext (Matrix.ext fun i j => funext fun v => ?_))
  rw [Subsingleton.elim v Rat.infinitePlace]
  rfl

theorem upR_comm (h : GL (Fin 2) ℝ) (u : GL (Fin 2) (Af ℚ)) : upR h * finGL ℚ 2 u = finGL ℚ 2 u * upR h := TR.infGL_comm _ _

theorem ratGL_eq (γ : GL (Fin 2) ℚ) : ratGL ℚ 2 γ = upR (toR γ) * finGL ℚ 2 (toF γ) := by
  rw [← TR.infGL_mul_finGL (ratGL ℚ 2 γ)]
  congr 1
  refine congrArg (TR.infGL ℚ 2) (Units.ext (Matrix.ext fun i j => ?_))
  exact DFunLike.congr_fun (Subsingleton.elim ((TR.pInf ℚ).comp (algebraMap ℚ (Ad ℚ)))
    ((algebraMap ℝ (TR.Rinf ℚ)).comp (Rat.castHom ℝ))) (γ i j)

def K1G (M : ℕ) : Subgroup (GL (Fin 2) (Af ℚ)) :=
  ((mirab _).comap (Matrix.GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat ℚ))})))).map
    (Matrix.GeneralLinearGroup.map (Ohat ℚ).subtype)

def lev (M : ℕ) (w : Pl ℚ) : ℕ := ordI w (Ideal.span {(M : 𝓞 ℚ)})

def IsZU (u : (Af ℚ)ˣ) : Prop := (u : Af ℚ) ∈ Ohat ℚ ∧ ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ) ∈ Ohat ℚ

def IsLift (k M : ℕ) (f : ℍ → ℂ) (φ : GA ℚ 2 → ℂ) : Prop :=
  ∀ (γ : GL (Fin 2) ℚ) (h : GL (Fin 2) ℝ), ∀ u ∈ K1G M, φ (ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u)) = nsl k f h UpperHalfPlane.I

structure IsDirOf {M : ℕ} (χ : DirichletCharacter ℂ M) (ω : HChar ℚ) : Prop where
  pos : ∀ t : (TR.Rinf ℚ)ˣ, (∀ v, 0 < t.val v) → ω.1 (TR.infId ℚ t) = 1
  unit : ∀ u, IsZU u → ∀ d : ℤ, (∃ y ∈ Ohat ℚ, (u : Af ℚ) - d = M * y) → ((ω.1 (finId ℚ u) : ℂˣ) : ℂ) * χ (d : ZMod M) = 1

example : IsLift 0 1 1 1 := fun _ _ _ _ => by simp [nsl]

example : IsDirOf (1 : DirichletCharacter ℂ 1) 1 :=
  ⟨fun _ _ => rfl, fun _ _ _ _ => by rw [MulChar.one_apply (isUnit_of_subsingleton _), mul_one]; rfl⟩

def icoef (f : ℍ → ℂ) (𝔪 : Ideal (𝓞 ℚ)) : ℂ := coef f (Ideal.absNorm 𝔪)

def MemK : Prop :=
  ∀ (M : ℕ) (g : GL (Fin 2) (Af ℚ)), g ∈ K1G M ↔ (∀ a b, g a b ∈ Ohat ℚ) ∧ (∀ a b, (g⁻¹ : GL (Fin 2) (Af ℚ)) a b ∈ Ohat ℚ) ∧
    (∃ y ∈ Ohat ℚ, g 1 0 = M * y) ∧ ∃ y ∈ Ohat ℚ, g 1 1 - 1 = M * y

def RatAd : Prop :=
  (∀ y : (Af ℚ)ˣ, ∃ (r : ℚˣ) (u : (Af ℚ)ˣ), 0 < (r : ℚ) ∧ IsZU u ∧ y = Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r * u) ∧
  (∀ M : ℕ, 1 ≤ M → ∀ x ∈ Ohat ℚ, ∃ d : ℤ, ∃ y ∈ Ohat ℚ, x - d = M * y) ∧
  ∀ r : ℚ, algebraMap ℚ (Af ℚ) r ∈ Ohat ℚ → ∃ n : ℤ, r = n

def KOpen : Prop :=
  ∀ M : ℕ, 1 ≤ M → IsOpen (K1G M : Set (GL (Fin 2) (Af ℚ))) ∧ ∀ u, IsZU u → ∀ x ∈ Ohat ℚ, aff u x ∈ K1G M

def KLocal : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∀ w : Pl ℚ, ∀ g ∈ K1 w (lev M w), locGL ℚ 2 w g ∈ K1G M

def Places : Prop :=
  ∀ w : Pl ℚ, (normV w).Prime ∧ w.asIdeal = Ideal.span {((normV w : ℕ) : 𝓞 ℚ)} ∧ Ideal.absNorm w.asIdeal = normV w ∧
    ∀ M : ℕ, 1 ≤ M → ¬ normV w ∣ M → lev M w = 0

def Decomp : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∀ g : GA ℚ 2, ∃ (γ : GL (Fin 2) ℚ) (h : GL (Fin 2) ℝ), ∃ u ∈ K1G M, g = ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u)

def RatK : Prop :=
  ∀ M : ℕ, 1 ≤ M → (∀ γ : GL (Fin 2) ℚ, toF γ ∈ K1G M → ∃ δ : SL(2, ℤ), δ ∈ Gamma1 M ∧
      ((toR γ).val = δ.1.map (Int.cast : ℤ → ℝ) ∨ (toR γ).val = eps * δ.1.map (Int.cast : ℤ → ℝ))) ∧
    ∀ u, IsZU u → ∃ (δ : SL(2, ℤ)) (γ : GL (Fin 2) ℚ), δ ∈ Gamma0 M ∧ γ.val = δ.1.map (Int.cast : ℤ → ℚ) ∧
      (toF γ)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ K1G M ∧ ∃ y ∈ Ohat ℚ, (u : Af ℚ) - (δ 1 1 : ℤ) = M * y

def DirChar : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∀ χ : DirichletCharacter ℂ M, ∃ ω, IsDirOf χ ω

def CharVal : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∀ (χ : DirichletCharacter ℂ M) (ω : HChar ℚ), IsDirOf χ ω → IsOfFinOrder ω ∧
    ∀ w : Pl ℚ, ¬ normV w ∣ M → ((ω.val w : ℂˣ) : ℂ) = χ (normV w : ZMod M)

def NslMul : Prop :=
  ∀ (k : ℕ) (f : ℍ → ℂ),
    (∀ x y : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → 0 < y.det → nsl k (nsl k f x) y = nsl k f (x * y)) ∧
    (∀ x, nsl k f (eps * x) = nsl k f x) ∧
    (∀ (t : ℝ) x, 0 < t → nsl k f (t • x) = nsl k f x) ∧
    (∀ (c : ℂ) x, nsl k (c • f) x = c • nsl k f x)

def NslSl : Prop :=
  ∀ (k : ℕ) (f : ℍ → ℂ),
    (∀ δ : SL(2, ℤ), nsl k f (δ.1.map (Int.cast : ℤ → ℝ)) = f ∣[(k : ℤ)] δ) ∧
    (∀ x : GL (Fin 2) ℝ, 0 < x.val.det → nsl k f x = (((x.val.det ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ)) • f ∣[(k : ℤ)] x) ∧
    (MDiff f → ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → MDiff (nsl k f x))

def NslInv : Prop :=
  ∀ (k M : ℕ) (f : ℍ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 →
    ((∀ δ : SL(2, ℤ), δ ∈ Gamma1 M → f ∣[(k : ℤ)] δ = f) → ∀ δ : SL(2, ℤ), δ ∈ Gamma1 M →
      nsl k f (δ.1.map (Int.cast : ℤ → ℝ) * x) = nsl k f x) ∧
    ∀ χ : DirichletCharacter ℂ M, HasChar k χ f → ∀ δ : SL(2, ℤ), δ ∈ Gamma0 M →
      nsl k f (δ.1.map (Int.cast : ℤ → ℝ) * x) = χ ((δ 1 1 : ℤ) : ZMod M) • nsl k f x

def ArchSm : Prop :=
  ∀ (k : ℕ) (f : ℍ → ℂ), MDiff f → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (arch k f) {x | (Matrix.of x).det ≠ 0}

def ArchDer : Prop :=
  ∀ (k : ℕ) (f : ℍ → ℂ), MDiff f → ∀ D : Fin 2 → Fin 2 → ℂ,
    (∀ i j, D i j = fderiv ℝ (arch k f) (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single i j 1))) →
    D 0 1 - D 1 0 = Complex.I * k * f UpperHalfPlane.I ∧ D 0 0 - D 1 1 = Complex.I * (D 0 1 + D 1 0)

def ArchBd : Prop :=
  ∀ (k M : ℕ), 1 ≤ M → ∀ f : CuspForm (Gamma1 M) (k : ℤ), ∃ C : ℝ, ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 →
    ‖nsl k f x UpperHalfPlane.I‖ ≤ C

def ClassCT : Prop :=
  ∀ (k M : ℕ), 1 ≤ M → ∀ (f : CuspForm (Gamma1 M) (k : ℤ)) (γ : GL (Fin 2) ℚ) (z : ℍ), ∃ N : ℕ, 0 < N ∧
    Function.Periodic (fun t : ℝ => nsl k f (toR γ) (t +ᵥ z)) N ∧ ∫ t in (0 : ℝ)..N, nsl k f (toR γ) (t +ᵥ z) = 0

def LiftEx : Prop :=
  ∀ (k M : ℕ), 1 ≤ M → ∀ f : ℍ → ℂ, (∀ δ : SL(2, ℤ), δ ∈ Gamma1 M → f ∣[(k : ℤ)] δ = f) → ∃ φ, IsLift k M f φ

def LiftSm : Prop :=
  ∀ (k M : ℕ), 1 ≤ M → ∀ (f : ℍ → ℂ) (φ : GA ℚ 2 → ℂ), IsLift k M f φ →
    (∀ γ g, φ (ratGL ℚ 2 γ * g) = φ g) ∧ (∀ u ∈ K1G M, ∀ g, φ (g * finGL ℚ 2 u) = φ g) ∧ (MDiff f → φ ∈ TR.Sm ℚ 2)

def LiftLie : Prop :=
  ∀ (k M : ℕ), 1 ≤ M → ∀ (f : ℍ → ℂ), MDiff f → ∀ φ : TR.Sm ℚ 2, IsLift k M f φ.1 → ∀ v,
    TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k) • φ ∧
    TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ)

def LiftCent : Prop :=
  ∀ (k M : ℕ), 1 ≤ M → ∀ (χ : DirichletCharacter ℂ M) (ω : HChar ℚ), IsDirOf χ ω → ∀ f : ℍ → ℂ, HasChar k χ f →
    ∀ φ : GA ℚ 2 → ℂ, IsLift k M f φ → ∀ (z : Ideles ℚ) (g : GA ℚ 2),
      φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ g

def LiftK : Prop :=
  ∀ (k M : ℕ), 1 ≤ M → ∀ (f : ℍ → ℂ) (φ : TR.Sm ℚ 2), IsLift k M f φ.1 →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun r => TR.cptRep ℚ 2 r φ))

def LiftCT : Prop :=
  ∀ (k M : ℕ), 1 ≤ M → ∀ (f : CuspForm (Gamma1 M) (k : ℤ)) (φ : GA ℚ 2 → ℂ), IsLift k M f φ → ∀ g, ∃ N : ℕ, 0 < N ∧
    Function.Periodic (fun t : ℝ => φ (upR (aff 1 t) * g)) N ∧ ∫ t in (0 : ℝ)..N, φ (upR (aff 1 t) * g) = 0

def AvgZero : Prop :=
  ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain Γ 𝓕 μ → ∀ ψ : G → ℂ, Continuous ψ → (∀ γ ∈ Γ, ∀ x, ψ (γ + x) = ψ x) →
    ∀ e : ℝ → G, Continuous e → ∀ N : ℝ, 0 < N → (∀ x, ∫ t in (0 : ℝ)..N, ψ (e t + x) = 0) → ∫ x in 𝓕, ψ x ∂μ = 0

def SmCont : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : TR.Sm F a), IsOpen {k | TR.finRep F a k φ = φ} → Continuous φ.1

def AutPer : Prop :=
  ∀ φ : TR.Sm ℚ 2, (∀ γ g, φ.1 (ratGL ℚ 2 γ * g) = φ.1 g) → IsOpen {k | TR.finRep ℚ 2 k φ = φ} → ∀ g, ∃ N : ℕ, 0 < N ∧
    ∀ x : BlockIx 2 1 → Ad ℚ, φ.1 (upR (aff 1 (N : ℝ)) * (unip x * g)) = φ.1 (unip x * g)

def CuspCrit : Prop :=
  ∀ φ : TR.Sm ℚ 2, (∀ γ g, φ.1 (ratGL ℚ 2 γ * g) = φ.1 g) → IsOpen {k | TR.finRep ℚ 2 k φ = φ} →
    (∀ g, ∃ N : ℕ, 0 < N ∧ Function.Periodic (fun t : ℝ => φ.1 (upR (aff 1 t) * g)) N ∧
      ∫ t in (0 : ℝ)..N, φ.1 (upR (aff 1 t) * g) = 0) → IsCuspidal φ.1

def CoefAt : Prop :=
  ∀ (a : ℕ → ℂ) (q : ℚ), 0 < q → ∀ u, IsZU u →
    coefAt (fun 𝔪 => a (Ideal.absNorm 𝔪)) (algebraMap ℚ (Af ℚ) q * (u : Af ℚ)) = if q.den = 1 then a q.num.toNat else 0

def AbsF : Prop :=
  ∀ r : ℚˣ, 0 < (r : ℚ) → ∀ u, IsZU u → absF (Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r * u) = (((r : ℚ) : ℝ))⁻¹

def LiftExp : Prop :=
  ∀ (k M : ℕ), 1 ≤ M → ∀ (f : CuspForm (Gamma1 M) (k : ℤ)) (φ : GA ℚ 2 → ℂ), IsLift k M f φ → HasExp φ k 0 (icoef f)

def HkCoef : Prop :=
  ∀ (k : ℕ) (f : Newform k) (ω : HChar ℚ) (w : Pl ℚ), ¬ normV w ∣ f.M → ((ω.val w : ℂˣ) : ℂ) = f.χ (normV w : ZMod f.M) →
    ∀ 𝔪, 𝔪 ≠ ⊥ → hkCoef k (lev f.M) ω w (icoef f.f) 𝔪 = f.a (normV w) * icoef f.f 𝔪

def LiftHol : Prop :=
  ∀ (k M : ℕ), 1 ≤ M → ∀ (χ : DirichletCharacter ℂ M) (ω : HChar ℚ), IsDirOf χ ω → ∀ f : CuspForm (Gamma1 M) (k : ℤ), HasChar k χ f →
    ∃ φ : TR.Sm ℚ 2, IsLift k M f φ.1 ∧ IsHol k (lev M) ω φ ∧ TR.IsCuspForm φ

def ZFin : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (ω : HChar F), IsOfFinOrder ω → ∀ φ : TR.Sm F 2,
    (∀ (z : Ideles F) (g : GA F 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) →
    (∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k) • φ) →
    (∀ v, TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ)) →
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F 2) => z φ) '' TR.Zalg F 2))

def Split : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : TR.Sm F a), φ ≠ 0 → φ ∈ ⨆ π : TR.CuspSub F a, π.V →
    ∃ (π : TR.CuspSub F a) (ψ : π.V) (W : Submodule ℂ (TR.Sm F a)), ψ ≠ 0 ∧ TR.IsStable W ∧ Disjoint π.V W ∧ φ - ψ ∈ W

def SatComp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (φ : TR.Sm F 2) (π : TR.CuspSub F 2) (ψ : π.V) (W : Submodule ℂ (TR.Sm F 2)),
    ψ ≠ 0 → TR.IsStable W → Disjoint π.V W → φ - ψ ∈ W → ∀ (w : Pl F) (B : Multiset ℂˣ),
    GlobalTheory.LFun.IsSatVecGL w (locSm F w) φ B → GlobalTheory.LFun.IsSatVecGL w (π.locRep w) ψ B

def SatOfU : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V) (x : V) (α β : ℂˣ), x ≠ 0 → x ∈ Hi.fixd ρ (K1 w 0) →
    Uop w ρ 0 x = ((((normV w : ℝ) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * ((α : ℂ) + β)) • x →
    ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) x = ((α * β : ℂˣ) : ℂ) • x →
    GlobalTheory.LFun.IsSatVecGL w ρ x {α, β}

def SatHol : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) (φ : TR.Sm F 2), IsHol k c ω φ → φ ≠ 0 →
    ∀ (w : Pl F) (lam : ℂ), c w = 0 → hk k w 0 φ = lam • φ → ∃ α β : ℂˣ, GlobalTheory.LFun.IsSatVecGL w (locSm F w) φ {α, β} ∧
      (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) = lam ∧ α * β = ω.val w

def SatOfVec : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a) (w : Pl F) (ψ : π.V) (B : Multiset ℂˣ),
    GlobalTheory.LFun.IsSatVecGL w (π.locRep w) ψ B → π.HasSat w B

def AbsExpo : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (s : ℝ) (v : InfinitePlace F), TR.expo (GlobalTheory.HeckeGal.Model.absPow F s) v = s

def RepOf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), 1 ≤ k → ∀ (c : Pl F → ℕ) (ω : HChar F), IsOfFinOrder ω →
    ∀ φ : TR.Sm F 2, IsHol k c ω φ → φ ≠ 0 → TR.IsCuspForm φ → ∀ j : ℤ, ∃ π : TR.CuspSub F 2,
      (∀ v, π.HasInfChar v {1 / 2 + (j : ℂ), 3 / 2 - (k : ℂ) + (j : ℂ)}) ∧
      ∀ (w : Pl F) (lam : ℂ), c w = 0 → hk k w 0 φ = lam • φ → ∃ B, π.HasSat w B ∧
        ((algSat 2 (normV w) B).map fun b => X - C ((normV w : ℂ) ^ j * b)).prod =
          X ^ 2 - C lam * X + C ((ω.val w : ℂˣ) * (normV w : ℂ) ^ (k - 1))

end UpperTheory.V.Af.Nf

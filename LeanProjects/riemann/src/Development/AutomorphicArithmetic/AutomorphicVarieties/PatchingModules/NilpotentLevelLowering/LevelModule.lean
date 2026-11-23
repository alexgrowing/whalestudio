import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MSplitDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Pa.Lev

abbrev PU (R : Type) [CommRing R] (q n : ℕ) : Type := MvPolynomial (Fin q × Fin n) R

abbrev PUY (R : Type) [CommRing R] (q n : ℕ) : Type := MvPolynomial ((Fin q × Fin n) ⊕ (Fin q × Fin n)) R

abbrev uV (R : Type) [CommRing R] {q n : ℕ} (j : Fin q) (i : Fin n) : PUY R q n := MvPolynomial.X (.inl (j, i))

abbrev yV (R : Type) [CommRing R] {q n : ℕ} (j : Fin q) (i : Fin n) : PUY R q n := MvPolynomial.X (.inr (j, i))

abbrev Del (l : ℕ) {q : ℕ} (n : ℕ) (a : Fin q → ℕ) : Type := ∀ p : Fin q × Fin n, Multiplicative (ZMod (l ^ a p.1))

def TwoMaps {R B M V : Type} [CommRing R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] {q n : ℕ}
    (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (f : PU R q n) : Prop :=
  ∃ (φ : MSplitAlg P n ⊗[B] M →+ V) (ψ : V →+ MSplitAlg P n ⊗[B] M),
    (∀ (t : PU R q n) z, φ (Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β t) • z) = act t (φ z)) ∧
    (∀ (t : PU R q n) v, ψ (act t v) = Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β t) • ψ v) ∧
    (∀ v, φ (ψ v) = act f v) ∧ ∀ z, ψ (φ z) = Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β f) • z

section Op

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  {r : Resid G0.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} {J : Ideal B} {D : ℕ}
  (b : TWBase u J Empty D) {G : Glob l L} (h : G.Hom G0) {q : ℕ}

structure OpMod (q N : ℕ) : Type 1 where
  rN : Resid G.frame O n
  compat : Glob.Compat h rN r
  R : Type
  [ring : CommRing R]
  [alg : Algebra O R]
  [co : IsCO O R]
  p : Pair rN R
  [algL : Algebra (abelian₂ O Empty D) R]
  [towO : IsScalarTower O (abelian₂ O Empty D) R]
  segmentWeightExponent : ∀ k, algebraMap (abelian₂ O Empty D) R (MvPowerSeries.X (.inr k)) =
    algebraMap O R (b.wt.c k) * (p.ψ (b.wt.v k) (b.wt.i k) (b.wt.γ k) : R) - 1
  β : R →ₐ[O] B
  β_pair : p.Maps β.toRingHom (u.D.comap h.p₀) u.ψ
  M1 : Type
  [add1 : AddCommGroup M1]
  [mod1 : Module R M1]
  [levelModuleAlt : Module (abelian₂ O Empty D) M1]
  [tow1 : IsScalarTower (abelian₂ O Empty D) R M1]
  fin1 : Module.Finite (abelian₂ O Empty D) M1
  Mw : Type
  [addw : AddCommGroup Mw]
  [modw : Module R Mw]
  act1 : PUY R q n →ₐ[R] Module.End R M1
  actw : PU R q n →ₐ[R] Module.End R Mw
  a : Fin q → ℕ
  le_a : ∀ j, N ≤ a j
  ρ : Representation (abelian₂ O Empty D) (Del l n a) M1
  ρ_gen : ∀ j i m, ρ (Pi.mulSingle (j, i) (Multiplicative.ofAdd 1)) m = act1 (1 + yV R j i) m
  proj : Module.Projective (MonoidAlgebra (abelian₂ O Empty D) (Del l n a)) ρ.asModule
  tr : M1 →ₗ[R] Mw
  tr_surj : Function.Surjective tr
  tr_ker : LinearMap.ker tr = ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2))
  tr_u : ∀ j i m, tr (act1 (uV R j i) m) = actw (MvPolynomial.X (j, i)) (tr m)

attribute [instance] OpMod.ring OpMod.alg OpMod.co OpMod.algL OpMod.towO OpMod.add1 OpMod.mod1 OpMod.levelModuleAlt OpMod.tow1
  OpMod.addw OpMod.modw

variable {b h} {N : ℕ} (A : OpMod b h q N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (ex : ℕ)

structure OpRel : Prop where
  two : TwoMaps (M := b.M) A.β.toRingHom (fun j => u.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1)) A.actw
    (fEl Nq fun j i => MvPolynomial.X (j, i))
  rel1 : ∀ j (g : G.G₀), A.act1 ((fEl Nq (uV A.R) * (A.p.D.map (MvPolynomial.C : A.R →+* PUY A.R q n)).tr
    (MonoidAlgebra.single g 1 * q1El (ph j) (uV A.R j))) ^ ex) = 0
  rel2 : ∀ j i (g : G.G₀), A.act1 ((fEl Nq (uV A.R) * (A.p.D.map (MvPolynomial.C : A.R →+* PUY A.R q n)).tr
    (MonoidAlgebra.single g 1 * q2El (ph j) (ta j) (uV A.R j) i (yV A.R j i))) ^ ex) = 0

end Op

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

def IsTheta (ρ : Representation A (GL (Fin n) k) M) (C : Subgroup 𝓀[k]ˣ)
    (θ : (Fin n → kˣ) →* (Module.End A (fixd ρ (iwC k n C)))ˣ) : Prop :=
  ∀ t, Dom t → (θ t : Module.End A (fixd ρ (iwC k n C))) = hk ρ (iwC k n C) (diagT k (Fin n) t)

variable (k) in

def IsGenMod (C : Subgroup 𝓀[k]ˣ) (δ : kˣ) : Prop :=
  ∃ d : 𝒪[k]ˣ, Units.map (algebraMap 𝒪[k] k).toMonoidHom d = δ ∧
    Subgroup.zpowers (Units.map (residue 𝒪[k]).toMonoidHom d) ⊔ C = ⊤

def LocRel (l : ℕ) (x δ : kˣ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (P T : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ C : Subgroup 𝓀[k]ˣ, ellC l _ ≤ C → ∀ θ, IsTheta π C θ → ∀ χ : (Fin n → kˣ) →* ℂˣ,
    (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ (fixd π (iwC k n C))) (χ t : ℂ)) ≠ ⊥ →
    ∀ α : Fin n → ℂ, (∀ i, α i = (resCard k : ℂ) ^ (i : ℕ) * χ (Pi.mulSingle i x)) →
    P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i)) ∧
    ((∀ i i', i ≠ i' → α i ≠ α i' ∧ α i ≠ (resCard k : ℂ) * α i') → ∀ i,
      (List.ofFn fun i' => if i' = i then 1 else P - α i' • (1 : Matrix (Fin n) (Fin n) ℂ)).prod *
        (T - (χ (Pi.mulSingle i δ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = 0)

end Loc

section Prod

variable {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

def UC (n : ℕ) (w : Fin q → Plc L) (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ) : Subgroup (GV n w) :=
  Subgroup.pi Set.univ fun j => iwC ((w j).adicCompletion L) n (C j)

def IsThetaQ (ρ : Representation A (GV n w) M) (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ)
    (Θ : ∀ j, (Fin n → ((w j).adicCompletion L)ˣ) →* (Module.End A (fixd ρ (UC n w C)))ˣ) : Prop :=
  (∀ j t, Dom t → ∀ m : fixd ρ (UC n w C), ((Θ j t : Module.End A (fixd ρ (UC n w C))) m : M) =
    dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) (diagT _ (Fin n) t) m) ∧
  ∀ j j' t t', Commute (Θ j t) (Θ j' t')

theorem UIw_eq : UIw n w = UC n w fun _ => ⊤ := rfl

theorem UIw1_eq (l : ℕ) : UIw1 l n w = UC n w fun _ => ellC l _ := rfl

end Prod

end UpperTheory.V.Pa.Lev

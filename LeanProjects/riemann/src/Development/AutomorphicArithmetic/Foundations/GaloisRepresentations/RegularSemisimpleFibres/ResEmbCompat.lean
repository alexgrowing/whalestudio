import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.NumberField
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt

def hcL {F : Type} [Field F] (Y : List (Σ m : ℕ, GL (Fin m) F → ℂ)) : (n : ℕ) → GL (Fin n) F → ℂ :=
  List.rec (motive := fun _ => (n : ℕ) → GL (Fin n) F → ℂ) (fun _ _ => 1)
    (fun p Y ih n => hc p.1 (Y.map Sigma.fst).sum p.2 (ih (Y.map Sigma.fst).sum) n) Y

theorem hcL_nil {F : Type} [Field F] (n : ℕ) : hcL ([] : List (Σ m : ℕ, GL (Fin m) F → ℂ)) n = fun _ => 1 := rfl

theorem hcL_cons {F : Type} [Field F] (p : Σ m : ℕ, GL (Fin m) F → ℂ) (Y : List (Σ m : ℕ, GL (Fin m) F → ℂ)) (n : ℕ) :
    hcL (p :: Y) n = hc p.1 (Y.map Sigma.fst).sum p.2 (hcL Y (Y.map Sigma.fst).sum) n := rfl

def resT {F : Type} [Field F] (a b : ℕ) {n : ℕ} (T : GL (Fin n) F → ℂ) (x : GL (Fin a) F) (y : GL (Fin b) F) : ℂ :=
  ∑ᶠ p : GL (Fin n) F, if InPar a p ∧ tlG a p = x ∧ brG a b p = y then T p else 0

def SuppAny : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ), 0 < n →
    ∀ (π : CuspSub E n) (Y : Pt E Ω n), Lifts (Pt.base Ω π) Y →
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 Y.K)) (h : IsPlaceOver A v)
      (h' : IsPlaceOver A w) (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* v.adicCompletion E), Continuous i →
    (∀ t ∈ Ine (F := E) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Y.K t) →
    ∀ τ τ', π.IsLocComp v τ → Y.π.IsLocComp w τ' → UpperTheory.Zero.LLC.DZ (IrrGL.of τ.ρ τ.smooth τ.irred) →
    ∀ f : ℕ, normV w = g ^ f → (∀ s, HasSupport τ.ρ s → ∀ y ∈ s, y.1 ∣ f) →
      ∃ ξ hξ, ToralOver h h' (IrrGL.of τ.ρ τ.smooth τ.irred) τ' ξ hξ

def UnlinkedBC : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ), 0 < n →
    ∀ (π : CuspSub E n) (Y : Pt E Ω n), Lifts (Pt.base Ω π) Y →
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 Y.K)) (h : IsPlaceOver A v)
      (h' : IsPlaceOver A w) (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* v.adicCompletion E), Continuous i →
    (∀ t ∈ Ine (F := E) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Y.K t) →
    ∀ τ τ', π.IsLocComp v τ → Y.π.IsLocComp w τ' → Mixed (IrrGL.of τ.ρ τ.smooth τ.irred) →
    ∀ ξ hξ, ToralOver h h' (IrrGL.of τ.ρ τ.smooth τ.irred) τ' ξ hξ → GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ξ hξ)

def LiftOk : Prop := ∀ (a : Lbl) (l : ℕ), l.Prime → a.Ok → (a.lift l).Ok ∧ (a.lift l).rk = a.rk

def LiftBlocks : Prop :=
  ∀ (a : Lbl) (l Q : ℕ), l.Prime → a.Ok → (a.lift l).Splits Q → a.Splits Q ∧ (a.lift l).blocks Q = a.blocks Q

def LeRank : Prop :=
  ∀ a b : Lbl, a.Ok → a.Le b → ∃ c : ℕ, 0 < c ∧ b.q = a.q ^ c ∧ ∀ p ∈ b.L, ∃ r ∈ a.L, p.1 * Nat.gcd r.1 c = r.1

def LeTop : Prop :=
  ∀ a b : Lbl, a.Ok → a.Le b → a.Splits b.q → b.Ok ∧ b.rk = a.rk ∧ (∀ p ∈ b.L, p.1 = 1) ∧ b.blocks b.q = a.blocks b.q

def PolTop : Prop :=
  ∀ (b : Lbl) (x : ℂ), 2 ≤ b.q → (∀ p ∈ b.L, p.1 = 1) → x ^ (b.q - 1) = 1 →
    b.blocks b.q = ((b.D ++ b.L).map fun p => (p.1, ((p.2 : ℕ) : ZMod (b.q - 1))) : List _) ∧
    b.pol b.q x = ((b.D ++ b.L).map fun p => (X - C (x ^ p.2)) ^ p.1).prod

def PolBot : Prop :=
  ∀ (q Q : ℕ) (L : List (ℕ × ℕ)) (x : ℂ), 2 ≤ Q → x ^ (Q - 1) = 1 →
    (⟨q, [], L⟩ : Lbl).pol Q x =
      (L.map fun p => ∏ j ∈ Finset.range p.1, (X - C (x ^ (p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1)))))).prod

def MeetsIff : Prop :=
  ∀ (H V W : Type) [Group H] [Finite H] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ H V) (κ : Representation ℂ H W),
    (Meets ρ (fun g => LinearMap.trace ℂ W (κ g)) ↔ ∃ f : V →ₗ[ℂ] W, f ≠ 0 ∧ ∀ g x, f (ρ g x) = κ g (f x)) ∧
    (Meets ρ (fun g => LinearMap.trace ℂ W (κ g)) ↔ ∃ f : W →ₗ[ℂ] V, f ≠ 0 ∧ ∀ g x, f (κ g x) = ρ g (f x))

def FinSec : Prop :=
  ∀ (H U V : Type) [Group H] [Finite H] [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H U) (σ : Representation ℂ H V) (f : U →ₗ[ℂ] V), (∀ g x, f (ρ g x) = σ g (f x)) → Function.Surjective f →
    ∃ s : V →ₗ[ℂ] U, (∀ g x, s (σ g x) = ρ g (s x)) ∧ ∀ x, f (s x) = x

def FrobTwo : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (a b n : ℕ), n = a + b → ∃ c : ℂ, c ≠ 0 ∧
    ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (T : GL (Fin n) F → ℂ), IsCl T →
      ∑ᶠ g, star (hc a b α β n g) * T g = c * ∑ᶠ x, star (α x) * ∑ᶠ y, star (β y) * resT a b T x y

def ResCl : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (a b n : ℕ), n = a + b → ∀ T : GL (Fin n) F → ℂ, IsCl T → ∀ x, IsCl (resT a b T x)

def ParCons : Prop :=
  ∀ (F : Type) [Field F] (s n : ℕ) (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n) (b : ℕ) (hb : ∑ i : Fin s, d i.succ = b)
    (p : GL (Fin n) F),
    (p ∈ parab F (stdBlocks d hd) ↔ InPar (d 0) p ∧ brG (d 0) b p ∈ parab F (stdBlocks (fun i : Fin s => d i.succ) hb)) ∧
    ∀ (hp : p ∈ parab F (stdBlocks d hd)) (hp' : brG (d 0) b p ∈ parab F (stdBlocks (fun i : Fin s => d i.succ) hb)),
      leviProj F (stdBlocks d hd) ⟨p, hp⟩ 0 = tlG (d 0) p ∧
      ∀ i : Fin s, leviProj F (stdBlocks d hd) ⟨p, hp⟩ i.succ =
        leviProj F (stdBlocks (fun i : Fin s => d i.succ) hb) ⟨brG (d 0) b p, hp'⟩ i

def FrobL : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (s : ℕ) (d : Fin s → ℕ) (n : ℕ) (hd : ∑ i, d i = n), ∃ c : ℂ, c ≠ 0 ∧
    ∀ (Y : ∀ i, GL (Fin (d i)) F → ℂ) (T : GL (Fin n) F → ℂ), IsCl T →
      ∑ᶠ g, star (hcL (List.ofFn fun i => ⟨d i, Y i⟩) n g) * T g =
        c * ∑ᶠ p : parab F (stdBlocks d hd), star (∏ i, Y i (leviProj F (stdBlocks d hd) p i)) * T p

def JDEq : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ),
    (∀ (D L : List (ℕ × ℕ)) (n : ℕ), JD θ D L n =
      hcL (D.map (fun p => ⟨p.1, detc θ p.1 p.2⟩) ++ L.map fun p => ⟨p.1, cusp θ p.1 p.2⟩) n) ∧
    (∀ k : ℕ, cusp θ 1 k = detc θ 1 k) ∧ ∀ (D L : List (ℕ × ℕ)) (n : ℕ), IsCl (JD θ D L n)

def CuspChar : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), Inj θ → ∀ m : ℕ, 0 < m →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (κ : Representation ℂ (GL (Fin m) F) W),
    κ.IsIrreducible → PositivityTheory.Rg.DzCount.FinCusp κ → ∃ k, Reg (Nat.card F) m k ∧ ∀ x, LinearMap.trace ℂ W (κ x) = cusp θ m k x

def TensTr : Prop :=
  ∀ (s : ℕ) (Γ W : Fin s → Type) [∀ a, Group (Γ a)] [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)]
    [∀ a, FiniteDimensional ℂ (W a)] (κ : ∀ a, Representation ℂ (Γ a) (W a)),
    FiniteDimensional ℂ (PiTensorProduct ℂ W) ∧
      ∀ x : ∀ a, Γ a, LinearMap.trace ℂ _ (piTensor κ x) = ∏ a, LinearMap.trace ℂ _ (κ a (x a))

def LiftHc : Prop :=
  ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) →
    ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsCl α → IsCl β →
    shLift s (hc a b α β n) = hcTw (s : F' →+* F') a b (shLift s α) (shLift s β) n

def KillsHc : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ), n = a + b →
    ∀ (α A : GL (Fin a) F → ℂ) (β B : GL (Fin b) F → ℂ), GlobalTheory.BI.IsChar ℂ ℂ A → GlobalTheory.BI.IsChar ℂ ℂ B → Kills α A → Kills β B →
    Kills (hcTw t a b α β n) (hc a b A B n)

def HcChar : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (a b n : ℕ), n = a + b → ∀ (A : GL (Fin a) F → ℂ) (B : GL (Fin b) F → ℂ),
    GlobalTheory.BI.IsChar ℂ ℂ A → GlobalTheory.BI.IsChar ℂ ℂ B → GlobalTheory.BI.IsChar ℂ ℂ (hc a b A B n)

def JDChar : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), Inj θ → (∀ t k, GlobalTheory.BI.IsChar ℂ ℂ (detc θ t k)) ∧
    ∀ a : Lbl, a.Ok → a.q = Nat.card F → GlobalTheory.BI.IsChar ℂ ℂ (JD θ a.D a.L a.rk)

def LiftDet : Prop :=
  ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ z, s z = z ^ Nat.card F) →
    ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ) (t k : ℕ),
    (∀ δ : GL (Fin t) F', ∃ γ, IsNorm s δ γ) →
    shLift s (detc (pullθ ι θ) t k) = detc θ t (k * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i)

def NormEx : Prop :=
  ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ z, s z = z ^ Nat.card F) →
    ∀ (t : ℕ) (δ : GL (Fin t) F'), ∃ γ, IsNorm s δ γ

def KillsOn (P : Lbl → Prop) : Prop :=
  ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime →
    (∀ z, s z = z ^ Nat.card F) → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), Inj θ →
    ∀ a : Lbl, P a → a.Ok → a.q = Nat.card F →
    Kills (shLift s (JD (pullθ ι θ) a.D a.L a.rk))
      (JD θ (a.lift (Module.finrank F F')).D (a.lift (Module.finrank F F')).L a.rk)

def CuspIrr : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (y : IrrGL k), y.IsCusp → UpperTheory.Zero.LLC.DZ y →
    FiniteDimensional ℂ (fixed y.rep (KOne k (Fin y.1))) ∧ (levelZero y.rep).IsIrreducible ∧
      PositivityTheory.Rg.DzCount.FinCusp (levelZero y.rep)

def TensFix : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s : ℕ) (d : Fin s → ℕ) (V : Fin s → Type) [∀ a, AddCommGroup (V a)] [∀ a, Module ℂ (V a)]
    (σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (V a)), (∀ a, IsSmooth (σ a)) →
    ∃ Φ : PiTensorProduct ℂ V →ₗ[ℂ] PiTensorProduct ℂ fun a => fixed (σ a) (KOne k (Fin (d a))),
      (∀ (x : leviK k fun a => Fin (d a)) (w : PiTensorProduct ℂ V),
        Φ (piTensor σ (x : Levi k fun a => Fin (d a)) w) = piTensor (fun a => levelZero (σ a)) (redLevi k _ x) (Φ w)) ∧
      ∀ w ∈ fixed (piTensor σ) (leviKOne k fun a => Fin (d a)), Φ w = 0 → w = 0

def SubqMap : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = N) (W V Z : Type) [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (π : Representation ℂ (GL (Fin N) k) V)
    (κ : Representation ℂ (Levi 𝓀[k] fun a => Fin (d a)) Z) (Φ : W →ₗ[ℂ] Z),
    (∀ (x : leviK k fun a => Fin (d a)) (w : W), Φ (ρ (x : Levi k fun a => Fin (d a)) w) = κ (redLevi k _ x) (Φ w)) →
    (∀ w ∈ fixed ρ (leviKOne k fun a => Fin (d a)), Φ w = 0 → w = 0) →
    IsSubquotient π (parInd (stdBlocks d hd) ρ) → fixed π (KOne k (Fin N)) ≠ ⊥ →
    ∃ ψ : fixed π (KOne k (Fin N)) →ₗ[ℂ] Z, ψ ≠ 0 ∧
      ∀ (p : parab 𝓀[k] (stdBlocks d hd)) (x : fixed π (KOne k (Fin N))),
        ψ (levelZero π p x) = κ (leviProj 𝓀[k] (stdBlocks d hd) p) (ψ x)

def SuppStd : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (S : Multiset (IrrGL k)), HasSupport π S → ∃ (s : ℕ) (x : Fin s → IrrGL k) (hd : ∑ a, (x a).1 = N),
      Finset.univ.val.map x = S ∧ IsSubquotient π (prodIrr x hd)

def LblOf : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (θ : AlgebraicClosure 𝓀[k] →* ℂ), Inj θ → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (S : Multiset (IrrGL k)), HasSupport π S → fixed π (KOne k (Fin N)) ≠ ⊥ →
    ∃ (s : ℕ) (x : Fin s → IrrGL k) (c : Fin s → ℕ), Finset.univ.val.map x = S ∧
      (∀ a, (x a).IsCusp ∧ UpperTheory.Zero.LLC.DZ (x a) ∧ Reg (Nat.card 𝓀[k]) (x a).1 (c a) ∧
        ∀ γ, LinearMap.trace ℂ _ (levelZero (x a).rep γ) = cusp θ (x a).1 (c a) γ) ∧
      HasLbl θ π ⟨Nat.card 𝓀[k], [], List.ofFn fun a => ((x a).1, c a)⟩

def TypeOfLbl : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (θ : AlgebraicClosure 𝓀[k] →* ℂ) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (b : Lbl), HasLbl θ π b → (∀ p ∈ b.L, p.1 = 1) →
    ∃ (s : ℕ) (d c : Fin s → ℕ) (hd : ∑ a, d a = N) (ω : Fin s → 𝓀[k]ˣ →* ℂˣ), List.ofFn (fun a => (d a, c a)) = b.D ++ b.L ∧
      (∀ a u, (ω a u : ℂ) = θ (algebraMap _ _ (u : 𝓀[k])) ^ c a) ∧ UpperTheory.Gal.TypesAndIwahori.HasTypeVec π (stdBlocks d hd) ω

def LblIso : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] (i : k ≃+* K),
    (∀ x : k, valuation K (i x) ≤ 1 ↔ valuation k x ≤ 1) →
    ∀ (j : AlgebraicClosure 𝓀[k] ≃+* AlgebraicClosure 𝓀[K]),
    (∀ (x : 𝒪[k]) (y : 𝒪[K]), (y : K) = i x →
      j (algebraMap _ _ (IsLocalRing.residue _ x)) = algebraMap _ _ (IsLocalRing.residue _ y)) →
    ∀ (θ : AlgebraicClosure 𝓀[K] →* ℂ) (N : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GL (Fin N) k) V) (P : Representation ℂ (GL (Fin N) K) W) (e : V ≃ₗ[ℂ] W),
      (∀ g x, e (π g x) = P (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)) →
      ∀ a : Lbl, HasLbl (θ.comp j.toMonoidHom) π a → HasLbl θ P a

def JDIso : Prop :=
  ∀ (F F' : Type) [Field F] [Field F'] [Finite F] (r : F ≃+* F') (j : AlgebraicClosure F ≃+* AlgebraicClosure F'),
    (∀ x, j (algebraMap _ _ x) = algebraMap _ _ (r x)) → ∀ (θ : AlgebraicClosure F' →* ℂ) (D L : List (ℕ × ℕ)) (n : ℕ)
    (g : GL (Fin n) F), JD θ D L n (Matrix.GeneralLinearGroup.map r.toRingHom g) = JD (θ.comp j.toMonoidHom) D L n g

def CuspIso : Prop :=
  ∀ (F F' : Type) [Field F] [Field F'] [Finite F] (r : F ≃+* F') (j : AlgebraicClosure F ≃+* AlgebraicClosure F'),
    (∀ x, j (algebraMap _ _ x) = algebraMap _ _ (r x)) → ∀ (θ : AlgebraicClosure F' →* ℂ) (m c : ℕ)
    (g : GL (Fin m) F), cusp θ m c (Matrix.GeneralLinearGroup.map r.toRingHom g) = cusp (θ.comp j.toMonoidHom) m c g

def ResEmbEx : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 E)) , IsPlaceOver A v → (∃ e, ResEmb A v e) ∧ ∃ Θ : IsLocalRing.ResidueField A →* ℂ, Inj Θ

def ResEmbCompat : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver M v) e e',
    ResEmb A v e → ResEmb A w.1 e' →
    ∃ (r : 𝓀[v.adicCompletion K] →+* 𝓀[w.1.adicCompletion M])
      (j : AlgebraicClosure 𝓀[v.adicCompletion K] ≃+* AlgebraicClosure 𝓀[w.1.adicCompletion M]),
      (∀ (x : 𝒪[v.adicCompletion K]) (y : 𝒪[w.1.adicCompletion M]), (y : w.1.adicCompletion M) = completionMap v w.1 x →
        IsLocalRing.residue _ y = r (IsLocalRing.residue _ x)) ∧
      (∀ x, j (algebraMap _ _ x) = algebraMap _ _ (r x)) ∧ ∀ x, e' (j x) = e x

def UnrOfIne : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsGalois K M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 M)), IsPlaceOver A v → IsPlaceOver A w → (∀ t ∈ Ine (F := K) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes M t) →
    w.under (𝓞 K) = v ∧ UpperTheory.ConvolutionTheory.GM.Unr M v ∧
      ∀ x : 𝓞 K, x ∉ v.asIdeal ^ 2 → algebraMap (𝓞 K) (𝓞 M) x ∉ w.asIdeal ^ 2

def ResDeg : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M], (Module.finrank K M).Prime →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver M v), ¬ UpperTheory.ConvolutionTheory.GM.Split M v → UpperTheory.ConvolutionTheory.GM.Unr M v →
    ∀ [Algebra 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M]],
      Module.finrank 𝓀[v.adicCompletion K] 𝓀[w.1.adicCompletion M] = Module.finrank K M ∧
      ∃ s : 𝓀[w.1.adicCompletion M] ≃ₐ[𝓀[v.adicCompletion K]] 𝓀[w.1.adicCompletion M],
        ∀ z, s z = z ^ Nat.card 𝓀[v.adicCompletion K]

def StableOf : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M] [IsTotallyComplex K]
    [IsTotallyComplex M], (Module.finrank K M).Prime → ∀ n : ℕ, 0 < n → ∀ (π : CuspSub K n) (P : CuspSub M n),
    WeakBC (Cusp.cx π).sat (Cusp.cx P).sat →
    (∀ g : M ≃ₐ[K] M, (Cusp.cx P).ConjIso g.toRingEquiv) ∧ SplitLift (Cusp.cx π) (Cusp.cx P)

def StepAt (P₀ : Lbl → Prop) (split : Prop → Prop) : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] [IsGalois K M] [IsTotallyComplex K] [IsTotallyComplex M], (Module.finrank K M).Prime →
    ∀ n : ℕ, 0 < n → ∀ (π : CuspSub K n) (P : CuspSub M n), WeakBC (Cusp.cx π).sat (Cusp.cx P).sat →
    ∀ (A : ValuationSubring Ω) (Θ : IsLocalRing.ResidueField A →* ℂ), Inj Θ →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver M v), split (UpperTheory.ConvolutionTheory.GM.Split M v) → UpperTheory.ConvolutionTheory.GM.Unr M v →
    ∀ e e', ResEmb A v e → ResEmb A w.1 e' → ∀ τ τ', π.IsLocComp v τ → P.IsLocComp w.1 τ' →
    ∀ a : Lbl, P₀ a → HasLbl (Θ.comp e.toMonoidHom) τ.ρ a → ∃ b, a.Le b ∧ HasLbl (Θ.comp e'.toMonoidHom) τ'.ρ b

def LblOn (P₀ : Lbl → Prop) : Prop :=
  ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (n : ℕ), 0 < n → ∀ X Y : Pt E Ω n, Lifts X Y →
    ∀ (A : ValuationSubring Ω) (Θ : IsLocalRing.ResidueField A →* ℂ), Inj Θ →
    (∀ t ∈ Ine (F := X.K) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Y.K t) →
    ∀ (v : HeightOneSpectrum (𝓞 X.K)) (w : HeightOneSpectrum (𝓞 Y.K)), IsPlaceOver A v → IsPlaceOver A w →
    ∀ e e', ResEmb A v e → ResEmb A w e' → ∀ τ τ', X.π.IsLocComp v τ → Y.π.IsLocComp w τ' →
    ∀ a : Lbl, P₀ a → HasLbl (Θ.comp e.toMonoidHom) τ.ρ a → ∃ b, a.Le b ∧ HasLbl (Θ.comp e'.toMonoidHom) τ'.ρ b

def LiftsFix : Prop :=
  ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (n : ℕ) (X Y : Pt E Ω n), Lifts X Y →
    ∀ x : X.K, ∃ y : Y.K, algebraMap Y.K Ω y = algebraMap X.K Ω x

def PlaceEx : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [IsTotallyComplex M] [Field Ω] [Algebra K Ω] [Algebra M Ω]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → ∀ (n : ℕ) (P : CuspSub M n),
    ∃ w : HeightOneSpectrum (𝓞 M), IsPlaceOver A w ∧ ∃ τ, P.IsLocComp w τ

def UnifTower : Prop :=
  ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (n : ℕ) (X Y : Pt E Ω n), Lifts X Y → ∀ (A : ValuationSubring Ω),
    (∀ t ∈ Ine (F := X.K) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Y.K t) →
    ∀ (v : HeightOneSpectrum (𝓞 X.K)) (w : HeightOneSpectrum (𝓞 Y.K)), IsPlaceOver A v → IsPlaceOver A w →
    ∀ g : ℕ, ((g : ℕ) : 𝓞 X.K) ∉ v.asIdeal ^ 2 → ((g : ℕ) : 𝓞 Y.K) ∉ w.asIdeal ^ 2

def BaseQ : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* v.adicCompletion E),
    Continuous i → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 ∧ Nat.card 𝓀[v.adicCompletion E] = g ∧
      Nonempty (𝓀[v.adicCompletion E] ≃+* ZMod g)

def CardRes : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)), Nat.card 𝓀[v.adicCompletion E] = normV v

def TameRead : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A v) (g : ℕ) [Fact g.Prime] (m : ℕ), 0 < m → ∀ (D : UpperTheory.Zero.LLC.Ext h g m) (R : Ine (F := E) A →* D.Kˣ), D.Res R →
    ∃ ι : D.K →+* IsLocalRing.ResidueField A, ∀ (t : Ine (F := E) A) (ϖ : Ω), ϖ ^ (g ^ m - 1) = (g : Ω) →
      ∀ z : A, (z : Ω) = (t : G E Ω) ϖ / ϖ → ι (R t : D.Kˣ) = IsLocalRing.residue A z

def ArtRead : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A v) (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ a, IsLocalArtin h a →
    ∀ e, ResEmb A v e → ∀ (t : Ine (F := E) A) (ϖ : Ω), ϖ ^ (normV v - 1) = (g : Ω) →
    ∃ (z : A) (u : 𝒪[v.adicCompletion E]ˣ), (z : Ω) = (t : G E Ω) ϖ / ϖ ∧ unitIncl _ u = a (ineIncl h t) ∧
      e (algebraMap _ _ ((unitRes _ u : 𝓀[v.adicCompletion E]ˣ) : 𝓀[v.adicCompletion E])) = IsLocalRing.residue A z ∧
      IsLocalRing.residue A z ^ (normV v - 1) = 1

def TypeChar : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* v.adicCompletion E),
    Continuous i → ∀ (r : 𝓀[v.adicCompletion E] ≃+* ZMod g) (y : IrrGL (v.adicCompletion E)) (τ : FDRep ℂ (GlobalTheory.GLq.Gn g y.1)),
    GlobalTheory.GLq.IsCusp τ.character → GlobalTheory.SerSys.TameGen.Inflates (y.rep.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
    ∀ γ, τ.character (Matrix.GeneralLinearGroup.map r.toRingHom γ) = LinearMap.trace ℂ _ (levelZero y.rep γ)

def NameOf : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (m : ℕ), 0 < m → ∀ (F K 𝔨 : Type) [Field F] [Finite F] [Field K] [Algebra (ZMod g) K] [Field 𝔨],
    Module.finrank (ZMod g) K = m → ∀ (r : F ≃+* ZMod g) (e : AlgebraicClosure F →+* 𝔨) (ι : K →+* 𝔨) (Θ : 𝔨 →* ℂ), Inj Θ →
    ∀ c : ℕ, Reg g m c → ∃ θ : Kˣ →* ℂˣ, (∀ u, (θ u : ℂ) = Θ (ι u) ^ c) ∧ GlobalTheory.Published.IsRegularChar g m θ ∧
      ∀ τ : FDRep ℂ (GlobalTheory.GLq.Gn g m),
        (∀ γ, τ.character (Matrix.GeneralLinearGroup.map r.toRingHom γ) = cusp (Θ.comp e.toMonoidHom) m c γ) →
        UpperTheory.Zero.LLC.Names g m θ τ

def CuspIne : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A v) (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* v.adicCompletion E), Continuous i →
    ∀ (Θ : IsLocalRing.ResidueField A →* ℂ), Inj Θ → ∀ (e : AlgebraicClosure 𝓀[v.adicCompletion E] →+* IsLocalRing.ResidueField A)
      (y : IrrGL (v.adicCompletion E)) (c : ℕ), y.IsCusp → UpperTheory.Zero.LLC.DZ y → Reg g y.1 c →
      (∀ γ, LinearMap.trace ℂ _ (levelZero y.rep γ) = cusp (Θ.comp e.toMonoidHom) y.1 c γ) →
    ∀ rc, UpperTheory.Zero.LLC.IsRecT h rc → ∀ f : ℕ, 0 < f → y.1 ∣ f → ∀ (t : Ine (F := E) A) (ϖ : Ω), ϖ ^ (g ^ f - 1) = (g : Ω) →
      ∀ z : A, (z : Ω) = (t : G E Ω) ϖ / ϖ → (rc y).inePol (t : G E Ω) =
        ∏ j ∈ Finset.range y.1, (X - C (Θ (IsLocalRing.residue A z) ^ (c * g ^ j * ((g ^ f - 1) / (g ^ y.1 - 1)))))

def SuppIne : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A v) (rc : IrrGL (v.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (x : IrrGL (v.adicCompletion E)) (S : Multiset (IrrGL (v.adicCompletion E))), HasSupport x.rep S →
    ∀ t : Ine (F := E) A, (rc x).inePol (t : G E Ω) = (S.map fun y => (rc y).inePol (t : G E Ω)).prod

def TameChars : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (ω : Fin N → 𝓀[k]ˣ →* ℂˣ), UpperTheory.Gal.TypesAndIwahori.HasTameSupp π ω →
    ∃ (ξ : Fin N → kˣ →* ℂˣ) (hξ : ∀ j, IsSmoothChar (ξ j)), (∀ j, UpperTheory.Zero.LLC.TameChar (ξ j)) ∧
      HasSupport π (GlobalTheory.RoadU.chars ξ hξ) ∧ ∀ j (u : 𝒪[k]ˣ), ξ j (unitIncl k u) = ω j (unitRes k u)

end UpperTheory.Gal.InertialTypesAlt

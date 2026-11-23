import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Lit.Ty

def Dom (P Q : Multiset ℕ) : Prop :=
  P.sum = Q.sum ∧ ∀ j : ℕ, ((Q.sort (· ≥ ·)).take j).sum ≤ ((P.sort (· ≥ ·)).take j).sum

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def SameI (x y : WD h) : Prop :=
  ∃ (n : ℕ) (a b : WDRep h (Fin n → ℂ)) (e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)), WD.mk a = x ∧ WD.mk b = y ∧
    ∀ (s : ↥(Ine (F := E) A)) v, e (a.ρ (ineIncl h s) v) = b.ρ (ineIncl h s) (e v)

variable (h) in

structure Shape : Type 1 where
  r : ℕ
  ρ : Fin r → WD h
  irr : ∀ i, IsIrrWD (ρ i)
  k : Fin r → ℕ
  pos : ∀ i, 1 ≤ k i

namespace Shape

def wd (S : Shape h) : WD h := sumList (List.ofFn fun i => (S.ρ i).lpChar (WD.lpSp h (S.k i)))

open Classical in

def part (S : Shape h) (ρ₀ : WD h) : Multiset ℕ := (Finset.univ.filter fun i => SameI (S.ρ i) ρ₀).val.map S.k

def Below (S' S : Shape h) : Prop := ∀ ρ₀, IsIrrWD ρ₀ → Dom (S.part ρ₀) (S'.part ρ₀)

def Same (S' S : Shape h) : Prop := ∀ ρ₀, IsIrrWD ρ₀ → S'.part ρ₀ = S.part ρ₀

end Shape

def IsIota {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {H V V' : Type} [Group H] [AddCommGroup V] [Module (Qbar l) V]
    [AddCommGroup V'] [Module ℂ V'] (π : Representation (Qbar l) H V) (π' : Representation ℂ H V') : Prop :=
  ∃ f : V ≃+ V', (∀ (z : Qbar l) v, f (z • v) = ι z • f v) ∧ ∀ g v, f (π g v) = π' g (f v)

def ShottonTypes : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (l : ℕ) [Fact l.Prime], ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
    ∀ (ι : Qbar l ≃+* ℂ) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (n : ℕ), 1 ≤ n → ∀ S : Shape h, S.wd.lpDim = n →
      ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (Qbar l) W) (σ : Representation (Qbar l) ↥(GlobalTheory.LFun.KGL w n) W),
        σ.IsIrreducible ∧ GlobalTheory.PRep.IsSmooth σ ∧
        ∀ (V : Type) [AddCommGroup V] [Module (Qbar l) V] (π : Representation (Qbar l) (GL (Fin n) (w.adicCompletion E)) V),
          π.IsIrreducible → GlobalTheory.PRep.IsSmooth π → GlobalTheory.PRep.IsAdmissible π →
          ∀ π' : SmIrr (GL (Fin n) (w.adicCompletion E)), IsIota ι π π'.ρ → ∀ S' : Shape h, S'.wd = rc (algNorm π') →
            ((∃ f : W →ₗ[Qbar l] V, Function.Injective f ∧ ∀ k v, f (σ k v) = π k (f v)) → S'.Below S) ∧
            (S'.Same S → Module.finrank (Qbar l) (σ.IntertwiningMap (π.comp (GlobalTheory.LFun.KGL w n).subtype)) = 1)

end UpperTheory.V.Lit.Ty

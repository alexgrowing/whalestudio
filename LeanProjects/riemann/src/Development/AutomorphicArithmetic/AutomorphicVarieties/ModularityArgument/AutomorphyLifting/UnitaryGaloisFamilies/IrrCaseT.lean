import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.GalUnitaryT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AbsCentral
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.V.Af.Gu UpperTheory.Zero.LLC

namespace UpperTheory.V.Z.Win.Gu

structure CompatG {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (p : ∀ w : HeightOneSpectrum (𝓞 E), Par Ω w)
    (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  ht : ∀ w, (∀ A h rc, IsRecT h rc → Gd (p w A h rc)) → HasHTAt r HT w
  par : ∀ w, ParAtT ι r w (p w)

def GdLaws : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w),
    (∀ x y : WD h, Gd (x.lpSum y) ↔ Gd x ∧ Gd y) ∧ (∀ (x : WD h) (t : ℝ), Gd (x.lpTw t) ↔ Gd x) ∧
      (∀ L : List (WD h), Gd (sumList L) ↔ ∀ x ∈ L, Gd x) ∧ ∀ x : WD h, x.unr → Gd x

def PlainGd : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecT h rc →
    ∀ (n : ℕ) (τ : SmIrr (GL (Fin n) (w.adicCompletion E))), GlobalTheory.RoadU.PlainTor (cl τ) → Gd (rc (algNorm τ))

def SumHTAt : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (a b : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)) (r' : G E Ω →* GL (Fin b) (Qbar l)), Continuous r → Continuous r' →
    ∀ HT HT' w, HasHTAt r HT w → HasHTAt r' HT' w → HasHTAt (Formalism.MainNotions.SumRepresentations.At.sumRep r r') (fun τ => HT τ + HT' τ) w

def SumTwoG : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (a b : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)) (r' : G E Ω →* GL (Fin b) (Qbar l)) p p' HT HT',
    CompatG ι r p HT → CompatG ι r' p' HT' →
      CompatG ι (Formalism.MainNotions.SumRepresentations.At.sumRep r r') (fun w A h rc => (p w A h rc).lpSum (p' w A h rc)) fun τ => HT τ + HT' τ

def SumFamG : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (c : ℕ), 1 ≤ c → ∀ (N : Fin c → ℕ), (∀ i, 1 ≤ N i) → ∀ (n : ℕ), ∑ i, N i = n →
    ∀ (r : ∀ i, G E Ω →* GL (Fin (N i)) (Qbar l)) (p : Fin c → ∀ w : HeightOneSpectrum (𝓞 E), Par Ω w)
      (HT : Fin c → (E →+* Qbar l) → Multiset ℤ), (∀ i, CompatG ι (r i) (p i) (HT i)) →
      ∃ R : G E Ω →* GL (Fin n) (Qbar l),
        CompatG ι R (fun w A h rc => sumList (List.ofFn fun i => p i w A h rc)) (fun τ => ∑ i, HT i τ) ∧
        (IsIrr R → c = 1 ∧ ∀ i, IsIrr (r i))

def PolG : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (P : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    (CG.mk P).IsRegAlg → IsPolarized P χ →
    ∀ σ : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin a) (w.adicCompletion E)), (∀ w, P.IsLocComp w (σ w)) →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (HT : (E →+* Qbar l) → Multiset ℤ),
        CompatG ι r (fun w _ _ rc => rc (algNorm (σ w))) HT ∧
        ∀ τ : E →+* Qbar l, (HT τ).map (fun k : ℤ => (k : ℂ)) =
          ((CG.mk P).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z

def HalfG : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (P : CuspSub E a), P.IsCsd →
    ∀ (ρ : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin a) (w.adicCompletion E))), (∀ w, P.IsLocComp w (ρ w)) →
    ∀ (m : (E →+* ℂ) → Multiset ℂ), (∀ τ, P.HasInfChar τ (m τ)) → ∀ e : ℤ,
      (∀ τ, (m τ).Nodup ∧ ∀ z ∈ m τ, ∃ j : ℤ, z + (e : ℂ) / 2 = j) →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (HT : (E →+* Qbar l) → Multiset ℤ),
        CompatG ι r (fun w _ _ rc => (rc (cl (ρ w))).lpTw ((e : ℝ) / 2)) HT ∧
        ∀ τ : E →+* Qbar l, (HT τ).map (fun k : ℤ => (k : ℂ)) = (m (ι.toRingHom.comp τ)).map fun z => -(z + (e : ℂ) / 2)

def ProdT : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (n c : ℕ) (N : Fin c → ℕ) (hn : ∑ i, N i = n) (w : HeightOneSpectrum (𝓞 E))
    (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))), (∀ i, GlobalTheory.SmGL.IsUnitarisable (σ i).ρ) →
    ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)), Nonempty (τ.ρ.Equiv (locProd hn w σ)) →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecT h rc →
      rc (cl τ) = sumList (List.ofFn fun i => rc (cl (σ i)))

def SpehT : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (a d : ℕ) (P : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (ρ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (σ : SmIrr (GL (Fin (d * a)) (w.adicCompletion E))), 1 ≤ a → 1 ≤ d → P.IsLocComp w ρ →
    GlobalTheory.SmGL.IsUnitarisable ρ.ρ → IsSpeh (cl ρ) d σ.ρ →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecT h rc →
      rc (cl σ) = sumList ((List.range d).map fun k : ℕ => (rc (cl ρ)).lpTw (((d : ℝ) - 1) / 2 - k))

def RecTotT : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (n c : ℕ) (a d : Fin c → ℕ) (hn : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i)) (w : HeightOneSpectrum (𝓞 E))
    (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (σ : ∀ i, SmIrr (GL (Fin (d i * a i)) (w.adicCompletion E))),
    (∀ i, 1 ≤ a i ∧ 1 ≤ d i) → (∀ i, (P i).IsLocComp w (ρ i)) →
    (∀ i, GlobalTheory.SmGL.IsUnitarisable (ρ i).ρ ∧ GlobalTheory.SmGL.IsUnitarisable (σ i).ρ ∧ IsSpeh (cl (ρ i)) (d i) (σ i).ρ) →
    ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)), Nonempty (τ.ρ.Equiv (locProd hn w σ)) →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecT h rc →
      totPar n d ρ A h rc = rc (algNorm τ)

def FrobTotT : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n c : ℕ) (a d : Fin c → ℕ) (r : G E Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
    ∀ (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (S : Fin c → Multiset ℂˣ), (∀ i, GlobalTheory.LFun.HasSatGL w (ρ i).ρ (S i)) →
      ParAtT ι r w (totPar n d ρ) → FrobEig ι r w (algSat n (normV w) (satTot w d S))

def IrrCaseT : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ (c : ℕ) (a d : Fin c → ℕ) (hn : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i))
      (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (m : Fin c → (E →+* ℂ) → Multiset ℂ)
      (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (d i * a i)) (w.adicCompletion E))),
      GlobalTheory.BcSpeh.Parts π a d hn P ρ m → (∀ i w, IsSpeh (cl (ρ i w)) (d i) (σ i w).ρ) →
      (∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd hn w (σ · w))) →
      (∀ w, IsUnramU π w → ∀ i, ∃ B, (CG.mk (P i)).HasSat w B) →
      c = 1 → (∀ i, d i = 1) → ∀ r : G E Ω →* GL (Fin n) (Qbar l), IsSSRep r →
      (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ S : Fin c → Multiset ℂˣ, (∀ i, (CG.mk (P i)).HasSat w (S i)) ∧
        FrobEig ι r w (algSat n (normV w) (satTot w d S))) →
      ∃ Q : CuspSub E n, (CG.mk Q).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj Q ∧ AttC ι r Q ∧
        (∀ φ lam, HasWeightAt π φ lam → Q.HasInfChar φ (infOfWeight lam)) ∧ (∀ w, IsUnramU π w → ∃ B, (CG.mk Q).HasSat w B) ∧
        ∀ w, IsSplitAt w → ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)), Q.IsLocComp w τ →
          IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ

end UpperTheory.V.Z.Win.Gu

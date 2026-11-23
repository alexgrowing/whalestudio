import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.TypeNear
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BlockCharacterApproximation.OfVecFixedIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.NumberField

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong
open UpperTheory.Gal.CharacterCongruences (Ch PolyApproxAt)

namespace UpperTheory.Gal.NearKilling

section Abstract

variable {Γ I : Type} [Group Γ] [Group I] {a c : ℕ}

def Diag {k : Type} [Field k] (ρ : Γ →* GL (Fin a) k) (j : I →* Γ) (f : Fin a → I → k) : Prop :=
  IsSSRep (ρ.comp j) ∧ (∃ κ : Fin a → I →* kˣ, ∀ t s, (κ t s : k) = f t s) ∧ TrSum ρ j f

def DiagAt {k : Type} [NormedField k] (ε : ℝ) (r : Γ →* GL (Fin a) k) (j : I →* Γ) (blk : Fin a → Fin (c + 1))
    (η : Fin (c + 1) → I → k) : Prop :=
  ∃ (H : Subgroup Γ) (_ : H.Normal) (hj : ∀ s, j s ∈ H) (F : Near r H ε) (e : Fin (c + 1) → I → ℕ),
    ∀ i, Diag (F.ρ i) (j.codRestrict H hj) fun t s => η (blk t) s * F.z i ^ e (blk t) s

end Abstract

section Global

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

abbrev Off (l : ℕ) (S : Set (HeightOneSpectrum (𝓞 E))) : Type :=
  {u : HeightOneSpectrum (𝓞 E) // IsSplitAt u ∧ ((l : ℕ) : 𝓞 E) ∉ u.asIdeal ∧ u ∉ S}

def IsTr {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {S : Set (HeightOneSpectrum (𝓞 E))} (π : CuspSub E a) (t : Off l S → Qbar l) : Prop :=
  ∀ u : Off l S, ∃ B, (CG.mk π).HasSat u.1 B ∧ t u = ι.symm (UpperTheory.V.Af.algSat a (normV u.1) B).sum

end Global

def NearOfDiag : Prop :=
  ∀ (k Γ I : Type) [NormedField k] [CharZero k] [Group Γ] [Group I] (a c : ℕ) (r : Γ →* GL (Fin a) k) (j : I →* Γ)
    (blk : Fin a → Fin (c + 1)) (η : Fin (c + 1) → I → k), (∀ ε : ℝ, 0 < ε → DiagAt ε r j blk η) →
    NearTr r j (fun t s => η (blk t) s) ∧ ∀ b₀, NearKills r j (η b₀) fun b => η (b₀.succAbove b)

def DiagPush : Prop :=
  ∀ (k Γ Γ' I I' : Type) [NormedField k] [Group Γ] [Group Γ'] [Group I] [Group I'] (a c : ℕ) (ε : ℝ) (r : Γ →* GL (Fin a) k)
    (f : Γ' →* Γ), Function.Injective f → f.range.Normal → ∀ (j : I →* Γ) (j' : I' →* Γ') (g : I ≃* I'), (∀ s, f (j' (g s)) = j s) →
    ∀ (blk : Fin a → Fin (c + 1)) (η' : Fin (c + 1) → I' → k) (F : Near (r.comp f) ⊤ ε) (e : Fin (c + 1) → I' → ℕ),
      (∀ i, Diag (F.ρ i) (j'.codRestrict ⊤ fun _ => trivial) fun t s => η' (blk t) s * F.z i ^ e (blk t) s) →
      DiagAt ε r j blk fun b s => η' b (g s)

def CongType : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) → ∀ w, IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
    ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), π.IsLocComp w σ →
    ∀ (c : ℕ) (d : Fin c → ℕ) (hd : ∑ b, d b = a) (θ : Fin c → (𝓀[w.adicCompletion E])ˣ →* ℂˣ), HasTypeVec σ.ρ (stdBlocks d hd) θ →
    ∀ N m : ℕ, m ≤ N → ∀ (ψ : (𝓀[w.adicCompletion E])ˣ →* Multiplicative (ZMod (l ^ N))) (n : Fin c → ℕ),
    ∃ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite ∧ ∃ t : Off l S → Qbar l, IsTr ι π t ∧
      PolyApproxAt (‖(l : Qbar l)‖ ^ m) (Sum.elim t fun _ : Multiplicative (ZMod (l ^ N)) => 1)
        {z | ∃ ξ : Ch (l ^ N), ξ ^ (l ^ (N - m)) ≠ 1 ∧ ∃ (π' : CuspSub E a) (t' : Off l S → Qbar l),
          InScope .all l π' (quadChar E ^ a) ∧ IsTr ι π' t' ∧
          (∀ σ', π'.IsLocComp w σ' → HasTypeVec σ'.ρ (stdBlocks d hd) fun b => θ b * (ξ.comp ψ) ^ n b) ∧
          z = Sum.elim t' fun x => ι.symm (ξ x : ℂ)}

def DenseFrob : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite →
    Dense {g : G E Ω | ∃ u, IsSplitAt u ∧ u ∉ S ∧ ∃ A : ValuationSubring Ω, IsPlaceOver A u ∧ IsFrob A (normV u) g⁻¹}

def NearOfCong : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite →
    ∀ (π : CuspSub E a) (r : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → ∀ t : Off l S → Qbar l, IsTr ι π t →
    ∀ (D : Type) (d₀ : D) (ε : ℝ) (Z : Set (Off l S ⊕ D → Qbar l)), PolyApproxAt ε (Sum.elim t fun _ : D => 1) Z →
    ∀ Q : (G E Ω →* GL (Fin a) (Qbar l)) → Qbar l → Prop,
      (∀ z ∈ Z, ∃ (π' : CuspSub E a) (ρ : G E Ω →* GL (Fin a) (Qbar l)), Weak π' ι ρ ∧ IsTr ι π' (fun u => z (.inl u)) ∧
        Q ρ (z (.inr d₀))) →
      ∃ F : Near r ⊤ ε, ∀ i, ∃ ρ, F.ρ i = ρ.comp (⊤ : Subgroup (G E Ω)).subtype ∧ Q ρ (F.z i)

def UnlinkedOfType : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
    ∀ (c : ℕ) (d : Fin c → ℕ) (hd : ∑ b, d b = a) (θ : Fin c → (𝓀[w.adicCompletion E])ˣ →* ℂˣ), (∀ b, 0 < d b) →
      Function.Injective θ → HasTypeVec σ.ρ (stdBlocks d hd) θ →
      ∃ (ξ : Fin a → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)),
        HasSupport (algNorm σ).rep (GlobalTheory.RoadU.chars ξ hξ) ∧ GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ξ hξ) ∧
        ∀ j, IsTameLift (ξ j) (θ (blockOf d hd j))

def DiagOfToral : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (l : ℕ) [Fact l.Prime] (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r → (wdOf h hl ι r).mono0 →
    ∀ κ : Fin a → Weil h →* ℂˣ, (∀ g, (wdOf h hl ι r).charPol g = ∏ j, (X - C (κ j g : ℂ))) →
      Diag (r.comp (⊤ : Subgroup (G E Ω)).subtype) ((Ine (F := E) A).subtype.codRestrict ⊤ fun _ => trivial)
        fun j s => ι.symm (κ j (ineIncl h s))

def OneLevel : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ w, IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
    ∀ (c : ℕ) (d : Fin (c + 1) → ℕ) (hd : ∑ b, d b = a) (θ : Fin (c + 1) → (𝓀[w.adicCompletion E])ˣ →* ℂˣ),
      (∀ b, 0 < d b) → HasTypeVec σ.ρ (stdBlocks d hd) θ →
    ∀ art : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h art →
    ∀ η : Fin (c + 1) → (w.adicCompletion E)ˣ →* ℂˣ, (∀ b, IsTameLift (η b) (θ b)) →
    ∀ N m e : ℕ, m ≤ N → 0 < e → (∀ b, θ b ^ e = 1) → c * e ≤ l ^ (N - m) → l ^ N ∣ normV w - 1 →
      ∃ (F : Near r ⊤ (‖(l : Qbar l)‖ ^ m)) (x : Fin (c + 1) → ↥(Ine (F := E) A) → ℕ),
        ∀ i, Diag (F.ρ i) ((Ine (F := E) A).subtype.codRestrict ⊤ fun _ => trivial)
          fun t s => ι.symm (η (blockOf d hd t) (art (ineIncl h s))) * F.z i ^ x (blockOf d hd t) s

def UnrField : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∀ f : ℕ, 0 < f → ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite →
    ∃ X : UnramifiedFromSplittingCriterion.Fld E Ω, UnramifiedFromSplittingCriterion.Tower S X ∧
      (∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ τ ∈ Ine (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) X.K τ) ∧
        ∀ w' : HeightOneSpectrum (𝓞 X.K), IsPlaceOver A w' → normV w' = normV w ^ f) ∧
      ∀ u : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt u → ∀ A : ValuationSubring Ω, IsPlaceOver A u → ∀ τ ∈ Ine (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) X.K τ

def TowerLift : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l a : ℕ) [Fact l.Prime],
    1 ≤ a → ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∀ S : Set (HeightOneSpectrum (𝓞 E)), (∀ u ∉ S, ∃ B, (CG.mk π).HasSat u B) → ∀ X : UnramifiedFromSplittingCriterion.Fld E Ω, UnramifiedFromSplittingCriterion.Tower S X →
    (∀ u : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt u → ∀ A : ValuationSubring Ω, IsPlaceOver A u → ∀ τ ∈ Ine (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) X.K τ) →
    ∃ P : CuspSub X.K a, InertialTypesAlt.Lifts (InertialTypesAlt.Pt.base Ω π) ({ K := X.K, π := P } : InertialTypesAlt.Pt E Ω a) ∧
      InScope .csd l P (quadChar X.K ^ a) ∧
      ∀ (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K))

def TypeBC : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ), 0 < a →
    ∀ (π : CuspSub E a) (Y : InertialTypesAlt.Pt E Ω a), InertialTypesAlt.Lifts (InertialTypesAlt.Pt.base Ω π) Y →
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 Y.K)) [w.asIdeal.LiesOver v.asIdeal],
      IsPlaceOver A v → IsPlaceOver A w → (∀ t ∈ Ine (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) Y.K t) →
    ∀ τ τ', π.IsLocComp v τ → Y.π.IsLocComp w τ' →
    ∀ (c : ℕ) (d : Fin c → ℕ) (hd : ∑ b, d b = a) (θ : Fin c → (𝓀[v.adicCompletion E])ˣ →* ℂˣ), (∀ b, 0 < d b) →
      HasTypeVec τ.ρ (stdBlocks d hd) θ → ∀ η : Fin c → (v.adicCompletion E)ˣ →* ℂˣ, (∀ b, IsTameLift (η b) (θ b)) →
      ∃ θ' : Fin c → (𝓀[w.adicCompletion Y.K])ˣ →* ℂˣ, HasTypeVec τ'.ρ (stdBlocks d hd) θ' ∧
        ∀ b, IsTameLift ((η b).comp (GlobalTheory.BCChar.normU v w)) (θ' b)

def IneNorm : Prop :=
  ∀ (E M Ω : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω] [Algebra E M] [Algebra E Ω] [Algebra M Ω]
    [IsScalarTower E M Ω] [IsAlgClosure E Ω] [IsAlgClosure M Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E))
    (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal] (h : IsPlaceOver A v) (h' : IsPlaceOver A w),
    (∀ t ∈ Ine (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) M t) → ∀ art art', IsLocalArtin h art → IsLocalArtin h' art' →
    ∃ g : ↥(Ine (F := E) A) ≃* ↥(Ine (F := M) A), (∀ s, UpperTheory.V.Af.Bc.res E Ω M (g s : G M Ω) = s) ∧
      ∀ s, art (ineIncl h s) = GlobalTheory.BCChar.normU v w (art' (ineIncl h' (g s)))

end UpperTheory.Gal.NearKilling

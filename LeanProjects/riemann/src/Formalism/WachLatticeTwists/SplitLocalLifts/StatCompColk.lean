import Formalism.WachLatticeTwists.SplitLocalLifts.Cocycles1MapOfEquivariant

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

def SpecK {O A T' G : Type*} [CommRing O] [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    {P : Type*} [AddCommGroup P] [Module A P] [Module O P] [SMulCommClass A O P]
    {L : Type*} [AddCommGroup L] [Module A L] [Module O L]
    (r : G →* A) (χ : G →* T'ˣ) (Dl : Subgroup G) (inc : P →ₗ[A] A) (v₁ : L)
    (Hf₁ : Submodule O (H1z (resRep (uRep O (M := P) r χ) Dl))) (ℓ e' : ℕ) {j : ℕ}
    (κ : Fin j → G → L) (Kc : Fin j → G → A) : Prop :=
  (∃ Kz : Fin j → coZ1s (resRep (uRep O (M := P) r χ) Dl),
    (∀ a (g : Dl), Kc a g = inc ((Kz a : Dl → P) g)) ∧ ∀ a, Submodule.mkQ _ (Kz a) ∈ Hf₁) ∧
  ∀ a, ∀ g ∈ Dl, Kc a g • v₁ = ((ℓ : O) ^ e') • κ a g

def Speck {O A T' G : Type*} [CommRing O] [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    {P : Type*} [AddCommGroup P] [Module A P] [Module O P] [SMulCommClass A O P]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (δO : O) (Dl : Subgroup G) (inc : P →ₗ[A] A)
    (Hf₁ : Submodule O (H1z (resRep (uRep O (M := P) r χ) Dl))) (ℓ e' : ℕ)
    (u : G → O) (k0 : G → A) : Prop :=
  (∃ kz : coZ1s (resRep (uRep O (M := P) r χ) Dl),
    (∀ g : Dl, k0 g = inc ((kz : Dl → P) g)) ∧ Submodule.mkQ _ kz ∈ Hf₁) ∧
  (∀ g, ∃ a : A, k0 g = a * E) ∧
  ∀ g ∈ Dl, ∀ m : M, k0 g • m = ((ℓ : O) ^ e' * δO * u g) • m

def StatCompColK : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [Algebra ℤ_[ℓ] O]
    (A T' G : Type) [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (P : Type) [AddCommGroup P] [Module A P] [Module O P] [SMulCommClass A O P]
    [Module ℤ_[ℓ] P] [IsScalarTower ℤ_[ℓ] O P]
    (L : Type) [AddCommGroup L] [Module A L] [Module O L] [SMulCommClass A O L]
    [Module ℤ_[ℓ] L] [IsScalarTower ℤ_[ℓ] O L]
    (r : G →* A) (χ : G →* T'ˣ) (Dl : Subgroup G) (inc : P →ₗ[A] A) (v₁ : L) (ev : P →ₗ[O] L)
    (hev : ∀ p, ev p = inc p • v₁), Function.Surjective ev →
    ∀ (Hf₁ : Submodule O (H1z (resRep (uRep O (M := P) r χ) Dl)))
      (Hf₂ : Submodule O (H1z (resRep (uRep O (M := L) r χ) Dl))) (e' j : ℕ)
      (κ : Fin j → G → L) (κz : Fin j → coZ1s (resRep (uRep O (M := L) r χ) Dl)),
    (∀ a (g : Dl), (κz a : Dl → L) g = κ a g) → (∀ a, Submodule.mkQ _ (κz a) ∈ Hf₂) →
    LiftSrcO ℓ Hf₁ Hf₂ (mapH1 _ _ ev (ev_equiv r χ Dl inc v₁ ev hev)) e' →
    ∃ Kc : Fin j → G → A, SpecK r χ Dl inc v₁ Hf₁ ℓ e' κ Kc

def StatCompColk : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [Algebra ℤ_[ℓ] O]
    (A T' G : Type) [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (P : Type) [AddCommGroup P] [Module A P] [Module O P] [SMulCommClass A O P]
    [Module ℤ_[ℓ] P] [IsScalarTower ℤ_[ℓ] O P]
    (M : Type) [AddCommGroup M] [Module A M] [Module O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (δO : O) (Dl : Subgroup G) (inc : P →ₗ[A] A)
    (ev : P →ₗ[O] ↥(Ideal.span {δO})),
    (∀ p, ∃ a : A, inc p = a * E) → (∀ p (m : M), inc p • m = ((ev p : ↥(Ideal.span {δO})) : O) • m) →
    ∀ (hev : ∀ g p, ev (uElt r χ g • p) = ev p), Function.Surjective ev →
    ∀ (Hf₁ : Submodule O (H1z (resRep (uRep O (M := P) r χ) Dl)))
      (Hf₂ : Submodule O (H1z (Representation.trivial O Dl ↥(Ideal.span {δO})))) (e' : ℕ)
      (u : G → O) (uz : coZ1s (Representation.trivial O Dl ↥(Ideal.span {δO}))),
    (∀ g : Dl, (((uz : Dl → ↥(Ideal.span {δO})) g : ↥(Ideal.span {δO})) : O) = δO * u g) →
    Submodule.mkQ _ uz ∈ Hf₂ →
    LiftSrcO ℓ Hf₁ Hf₂ (mapH1 _ _ ev (ev_equiv_triv r χ Dl ev hev)) e' →
    ∃ k0 : G → A, Speck M r χ E δO Dl inc Hf₁ ℓ e' u k0

def StatCompRow : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O]
    (H₁ Cs : Type) [AddCommGroup H₁] [Module O H₁] [Module ℤ_[ℓ] H₁] [IsScalarTower ℤ_[ℓ] O H₁]
    [AddCommGroup Cs] [Module O Cs] [Module ℤ_[ℓ] Cs] [IsScalarTower ℤ_[ℓ] O Cs]
    (Hf₁ : Submodule O H₁) (Fs : Submodule O Cs) [Module.Finite O Fs] (g : H₁ →ₗ[O] Cs) (e' : ℕ),
    LiftSrcO ℓ Hf₁ Fs g e' →
    Module.length O (Fs ⧸ (Hf₁.map g).comap Fs.subtype) ≤
      (Module.finrank O Fs : ℕ∞) * ((e' : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})) +
        Module.length O (Submodule.torsion O Fs)

def StatCompLoc : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O A HV HT' HV' : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[ℓ] O]
    [AddCommGroup A] [Module O A] [AddCommGroup HV] [Module O HV]
    [AddCommGroup HT'] [Module O HT'] [Module.Finite O HT'] [Module ℤ_[ℓ] HT']
    [IsScalarTower ℤ_[ℓ] O HT']
    [AddCommGroup HV'] [Module O HV'] [Module.IsTorsionFree O HV']
    (q : HV →ₗ[O] A) (j' : HT' →ₗ[O] HV') (pr : A →ₗ[O] HT' →ₗ[O] KO O)
    (HfV : Submodule O HV) (HfV' : Submodule O HV') (e' d : ℕ)
    (N : Submodule O (Fin d → KO O)) (δ : N →ₗ[O] HT')
    (ι₁ ι₂ : Type) (P : ι₁ → LOC.DirectPush O A HV q) (Q : ι₂ → LOC.DualPush O A HT' pr)
    [∀ i, Module ℤ_[ℓ] (P i).HY] [∀ i, IsScalarTower ℤ_[ℓ] O (P i).HY]
    [∀ i, Module ℤ_[ℓ] (P i).HL] [∀ i, IsScalarTower ℤ_[ℓ] O (P i).HL]
    [∀ i, Module ℤ_[ℓ] (Q i).HLb] [∀ i, IsScalarTower ℤ_[ℓ] O (Q i).HLb],
    HfV.map q = annih pr (HfV'.comap j') →
    LinearMap.range δ = Submodule.torsion O HT' →
    (∀ i, (P i).Fun HfV ∧ LiftSrcO ℓ (P i).HfL (P i).HfY (P i).p1 e') →
    (∀ i, (Q i).Fun ∧ (Q i).Orth ∧ LiftSrcO ℓ (Q i).HfLb (HfV'.comap j') (Q i).p1 e') →
    (∀ i, ∀ y ∈ (P i).HfY, ((ℓ : O) ^ e') • (P i).φs y ∈ HfV.map q) ∧
    (∀ i, ∀ y ∈ (Q i).HfY, ((ℓ : O) ^ e') • (Q i).φs y ∈ HfV.map q) ∧
    Module.length O (LOC.pushSpan P Q ⧸ (HfV.map q).comap (LOC.pushSpan P Q).subtype) ≤
      ((Module.finrank O ↥(HfV'.comap j') + d : ℕ) : ℕ∞) * ((e' : ℕ∞) * LOC.eO O ℓ)

end Formalism.RepresentationBoundsCohomology.JL

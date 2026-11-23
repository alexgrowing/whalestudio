import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
import Formalism.WachLatticeTwists.CoprimeLiftBounds.WachTwistTheorem

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

def StatCTBMono : Prop :=
  ∀ (ℓ s m e gK : ℕ) (U U' : Finset ℤ), U ⊆ U' → cTB ℓ s m e gK U ≤ cTB ℓ s m e gK U'

def HZeroInvariantsKilled : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] (G : Type) [Group G] (A : Type) [AddCommGroup A]
    [Module O A] (ρA : Representation O G A) (Dw : Subgroup G) (Dat : InvariantsCohomologyData ℓ) (b : Dat.M →+ A)
    (w : ℤ_[ℓ]ˣ) (m : ℕ) (U : Finset ℤ),
    (∀ z : A, (∀ g ∈ Dw, ρA g z = z) → ∃ x, b x = z) → HZeroHypotheses Dat w m U →
    ∀ z : A, (∀ g ∈ Dw, ρA g z = z) → ((ℓ : O) ^ c0 ℓ m U) • z = 0

def BKIn {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {X : Type} [AddCommGroup X] [Module O X] (Hc : Submodule O X)
    {HV Cs HV' : Type}
    [AddCommGroup HV] [Module (FractionRing O) HV] [Module O HV]
    [IsScalarTower O (FractionRing O) HV]
    [AddCommGroup Cs] [Module O Cs]
    [AddCommGroup HV'] [Module (FractionRing O) HV'] [Module O HV']
    [IsScalarTower O (FractionRing O) HV']
    (q : HV →ₗ[O] Hc) (j' : Cs →ₗ[O] HV') (pr : Hc →ₗ[O] Cs →ₗ[O] KO O)
    (pair : HV →ₗ[FractionRing O] HV' →ₗ[FractionRing O] FractionRing O)
    (HfV : Submodule (FractionRing O) HV) (HfV' : Submodule (FractionRing O) HV')
    (F : Submodule O X) (Fs : Submodule O Cs) : Prop :=
  Module.Finite O Cs ∧
  (∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', pair a b = 0) ∧
  (∀ f : HV' →ₗ[FractionRing O] FractionRing O, ∃ a, ∀ b, pair a b = f b) ∧
  (∀ a t, pr (q a) t = Submodule.Quotient.mk (pair a (j' t))) ∧
  (∀ x : Hc, (∀ t, pr x t = 0) → x = 0) ∧
  F = ((HfV.restrictScalars O).map q).map Hc.subtype ∧ Fs = (HfV'.restrictScalars O).comap j'

section Defs
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type*} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]

def InRowRhoNoBK (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) (ε : G →* Oˣ)
    {T₁ T₂ : Type*} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (inc : T₁ →ₗ[O] A) (π : T₁ →ₗ[O] T₂)
    (γ : T₂ →ₗ[O] M →ₗ[O] KO O)
    (Hc : Submodule O (H1z (resRep (uRep O (M := M) r χ) Dw)))
    {Cs : Type*} [AddCommGroup Cs] [Module O Cs] (cls : (Dw → T₂) → Cs)
    (pr : Hc →ₗ[O] Cs →ₗ[O] KO O) (Fs Im : Submodule O Cs) : Prop :=
  ∃ (C₁ : (Dw → T₁) → Prop) (CN2 : (Dw → Dw → Ymod r χ E) → Prop)
    (CN : (Dw → Ymod r χ E) → Prop) (CA : (Dw → A) → Prop) (CP : (Dw → KO O) → Prop),
    (∀ a, C₁ a → CN2 (fun g h => inc (a g) • (uElt r χ (g : G) • yY r χ E (h : G)))) ∧
    (∀ a, C₁ a → CA (fun g => -(inc (a g) * (uElt r χ (g : G) * E)))) ∧
    (∀ (ψ : Ymod r χ E →ₗ[O] KO O) f, CN f → CP (fun g => ψ (f g))) ∧
    (∀ z ∈ characterColumnKernelPairSetVariant (twRep (ε.comp Dw.subtype) (Ymod r χ E)), CN2 z →
      (∃ f, CA f ∧ ∀ g h, ((z g h : Ymod r χ E) : A) =
        ((ε (g : G) : Oˣ) : O) • f h - f (g * h) + f g) →
      ∃ c, CN c ∧ ∀ g h, z g h = ((ε (g : G) : Oˣ) : O) • c h - c (g * h) + c g) ∧
    (∀ (a : Dw → T₁) (b : coZ1s (resRep (uRep O (M := M) r χ) Dw))
      (hb : Submodule.mkQ _ b ∈ Hc), a ∈ characterColumnKernelSet (resRep ρ₁ Dw) → C₁ a →
      (∃ c, CP c ∧ ∀ g h : Dw, γ (π (a g)) (uElt r χ (g : G) • (b : Dw → M) h) =
        ((ε (g : G) : Oˣ) : O) • c h - c (g * h) + c g) →
      pr ⟨Submodule.mkQ _ b, hb⟩ (cls (fun g => π (a g))) = 0) ∧
    (∀ x ∈ Im, ∃ a ∈ characterColumnKernelSet (resRep ρ₁ Dw), C₁ a ∧ x = cls (fun g => π (a g))) ∧
    Im ≤ Fs

def InRhoNoBK (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j e' : ℕ → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
    (k0 : ι → G → A) (ℓ : ℕ) (what₂ : Finset ℕ) (s : ℕ∞)
    {L : Type*} [AddCommGroup L] [Module A L] [Module O L] (tens : L →ₗ[O] KO O →ₗ[O] M) (v₁ : L)
    (κ : ∀ l, Fin (j (colIdx l)) → G → L)
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo : Type*} (Io : Vo → Subgroup G) (ε : G →* Oˣ)
    {T₁ T₂ : Type*} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] A)
    (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O) (lam : M →ₗ[O] KO O)
    {Cs : ℕ → Type*} [∀ w, AddCommGroup (Cs w)] [∀ w, Module O (Cs w)]
    (cls : ∀ w, (D w → T₂) → Cs w) (pr : ∀ w, Hc w →ₗ[O] Cs w →ₗ[O] KO O)
    (Fs Im : ∀ w, Submodule O (Cs w)) : Prop :=
  (∀ (a : A) v x, tens (a • v) x = a • tens v x) ∧
  (∀ m : M, e₁ • m = m → ∃ x, m = tens v₁ x) ∧
  (∀ l a, ∀ g ∈ D (colIdx l), Kc l a g • v₁ = ((ℓ : O) ^ e' (colIdx l)) • κ l a g) ∧
  (∀ l (z : coZ1s (resRep (uRep O (M := M) r χ) (D (colIdx l)))) (x : Fin (j (colIdx l)) → KO O),
    (∀ g : D (colIdx l), (z : D (colIdx l) → M) g = ∑ a, tens (κ l a g) (x a)) →
    Submodule.mkQ _ z ∈ F (colIdx l)) ∧
  (∀ l (x : Fin (j (colIdx l)) → KO O), (fun g : D (colIdx l) => ∑ a, tens (κ l a g) (x a)) ∈
    LinearMap.range (colDO (O := O) (M := M) r χ (D (colIdx l))) → ∀ a, x a = 0) ∧
  (∀ φ, Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ (fun l => D (colIdx l))
    (fun l => j (colIdx l)) Kc k0 φ) ∈ HcG) ∧
  (∀ w ∈ what₂, HcG ≤ (Hc w).comap (resH1 (uRep O (M := M) r χ) (D w))) ∧
  (∀ v, ∀ g ∈ Io v, r g = 1 ∧ χ g = 1) ∧
  (∀ g b, inc (ρ₁ g b) = ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • (inc b * r g⁻¹))) ∧
  IsEquivMap ρ₁ ρ₂ π ∧ (∀ b m, γ (π b) m = lam (inc b • m)) ∧
  (∀ w ∈ what₂, InRowRhoNoBK M r χ E (D w) ε ρ₁ inc π γ (Hc w) (cls w) (pr w) (Fs w) (Im w)) ∧
  Module.length O ↥((HcG ⊓ ⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
    ⨅ w ∈ what₂ ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))) ≤ s

end Defs

def StatInRhoBK : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type*) [Fintype ι]
    [DecidableEq ι] (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j e' : ℕ → ℕ)
    (Kc : ∀ l, Fin (j (colIdx l)) → G → A) (k0 : ι → G → A) (ℓ : ℕ) (what₂ : Finset ℕ) (s : ℕ∞)
    (L : Type*) [AddCommGroup L] [Module A L] [Module O L] (tens : L →ₗ[O] KO O →ₗ[O] M) (v₁ : L)
    (κ : ∀ l, Fin (j (colIdx l)) → G → L)
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    (Vo : Type*) (Io : Vo → Subgroup G) (ε : G →* Oˣ)
    (T₁ T₂ : Type*) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] A)
    (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O) (lam : M →ₗ[O] KO O)
    (Cs : ℕ → Type*) [∀ w, AddCommGroup (Cs w)] [∀ w, Module O (Cs w)]
    (cls : ∀ w, (D w → T₂) → Cs w) (pr : ∀ w, Hc w →ₗ[O] Cs w →ₗ[O] KO O)
    (Fs Im : ∀ w, Submodule O (Cs w)),
    InRhoNoBK M r χ E e₁ δ colIdx D j e' Kc k0 ℓ what₂ s tens v₁ κ HcG Hc F Io ε ρ₁ ρ₂ inc π γ lam
      cls pr Fs Im →
    (∀ w ∈ what₂, F w = (annih (pr w) (Fs w)).map (Hc w).subtype) →
    InRho M r χ E e₁ δ colIdx D j e' Kc k0 ℓ what₂ s tens v₁ κ HcG Hc F Io ε ρ₁ ρ₂ inc π γ lam
      cls pr Fs Im

def WachTwistTheoremFromTorsionBound : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X X' : Type)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (Z : Set X) (p : X' → X) (q : ℕ)
    (b : Fin q → (X' → O)),
    (∀ f' ∈ T', ∃ a : Fin q → (X → O), (∀ k, a k ∈ T) ∧ f' = ∑ k, (a k ∘ p) * b k) →
    (∀ x ∉ Z, ∀ a : Fin q → O, (∀ x', p x' = x → ∑ k, a k * b k x' = 0) → a = 0) →
    ∀ (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
      [IsNoetherian R' R'],
    (∀ (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R'), ∃ f ∈ T', ∀ x',
      algebraMap O (FractionRing O) (f x') =
        (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det) →
    ∀ (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
      [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
      (G : Type) [Group G] (r : G →* R') (χ : G →* Tcˣ) (E e₁ : R') (δ : Tc)
      (ι : Type) [Fintype ι] [DecidableEq ι] (colIdx : ι → ℕ), Function.Injective colIdx →
    ∀ (D : ℕ → Subgroup G) (j e' : ℕ → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → R')
      (k0 : ι → G → R'),
      E * E = algebraMap Tc R' δ * E → e₁ * e₁ = e₁ →
    (∀ x', p x' ∉ Z →
      ∃ δx : FractionRing O, δx ≠ 0 ∧ (∀ v : EvalSp O d R' x', δ • v = δx • v) ∧
      Module.finrank (FractionRing O)
        (LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E)) = 1 ∧
      Module.finrank (FractionRing O)
        (LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') e₁)) = 1 ∧
      (∀ η ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E), η ≠ 0 →
        ∃ g : G, ((((χ g)⁻¹ : Tcˣ) : Tc) • r g) • η ≠ η) ∧
      (∀ l, ∃ L : Submodule (FractionRing O) (D (colIdx l) → EvalSp O d R' x'),
        LinearMap.range (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l))) ≤ L ∧
        (∀ a, ∀ s ∈ LinearMap.range
            (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') e₁),
          (fun g : D (colIdx l) => Kc l a g • s) ∈ L) ∧
        (∀ s ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E),
          (fun g : D (colIdx l) => k0 l g • s) ∈ L) ∧
        Module.rank (FractionRing O)
            (L ⧸ (LinearMap.range
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l)))).comap
              L.subtype) ≤
          (j (colIdx l) + Module.finrank (FractionRing O)
            (LinearMap.ker
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l)))) : ℕ))) →
    ∀ (g₀ : ℕ)
      (n : Fin g₀ → ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0),
      Submodule.span R' (Set.range n) = ⊤ →
    ∀ (π' : X') (ρπ : R' →ₐ[O] Matrix d d O),
      (∀ r : R', (ρπ r).map (algebraMap O (FractionRing O)) = (r : X' → Matrix d d (FractionRing O)) π') →
    ∀ (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1)), (∀ r, (ρπ r).BlockTriangular bl) →
    ∀ (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O),
      (∀ k, Function.Surjective (ρk k)) → (∀ r k, (ρπ r).toSquareBlock bl k = ρk k r) →
      [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] → [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)] →
      [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] → [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)] →
      ((g₀ * ∑ k : Fin (t + 1), Fintype.card {a // bl a = k} : ℕ) : Cardinal) <
        Cardinal.mk (IsLocalRing.ResidueField O) →
      (∀ c : Fin (t + 1), c ≠ 0 → Fintype.card {a // bl a = c} = 1) →
    ∀ (sE : Finset G) (tE : G → Tc) (δO : O) (ℓ : ℕ) [Fact ℓ.Prime] (what₂ qs : Finset ℕ)
      (deg : ℕ → ℕ) (s vhE H0 : ℕ∞) (Sha : ℕ → ℕ∞)
      (uT wT : ℕ → ℤ_[ℓ]ˣ) (sT mT dT : ℕ → ℕ) (UT : ℕ → Finset ℤ),
      E = ∑ g ∈ sE, tE g • r g → (∀ l g, ∃ a : R', k0 l g = a * E) →
    let NNc := ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0
    let cols : Finset ℕ := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let cB : ℕ := cBAll ℓ t what₂ sT mT (fun w => padicValNat ℓ (dT w)) UT
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    let N : ℕ∞ := Fintype.card {a // bl a = 0}
    let h0 : ℕ → ℕ∞ := fun w =>
      Module.length O (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk 0) r χ (D w)))

    ∀ (L : Type) [AddCommGroup L] [Module R' L] [Module O L]
      (tens : L →ₗ[O] KO O →ₗ[O] blockRestrictedRepresentationType bl ρk 0) (v₁ : L) (κ : ∀ l, Fin (j (colIdx l)) → G → L)
      (HcG : ∀ c, Submodule O (H1z (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ)))
      (Hc F : ∀ c w, Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (D w))))
      (Vo VS : Type) (Io : Vo → Subgroup G) (IS : VS → Subgroup G) (ε : G →* Oˣ)
      (T₁ T₂ : Type) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
      (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] R')
      (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O) (lam : blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O)
      (Cs : ℕ → Type) [∀ w, AddCommGroup (Cs w)] [∀ w, Module O (Cs w)]
      (cls : ∀ w, (D w → T₂) → Cs w) (pr : ∀ w, Hc 0 w →ₗ[O] Cs w →ₗ[O] KO O)
      (Fs Im : ∀ w, Submodule O (Cs w))
      (I : ∀ w, Subgroup (D w)) (γQ : ∀ w, D w) (ζ : ℕ → Tc)
      (ζO : ℕ → O) (nQ : ∀ w, D w → ℕ) (u : ι → G → O)
      (HW HV₂ : ℕ → Type) [∀ w, AddCommGroup (HW w)] [∀ w, Module (FractionRing O) (HW w)]
      [∀ w, Module O (HW w)] [∀ w, IsScalarTower O (FractionRing O) (HW w)]
      [∀ w, AddCommGroup (HV₂ w)] [∀ w, Module (FractionRing O) (HV₂ w)]
      [∀ w, Module O (HV₂ w)] [∀ w, IsScalarTower O (FractionRing O) (HV₂ w)]
      (qW : ∀ w, HW w →ₗ[O] Hc 0 w) (jT : ∀ w, Cs w →ₗ[O] HV₂ w)
      (pairW : ∀ w, HW w →ₗ[FractionRing O] HV₂ w →ₗ[FractionRing O] FractionRing O)
      (HfW : ∀ w, Submodule (FractionRing O) (HW w))
      (Hf₂ : ∀ w, Submodule (FractionRing O) (HV₂ w)),

    (∀ m : blockRestrictedRepresentationType bl ρk 0, E • m = 0) → (∀ m : blockRestrictedRepresentationType bl ρk 0, δ • m = δO • m) →
    (∀ m : blockRestrictedRepresentationType bl ρk 0, (∑ g ∈ sE, tE g * ((χ g : Tcˣ) : Tc)) • m = δO • m) →
    Nonempty (↥(LinearMap.range (DistribSMul.toLinearMap O (blockRestrictedRepresentationType bl ρk 0) e₁)) ≃ₗ[O] KO O) →
    InRhoNoBK (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ δ colIdx D j e' Kc k0 ℓ what₂ s tens v₁ κ (HcG 0) (Hc 0) (F 0)
      Io ε ρ₁ ρ₂ inc π γ lam cls pr Fs Im →

    (∀ w ∈ what₂, BKIn (Hc 0 w) (qW w) (jT w) (pr w) (pairW w) (HfW w) (Hf₂ w) (F 0 w) (Fs w)) →

    (∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
      (∀ m : blockRestrictedRepresentationType bl ρk c, e₁ • m = 0) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c, E • m = 0) ∧
      (∀ m : blockRestrictedRepresentationType bl ρk c, δ • m = δO • m) ∧
      (∀ m : blockRestrictedRepresentationType bl ρk c, (∑ g ∈ sE, tE g * ((χ g : Tcˣ) : Tc)) • m = δO • m) ∧
      (∀ w ∈ cols, Module.length O
        (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ (D w))) ≤ H0) ∧
      (∀ w ∈ what₂, RowIn ℓ (blockRestrictedRepresentationType bl ρk c) r χ E (D w) (Hc c w) (F c w) (uT w) (wT w) (sT w) (mT w)
        ((c : ℕ) - 1) (dT w) (UT w) (deg w)) ∧
      InChiRest (blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ colIdx D j Kc k0 what₂ qs
        (Sha ((c : ℕ) - 1)) (HcG c) (Hc c) (F c) Io IS I γQ ζ ζO nQ) →

    (let c1 : Fin (t + 1) := ⟨1, by omega⟩
     (∀ g (m : blockRestrictedRepresentationType bl ρk c1), uElt r χ g • m = m) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c1, e₁ • m = 0) ∧
     (∀ m : blockRestrictedRepresentationType bl ρk c1, E • m = δO • m) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c1, δ • m = δO • m) ∧
     (∀ l, ∀ g ∈ D (colIdx l), ∀ m : blockRestrictedRepresentationType bl ρk c1,
       k0 l g • m = ((ℓ : O) ^ e' (colIdx l) * δO * u l g) • m) ∧
     (∀ l, ∀ g ∈ I (colIdx l), u l (g : G) = 0) ∧ (∀ l, ∃ g ∈ D (colIdx l), u l g = 1) ∧
     (∀ l, unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) (D (colIdx l))) (I (colIdx l)) ≤
       F c1 (colIdx l)) ∧
     (∀ w ∈ what₂, RowIn ℓ (blockRestrictedRepresentationType bl ρk c1) r χ E (D w) (Hc c1 w) (F c1 w) (uT w) (wT w) (sT w) (mT w)
       0 (dT w) (UT w) (deg w)) ∧
     InChiRest (blockRestrictedRepresentationType bl ρk c1) r χ E e₁ δ colIdx D j Kc k0 what₂ qs vhE
       (HcG c1) (Hc c1) (F c1) Io IS I γQ ζ ζO nQ) →
    vcc T Z (p π') ≤
      ∑ w ∈ what₂, Module.length O (Fs w ⧸ (Im w).comap (Fs w).subtype) +
        ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w) + s +
        ∑ e ∈ Finset.Ioo 0 t, Sha e + vhE +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, IsDiscreteValuationRing.addVal O (ζO w - 1)

end Formalism.RepresentationBoundsCohomology.JT

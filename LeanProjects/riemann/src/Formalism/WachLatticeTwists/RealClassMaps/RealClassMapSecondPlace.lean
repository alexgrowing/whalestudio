import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapTheorem
import Formalism.WachLatticeTwists.RealClassMaps.StatClassMapReal

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)

section Defs
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace G]

def InRhoFixReal2 (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (e₁ : A) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j : ℕ → ℕ) (what₂ : Finset ℕ) (s : ℕ∞)
    {L : Type} [AddCommGroup L] [Module A L] [Module O L] [SMulCommClass A O L]
    (tens : L →ₗ[O] KO O →ₗ[O] M) (v₁ : L)
    (κ : ∀ l, Fin (j (colIdx l)) → G → L)
    {V : Type} [AddCommGroup V] [Module A V] [Module O V] [Module (FractionRing O) V]
    (iL : L →ₗ[O] V) (qV : V →ₗ[O] M)
    (Ff : ∀ l, Submodule O (H1z (resRep (uRep O (M := L) r χ) (D (colIdx l)))))
    (κz : ∀ l, Fin (j (colIdx l)) → coZ1s (resRep (uRep O (M := L) r χ) (D (colIdx l))))
    (F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo : Type} (Io : Vo → Subgroup G) (ε : G →* Oˣ)
    {T₁ T₂ : Type} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] A)
    (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O) (lam : M →ₗ[O] KO O) : Prop :=
  (∀ (a : A) v x, tens (a • v) x = a • tens v x) ∧
  (∀ m : M, e₁ • m = m → ∃ x, m = tens v₁ x) ∧
  (∀ l (z : coZ1s (resRep (uRep O (M := M) r χ) (D (colIdx l)))) (x : Fin (j (colIdx l)) → KO O),
    (∀ g : D (colIdx l), (z : D (colIdx l) → M) g = ∑ a, tens (κ l a g) (x a)) →
    Submodule.mkQ _ z ∈ F (colIdx l)) ∧
  ((∀ (a : A) v, iL (a • v) = a • iL v) ∧ (∀ (a : A) v, qV (a • v) = a • qV v) ∧
    (∀ v (x : FractionRing O), tens v (Submodule.Quotient.mk x) = qV (x • iL v)) ∧
    Function.Injective iL ∧ Function.Surjective qV ∧ LinearMap.ker qV = LinearMap.range iL ∧
    (∀ v : V, ∃ c : O, c ≠ 0 ∧ c • v ∈ LinearMap.range iL) ∧
    ∀ l, (∀ a (g : D (colIdx l)), (κz l a : D (colIdx l) → L) g = κ l a g) ∧
      (∀ (c : O) z, c ≠ 0 → c • z ∈ Ff l → z ∈ Ff l) ∧
      (∀ a, Submodule.mkQ _ (κz l a) ∈ Ff l) ∧
      (∀ z ∈ Ff l, ∃ (b : Fin (j (colIdx l)) → O) (c : O), c ≠ 0 ∧
        c • (z - ∑ a, b a • (Submodule.mkQ _ (κz l a) :
          H1z (resRep (uRep O (M := L) r χ) (D (colIdx l))))) = 0) ∧
      (∀ (b : Fin (j (colIdx l)) → O) (c : O), c ≠ 0 →
        c • ∑ a, b a • (Submodule.mkQ _ (κz l a) :
          H1z (resRep (uRep O (M := L) r χ) (D (colIdx l)))) = 0 → b = 0)) ∧
  (∀ v, ∀ g ∈ Io v, r g = 1 ∧ χ g = 1) ∧
  (∀ g b, inc (ρ₁ g b) = ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • (inc b * r g⁻¹))) ∧
  IsEquivMap ρ₁ ρ₂ π ∧ (∀ b m, γ (π b) m = lam (inc b • m)) ∧
  Module.length O ↥((lcH1 (uRep O (M := M) r χ) ⊓ ⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
    ⨅ w ∈ what₂ ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))) ≤ s

def InChiLoc (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (D : ℕ → Subgroup G) (qs : Finset ℕ)
    (F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo VS : Type} (Io : Vo → Subgroup G) (IS : VS → Subgroup G)
    (I : ∀ w, Subgroup (D w)) (γ : ∀ w, D w) (ζ : ℕ → T') (ζO : ℕ → O) (n : ∀ w, D w → ℕ) : Prop :=
  (∀ w ∈ qs, F w = unrH1 (resRep (uRep O (M := M) r χ) (D w)) (I w) ∧ γ w ∈ I w ∧
    (r (γ w : G) - 1) * (r (γ w : G) - algebraMap T' A (ζ w)) = 0 ∧
    ((χ (γ w : G) : T'ˣ) : T') = ζ w ∧
    (∀ g ∈ I w, r (g : G) = r (γ w : G) ^ n w g ∧ χ (g : G) = χ (γ w : G) ^ n w g) ∧
    (∀ g ∈ I w, ∀ m : M, uElt r χ (g : G) • m = m) ∧
    (∀ m : M, r (γ w : G) • m = ζO w • m)) ∧
  (∀ v, ∀ g ∈ Io v, r g = 1 ∧ χ g = 1) ∧
  (∀ v, ∀ g ∈ IS v, ∃ a : A, a * ((r g - algebraMap T' A ((χ g : T'ˣ) : T')) * E) = 0 ∧
    ∀ m : M, a • m = 0 → m = 0)

def InChiFixReal (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (what₂ qs : Finset ℕ) (s : ℕ∞)
    (F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo VS : Type} (Io : Vo → Subgroup G) (IS : VS → Subgroup G)
    (I : ∀ w, Subgroup (D w)) (γ : ∀ w, D w) (ζ : ℕ → T') (ζO : ℕ → O) (n : ∀ w, D w → ℕ) : Prop :=
  InChiLoc M r χ E D qs F Io IS I γ ζ ζO n ∧
  Module.length O ↥((lcH1 (uRep O (M := M) r χ) ⊓ (⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
      ⨅ v, unrH1 (uRep O (M := M) r χ) (IS v)) ⊓
    ⨅ w ∈ what₂ ∪ qs ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))) ≤ s

end Defs

set_option maxHeartbeats 2000000 in

def RealClassMapSecondPlace : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] (X X' : Type)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (Z : Set X) (p : X' → X) (q : ℕ)
    (b : Fin q → (X' → O)),
    (∀ f' ∈ T', ∃ a : Fin q → (X → O), (∀ k, a k ∈ T) ∧ f' = ∑ k, (a k ∘ p) * b k) →
    (∀ x ∉ Z, ∀ a : Fin q → O, (∀ x', p x' = x → ∑ k, a k * b k x' = 0) → a = 0) →
    ∀ (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
      [IsNoetherian R' R'] [TopologicalSpace R'] [IsTopologicalAddGroup R'] [ContinuousConstSMul O R'] [ContinuousMul R'],
    (∀ (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R'), ∃ f ∈ T', ∀ x',
      algebraMap O (FractionRing O) (f x') =
        (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det) →
    ∀ (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
      [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
      (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
      (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) (E e₁ : R') (δ : Tc)
      (ι : Type) [Fintype ι] [DecidableEq ι] (colIdx : ι → ℕ), Function.Injective colIdx →
    ∀ (Aw : ℕ → ValuationSubring Ω) (pl : ℕ → HeightOneSpectrum (𝓞 Ek))
      (Av : HeightOneSpectrum (𝓞 Ek) → ValuationSubring Ω) (j e' : ℕ → ℕ),
      E * E = algebraMap Tc R' δ * E → e₁ * e₁ = e₁ →
    ∀ (π' : X') (ρπ : R' →ₐ[O] Matrix d d O),
      (∀ r : R', (ρπ r).map (algebraMap O (FractionRing O)) = (r : X' → Matrix d d (FractionRing O)) π') →
    ∀ (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1)), (∀ r, (ρπ r).BlockTriangular bl) →
    ∀ (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O),
      (∀ k, Function.Surjective (ρk k)) → (∀ r k, (ρπ r).toSquareBlock bl k = ρk k r) →
      [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] → [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)] →
      [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] → [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)] →
      (∀ c : Fin (t + 1), c ≠ 0 → Fintype.card {a // bl a = c} = 1) →
    ∀ (sE : Finset (Ω ≃ₐ[Ek] Ω)) (tE : (Ω ≃ₐ[Ek] Ω) → Tc) (δO : O) (what₂ qs : Finset ℕ)
      (s H0 : ℕ∞) (Sha : ℕ → ℕ∞)
      (uT wT : ℕ → ℤ_[ℓ]ˣ) (sT mT dT : ℕ → ℕ) (UT : ℕ → Finset ℤ),
      E = ∑ g ∈ sE, tE g • r g →
    let cols : Finset ℕ := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let cB : ℕ := cBAll ℓ t what₂ sT mT (fun w => padicValNat ℓ (dT w)) UT
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    let N : ℕ∞ := Fintype.card {a // bl a = 0}
    let h0 : ℕ → ℕ∞ := fun w =>
      Module.length O (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk 0) r χ ((decs Ek Aw) w)))
    let c1 : Fin (t + 1) := ⟨1, by omega⟩

    ∀ (L : Type) [AddCommGroup L] [Module R' L] [Module O L] [SMulCommClass R' O L]
      [Module ℤ_[ℓ] L] [IsScalarTower ℤ_[ℓ] O L]
      (tens : L →ₗ[O] KO O →ₗ[O] blockRestrictedRepresentationType bl ρk 0) (v₁ : L) (κ : ∀ l, Fin (j (colIdx l)) → (Ω ≃ₐ[Ek] Ω) → L)
      (V : Type) [AddCommGroup V] [Module R' V] [Module O V] [Module (FractionRing O) V]
      [IsScalarTower O (FractionRing O) V] [SMulCommClass R' (FractionRing O) V]
      (iL : L →ₗ[O] V) (qV : V →ₗ[O] blockRestrictedRepresentationType bl ρk 0)
      (Ff : ∀ l, Submodule O (H1z (resRep (uRep O (M := L) r χ) ((decs Ek Aw) (colIdx l)))))
      (κz : ∀ l, Fin (j (colIdx l)) → coZ1s (resRep (uRep O (M := L) r χ) ((decs Ek Aw) (colIdx l))))
      (F : ∀ c w, Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ((decs Ek Aw) w))))
      (Vo VS : Type) (Io : Vo → Subgroup (Ω ≃ₐ[Ek] Ω)) (IS : VS → Subgroup (Ω ≃ₐ[Ek] Ω)) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ)
      (T₁ T₂ : Type) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
      [TopologicalSpace T₁] [IsTopologicalAddGroup T₁] [ContinuousConstSMul O T₁]
      (ρ₁ : Representation O (Ω ≃ₐ[Ek] Ω) T₁) (ρ₂ : Representation O (Ω ≃ₐ[Ek] Ω) T₂) (inc : T₁ →ₗ[O] R')
      (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O) (lam : blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O)

      (VT VT' : ℕ → Type)
      [∀ w, AddCommGroup (VT w)] [∀ w, Module O (VT w)] [∀ w, TopologicalSpace (VT w)]
      [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul O (VT w)]
      [∀ w, Module (FractionRing O) (VT w)] [∀ w, IsScalarTower O (FractionRing O) (VT w)]
      [∀ w, AddCommGroup (VT' w)] [∀ w, Module O (VT' w)] [∀ w, TopologicalSpace (VT' w)]
      [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul O (VT' w)]
      [∀ w, Module (FractionRing O) (VT' w)] [∀ w, IsScalarTower O (FractionRing O) (VT' w)]
      (Dat : ∀ w, LatData O ((decs Ek Aw) w) (VT w) (VT' w))
      (uD : ∀ w, blockRestrictedRepresentationType bl ρk 0 ≃ₗ[O] (VT w ⧸ (Dat w).T))
      (huD : ∀ w g m, uD w (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk 0) r χ) ((decs Ek Aw) w) g m) = (Dat w).ρA g (uD w m))
      (vD : ∀ w, T₂ ≃ₗ[O] (Dat w).T') (hpD : ∀ w, Continuous fun t => vD w (π t))
      (heD : ∀ w g t, vD w (π (resRep ρ₁ ((decs Ek Aw) w) g t)) = (Dat w).ρTl' g (vD w (π t)))
      [∀ w, Module ℤ_[ℓ] (H1 (Dat w).ρTl')] [∀ w, IsScalarTower ℤ_[ℓ] O (H1 (Dat w).ρTl')]

      [∀ w, Module ℤ_[ℓ] (H1 (resRep ρ₁ ((decs Ek Aw) w)))] [∀ w, IsScalarTower ℤ_[ℓ] O (H1 (resRep ρ₁ ((decs Ek Aw) w)))]
      (Fs : ∀ w, Submodule O (H1 (Dat w).ρTl')) (Hf₁ : ∀ w, Submodule O (H1 (resRep ρ₁ ((decs Ek Aw) w))))
      (I : ∀ w, Subgroup ((decs Ek Aw) w)) (γQ : ∀ w, (decs Ek Aw) w) (ζ : ℕ → Tc)
      (ζO : ℕ → O) (nQ : ∀ w, (decs Ek Aw) w → ℕ) (u : ι → (Ω ≃ₐ[Ek] Ω) → O)
      (rr : ℕ → Tc) (gI : (Ω ≃ₐ[Ek] Ω)) (s₀ : ℕ) (u₁ y : Oˣ)

      [∀ w, Module (FractionRing O) (H1 (Dat w).ρT)] [∀ w, IsScalarTower O (FractionRing O) (H1 (Dat w).ρT)]
      [∀ w, Module (FractionRing O) (H1 (Dat w).ρT')] [∀ w, IsScalarTower O (FractionRing O) (H1 (Dat w).ρT')]
      (HfW : ∀ w, Submodule (FractionRing O) (H1 (Dat w).ρT))
      (Hf₂ : ∀ w, Submodule (FractionRing O) (H1 (Dat w).ρT')),

    let gR : ∀ w, H1 (resRep ρ₁ ((decs Ek Aw) w)) →ₗ[O] H1 (Dat w).ρTl' :=
      fun w => gRow (Dat w) (resRep ρ₁ ((decs Ek Aw) w)) π (vD w) (hpD w) (heD w)
    let Im : ∀ w, Submodule O (H1 (Dat w).ρTl') := fun w => (Hf₁ w).map (gR w)

    ∀ (Pe : Type) [AddCommGroup Pe] [Module R' Pe] [Module O Pe] [SMulCommClass R' O Pe]
      [Module ℤ_[ℓ] Pe] [IsScalarTower ℤ_[ℓ] O Pe]
      (ince : Pe →ₗ[R'] R') (eve : Pe →ₗ[O] L) (heve : ∀ a, eve a = ince a • v₁)
      (PE : Type) [AddCommGroup PE] [Module R' PE] [Module O PE] [SMulCommClass R' O PE]
      [Module ℤ_[ℓ] PE] [IsScalarTower ℤ_[ℓ] O PE]
      (incE : PE →ₗ[R'] R') (evE : PE →ₗ[O] ↥(Ideal.span {δO}))
      (hevE : ∀ g a, evE (uElt r χ g • a) = evE a)
      (Hfe₁ : ∀ l : ι, Submodule O (H1z (resRep (uRep O (M := Pe) r χ) ((decs Ek Aw) (colIdx l)))))
      (HfE₁ : ∀ l : ι, Submodule O (H1z (resRep (uRep O (M := PE) r χ) ((decs Ek Aw) (colIdx l)))))
      (HfE₂ : ∀ l : ι,
        Submodule O (H1z (Representation.trivial O ((decs Ek Aw) (colIdx l)) ↥(Ideal.span {δO}))))
      (uz : ∀ l : ι, coZ1s (Representation.trivial O ((decs Ek Aw) (colIdx l)) ↥(Ideal.span {δO}))),

    Function.Injective (algebraMap ℤ_[ℓ] O) → PadicCoeff ℓ O → FracTop O → IsFGTop O R' → IsCycG ℓ ε →
    Continuous inc → (Continuous fun g : (Ω ≃ₐ[Ek] Ω) => uElt r χ g) →
    (∀ v, IsPlaceOver (Av v) v) → (ℓ ≠ 2 ∨ InfinitePlace.nrRealPlaces Ek = 0) →
    1 ≤ s₀ → (ℓ = 2 → 2 ≤ s₀) →
    ((ε gI : Oˣ) : O) - 1 = (ℓ : O) ^ s₀ * (y : O) →
    δ = ∏ i ∈ Finset.Ioo 0 t, (rr 0 - rr i) →
    δO = ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)) →
    (∀ (c : Fin (t + 1)) (i : ℕ), i < t → ∀ m : blockRestrictedRepresentationType bl ρk c,
      rr i • m = ((u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)) • m) →

    Function.Surjective eve → Function.Surjective evE → (∀ a, ∃ c : R', incE a = c * E) →
    (∀ a (m : blockRestrictedRepresentationType bl ρk c1), incE a • m = ((evE a : ↥(Ideal.span {δO})) : O) • m) →

    (∀ l (g : (decs Ek Aw) (colIdx l)),
      (((uz l : (decs Ek Aw) (colIdx l) → ↥(Ideal.span {δO})) g : ↥(Ideal.span {δO})) : O) = δO * u l g) →
    (∀ l, Submodule.mkQ _ (uz l) ∈ HfE₂ l) →

    (∀ l, LiftSrcO ℓ (Hfe₁ l) (Ff l)
      (mapH1 _ _ eve (ev_equiv r χ ((decs Ek Aw) (colIdx l)) ince v₁ eve heve)) (e' (colIdx l))) →
    (∀ l, LiftSrcO ℓ (HfE₁ l) (HfE₂ l)
      (mapH1 _ _ evE (ev_equiv_triv r χ ((decs Ek Aw) (colIdx l)) evE hevE)) (e' (colIdx l))) →

    (∀ x', p x' ∉ Z →
      ∃ δx : FractionRing O, δx ≠ 0 ∧ (∀ v : EvalSp O d R' x', δ • v = δx • v) ∧
      Module.finrank (FractionRing O)
        (LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E)) = 1 ∧
      Module.finrank (FractionRing O)
        (LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') e₁)) = 1 ∧
      (∀ η ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E), η ≠ 0 →
        ∃ g : (Ω ≃ₐ[Ek] Ω), ((((χ g)⁻¹ : Tcˣ) : Tc) • r g) • η ≠ η) ∧
      (∀ l, ∃ Lx : Submodule (FractionRing O) ((decs Ek Aw) (colIdx l) → EvalSp O d R' x'),
        LinearMap.range (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ ((decs Ek Aw) (colIdx l))) ≤ Lx ∧
        (∀ (f : Pe →ₗ[R'] EvalSp O d R' x')
          (z : coZ1s (resRep (uRep O (M := Pe) r χ) ((decs Ek Aw) (colIdx l)))), Submodule.mkQ _ z ∈ Hfe₁ l →
          (fun g : (decs Ek Aw) (colIdx l) => f ((z : (decs Ek Aw) (colIdx l) → Pe) g)) ∈ Lx) ∧
        (∀ (f : PE →ₗ[R'] EvalSp O d R' x')
          (z : coZ1s (resRep (uRep O (M := PE) r χ) ((decs Ek Aw) (colIdx l)))), Submodule.mkQ _ z ∈ HfE₁ l →
          (fun g : (decs Ek Aw) (colIdx l) => f ((z : (decs Ek Aw) (colIdx l) → PE) g)) ∈ Lx) ∧
        Module.rank (FractionRing O)
            (Lx ⧸ (LinearMap.range
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ ((decs Ek Aw) (colIdx l)))).comap
              Lx.subtype) ≤
          (j (colIdx l) + Module.finrank (FractionRing O)
            (LinearMap.ker
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ ((decs Ek Aw) (colIdx l)))) : ℕ))) →

    (∀ m : blockRestrictedRepresentationType bl ρk 0, E • m = 0) →
    (∀ m : blockRestrictedRepresentationType bl ρk 0, (∑ g ∈ sE, tE g * ((χ g : Tcˣ) : Tc)) • m = δO • m) →
    Nonempty (↥(LinearMap.range (DistribSMul.toLinearMap O (blockRestrictedRepresentationType bl ρk 0) e₁)) ≃ₗ[O] KO O) →
    InRhoFixReal2 (blockRestrictedRepresentationType bl ρk 0) r χ e₁ colIdx (decs Ek Aw) j what₂ s tens v₁ κ iL qV Ff κz (F 0)
      Io ε ρ₁ ρ₂ inc π γ lam →

    (∀ w ∈ what₂, (Aw w).valuation (ℓ : Ω) < 1 ∧ IsPlaceOver (Aw w) (pl w) ∧
      (∀ g : (decs Ek Aw) w, (Dat w).ε g = ε g) ∧ RealLat (Dat w) ∧
      (∀ (g : (decs Ek Aw) w) t, vD w (ρ₂ g t) = (Dat w).ρTl' g (vD w t)) ∧
      (∀ t m, γ t m = pairKO (Dat w).bT (Dat w).T (uD w m) (vD w t)) ∧
      (∀ a, a ∈ HfW w ↔ ∀ b ∈ Hf₂ w, cupFG (Dat w) a b = 0) ∧
      F 0 w = (((HfW w).restrictScalars O).map (Dat w).q).map (kRow (Dat w) _ (uD w) (huD w)) ∧
      Fs w = ((Hf₂ w).restrictScalars O).comap (Dat w).j' ∧ Im w ≤ Fs w) →

    (∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
      (∀ m : blockRestrictedRepresentationType bl ρk c, e₁ • m = 0) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c, E • m = 0) ∧
      (∀ m : blockRestrictedRepresentationType bl ρk c, (∑ g ∈ sE, tE g * ((χ g : Tcˣ) : Tc)) • m = δO • m) ∧
      (∀ w ∈ cols, Module.length O
        (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ ((decs Ek Aw) w))) ≤ H0) ∧
      (∀ w ∈ what₂, F c w = ⊥ ∧
        (∀ g ∈ (decs Ek Aw) w, ∀ m : blockRestrictedRepresentationType bl ρk c, uElt r χ g • m = ((((ε g) ^ ((c : ℕ) - 1))⁻¹ : Oˣ) : O) • m) ∧
        RowTB ℓ (blockRestrictedRepresentationType bl ρk c) r χ E ((decs Ek Aw) w) (F c w) (uT w) (wT w) (sT w) (mT w)
          ((c : ℕ) - 1) (dT w) (UT w)) ∧
      InChiFixReal (blockRestrictedRepresentationType bl ρk c) r χ E colIdx (decs Ek Aw) what₂ qs
        (Sha ((c : ℕ) - 1)) (F c) Io IS I γQ ζ ζO nQ) →

    ((∀ g (m : blockRestrictedRepresentationType bl ρk c1), uElt r χ g • m = m) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c1, e₁ • m = 0) ∧
     (∀ m : blockRestrictedRepresentationType bl ρk c1, E • m = δO • m) ∧
     (∀ l, ∀ g ∈ I (colIdx l), u l (g : (Ω ≃ₐ[Ek] Ω)) = 0) ∧ (∀ l, ∃ g ∈ (decs Ek Aw) (colIdx l), u l g = 1) ∧
     (∀ l, unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) (colIdx l))) (I (colIdx l)) ≤
       F c1 (colIdx l)) ∧
     (∀ w ∈ what₂, F c1 w = lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) ⊓
         unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) ((Ine (F := Ek) (Aw w)).subgroupOf ((decs Ek Aw) w)) ∧
       RowTB ℓ (blockRestrictedRepresentationType bl ρk c1) r χ E ((decs Ek Aw) w) (F c1 w) (uT w) (wT w) (sT w) (mT w) 0 (dT w) (UT w)) ∧
     InChiLoc (blockRestrictedRepresentationType bl ρk c1) r χ E (decs Ek Aw) qs (F c1) Io IS I γQ ζ ζO nQ ∧

     (∀ v, (∃ a, Ine (F := Ek) (Av v) ≤ Io a) ∨ (∃ a, Ine (F := Ek) (Av v) ≤ IS a) ∨
        ∃ w ∈ what₂ ∪ qs ∪ univ.image colIdx, ∃ J : Subgroup ((decs Ek Aw) w),
          F c1 w ≤ unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) J ∧
          Ine (F := Ek) (Av v) ≤ J.map ((decs Ek Aw) w).subtype)) →

    (∀ (Kc : ∀ l, Fin (j (colIdx l)) → (Ω ≃ₐ[Ek] Ω) → R') (k0 : ι → (Ω ≃ₐ[Ek] Ω) → R'),
      (∀ l, SpecK r χ ((decs Ek Aw) (colIdx l)) ince v₁ (Hfe₁ l) ℓ (e' (colIdx l)) (κ l) (Kc l)) →
      (∀ l, Speck (blockRestrictedRepresentationType bl ρk c1) r χ E δO ((decs Ek Aw) (colIdx l)) incE (HfE₁ l) ℓ (e' (colIdx l)) (u l)
        (k0 l)) →
      (∃ (g₀ : ℕ)
        (n : Fin g₀ → ColNNJ r χ E e₁ δ (fun l => (decs Ek Aw) (colIdx l)) (fun l => j (colIdx l)) Kc k0),
        Submodule.span R' (Set.range n) = ⊤ ∧
        ((g₀ * ∑ k : Fin (t + 1), Fintype.card {a // bl a = k} : ℕ) : Cardinal) <
          Cardinal.mk (IsLocalRing.ResidueField O)) ∧
      ∀ (c : Fin (t + 1)) φ, Submodule.mkQ _ (colPsi (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ
        (fun l => (decs Ek Aw) (colIdx l)) (fun l => j (colIdx l)) Kc k0 φ) ∈ lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ)) →

    ∀ (conj : ℕ → ℕ) (nlam : ℕ → ℕ) (m : ℕ)
      (cloudC lowsC cloudR lowsR : ∀ w, Fin (nlam w) → Multiset ℤ) (h0C h0R : ℕ → ℕ)
      (V₂ : Type) [AddCommGroup V₂] [Module O V₂] [Module (FractionRing O) V₂]
      [IsScalarTower O (FractionRing O) V₂] (ρV : Representation O (Ω ≃ₐ[Ek] Ω) V₂)
      (ρA : Representation O (Ω ≃ₐ[Ek] Ω) ({a // bl a = 0} → KO O)) (iV : T₂ →ₗ[O] V₂)
      (qA : V₂ →ₗ[O] ({a // bl a = 0} → KO O)) (wD : ∀ w, V₂ ≃ₗ[O] VT' w)
      (τH : ∀ w, Fin (nlam w)) (DatH : ℕ → InvariantsCohomologyData ℓ)
      (bH : ∀ w, (DatH w).M →+ ({a // bl a = 0} → KO O)) (wH : ℕ → ℤ_[ℓ]ˣ) (mH : ℕ → ℕ),

    what₂ = cols.image conj →

    IsLatSeq ρ₂ ρV ρA iV qA →

    (∀ w ∈ cols, (∀ t, wD (conj w) (iV t) = (vD (conj w) t : VT' (conj w))) ∧
      (∀ (g : (decs Ek Aw) (conj w)) x, wD (conj w) (ρV g x) = (Dat (conj w)).ρT' g (wD (conj w) x))) →

    (∀ w ∈ cols, LiftSrcO ℓ (Hf₁ (conj w)) (Fs (conj w)) (gR (conj w)) (e' w)) →

    (∀ w ∈ cols,
      (∀ z : {a // bl a = 0} → KO O, (∀ g ∈ (decs Ek Aw) (conj w), ρA g z = z) → ∃ x, bH w x = z) ∧
      HZeroHypothesesJumps (DatH w) (wH w) (mH w) (cloudR w (τH w) + lowsR w (τH w))) →

    (∀ w ∈ cols, (∀ τ, ∀ u ∈ cloudC w τ, 0 < u) ∧ (∀ τ, Multiset.card (lowsC w τ) ≤ m) ∧
       j w = h0C w + ∑ τ, Formalism.RepresentationBoundsCohomology.negCount (cloudC w τ + lowsC w τ) ∧ h0C w = 0) →

    (∀ w ∈ cols, (∀ τ, ∀ u ∈ cloudR w τ, u < 0) ∧ (∀ τ, Multiset.card (lowsR w τ) ≤ m) ∧
       Module.Finite (FractionRing O) (Hf₂ (conj w)) ∧
       Module.finrank (FractionRing O) (Hf₂ (conj w)) =
         h0R w + ∑ τ, Formalism.RepresentationBoundsCohomology.negCount ((cloudR w τ + lowsR w τ).map (fun u => -u - 1)) ∧
       h0R w = 0) →
    (∀ w ∈ cols, j w ≤ nlam w * m) ∧
    (∀ w ∈ cols, Module.finrank (FractionRing O) (Hf₂ (conj w)) ≤ nlam w * m) ∧
    (∀ w ∈ cols,
      (∑ τ, Formalism.RepresentationBoundsCohomology.negCount ((cloudR w τ + lowsR w τ).map (fun u => -u - 1))) =
        (∑ τ, Formalism.RepresentationBoundsCohomology.negCount (cloudC w τ + lowsC w τ)) →
      Module.finrank (FractionRing O) (Hf₂ (conj w)) = j w) ∧
    (∀ w ∈ cols, Module.length O (Fs (conj w) ⧸ (Im (conj w)).comap (Fs (conj w)).subtype) ≤
      ((Module.finrank (FractionRing O) (Hf₂ (conj w)) : ℕ) : ℕ∞) * ((e' w : ℕ∞) * eO) +
        N * ((c0 ℓ (mH w) (jumpsDualTwist (cloudR w (τH w) + lowsR w (τH w))) : ℕ∞) * eO)) ∧
    (∀ w ∈ cols, Module.length O (Fs (conj w) ⧸ (Im (conj w)).comap (Fs (conj w)).subtype) ≤
      ((nlam w * m : ℕ) : ℕ∞) * ((e' w : ℕ∞) * eO) +
        N * ((c0 ℓ (mH w) (jumpsDualTwist (cloudR w (τH w) + lowsR w (τH w))) : ℕ∞) * eO)) ∧
    (vcc T Z (p π') ≤
      ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ +
          h0 w + ((Module.finrank (FractionRing O) (Hf₂ (conj w)) : ℕ) : ℕ∞) * ((e' w : ℕ∞) * eO) +
          N * ((c0 ℓ (mH w) (jumpsDualTwist (cloudR w (τH w) + lowsR w (τH w))) : ℕ∞) * eO)) + s +
        ∑ e ∈ Finset.Ioo 0 t, Sha e + eO * (padicValNat ℓ (classNumber Ek) : ℕ∞) +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((locDeg (pl w) : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, IsDiscreteValuationRing.addVal O (ζO w - 1)) ∧
    (vcc T Z (p π') ≤
      ∑ w ∈ cols, (eO * (e' w : ℕ∞) + ((nlam w * m : ℕ) : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ +
          h0 w + ((nlam w * m : ℕ) : ℕ∞) * ((e' w : ℕ∞) * eO) +
          N * ((c0 ℓ (mH w) (jumpsDualTwist (cloudR w (τH w) + lowsR w (τH w))) : ℕ∞) * eO)) + s +
        ∑ e ∈ Finset.Ioo 0 t, Sha e + eO * (padicValNat ℓ (classNumber Ek) : ℕ∞) +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((locDeg (pl w) : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, IsDiscreteValuationRing.addVal O (ζO w - 1)) ∧
    vδ = eO * ((∑ i ∈ Finset.Ioo 0 t, (s₀ + padicValNat ℓ i) : ℕ) : ℕ∞) ∧
    vδ ≤ eO * ((t * s₀ + padicValNat ℓ t.factorial : ℕ) : ℕ∞)

end Formalism.RepresentationBoundsCohomology.FIN

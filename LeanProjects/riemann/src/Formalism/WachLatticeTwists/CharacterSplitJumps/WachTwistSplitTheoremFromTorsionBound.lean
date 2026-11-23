import Formalism.WachLatticeTwists.CharacterSplitJumps.WachTwistTheoremFromTorsionBound
import Formalism.WachLatticeTwists.TorsionKernelSplitting.WachTwistSplitTheoremStatedForm

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JS

def HZeroHypothesesJumps {ℓ : ℕ} [Fact ℓ.Prime] (D : InvariantsCohomologyData ℓ) (w : ℤ_[ℓ]ˣ) (m : ℕ) (J : Multiset ℤ) : Prop :=
  (-1 : ℤ) ∉ J ∧ J ≠ 0 ∧ 1 ≤ m ∧ (ℓ = 2 → 2 ≤ m) ∧ PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m ∧
  D.piece.Inputs w (jumpsDualTwist J) 0 ∧ D.Union ∧ D.Flat ∧ D.LES ∧ D.Inv

def WachTwistSplitTheoremFromTorsionBound : Prop :=
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
      (ζO : ℕ → O) (nQ : ∀ w, D w → ℕ) (u : ι → G → O),

    (∀ m : blockRestrictedRepresentationType bl ρk 0, E • m = 0) → (∀ m : blockRestrictedRepresentationType bl ρk 0, δ • m = δO • m) →
    (∀ m : blockRestrictedRepresentationType bl ρk 0, (∑ g ∈ sE, tE g * ((χ g : Tcˣ) : Tc)) • m = δO • m) →
    Nonempty (↥(LinearMap.range (DistribSMul.toLinearMap O (blockRestrictedRepresentationType bl ρk 0) e₁)) ≃ₗ[O] KO O) →
    InRhoNoBK (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ δ colIdx D j e' Kc k0 ℓ what₂ s tens v₁ κ (HcG 0) (Hc 0) (F 0)
      Io ε ρ₁ ρ₂ inc π γ lam cls pr Fs Im →

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
    ∀ (conj : ℕ → ℕ) (nlam : ℕ → ℕ) (m : ℕ)
      (cloudC lowsC cloudR lowsR : ∀ w, Fin (nlam w) → Multiset ℤ) (h0C h0R : ℕ → ℕ)
      (V : Type) [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
      [IsScalarTower O (FractionRing O) V] (ρV : Representation O G V)
      (ρA : Representation O G ({a // bl a = 0} → KO O)) (iV : T₂ →ₗ[O] V)
      (qV : V →ₗ[O] ({a // bl a = 0} → KO O)) (Zc : ∀ w, Submodule O (D w → T₂))
      (HV : ℕ → Type) [∀ w, AddCommGroup (HV w)] [∀ w, Module O (HV w)]
      [∀ w, Module (FractionRing O) (HV w)] [∀ w, IsScalarTower O (FractionRing O) (HV w)]
      (clsV : ∀ w, (D w → V) → HV w) (jT : ∀ w, Cs w →ₗ[O] HV w)
      (Hf : ∀ w, Submodule (FractionRing O) (HV w))
      (HW : ℕ → Type) [∀ w, AddCommGroup (HW w)] [∀ w, Module (FractionRing O) (HW w)]
      [∀ w, Module O (HW w)] [∀ w, IsScalarTower O (FractionRing O) (HW w)]
      (qW : ∀ w, HW w →ₗ[O] Hc 0 w)
      (pairW : ∀ w, HW w →ₗ[FractionRing O] HV w →ₗ[FractionRing O] FractionRing O)
      (HfW : ∀ w, Submodule (FractionRing O) (HW w))
      (τH : ∀ w, Fin (nlam w)) (DatH : ℕ → InvariantsCohomologyData ℓ)
      (bH : ∀ w, (DatH w).M →+ ({a // bl a = 0} → KO O)) (wH : ℕ → ℤ_[ℓ]ˣ) (mH : ℕ → ℕ),

    (∀ w ∈ what₂, BKIn (Hc 0 w) (qW w) (jT w) (pr w) (pairW w) (HfW w) (Hf w) (F 0 w) (Fs w)) →

    what₂ = cols.image conj →

    IsLatSeq ρ₂ ρV ρA iV qV →

    (∀ w ∈ cols, Module.Finite O (Cs (conj w))) →

    (∀ w ∈ cols, IsClassMap (resRep ρ₂ (D (conj w))) (Zc (conj w)) (cls (conj w)) (Fs (conj w))) →

    (∀ w ∈ cols, ∀ a ∈ Zc (conj w),
       jT (conj w) (cls (conj w) a) = clsV (conj w) (fun g => iV (a g)) ∧
       (clsV (conj w) (fun g => iV (a g)) = 0 →
         (fun g => iV (a g)) ∈ coB1 (resRep ρV (D (conj w))))) →

    (∀ w ∈ cols, ∀ x ∈ Fs (conj w), jT (conj w) x ∈ Hf (conj w)) →

    (∀ w ∈ cols, ∀ x ∈ Fs (conj w), ((ℓ : O) ^ e' w) • x ∈ Im (conj w)) →

    (∀ w ∈ cols,
       (∀ z : {a // bl a = 0} → KO O, (∀ g ∈ D (conj w), ρA g z = z) → ∃ x, bH w x = z) ∧
       HZeroHypothesesJumps (DatH w) (wH w) (mH w) (cloudR w (τH w) + lowsR w (τH w))) →

    (∀ w ∈ cols, (∀ τ, ∀ u ∈ cloudC w τ, 0 < u) ∧ (∀ τ, Multiset.card (lowsC w τ) ≤ m) ∧
       j w = h0C w + ∑ τ, Formalism.RepresentationBoundsCohomology.negCount (cloudC w τ + lowsC w τ) ∧ h0C w = 0) →

    (∀ w ∈ cols, (∀ τ, ∀ u ∈ cloudR w τ, u < 0) ∧ (∀ τ, Multiset.card (lowsR w τ) ≤ m) ∧
       Module.Finite (FractionRing O) (Hf (conj w)) ∧
       Module.finrank (FractionRing O) (Hf (conj w)) =
         h0R w + ∑ τ, Formalism.RepresentationBoundsCohomology.negCount ((cloudR w τ + lowsR w τ).map (fun u => -u - 1)) ∧
       h0R w = 0) →
    (∀ w ∈ cols, j w ≤ nlam w * m) ∧
    (∀ w ∈ cols, Module.length O (Fs (conj w) ⧸ (Im (conj w)).comap (Fs (conj w)).subtype) ≤
      ((nlam w * m : ℕ) : ℕ∞) * ((e' w : ℕ∞) * eO) + N * ((c0 ℓ (mH w) (jumpsDualTwist (cloudR w (τH w) + lowsR w (τH w))) : ℕ∞) * eO)) ∧
    vcc T Z (p π') ≤
      ∑ w ∈ cols, (eO * (e' w : ℕ∞) + ((nlam w * m : ℕ) : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ +
          h0 w + ((nlam w * m : ℕ) : ℕ∞) * ((e' w : ℕ∞) * eO) + N * ((c0 ℓ (mH w) (jumpsDualTwist (cloudR w (τH w) + lowsR w (τH w))) : ℕ∞) * eO)) + s +
        ∑ e ∈ Finset.Ioo 0 t, Sha e + vhE +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, IsDiscreteValuationRing.addVal O (ζO w - 1)

end Formalism.RepresentationBoundsCohomology.JT

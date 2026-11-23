import Formalism.WachLatticeTwists.Statement
import Formalism.CharacterColumnKernels.CharacterColumnKernelEqualityForm

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology

open Formalism.NG

def LengthBoundViaSplitting : Prop :=
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
      [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] →
      ((g₀ * ∑ k : Fin (t + 1), Fintype.card {a // bl a = k} : ℕ) : Cardinal) <
        Cardinal.mk (IsLocalRing.ResidueField O) →
      (∀ c : Fin (t + 1), c ≠ 0 → Fintype.card {a // bl a = c} = 1) →
    ∀ (sE : Finset G) (tE : G → Tc) (δO : O) (ℓ cB : ℕ) (what₂ qs : Finset ℕ) (lenRow : ℕ → ℕ∞)
      (deg : ℕ → ℕ) (vζ : ℕ → ℕ∞) (s vhE H0 : ℕ∞) (Sha : ℕ → ℕ∞),
      E = ∑ g ∈ sE, tE g • r g → (∀ l g, ∃ a : R', k0 l g = a * E) →
    let NNc := ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0
    let cols : Finset ℕ := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    let N : ℕ∞ := Fintype.card {a // bl a = 0}
    let h0 : ℕ → ℕ∞ := fun w =>
      Module.length O (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk 0) r χ (D w)))

    (∀ m : blockRestrictedRepresentationType bl ρk 0, E • m = 0) → (∀ m : blockRestrictedRepresentationType bl ρk 0, δ • m = δO • m) →
    (∀ m : blockRestrictedRepresentationType bl ρk 0, (∑ g ∈ sE, tE g * ((χ g : Tcˣ) : Tc)) • m = δO • m) →
    Nonempty (↥(LinearMap.range (DistribSMul.toLinearMap O (blockRestrictedRepresentationType bl ρk 0) e₁)) ≃ₗ[O] KO O) →
    (∀ l (s : Fin (j (colIdx l)) → blockRestrictedRepresentationType bl ρk 0),
      (∀ a, s a ∈ LinearMap.range (DistribSMul.toLinearMap O (blockRestrictedRepresentationType bl ρk 0) e₁)) →
      (fun g : D (colIdx l) => ∑ a, Kc l a g • s a) ∈
        LinearMap.range (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk 0) r χ (D (colIdx l))) →
      ∀ a, ((ℓ : O) ^ e' (colIdx l)) • s a = 0) →
    (let ρM := uRep O (M := blockRestrictedRepresentationType bl ρk 0) r χ
     let Ψ := colPsi (O := O) (M := blockRestrictedRepresentationType bl ρk 0) r χ E e₁ δ (fun l => D (colIdx l))
       (fun l => j (colIdx l)) Kc k0
     ∃ (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (Q : Submodule O (H1z ρM)),
      (∀ w ∈ what₂, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
        Module.length O (B ⧸ (F w).comap B.subtype) ≤ lenRow w ∧
        ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) ∧
      (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) ∧
      (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) ∧
      Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ s) →

    (∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
      (∀ m : blockRestrictedRepresentationType bl ρk c, e₁ • m = 0) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c, E • m = 0) ∧
      (∀ m : blockRestrictedRepresentationType bl ρk c, δ • m = δO • m) ∧
      (∀ m : blockRestrictedRepresentationType bl ρk c, (∑ g ∈ sE, tE g * ((χ g : Tcˣ) : Tc)) • m = δO • m) ∧
      (∀ w ∈ cols, Module.length O
        (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ (D w))) ≤ H0) ∧
      (let ρM := uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ
       let Ψ := colPsi (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ (fun l => D (colIdx l))
         (fun l => j (colIdx l)) Kc k0
       ∃ (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (Q : Submodule O (H1z ρM)),
        (∀ w ∈ what₂, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
          Module.length O (B ⧸ (F w).comap B.subtype) ≤ eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) ∧
          ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) ∧
        (∀ w ∈ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
          Module.length O (B ⧸ (F w).comap B.subtype) ≤ vζ w ∧
          ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) ∧
        (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) ∧
        (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) ∧
        Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ qs ∪ cols, (F w).comap (resH1 ρM (D w))) ≤
          Sha ((c : ℕ) - 1))) →

    (let c1 : Fin (t + 1) := ⟨1, by omega⟩
     (∀ g (m : blockRestrictedRepresentationType bl ρk c1), uElt r χ g • m = m) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c1, e₁ • m = 0) ∧
     (∀ m : blockRestrictedRepresentationType bl ρk c1, E • m = δO • m) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c1, δ • m = δO • m) ∧
     (∀ l, ∃ g ∈ D (colIdx l), ∃ c : O, IsUnit c ∧
       ∀ m : blockRestrictedRepresentationType bl ρk c1, k0 l g • m = ((ℓ : O) ^ e' (colIdx l) * δO * c) • m) ∧
     (let ρM := uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ
      let Ψ := colPsi (O := O) (M := blockRestrictedRepresentationType bl ρk c1) r χ E e₁ δ (fun l => D (colIdx l))
        (fun l => j (colIdx l)) Kc k0
      ∃ (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (Q : Submodule O (H1z ρM)),
       (∀ w ∈ what₂, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
         Module.length O (B ⧸ (F w).comap B.subtype) ≤ eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) ∧
         ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) ∧
       (∀ w ∈ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
         Module.length O (B ⧸ (F w).comap B.subtype) ≤ vζ w ∧
         ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) ∧
       (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) ∧
       (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) ∧
       Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ qs ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ vhE)) →
    ∀ (conj : ℕ → ℕ) (nlam : ℕ → ℕ) (m : ℕ) (c0 : ℕ → ℕ)
      (Mrow : ℕ → Type) [∀ w, AddCommGroup (Mrow w)] [∀ w, Module O (Mrow w)]
      [∀ w, Module.Finite O (Mrow w)] (Irow : ∀ w, Submodule O (Mrow w))
      (cloudC lowsC cloudR lowsR : ∀ w, Fin (nlam w) → Multiset ℤ) (h0C h0R : ℕ → ℕ),

    what₂ = cols.image conj →

    (∀ w ∈ cols, lenRow (conj w) = Module.length O (Mrow (conj w) ⧸ Irow (conj w))) →

    (∀ w ∈ cols, ∀ x : Mrow (conj w), ((ℓ : O) ^ e' w) • x ∈ Irow (conj w)) →

    (∀ w ∈ cols, ∃ H : Submodule O ({a // bl a = 0} → Formalism.NG.KO O),
       (∀ x ∈ H, ((ℓ : O) ^ c0 w) • x = 0) ∧
       Module.length O (Submodule.torsion O (Mrow (conj w))) ≤ Module.length O H) →

    (∀ w ∈ cols, (∀ τ, ∀ u ∈ cloudC w τ, 0 < u) ∧ (∀ τ, Multiset.card (lowsC w τ) ≤ m) ∧
       j w = h0C w + ∑ τ, Formalism.RepresentationBoundsCohomology.negCount (cloudC w τ + lowsC w τ) ∧ h0C w = 0) →

    (∀ w ∈ cols, (∀ τ, ∀ u ∈ cloudR w τ, u < 0) ∧ (∀ τ, Multiset.card (lowsR w τ) ≤ m) ∧
       Module.finrank O (Mrow (conj w)) =
         h0R w + ∑ τ, Formalism.RepresentationBoundsCohomology.negCount ((cloudR w τ + lowsR w τ).map (fun u => -u - 1)) ∧
       h0R w = 0) →
    (∀ w ∈ cols, j w ≤ nlam w * m) ∧
    (∀ w ∈ cols, lenRow (conj w) ≤
      ((nlam w * m : ℕ) : ℕ∞) * ((e' w : ℕ∞) * eO) + N * ((c0 w : ℕ∞) * eO)) ∧
    vcc T Z (p π') ≤
      ∑ w ∈ cols, (eO * (e' w : ℕ∞) + ((nlam w * m : ℕ) : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ +
          h0 w + ((nlam w * m : ℕ) : ℕ∞) * ((e' w : ℕ∞) * eO) + N * ((c0 w : ℕ∞) * eO)) + s +
        ∑ e ∈ Finset.Ioo 0 t, Sha e + vhE +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, vζ w

end Formalism.RepresentationBoundsCohomology

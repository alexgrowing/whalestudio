import Mathlib
import GroundTheory.ProfiniteCohomology.PoincarePairs.ConeProduct
import GroundTheory.ProfiniteCohomology.PoincarePairs.ConjHomotopyFunCupCochainZeroRight
import GroundTheory.ProfiniteCohomology.PoincarePairs.Natural
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory TensorProduct GroundTheory.GroupCoh

universe u

section Pairing

variable {k G : Type u} [CommRing k] [Group G] (V : Subgroup G) {N₁ N₂ N₃ : Rep.{u} k V}
  (μ : N₁ ⊗ N₂ ⟶ N₃)

def coindPairingFun (f : Rep.coind V.subtype N₁) (g : Rep.coind V.subtype N₂) :
    Rep.coind V.subtype N₃ :=
  ⟨fun y => μ.hom (f.1 y ⊗ₜ[k] g.1 y), fun u y => by
    change μ.hom (f.1 (V.subtype u * y) ⊗ₜ[k] g.1 (V.subtype u * y)) =
      N₃.ρ u (μ.hom (f.1 y ⊗ₜ[k] g.1 y))
    rw [f.2 u y, g.2 u y]
    exact Rep.hom_comm_apply μ u (f.1 y ⊗ₜ[k] g.1 y)⟩

def coindPairing :
    Rep.coind V.subtype N₁ ⊗ Rep.coind V.subtype N₂ ⟶ Rep.coind V.subtype N₃ :=
  Rep.ofHom ⟨TensorProduct.lift (LinearMap.mk₂ k (coindPairingFun V μ)
      (fun f f' g => Subtype.ext (funext fun y => by
        change μ.hom ((f.1 y + f'.1 y) ⊗ₜ[k] g.1 y) =
          μ.hom (f.1 y ⊗ₜ[k] g.1 y) + μ.hom (f'.1 y ⊗ₜ[k] g.1 y)
        rw [add_tmul, map_add]))
      (fun c f g => Subtype.ext (funext fun y => by
        change μ.hom ((c • f.1 y) ⊗ₜ[k] g.1 y) = c • μ.hom (f.1 y ⊗ₜ[k] g.1 y)
        rw [← smul_tmul', map_smul]))
      (fun f g g' => Subtype.ext (funext fun y => by
        change μ.hom (f.1 y ⊗ₜ[k] (g.1 y + g'.1 y)) =
          μ.hom (f.1 y ⊗ₜ[k] g.1 y) + μ.hom (f.1 y ⊗ₜ[k] g'.1 y)
        rw [tmul_add, map_add]))
      (fun c f g => Subtype.ext (funext fun y => by
        change μ.hom (f.1 y ⊗ₜ[k] (c • g.1 y)) = c • μ.hom (f.1 y ⊗ₜ[k] g.1 y)
        rw [tmul_smul, map_smul]))),
    fun σ => TensorProduct.ext' fun f g => rfl⟩

theorem coindPairing_tmul_apply (f : Rep.coind V.subtype N₁) (g : Rep.coind V.subtype N₂) (y : G) :
    ((coindPairing V μ).hom (f ⊗ₜ[k] g : (Rep.coind V.subtype N₁ ⊗ Rep.coind V.subtype N₂ :
      Rep k G))).1 y = μ.hom (f.1 y ⊗ₜ[k] g.1 y) :=
  rfl

end Pairing

section Shapiro

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (V : OpenSubgroup G) {N₁ N₂ N₃ : Rep.{u} k (V : Subgroup G)} [IsDiscreteRep N₁]
  [IsDiscreteRep N₂] [IsDiscreteRep N₃] (μ : N₁ ⊗ N₂ ⟶ N₃)

theorem shapiroCochains_cupPairingCochains {r s n : ℕ} (h : r + s = n)
    (x : (cochainsComplex (Rep.coind (V : Subgroup G).subtype N₁)).X r)
    (z : (cochainsComplex (Rep.coind (V : Subgroup G).subtype N₂)).X s) :
    ((shapiroCochains V N₃).f n).hom (cupPairingCochains (coindPairing (V : Subgroup G) μ) h x z) =
      cupPairingCochains μ h (((shapiroCochains V N₁).f r).hom x)
        (((shapiroCochains V N₂).f s).hom z) := by
  apply cochainOf_injective
  funext σ
  change ((coindPairing (V : Subgroup G) μ).hom (cupCochain h (cochainOf _ x) (cochainOf _ z)
      (⇑(V : Subgroup G).subtype ∘ σ))).1 1 =
    μ.hom (cupCochain h (fun τ => (cochainOf _ x (⇑(V : Subgroup G).subtype ∘ τ)).1 1)
      (fun τ => (cochainOf _ z (⇑(V : Subgroup G).subtype ∘ τ)).1 1) σ)
  rw [cupCochain_apply, cupCochain_apply, coindPairing_tmul_apply, partialProd_comp_monoidHom]
  congr 2
  change (cochainOf _ z _).1 (1 * (V : Subgroup G).subtype (Fin.partialProd σ ⟨r, by omega⟩)) =
    N₂.ρ (Fin.partialProd σ ⟨r, by omega⟩) ((cochainOf _ z _).1 1)
  rw [one_mul, ← mul_one ((V : Subgroup G).subtype _), (cochainOf _ z _).2]
  rfl

end Shapiro

section MackeyFun

variable {k G H : Type u} [CommRing k] [Group G] [Group H] (V : Subgroup G)
  {N₁ N₂ N₃ : Rep.{u} k V} (μ : N₁ ⊗ N₂ ⟶ N₃)

theorem coindPairing_cupCochain_apply (ι : H →* G) (x : G) {r s n : ℕ} (h : r + s = n)
    (F : (Fin r → H) → Rep.coind V.subtype N₁) (E : (Fin s → H) → Rep.coind V.subtype N₂)
    (σ : Fin n → mackeySubgroup V ι x) :
    (((Rep.resFunctor ι).map (coindPairing V μ)).hom
        (cupCochain (G := H) (A := Rep.res ι (Rep.coind V.subtype N₁))
          (B := Rep.res ι (Rep.coind V.subtype N₂)) h F E
          (⇑(mackeySubgroup V ι x).subtype ∘ σ))).1 x =
      ((Rep.resFunctor (mackeyConj V ι x)).map μ).hom
        (cupCochain (G := mackeySubgroup V ι x) (A := Rep.res (mackeyConj V ι x) N₁)
          (B := Rep.res (mackeyConj V ι x) N₂) h
          (fun τ : Fin r → mackeySubgroup V ι x => (F (⇑(mackeySubgroup V ι x).subtype ∘ τ)).1 x)
          (fun τ : Fin s → mackeySubgroup V ι x => (E (⇑(mackeySubgroup V ι x).subtype ∘ τ)).1 x)
          σ) := by
  rw [cupCochain_apply, cupCochain_apply]
  change μ.hom _ = μ.hom _
  congr 2
  rw [partialProd_comp_monoidHom]
  change (E _).1 (x * ι ((mackeySubgroup V ι x).subtype (Fin.partialProd σ ⟨r, by omega⟩))) =
    N₂.ρ (mackeyConj V ι x (Fin.partialProd σ ⟨r, by omega⟩)) ((E _).1 x)
  rw [← (E _).2]
  simp [mul_assoc]
  rfl

end MackeyFun

section Cochains

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)]
  [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)]
  (V : OpenSubgroup G) (φ : ∀ v, Hv v →ₜ* G)

theorem mackeyLocalHomotopy_hom_apply (N : Rep.{u} k (V : Subgroup G)) [IsDiscreteRep N] (m : ℕ)
    (a : (cochainsComplex (Rep.coind (V : Subgroup G).subtype N)).X (m + 1)) (p : MackeyIndex V φ) :
    ((mackeyLocalHomotopy V φ N).hom (m + 1) m).hom a p =
      -((mackeyCochainsMap V (φ p.1) N p.2.out).f m).hom
        (((cochainsMapAlong (φ p.1).toMonoidHom (continuous_toMonoidHom (φ p.1))
          (𝟙 (Rep.res (φ p.1).toMonoidHom (Rep.coind (V : Subgroup G).subtype N)))).f m).hom
          (conjHomotopyLinear (Rep.coind (V : Subgroup G).subtype N) p.2.out⁻¹ m a)) := by
  simp only [mackeyLocalHomotopy, Homotopy.trans_hom, Homotopy.ofEq_hom, Pi.zero_apply, zero_add,
    add_zero]
  simp only [piLiftHomotopy, Homotopy.symm_hom, mackeyHomotopy, conjHomotopy, Homotopy.trans_hom,
    Homotopy.ofEq_hom, Pi.zero_apply, zero_add, Homotopy.compRightId_hom, Homotopy.equivSubZero,
    Equiv.coe_fn_symm_mk, Homotopy.nullHomotopy'_hom, ComplexShape.up_Rel, dite_true,
    ModuleCat.hom_neg, ModuleCat.hom_comp, HomologicalComplex.comp_f]
  rfl

variable {N₁ N₂ N₃ : Rep.{u} k (V : Subgroup G)} [IsDiscreteRep N₁] [IsDiscreteRep N₂]
  [IsDiscreteRep N₃] (μ : N₁ ⊗ N₂ ⟶ N₃)

noncomputable abbrev coindLocalCup : LeibnizPairing
    (piComplex fun v => cochainsComplex
      (Rep.res (φ v).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₁)))
    (piComplex fun v => cochainsComplex
      (Rep.res (φ v).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₂)))
    (piComplex fun v => cochainsComplex
      (Rep.res (φ v).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₃))) :=
  LeibnizPairing.pi fun v =>
    cupLeibniz (A := Rep.res (φ v).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₁))
      (B := Rep.res (φ v).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₂))
      (C := Rep.res (φ v).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₃))
      ((Rep.resFunctor (φ v).toMonoidHom).map (coindPairing (V : Subgroup G) μ))

noncomputable abbrev mackeyLocalCup : LeibnizPairing
    (piComplex fun p => cochainsComplex (mackeyCoeff V φ N₁ p))
    (piComplex fun p => cochainsComplex (mackeyCoeff V φ N₂ p))
    (piComplex fun p => cochainsComplex (mackeyCoeff V φ N₃ p)) :=
  LeibnizPairing.pi fun p =>
    cupLeibniz (A := mackeyCoeff V φ N₁ p) (B := mackeyCoeff V φ N₂ p) (C := mackeyCoeff V φ N₃ p)
      ((Rep.resFunctor (mackeyFamily V φ p).toMonoidHom).map μ)

theorem mackeyLocalMap_pi_cup {r s n : ℕ} (h : r + s = n)
    (y : (piComplex fun v => cochainsComplex
      (Rep.res (φ v).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₁))).X r)
    (w : (piComplex fun v => cochainsComplex
      (Rep.res (φ v).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₂))).X s) :
    ((mackeyLocalMap V φ N₃).f n).hom ((coindLocalCup V φ μ).μ h y w) =
      (mackeyLocalCup V φ μ).μ h (((mackeyLocalMap V φ N₁).f r).hom y)
        (((mackeyLocalMap V φ N₂).f s).hom w) := by
  funext p
  apply cochainOf_injective
  funext σ
  change (((Rep.resFunctor (φ p.1).toMonoidHom).map (coindPairing (V : Subgroup G) μ)).hom
      (cupCochain (G := Hv p.1)
        (A := Rep.res (φ p.1).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₁))
        (B := Rep.res (φ p.1).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₂)) h
        (cochainOf (Rep.res (φ p.1).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₁)) (y p.1))
        (cochainOf (Rep.res (φ p.1).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₂)) (w p.1))
        (⇑(mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out).subtype ∘ σ))).1
        (p.2.out * (φ p.1).toMonoidHom 1) =
    ((Rep.resFunctor (mackeyConj (V : Subgroup G) (φ p.1).toMonoidHom p.2.out)).map μ).hom
      (cupCochain (G := mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out)
        (A := Rep.res (mackeyConj (V : Subgroup G) (φ p.1).toMonoidHom p.2.out) N₁)
        (B := Rep.res (mackeyConj (V : Subgroup G) (φ p.1).toMonoidHom p.2.out) N₂) h
        (fun τ => (cochainOf (Rep.res (φ p.1).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₁))
          (y p.1) (⇑(mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out).subtype ∘ τ)).1
            (p.2.out * (φ p.1).toMonoidHom 1))
        (fun τ => (cochainOf (Rep.res (φ p.1).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₂))
          (w p.1) (⇑(mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out).subtype ∘ τ)).1
            (p.2.out * (φ p.1).toMonoidHom 1)) σ)
  simp only [map_one, mul_one]
  exact coindPairing_cupCochain_apply (V : Subgroup G) μ (φ p.1).toMonoidHom p.2.out h _ _ σ

end Cochains

section PrismFun

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

theorem cupCochain_comp_monoidHom (ι : H →* G) {A B : Rep.{u} k G} {r s n : ℕ} (h : r + s = n)
    (F : (Fin r → G) → A) (E : (Fin s → G) → B) (τ : Fin n → H) :
    cupCochain h F E (⇑ι ∘ τ) =
      cupCochain (G := H) (A := Rep.res ι A) (B := Rep.res ι B) h (fun σ => F (⇑ι ∘ σ))
        (fun σ => E (⇑ι ∘ σ)) τ := by
  rw [cupCochain_apply, cupCochain_apply, partialProd_comp_monoidHom]
  rfl

omit [Group H] in

theorem hom_conjHomotopyFun {X Y : Rep.{u} k G} (P : X ⟶ Y) (g : G) (m : ℕ)
    (K : (Fin (m + 1) → G) → X) (γ : Fin m → G) :
    P.hom (conjHomotopyFun X g m K γ) = conjHomotopyFun Y g m (fun τ => P.hom (K τ)) γ := by
  simp only [conjHomotopyFun, map_sum, map_smul]

omit [Group H] in

theorem cupCochain_neg_left {A B : Rep.{u} k G} {r s n : ℕ} (h : r + s = n)
    (F : (Fin r → G) → A) (E : (Fin s → G) → B) (σ : Fin n → G) :
    cupCochain h (fun τ => -F τ) E σ = -cupCochain h F E σ := by
  rw [cupCochain_apply, cupCochain_apply, neg_tmul]

omit [Group H] in

theorem cupCochain_neg_right {A B : Rep.{u} k G} {r s n : ℕ} (h : r + s = n)
    (F : (Fin r → G) → A) (E : (Fin s → G) → B) (σ : Fin n → G) :
    cupCochain h F (fun τ => -E τ) σ = -cupCochain h F E σ := by
  rw [cupCochain_apply, cupCochain_apply, map_neg, tmul_neg]

variable (V : Subgroup G) {N₁ N₂ N₃ : Rep.{u} k V} (μ : N₁ ⊗ N₂ ⟶ N₃)

theorem coindPairing_cupCochain_comp_apply (ι : H →* G) (x : G) {r s n : ℕ} (h : r + s = n)
    (F : (Fin r → G) → Rep.coind V.subtype N₁) (E : (Fin s → G) → Rep.coind V.subtype N₂)
    (σ : Fin n → mackeySubgroup V ι x) :
    ((coindPairing V μ).hom (cupCochain h F E (⇑ι ∘ ⇑(mackeySubgroup V ι x).subtype ∘ σ))).1 x =
      ((Rep.resFunctor (mackeyConj V ι x)).map μ).hom
        (cupCochain (G := mackeySubgroup V ι x) (A := Rep.res (mackeyConj V ι x) N₁)
          (B := Rep.res (mackeyConj V ι x) N₂) h
          (fun τ => (F (⇑ι ∘ ⇑(mackeySubgroup V ι x).subtype ∘ τ)).1 x)
          (fun τ => (E (⇑ι ∘ ⇑(mackeySubgroup V ι x).subtype ∘ τ)).1 x) σ) := by
  rw [cupCochain_comp_monoidHom]
  exact coindPairing_cupCochain_apply V μ ι x h (fun τ => F (⇑ι ∘ τ)) (fun τ => E (⇑ι ∘ τ)) σ

theorem conjCochainFun_comp_apply (ι : H →* G) (x : G) {n : ℕ}
    (Z : (Fin n → G) → Rep.coind V.subtype N₂) (τ : Fin n → mackeySubgroup V ι x) :
    (conjCochainFun (Rep.coind V.subtype N₂) x⁻¹ Z (⇑ι ∘ ⇑(mackeySubgroup V ι x).subtype ∘ τ)).1 x =
      (Z (⇑V.subtype ∘ ⇑(mackeyConj V ι x) ∘ τ)).1 1 := by
  change (Z fun l => x⁻¹⁻¹ * ι (τ l) * x⁻¹).1 (x * x⁻¹) = _
  rw [mul_inv_cancel, inv_inv]
  rfl

theorem neg_conjHomotopyFun_coindPairing_apply (ι : H →* G) (x : G) {r s m : ℕ}
    (h : r + 1 + (s + 1) = m + 1) (A : (Fin (r + 1) → G) → Rep.coind V.subtype N₁)
    (Z : (Fin (s + 1) → G) → Rep.coind V.subtype N₂) (σ : Fin m → mackeySubgroup V ι x) :
    -(conjHomotopyFun (Rep.coind V.subtype N₃) x⁻¹ m
        (fun γ => (coindPairing V μ).hom (cupCochain h A Z γ))
        (⇑ι ∘ ⇑(mackeySubgroup V ι x).subtype ∘ σ)).1 x =
      ((Rep.resFunctor (mackeyConj V ι x)).map μ).hom
          (cupCochain (G := mackeySubgroup V ι x) (A := Rep.res (mackeyConj V ι x) N₁)
            (B := Rep.res (mackeyConj V ι x) N₂) (show r + (s + 1) = m by omega)
            (fun τ => -(conjHomotopyFun (Rep.coind V.subtype N₁) x⁻¹ r A
              (⇑ι ∘ ⇑(mackeySubgroup V ι x).subtype ∘ τ)).1 x)
            (fun τ => (Z (⇑V.subtype ∘ ⇑(mackeyConj V ι x) ∘ τ)).1 1) σ) +
        (-1 : k) ^ (r + 1) • ((Rep.resFunctor (mackeyConj V ι x)).map μ).hom
          (cupCochain (G := mackeySubgroup V ι x) (A := Rep.res (mackeyConj V ι x) N₁)
            (B := Rep.res (mackeyConj V ι x) N₂) (show r + 1 + s = m by omega)
            (fun τ => (A (⇑ι ∘ ⇑(mackeySubgroup V ι x).subtype ∘ τ)).1 x)
            (fun τ => -(conjHomotopyFun (Rep.coind V.subtype N₂) x⁻¹ s Z
              (⇑ι ∘ ⇑(mackeySubgroup V ι x).subtype ∘ τ)).1 x) σ) := by
  rw [← hom_conjHomotopyFun, conjHomotopyFun_cupCochain, cupCochain_neg_left, cupCochain_neg_right,
    map_neg, map_neg, smul_neg, ← neg_add]
  congr 1
  rw [Pi.add_apply, Pi.smul_apply, map_add, map_smul]
  simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply]
  congr 1
  · rw [coindPairing_cupCochain_comp_apply]
    congr 2
    funext τ
    exact conjCochainFun_comp_apply V ι x Z τ
  · rw [coindPairing_cupCochain_comp_apply]

theorem neg_conjHomotopyFun_coindPairing_apply_zero_left (ι : H →* G) (x : G) {s m : ℕ}
    (h : 0 + (s + 1) = m + 1) (A : (Fin 0 → G) → Rep.coind V.subtype N₁)
    (Z : (Fin (s + 1) → G) → Rep.coind V.subtype N₂) (σ : Fin m → mackeySubgroup V ι x) :
    -(conjHomotopyFun (Rep.coind V.subtype N₃) x⁻¹ m
        (fun γ => (coindPairing V μ).hom (cupCochain h A Z γ))
        (⇑ι ∘ ⇑(mackeySubgroup V ι x).subtype ∘ σ)).1 x =
      ((Rep.resFunctor (mackeyConj V ι x)).map μ).hom
          (cupCochain (G := mackeySubgroup V ι x) (A := Rep.res (mackeyConj V ι x) N₁)
            (B := Rep.res (mackeyConj V ι x) N₂) (show 0 + s = m by omega)
            (fun τ => (A (⇑ι ∘ ⇑(mackeySubgroup V ι x).subtype ∘ τ)).1 x)
            (fun τ => -(conjHomotopyFun (Rep.coind V.subtype N₂) x⁻¹ s Z
              (⇑ι ∘ ⇑(mackeySubgroup V ι x).subtype ∘ τ)).1 x) σ) := by
  rw [← hom_conjHomotopyFun, conjHomotopyFun_cupCochain_zero_left, cupCochain_neg_right, map_neg]
  congr 1
  exact coindPairing_cupCochain_comp_apply V μ ι x _ _ _ σ

theorem neg_conjHomotopyFun_coindPairing_apply_zero_right (ι : H →* G) (x : G) {r m : ℕ}
    (h : r + 1 + 0 = m + 1) (A : (Fin (r + 1) → G) → Rep.coind V.subtype N₁)
    (Z : (Fin 0 → G) → Rep.coind V.subtype N₂) (σ : Fin m → mackeySubgroup V ι x) :
    -(conjHomotopyFun (Rep.coind V.subtype N₃) x⁻¹ m
        (fun γ => (coindPairing V μ).hom (cupCochain h A Z γ))
        (⇑ι ∘ ⇑(mackeySubgroup V ι x).subtype ∘ σ)).1 x =
      ((Rep.resFunctor (mackeyConj V ι x)).map μ).hom
          (cupCochain (G := mackeySubgroup V ι x) (A := Rep.res (mackeyConj V ι x) N₁)
            (B := Rep.res (mackeyConj V ι x) N₂) (show r + 0 = m by omega)
            (fun τ => -(conjHomotopyFun (Rep.coind V.subtype N₁) x⁻¹ r A
              (⇑ι ∘ ⇑(mackeySubgroup V ι x).subtype ∘ τ)).1 x)
            (fun τ => (Z (⇑V.subtype ∘ ⇑(mackeyConj V ι x) ∘ τ)).1 1) σ) := by
  rw [← hom_conjHomotopyFun, conjHomotopyFun_cupCochain_zero_right, cupCochain_neg_left, map_neg]
  congr 1
  rw [coindPairing_cupCochain_comp_apply]
  congr 2
  funext τ
  exact conjCochainFun_comp_apply V ι x Z τ

end PrismFun

section Leibniz

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)]
  [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)]
  (V : OpenSubgroup G) (φ : ∀ v, Hv v →ₜ* G)

theorem mackeyLocalHomotopy_hom_eq (N : Rep.{u} k (V : Subgroup G)) [IsDiscreteRep N] (m : ℕ)
    (a : (cochainsComplex (Rep.coind (V : Subgroup G).subtype N)).X (m + 1)) :
    ((mackeyLocalHomotopy V φ N).hom (m + 1) m).hom a =
      (show (piComplex fun p => cochainsComplex (mackeyCoeff V φ N p)).X m from fun p =>
        -((mackeyCochainsMap V (φ p.1) N p.2.out).f m).hom
          (((cochainsMapAlong (φ p.1).toMonoidHom (continuous_toMonoidHom (φ p.1))
            (𝟙 (Rep.res (φ p.1).toMonoidHom (Rep.coind (V : Subgroup G).subtype N)))).f m).hom
            (conjHomotopyLinear (Rep.coind (V : Subgroup G).subtype N) p.2.out⁻¹ m a))) :=
  funext fun p => mackeyLocalHomotopy_hom_apply V φ N m a p

variable {N₁ N₂ N₃ : Rep.{u} k (V : Subgroup G)} [IsDiscreteRep N₁] [IsDiscreteRep N₂]
  [IsDiscreteRep N₃] (μ : N₁ ⊗ N₂ ⟶ N₃)

theorem mackeyLocalHomotopy_cup {r s m : ℕ} (h : r + 1 + (s + 1) = m + 1)
    (a : (cochainsComplex (Rep.coind (V : Subgroup G).subtype N₁)).X (r + 1))
    (z : (cochainsComplex (Rep.coind (V : Subgroup G).subtype N₂)).X (s + 1)) :
    ((mackeyLocalHomotopy V φ N₃).hom (m + 1) m).hom
        (cupPairingCochains (coindPairing (V : Subgroup G) μ) h a z) =
      (mackeyLocalCup V φ μ).μ (show r + (s + 1) = m by omega)
          (((mackeyLocalHomotopy V φ N₁).hom (r + 1) r).hom a)
          (((localRes (mackeyFamily V φ) N₂ (mackeyCoeff V φ N₂) (fun _ => 𝟙 _)).f (s + 1)).hom
            (((shapiroCochains V N₂).f (s + 1)).hom z)) +
        (-1 : k) ^ (r + 1) • (mackeyLocalCup V φ μ).μ (show r + 1 + s = m by omega)
          (((mackeyLocalMap V φ N₁).f (r + 1)).hom
            (((localRes φ (Rep.coind (V : Subgroup G).subtype N₁)
              (fun v => Rep.res (φ v).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₁))
              (fun _ => 𝟙 _)).f (r + 1)).hom a))
          (((mackeyLocalHomotopy V φ N₂).hom (s + 1) s).hom z) := by
  rw [mackeyLocalHomotopy_hom_eq, mackeyLocalHomotopy_hom_eq, mackeyLocalHomotopy_hom_eq]
  funext p
  apply cochainOf_injective
  funext σ
  change -(conjHomotopyFun (Rep.coind (V : Subgroup G).subtype N₃) p.2.out⁻¹ m
      (fun γ => (coindPairing (V : Subgroup G) μ).hom
        (cupCochain h (cochainOf _ a) (cochainOf _ z) γ))
      (⇑(φ p.1).toMonoidHom ∘
        ⇑(mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out).subtype ∘ σ)).1
        (p.2.out * (φ p.1).toMonoidHom 1) =
    ((Rep.resFunctor (mackeyConj (V : Subgroup G) (φ p.1).toMonoidHom p.2.out)).map μ).hom
        (cupCochain (G := mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out)
          (A := Rep.res (mackeyConj (V : Subgroup G) (φ p.1).toMonoidHom p.2.out) N₁)
          (B := Rep.res (mackeyConj (V : Subgroup G) (φ p.1).toMonoidHom p.2.out) N₂)
          (show r + (s + 1) = m by omega)
          (fun τ => -(conjHomotopyFun (Rep.coind (V : Subgroup G).subtype N₁) p.2.out⁻¹ r
            (cochainOf _ a) (⇑(φ p.1).toMonoidHom ∘
              ⇑(mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out).subtype ∘ τ)).1
              (p.2.out * (φ p.1).toMonoidHom 1))
          (fun τ => (cochainOf _ z (⇑(V : Subgroup G).subtype ∘
            ⇑(mackeyConj (V : Subgroup G) (φ p.1).toMonoidHom p.2.out) ∘ τ)).1 1) σ) +
      (-1 : k) ^ (r + 1) •
        ((Rep.resFunctor (mackeyConj (V : Subgroup G) (φ p.1).toMonoidHom p.2.out)).map μ).hom
        (cupCochain (G := mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out)
          (A := Rep.res (mackeyConj (V : Subgroup G) (φ p.1).toMonoidHom p.2.out) N₁)
          (B := Rep.res (mackeyConj (V : Subgroup G) (φ p.1).toMonoidHom p.2.out) N₂)
          (show r + 1 + s = m by omega)
          (fun τ => (cochainOf _ a (⇑(φ p.1).toMonoidHom ∘
            ⇑(mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out).subtype ∘ τ)).1
              (p.2.out * (φ p.1).toMonoidHom 1))
          (fun τ => -(conjHomotopyFun (Rep.coind (V : Subgroup G).subtype N₂) p.2.out⁻¹ s
            (cochainOf _ z) (⇑(φ p.1).toMonoidHom ∘
              ⇑(mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out).subtype ∘ τ)).1
              (p.2.out * (φ p.1).toMonoidHom 1)) σ)
  simp only [map_one, mul_one]
  exact neg_conjHomotopyFun_coindPairing_apply (V : Subgroup G) μ (φ p.1).toMonoidHom p.2.out h
    (cochainOf _ a) (cochainOf _ z) σ

theorem mackeyLocalHomotopy_cup_zero_left {s m : ℕ} (h : 0 + (s + 1) = m + 1)
    (a : (cochainsComplex (Rep.coind (V : Subgroup G).subtype N₁)).X 0)
    (z : (cochainsComplex (Rep.coind (V : Subgroup G).subtype N₂)).X (s + 1)) :
    ((mackeyLocalHomotopy V φ N₃).hom (m + 1) m).hom
        (cupPairingCochains (coindPairing (V : Subgroup G) μ) h a z) =
      (mackeyLocalCup V φ μ).μ (show 0 + s = m by omega)
          (((mackeyLocalMap V φ N₁).f 0).hom
            (((localRes φ (Rep.coind (V : Subgroup G).subtype N₁)
              (fun v => Rep.res (φ v).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₁))
              (fun _ => 𝟙 _)).f 0).hom a))
          (((mackeyLocalHomotopy V φ N₂).hom (s + 1) s).hom z) := by
  rw [mackeyLocalHomotopy_hom_eq, mackeyLocalHomotopy_hom_eq]
  funext p
  apply cochainOf_injective
  funext σ
  change -(conjHomotopyFun (Rep.coind (V : Subgroup G).subtype N₃) p.2.out⁻¹ m
      (fun γ => (coindPairing (V : Subgroup G) μ).hom
        (cupCochain h (cochainOf _ a) (cochainOf _ z) γ))
      (⇑(φ p.1).toMonoidHom ∘
        ⇑(mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out).subtype ∘ σ)).1
        (p.2.out * (φ p.1).toMonoidHom 1) =
    ((Rep.resFunctor (mackeyConj (V : Subgroup G) (φ p.1).toMonoidHom p.2.out)).map μ).hom
        (cupCochain (G := mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out)
          (A := Rep.res (mackeyConj (V : Subgroup G) (φ p.1).toMonoidHom p.2.out) N₁)
          (B := Rep.res (mackeyConj (V : Subgroup G) (φ p.1).toMonoidHom p.2.out) N₂)
          (show 0 + s = m by omega)
          (fun τ => (cochainOf _ a (⇑(φ p.1).toMonoidHom ∘
            ⇑(mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out).subtype ∘ τ)).1
              (p.2.out * (φ p.1).toMonoidHom 1))
          (fun τ => -(conjHomotopyFun (Rep.coind (V : Subgroup G).subtype N₂) p.2.out⁻¹ s
            (cochainOf _ z) (⇑(φ p.1).toMonoidHom ∘
              ⇑(mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out).subtype ∘ τ)).1
              (p.2.out * (φ p.1).toMonoidHom 1)) σ)
  simp only [map_one, mul_one]
  exact neg_conjHomotopyFun_coindPairing_apply_zero_left (V : Subgroup G) μ (φ p.1).toMonoidHom
    p.2.out h (cochainOf _ a) (cochainOf _ z) σ

theorem mackeyLocalHomotopy_cup_zero_right {r m : ℕ} (h : r + 1 + 0 = m + 1)
    (a : (cochainsComplex (Rep.coind (V : Subgroup G).subtype N₁)).X (r + 1))
    (z : (cochainsComplex (Rep.coind (V : Subgroup G).subtype N₂)).X 0) :
    ((mackeyLocalHomotopy V φ N₃).hom (m + 1) m).hom
        (cupPairingCochains (coindPairing (V : Subgroup G) μ) h a z) =
      (mackeyLocalCup V φ μ).μ (show r + 0 = m by omega)
          (((mackeyLocalHomotopy V φ N₁).hom (r + 1) r).hom a)
          (((localRes (mackeyFamily V φ) N₂ (mackeyCoeff V φ N₂) (fun _ => 𝟙 _)).f 0).hom
            (((shapiroCochains V N₂).f 0).hom z)) := by
  rw [mackeyLocalHomotopy_hom_eq, mackeyLocalHomotopy_hom_eq]
  funext p
  apply cochainOf_injective
  funext σ
  change -(conjHomotopyFun (Rep.coind (V : Subgroup G).subtype N₃) p.2.out⁻¹ m
      (fun γ => (coindPairing (V : Subgroup G) μ).hom
        (cupCochain h (cochainOf _ a) (cochainOf _ z) γ))
      (⇑(φ p.1).toMonoidHom ∘
        ⇑(mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out).subtype ∘ σ)).1
        (p.2.out * (φ p.1).toMonoidHom 1) =
    ((Rep.resFunctor (mackeyConj (V : Subgroup G) (φ p.1).toMonoidHom p.2.out)).map μ).hom
        (cupCochain (G := mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out)
          (A := Rep.res (mackeyConj (V : Subgroup G) (φ p.1).toMonoidHom p.2.out) N₁)
          (B := Rep.res (mackeyConj (V : Subgroup G) (φ p.1).toMonoidHom p.2.out) N₂)
          (show r + 0 = m by omega)
          (fun τ => -(conjHomotopyFun (Rep.coind (V : Subgroup G).subtype N₁) p.2.out⁻¹ r
            (cochainOf _ a) (⇑(φ p.1).toMonoidHom ∘
              ⇑(mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out).subtype ∘ τ)).1
              (p.2.out * (φ p.1).toMonoidHom 1))
          (fun τ => (cochainOf _ z (⇑(V : Subgroup G).subtype ∘
            ⇑(mackeyConj (V : Subgroup G) (φ p.1).toMonoidHom p.2.out) ∘ τ)).1 1) σ)
  simp only [map_one, mul_one]
  exact neg_conjHomotopyFun_coindPairing_apply_zero_right (V : Subgroup G) μ (φ p.1).toMonoidHom
    p.2.out h (cochainOf _ a) (cochainOf _ z) σ

theorem mackeyCompactCohomologyIso_compactCupRes {r s n : ℕ} (h : r + s = n)
    (y : compactCohomologyRes φ (Rep.coind (V : Subgroup G).subtype N₁) r)
    (x : cohomology (Rep.coind (V : Subgroup G).subtype N₂) s) :
    (mackeyCompactCohomologyIso V φ N₃ n).hom.hom
        (compactCupRes φ (coindPairing (V : Subgroup G) μ) h y x) =
      compactCupRes (mackeyFamily V φ) μ h ((mackeyCompactCohomologyIso V φ N₁ r).hom.hom y)
        ((shapiroMap V N₂ s).hom x) := by
  have hc := fun {r s n : ℕ} (hh : r + s = n)
      (x₀ : (cochainsComplex (Rep.coind (V : Subgroup G).subtype N₁)).X r)
      (z₀ : (cochainsComplex (Rep.coind (V : Subgroup G).subtype N₂)).X s) =>
    localRes_cupPairingCochains φ (coindPairing (V : Subgroup G) μ)
      (Aᵥ := fun v => Rep.res (φ v).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₁))
      (Bᵥ := fun v => Rep.res (φ v).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₂))
      (Cᵥ := fun v => Rep.res (φ v).toMonoidHom (Rep.coind (V : Subgroup G).subtype N₃))
      (a := fun _ => 𝟙 _) (b := fun _ => 𝟙 _) (c := fun _ => 𝟙 _)
      (fun v => (Rep.resFunctor (φ v).toMonoidHom).map (coindPairing (V : Subgroup G) μ))
      (fun v => resFunctor_map_comp_id (φ v).toMonoidHom _) hh x₀ z₀
  have hc' := fun {r s n : ℕ} (hh : r + s = n) (x₀ : (cochainsComplex N₁).X r)
      (z₀ : (cochainsComplex N₂).X s) =>
    localRes_cupPairingCochains (mackeyFamily V φ) μ
      (Aᵥ := mackeyCoeff V φ N₁) (Bᵥ := mackeyCoeff V φ N₂) (Cᵥ := mackeyCoeff V φ N₃)
      (a := fun _ => 𝟙 _) (b := fun _ => 𝟙 _) (c := fun _ => 𝟙 _)
      (fun p => (Rep.resFunctor (mackeyFamily V φ p).toMonoidHom).map μ)
      (fun p => resFunctor_map_comp_id (mackeyFamily V φ p).toMonoidHom _) hh x₀ z₀
  exact mappingCoconeNat.homologyMap_mapOfHomotopy_coconeLeft (mackeyLocalHomotopy V φ N₁)
    (mackeyLocalHomotopy V φ N₃) (mackeyLocalHomotopy V φ N₂) (coindLocalCup V φ μ)
    (cupLeibniz (coindPairing (V : Subgroup G) μ)) (mackeyLocalCup V φ μ) (cupLeibniz μ) hc hc'
    (shapiroCochains_cupPairingCochains V μ) (mackeyLocalMap_pi_cup V φ μ)
    (mackeyLocalHomotopy_cup V φ μ) (mackeyLocalHomotopy_cup_zero_left V φ μ)
    (mackeyLocalHomotopy_cup_zero_right V φ μ) h y x

end Leibniz

end GroundTheory.ProfCoh

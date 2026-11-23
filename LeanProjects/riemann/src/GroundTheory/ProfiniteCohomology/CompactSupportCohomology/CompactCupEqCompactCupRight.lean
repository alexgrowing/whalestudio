import Mathlib
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.CupLeibniz
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.ConeSymmetry
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology
import GroundTheory.ProfiniteCohomology.PoincareDuality.DeltaPairing
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)

section Left

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)]
  {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}

noncomputable def compactCupLeibniz (μ : A ⊗ B ⟶ C)
    (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v)
    (hμ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ ≫ c v =
      resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μᵥ v) :
    LeibnizPairing (compactCochains φ A Aᵥ a) (cochainsComplex B) (compactCochains φ C Cᵥ c) :=
  LeibnizPairing.coconeLeft (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v))
    (localRes φ B (fun v => Rep.res (φ v).toMonoidHom B) fun _ => 𝟙 _) (cupLeibniz μ)
    (localRes_cupPairingCochains φ μ μᵥ hμ)

noncomputable def compactCup (μ : A ⊗ B ⟶ C)
    (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v)
    (hμ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ ≫ c v =
      resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μᵥ v) {r s n : ℕ} (h : r + s = n) :
    compactCohomology φ A Aᵥ a r →ₗ[k] cohomology B s →ₗ[k] compactCohomology φ C Cᵥ c n :=
  (compactCupLeibniz φ μ μᵥ hμ).homology h

variable (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v)
  (hμ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ ≫ c v =
    resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μᵥ v)

theorem compactCup_localToCompact {r s n : ℕ} (h : r + s = n) (h' : r + 1 + s = n + 1)
    (ξ : ∀ v, cohomology (Aᵥ v) r) (z : cohomology B s) :
    compactCup φ μ μᵥ hμ h' ((localToCompact φ A Aᵥ a r).hom ξ) z =
      (localToCompact φ C Cᵥ c n).hom (fun v => cupPairing (μᵥ v) h (ξ v)
        ((cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) s).hom z)) := by
  change (compactCupLeibniz φ μ μᵥ hμ).homology h'
      ((mappingCoconeNat.homologyδ (localRes φ A Aᵥ a) r).hom
        ((localCohomologyIso Aᵥ r).inv.hom ξ)) z =
    (mappingCoconeNat.homologyδ (localRes φ C Cᵥ c) n).hom
      ((localCohomologyIso Cᵥ n).inv.hom _)
  refine (LeibnizPairing.coconeLeft_homology_homologyδ (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v))
    (localRes φ B (fun v => Rep.res (φ v).toMonoidHom B) fun _ => 𝟙 _) (cupLeibniz μ)
    (localRes_cupPairingCochains φ μ μᵥ hμ) h h' _ z).trans ?_
  congr 1
  apply (ModuleCat.mono_iff_injective (localCohomologyIso Cᵥ n).hom).1 inferInstance
  rw [hom_apply_hom_apply_of_comp_eq (localCohomologyIso Cᵥ n).inv_hom_id]
  funext v
  refine (LeibnizPairing.piHomologyIso_hom_pi_homology (fun v => cupLeibniz (μᵥ v)) h _ _ v).trans ?_
  refine (cupLeibniz_homology (μᵥ v) h _ _).trans ?_
  exact congrArg₂ (fun p q => cupPairing (μᵥ v) h p q)
    (congrFun (hom_apply_hom_apply_of_comp_eq (localCohomologyIso Aᵥ r).inv_hom_id ξ) v)
    (congrFun (ConcreteCategory.congr_hom (homologyMap_piLift_piHomologyIso_hom _
      (fun v => cochainsMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v))
        (𝟙 (Rep.res (φ v).toMonoidHom B))) s) z) v)

end Left

section Right

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Bᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Bᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)]
  {b : ∀ v, Rep.res (φ v).toMonoidHom B ⟶ Bᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}

noncomputable def compactCupRightLeibniz (μ : A ⊗ B ⟶ C)
    (μᵥ' : ∀ v, Rep.res (φ v).toMonoidHom A ⊗ Bᵥ v ⟶ Cᵥ v)
    (hμ' : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ ≫ c v =
      resTensorHom (φ v).toMonoidHom (𝟙 _) (b v) ≫ μᵥ' v) :
    LeibnizPairing (cochainsComplex A) (compactCochains φ B Bᵥ b) (compactCochains φ C Cᵥ c) :=
  LeibnizPairing.coconeRight (LeibnizPairing.pi fun v => cupLeibniz (μᵥ' v))
    (localRes φ A (fun v => Rep.res (φ v).toMonoidHom A) fun _ => 𝟙 _) (cupLeibniz μ)
    (localRes_cupPairingCochains φ μ μᵥ' hμ')

noncomputable def compactCupRight (μ : A ⊗ B ⟶ C)
    (μᵥ' : ∀ v, Rep.res (φ v).toMonoidHom A ⊗ Bᵥ v ⟶ Cᵥ v)
    (hμ' : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ ≫ c v =
      resTensorHom (φ v).toMonoidHom (𝟙 _) (b v) ≫ μᵥ' v) {r s n : ℕ} (h : r + s = n) :
    cohomology A r →ₗ[k] compactCohomology φ B Bᵥ b s →ₗ[k] compactCohomology φ C Cᵥ c n :=
  (compactCupRightLeibniz φ μ μᵥ' hμ').homology h

end Right

section Symmetry

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Aᵥ Bᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Bᵥ v)]
  [∀ v, IsDiscreteRep (Cᵥ v)] {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v}
  {b : ∀ v, Rep.res (φ v).toMonoidHom B ⟶ Bᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
  (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v)
  (μᵥ' : ∀ v, Rep.res (φ v).toMonoidHom A ⊗ Bᵥ v ⟶ Cᵥ v) (μᵥ'' : ∀ v, Aᵥ v ⊗ Bᵥ v ⟶ Cᵥ v)
  (hμ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ ≫ c v =
    resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μᵥ v)
  (hμ' : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ ≫ c v =
    resTensorHom (φ v).toMonoidHom (𝟙 _) (b v) ≫ μᵥ' v)

theorem cupCochain_tensorHom_eq {K : Type u} [Group K] {X Y Y' Z : Rep.{u} k K}
    (ν : X ⊗ Y ⟶ Z) (ν' : X ⊗ Y' ⟶ Z) (β : Y ⟶ Y') (hν : ν = (𝟙 X ⊗ₘ β) ≫ ν') {r s n : ℕ}
    (h : r + s = n) (f : (Fin r → K) → X) (g : (Fin s → K) → Y) (σ : Fin n → K) :
    ν.hom (cupCochain h f g σ) = ν'.hom (cupCochain h f (fun τ => β.hom (g τ)) σ) := by
  subst hν
  exact congrArg ν'.hom (tensorHom_cupCochain (𝟙 X) β h f g σ)

theorem cupCochain_tensorHom_eq' {K : Type u} [Group K] {X X' Y Z : Rep.{u} k K}
    (ν : X ⊗ Y ⟶ Z) (ν' : X' ⊗ Y ⟶ Z) (α : X ⟶ X') (hν : ν = (α ⊗ₘ 𝟙 Y) ≫ ν') {r s n : ℕ}
    (h : r + s = n) (f : (Fin r → K) → X) (g : (Fin s → K) → Y) (σ : Fin n → K) :
    ν.hom (cupCochain h f g σ) = ν'.hom (cupCochain h (fun τ => α.hom (f τ)) g σ) := by
  subst hν
  exact congrArg ν'.hom (tensorHom_cupCochain α (𝟙 Y) h f g σ)

theorem compactCup_eq_compactCupRight (hL : ∀ v, μᵥ v = (𝟙 _ ⊗ₘ b v) ≫ μᵥ'' v)
    (hR : ∀ v, μᵥ' v = (a v ⊗ₘ 𝟙 _) ≫ μᵥ'' v) {r s n : ℕ} (h : r + s = n)
    (x : compactCohomology φ A Aᵥ a r) (y : compactCohomology φ B Bᵥ b s) :
    compactCup φ μ μᵥ hμ h x ((compactToGlobal φ B Bᵥ b s).hom y) =
      compactCupRight φ μ μᵥ' hμ' h ((compactToGlobal φ A Aᵥ a r).hom x) y :=
  LeibnizPairing.coconeLeft_homology_eq_coconeRight_homology (fA := localRes φ A Aᵥ a)
    (fB := localRes φ B Bᵥ b) (fC := localRes φ C Cᵥ c)
    (LeibnizPairing.pi fun v => cupLeibniz (μᵥ'' v))
    (localRes φ A (fun v => Rep.res (φ v).toMonoidHom A) fun _ => 𝟙 _)
    (localRes φ B (fun v => Rep.res (φ v).toMonoidHom B) fun _ => 𝟙 _)
    (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v)) (LeibnizPairing.pi fun v => cupLeibniz (μᵥ' v))
    (fun {_ _ _} h' u y' => funext fun v => cochainOf_injective (funext fun σ =>
      cupCochain_tensorHom_eq (μᵥ v) (μᵥ'' v) (b v) (hL v) h' (cochainOf (Aᵥ v) (u v))
        (fun τ => cochainOf B y' (⇑(φ v).toMonoidHom ∘ τ)) σ))
    (fun {_ _ _} h' x' w => funext fun v => cochainOf_injective (funext fun σ =>
      cupCochain_tensorHom_eq' (μᵥ' v) (μᵥ'' v) (a v) (hR v) h'
        (fun τ => cochainOf A x' (⇑(φ v).toMonoidHom ∘ τ)) (cochainOf (Bᵥ v) (w v)) σ))
    (cupLeibniz μ) (localRes_cupPairingCochains φ μ μᵥ hμ)
    (localRes_cupPairingCochains φ μ μᵥ' hμ') h x y

end Symmetry

section TwoSequences

variable {SA : ShortComplex (Rep.{u} k G)} [IsDiscreteRep SA.X₁] [IsDiscreteRep SA.X₂]
  [IsDiscreteRep SA.X₃] {SAᵥ : ∀ v, ShortComplex (Rep.{u} k (H v))}
  [∀ v, IsDiscreteRep (SAᵥ v).X₁] [∀ v, IsDiscreteRep (SAᵥ v).X₂] [∀ v, IsDiscreteRep (SAᵥ v).X₃]
  (sA : ∀ v, SA.map (Rep.resFunctor (φ v).toMonoidHom) ⟶ SAᵥ v)
  {SB : ShortComplex (Rep.{u} k G)} [IsDiscreteRep SB.X₁] [IsDiscreteRep SB.X₂]
  [IsDiscreteRep SB.X₃] {C : Rep.{u} k G} [IsDiscreteRep C] {Cᵥ : ∀ v, Rep.{u} k (H v)}
  [∀ v, IsDiscreteRep (Cᵥ v)] {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
  (μ₁ : SA.X₁ ⊗ SB.X₃ ⟶ C) (μ₂ : SA.X₂ ⊗ SB.X₂ ⟶ C) (μ₃ : SA.X₃ ⊗ SB.X₁ ⟶ C)
  (μ₁ᵥ : ∀ v, (SAᵥ v).X₁ ⊗ Rep.res (φ v).toMonoidHom SB.X₃ ⟶ Cᵥ v)
  (μ₂ᵥ : ∀ v, (SAᵥ v).X₂ ⊗ Rep.res (φ v).toMonoidHom SB.X₂ ⟶ Cᵥ v)
  (μ₃ᵥ : ∀ v, (SAᵥ v).X₃ ⊗ Rep.res (φ v).toMonoidHom SB.X₁ ⟶ Cᵥ v)
  (hμ₁ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₁ ≫ c v =
    resTensorHom (φ v).toMonoidHom (sA v).τ₁ (𝟙 _) ≫ μ₁ᵥ v)
  (hμ₂ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₂ ≫ c v =
    resTensorHom (φ v).toMonoidHom (sA v).τ₂ (𝟙 _) ≫ μ₂ᵥ v)
  (hμ₃ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₃ ≫ c v =
    resTensorHom (φ v).toMonoidHom (sA v).τ₃ (𝟙 _) ≫ μ₃ᵥ v)

include hμ₂ in

theorem compactCup_compactδ_add_compactCup_δ
    (h₁₂ : (SA.f ⊗ₘ 𝟙 SB.X₂) ≫ μ₂ = (𝟙 SA.X₁ ⊗ₘ SB.g) ≫ μ₁)
    (h₂₃ : (𝟙 SA.X₂ ⊗ₘ SB.f) ≫ μ₂ = (SA.g ⊗ₘ 𝟙 SB.X₁) ≫ μ₃)
    (h₁₂ᵥ : ∀ v, ((SAᵥ v).f ⊗ₘ 𝟙 _) ≫ μ₂ᵥ v =
      (𝟙 _ ⊗ₘ (Rep.resFunctor (φ v).toMonoidHom).map SB.g) ≫ μ₁ᵥ v)
    (h₂₃ᵥ : ∀ v, (𝟙 _ ⊗ₘ (Rep.resFunctor (φ v).toMonoidHom).map SB.f) ≫ μ₂ᵥ v =
      ((SAᵥ v).g ⊗ₘ 𝟙 _) ≫ μ₃ᵥ v)
    (hSA : SA.ShortExact) (hSAᵥ : ∀ v, (SAᵥ v).ShortExact) (hSB : SB.ShortExact) {r s n : ℕ}
    (h₁ : r + 1 + s = n + 1) (h₃ : r + (s + 1) = n + 1)
    (x : compactCohomology φ SA.X₃ (fun v => (SAᵥ v).X₃) (fun v => (sA v).τ₃) r)
    (y : cohomology SB.X₃ s) :
    compactCup φ μ₁ μ₁ᵥ hμ₁ h₁ ((compactδ φ sA hSA hSAᵥ r).hom x) y +
      (-1 : k) ^ r • compactCup φ μ₃ μ₃ᵥ hμ₃ h₃ x ((δ hSB s (s + 1) rfl).hom y) = 0 := by
  refine LeibnizPairing.homology_δ_add_homology_δ
    (SM := mappingCoconeNat.mapShortComplex (localResShortComplex φ SA SAᵥ sA))
    (SN := cochainsShortComplex SB) (compactCupLeibniz φ μ₂ μ₂ᵥ hμ₂)
    (compactCupLeibniz φ μ₁ μ₁ᵥ hμ₁) (compactCupLeibniz φ μ₃ μ₃ᵥ hμ₃) ?_ ?_
    (compactCochains_shortExact φ sA hSA hSAᵥ) (cochainsShortComplex_shortExact hSB) h₁ h₃ x y
  · intro r s n h p y
    revert p
    intro (p : (cochainsComplex SA.X₁).X r ×
      shiftNegOneX (piComplex fun v => cochainsComplex (SAᵥ v).X₁) r)
    obtain ⟨x0, b⟩ := p
    refine Prod.ext ?_ ?_
    · apply cochainOf_injective
      funext σ
      exact cupCochain_pairing_left μ₁ μ₂ h₁₂ h (cochainOf _ x0) (cochainOf _ y) σ
    · cases r with
      | zero => rfl
      | succ r =>
        cases n with
        | zero => rfl
        | succ m =>
          revert b
          intro (b : (piComplex fun v => cochainsComplex (SAᵥ v).X₁).X r)
          refine funext fun v => ?_
          apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_left (S := SAᵥ v)
            (T := SB.map (Rep.resFunctor (φ v).toMonoidHom)) (μ₁ᵥ v) (μ₂ᵥ v) (h₁₂ᵥ v)
            (show r + s = m by omega) (cochainOf _ (b v))
            (fun τ => cochainOf SB.X₂ y (⇑(φ v).toMonoidHom ∘ τ)) σ
  · intro r s n h p y
    revert p
    intro (p : (cochainsComplex SA.X₂).X r ×
      shiftNegOneX (piComplex fun v => cochainsComplex (SAᵥ v).X₂) r)
    obtain ⟨x0, b⟩ := p
    refine Prod.ext ?_ ?_
    · apply cochainOf_injective
      funext σ
      exact cupCochain_pairing_right μ₂ μ₃ h₂₃ h (cochainOf _ x0) (cochainOf _ y) σ
    · cases r with
      | zero => rfl
      | succ r =>
        cases n with
        | zero => rfl
        | succ m =>
          revert b
          intro (b : (piComplex fun v => cochainsComplex (SAᵥ v).X₂).X r)
          refine funext fun v => ?_
          apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_right (S := SAᵥ v)
            (T := SB.map (Rep.resFunctor (φ v).toMonoidHom)) (μ₂ᵥ v) (μ₃ᵥ v) (h₂₃ᵥ v)
            (show r + s = m by omega) (cochainOf _ (b v))
            (fun τ => cochainOf SB.X₁ y (⇑(φ v).toMonoidHom ∘ τ)) σ

end TwoSequences

end GroundTheory.ProfCoh

import Mathlib
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.Pairing
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.HomologyMapPiLiftPiHomologyIsoHom
import GroundTheory.ProfiniteCohomology.CupProducts.Pairing
import GroundTheory.ProfiniteCohomology.CupProducts.Functoriality
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory groupCohomology GroundTheory.GroupCoh

universe u

section Global

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]

noncomputable def cupPairingCochains (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) :
    (cochainsComplex A).X r →ₗ[k] (cochainsComplex B).X s →ₗ[k] (cochainsComplex C).X n :=
  (cupLocallyConstant h).compr₂ ((cochainsMap μ).f n).hom

theorem cochainOf_cupPairingCochains (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n)
    (x : (cochainsComplex A).X r) (y : (cochainsComplex B).X s) :
    cochainOf C (cupPairingCochains μ h x y) =
      fun σ => μ.hom (cupCochain h (cochainOf A x) (cochainOf B y) σ) :=
  rfl

theorem d_cupLocallyConstant {r s n : ℕ} (h : r + s = n) (x : (cochainsComplex A).X r)
    (y : (cochainsComplex B).X s) :
    ((cochainsComplex (A ⊗ B)).d n (n + 1)).hom (cupLocallyConstant h x y) =
      cupLocallyConstant (by omega) (((cochainsComplex A).d r (r + 1)).hom x) y +
        (-1 : k) ^ r • cupLocallyConstant (by omega) x (((cochainsComplex B).d s (s + 1)).hom y) := by
  apply cochainOf_injective
  rw [cochainOf_add, cochainOf_smul]
  exact (cochainOf_d _).trans ((d_cupCochain h _ _).trans (by
    rw [← cochainOf_d, ← cochainOf_d]
    rfl))

noncomputable def cupLeibniz (μ : A ⊗ B ⟶ C) :
    LeibnizPairing (cochainsComplex A) (cochainsComplex B) (cochainsComplex C) where
  μ h := cupPairingCochains μ h
  leibniz {r s n} h x y := by
    change ((cochainsComplex C).d n (n + 1)).hom
        (((cochainsMap μ).f n).hom (cupLocallyConstant h x y)) =
      ((cochainsMap μ).f (n + 1)).hom
          (cupLocallyConstant (by omega) (((cochainsComplex A).d r (r + 1)).hom x) y) +
        (-1 : k) ^ r • ((cochainsMap μ).f (n + 1)).hom
          (cupLocallyConstant (by omega) x (((cochainsComplex B).d s (s + 1)).hom y))
    rw [hom_apply_hom_apply_eq_of_comp_eq ((cochainsMap μ).comm n (n + 1)),
      d_cupLocallyConstant, map_add, map_smul]

theorem cupLeibniz_homology (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) (x : cohomology A r)
    (y : cohomology B s) : (cupLeibniz μ).homology h x y = cupPairing μ h x y := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective _ s y
  refine ((cupLeibniz μ).homology_homologyπ h x y).trans ?_
  refine Eq.trans ?_ (cupPairing_cohomologyπ μ h x y).symm
  congr 1
  apply iCycles_hom_injective
  rw [LeibnizPairing.iCycles_cycles, iCycles_cyclesMap_apply]
  exact congrArg ((cochainsMap μ).f n).hom (cocycleι_cupCocycles h x y).symm

end Global

namespace LeibnizPairing

variable {k : Type u} [CommRing k] {ι : Type u} {K N P : ι → CochainComplex (ModuleCat.{u} k) ℕ}
  (μs : ∀ v, LeibnizPairing (K v) (N v) (P v))

noncomputable def pi : LeibnizPairing (piComplex K) (piComplex N) (piComplex P) where
  μ {r s n} h := LinearMap.mk₂ k
    (fun (x : ∀ v, (K v).X r) (y : ∀ v, (N v).X s) =>
      (show (piComplex P).X n from fun v => (μs v).μ h (x v) (y v)))
    (fun x x' y => funext fun v => LinearMap.map_add₂ _ _ _ _)
    (fun c x y => funext fun v => LinearMap.map_smul₂ _ _ _ _)
    (fun x y y' => funext fun v => map_add _ _ _)
    (fun c x y => funext fun v => map_smul _ _ _)
  leibniz {r s n} h x y := funext fun v => by
    rw [piComplex_d_hom_apply]
    change ((P v).d n (n + 1)).hom ((μs v).μ h (x v) (y v)) =
      (μs v).μ (by omega) (((piComplex K).d r (r + 1)).hom x v) (y v) +
        (-1 : k) ^ r • (μs v).μ (by omega) (x v) (((piComplex N).d s (s + 1)).hom y v)
    rw [piComplex_d_hom_apply, piComplex_d_hom_apply]
    exact (μs v).leibniz h (x v) (y v)

theorem pi_μ_apply {r s n : ℕ} (h : r + s = n) (x : (piComplex K).X r) (y : (piComplex N).X s)
    (v : ι) : (pi μs).μ h x y v = (μs v).μ h (x v) (y v) :=
  rfl

theorem piHomologyIso_hom_pi_homology {r s n : ℕ} (h : r + s = n)
    (x : (piComplex K).homology r) (y : (piComplex N).homology s) (v : ι) :
    (piHomologyIso P n).hom.hom ((pi μs).homology h x y) v =
      (μs v).homology h ((piHomologyIso K r).hom.hom x v) ((piHomologyIso N s).hom.hom y v) := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective _ s y
  rw [piHomologyIso_hom_apply, piHomologyIso_hom_apply, piHomologyIso_hom_apply,
    homology_homologyπ, homologyMap_homologyπ_apply, homologyMap_homologyπ_apply,
    homologyMap_homologyπ_apply, homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, iCycles_cycles, iCycles_cycles, iCycles_cyclesMap_apply,
    iCycles_cyclesMap_apply]
  rfl

end LeibnizPairing

section Local

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Aᵥ Bᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Bᵥ v)]
  [∀ v, IsDiscreteRep (Cᵥ v)] {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v}
  {b : ∀ v, Rep.res (φ v).toMonoidHom B ⟶ Bᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}

theorem localRes_cupPairingCochains (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Bᵥ v ⟶ Cᵥ v)
    (hμ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ ≫ c v =
      resTensorHom (φ v).toMonoidHom (a v) (b v) ≫ μᵥ v)
    {r s n : ℕ} (h : r + s = n) (x : (cochainsComplex A).X r) (z : (cochainsComplex B).X s) :
    ((localRes φ C Cᵥ c).f n).hom (cupPairingCochains μ h x z) =
      (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v)).μ h (((localRes φ A Aᵥ a).f r).hom x)
        (((localRes φ B Bᵥ b).f s).hom z) := by
  funext v
  apply cochainOf_injective
  funext σ
  change (c v).hom (μ.hom (cupCochain h (cochainOf A x) (cochainOf B z) (⇑(φ v).toMonoidHom ∘ σ))) =
    (μᵥ v).hom (cupCochain h (fun τ => (a v).hom (cochainOf A x (⇑(φ v).toMonoidHom ∘ τ)))
      (fun τ => (b v).hom (cochainOf B z (⇑(φ v).toMonoidHom ∘ τ))) σ)
  rw [cupCochain_apply, cupCochain_apply, ← Rep.hom_comm_apply, partialProd_comp_monoidHom]
  exact congrArg (fun F : Rep.res (φ v).toMonoidHom (A ⊗ B) ⟶ Cᵥ v => F.hom
    ((cochainOf A x fun i => (⇑(φ v).toMonoidHom ∘ σ) ⟨i, by omega⟩) ⊗ₜ[k]
      B.ρ ((φ v).toMonoidHom (Fin.partialProd σ ⟨r, by omega⟩))
        (cochainOf B z fun j => (⇑(φ v).toMonoidHom ∘ σ) ⟨r + j, by omega⟩) :
      (A ⊗ B : Rep k G))) (hμ v)

end Local

end GroundTheory.ProfCoh

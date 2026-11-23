import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartUniv

section Jets
open ReciprocityTheory.ChartRestriction.G.Chart

variable {R : Type} [CommRing R]

theorem jetAug_eq (κ : Type) (m : ℕ) : jetAug R κ m = (jetAug R κ 0).comp (jetZeroR R κ m) :=
  jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR]; exact (jetAug_zR (R := R) 0 j).symm

theorem jetZero_zR (κ : Type) (m : ℕ) (j : κ) : jetZeroR R κ m (zR m j) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact Ideal.subset_span ⟨j, rfl⟩)

theorem jetZero_eq (κ : Type) (m : ℕ) : jetZeroR R κ m = (Algebra.ofId R (JetR R κ 0)).comp (jetAug R κ m) :=
  jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR, map_zero, jetZero_zR]

theorem aug_comp_iff {κ κ' : Type} {m : ℕ} (ψ : JetR R κ m →ₐ[R] JetR R κ' m) :
    (jetAug R κ' m).comp ψ = jetAug R κ m ↔ ∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0 := by
  constructor
  · intro h j
    have := AlgHom.congr_fun h (zR m j)
    rw [AlgHom.comp_apply, jetAug_zR] at this
    rw [jetZero_eq, AlgHom.comp_apply, this, map_zero]
  · intro h
    refine jet_ext fun j => ?_
    rw [AlgHom.comp_apply, jetAug_zR, jetAug_eq, AlgHom.comp_apply, h, map_zero]

theorem spMap_id' (A : Type) [CommRing A] [Algebra R A] : spMap (R₀ := R) (AlgHom.id R A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  rw [spMap_left]
  exact Spec.map_id _

def jetRen {κ κ' : Type} (f : κ → κ') (m : ℕ) : JetR R κ m →ₐ[R] JetR R κ' m :=
  jetLift R (RingHom.ker (jetAug R κ' m)) (ker_jetAug_pow κ' m) (fun j => zR m (f j)) (fun j => zR_mem_ker m (f j))

theorem jetRen_zR {κ κ' : Type} (f : κ → κ') (m : ℕ) (j : κ) : jetRen (R := R) f m (zR m j) = zR m (f j) :=
  jetLift_zR _ _ _ _ j

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem univ_all [IsLocalRing R] [Smooth G.hom] {κ : Type} {m : ℕ} (x : sp (R₀ := R) (JetR R κ m) ⟶ G)
    (h0 : spMap (jetZeroR R κ m) ≫ x = 1)
    (hu : ∀ (κ' : Type) (y : sp (R₀ := R) (JetR R κ' m) ⟶ G), spMap (jetZeroR R κ' m) ≫ y = 1 →
      ∃! ψ : JetR R κ m →ₐ[R] JetR R κ' m, (∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0) ∧ y = spMap ψ ≫ x)
    (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (hA : (RingHom.ker aug) ^ (m + 1) = ⊥)
    (y : sp (R₀ := R) A ⟶ G) (hy : spMap aug ≫ y = 1) :
    ∃! ψ : JetR R κ m →ₐ[R] A, aug.comp ψ = jetAug R κ m ∧ y = spMap ψ ≫ x := by
  obtain ⟨n, z, -, hz0, hzu⟩ := univChartLoc G
  have hxa : spMap (jetAug R κ m) ≫ x = 1 := by
    rw [jetAug_eq, ← spMap_comp, Category.assoc, h0, comp_one']
  obtain ⟨α, ⟨ha1, ha2⟩, -⟩ := hzu (JetR R κ m) (jetAug R κ m) m (ker_jetAug_pow κ m) x hxa
  obtain ⟨β, ⟨hb1, hb2⟩, -⟩ := hu (Fin n) (z m) (hz0 m)
  have hb1' := (aug_comp_iff β).2 hb1
  have hab : α.comp β = AlgHom.id R _ := by
    refine (hu κ x h0).unique ⟨(aug_comp_iff _).1 ?_, ?_⟩ ⟨fun j => jetZero_zR κ m j, ?_⟩
    · rw [← AlgHom.comp_assoc, ha1, hb1']
    · rw [← spMap_comp, Category.assoc, ← hb2, ← ha2]
    · rw [spMap_id', Category.id_comp]
  obtain ⟨ψ, ⟨h1, h2⟩, hψ⟩ := hzu A aug m hA y hy
  refine ⟨ψ.comp β, ⟨?_, ?_⟩, ?_⟩
  · rw [← AlgHom.comp_assoc, h1, hb1']
  · rw [← spMap_comp, Category.assoc, ← hb2, ← h2]
  · rintro φ ⟨g1, g2⟩
    have : φ.comp α = ψ := hψ _ ⟨by rw [← AlgHom.comp_assoc, g1, ha1], by
      rw [← spMap_comp, Category.assoc, ← ha2, ← g2]⟩
    rw [← this, AlgHom.comp_assoc, hab, AlgHom.comp_id]

theorem isUnivChart_ren [IsLocalRing R] [Smooth G.hom] {κ : Type} {d : ℕ} (e : κ ≃ Fin d)
    (x : ∀ m, sp (R₀ := R) (JetR R κ m) ⟶ G)
    (ht : ∀ m, spMap (jetTruncR R κ m) ≫ x (m + 1) = x m)
    (h0 : ∀ m, spMap (jetZeroR R κ m) ≫ x m = 1)
    (hu : ∀ (κ' : Type) (m : ℕ) (y : sp (R₀ := R) (JetR R κ' m) ⟶ G), spMap (jetZeroR R κ' m) ≫ y = 1 →
      ∃! ψ : JetR R κ m →ₐ[R] JetR R κ' m, (∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0) ∧ y = spMap ψ ≫ x m) :
    IsUnivChart G d (fun m => spMap (jetRen e m) ≫ x m) := by
  refine ⟨fun m => ?_, fun m => ?_, fun A _ _ aug m hA y hy => ?_⟩
  · have : (jetTruncR R (Fin d) m).comp (jetRen e (m + 1)) = (jetRen e m).comp (jetTruncR R κ m) :=
      jet_ext fun j => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, jetRen_zR]
        exact (jetRen_zR (R := R) e m j).symm
    show _ ≫ _ ≫ _ = _ ≫ _
    rw [← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, ht]
  · have : (jetZeroR R (Fin d) m).comp (jetRen e m) = (jetRen e 0).comp (jetZeroR R κ m) :=
      jet_ext fun j => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, jetRen_zR, jetZero_zR, jetZero_zR, map_zero]
    show _ ≫ _ ≫ _ = _
    rw [← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, h0, comp_one']
  · obtain ⟨ψ, ⟨h1, h2⟩, hψ⟩ := univ_all (x m) (h0 m) (fun κ' => hu κ' m) A aug hA y hy
    have e1 : (jetRen (R := R) e m).comp (jetRen e.symm m) = AlgHom.id R _ :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetRen_zR, e.apply_symm_apply]; rfl
    have e2 : (jetRen (R := R) e.symm m).comp (jetRen e m) = AlgHom.id R _ :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetRen_zR, e.symm_apply_apply]; rfl
    have a1 : (jetAug R κ m).comp (jetRen e.symm m) = jetAug R (Fin d) m :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetAug_zR, jetAug_zR]
    have a2 : (jetAug R (Fin d) m).comp (jetRen e m) = jetAug R κ m :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetAug_zR, jetAug_zR]
    refine ⟨ψ.comp (jetRen e.symm m), ⟨?_, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, h1, a1]
    · show y = _ ≫ _ ≫ _
      rw [← Category.assoc, spMap_comp, AlgHom.comp_assoc, e2, AlgHom.comp_id]
      exact h2
    · rintro φ ⟨g1, g2⟩
      have : φ.comp (jetRen e m) = ψ := hψ _ ⟨by rw [← AlgHom.comp_assoc, g1, a2], by
        rw [← spMap_comp, Category.assoc]; exact g2⟩
      rw [← this, AlgHom.comp_assoc, e1, AlgHom.comp_id]

end Jets

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj

theorem isUnivChart_of_isChartJ : ∀ (T : Type) [CommRing T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∃ x0 : GlobalTheory.JetSer.Fam G (Fin d), Chart.IsUnivChart G d x0 ∧ ∃ ρ : ∀ m, JetR T (Fin 1 × Fin d) m →ₐ[T] Chart.JetR T (Fin d) m, (∀ m j, ρ m (zR m ((0 : Fin 1), j)) = Chart.zR m j) ∧ ∀ m, (x0 m).left = spMap (ρ m : JetR T (Fin 1 × Fin d) m →+* Chart.JetR T (Fin d) m) ≫ (x m).left := by
  intro T _ _ G _ _ hG d F x hx
  haveI := hG
  let e : Fin 1 × Fin d ≃ Fin d := Equiv.uniqueProd (Fin d) (Fin 1)
  refine ⟨fun m => Chart.spMap (jetRen e m) ≫ x m,
    isUnivChart_ren e x hx.trunc hx.zero hx.univ, fun m => jetRen e m, fun m j => jetRen_zR e m _, fun m => rfl⟩

end GlobalTheory.ChartUniv

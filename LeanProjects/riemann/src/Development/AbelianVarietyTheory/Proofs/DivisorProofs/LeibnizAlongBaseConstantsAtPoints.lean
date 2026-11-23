import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldConstFnEqZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat

theorem Heat.acts_const_at_points : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}} (m : G.left ⟶ X) (L : LB X), L.IsLB → ∀ (v : Fin n → TanM (𝟙 (Sp R)) G) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat G m L dd ⇑D) (k : ℕ) (a b : R) (ρ τ ρ' τ' : SecM m L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → gs r z ⊤ (scal G.hom a) * sval ρ r z J = gs r z ⊤ (scal G.hom b) * sval τ r z J) → h.Acts k ρ ρ' → h.Acts k τ τ' → ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → gs r z ⊤ (scal G.hom a) * sval ρ' r z J + gs r z ⊤ (scal G.hom (2 * (k : R) * D a)) * sval ρ r z J = gs r z ⊤ (scal G.hom b) * sval τ' r z J + gs r z ⊤ (scal G.hom (2 * (k : R) * D b)) * sval τ r z J := by
  intro R _ G _ _ n X m L hL v dd hinv D h k a b ρ τ ρ' τ' hpt hρ hτ

  have cTop : ∀ c : R, constFn G.hom ⊤ c = scal G.hom c := fun c => by
    simp only [constFn, Out.scal, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have gsR : ∀ {Z : Scheme.{0}} (r : Z ⟶ G.left) (z : Z) {O O₀ : G.left.Opens} (hle : O ≤ O₀) (hz : r z ∈ O)
      (s : Γ(G.left, O₀)), gs r z O (rsT s O) = gs r z O₀ s := fun r z _ _ hle hz s => by
    rw [GlobalTheory.KS.rsT_of_le hle]; exact gs_res r z hle hz s
  have gsC : ∀ {Z : Scheme.{0}} (r : Z ⟶ G.left) (z : Z) (O : G.left.Opens) (hz : r z ∈ O) (c : R),
      gs r z O (constFn G.hom O c) = gs r z ⊤ (scal G.hom c) := fun r z O hz c => by
    rw [← GlobalTheory.KS.rsT_constFn G.hom (le_top : O ≤ ⊤) c, gsR r z le_top hz, cTop]
  have cMul : ∀ (O : G.left.Opens) (c : R),
      constFn G.hom O (2 * (k : R) * c) = 2 * (k : Γ(G.left, O)) * constFn G.hom O c := fun O c => by
    simp [constFn, map_mul, map_natCast, map_ofNat]
  have hWc : ∀ i, h.W i ≤ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) := fun i => Glue.le_wchart _ (h.le i)

  have leib : ∀ i (c : R) (F : Γ(G.left, h.W i)),
      op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) (constFn G.hom (h.W i) c * F) =
        constFn G.hom (h.W i) c * op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) F +
          constFn G.hom (h.W i) (2 * (k : R) * D c) * F := by
    intro i c F
    have hd := (h.lift i).1.2.1 (h.W i) le_rfl (constFn G.hom (h.W i) c) F
    have hdc := (h.lift i).2 (h.W i) le_rfl c
    have hdd : ∀ a' (f : Γ(G.left, h.W i)), dd a' (h.W i) (constFn G.hom (h.W i) c * f) =
        constFn G.hom (h.W i) c * dd a' (h.W i) f := fun a' f => by
      rw [(hinv a').1.2.1 (h.W i) le_top, IsInv.apply_constFn G (v a') (dd a') (hinv a'), mul_zero, add_zero]
    have hs : ∀ (f : Γ(G.left, h.W i)),
        ∑ a', ∑ b', constFn G.hom (h.W i) (h.Θ a' b') * dd a' (h.W i) (dd b' (h.W i) (constFn G.hom (h.W i) c * f)) =
          constFn G.hom (h.W i) c * ∑ a', ∑ b', constFn G.hom (h.W i) (h.Θ a' b') * dd a' (h.W i) (dd b' (h.W i) f) := by
      intro f
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [hdd, hdd]; ring
    have hs' : ∑ a', constFn G.hom (h.W i) (h.u a') * dd a' (h.W i) (constFn G.hom (h.W i) c * F) =
        constFn G.hom (h.W i) c * ∑ a', constFn G.hom (h.W i) (h.u a') * dd a' (h.W i) F := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [hdd]; ring
    simp only [op]
    rw [hs, hs', hd, hdc, cMul]
    ring

  have onW : ∀ i, constFn G.hom (h.W i) a * rsT (ρ'.f fun _ => h.j i) (h.W i) +
      constFn G.hom (h.W i) (2 * (k : R) * D a) * rsT (ρ.f fun _ => h.j i) (h.W i) =
      constFn G.hom (h.W i) b * rsT (τ'.f fun _ => h.j i) (h.W i) +
      constFn G.hom (h.W i) (2 * (k : R) * D b) * rsT (τ.f fun _ => h.j i) (h.W i) := by
    intro i
    have hA : constFn G.hom (h.W i) a * rsT (ρ.f fun _ => h.j i) (h.W i) =
        constFn G.hom (h.W i) b * rsT (τ.f fun _ => h.j i) (h.W i) := by
      refine fn_ext fun x hx => ?_
      obtain ⟨J, hJ, e⟩ := exists_good L hL x (fun _ : Fin 1 => m) (fun _ => h.j i) (fun _ _ _ => rfl)
        (fun _ => h.le i hx)
      have hp := hpt G.left (𝟙 _) x J hJ
      have s1 : ∀ σ : SecM m L k, sval σ (𝟙 G.left) x J = gs (𝟙 G.left) x (h.W i) (rsT (σ.f fun _ => h.j i) (h.W i)) :=
        fun σ => by
          rw [sval_of σ (𝟙 G.left) x J (fun _ => h.j i) (fun q => by rw [Category.id_comp]; exact e q)]
          exact (gsR (𝟙 G.left) x (hWc i) hx _).symm
      rw [s1, s1] at hp
      rw [gs_mul _ x _ hx, gs_mul _ x _ hx, gsC _ x _ hx, gsC _ x _ hx]
      exact hp
    rw [hρ i, hτ i, ← leib, ← leib, hA]

  intro Z r z J hJ
  obtain ⟨i, hi⟩ : ∃ i, r z ∈ h.W i := by
    have : r z ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hz1 := hJ.mem (fun _ : Fin 1 => m) r
  have hz2 : r z ∈ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) := hWc i hi
  have sv : ∀ σ : SecM m L k, sval σ r z J =
      (trF (fun _ : Fin 1 => m) (fun _ => (k : ℤ)) r z (fun _ => J (r ≫ m)) (fun _ => h.j i)).val *
        gs r z (h.W i) (rsT (σ.f fun _ => h.j i) (h.W i)) := fun σ => by
    exact (sec_trans σ r z hz1 hz2).trans (congrArg _ (gsR r z (hWc i) hi _).symm)
  have E := congrArg (gs r z (h.W i)) (onW i)
  simp only [gs_add r z _ hi, gs_mul r z _ hi, gsC r z _ hi] at E
  rw [sv ρ, sv τ, sv ρ', sv τ']
  linear_combination (trF (fun _ : Fin 1 => m) (fun _ => (k : ℤ)) r z (fun _ => J (r ≫ m)) (fun _ => h.j i)).val * E

end GlobalTheory.Heat

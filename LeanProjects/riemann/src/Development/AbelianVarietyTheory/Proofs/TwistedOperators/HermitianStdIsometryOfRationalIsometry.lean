import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

variable {D : D7}

def sumMap (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) {a ρ : ℕ} (z : Fin a → Y.V) (e f : Fin ρ → Y.V) :
    (X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) →ₗ[D.host.E] Y.V :=
  ι.coprod ((Fintype.linearCombination D.host.E z).coprod
    ((Fintype.linearCombination D.host.E e).coprod (Fintype.linearCombination D.host.E f)))

theorem sumMap_apply (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) {a ρ : ℕ} (z : Fin a → Y.V) (e f : Fin ρ → Y.V)
    (p : X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) :
    sumMap Y X ι z e f p = ι p.1 + (∑ i, p.2.1 i • z i + (∑ i, p.2.2.1 i • e i + ∑ i, p.2.2.2 i • f i)) := by
  simp [sumMap, Fintype.linearCombination_apply]

theorem hT_swap (Y : HSp D) (x y : Y.V) : Y.hT x y = star (Y.hT y x) := (Y.herm.eq y x).symm

theorem form_sumMap {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f)
    (p q : X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) :
    Y.hT (sumMap Y X ι z e f p) (sumMap Y X ι z e f q) =
      X.hT p.1 q.1 + (∑ i, star (p.2.1 i) * q.2.1 i * c +
        (∑ i, star (p.2.2.1 i) * q.2.2.2 i + ∑ i, star (p.2.2.2 i) * q.2.2.1 i)) := by
  have hsub : Subsingleton (Fin a) := by
    have := h.a_le
    exact ⟨fun i j => Fin.ext (by omega)⟩
  have zz : ∀ i j, Y.hT (z i) (z j) = if i = j then c else 0 := fun i j => by
    obtain rfl := Subsingleton.elim i j
    rw [if_pos rfl]; exact h.z_norm i
  have zx : ∀ i x, Y.hT (z i) (ι x) = 0 := fun i x => h.z_X i x
  have xz : ∀ i x, Y.hT (ι x) (z i) = 0 := fun i x => by rw [hT_swap, zx, star_zero]
  have ex : ∀ i x, Y.hT (e i) (ι x) = 0 := fun i x => (h.hyp_X i x).1
  have xe : ∀ i x, Y.hT (ι x) (e i) = 0 := fun i x => by rw [hT_swap, ex, star_zero]
  have fx : ∀ i x, Y.hT (f i) (ι x) = 0 := fun i x => (h.hyp_X i x).2
  have xf : ∀ i x, Y.hT (ι x) (f i) = 0 := fun i x => by rw [hT_swap, fx, star_zero]
  have ez : ∀ i j, Y.hT (e i) (z j) = 0 := fun i x => (h.hyperbolicDecomp_hyp_orthogonal_line i x).1
  have ze : ∀ i j, Y.hT (z j) (e i) = 0 := fun i x => by rw [hT_swap, ez, star_zero]
  have fz : ∀ i j, Y.hT (f i) (z j) = 0 := fun i x => (h.hyperbolicDecomp_hyp_orthogonal_line i x).2
  have zf : ∀ i j, Y.hT (z j) (f i) = 0 := fun i x => by rw [hT_swap, fz, star_zero]
  have ee : ∀ i j, Y.hT (e i) (e j) = 0 := fun i j => h.ee j i
  have ff : ∀ i j, Y.hT (f i) (f j) = 0 := fun i j => h.ff j i
  have fe : ∀ i j, Y.hT (f i) (e j) = if j = i then 1 else 0 := fun i j => h.ef j i
  have ef : ∀ i j, Y.hT (e i) (f j) = if i = j then 1 else 0 := fun i j => by
    rw [hT_swap, fe]; split_ifs <;> simp
  have xx : ∀ x y, Y.hT (ι x) (ι y) = X.hT x y := h.isom
  rw [sumMap_apply, sumMap_apply]
  simp only [map_add, map_sum, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, zz, zx, xz, ex, xe, fx, xf, ez, ze, fz, zf, ee, ff, fe, ef, xx, smul_eq_mul, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, mul_one, RingHom.id_apply, starRingEnd_apply]
  rw [add_comm (∑ i, star (p.2.2.1 i) * q.2.2.2 i)]
  congr 1
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

theorem sumMap_injective {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f) (hc : c ≠ 0) : Function.Injective (sumMap Y X ι z e f) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨x, α, β, γ⟩ hp
  have H := fun q => form_sumMap h (x, α, β, γ) q
  simp only [hp, map_zero, LinearMap.zero_apply] at H
  have h1 : x = 0 := X.nondeg.1 x fun y => by simpa using (H (y, 0, 0, 0)).symm
  have h2 : α = 0 := funext fun i => by
    simpa [Pi.single_apply, hc] using (H (0, Pi.single i 1, 0, 0)).symm
  have h3 : β = 0 := funext fun i => by
    simpa [Pi.single_apply] using (H (0, 0, 0, Pi.single i 1)).symm
  have h4 : γ = 0 := funext fun i => by
    simpa [Pi.single_apply] using (H (0, 0, Pi.single i 1, 0)).symm
  simp [h1, h2, h3, h4]

def sumEquiv {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f) (hc : c ≠ 0) :
    (X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) ≃ₗ[D.host.E] Y.V :=
  LinearEquiv.ofInjectiveOfFinrankEq (sumMap Y X ι z e f) (sumMap_injective h hc) (by
    simp only [Module.finrank_prod, Module.finrank_fin_fun, X.rank_eq, Y.rank_eq, h.rank]
    ring)

theorem sumEquiv_apply {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f) (hc : c ≠ 0) (p) :
    sumEquiv h hc p = sumMap Y X ι z e f p := rfl

theorem exists_isom {Y Y' X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {ι' : X.V →ₗ[D.host.E] Y'.V} {a ρ : ℕ}
    {z : Fin a → Y.V} {z' : Fin a → Y'.V} {c : D.host.E} {e f : Fin ρ → Y.V} {e' f' : Fin ρ → Y'.V}
    (h : IsDec Y X ι z c e f) (h' : IsDec Y' X ι' z' c e' f') (hc : c ≠ 0) :
    ∃ io : Y.V ≃ₗ[D.host.E] Y'.V, HSpace.IsIsomEmb Y Y' io.toLinearMap ∧
      (∀ x, io (ι x) = ι' x) ∧ (∀ i, io (z i) = z' i) ∧ ∀ i, io (e i) = e' i ∧ io (f i) = f' i := by
  have key : ∀ p, ((sumEquiv h hc).symm.trans (sumEquiv h' hc)) (sumMap Y X ι z e f p) =
      sumMap Y' X ι' z' e' f' p := fun p => by
    rw [← sumEquiv_apply h hc, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, sumEquiv_apply]
  refine ⟨(sumEquiv h hc).symm.trans (sumEquiv h' hc), fun x y => ?_, fun x => ?_, fun i => ?_, fun i => ⟨?_, ?_⟩⟩
  · obtain ⟨p, rfl⟩ := (sumEquiv h hc).surjective x
    obtain ⟨q, rfl⟩ := (sumEquiv h hc).surjective y
    rw [sumEquiv_apply, sumEquiv_apply, LinearEquiv.coe_coe, key, key, form_sumMap h, form_sumMap h']
  · simpa [sumMap_apply] using key (x, 0, 0, 0)
  · simpa [sumMap_apply, Pi.single_apply] using key (0, Pi.single i 1, 0, 0)
  · simpa [sumMap_apply, Pi.single_apply] using key (0, 0, Pi.single i 1, 0)
  · simpa [sumMap_apply, Pi.single_apply] using key (0, 0, 0, Pi.single i 1)

theorem isDec_rescale {Y X X' : HSp D} {ι : X'.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X' ι z c e f) (φ : X.V →ₗ[D.host.E] X'.V) (hφ : HSpace.IsIsomEmb X X' φ)
    (hr : X.rank = X'.rank) (π : D.host.E) :
    IsDec Y X (ι ∘ₗ φ) (fun i => π • z i) (c * (π * star π)) e f where
  isom x y := (h.isom _ _).trans (hφ x y)
  a_le := h.a_le
  rank := by rw [hr, h.rank]
  z_norm i := by
    have := h.z_norm i
    simp only [HSpace.hD, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      starRingEnd_apply] at this ⊢
    rw [this]; ring
  z_X i x := by
    have := h.z_X i (φ x)
    simp only [HSpace.hD, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply] at this ⊢
    rw [this, mul_zero]
  ee := h.ee
  ff := h.ff
  ef := h.ef
  hyp_X i x := h.hyp_X i (φ x)
  hyperbolicDecomp_hyp_orthogonal_line i j := by
    have := h.hyperbolicDecomp_hyp_orthogonal_line i j
    simp only [HSpace.hD, LinearMap.map_smulₛₗ, smul_eq_mul] at this ⊢
    rw [this.1, this.2, mul_zero]; exact ⟨rfl, rfl⟩

theorem stdIsomSt_of_rationalSt : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D → GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.StdIsomSt D := by
  intro D hR u
  refine ⟨?_, ?_⟩
  · obtain ⟨π, h1, h2, -⟩ := D.T_norm u
    exact ⟨π, h1, by rw [bridge_star_holds D.R D.host]; exact h2⟩
  intro π hπ s a ρ Y X ι z e f Y' X' ι' z' e' f' h h' hX hX' hp hp' hr
  obtain ⟨φ, hφ⟩ := hR X X' hX hX' hr fun τ => by rw [hp τ, hp' τ, hr]
  have h2 := isDec_rescale h' φ.toLinearMap hφ hr (π : D.host.E)
  rw [hπ.2] at h2
  have hc : ((s : ℤ) : D.host.E) * Tu D u ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr s.ne_zero) (Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero)
  obtain ⟨io, a1, a2, a3, a4⟩ := exists_isom h h2 hc
  exact ⟨φ, io, hφ, a1, a2, a3, a4⟩

end GlobalTheory.StdIsom
end

import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LieMet MonObj

namespace GlobalTheory.ShFam.Pad.Pull

attribute [local instance] Over.cartesianMonoidalCategory

section Lin

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V] {m : ℕ}

theorem lin_comp {u u' : Fin m → V} (A : Fin m → Fin m → k) (hA : ∀ j i, j < i → A j i = 0)
    (hu : ∀ j, u' j = ∑ i, A j i • u i) (d : Fin m → k) (j : Fin m) (hd : ∀ i, j < i → d i = 0) :
    ∃ e : Fin m → k, (∀ i, j < i → e i = 0) ∧ e j = d j * A j j ∧ ∑ i, d i • u' i = ∑ i, e i • u i := by
  refine ⟨fun i => ∑ l, d l * A l i, fun i hi => Finset.sum_eq_zero fun l _ => ?_, ?_, ?_⟩
  · rcases lt_or_ge j l with h | h
    · rw [hd l h, zero_mul]
    · rw [hA l i (h.trans_lt hi), mul_zero]
  · refine Finset.sum_eq_single j (fun l _ hl => ?_) (by simp)
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hA l j h, mul_zero]
    · rw [hd l h, zero_mul]
  · simp only [hu, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm

theorem lin_symm {u u' : Fin m → V} (hi : ∀ c c' : Fin m → k, ∑ i, c i • u' i = ∑ i, c' i • u' i → c = c')
    (A : Fin m → Fin m → k) (hA : ∀ j i, j < i → A j i = 0) (hu : ∀ j, u' j = ∑ i, A j i • u i) :
    ∃ B : Fin m → Fin m → k, (∀ j i, j < i → B j i = 0) ∧ (∀ j, u j = ∑ i, B j i • u' i) ∧ ∀ j, A j j * B j j = 1 := by
  classical
  let M : Matrix (Fin m) (Fin m) k := Matrix.of A
  have key : ∀ d : Fin m → k, ∑ i, d i • u' i = ∑ i, Matrix.vecMul d M i • u i := fun d => by
    simp only [hu, Finset.smul_sum, smul_smul, Finset.sum_smul, Matrix.vecMul, dotProduct, M, Matrix.of_apply]
    exact Finset.sum_comm
  have hM : IsUnit M := Matrix.vecMul_injective_iff_isUnit.1 fun d d' h => hi _ _ (by
    rw [key, key]; exact congrArg (fun c : Fin m → k => ∑ i, c i • u i) h)
  obtain ⟨I⟩ := hM.nonempty_invertible
  have ht : M.BlockTriangular OrderDual.toDual := fun j i h => hA j i h
  have hB : ∀ j i, j < i → M⁻¹ j i = 0 := fun j i h => Matrix.blockTriangular_inv_of_blockTriangular ht h
  have h2 : ∀ j, u j = ∑ i, M⁻¹ j i • u' i := fun j => by
    rw [key, show Matrix.vecMul (M⁻¹ j) M = (M⁻¹ * M) j from rfl, Matrix.inv_mul_of_invertible]
    simp [Matrix.one_apply]
  refine ⟨fun j i => M⁻¹ j i, hB, h2, fun j => ?_⟩
  obtain ⟨e, -, he, h⟩ := lin_comp (fun j i => M⁻¹ j i) hB h2 (A j) j (hA j)
  have := hi e (Pi.single j 1) (by rw [← h, ← hu]; simp [Pi.single_apply])
  rw [← he, this, Pi.single_eq_same]

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

section Tan

variable {k : Type} [Field k] (x : Sp k ⟶ X) {m : ℕ}

def Ind (u : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (u i)) ∧ ∀ cf cf' w, IsCombAtG t x u cf w → IsCombAtG t x u cf' w → cf = cf'

def Tri (u u' : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) : Prop :=
  ∀ j, ∃ cf : Fin m → k, (∀ i, j < i → cf i = 0) ∧ IsCombAtG t x u cf (u' j)

variable {t x} {u u' u'' : Fin m → (Sp (DualNumber k) ⟶ t.G.left)}

theorem comb_iff (U : Fin m → TanM x t.G) (a : Fin m → k) (w : Sp (DualNumber k) ⟶ t.G.left) :
    IsCombAtG t x (fun i => (tv (U i)).left) a w ↔ w = (tv (∑ i, a i • U i)).left := by
  have h := (GlobalTheory.LieMet.isComb_iff U a _).2 rfl
  refine ⟨fun h' => ?_, fun e => e ▸ h⟩
  exact ((isCombAtG_iff t x (fun i => tv (U i)) a _).1 h').symm.trans
    ((isCombAtG_iff t x (fun i => tv (U i)) a _).1 h)

theorem exists_tan (h : ∀ i, IsTanAtG t x (u i)) : ∃ U : Fin m → TanM x t.G, u = fun i => (tv (U i)).left :=
  ⟨fun i => tanOf (h i), rfl⟩

theorem Tri.comp (hu : ∀ i, IsTanAtG t x (u i)) (hu' : ∀ i, IsTanAtG t x (u' i)) (h : Tri t x u u') {d : Fin m → k}
    {j : Fin m} (hd : ∀ i, j < i → d i = 0) {w : Sp (DualNumber k) ⟶ t.G.left} (hw : IsCombAtG t x u' d w) :
    ∃ c e : Fin m → k, IsCombAtG t x u c (u' j) ∧ (∀ i, j < i → e i = 0) ∧ e j = d j * c j ∧ IsCombAtG t x u e w := by
  obtain ⟨U, rfl⟩ := exists_tan hu
  obtain ⟨U', rfl⟩ := exists_tan hu'
  choose A hA hc using h
  obtain ⟨e, h1, h2, h3⟩ := lin_comp A hA (fun j => (GlobalTheory.LieMet.isComb_iff U _ _).1 (hc j)) d j hd
  exact ⟨A j, e, hc j, h1, h2, (comb_iff _ _ _).2 (h3 ▸ (comb_iff _ _ _).1 hw)⟩

theorem Tri.trans (hu : ∀ i, IsTanAtG t x (u i)) (hu' : ∀ i, IsTanAtG t x (u' i)) (h : Tri t x u u')
    (h' : Tri t x u' u'') : Tri t x u u'' := fun j => by
  obtain ⟨d, hd, hw⟩ := h' j
  obtain ⟨-, e, -, h1, -, h2⟩ := h.comp hu hu' hd hw
  exact ⟨e, h1, h2⟩

theorem Tri.symm (hu : Ind t x u) (hu' : Ind t x u') (h : Tri t x u u') : Tri t x u' u ∧
    ∀ j c d, IsCombAtG t x u c (u' j) → IsCombAtG t x u' d (u j) → c j * d j = 1 := by
  obtain ⟨U, rfl⟩ := exists_tan hu.1
  obtain ⟨U', rfl⟩ := exists_tan hu'.1
  choose A hA hc using h
  obtain ⟨B, h1, h2, h3⟩ := lin_symm (u := U) (u' := U') (fun c c' e => hu'.2 c c' _ ((GlobalTheory.LieMet.isComb_iff _ _ _).2 rfl)
    ((GlobalTheory.LieMet.isComb_iff _ _ _).2 e)) A hA fun j => (GlobalTheory.LieMet.isComb_iff U _ _).1 (hc j)
  refine ⟨fun j => ⟨B j, h1 j, (GlobalTheory.LieMet.isComb_iff _ _ _).2 (h2 j)⟩, fun j c d hc' hd => ?_⟩
  rw [hu.2 _ _ _ hc' (hc j), hu'.2 _ _ _ hd ((GlobalTheory.LieMet.isComb_iff _ _ _).2 (h2 j)), h3]

theorem Tri.diag (hu : Ind t x u) (hu' : Ind t x u') (h : Tri t x u u') {j : Fin m} {c : Fin m → k}
    (hc : IsCombAtG t x u c (u' j)) : c j ≠ 0 ∧ ∀ i, j < i → c i = 0 := by
  obtain ⟨h1, h2⟩ := h.symm hu hu'
  obtain ⟨d, -, hd⟩ := h1 j
  obtain ⟨c', h3, h4⟩ := h j
  exact ⟨left_ne_zero_of_mul_eq_one (h2 j c d hc hd), hu.2 _ _ _ hc h4 ▸ h3⟩

theorem Tri.diag_mul (hu : Ind t x u) (hu' : ∀ i, IsTanAtG t x (u' i)) (h : Tri t x u u') {c d e : Fin m → k}
    {j : Fin m} (hd : ∀ i, j < i → d i = 0) {w : Sp (DualNumber k) ⟶ t.G.left} (hw : IsCombAtG t x u' d w)
    (hc : IsCombAtG t x u c (u' j)) (he : IsCombAtG t x u e w) : e j = d j * c j := by
  obtain ⟨c', e', h1, -, h2, h3⟩ := h.comp hu.1 hu' hd hw
  rw [hu.2 _ _ _ he h3, hu.2 _ _ _ hc h1, h2]

end Tan

section Norm

variable {t} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {x : Sp C ⟶ X} {m : ℕ}
  {u u' : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}

open Pointwise in
theorem Tri.grNorm_eq (hu : Ind t x u) (hu' : Ind t x u') (h : Tri t x u u') (Λ : Set (Sp (DualNumber C) ⟶ t.G.left))
    {j : Fin m} {c : Fin m → C} (hc : IsCombAtG t x u c (u' j)) :
    grNorm t x Λ u' j = ‖c j‖ * grNorm t x Λ u j := by
  have h0 := (h.diag hu hu' hc).1
  obtain ⟨h1, h2⟩ := h.symm hu hu'
  rw [grNorm, grNorm, ← smul_eq_mul, ← Real.sInf_smul_of_nonneg (norm_nonneg _)]
  congr 1
  ext r
  constructor
  · rintro ⟨d, d0, d1, ⟨w, hw, d2⟩, rfl⟩
    obtain ⟨c', e, k1, k2, k3, k4⟩ := h.comp hu.1 hu'.1 d1 d2
    obtain rfl := hu.2 _ _ _ hc k1
    refine ⟨_, ⟨e, k3 ▸ mul_ne_zero d0 h0, k2, ⟨w, hw, k4⟩, rfl⟩, ?_⟩
    have := norm_ne_zero_iff.2 h0
    simp only [k3, norm_mul, smul_eq_mul]
    field_simp
  · rintro ⟨_, ⟨d, d0, d1, ⟨w, hw, d2⟩, rfl⟩, rfl⟩
    obtain ⟨c', e, k1, k2, k3, k4⟩ := h1.comp hu'.1 hu.1 d1 d2
    have e1 := h2 j c c' hc k1
    refine ⟨e, k3 ▸ mul_ne_zero d0 (right_ne_zero_of_mul_eq_one e1), k2, ⟨w, hw, k4⟩, ?_⟩
    rw [k3, eq_inv_of_mul_eq_one_right e1]
    simp [mul_comm]

theorem grNorm_push {X' : Scheme.{0}} {t' : SAB H X'} {f : X' ⟶ X} (mu : SABMap t' t f) {x' : Sp C ⟶ X'}
    (hx : x' ≫ f = x) {Λ' : Set (Sp (DualNumber C) ⟶ t'.G.left)} {Λ : Set (Sp (DualNumber C) ⟶ t.G.left)}
    (hΛ : ∀ v, IsTanAtG t' x' v → (v ∈ Λ' ↔ v ≫ mu.φ ∈ Λ)) {v : Fin m → (Sp (DualNumber C) ⟶ t'.G.left)}
    (hv : ∀ i, IsTanAtG t' x' (v i)) (j : Fin m) :
    grNorm t' x' Λ' v j = grNorm t x Λ (fun i => v i ≫ mu.φ) j := by
  obtain ⟨U, rfl⟩ := exists_tan hv
  have e : ∀ c : Fin m → C, (∃ w ∈ Λ', IsCombAtG t' x' (fun i => (tv (U i)).left) c w) ↔
      ∃ w ∈ Λ, IsCombAtG t x (fun i => (tv (pushL mu x' hx (U i))).left) c w := fun c => by
    simp only [comb_iff, exists_eq_right]
    rw [hΛ _ (isTan_tv _), ← left_pushL mu x' hx, map_sum]
    simp only [map_smul]
  simp only [grNorm, e]
  rfl

end Norm

end GlobalTheory.ShFam.Pad.Pull

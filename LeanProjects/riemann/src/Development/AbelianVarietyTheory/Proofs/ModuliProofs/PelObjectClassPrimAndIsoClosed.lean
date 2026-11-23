import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.PelPrim

def chartPullSection {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (ψ : X ⟶ Y) (e : ψ ≫ φ = 𝟙 X) :
    ChartPull L (L.pull φ) ψ :=
  have le : ∀ i, L.U i ≤ ψ ⁻¹ᵁ (L.pull φ).U (fun _ => i) := fun i y hy => mem_pull.2 (by
    have : (ψ ≫ φ) y ∈ L.U i := by rw [e]; exact hy
    exact this)
  { idx := fun i _ => i
    le := le
    g := fun y i j hi hj =>
      ((gm_pull_g L φ ψ y (fun _ => i) (fun _ => j) (le i hi) (le j hj)).trans (by rw [e])).symm }

theorem lbIso_inv {X Y : Scheme.{0}} {L : LB X} {M : LB Y} {φ : Y ⟶ X} {ψ : X ⟶ Y} (e : ψ ≫ φ = 𝟙 X)
    (h : LBIso M (L.pull φ)) : LBIso L (M.pull ψ) :=
  (LBIso.chartPull (chartPullPull M ψ ψ rfl) (chartPullSection L φ ψ e) h).symm

theorem lbIso_comp {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
    (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB) (h : LBIso L' (L.pull F)) (h' : LBIso L'' (L'.pull F')) :
    LBIso L'' (L.pull (F' ≫ F)) := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw'⟩ := h'
  obtain ⟨w'', T⟩ := exists_comp hL' w w' ((isGen_iff w).1 hw) ((isGen_iff w').1 hw') hL hL''
  exact ⟨w'', (isGen_iff w'').2 (T.pgen_comp hL' ((isGen_iff w).1 hw) ((isGen_iff w').1 hw'))⟩

theorem lbIso_linComb {X Y : Scheme.{0}} {L M : LB X} (h : LBIso L M) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) : LBIso (LB.LinComb L φ ε) (LB.LinComb M φ ε) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨_, DVR.linCombIso_isGen w hw φ ε⟩

section Cube
variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]

theorem psum_comp (ψ : A ⟶ G) [IsMonHom ψ] {T T' : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ A)) (x : Fin n → (T ⟶ G))
    (U : T' ⟶ T) (hx : ∀ i, x' i ≫ ψ = U ≫ x i) (I : Finset (Fin n)) :
    (psum A x' I).left ≫ ψ.left = U.left ≫ (psum G x I).left := by
  have e : psum A x' I ≫ ψ = U ≫ psum G x I :=
    (psum_hom (MonoidHom.mk' (· ≫ ψ) fun a b => MonObj.mul_comp a b ψ) x' I).trans
      ((congrArg (fun z => psum G z I) (funext hx)).trans (psum_hom (preHom U) x I).symm)
  exact congrArg (fun z => z.left) e

def chartPullCube (ψ : A ⟶ G) [IsMonHom ψ] (M : LB G.left) {T T' : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ A))
    (x : Fin n → (T ⟶ G)) (U : T' ⟶ T) (hx : ∀ i, x' i ≫ ψ = U ≫ x i) :
    ChartPull (cubeLB A x' (M.pull ψ.left)) (cubeLB G x M) U.left :=
  chartPullLinComb M _ _ _ _ U.left fun I => psum_comp ψ x' x U hx I.down

omit [IsCommMonObj A] in
theorem cube_isLB {L : LB A.left} (hL : L.IsLB) {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) : (cubeLB A x L).IsLB :=
  DVR.linComb_isLB L hL _ _

omit [IsCommMonObj A] in
theorem cube_congr {L M : LB A.left} (h : LBIso L M) {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) :
    LBIso (cubeLB A x L) (cubeLB A x M) := lbIso_linComb h _ _

theorem adj_pull (ψ : A ⟶ G) [IsMonHom ψ] {L : LB A.left} {M : LB G.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso L (M.pull ψ.left)) {u v : A ⟶ A} {u₀ v₀ : G ⟶ G} (hu : u ≫ ψ = ψ ≫ u₀) (hv : v ≫ ψ = ψ ≫ v₀)
    (H : LBIso (cubeLB G ![fst G G ≫ u₀, snd G G] M) (cubeLB G ![fst G G, snd G G ≫ v₀] M)) :
    LBIso (cubeLB A ![fst A A ≫ u, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ v] L) := by
  have hP := pull_isLB hM ψ.left
  refine ((cube_congr h _).trans (cube_isLB hL _) (cube_isLB hP _) (cube_isLB hP _) ?_).trans
    (cube_isLB hL _) (cube_isLB hP _) (cube_isLB hL _) (cube_congr h _).symm
  refine LBIso.chartPull (chartPullCube ψ M _ _ (ψ ⊗ₘ ψ) fun i => ?_) (chartPullCube ψ M _ _ (ψ ⊗ₘ ψ) fun i => ?_) H
  · fin_cases i <;> simp [hu]
  · fin_cases i <;> simp [hv]

theorem prim_pull (ψ : A ⟶ G) [IsMonHom ψ] {L : LB A.left} {M : LB G.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso L (M.pull ψ.left)) {u : A ⟶ A} {u₀ : G ⟶ G} (hu : u ≫ ψ = ψ ≫ u₀)
    (H : LBIso M (cubeLB G ![𝟙 G, u₀] M)) : LBIso L (cubeLB A ![𝟙 A, u] L) := by
  have hP := pull_isLB hM ψ.left
  refine (h.trans hL hP (cube_isLB hP _) ?_).trans hL (cube_isLB hP _) (cube_isLB hL _) (cube_congr h _).symm
  refine LBIso.chartPull (chartPullPull M _ ψ.left rfl) (chartPullCube ψ M _ _ ψ fun i => ?_) H
  fin_cases i <;> simp [hu]

end Cube

theorem cmHostUnit_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have hd : 0 < H.d := H.d_prime.pos
  have h1 : H.bar H.rt ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  have h2 : H.bar H.rt = -H.rt := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exfalso
      obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have e := H.bar_eq H.rt
      rw [h] at e
      have e2 : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
        rw [← IsCMField.complexEmbedding_complexConj, ← e]
      have e3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
        have := congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq
        simpa using this
      obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 e2
      rw [hr] at e3
      have e4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast e3
      have : (0 : ℝ) < H.d := by exact_mod_cast hd
      nlinarith [sq_nonneg r]
    · exact h
  have h3 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_add, map_one, h2, map_ofNat] at this
    rw [this]; ring
  have h4 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by rw [mul_add, h3, H.two_weight_eq_one_add_root]; ring
  exact mul_left_cancel₀ two_ne_zero h4

end GlobalTheory.PelPrim

open GlobalTheory.PelPrim in

theorem GlobalTheory.pelClass_prim_and_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (t : TObj g k J b (spMap em)), PELClass D a bas ρ em t → (a w = H.w0 → a w' = H.bar H.w0 → t.Prim w w') ∧ ∀ t' : TObj g k J b (spMap em), TMap t' t (𝟙 _) → PELClass D a bas ρ em t' := by
  intro E _ _ _ H D o _ g k J b em w w' a bas ρ t ⟨τ, φ, hφ, hL, hact, hpt⟩
  refine ⟨fun hw hw' => ?_, fun t' ⟨ψ, hψ, hL', hpt', hact'⟩ => ?_⟩
  · let _ := t.ab.comm
    have hinv : ∀ j, t.act j ≫ φ.inv = φ.inv ≫ τ.act.act (a j) := fun j => by
      rw [Iso.comp_inv_eq, Category.assoc, hact, φ.inv_hom_id_assoc]
    have hL₀ : LBIso t.L (τ.PP.L.pull φ.inv.left) :=
      lbIso_inv (by rw [← Over.comp_left, φ.inv_hom_id, Over.id_left]) hL
    refine ⟨?_, adj_pull φ.inv t.isLB τ.PP.isLB hL₀ (hinv w) (hinv w') ?_,
      prim_pull φ.inv t.isLB τ.PP.isLB hL₀ (hinv w) ?_⟩
    · rw [← cancel_epi φ.hom, MonObj.comp_mul, ← hact, ← hact, ← MonObj.mul_comp, ← τ.act.add, hw, hw', cmHostUnit_add_conj_eq_one,
        τ.act.one, Category.id_comp, Category.comp_id]
    · rw [hw, hw']; exact τ.adj _
    · rw [hw]; exact τ.prim
  · have : IsMonHom (Iso.refl t.A).hom := inferInstanceAs (IsMonHom (𝟙 t.A))
    obtain ⟨e, he, hl⟩ := grpPullback_iso hψ (isGrpPullback_of_iso (Iso.refl t.A))
    have hl' : e.hom.left = ψ := (Category.comp_id _).symm.trans hl
    subst hl'
    have hact₀ : ∀ j, t.act j ≫ e.inv = e.inv ≫ t'.act j := fun j => by
      have : t'.act j ≫ e.hom = e.hom ≫ t.act j := Over.OverMorphism.ext (hact' j)
      rw [Iso.comp_inv_eq, Category.assoc, this, e.inv_hom_id_assoc]
    have hpt₀ : ∀ i, t.pt i ≫ e.inv = t'.pt i := fun i => by
      have : t'.pt i ≫ e.hom = t.pt i := Over.OverMorphism.ext ((hpt' i).trans (Category.id_comp _))
      rw [Iso.comp_inv_eq, this]
    have hL₀ : LBIso t.L (t'.L.pull e.inv.left) :=
      lbIso_inv (by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]) hL'
    refine ⟨τ, φ ≪≫ e.symm, inferInstanceAs (IsMonHom (φ.hom ≫ e.inv)),
      lbIso_comp t'.isLB t.isLB τ.PP.isLB hL₀ hL, fun j => ?_, fun K _ _ _ x β hx => ?_⟩
    · show _ ≫ φ.hom ≫ e.inv = (φ.hom ≫ e.inv) ≫ _
      rw [← Category.assoc, hact, Category.assoc, hact₀, Category.assoc]
    · obtain ⟨h₁, I, h₂, h₃⟩ := hpt K x β hx
      refine ⟨h₁, I, h₂, fun i => ?_⟩
      show _ ≫ φ.hom ≫ e.inv = _
      rw [← Category.assoc, h₃, Category.assoc, hpt₀]
end

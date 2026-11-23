import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LieCoordMult

theorem tanScal_decomp : ∀ (O : Type) [Ring O] (F' : Type) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (act : OActN O G) (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (n a : ℕ) (T : (Fin n → R') → (epsPtR x ⟶ G)) (A : O → Matrix (Fin n) (Fin n) R') (emb : F' → O) (ω : F') (l : R') (χ : Fin a → F' → R'), Function.Injective T → (∀ v : epsPtR x ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk x ⟶ G).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : R') c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) → (∀ b c, T c ≫ act.act b = T (A b *ᵥ c)) → (∀ y : Fin n → R', A (emb ω) *ᵥ y = l • y → ∃ z : Fin a → Fin n → R', (∀ i c, A (emb c) *ᵥ z i = χ i c • z i) ∧ y = ∑ i, z i) → ∀ v : epsPtR x ⟶ G, IsTanScal act x (emb ω) l v → ∃ w : Fin a → (epsPtR x ⟶ G), (∀ i c, IsTanScal act x (emb c) (χ i c) (w i)) ∧ v = (List.ofFn w).prod := by
  intro O _ F' S G _ _ act R' _ x n a T A emb ω l χ hinj htan hadd hsc hact hdec v hv
  have T0 : T 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have Tsum : ∀ (m : ℕ) (y : Fin m → (Fin n → R')), (List.ofFn (fun i => T (y i))).prod = T (∑ i, y i) := by
    intro m
    induction m with
    | zero => intro y; simp [T0]
    | succ m ih => intro y; rw [List.ofFn_succ, List.prod_cons, ih, Fin.sum_univ_succ, hadd]
  have eig : ∀ (b : O) (c : R') (w : epsPtR x ⟶ G), IsTanScal act x b c w ↔ ∃ y, A b *ᵥ y = c • y ∧ w = T y := by
    intro b c w
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ := (htan w).1 h1
      refine ⟨y, hinj (Over.OverMorphism.ext ?_), rfl⟩
      rw [← hact, h2, hsc]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(htan _).2 ⟨y, rfl⟩, ?_⟩
      rw [hact, hy, hsc]
  obtain ⟨y, hy, rfl⟩ := (eig _ _ _).1 hv
  obtain ⟨z, hz, rfl⟩ := hdec y hy
  exact ⟨fun i => T (z i), fun i c => (eig _ _ _).2 ⟨z i, hz i c, rfl⟩, (Tsum a z).symm⟩

end GlobalTheory.LieCoordMult

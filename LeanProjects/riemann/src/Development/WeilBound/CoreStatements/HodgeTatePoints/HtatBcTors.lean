import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHt

noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

section
variable {S Y : Scheme.{0}} {G : Over S} [GrpObj G]

theorem pow_congr {a b : Y ⟶ S} (h : a = b) (g : Over.mk a ⟶ G) (g' : Over.mk b ⟶ G) (e : g.left = g'.left) (N : ℕ) :
    g ^ N = 1 ↔ g' ^ N = 1 := by
  subst h
  rw [Over.OverMorphism.ext e]

theorem mul_congr {a b : Y ⟶ S} (h : a = b) (g k : Over.mk a ⟶ G) (g' k' : Over.mk b ⟶ G) (e : g.left = g'.left)
    (e' : k.left = k'.left) : (g * k).left = (g' * k').left := by
  subst h
  rw [Over.OverMorphism.ext e, Over.OverMorphism.ext e']

theorem comp_pow_pt {A B : Over S} (ψ : A ⟶ B) (g : B ⟶ G) (n : ℕ) : ψ ≫ g ^ n = (ψ ≫ g) ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T}
  {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}

theorem tors_of_pt (h : Γ.IsTorsionAlong G x N i) (v : Y ⟶ Γ.G.left) {c : Y ⟶ S} (g : Over.mk c ⟶ G)
    (e : g.left = v ≫ i) : g ^ N = 1 := by
  have hc : c = (v ≫ Γ.G.hom) ≫ x := by
    rw [Category.assoc, ← h.isOver, ← Category.assoc, ← e]; exact (Over.w g).symm
  subst hc
  exact (h.kernel (Over.mk (v ≫ Γ.G.hom)) g).2 ⟨Over.homMk v rfl, e.symm⟩

theorem pt_of_tors (h : Γ.IsTorsionAlong G x N i) (b : Y ⟶ Spec (CommRingCat.of R)) {c : Y ⟶ S} (hc : c = b ≫ x)
    (g : Over.mk c ⟶ G) (hg : g ^ N = 1) : ∃ v : Y ⟶ Γ.G.left, v ≫ Γ.G.hom = b ∧ v ≫ i = g.left := by
  subst hc
  obtain ⟨y, hy⟩ := (h.kernel (Over.mk b) g).1 hg
  exact ⟨y.left, Over.w y, hy⟩

end

theorem torsion_bc : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → IsSeparated G.hom → ∀ (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R') (Γ' : QFGroup R' T) (i' : Γ'.G.left ⟶ G.left), Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom φ) ≫ x) N i' → ∀ (B : Type) [CommRing B] (b : R →+* B) (j : B →+* FractionRing R) (j' : B →+* FractionRing R') (σ : T → (Spec (CommRingCat.of B) ⟶ G.left)), Function.Injective j → j.comp b = algebraMap R _ → j'.comp b = (algebraMap R' _).comp φ → (∀ t, σ t ≫ G.hom = Spec.map (CommRingCat.ofHom b) ≫ x) → (∀ t, Spec.map (CommRingCat.ofHom j) ≫ σ t = (Γ.pt t).left ≫ i) → (∀ t, Spec.map (CommRingCat.ofHom j') ≫ σ t = (Γ'.pt t).left ≫ i') → ∃ F : Γ'.G.left ⟶ Γ.G.left, F ≫ i = i' ∧ Γ'.IsBaseChange Γ φ F := by
  intro R _ _ T _ _ Γ S G _ _ x N i h hsep R' _ _ φ Γ' i' h' B _ b j j' σ hj hjb hj'b hσ hσj hσj'
  let g : Over.mk (i' ≫ G.hom) ⟶ G := Over.homMk i' rfl
  obtain ⟨F, hF1, hF2⟩ := pt_of_tors h (Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ))
    (h'.isOver.trans (Category.assoc _ _ _).symm) g (tors_of_pt h' (𝟙 _) g (Category.id_comp _).symm)
  replace hF2 : F ≫ i = i' := hF2
  refine ⟨F, hF2, ?_, fun Y y z y₀ z₀ hy hz => ?_, ?_⟩
  · have hl : ∀ c : PullbackCone Γ.G.hom (Spec.map (CommRingCat.ofHom φ)), ∃ v : c.pt ⟶ Γ'.G.left,
        v ≫ F = c.fst ∧ v ≫ Γ'.G.hom = c.snd := fun c => by
      let k : Over.mk ((c.fst ≫ i) ≫ G.hom) ⟶ G := Over.homMk (c.fst ≫ i) rfl
      obtain ⟨v, h1, h2⟩ := pt_of_tors h' c.snd
        (by rw [Category.assoc, h.isOver, ← Category.assoc, c.condition, Category.assoc]) k (tors_of_pt h c.fst k rfl)
      exact ⟨v, tors_ext h (by rw [Category.assoc, hF1, ← Category.assoc, h1, c.condition])
        (by rw [Category.assoc, hF2, h2]; rfl), h1⟩
    choose l h1 h2 using hl
    exact ⟨⟨hF1⟩, ⟨PullbackCone.IsLimit.mk hF1 l h1 h2 fun c m a1 a2 => tors_ext h' (a2.trans (h2 c).symm) (by
      rw [← hF2, ← Category.assoc, ← Category.assoc, a1, h1])⟩⟩
  · have w : ∀ {y₀ : Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ)) ⟶ Γ.G},
        (y₀.left ≫ i) ≫ G.hom = (Y.hom ≫ Spec.map (CommRingCat.ofHom φ)) ≫ x := fun {y₀} => by
      rw [Category.assoc, h.isOver, ← Category.assoc, Over.w y₀]; rfl
    have w' : ∀ {y : Y ⟶ Γ'.G}, (y.left ≫ i') ≫ G.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ x := fun {y} => by
      rw [Category.assoc, h'.isOver, ← Category.assoc, Over.w y]
    refine tors_ext h ?_ ?_
    · rw [Category.assoc, hF1, ← Category.assoc, Over.w (y * z)]
      exact Over.w (y₀ * z₀)
    · refine (h.mul _ y₀ z₀ (Over.homMk (y₀.left ≫ i) w) (Over.homMk (z₀.left ≫ i) w) rfl rfl).symm.trans ?_
      rw [Category.assoc, hF2]
      refine Eq.trans ?_ (h'.mul Y y z (Over.homMk (y.left ≫ i') w') (Over.homMk (z.left ≫ i') w') rfl rfl)
      refine mul_congr (Category.assoc _ _ _) _ _ _ _ ?_ ?_
      · show y₀.left ≫ i = y.left ≫ i'
        rw [hy, Category.assoc, hF2]
      · show z₀.left ≫ i = z.left ≫ i'
        rw [hz, Category.assoc, hF2]
  · have : IsDomain B := hj.isDomain j
    have : IsDominant (Spec.map (CommRingCat.ofHom j)) := ⟨by
      have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
        rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)
      exact this⟩
    have hσ' : ∀ t, ∃ v : Spec (CommRingCat.of B) ⟶ Γ.G.left,
        v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom b) ∧ v ≫ i = σ t := fun t => by
      let k : Over.mk (σ t ≫ G.hom) ⟶ G := Over.homMk (σ t) rfl
      refine pt_of_tors h _ (hσ t) k ?_
      let ψ : Over.mk (Spec.map (CommRingCat.ofHom j) ≫ σ t ≫ G.hom) ⟶ Over.mk (σ t ≫ G.hom) :=
        Over.homMk (Spec.map (CommRingCat.ofHom j)) rfl
      have h1 : ψ ≫ k ^ N = ψ ≫ 1 := by
        rw [comp_pow_pt, MonObj.comp_one]
        exact tors_of_pt h (Γ.pt t).left _ (hσj t)
      exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of B)) G.hom
        ((Over.w _).trans (Over.w _).symm) (Spec.map (CommRingCat.ofHom j)) (congrArg (·.left) h1))
    choose v h1 h2 using hσ'
    refine ⟨B, inferInstance, b, j, j', v, hj, hjb, hj'b, h1, fun t => tors_ext h ?_ ?_, fun t => tors_ext h ?_ ?_⟩
    · rw [Category.assoc, h1, Over.w, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjb]; rfl
    · rw [Category.assoc, h2, hσj]
    · rw [Category.assoc, Category.assoc, h1, hF1, ← Category.assoc, Over.w, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hj'b, CommRingCat.ofHom_comp, Spec.map_comp]; rfl
    · rw [Category.assoc, Category.assoc, h2, hF2, hσj']

end PositivityTheory.HtPt.Htat

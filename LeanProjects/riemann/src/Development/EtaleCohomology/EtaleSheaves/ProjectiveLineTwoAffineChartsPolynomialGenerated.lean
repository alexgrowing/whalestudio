import Development.EtaleCohomology.EtaleSheaves.EmbedNonDeg

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.GeometricData

namespace LateralTheory.E.ProjectiveLineCharts₂

def ProjectiveLineTwoAffineChartsPolynomialGenerated : Prop :=
  ∃ (U V : P1.Opens) (s : Γ(P1, U)) (s' : Γ(P1, V)), IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ ∧
    P1.basicOpen s = U ⊓ V ∧ P1.basicOpen s' = U ⊓ V ∧
    P1.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s *
      P1.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s' = 1 ∧
    Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(P1, U)) s) ∧
    Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(P1, V)) s')

def ChartBC : Prop := ∀ (A : Type) [CommRing A] {L : Scheme.{0}} (l : L ⟶ Spec (CommRingCat.of A)) (f : L ⟶ P1),
  IsPullback f l (terminal.from P1) (terminal.from _) → ∀ (W : P1.Opens) (x : Γ(P1, W)), IsAffineOpen W →
  Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(P1, W)) x) →
  IsAffineOpen (f ⁻¹ᵁ W) ∧ Function.Surjective (Polynomial.eval₂RingHom (rA l (f ⁻¹ᵁ W)) (f.app W x))

theorem rA_comp {A : Type} [CommRing A] {Z L : Scheme.{0}} (u : Z ⟶ L) (l : L ⟶ Spec (CommRingCat.of A))
    (W : L.Opens) : rA (u ≫ l) (u ⁻¹ᵁ W) = (u.app W).hom.comp (rA l W) := by
  simp only [rA]
  rw [← Scheme.Hom.appLE_comp_appLE u l ⊤ W (u ⁻¹ᵁ W) le_top le_rfl, u.appLE_eq_app]
  rfl

theorem res_app {X Y : Scheme.{0}} (g : X ⟶ Y) {W W' : Y.Opens} (h : W' ≤ W) (x : Γ(Y, W)) :
    X.presheaf.map (homOfLE (g.preimage_mono h)).op (g.app W x) = g.app W' (Y.presheaf.map (homOfLE h).op x) := by
  have := congrArg (fun φ => φ.hom x) (g.naturality (homOfLE h).op)
  exact this.symm

theorem transport {X Y : Scheme.{0}} (g : X ⟶ Y) {U V : Y.Opens} (s : Γ(Y, U)) (s' : Γ(Y, V))
    (h1 : U ⊔ V = ⊤) (h2 : Y.basicOpen s = U ⊓ V) (h3 : Y.basicOpen s' = U ⊓ V)
    (h4 : Y.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s *
      Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s' = 1) :
    g ⁻¹ᵁ U ⊔ g ⁻¹ᵁ V = ⊤ ∧ X.basicOpen (g.app U s) = g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ∧
    X.basicOpen (g.app V s') = g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ∧
    X.presheaf.map (homOfLE (inf_le_left : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U)).op (g.app U s) *
      X.presheaf.map (homOfLE (inf_le_right : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ V)).op (g.app V s') = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Scheme.Hom.preimage_sup, h1]; rfl
  · rw [← Scheme.preimage_basicOpen, h2]; rfl
  · rw [← Scheme.preimage_basicOpen, h3]; rfl
  · erw [res_app g inf_le_left s, res_app g inf_le_right s', ← map_mul, h4]
    exact map_one _

theorem LineOpens_of (hP : ProjectiveLineTwoAffineChartsPolynomialGenerated) (hB : ChartBC) : LineOpens := by
  intro A _ _ Z p hIL hZ
  obtain ⟨L, u, l, hu, ⟨_, f, hf⟩, rfl⟩ := hIL
  obtain ⟨U0, V0, x, y, hU0, hV0, h1, h2, h3, h4, hsx, hsy⟩ := hP
  obtain ⟨hU1, hsU⟩ := hB A l f hf U0 x hU0 hsx
  obtain ⟨hV1, hsV⟩ := hB A l f hf V0 y hV0 hsy
  obtain ⟨k1, k2, k3, k4⟩ := transport f x y h1 h2 h3 h4
  obtain ⟨m1, m2, m3, m4⟩ := transport u _ _ k1 k2 k3 k4
  have hUa : IsAffineOpen (u ⁻¹ᵁ (f ⁻¹ᵁ U0)) := hU1.preimage u
  have hVa : IsAffineOpen (u ⁻¹ᵁ (f ⁻¹ᵁ V0)) := hV1.preimage u
  have hint : ∀ (W : L.Opens) (z : Γ(L, W)), IsAffineOpen W →
      Function.Surjective (Polynomial.eval₂RingHom (rA l W) z) →
      (Polynomial.eval₂RingHom (rA (u ≫ l) (u ⁻¹ᵁ W)) (u.app W z)).IsIntegral := by
    intro W z hW hs
    have he : Polynomial.eval₂RingHom (rA (u ≫ l) (u ⁻¹ᵁ W)) (u.app W z) =
        (u.app W).hom.comp (Polynomial.eval₂RingHom (rA l W) z) := by
      apply Polynomial.ringHom_ext
      · intro a; simp [rA_comp]
      · simp
    rw [he]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ hs) (u.isIntegral_app W hW)
  by_cases hne : ((u ⁻¹ᵁ (f ⁻¹ᵁ U0) ⊓ u ⁻¹ᵁ (f ⁻¹ᵁ V0) : Z.Opens) : Set Z).Nonempty
  · exact Or.inr ⟨_, _, _, _, hUa, hVa, m1, m2, m3, hne, m4, hint _ _ hU1 hsU, hint _ _ hV1 hsV⟩
  · left
    have : IsIntegral Z := hZ.1
    have hUV : ¬ (((u ⁻¹ᵁ (f ⁻¹ᵁ U0) : Z.Opens) : Set Z).Nonempty ∧
        ((u ⁻¹ᵁ (f ⁻¹ᵁ V0) : Z.Opens) : Set Z).Nonempty) := by
      rintro ⟨a, b⟩
      exact hne (nonempty_preirreducible_inter (u ⁻¹ᵁ (f ⁻¹ᵁ U0)).isOpen (u ⁻¹ᵁ (f ⁻¹ᵁ V0)).isOpen a b)
    rcases not_and_or.mp hUV with h | h
    · have : u ⁻¹ᵁ (f ⁻¹ᵁ V0) = ⊤ := by
        rw [eq_top_iff]; intro z _
        have hz : z ∈ u ⁻¹ᵁ (f ⁻¹ᵁ U0) ⊔ u ⁻¹ᵁ (f ⁻¹ᵁ V0) := m1 ▸ trivial
        rcases (TopologicalSpace.Opens.mem_sup.mp hz) with hz | hz
        · exact absurd ⟨z, hz⟩ h
        · exact hz
      exact this ▸ hVa
    · have : u ⁻¹ᵁ (f ⁻¹ᵁ U0) = ⊤ := by
        rw [eq_top_iff]; intro z _
        have hz : z ∈ u ⁻¹ᵁ (f ⁻¹ᵁ U0) ⊔ u ⁻¹ᵁ (f ⁻¹ᵁ V0) := m1 ▸ trivial
        rcases (TopologicalSpace.Opens.mem_sup.mp hz) with hz | hz
        · exact hz
        · exact absurd ⟨z, hz⟩ h
      exact this ▸ hUa

end LateralTheory.E.ProjectiveLineCharts₂

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeSetEtaleLevelStructureExistsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtOfGeometricPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelSchemeUniversalStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem range_subset_iff_of_charts {X Hk S S₁ S₂ U G₀ G G₁ G₂ P : Scheme.{0}} {g₀ : G₀ ⟶ Hk} {gU : U ⟶ X}
    {m₁ : G₀ ⟶ U} {f : S ⟶ X} {g : G ⟶ S} {mu : G ⟶ U} (hmu : IsPullback mu g gU f)
    {K : Set G₀} {K' : Set G}
    {q₁ : S₁ ⟶ S} {g₁ : G₁ ⟶ S₁} {a₁ : G₁ ⟶ G} (ha₁ : a₁ ≫ g = g₁ ≫ q₁) {h₁ : S₁ ⟶ Hk} {n₁ : G₁ ⟶ G₀}
    (hn₁ : IsPullback n₁ g₁ g₀ h₁) (e₁ : n₁ ≫ m₁ = a₁ ≫ mu) (k₁ : a₁ ⁻¹' K' = n₁ ⁻¹' K)
    {q₂ : S₂ ⟶ S} {g₂ : G₂ ⟶ S₂} {a₂ : G₂ ⟶ G} (ha₂ : a₂ ≫ g = g₂ ≫ q₂) {h₂ : S₂ ⟶ Hk} {n₂ : G₂ ⟶ G₀}
    (hn₂ : IsPullback n₂ g₂ g₀ h₂) (e₂ : n₂ ≫ m₁ = a₂ ≫ mu) (k₂ : a₂ ⁻¹' K' = n₂ ⁻¹' K)
    (x₁ : P ⟶ S₁) (x₂ : P ⟶ S₂) (hx : x₁ ≫ q₁ = x₂ ≫ q₂)
    (u₁ u₂ : P ⟶ G₀) (hu₁ : u₁ ≫ g₀ = x₁ ≫ h₁) (hu₂ : u₂ ≫ g₀ = x₂ ≫ h₂) (hu : u₁ ≫ m₁ = u₂ ≫ m₁) :
    (Set.range u₁ ⊆ K ↔ Set.range u₂ ⊆ K) := by
  have key : ∀ {A B : Scheme.{0}} (w : P ⟶ A) (c : A ⟶ B) (L : Set B),
      Set.range (w ≫ c) ⊆ L ↔ Set.range w ⊆ c ⁻¹' L := by
    intro A B w c L
    simp [Set.range_subset_iff]
  obtain ⟨w₁, hw₁, hw₁'⟩ := hn₁.exists_lift u₁ x₁ hu₁
  obtain ⟨w₂, hw₂, hw₂'⟩ := hn₂.exists_lift u₂ x₂ hu₂
  have hw : w₁ ≫ a₁ = w₂ ≫ a₂ := by
    apply hmu.hom_ext
    · rw [Category.assoc, Category.assoc, ← e₁, ← e₂, ← Category.assoc, ← Category.assoc, hw₁, hw₂, hu]
    · rw [Category.assoc, Category.assoc, ha₁, ha₂, ← Category.assoc, ← Category.assoc, hw₁', hw₂', hx]
  rw [← hw₁, ← hw₂, key, key, ← k₁, ← k₂, ← key, ← key, hw]

theorem exists_kerScheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), admitted l 𝔓 p → ∃ Z : KerScheme Xo 𝔓 p i, EtSet Z.o₁.t.G Z.K := by
  intro E _ _ _ H D l Xo 𝔓 p i hA
  have laws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨Hk, π₁, o₁, m₁, K, fin₁, et₁, hK, hE, hpt, hex⟩ := GlobalTheory.T.exists_heckeKernel_scheme_universal E H D l Xo 𝔓 p i hA
  refine ⟨⟨Hk, π₁, fin₁, et₁, o₁, m₁, K, hK, hE, ?_⟩, hE⟩
  intro S s hS o K' hE' hK'
  obtain ⟨f, ⟨hf, ⟨mu⟩⟩, hfu⟩ := Xo.rep S s hS o
  obtain ⟨S', π, o', m, τ, hπ₁, hπ₂, hπ₃, hL⟩ := GlobalTheory.T.hecke_set_etale_level_structure_exists E H D l 𝔓 p i S s o K' hA hE' hK'
  have hK'' := ((GlobalTheory.heckeSets_pull E H D 𝔓 p i S S' o.t o'.t π m.toSABMap o.proper).2 K').1 hK'
  obtain ⟨mu', hmu'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o o').2 f π mu).1 m
  obtain ⟨h', n', hh', hn', hKn'⟩ := hex S' (π ≫ s) o' (π ≫ f) mu' τ _ hL hK''
  have cm := m.cart.1
  have cm₁ := m₁.cart.1
  have cn' := n'.cart.1
  haveI : IsReduced S' := GlobalTheory.isReduced_of_smooth_of_isReduced π
  haveI : IsReduced (pullback π π : Scheme.{0}) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst π π)
  have hd : pullback.fst π π ≫ h' = pullback.snd π π ≫ h' := by
    have h0 : (pullback.fst π π ≫ h') ≫ π₁ = (pullback.snd π π ≫ h') ≫ π₁ := by
      rw [Category.assoc, Category.assoc, hh', pullback.condition_assoc]
    refine hom_ext_of_geometric_points _ _ _ π₁ _ _ h0 ?_
    intro k _ _ x
    refine hpt k _ _ (by rw [Category.assoc, Category.assoc x, h0]) ?_
    intro u u' huu
    exact range_subset_iff_of_charts mu.cart.1 cm.w cn' (hn'.trans hmu') hKn' cm.w cn' (hn'.trans hmu') hKn'
      (x ≫ pullback.fst π π) (x ≫ pullback.snd π π) (by rw [Category.assoc, Category.assoc, pullback.condition])
      u.left u'.left (by rw [Category.assoc]; exact Over.w u) (by rw [Category.assoc]; exact Over.w u') huu
  obtain ⟨h, hh⟩ : ∃ h : S ⟶ Hk, π ≫ h = h' := by
    suffices hc : ∀ {Z : Scheme.{0}} (a b : Z ⟶ S'), a ≫ π = b ≫ π → a ≫ h' = b ≫ h' from
      ⟨EffectiveEpi.desc π h' hc, EffectiveEpi.fac π h' hc⟩
    focus
      intro Z a b hab
      have := congrArg (pullback.lift a b hab ≫ ·) hd
      simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this
  have hhf : h ≫ π₁ = f := by
    rw [← cancel_epi π, ← Category.assoc, hh, hh']
  subst hhf
  obtain ⟨n, hn⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ o).2 π₁ h m₁).2 mu
  have cn := n.cart.1
  have hmn : m.toSABMap.φ ≫ n.toSABMap.φ = n'.toSABMap.φ := by
    apply cm₁.hom_ext
    · rw [Category.assoc, ← hn]
      exact (hn'.trans hmu').symm
    · rw [Category.assoc, cn.w, cn'.w, ← Category.assoc, cm.w, Category.assoc, hh]
  have hsurj : Surjective m.toSABMap.φ := MorphismProperty.of_isPullback cm.flip hπ₃
  have hKn : K' = n.toSABMap.φ ⁻¹' K := by
    apply hsurj.surj.preimage_injective
    rw [hKn', ← hmn]
    ext y
    simp
  refine ⟨h, ⟨by rw [← Category.assoc, hf], n, hKn⟩, ?_⟩
  rintro h₂ ⟨hs₂, n₂, hKn₂⟩
  obtain ⟨mu₂, hmu₂⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ o).2 π₁ h₂ m₁).1 n₂
  have h0 : h₂ ≫ π₁ = h ≫ π₁ := hfu _ ⟨by rw [Category.assoc, hs₂], ⟨mu₂⟩⟩
  have hrig : ∀ (f₂ : S ⟶ Xo.X) (mu₂ : ObjMap o Xo.univ f₂), f₂ = h ≫ π₁ → mu₂.toSABMap.φ = mu.toSABMap.φ := by
    intro f₂ mu₂ e
    subst e
    exact GlobalTheory.obj_rigid_closed laws E H D l _ _ _ _ _ _ _ _ Xo.univ o _ (Or.inl hS) _ _
      fun a => ⟨_, mu₂.eta a, mu.eta a⟩
  have e₂ := hmu₂.symm.trans (hrig _ mu₂ h0)
  refine hom_ext_of_geometric_points _ _ _ π₁ _ _ h0 ?_
  intro k _ _ x
  refine hpt k _ _ (by rw [Category.assoc, Category.assoc x, h0]) ?_
  intro u u' huu
  exact range_subset_iff_of_charts (q₁ := 𝟙 S) (q₂ := 𝟙 S) (a₁ := 𝟙 _) (a₂ := 𝟙 _) (K' := K') mu.cart.1 (by simp) n₂.cart.1
    (by rw [Category.id_comp]; exact e₂) (by rw [← hKn₂]; simp) (by simp) cn (by rw [Category.id_comp]; exact hn.symm)
    (by rw [← hKn]; simp) x x rfl u.left u'.left (Over.w u) (Over.w u') huu

end GlobalTheory.HkFam

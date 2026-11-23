import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EtSetOfLists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelListsModuloPermutationsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeSetDescends
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeomPtRangeEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam.KerSch

theorem exists_lift_of_finite {k : Type} [Field k] [IsAlgClosed k] {Y Z : Scheme.{0}} (q : Y ⟶ Z)
    [IsFinite q] [Surjective q] (x : Sp k ⟶ Z) : ∃ y : Sp k ⟶ Y, y ≫ q = x := by
  have : CompactSpace ↥(pullback q x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd q x)
  obtain ⟨p, -⟩ := (pullback.snd q x).surjective (default : PrimeSpectrum k)
  obtain ⟨z, -, hz⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback q x)) ⟨p, trivial⟩
  refine ⟨pointOfClosedPoint (pullback.snd q x) z hz ≫ pullback.fst q x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

theorem exists_lift_ext {k : Type} [Field k] {Y Z : Scheme.{0}} (f : Y ⟶ Z) (u : Sp k ⟶ Z) (t : Sp k) (y₀ : Y)
    (h : f y₀ = u t) : ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (a : Sp k' ⟶ Sp k) (y : Sp k' ⟶ Y),
      Epi a ∧ y ≫ f = a ≫ u := by
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback y₀ t h
  obtain ⟨k', _, _, z, -⟩ := exists_geomPt_range_eq (pullback f u) w
  refine ⟨k', inferInstance, inferInstance, z ≫ pullback.snd f u, z ≫ pullback.fst f u, ?_, ?_⟩
  · generalize z ≫ pullback.snd f u = a
    have : Surjective a := ⟨fun x => ⟨(default : PrimeSpectrum k'), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
    have : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    have : Flat a := inferInstance
    exact Flat.epi_of_flat_of_surjective a
  · rw [Category.assoc, Category.assoc, pullback.condition]

section

variable {A X G₁ Z GY Y : Scheme.{0}} {α : A ⟶ X} {g₁ : G₁ ⟶ Z} {gY : GY ⟶ Y} {φ : G₁ ⟶ A} {ψ : GY ⟶ G₁}
  {π : Z ⟶ X} {q : Y ⟶ Z} {n : ℕ} {σ : Fin n → (Y ⟶ GY)}

theorem range_subset_iff (h₁ : IsPullback φ g₁ α π) (h₂ : IsPullback ψ gY g₁ q) (hσ : ∀ j, σ j ≫ gY = 𝟙 Y)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q →
      Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) = Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ))
    {k : Type} [Field k] (y : Sp k ⟶ Y) (u : Sp k ⟶ G₁) (hu : u ≫ g₁ = y ≫ q) :
    Set.range u ⊆ ψ '' (⋃ j, Set.range (σ j)) ↔ ∃ j, u = y ≫ σ j ≫ ψ := by
  have hs : ∀ j, σ j ≫ ψ ≫ g₁ = q := fun j => by rw [h₂.w, reassoc_of% hσ j]
  constructor
  · intro h
    obtain ⟨w, hw, e⟩ := h ⟨(default : PrimeSpectrum k), rfl⟩
    obtain ⟨j, y₀, rfl⟩ := Set.mem_iUnion.1 hw
    obtain ⟨k', _, _, a, y', ha, e'⟩ := exists_lift_ext (σ j ≫ ψ) u _ y₀ (by rw [Scheme.Hom.comp_apply]; exact e)
    have e₁ : y' ≫ q = (a ≫ y) ≫ q := by
      rw [Category.assoc, ← hu, ← reassoc_of% e', hs j]
    have e₂ : y' ≫ σ j ≫ ψ ≫ φ ∈ Set.range (fun j => (a ≫ y) ≫ σ j ≫ ψ ≫ φ) := hfib k' _ _ e₁ ▸ ⟨j, rfl⟩
    obtain ⟨j', e₃⟩ := e₂
    refine ⟨j', h₁.hom_ext ?_ ?_⟩
    · rw [← cancel_epi a, ← reassoc_of% e']
      simpa using e₃.symm
    · simp only [Category.assoc, hs, hu]
  · rintro ⟨j, rfl⟩ _ ⟨t, rfl⟩
    exact ⟨σ j (y t), Set.mem_iUnion.2 ⟨j, _, rfl⟩, by simp⟩

theorem preimage_eq (h₁ : IsPullback φ g₁ α π) (h₂ : IsPullback ψ gY g₁ q) (hσ : ∀ j, σ j ≫ gY = 𝟙 Y)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q →
      Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) = Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ))
    {GT T : Scheme.{0}} {gT : GT ⟶ T} {ν : GT ⟶ G₁} {h : T ⟶ Y} (h₃ : IsPullback ν gT g₁ (h ≫ q))
    {τ : Fin n → (T ⟶ GT)} (hτ : ∀ j, τ j ≫ gT = 𝟙 T) (hh : ∀ j, τ j ≫ ν = h ≫ σ j ≫ ψ) :
    (⋃ j, Set.range (τ j)) = ν ⁻¹' (ψ '' (⋃ j, Set.range (σ j))) := by
  ext w
  constructor
  · intro hw
    obtain ⟨j, t, rfl⟩ := Set.mem_iUnion.1 hw
    refine ⟨σ j (h t), Set.mem_iUnion.2 ⟨j, _, rfl⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hh]
  · intro hw
    obtain ⟨k, _, _, z, hz⟩ := exists_geomPt_range_eq GT w
    have hzw : ∀ t, z t = w := fun t => by
      have : z t ∈ Set.range z := ⟨_, rfl⟩
      rwa [hz] at this
    obtain ⟨t₀⟩ : Nonempty (Sp k) := ⟨(default : PrimeSpectrum k)⟩
    obtain ⟨j, e⟩ := (range_subset_iff h₁ h₂ hσ hfib (z ≫ gT ≫ h) (z ≫ ν) (by simp [h₃.w])).1 (by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Hom.comp_apply, hzw]
      exact hw)
    have e' : z = z ≫ gT ≫ τ j := h₃.hom_ext (by simp [e, hh]) (by simp [hτ])
    refine Set.mem_iUnion.2 ⟨j, gT w, ?_⟩
    rw [← hzw t₀, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← e']

theorem range_subset_range (h₁ : IsPullback φ g₁ α π) (h₂ : IsPullback ψ gY g₁ q) (hσ : ∀ j, σ j ≫ gY = 𝟙 Y)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q →
      Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) = Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ))
    {k : Type} [Field k] (y y' : Sp k ⟶ Y) (e : y ≫ q ≫ π = y' ≫ q ≫ π)
    (H : ∀ u u' : Sp k ⟶ G₁, u ≫ g₁ = y ≫ q → u' ≫ g₁ = y' ≫ q → u ≫ φ = u' ≫ φ →
      Set.range u ⊆ ψ '' (⋃ j, Set.range (σ j)) → Set.range u' ⊆ ψ '' (⋃ j, Set.range (σ j))) :
    Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) ⊆ Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ) := by
  have hs : ∀ j, σ j ≫ ψ ≫ g₁ = q := fun j => by rw [h₂.w, reassoc_of% hσ j]
  rintro _ ⟨j, rfl⟩
  have w : (y ≫ σ j ≫ ψ ≫ φ) ≫ α = (y' ≫ q) ≫ π := by
    simp only [Category.assoc, h₁.w, reassoc_of% hs, e]
  have hu : (y ≫ σ j ≫ ψ) ≫ g₁ = y ≫ q := by simp only [Category.assoc, hs]
  have := H (y ≫ σ j ≫ ψ) (h₁.lift _ _ w) hu (h₁.lift_snd _ _ _) (by simp)
    ((range_subset_iff h₁ h₂ hσ hfib y _ hu).2 ⟨j, rfl⟩)
  obtain ⟨j', e'⟩ := (range_subset_iff h₁ h₂ hσ hfib y' _ (h₁.lift_snd _ _ w)).1 this
  refine ⟨j', ?_⟩
  have := h₁.lift_fst _ _ w
  rw [e'] at this
  simpa using this

end

end GlobalTheory.HkFam.KerSch

namespace GlobalTheory.HkFam

open KerSch

theorem exists_heckeKernelScheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), admitted l 𝔓 p → ∃ (Hk : Scheme.{0}) (π₁ : Hk ⟶ Xo.X) (o₁ : Ob D l (π₁ ≫ Xo.s)) (m₁ : ObjMap o₁ Xo.univ π₁) (K : Set o₁.t.G.left), IsFinite π₁ ∧ Etale π₁ ∧ HeckeSet D o₁.t 𝔓 p i K ∧ EtSet o₁.t.G K ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (z : Sp k ⟶ Hk) (z' : Sp k ⟶ Hk), z ≫ π₁ = z' ≫ π₁ → (∀ (u : Over.mk z ⟶ o₁.t.G) (u' : Over.mk z' ⟶ o₁.t.G), u.left ≫ m₁.toSABMap.φ = u'.left ≫ m₁.toSABMap.φ → (Set.range u.left ⊆ K ↔ Set.range u'.left ⊆ K)) → z = z') ∧ ∀ (T : Scheme.{0}) (s : T ⟶ Sp (KA l)) (o : Ob D l s) (f : T ⟶ Xo.X) (mu : ObjMap o Xo.univ f) (τ : Fin (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) → (𝟙_ (Over T) ⟶ o.t.G)) (K' : Set o.t.G.left), Lists (p ^ 2) τ K' → HeckeSet D o.t 𝔓 p i K' → ∃ (h : T ⟶ Hk) (n : ObjMap o o₁ h), h ≫ π₁ = f ∧ n.toSABMap.φ ≫ m₁.toSABMap.φ = mu.toSABMap.φ ∧ K' = n.toSABMap.φ ⁻¹' K := by
  intro E _ _ _ H D l Xo 𝔓 p i hA
  obtain ⟨Y, Hk, q, π₁, oY, m, σ, K, hqf, hqe, hqs, hπf, hπe, hL, hK, hfib, huniv⟩ :=
    GlobalTheory.T.exists_heckeKernelLists_modulo_permutations E H D l Xo 𝔓 p i (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) hA
  obtain ⟨o₁, ⟨m₁⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (π₁ ≫ Xo.s) π₁ rfl rfl
    (by simp [spMap]) Xo.univ
  obtain ⟨m', hm'⟩ := ((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ oY).2 π₁ q m₁).2 m
  have h₁ := m₁.cart.1
  have h₂ := m'.cart.1
  have hσ : ∀ j, (σ j).left ≫ oY.t.G.hom = 𝟙 Y := fun j => Over.w (σ j)
  rw [hm'] at hfib
  have hfib' := fun (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y) e => ((hfib k y y').1 e).1
  have hKσ := hL.2.1
  have hpre : K = m'.toSABMap.φ ⁻¹' (m'.toSABMap.φ '' K) := by
    have := preimage_eq (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' (h := 𝟙 Y) (ν := m'.toSABMap.φ)
      (gT := oY.t.G.hom) (by simpa using h₂) (τ := fun j => (σ j).left) hσ (fun j => by simp)
    rw [hKσ]; exact this
  refine ⟨Hk, π₁, o₁, m₁, m'.toSABMap.φ '' K, hπf, hπe, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.heckeSet_descends E H D l 𝔓 p i _ _ _ _ q o₁ oY m' _ hA hqs (hpre ▸ hK)
  · refine etSet_of_lists _ _ q _ _ m'.toSABMap.φ (p ^ 2) _ σ _ (ObjDim.isAbelianScheme o₁) m'.cart ?_ hqf hqe hqs
      (hpre ▸ hL)
    have := ((baseKA l).unit (p ^ 2) (pow_pos hA.2.2.1.pos 2)).map
      ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ (π₁ ≫ Xo.s).appTop).hom
    rwa [map_natCast] at this
  · intro k _ _ z z' e h
    obtain ⟨y, rfl⟩ := exists_lift_of_finite q z
    obtain ⟨y', rfl⟩ := exists_lift_of_finite q z'
    rw [Category.assoc, Category.assoc] at e
    rw [hKσ] at h
    refine (hfib k y y').2 ⟨subset_antisymm ?_ ?_, e⟩
    · exact range_subset_range (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' y y' e fun u u' hu hu' e' =>
        (h (Over.homMk u hu) (Over.homMk u' hu') e').1
    · exact range_subset_range (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' y' y e.symm fun u u' hu hu' e' =>
        (h (Over.homMk u' hu') (Over.homMk u hu) e'.symm).2
  · intro T s o f mu τ K' hL' hK'
    obtain ⟨h, hf, hh⟩ := huniv T f o.t mu.toSABMap τ K' hL' hK'
    rw [← Category.assoc] at hf
    subst hf
    obtain ⟨n, hn⟩ := ((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ o).2 π₁ (h ≫ q) m₁).2 mu
    have h₃ := n.cart.1
    have hτ : ∀ j, (τ j).left ≫ o.t.G.hom = 𝟙 T := fun j => Over.w (τ j)
    refine ⟨h ≫ q, n, rfl, hn.symm, ?_⟩
    rw [hL'.2.1, hKσ]
    refine preimage_eq (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' h₃ (τ := fun j => (τ j).left) hτ fun j => ?_
    refine h₁.hom_ext ?_ ?_
    · have := hh j
      rw [hm', hn] at this
      simpa using this.symm
    · have e₁ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (h ≫ q)) (hτ j))
      have e₂ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) (hσ j))
      simp only [Category.assoc, h₃.w, h₂.w]
      exact (e₁.trans (Category.id_comp _)).trans (congrArg (h ≫ ·) (e₂.trans (Category.id_comp _)).symm)

end GlobalTheory.HkFam

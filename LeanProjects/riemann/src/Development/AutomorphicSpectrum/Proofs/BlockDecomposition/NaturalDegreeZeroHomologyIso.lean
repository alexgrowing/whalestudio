import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

namespace GlobalTheory.CompanionTheory.Hodge.DimShift

variable {R : Type} [CommRing R]

def h0ι (K : CochainComplex (ModuleCat.{0} R) ℕ) : K.homology 0 ⟶ K.X 0 :=
  K.isoHomologyπ₀.inv ≫ K.iCycles 0

instance h0ι_mono (K : CochainComplex (ModuleCat.{0} R) ℕ) : Mono (h0ι K) := by
  unfold h0ι
  infer_instance

theorem h0ι_d (K : CochainComplex (ModuleCat.{0} R) ℕ) : h0ι K ≫ K.d 0 1 = 0 := by
  unfold GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι
  rw [Category.assoc, HomologicalComplex.iCycles_d, comp_zero]

theorem h0ι_lift (K : CochainComplex (ModuleCat.{0} R) ℕ) {A : ModuleCat.{0} R} (f : A ⟶ K.X 0)
    (hf : f ≫ K.d 0 1 = 0) : ∃ g : A ⟶ K.homology 0, g ≫ h0ι K = f := by
  refine ⟨K.liftCycles f 1 (CochainComplex.next ℕ 0) hf ≫ K.isoHomologyπ₀.hom, ?_⟩
  unfold GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι
  rw [Category.assoc, Iso.hom_inv_id_assoc, HomologicalComplex.liftCycles_i]

theorem h0ι_naturality {K L : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ L) :
    HomologicalComplex.homologyMap φ 0 ≫ h0ι L = h0ι K ≫ φ.f 0 := by
  unfold GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι
  rw [← Category.assoc, CochainComplex.isoHomologyπ₀_inv_naturality, Category.assoc,
    HomologicalComplex.cyclesMap_i, Category.assoc]

theorem exists_h0_iso (K L : CochainComplex (ModuleCat.{0} R) ℕ) (ε : K.X 0 ≅ L.X 0)
    (h : ∀ x : K.X 0, (K.d 0 1).hom x = 0 ↔ (L.d 0 1).hom (ε.hom.hom x) = 0) :
    ∃ e : K.homology 0 ≅ L.homology 0, e.hom ≫ h0ι L = h0ι K ≫ ε.hom := by
  have hK : ∀ x, (K.d 0 1).hom ((GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι K).hom x) = 0 := fun x => by
    have := congrArg (fun φ => ModuleCat.Hom.hom φ x) (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι_d K)
    first
      | exact this
      | simpa using this
  have hL : ∀ y, (L.d 0 1).hom ((GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι L).hom y) = 0 := fun y => by
    have := congrArg (fun φ => ModuleCat.Hom.hom φ y) (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι_d L)
    first
      | exact this
      | simpa using this
  have h1 : (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι K ≫ ε.hom) ≫ L.d 0 1 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    first
      | exact (h _).1 (hK x)
      | simpa using (h _).1 (hK x)
  have h2 : (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι L ≫ ε.inv) ≫ K.d 0 1 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    have hε : ε.hom.hom (ε.inv.hom ((GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι L).hom y)) = (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι L).hom y := by
      show (ε.inv ≫ ε.hom).hom _ = _
      rw [ε.inv_hom_id]
      rfl
    have := (h (ε.inv.hom ((GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι L).hom y))).2 (by rw [hε]; exact hL y)
    first
      | exact this
      | simpa using this
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι_lift L (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι K ≫ ε.hom) h1
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι_lift K (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι L ≫ ε.inv) h2
  refine ⟨⟨f₁, f₂, ?_, ?_⟩, hf₁⟩
  · rw [← cancel_mono (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι K), Category.assoc, hf₂, ← Category.assoc, hf₁]
    simp
  · rw [← cancel_mono (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι L), Category.assoc, hf₁, ← Category.assoc, hf₂]
    simp

theorem nonempty_iso_of_middle_isZero {S : ShortComplex (CochainComplex (ModuleCat.{0} R) ℕ)}
    (hS : S.ShortExact) (k : ℕ) (h₁ : IsZero (S.X₂.homology (k + 1)))
    (h₂ : IsZero (S.X₂.homology (k + 2))) :
    Nonempty (S.X₃.homology (k + 1) ≅ S.X₁.homology (k + 2)) := by
  have r : (ComplexShape.up ℕ).Rel (k + 1) (k + 2) := rfl
  haveI : Mono (hS.δ (k + 1) (k + 2) r) :=
    (hS.homology_exact₃ (k + 1) (k + 2) r).mono_g (h₁.eq_of_src _ _)
  haveI : Epi (hS.δ (k + 1) (k + 2) r) :=
    (hS.homology_exact₁ (k + 1) (k + 2) r).epi_f (h₂.eq_of_tgt _ _)
  haveI : IsIso (hS.δ (k + 1) (k + 2) r) := isIso_of_mono_of_epi _
  exact ⟨asIso (hS.δ (k + 1) (k + 2) r)⟩

theorem nonempty_iso_h1 {S₁ S₂ : ShortComplex (CochainComplex (ModuleCat.{0} R) ℕ)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (z₁ : IsZero (S₁.X₂.homology 1)) (z₂ : IsZero (S₂.X₂.homology 1))
    (eI : S₁.X₂.homology 0 ≅ S₂.X₂.homology 0) (eQ : S₁.X₃.homology 0 ≅ S₂.X₃.homology 0)
    (w : HomologicalComplex.homologyMap S₁.g 0 ≫ eQ.hom =
      eI.hom ≫ HomologicalComplex.homologyMap S₂.g 0) :
    Nonempty (S₁.X₁.homology 1 ≅ S₂.X₁.homology 1) := by
  have hr : (ComplexShape.up ℕ).Rel 0 1 := rfl
  haveI : Epi (hS₁.δ 0 1 hr) := (hS₁.homology_exact₁ 0 1 hr).epi_f (z₁.eq_of_tgt _ _)
  haveI : Epi (hS₂.δ 0 1 hr) := (hS₂.homology_exact₁ 0 1 hr).epi_f (z₂.eq_of_tgt _ _)
  have hc₁ := (hS₁.homology_exact₃ 0 1 hr).gIsCokernel
  have hc₂ := (hS₂.homology_exact₃ 0 1 hr).gIsCokernel
  have w' : HomologicalComplex.homologyMap S₂.g 0 ≫ eQ.inv =
      eI.inv ≫ HomologicalComplex.homologyMap S₁.g 0 := by
    rw [← cancel_epi eI.hom, ← Category.assoc, ← w]
    simp
  obtain ⟨φ, hφ⟩ := CokernelCofork.IsColimit.desc' hc₁ (eQ.hom ≫ hS₂.δ 0 1 hr) (by
    show HomologicalComplex.homologyMap S₁.g 0 ≫ eQ.hom ≫ hS₂.δ 0 1 hr = 0
    rw [← Category.assoc, w, Category.assoc, hS₂.comp_δ 0 1 hr, comp_zero])
  obtain ⟨ψ, hψ⟩ := CokernelCofork.IsColimit.desc' hc₂ (eQ.inv ≫ hS₁.δ 0 1 hr) (by
    show HomologicalComplex.homologyMap S₂.g 0 ≫ eQ.inv ≫ hS₁.δ 0 1 hr = 0
    rw [← Category.assoc, w', Category.assoc, hS₁.comp_δ 0 1 hr, comp_zero])
  have hφ' : hS₁.δ 0 1 hr ≫ φ = eQ.hom ≫ hS₂.δ 0 1 hr := hφ
  have hψ' : hS₂.δ 0 1 hr ≫ ψ = eQ.inv ≫ hS₁.δ 0 1 hr := hψ
  refine ⟨⟨φ, ψ, ?_, ?_⟩⟩
  · rw [← cancel_epi (hS₁.δ 0 1 hr), ← Category.assoc, hφ', Category.assoc, hψ']
    simp
  · rw [← cancel_epi (hS₂.δ 0 1 hr), ← Category.assoc, hψ', Category.assoc, hφ']
    simp

theorem homology_nonempty_iso : ∀ {R : Type} [CommRing R] {𝒜 : Type 1} [Category.{0} 𝒜] [HasZeroMorphisms 𝒜]
    (T₁ T₂ : 𝒜 ⥤ CochainComplex (ModuleCat.{0} R) ℕ) [T₁.PreservesZeroMorphisms] [T₂.PreservesZeroMorphisms]
    (ε : ∀ G, (T₁.obj G).X 0 ≅ (T₂.obj G).X 0),
    (∀ {G G' : 𝒜} (φ : G ⟶ G'), (T₁.map φ).f 0 ≫ (ε G').hom = (ε G).hom ≫ (T₂.map φ).f 0) →
    (∀ (G : 𝒜) (x : (T₁.obj G).X 0),
      ((T₁.obj G).d 0 1).hom x = 0 ↔ ((T₂.obj G).d 0 1).hom ((ε G).hom.hom x) = 0) →
    (∀ G : 𝒜, ∃ (I Q : 𝒜) (i : G ⟶ I) (p : I ⟶ Q) (w : i ≫ p = 0),
      ((ShortComplex.mk i p w).map T₁).ShortExact ∧ ((ShortComplex.mk i p w).map T₂).ShortExact ∧
      ∀ n, IsZero ((T₁.obj I).homology (n + 1)) ∧ IsZero ((T₂.obj I).homology (n + 1))) →
    ∀ (n : ℕ) (G : 𝒜), Nonempty ((T₁.obj G).homology n ≅ (T₂.obj G).homology n) := by
  intro R _ 𝒜 _ _ T₁ T₂ _ _ ε hnat hker hres
  have h0 : ∀ G, ∃ e : (T₁.obj G).homology 0 ≅ (T₂.obj G).homology 0,
      e.hom ≫ GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι (T₂.obj G) = GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι (T₁.obj G) ≫ (ε G).hom :=
    fun G => GlobalTheory.CompanionTheory.Hodge.DimShift.exists_h0_iso _ _ (ε G) (hker G)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G
    obtain ⟨I, Q, i, p, w, hS₁, hS₂, hI⟩ := hres G
    rcases n with _ | _ | k
    · obtain ⟨e, -⟩ := h0 G
      exact ⟨e⟩
    · obtain ⟨eI, heI⟩ := h0 I
      obtain ⟨eQ, heQ⟩ := h0 Q
      refine GlobalTheory.CompanionTheory.Hodge.DimShift.nonempty_iso_h1 hS₁ hS₂ (hI 0).1 (hI 0).2 eI eQ ?_
      show HomologicalComplex.homologyMap (T₁.map p) 0 ≫ eQ.hom =
        eI.hom ≫ HomologicalComplex.homologyMap (T₂.map p) 0
      rw [← cancel_mono (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι (T₂.obj Q))]
      simp only [Category.assoc, heQ, GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι_naturality,
        reassoc_of% (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι_naturality (T₁.map p)), reassoc_of% heI, hnat]
    · obtain ⟨a⟩ := GlobalTheory.CompanionTheory.Hodge.DimShift.nonempty_iso_of_middle_isZero hS₁ k (hI k).1 (hI (k + 1)).1
      obtain ⟨b⟩ := GlobalTheory.CompanionTheory.Hodge.DimShift.nonempty_iso_of_middle_isZero hS₂ k (hI k).2 (hI (k + 1)).2
      obtain ⟨c⟩ := ih (k + 1) (by omega) Q
      exact ⟨a.symm ≪≫ c ≪≫ b⟩

end GlobalTheory.CompanionTheory.Hodge.DimShift

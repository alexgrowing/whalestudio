import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.LocallyExactCech

open CategoryTheory Limits AlgebraicGeometry Opposite UpperTheory.Et

private theorem typeSheaf {τ : GrothendieckTopology Scheme.{0}} {R : Type} [CommRing R] {M : PMod R}
    (h : Presheaf.IsSheaf τ M) : Presieve.IsSheaf τ (M ⋙ forget _) := by
  have h1 := (Presheaf.isSheaf_iff_isSheaf_comp τ M (forget _)).mp h
  exact (isSheaf_iff_isSheaf_of_type τ _).mp h1

private theorem ap_rs {R : Type} [CommRing R] {M N : PMod R} (α : M ⟶ N) {V U : Scheme.{0}} (g : V ⟶ U)
    (y : sec M U) : ap α (rs M g y) = rs N g (ap α y) :=
  ConcreteCategory.congr_hom (α.naturality g.op) y

private theorem rs_comp {R : Type} [CommRing R] (M : PMod R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U)
    (z : sec M U) : rs M (f ≫ g) z = rs M f (rs M g z) := by
  simp [rs]

private theorem loc_mono {τ : GrothendieckTopology Scheme.{0}} {U : Scheme.{0}}
    {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : LocT τ U P) (hPQ : ∀ V g, P V g → Q V g) : LocT τ U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

private theorem loc_and {τ : GrothendieckTopology Scheme.{0}} {U : Scheme.{0}}
    {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : LocT τ U P) (h' : LocT τ U Q) :
    LocT τ U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨T, hT, hQ⟩ := h'
  exact ⟨S ⊓ T, τ.intersection_covering hS hT, fun V g hg => ⟨hP V g hg.1, hQ V g hg.2⟩⟩

private theorem loc_top {τ : GrothendieckTopology Scheme.{0}} {U : Scheme.{0}}
    {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : LocT τ U P :=
  ⟨⊤, τ.top_mem U, fun V g _ => h V g⟩

theorem UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback :
    ∀ (τ : GrothendieckTopology Scheme.{0}),
    (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ V g, P V g) → LocT τ U P) ∧
    (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), LocT τ U P → (∀ V g, P V g → Q V g) → LocT τ U Q) ∧
    (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), LocT τ U P → LocT τ U Q → LocT τ U fun V g => P V g ∧ Q V g) ∧
    (∀ (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), LocT τ U P → LocT τ W fun V g => P V (g ≫ k)) ∧
    (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), LocT τ U (fun V g => LocT τ V fun W k => P W (k ≫ g)) → LocT τ U P) ∧
    (∀ (U : Scheme.{0}) (ι : Type 1) (s : Finset ι) (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ i ∈ s, LocT τ U (P i)) → LocT τ U fun V g => ∀ i ∈ s, P i V g) ∧
    (∀ (R : Type) [CommRing R] (M : PMod R), Presheaf.IsSheaf τ M → ∀ (U : Scheme.{0}) (z : sec M U), (LocT τ U fun _ g => rs M g z = 0) → z = 0) ∧
    (∀ (R : Type) [CommRing R] (M N : PMod R) (α : M ⟶ N), Presheaf.IsSheaf τ M → Presheaf.IsSheaf τ N → ∀ (U : Scheme.{0}), (∀ (V : Scheme.{0}) (_ : V ⟶ U), Function.Injective (ap α (U := V))) → ∀ z : sec N U, (LocT τ U fun V g => ∃ y : sec M V, ap α y = rs N g z) → ∃ y : sec M U, ap α y = z) := by
  intro τ
  refine ⟨fun U P h => loc_top h, fun U P Q h hPQ => loc_mono h hPQ,
    fun U P Q h h' => loc_and h h', ?_, ?_, ?_, ?_, ?_⟩
  · intro U W k P h
    obtain ⟨S, hS, hP⟩ := h
    exact ⟨S.pullback k, τ.pullback_stable k hS, fun V g hg => hP V (g ≫ k) hg⟩
  · intro U P h
    obtain ⟨S, hS, hP⟩ := h
    choose T hT hTP using hP
    refine ⟨Sieve.bind S.arrows (fun V g hg => T V g hg), τ.bind_covering hS (fun V g hg => hT V g hg), ?_⟩
    rintro V f ⟨W, f', g, hg, hf', rfl⟩
    exact hTP W g hg V f' hf'
  · intro U ι s P h
    classical
    induction s using Finset.induction_on with
    | empty => exact loc_top fun V g i hi => absurd hi (Finset.notMem_empty i)
    | insert a s ha ih =>
      have h1 := h a (Finset.mem_insert_self a s)
      have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      refine loc_mono (loc_and h1 h2) ?_
      rintro V g ⟨hA, hB⟩ i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hA
      · exact hB i hi
  · intro R _ M hM U z hz
    obtain ⟨S, hS, hP⟩ := hz
    have hM' := typeSheaf hM
    refine (hM' S hS).isSeparatedFor.ext ?_
    intro V g hg
    change rs M g z = (ModuleCat.Hom.hom (M.map g.op)) 0
    rw [hP V g hg, map_zero]
  · intro R _ M N α hM hN U hinj z hz
    obtain ⟨S, hS, hP⟩ := hz
    choose y hy using hP
    have hM' := typeSheaf hM
    have hN' := typeSheaf hN
    let x : Presieve.FamilyOfElements (M ⋙ forget _) S.arrows := fun V g hg => y V g hg
    have hx : x.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ he
      apply hinj Z (g₁ ≫ f₁)
      change ap α (rs M g₁ (y Y₁ f₁ h₁)) = ap α (rs M g₂ (y Y₂ f₂ h₂))
      rw [ap_rs, ap_rs, hy, hy, ← rs_comp, ← rs_comp, he]
    obtain ⟨t, ht, -⟩ := hM' S hS x hx
    refine ⟨t, (hN' S hS).isSeparatedFor.ext ?_⟩
    intro V g hg
    change rs N g (ap α t) = rs N g z
    rw [← ap_rs]
    change ap α ((M ⋙ forget _).map g.op t) = rs N g z
    rw [ht g hg]
    exact hy V g hg

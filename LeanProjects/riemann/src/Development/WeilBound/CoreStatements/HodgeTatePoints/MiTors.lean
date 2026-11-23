import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tors ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

namespace PositivityTheory.HtPt.Mi

section Cat
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

omit [BraidedCategory C] in

theorem isMonHom_of_mul {A B : C} [GrpObj A] [GrpObj B] (j : A ⟶ B)
    (h : ∀ (Y : C) (y z : Y ⟶ A), (y * z) ≫ j = (y ≫ j) * (z ≫ j)) : IsMonHom j := by
  constructor
  · have h1 := h (𝟙_ C) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ C ⟶ A) ≫ j = 1 := by
      have := h1
      exact (left_eq_mul.1 this)
    simpa [Hom.one_def] using h2
  · have h1 := h (A ⊗ A) (fst A A) (snd A A)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h1
    rw [h1]
    congr 1
    ext <;> simp

theorem isPullback_of_kernel {A B : C} [GrpObj B] [IsCommMonObj B] {N : ℕ} (j : A ⟶ B)
    (inj : ∀ (Y : C) (y z : Y ⟶ A), y ≫ j = z ≫ j → y = z)
    (ker : ∀ (Y : C) (g : Y ⟶ B), g ^ N = 1 ↔ ∃ y : Y ⟶ A, y ≫ j = g) :
    IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B] := by
  have hw : j ≫ (𝟙 B) ^ N = toUnit A ≫ η[B] := by
    rw [comp_pow_id, (ker A j).2 ⟨𝟙 _, Category.id_comp _⟩, Hom.one_def]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => ((ker _ s.fst).1 ?_).choose) (fun s => ?_) (fun s => ?_)
    (fun s m h1 _ => ?_)⟩⟩
  · rw [← comp_pow_id s.fst, Hom.one_def, ← toUnit_unique s.snd (toUnit _)]
    exact s.condition
  · exact Exists.choose_spec (p := fun y => y ≫ j = s.fst) _
  · exact toUnit_unique _ _
  · apply inj
    rw [h1]
    exact (Exists.choose_spec (p := fun y => y ≫ j = s.fst) _).symm

omit [BraidedCategory C] in
theorem pow_comp {Y A B : C} [GrpObj A] [GrpObj B] (g : Y ⟶ A) (a : A ⟶ B) [IsMonHom a] (n : ℕ) :
    (g ^ n) ≫ a = (g ≫ a) ^ n := by
  induction n with
  | zero => simp [MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

end Cat

section Tors
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T} {S : Scheme.{0}}
  {G : Over S} [GrpObj G] [IsCommMonObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}

theorem kernel_of_tors (h : Γ.IsTorsionAlong G x N i) :
    ∃ j : Γ.G ⟶ (Over.pullback x).obj G, j.left ≫ pullback.fst G.hom x = i ∧
      IsPullback j (toUnit Γ.G) ((𝟙 ((Over.pullback x).obj G)) ^ N) η[(Over.pullback x).obj G] := by
  let g : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have hj : (toPull x G g).left ≫ pullback.fst G.hom x = i := toPull_fst x G g
  refine ⟨toPull x G g, hj, isPullback_of_kernel _ (fun Y y z e => h.inj Y y z ?_) (fun Y c => ?_)⟩
  · rw [← hj, ← Category.assoc, ← Category.assoc, ← Over.comp_left, e, Over.comp_left]
  · have h1 : c ^ N = 1 ↔ ofPull x G c ^ N = 1 := by
      have h2 := map_pow (toPullHom x G Y) (ofPull x G c) N
      have h3 : toPullHom x G Y (ofPull x G c) = c := toPull_ofPull x G c
      rw [h3] at h2
      rw [← h2]
      constructor
      · intro e
        rw [← map_one (toPullHom x G Y)] at e
        exact toPull_inj e
      · intro e
        rw [e, map_one]
    rw [h1, h.kernel]
    refine exists_congr fun y => ⟨fun e => hom_ext_pull ?_, fun e => ?_⟩
    · rw [Over.comp_left, Category.assoc, hj, e]; rfl
    · rw [← hj, ← Category.assoc, ← Over.comp_left, e]; rfl

end Tors

theorem kernel_isPullback {Z : Scheme.{0}} {A B D : Over Z} [GrpObj D] {j : A ⟶ B} {q : B ⟶ D}
    (hp : IsPullback j (toUnit A) q η[D]) : IsPullback j.left A.hom q.left (η[D]).left := by
  have hl := hp.map (Over.forget Z)
  have hA : (toUnit A).left = A.hom := by simpa using Over.w (toUnit A)
  rw [← hA]; exact hl

theorem isClosedImmersion_unit {Z : Scheme.{0}} (B : Over Z) [GrpObj B] [IsSeparated B.hom] :
    IsClosedImmersion (η[B]).left := by
  have : IsClosedImmersion ((η[B]).left ≫ B.hom) := by
    have : (η[B]).left ≫ B.hom = 𝟙 _ := by simpa using Over.w η[B]
    rw [this]; infer_instance
  exact IsClosedImmersion.of_comp _ B.hom

theorem torsion_finite : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → IsProper (pullback.snd G.hom x) → IsFinite Γ.G.hom := by
  intro R _ _ T _ _ Γ S G _ _ x N i h hprop
  obtain ⟨j, -, hp⟩ := kernel_of_tors h
  have : IsProper ((Over.pullback x).obj G).hom := hprop
  have hj : IsClosedImmersion j.left :=
    MorphismProperty.of_isPullback (kernel_isPullback hp).flip (isClosedImmersion_unit _)
  have : IsProper Γ.G.hom := by rw [← Over.w j]; infer_instance
  have := Γ.quasiFinite
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

theorem torsion_etale : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → IsUnit (N : R) → Etale Γ.G.hom := by
  intro R _ _ T _ _ Γ S G _ _ x N i h _ hN
  obtain ⟨j, -, hp⟩ := kernel_of_tors h
  have hN' : IsUnit (N : Γ(Spec (CommRingCat.of R), ⊤)) := by
    simpa using hN.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have e1 : FormallyUnramified ((𝟙 ((Over.pullback x).obj G)) ^ N).left :=
    GlobalTheory.formallyUnramified_mulA _ ((Over.pullback x).obj G) N hN'
  have : FormallyUnramified Γ.G.hom := MorphismProperty.of_isPullback (kernel_isPullback hp) e1
  have := Γ.flat
  have := Γ.finPres
  exact Etale.of_formallyUnramified_of_flat _

theorem torsion_end : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (a : G ⟶ G) [IsMonHom a], ∃ a' : Γ.G ⟶ Γ.G, IsMonHom a' ∧ a'.left ≫ i = i ≫ a.left := by
  intro R _ _ T _ _ Γ S G _ _ x N i h a _
  let g : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have hg : g ^ N = 1 := (h.kernel Γ.G g).2 ⟨𝟙 _, Category.id_comp _⟩
  have hga : (g ≫ a) ^ N = 1 := by rw [← pow_comp, hg, MonObj.one_comp]
  obtain ⟨a', ha'⟩ := (h.kernel Γ.G (g ≫ a)).1 hga
  replace ha' : a'.left ≫ i = i ≫ a.left := ha'
  refine ⟨a', isMonHom_of_mul _ fun Y y z => h.inj Y _ _ ?_, ha'⟩
  let p : (Y ⟶ Γ.G) → (Over.mk (Y.hom ≫ x) ⟶ G) := fun y => Over.homMk (y.left ≫ i) (by
    simp only [Over.mk_hom, Category.assoc, h.isOver]; rw [← Category.assoc, Over.w])
  have hp : ∀ y, (p y).left = y.left ≫ i := fun _ => rfl
  have hpa : ∀ y, (p y ≫ a).left = (y ≫ a').left ≫ i := fun y => by
    rw [Over.comp_left, Over.comp_left, hp, Category.assoc, Category.assoc, ha']
  rw [← h.mul Y _ _ _ _ (hpa y) (hpa z), ← MonObj.mul_comp, Over.comp_left, Over.comp_left,
    h.mul Y _ _ _ _ (hp y) (hp z), Category.assoc, Category.assoc, ha']

end PositivityTheory.HtPt.Mi

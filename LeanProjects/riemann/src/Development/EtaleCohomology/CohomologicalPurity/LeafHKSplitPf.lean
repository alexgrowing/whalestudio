import Development.EtaleCohomology.CohomologicalPurity.LeafRelPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

section Gen
variable {C : Type*} [Category C] [Abelian C] {A B D Q I : CochainComplex C ℤ}

def hsCok (f : A ⟶ B) (l r : B ⟶ D) (hpo : IsPushout f f l r) (p : D ⟶ cokernel f)
    (hl : l ≫ p = cokernel.π f) (hr : r ≫ p = 0) : IsColimit (CokernelCofork.ofπ p hr) :=
  CokernelCofork.IsColimit.ofπ p hr
    (fun g' _ => cokernel.desc f (l ≫ g') (by rw [← Category.assoc, hpo.w, Category.assoc]; simp [*]))
    (fun g' eq' => by
      apply hpo.hom_ext
      · rw [← Category.assoc, hl, cokernel.π_desc]
      · rw [← Category.assoc, hr, zero_comp, eq'])
    (fun g' eq' m hm => by
      apply (cancel_epi (cokernel.π f)).1
      rw [cokernel.π_desc, ← hl, Category.assoc, hm])

def hsCokDeg {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hr)) (k : ℤ) :
    IsColimit ((CokernelCofork.ofπ p hr).map (HomologicalComplex.eval C _ k)) :=
  CokernelCofork.mapIsColimit _ hc _

def hsCokDeg' {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hr)) (k : ℤ) :
    IsColimit (CokernelCofork.ofπ (f := r.f k) (p.f k) (by rw [← HomologicalComplex.comp_f, hr]; rfl)) :=
  hsCokDeg hr hc k

theorem hsFac {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hr)) {m : ℤ}
    (z : Cochain D I m) (hz : (Cochain.ofHom r).comp z (zero_add m) = 0) :
    ∃ y : Cochain Q I m, (Cochain.ofHom p).comp y (zero_add m) = z := by
  have key : ∀ a b (h : a + m = b), r.f a ≫ z.v a b h = 0 := fun a b h => by
    have := congrArg (fun w => w.v a b h) hz
    simpa [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using this
  refine ⟨Cochain.mk (fun a b h => (CokernelCofork.IsColimit.desc' (hsCokDeg' hr hc a) (z.v a b h) (key a b h)).1), ?_⟩
  ext a b h
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
  exact (CokernelCofork.IsColimit.desc' (hsCokDeg' hr hc a) (z.v a b h) (key a b h)).2

theorem hsCancel {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hr)) {m : ℤ}
    (y₁ y₂ : Cochain Q I m) (h : (Cochain.ofHom p).comp y₁ (zero_add m) = (Cochain.ofHom p).comp y₂ (zero_add m)) :
    y₁ = y₂ := by
  ext a b hab
  have := congrArg (fun w => w.v a b hab) h
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at this
  have : Epi (p.f a) := epi_of_isColimit_cofork (hsCokDeg' hr hc a)
  exact (cancel_epi (p.f a)).1 ‹_›

theorem hsRS {r : B ⟶ D} {s : D ⟶ B} (hrs : r ≫ s = 𝟙 _) {m : ℤ} (z : Cochain B I m) :
    (Cochain.ofHom r).comp ((Cochain.ofHom s).comp z (zero_add m)) (zero_add m) = z := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, hrs]
  ext a b h
  simp

theorem hsRP {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) {m : ℤ} (z : Cochain Q I m) :
    (Cochain.ofHom r).comp ((Cochain.ofHom p).comp z (zero_add m)) (zero_add m) = 0 := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, hr, Cochain.ofHom_zero, Cochain.zero_comp]

theorem hsInj {r : B ⟶ D} {s : D ⟶ B} {p : D ⟶ Q} (hrs : r ≫ s = 𝟙 _) (hr : r ≫ p = 0)
    (hc : IsColimit (CokernelCofork.ofπ p hr)) (n : ℤ) :
    Function.Injective (cpre (Cocycle.ofHom p) I n n (zero_add n)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hx
  obtain ⟨β, hβ⟩ := hx
  change δ (n - 1) n β = (Cochain.ofHom p).comp x.1 (zero_add n) at hβ
  obtain ⟨γ, hγ⟩ := hsFac hr hc (β - (Cochain.ofHom s).comp ((Cochain.ofHom r).comp β (zero_add _)) (zero_add _))
    (by rw [Cochain.comp_sub, hsRS hrs, sub_self])
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨γ, hsCancel hr hc _ _ ?_⟩
  rw [← δ_ofHom_comp, hγ, δ_sub, δ_ofHom_comp, δ_ofHom_comp, hβ, hsRP hr, Cochain.comp_zero, sub_zero]

theorem hsExact {r : B ⟶ D} {s : D ⟶ B} {p : D ⟶ Q} (hrs : r ≫ s = 𝟙 _) (hr : r ≫ p = 0)
    (hc : IsColimit (CokernelCofork.ofπ p hr)) (n : ℤ) (x : CohomologyClass D I n)
    (hx : cpre (Cocycle.ofHom r) I n n (zero_add n) x = 0) :
    ∃ y, cpre (Cocycle.ofHom p) I n n (zero_add n) y = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hx
  obtain ⟨β, hβ⟩ := hx
  change δ (n - 1) n β = (Cochain.ofHom r).comp x.1 (zero_add n) at hβ
  obtain ⟨y, hy⟩ := hsFac hr hc (x.1 - δ (n - 1) n ((Cochain.ofHom s).comp β (zero_add _)))
    (by rw [Cochain.comp_sub, δ_ofHom_comp, hsRS hrs, hβ, sub_self])
  have hδ : δ n (n + 1) y = 0 := by
    apply hsCancel hr hc
    rw [← δ_ofHom_comp, hy, δ_sub, δ_δ, Cocycle.δ_eq_zero, sub_zero, Cochain.comp_zero]
  refine ⟨CohomologyClass.mk (Cocycle.mk y (n + 1) rfl hδ), ?_⟩
  change CohomologyClass.mk _ = _
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨-((Cochain.ofHom s).comp β (zero_add _)), ?_⟩
  change _ = (Cochain.ofHom p).comp y (zero_add n) - x.1
  rw [hy, δ_neg]; abel

end Gen

theorem LeafHKSplit_of : LeafHKSplit := by
  intro R _ F n A B D f l r s hpo hrs p hl hr
  have hc := hsCok f l r hpo p hl hr
  exact ⟨hsInj hrs hr hc n, fun x hx => hsExact hrs hr hc n x hx⟩

end LateralTheory.CohomologicalPurity.TubeCut

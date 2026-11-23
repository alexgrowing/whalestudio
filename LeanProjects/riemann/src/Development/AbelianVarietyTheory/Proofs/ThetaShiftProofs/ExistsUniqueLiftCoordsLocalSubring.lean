import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.LiftPoint

open GlobalTheory.Points GlobalTheory.AmpleSpan GlobalTheory.Specialise

section General

variable {A K : Type} [CommRing A] [CommRing K] {j : A →+* K} {X Y : Scheme.{0}} {f : X ⟶ Y} {H : LB X}
  {I : Type} {t : I → LB.Sec H}

theorem exists_lift_of_valR_mem (hj : Function.Injective j) {D : X.Opens} (hD : IsAffineOpen D) (x : Sp K ⟶ X)
    (hx : ⊤ ≤ x ⁻¹ᵁ D) (h : ∀ g, valR x D g ∈ j.range) :
    ∃ ξ : Sp A ⟶ X, ⊤ ≤ ξ ⁻¹ᵁ D ∧ spMap j ≫ ξ = x := by
  choose φ hφ using h
  simp only [valR_eq x D hx] at hφ
  let ψ : Γ(X, D) →+* A := ⟨⟨⟨φ, hj (by simp [hφ])⟩, fun a b => hj (by simp [hφ])⟩, hj (by simp [hφ]),
    fun a b => hj (by simp [hφ])⟩
  refine ⟨_, le_preimage_specMap_fromSpec hD (CommRingCat.ofHom ψ), ?_⟩
  rw [← specMap_valMap_fromSpec hD x hx, ← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext hφ)

theorem ext_of_spMap_comp [IsAffine Y] (hj : Function.Injective j) {ξ ξ' : Sp A ⟶ Y}
    (h : spMap j ≫ ξ = spMap j ≫ ξ') : ξ = ξ' :=
  ext_of_valR (isAffineOpen_top Y) (le_preimage_top _) (le_preimage_top _) fun g => hj (by
    rw [← valR_spMap_comp j ξ ⊤ (le_preimage_top _), ← valR_spMap_comp j ξ' ⊤ (le_preimage_top _), h])

theorem exists_lift [IsAffine Y] [IsLocalRing A] (ht : EmbedsBy f t) (hj : Function.Injective j) {b : Sp A ⟶ Y}
    {x : Sp K ⟶ X} (hb : x ≫ f = spMap j ≫ b) {c : I → A} (h : HasCoords x t fun l => j (c l)) {m : I}
    (hm : IsUnit (c m)) : ∃ ξ : Sp A ⟶ X, ξ ≫ f = b ∧ spMap j ≫ ξ = x ∧ HasCoords ξ t c := by
  obtain ⟨hD, ρ, hρ, hsurj⟩ := ht.2 m
  have hx := h.le_nonzeroLocus (hm.map j)
  obtain ⟨ξ, hξ, e⟩ := exists_lift_of_valR_mem hj hD x hx fun g => by
    obtain ⟨q, rfl⟩ := hsurj g
    rw [valR_eval₂Hom f x hx]
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C, ← valR_eq, hb, valR_spMap_comp j b ⊤ (le_preimage_top _)]
      exact ⟨_, rfl⟩
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p l hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      refine mul_mem hp ⟨c l * hm.unit⁻¹.val, (hm.map j).mul_right_cancel ?_⟩
      rw [h.valR_ratio hx (hρ l), ← map_mul, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]
  refine ⟨ξ, ext_of_spMap_comp hj ?_, e, ?_⟩
  · rw [← Category.assoc, e, hb]
  · have e' : (fun l => valR ξ (Out.nonzeroLocus (t m)) (ρ l) * c m) = c := funext fun l => hj (by
      rw [map_mul, ← valR_spMap_comp j ξ _ hξ, e]
      exact h.valR_ratio hx (hρ l))
    rw [← e']
    exact (hasCoords_ratio hξ hρ).mul_unit hm

end General

theorem le_preimage_powOver {S : Scheme.{0}} (G : Over S) (L : LB G.left) (U : S.Opens) (N : ℕ) {A : Type}
    [CommRing A] (x : Sp A ⟶ (G.hom ⁻¹ᵁ U).toScheme) {j : L.ι} (h : ⊤ ≤ (x ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j) :
    ⊤ ≤ x ⁻¹ᵁ (Out.powOver G L U N).U (fun _ => j) :=
  fun _ hz => Set.mem_iInter.2 fun _ => h hz

theorem existsUnique_lift : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (L : LB G.left) (U : S.Opens) (N n : ℕ) (b : Fin n → LB.Sec (Out.powOver G L U N)) (R K : Type) [CommRing R] [IsLocalRing R] [CommRing K] [IsLocalRing K] (f : R →+* K) (y : Sp R ⟶ S) (x : Sp K ⟶ (G.hom ⁻¹ᵁ U).toScheme) (cf : Fin n → R) (j : L.ι) (u : Kˣ), L.IsLB → IsAffineOpen U → AmpleSpan.EmbedsBy (G.hom ∣_ U) b → Function.Injective f → ⊤ ≤ y ⁻¹ᵁ U → x ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = spMap f ≫ y → ⊤ ≤ (x ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → (∀ i, valR x ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = f (cf i) * u) → (∃ i, IsUnit (cf i)) → ∃! x' : Sp R ⟶ (G.hom ⁻¹ᵁ U).toScheme, x' ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = y ∧ spMap f ≫ x' = x ∧ ∀ j', ⊤ ≤ (x' ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j' → ∃ u' : Rˣ, ∀ i, valR x' ((Out.powOver G L U N).U (fun _ => j')) ((b i).f (fun _ => j')) = cf i * u' := by
  intro S G _ _ L U N n b R K _ _ _ _ f y x cf j u hL hU hb hf hy hxy hj hval ⟨m, hm⟩
  have : IsAffine U := hU
  let y' : Sp R ⟶ U.toScheme := IsOpenImmersion.lift U.ι y (by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨y z, hy trivial⟩, rfl⟩)
  have ey : y' ≫ U.ι = y := IsOpenImmersion.lift_fac _ _ _
  have key : ∀ ξ : Sp R ⟶ (G.hom ⁻¹ᵁ U).toScheme,
      ξ ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = y ↔ ξ ≫ G.hom ∣_ U = y' := fun ξ => by
    rw [← cancel_mono U.ι, ey, Category.assoc, morphismRestrict_ι]
  have hxy' : x ≫ G.hom ∣_ U = spMap f ≫ y' := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, ey, morphismRestrict_ι, hxy]
  obtain ⟨ξ, h₁, h₂, h₃⟩ := exists_lift hb hf hxy' (c := cf)
    ⟨fun _ => j, le_preimage_powOver G L U N x hj, u, hval⟩ hm
  refine ⟨ξ, ⟨(key ξ).2 h₁, h₂, fun j' hj' => h₃.chart (le_preimage_powOver G L U N ξ hj')⟩, ?_⟩
  rintro ξ' ⟨k₁, -, k₃⟩
  obtain ⟨j', hj'⟩ := exists_le_preimage_of_iSup_eq_top (ξ' ≫ (G.hom ⁻¹ᵁ U).ι) hL.cover
  exact HasCoords.ext hb (((key ξ').1 k₁).trans h₁.symm)
    ⟨fun _ => j', le_preimage_powOver G L U N ξ' hj', k₃ j' hj'⟩ h₃ hm

end GlobalTheory.LiftPoint

import Mathlib
import GroundTheory.TateCohomology.DeltaMap
import GroundTheory.TateCohomology.CoindOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits groupCohomology Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

theorem map_one_succ {H : Type u} [Group H] {A : Rep k H} {B : Rep k G}
    (φ : res (1 : G →* H) A ⟶ B) (n : ℕ) : map 1 φ (n + 1) = 0 := by
  let f : PUnit.{u + 1} →* H := 1
  let g : G →* PUnit.{u + 1} := 1
  let ψ : res g (res f A) ⟶ B := ofHom ⟨φ.hom.toLinearMap, fun x => φ.hom.isIntertwining' x⟩
  have h : map 1 φ (n + 1) = map (f.comp g) ((resFunctor g).map (𝟙 (res f A)) ≫ ψ) (n + 1) :=
    map_congr (by ext; rfl) rfl (n + 1)
  rw [h, map_comp, (isZero_groupCohomology_succ_of_subsingleton (res f A) n).eq_zero_of_src
    (map g ψ (n + 1)), Limits.comp_zero]

variable (A : Rep k G) (S : Subgroup G) [S.Normal]

noncomputable abbrev inflation (n : ℕ) :
    groupCohomology (A.quotientToInvariants S) n ⟶ groupCohomology A n :=
  map (QuotientGroup.mk' S) (ofHom (A.ρ.quotientToInvariants_lift S)) n

noncomputable abbrev restriction (n : ℕ) :
    groupCohomology A n ⟶ groupCohomology (res S.subtype A) n :=
  map S.subtype (𝟙 _) n

theorem inflation_comp_restriction (n : ℕ) :
    inflation A S (n + 1) ≫ restriction A S (n + 1) = 0 := by
  rw [← map_comp, Category.comp_id, groupCohomology.congr (QuotientGroup.mk'_comp_subtype S)
    (fun f φ => map f φ (n + 1)), map_one_succ]

@[simps X₁ X₂ X₃ f g]
noncomputable def infResShortComplex (n : ℕ) : ShortComplex (ModuleCat k) where
  X₁ := groupCohomology (A.quotientToInvariants S) (n + 1)
  X₂ := groupCohomology A (n + 1)
  X₃ := groupCohomology (res S.subtype A) (n + 1)
  f := inflation A S (n + 1)
  g := restriction A S (n + 1)
  zero := inflation_comp_restriction A S n

lemma invariants_map_surjective {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (h1 : IsZero (groupCohomology X.X₁ 1)) :
    Function.Surjective ((invariantsFunctor k G).map X.g).hom := by
  have ex := (map_cochainsFunctor_shortExact hX).homology_exact₃ 0 1 rfl
  have e : Epi (map (MonoidHom.id G) X.g 0) := ex.epi_f (h1.eq_of_tgt _ _)
  have hc := map_id_comp_H0Iso_hom X.g
  have e2 : Epi ((H0Iso X.X₂).hom ≫ (invariantsFunctor k G).map X.g) := by
    rw [← hc]; infer_instance
  have e3 := epi_of_epi (H0Iso X.X₂).hom ((invariantsFunctor k G).map X.g)
  exact (ModuleCat.epi_iff_surjective _).1 e3

noncomputable def toCoindOne : A ⟶ coindOne k G A :=
  ofHom ⟨LinearMap.pi fun x => A.ρ x, fun g => by ext a x; simp⟩

lemma toCoindOne_hom_apply (a : A) (x : G) : (toCoindOne A).hom a x = A.ρ x a := rfl

lemma toCoindOne_injective : Function.Injective (toCoindOne A).hom := fun a b h => by
  have h' : A.ρ 1 a = A.ρ 1 b := congrFun h 1
  simpa using h'

instance : Mono (toCoindOne A) := (Rep.mono_iff_injective _).2 (toCoindOne_injective A)

noncomputable abbrev shiftSC : ShortComplex (Rep k G) :=
  ShortComplex.mk (toCoindOne A) (cokernel.π (toCoindOne A)) (cokernel.condition _)

lemma shiftSC_shortExact : (shiftSC A).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  mono_f := inferInstanceAs (Mono (toCoindOne A))
  epi_g := inferInstanceAs (Epi (cokernel.π _))

instance : (quotientToInvariantsFunctor k S).PreservesZeroMorphisms where
  map_zero _ _ := by ext; rfl

noncomputable abbrev shiftSCQ : ShortComplex (Rep k (G ⧸ S)) :=
  (shiftSC A).map (quotientToInvariantsFunctor k S)

lemma shiftSCQ_shortExact (h1 : IsZero (groupCohomology (res S.subtype A) 1)) :
    (shiftSCQ A S).ShortExact where
  mono_f := (Rep.mono_iff_injective _).2 fun x y h =>
    Subtype.ext (toCoindOne_injective A (congrArg Subtype.val h))
  epi_g := (Rep.epi_iff_surjective _).2
    (invariants_map_surjective ((shortExact_res S.subtype).2 (shiftSC_shortExact A)) h1)
  exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k (G ⧸ S)) (ModuleCat k)),
      ShortComplex.moduleCat_exact_iff_ker_sub_range]
    intro x hx
    have hrk := ((shiftSC_shortExact A).exact.map
      (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
    have hx' : x.1 ∈ LinearMap.ker ((shiftSC A).map (forget₂ (Rep k G) (ModuleCat k))).g.hom :=
      congrArg Subtype.val hx
    rw [← hrk] at hx'
    obtain ⟨a, ha⟩ := hx'
    have ha' : (toCoindOne A).hom a = x.1 := ha
    refine ⟨⟨a, fun s => toCoindOne_injective A ?_⟩, Subtype.ext ha'⟩
    refine (hom_comm_apply (toCoindOne A) (s : G) a).trans ?_
    rw [ha']
    exact x.2 s

theorem infRes_step (n : ℕ)
    (ih : ∀ B : Rep k G, (∀ i, 0 < i → i < n + 1 → IsZero (groupCohomology (res S.subtype B) i)) →
      Mono (infResShortComplex B S n).f ∧ (infResShortComplex B S n).Exact)
    (hA : ∀ i, 0 < i → i < n + 2 → IsZero (groupCohomology (res S.subtype A) i)) :
    Mono (infResShortComplex A S (n + 1)).f ∧ (infResShortComplex A S (n + 1)).Exact := by
  have hX := shiftSC_shortExact A
  have hS := (shortExact_res S.subtype).2 hX
  have hQ := shiftSCQ_shortExact A S (hA 1 one_pos (by omega))
  have hC : ∀ i, 0 < i → i < n + 1 →
      IsZero (groupCohomology (res S.subtype (shiftSC A).X₃) i) := by
    intro i hi hin
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have hδ := isIso_δ_of_isZero hS (m + 1) (isZero_res_coindOne k A S m)
      (isZero_res_coindOne k A S (m + 1))
    exact (hA (m + 1 + 1) (by omega) (by omega)).of_iso (@asIso _ _ _ _ _ hδ)
  obtain ⟨ihm, ihe⟩ := ih (shiftSC A).X₃ hC
  have hδQ := isIso_δ_of_isZero hQ (n + 1) (isZero_quotientToInvariants_coindOne k A S n)
    (isZero_quotientToInvariants_coindOne k A S (n + 1))
  have hδX := isIso_δ_of_isZero hX (n + 1) (isZero_coindOne k G A n)
    (isZero_coindOne k G A (n + 1))
  have hδS := isIso_δ_of_isZero hS (n + 1) (isZero_res_coindOne k A S n)
    (isZero_res_coindOne k A S (n + 1))
  let F : (shiftSCQ A S).map (resFunctor (QuotientGroup.mk' S)) ⟶ shiftSC A :=
    { τ₁ := ofHom (A.ρ.quotientToInvariants_lift S)
      τ₂ := ofHom ((coindOne k G A).ρ.quotientToInvariants_lift S)
      τ₃ := ofHom ((shiftSC A).X₃.ρ.quotientToInvariants_lift S)
      comm₁₂ := by ext; rfl
      comm₂₃ := by ext; rfl }
  have h1 : δ hQ (n + 1) (n + 1 + 1) rfl ≫ inflation A S (n + 1 + 1) =
      inflation (shiftSC A).X₃ S (n + 1) ≫ δ hX (n + 1) (n + 1 + 1) rfl :=
    δ_comp_map (QuotientGroup.mk' S) hQ hX F (n + 1) (n + 1 + 1) rfl
  have h2 : δ hX (n + 1) (n + 1 + 1) rfl ≫ restriction A S (n + 1 + 1) =
      restriction (shiftSC A).X₃ S (n + 1) ≫ δ hS (n + 1) (n + 1 + 1) rfl :=
    δ_comp_map_res S.subtype hX (n + 1) (n + 1 + 1) rfl
  let e : infResShortComplex (shiftSC A).X₃ S n ≅ infResShortComplex A S (n + 1) :=
    ShortComplex.isoMk (@asIso _ _ _ _ _ hδQ) (@asIso _ _ _ _ _ hδX) (@asIso _ _ _ _ _ hδS) h1 h2
  refine ⟨?_, (ShortComplex.exact_iff_of_iso e).1 ihe⟩
  have hf : e.inv.τ₁ ≫ (infResShortComplex (shiftSC A).X₃ S n).f ≫ e.hom.τ₂ =
      (infResShortComplex A S (n + 1)).f := by
    rw [← Category.assoc, e.inv.comm₁₂, Category.assoc, ← ShortComplex.comp_τ₂, e.inv_hom_id,
      ShortComplex.id_τ₂, Category.comp_id]
  rw [← hf]
  infer_instance

theorem infResShortComplex_mono_exact (n : ℕ) :
    ∀ A : Rep k G, (∀ i, 0 < i → i < n + 1 → IsZero (groupCohomology (res S.subtype A) i)) →
      Mono (infResShortComplex A S n).f ∧ (infResShortComplex A S n).Exact := by
  induction n with
  | zero => exact fun A _ => ⟨inferInstanceAs (Mono (H1InfRes A S).f), H1InfRes_exact A S⟩
  | succ n ih => exact fun A hA => infRes_step A S n ih hA

variable {A S}

theorem inflation_injective {q : ℕ} (hq : q ≠ 0)
    (hA : ∀ i, 0 < i → i < q → IsZero (groupCohomology (res S.subtype A) i)) :
    Function.Injective (inflation A S q).hom := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  exact (ModuleCat.mono_iff_injective _).1 (infResShortComplex_mono_exact S n A hA).1

theorem range_inflation_eq_ker_restriction {q : ℕ} (hq : q ≠ 0)
    (hA : ∀ i, 0 < i → i < q → IsZero (groupCohomology (res S.subtype A) i)) :
    LinearMap.range (inflation A S q).hom = LinearMap.ker (restriction A S q).hom := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  exact (infResShortComplex_mono_exact S n A hA).2.moduleCat_range_eq_ker

theorem inflation_two_injective (h1 : IsZero (groupCohomology (res S.subtype A) 1)) :
    Function.Injective (inflation A S 2).hom :=
  inflation_injective two_ne_zero fun i hi hi2 => by
    obtain rfl : i = 1 := by omega
    exact h1

theorem range_inflation_two_eq_ker_restriction
    (h1 : IsZero (groupCohomology (res S.subtype A) 1)) :
    LinearMap.range (inflation A S 2).hom = LinearMap.ker (restriction A S 2).hom :=
  range_inflation_eq_ker_restriction two_ne_zero fun i hi hi2 => by
    obtain rfl : i = 1 := by omega
    exact h1

end GroundTheory.GroupCoh

import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FreeHomExtOfCovering
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr.SumEq

end GlobalTheory.EtC.Tr.SumEq

namespace GlobalTheory.EtC.Tr

open CategoryTheory Limits AlgebraicGeometry in
private lemma exists_sigma_ι_apply_eq_of_finite_coprod {σ : Type} [Finite σ] (g : σ → Scheme.{0}) (q : ↥(∐ g)) :
    ∃ k a, (Sigma.ι g k) a = q :=
  (sigmaOpenCover g).exists_eq q

open CategoryTheory Limits AlgebraicGeometry in
private lemma exists_pullback_lift_apply_eq_of_isIso_sigmaDesc {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ}
    {s : Fin m → (V ⟶ Z)} (hc : ∀ j, s j ≫ f = y)
    [IsIso (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y)]
    (p : ↥(pullback f y)) : ∃ k a, pullback.lift (s k) (𝟙 V) (by simp [hc k]) a = p := by
  obtain ⟨q, rfl⟩ := Scheme.Hom.surjective
    (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y) p
  obtain ⟨k, a, rfl⟩ := exists_sigma_ι_apply_eq_of_finite_coprod _ q
  exact ⟨k, a, by rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]⟩

open CategoryTheory Limits AlgebraicGeometry in
private lemma isOpenImmersion_pullback_lift_of_isIso_sigmaDesc {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ}
    {s : Fin m → (V ⟶ Z)} (hc : ∀ j, s j ≫ f = y)
    [IsIso (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y)] (k : Fin m) :
    IsOpenImmersion (pullback.lift (s k) (𝟙 V) (by simp [hc k]) : V ⟶ pullback f y) := by
  rw [← Sigma.ι_desc (fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
    (j : Fin m) → V ⟶ pullback f y) k]
  infer_instance

open CategoryTheory Limits AlgebraicGeometry in
private lemma pullback_snd_lift_id_apply {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} (t : V ⟶ Z)
    (h : t ≫ f = 𝟙 V ≫ y) (a : ↥V) : pullback.snd f y (pullback.lift t (𝟙 V) h a) = a := by
  rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
  rfl

open CategoryTheory Limits AlgebraicGeometry in
private lemma index_eq_of_pullback_lift_apply_eq {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ}
    {s : Fin m → (V ⟶ Z)} (hc : ∀ j, s j ≫ f = y)
    [IsIso (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y)]
    {j j' : Fin m} (a b : ↥V)
    (h : (pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y) a =
      (pullback.lift (s j') (𝟙 V) (by simp [hc j']) : V ⟶ pullback f y) b) :
    j = j' := by
  have h1 : (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y) (Sigma.ι (fun _ : Fin m => V) j a) =
      (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y) (Sigma.ι (fun _ : Fin m => V) j' b) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Sigma.ι_desc, Sigma.ι_desc]
    exact h
  have h2 : (Sigma.ι (fun _ : Fin m => V) j) a = (Sigma.ι (fun _ : Fin m => V) j') b :=
    Scheme.Hom.injective _ h1
  exact congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : Fin m => V) j j' a b).mp (by convert h2))

open CategoryTheory Limits AlgebraicGeometry in
private lemma injective_of_pullback_lift_apply_eq_of_isIso {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m m' : ℕ}
    {s : Fin m → (V ⟶ Z)} {s' : Fin m' → (V ⟶ Z)} (hc : ∀ j, s j ≫ f = y) (hc' : ∀ j, s' j ≫ f = y)
    [IsIso (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y)]
    (x : ↥V) (K : Fin m → Fin m') (A : Fin m → ↥V)
    (hKA : ∀ j, (pullback.lift (s' (K j)) (𝟙 V) (by simp [hc' (K j)]) : V ⟶ pullback f y) (A j) =
      (pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y) x) : Function.Injective K := by
  intro j j' hjj
  have hA : ∀ i, A i = x := fun i => by
    have := congrArg (pullback.snd f y) (hKA i)
    rwa [pullback_snd_lift_id_apply, pullback_snd_lift_id_apply] at this
  refine index_eq_of_pullback_lift_apply_eq hc x x ?_
  rw [← hKA j, ← hKA j', hA, hA]
  have key : ∀ k k' : Fin m', k = k' →
      (pullback.lift (s' k) (𝟙 V) (by simp [hc' k]) : V ⟶ pullback f y) x =
      (pullback.lift (s' k') (𝟙 V) (by simp [hc' k']) : V ⟶ pullback f y) x := by
    rintro k _ rfl
    rfl
  exact key _ _ hjj

open CategoryTheory Limits AlgebraicGeometry in

theorem _root_.GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings : ∀ (R : Type) [CommRing R] {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X}
    {m m' : ℕ} {s : Fin m → (V ⟶ Z)} {s' : Fin m' → (V ⟶ Z)}, _root_.GlobalTheory.EtC.Tr.SplitBy f y s → _root_.GlobalTheory.EtC.Tr.SplitBy f y s' →
    ∑ j, (_root_.GlobalTheory.EtC.free R).map (yoneda.map (s j)) = ∑ j, (_root_.GlobalTheory.EtC.free R).map (yoneda.map (s' j)) := by
  intro R _ Z X V f y m m' s s' hs hs'
  obtain ⟨hc, hi⟩ := hs
  obtain ⟨hc', hi'⟩ := hs'
  let T : Sieve V :=
    { arrows := fun W v => (_root_.GlobalTheory.EtC.free R).map (yoneda.map v) ≫
          ∑ j, (_root_.GlobalTheory.EtC.free R).map (yoneda.map (s j)) =
        (_root_.GlobalTheory.EtC.free R).map (yoneda.map v) ≫
          ∑ j, (_root_.GlobalTheory.EtC.free R).map (yoneda.map (s' j))
      downward_closed := by
        intro W W' v hv g
        rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hv] }
  refine _root_.GlobalTheory.EtC.Tr.free_hom_ext_of_covering R (_root_.GlobalTheory.EtC.Tr.freeSch R Z) _ _ T ?_ (fun W v hv => hv)
  apply Scheme.zariskiTopology_le_etaleTopology
  choose K A hKA using fun (x : ↥V) (j : Fin m) =>
    exists_pullback_lift_apply_eq_of_isIso_sigmaDesc hc' ((pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y) x)
  choose K' A' hKA' using fun (x : ↥V) (k : Fin m') =>
    exists_pullback_lift_apply_eq_of_isIso_sigmaDesc hc ((pullback.lift (s' k) (𝟙 V) (by simp [hc' k]) : V ⟶ pullback f y) x)
  have hopen := isOpenImmersion_pullback_lift_of_isIso_sigmaDesc hc'
  let U : ↥V → V.Opens := fun x =>
    ⟨⋂ j, (pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y) ⁻¹'
        Set.range (pullback.lift (s' (K x j)) (𝟙 V) (by simp [hc' (K x j)]) : V ⟶ pullback f y),
      isOpen_iInter_of_finite fun j =>
        (Scheme.Hom.isOpenEmbedding _).isOpen_range.preimage (Scheme.Hom.continuous _)⟩
  have hxU : ∀ x, x ∈ U x := fun x => Set.mem_iInter.mpr fun j => ⟨A x j, hKA x j⟩
  have hagree : ∀ x, T ((U x).ι) := by
    intro x
    have hinj := injective_of_pullback_lift_apply_eq_of_isIso hc hc' x (K x) (A x) (hKA x)
    have hinj' := injective_of_pullback_lift_apply_eq_of_isIso hc' hc x (K' x) (A' x) (hKA' x)
    have hbij : Function.Bijective (K x) := (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hinj, le_antisymm (Fintype.card_le_of_injective _ hinj) (Fintype.card_le_of_injective _ hinj')⟩
    have hsec : ∀ j, (U x).ι ≫ s j = (U x).ι ≫ s' (K x j) := by
      intro j
      have hr : Set.range ⇑((U x).ι ≫ (pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y)) ⊆
          Set.range (pullback.lift (s' (K x j)) (𝟙 V) (by simp [hc' (K x j)]) : V ⟶ pullback f y) := by
        rintro _ ⟨w, rfl⟩
        have hw : (U x).ι w ∈ U x := by
          have hw' : (U x).ι w ∈ Set.range (U x).ι := ⟨w, rfl⟩
          rwa [Scheme.Opens.range_ι] at hw'
        rw [Scheme.Hom.comp_apply]
        exact Set.mem_iInter.mp hw j
      have hg := IsOpenImmersion.lift_fac _ _ hr
      have hgι : IsOpenImmersion.lift _ _ hr = (U x).ι := by
        have := congrArg (· ≫ pullback.snd f y) hg
        simp only [Category.assoc, pullback.lift_snd, Category.comp_id] at this
        exact this
      rw [hgι] at hg
      have := congrArg (· ≫ pullback.fst f y) hg
      simp only [Category.assoc, pullback.lift_fst] at this
      exact this.symm
    show (_root_.GlobalTheory.EtC.free R).map (yoneda.map (U x).ι) ≫ _ =
      (_root_.GlobalTheory.EtC.free R).map (yoneda.map (U x).ι) ≫ _
    rw [Preadditive.comp_sum, Preadditive.comp_sum]
    refine Fintype.sum_equiv (Equiv.ofBijective _ hbij) _ _ fun j => ?_
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      Equiv.ofBijective_apply, hsec j]
  rw [show Scheme.zariskiTopology = Scheme.grothendieckTopology @IsOpenImmersion from rfl,
    Scheme.mem_grothendieckTopology_iff]
  refine ⟨Scheme.Cover.mkOfCovers V (fun x => (U x : Scheme.{0})) (fun x => (U x).ι)
    (fun x => ⟨x, ⟨x, hxU x⟩, rfl⟩), ?_⟩
  rintro W _ ⟨x⟩
  exact hagree x

end GlobalTheory.EtC.Tr

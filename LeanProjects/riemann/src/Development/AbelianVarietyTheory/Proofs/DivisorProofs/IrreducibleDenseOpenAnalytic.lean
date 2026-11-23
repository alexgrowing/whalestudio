import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

section ChartAssemble

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N : ℕ}

theorem torsPullback_snd :
    (pullback.snd ((𝟙 G) ^ N : G ⟶ G).left η[G].left : _ ⟶ Sp R) =
      pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom := by
  have hw : η[G].left ≫ G.hom = 𝟙 _ := Over.w η[G]
  calc (pullback.snd ((𝟙 G) ^ N : G ⟶ G).left η[G].left : _ ⟶ Sp R)
      = pullback.snd ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ η[G].left ≫ G.hom := by
        rw [hw]; rfl
    _ = pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ ((𝟙 G) ^ N : G ⟶ G).left ≫ G.hom := by
        rw [← Category.assoc, ← pullback.condition, Category.assoc]
    _ = _ := by rw [Over.w]

theorem pow_eq_one_iff_left (B : Type) [CommRing B] [Algebra R B] (x : SpAlg R B ⟶ G) :
    x ^ N = 1 ↔ x.left ≫ ((𝟙 G) ^ N : G ⟶ G).left = spMap (algebraMap R B) ≫ η[G].left := by
  have e1 : x ^ N = x ≫ (𝟙 G) ^ N := by rw [MonObj.comp_pow, Category.comp_id]
  have e2 : (1 : SpAlg R B ⟶ G).left = spMap (algebraMap R B) ≫ η[G].left := by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]; rfl
  rw [e1]
  constructor
  · intro h; rw [← e2, ← Over.comp_left, h]
  · intro h; apply Over.OverMorphism.ext; rw [Over.comp_left, h, e2]

end ChartAssemble

theorem preChart_of_open : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [IsSeparated G.hom]
    (N : ℕ) (q : PrimeSpectrum R) (r : R), r ∉ q.asIdeal → ∀ (C : Type) [CommRing C] [Algebra R C]
    [Algebra (Localization.Away r) C] [IsScalarTower R (Localization.Away r) C] [Module.Finite (Localization.Away r) C]
    [Module.Free (Localization.Away r) C] (U : (pullback ((𝟙 G) ^ N : G ⟶ G).left η[G].left).Opens)
    (e : Sp C ≅ U.toScheme),
    e.hom ≫ U.ι ≫ pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom = spMap (algebraMap R C) →
    (∀ t, (pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom) t = q → t ∈ U) →
    Nonempty (PreChart G N q) := by
  intro R _ G _ _ _ N q r hr C _ _ _ _ _ _ U e he hU
  have hw : η[G].left ≫ G.hom = 𝟙 _ := Over.w η[G]
  haveI : IsClosedImmersion (η[G].left ≫ G.hom) := hw ▸ inferInstance
  haveI : IsClosedImmersion η[G].left := IsClosedImmersion.of_comp _ G.hom
  haveI hfc : IsClosedImmersion (pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left) := inferInstance
  obtain ⟨W, hWo, hWU⟩ :=
    (pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left).isClosedEmbedding.isInducing.isOpen_iff.1 U.2
  let W' : G.left.Opens := ⟨W, hWo⟩
  have hmem : ∀ t, t ∈ U ↔ pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left t ∈ W' := fun t => by
    change t ∈ U.carrier ↔ _ ∈ W
    rw [← hWU]; rfl
  let m := e.hom ≫ U.ι ≫ pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left
  have hm : m ≫ G.hom = spMap (algebraMap R C) := by simpa only [m, Category.assoc] using he
  let j0 : SpAlg R C ⟶ G := Over.homMk m hm
  have hj : j0 ^ N = 1 := by
    rw [pow_eq_one_iff_left]
    show m ≫ _ = _
    calc m ≫ ((𝟙 G) ^ N : G ⟶ G).left
        = e.hom ≫ U.ι ≫ pullback.snd ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ η[G].left := by
          simp only [m, Category.assoc, pullback.condition]
      _ = (m ≫ G.hom) ≫ η[G].left := by
          rw [torsPullback_snd]; simp only [m, Category.assoc]
      _ = _ := by rw [hm]
  have hrange : ∀ {T : Scheme.{0}} (a : T ⟶ U.toScheme),
      Set.range (a ≫ U.ι ≫ pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left) ⊆ W' := by
    rintro T a _ ⟨x, rfl⟩
    have hx : U.ι (a x) ∈ U := by rw [← SetLike.mem_coe, ← U.range_ι]; exact ⟨_, rfl⟩
    have h' := (hmem _).1 hx
    simp only [Scheme.Hom.comp_apply, SetLike.mem_coe]
    exact h'

  have hlift : ∀ (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B),
      ∃ t : Sp B ⟶ pullback ((𝟙 G) ^ N : G ⟶ G).left η[G].left,
        t ≫ pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left = z.1.left := fun B _ _ z =>
    ⟨pullback.lift z.1.left (spMap (algebraMap R B)) ((pow_eq_one_iff_left B z.1).1 z.2),
      pullback.lift_fst _ _ _⟩
  haveI : Mono m := inferInstance
  refine ⟨{ r := r, hr := hr, C := C, j := ⟨j0, hj⟩, W := W', bij := fun B _ _ => ?_, fibre := ?_ }⟩
  · refine ⟨fun ψ _ => hrange (spMap (ψ : C →+* B) ≫ e.hom), fun ψ _ ψ' _ h => ?_, fun z hz => ?_⟩
    · have h1 : spMap (ψ : C →+* B) ≫ m = spMap (ψ' : C →+* B) ≫ m := congrArg (fun z => z.1.left) h
      have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono m).1 h1))
      exact AlgHom.coe_ringHom_injective h2
    · obtain ⟨t, ht⟩ := hlift B z
      have htU : Set.range t ⊆ Set.range U.ι := by
        rw [U.range_ι]
        rintro _ ⟨x, rfl⟩
        rw [SetLike.mem_coe, hmem, ← Scheme.Hom.comp_apply, ht]
        exact hz ⟨x, rfl⟩
      let s := IsOpenImmersion.lift U.ι t htU ≫ e.inv
      obtain ⟨φ, hφ⟩ := Spec.map_surjective s
      have hs : s ≫ m = z.1.left := by
        simp only [s, m, Category.assoc, Iso.inv_hom_id_assoc, IsOpenImmersion.lift_fac_assoc, ht]
      have halg : φ.hom.comp (algebraMap R C) = algebraMap R B := by
        have h3 : Spec.map (CommRingCat.ofHom (φ.hom.comp (algebraMap R C))) =
            Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
          rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, hφ]
          show s ≫ spMap (algebraMap R C) = _
          rw [← hm, ← Category.assoc, hs]
          exact Over.w z.1
        exact congrArg CommRingCat.Hom.hom (Spec.map_injective h3)
      let ψ : C →ₐ[R] B := { φ.hom with commutes' := fun c => congrArg (fun g => g c) halg }
      refine ⟨ψ, trivial, Subtype.ext (Over.OverMorphism.ext ?_)⟩
      show spMap (ψ : C →+* B) ≫ m = z.1.left
      have : spMap (ψ : C →+* B) = s := by rw [← hφ]; rfl
      rw [this, hs]
  · intro k _ _ hk z
    obtain ⟨t, ht⟩ := hlift k z
    rintro _ ⟨x, rfl⟩
    have hx : t x ∈ U := by
      apply hU
      rw [← Scheme.Hom.comp_apply, ← Category.assoc, ht, Over.w z.1]
      refine PrimeSpectrum.ext (R := R) ?_
      show Ideal.comap (algebraMap R k) x.asIdeal = q.asIdeal
      haveI := x.isPrime
      rw [Ideal.eq_bot_of_prime x.asIdeal, ← RingHom.ker_eq_comap_bot, hk]
    have := (hmem _).1 hx
    rw [← Scheme.Hom.comp_apply, ht] at this
    exact this

end GlobalTheory.GroupBplus.Aff

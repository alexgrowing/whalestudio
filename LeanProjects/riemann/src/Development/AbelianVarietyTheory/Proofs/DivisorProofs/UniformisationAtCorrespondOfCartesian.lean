import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EpsPtScaleZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.UnifPull

variable {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} [GrpObj G] [GrpObj G'] {f : X' ⟶ X}
  {φ : G'.left ⟶ G.left}

def push (hw : φ ≫ G.hom = G'.hom ≫ f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t' ⟶ G') : Over.mk t ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    show (x.left ≫ φ) ≫ G.hom = t
    rw [Category.assoc, hw, ← Category.assoc, Over.w x, ← ht]
    rfl)

theorem push_left (hw : φ ≫ G.hom = G'.hom ≫ f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t' ⟶ G') : (push hw ht x).left = x.left ≫ φ := rfl

def pull (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t ⟶ G) : Over.mk t' ⟶ G' :=
  Over.homMk (H.lift x.left t' ((Over.w x).trans ht.symm)) (H.lift_snd _ _ _)

theorem push_pull (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t ⟶ G) : push H.w ht (pull H ht x) = x :=
  Over.OverMorphism.ext (H.lift_fst _ _ _)

theorem push_injective (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X}
    (ht : t' ≫ f = t) : Function.Injective (push H.w ht) := fun x y h =>
  Over.OverMorphism.ext (H.hom_ext (congrArg (fun u => u.left) h) (by rw [Over.w x, Over.w y]))

theorem push_surjective (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X}
    (ht : t' ≫ f = t) : Function.Surjective (push H.w ht) := fun x => ⟨_, push_pull H ht x⟩

theorem push_mul (hφ : IsGrpPullback G' G f φ) {T : Scheme.{0}} (t' : T ⟶ X') (x y : Over.mk t' ⟶ G') :
    push hφ.1.w (t := t' ≫ f) rfl (x * y) = push hφ.1.w rfl x * push hφ.1.w rfl y :=
  Over.OverMorphism.ext (hφ.2 (Over.mk t') x y (push hφ.1.w rfl x) (push hφ.1.w rfl y) rfl rfl).symm

theorem push_one (hφ : IsGrpPullback G' G f φ) {T : Scheme.{0}} (t' : T ⟶ X') :
    push hφ.1.w (t := t' ≫ f) rfl (1 : Over.mk t' ⟶ G') = 1 := by
  have h := push_mul hφ t' 1 1
  rw [_root_.mul_one] at h
  exact mul_eq_left.1 h.symm

theorem push_comp (hw : φ ≫ G.hom = G'.hom ≫ f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    {a' : G' ⟶ G'} {a : G ⟶ G} (ha : a'.left ≫ φ = φ ≫ a.left) (x : Over.mk t' ⟶ G') :
    push hw ht (x ≫ a') = push hw ht x ≫ a :=
  Over.OverMorphism.ext (by
    show (x ≫ a').left ≫ φ = (push hw ht x ≫ a).left
    rw [Over.comp_left, Over.comp_left, push_left, Category.assoc, ha, Category.assoc])

theorem isDerivAt0_iff_comp (H : IsPullback φ G'.hom G.hom f) {g : ℕ} {y' : Sp ℂ ⟶ X'}
    {e : (Fin g → ℂ) → (Sp ℂ ⟶ G'.left)} (he : ∀ z, e z ≫ G'.hom = y')
    (hol : IsHolTo Set.univ (fun z => e z ≫ φ)) (w : Fin g → ℂ) {v : Sp (DualNumber ℂ) ⟶ G'.left}
    (hv : v ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y') :
    IsDerivAt0 e w v ↔ IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ) := by
  refine ⟨fun h => FibreDeriv.isDerivAt0_comp h φ, fun h => ?_⟩
  have H₁ := (IsPullback.of_hasPullback G'.hom y').paste_horiz H
  let e₁ : (Fin g → ℂ) → (Sp ℂ ⟶ pullback G'.hom y') :=
    fun z => pullback.lift (e z) (𝟙 _) (by rw [he, Category.id_comp])
  let v₁ : Sp (DualNumber ℂ) ⟶ pullback G'.hom y' := pullback.lift v (spMap (algebraMap ℂ (DualNumber ℂ))) hv
  have h1 : ∀ z, e₁ z ≫ pullback.fst _ _ = e z := fun z => pullback.lift_fst _ _ _
  have hv1 : v₁ ≫ pullback.fst _ _ = v := pullback.lift_fst _ _ _
  have hf1 : (fun z => e₁ z ≫ pullback.fst G'.hom y' ≫ φ) = fun z => e z ≫ φ :=
    funext fun z => by rw [← Category.assoc, h1]
  have key := FibreDeriv.isDerivAt0_of_isPullback H₁ (e := e₁) (fun z => pullback.lift_snd _ _ _)
    (by rw [hf1]; exact hol) (pullback.lift_snd _ _ _) (by rw [hf1, ← Category.assoc, hv1]; exact h)
  have := FibreDeriv.isDerivAt0_comp key (pullback.fst _ _)
  rw [hv1] at this
  simpa only [h1] using this

theorem spMap_fst_alg : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem isExp_iff (hφ : IsGrpPullback G' G f φ) {g : ℕ} (y' : Sp ℂ ⟶ X') (e : (Fin g → ℂ) → (Over.mk y' ⟶ G')) :
    IsExp y' e ↔ IsExp (y' ≫ f) (fun z => push hφ.1.w rfl (e z)) := by
  have H := hφ.1
  have hpe : ∀ z, (push H.w (t := y' ≫ f) rfl (e z)).left = (e z).left ≫ φ := fun z => rfl
  have hes : ∀ z, (e z).left ≫ G'.hom = y' := fun z => Over.w (e z)
  have hol : IsHolTo Set.univ (fun z => (e z).left) ↔ IsHolTo Set.univ (fun z => (e z).left ≫ φ) :=
    ⟨fun h => HolFibre.isHolTo_comp h φ, fun h => HolFibre.isHolTo_of_isPullback H h
      (by simp only [hes]; exact HolFibre.isHolTo_const isOpen_univ y')⟩
  have ht : (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y') ≫ f = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (y' ≫ f) :=
    Category.assoc _ _ _
  let pE : (epsPt y' ⟶ G') → (epsPt (y' ≫ f) ⟶ G) := push H.w ht
  have pEi : Function.Injective pE := push_injective H ht
  have pEs : Function.Surjective pE := push_surjective H ht
  have hd : IsHolTo Set.univ (fun z => (e z).left ≫ φ) → ∀ w (v : epsPt y' ⟶ G'),
      IsDerivAt0 (fun z => (e z).left) w v.left ↔ IsDerivAt0 (fun z => (push H.w (t := y' ≫ f) rfl (e z)).left) w (pE v).left :=
    fun h w v => isDerivAt0_iff_comp H hes h w (Over.w v)
  have hbase : ∀ v : epsPt y' ⟶ G', spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (pE v).left =
      (push H.w (t := y' ≫ f) rfl (e 0)).left ↔ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left := by
    intro v
    refine ⟨fun h => H.hom_ext (by rw [Category.assoc]; exact h) ?_, fun h => ?_⟩
    · rw [Category.assoc, Over.w v, hes]
      show spMap _ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y' = y'
      rw [← Category.assoc, spMap_fst_alg, Category.id_comp]
    · show spMap _ ≫ v.left ≫ φ = (e 0).left ≫ φ
      rw [← Category.assoc, h]
  have hinj : Function.Injective (push H.w (t := y' ≫ f) rfl (t' := y')) := push_injective H rfl
  constructor
  · rintro ⟨hadd, hsurj, hh, hd1, hd2⟩
    have hh' := hol.1 hh
    refine ⟨fun z w => by dsimp only; rw [hadd, push_mul hφ], (push_surjective H rfl).comp hsurj, hh', fun w => ?_,
      fun v hv => ?_⟩
    · obtain ⟨v, hv, hu⟩ := hd1 w
      refine ⟨pE v, (hd hh' w v).1 hv, fun v' hv' => ?_⟩
      obtain ⟨v', rfl⟩ := pEs v'
      rw [hu v' ((hd hh' w v').2 hv')]
    · obtain ⟨v, rfl⟩ := pEs v
      obtain ⟨w, hw, hu⟩ := hd2 v ((hbase v).1 hv)
      exact ⟨w, (hd hh' w v).1 hw, fun w' hw' => hu w' ((hd hh' w' v).2 hw')⟩
  · rintro ⟨hadd, hsurj, hh, hd1, hd2⟩
    have hh' : IsHolTo Set.univ (fun z => (e z).left ≫ φ) := hh
    refine ⟨fun z w => hinj (by have h := hadd z w; dsimp only at h; rw [h, push_mul hφ]), fun x => ?_, hol.2 hh', fun w => ?_, fun v hv => ?_⟩
    · obtain ⟨z, hz⟩ := hsurj (push H.w rfl x)
      exact ⟨z, hinj hz⟩
    · obtain ⟨v, hv, hu⟩ := hd1 w
      obtain ⟨v, rfl⟩ := pEs v
      exact ⟨v, (hd hh' w v).2 hv, fun v' hv' => pEi (hu _ ((hd hh' w v').1 hv'))⟩
    · obtain ⟨w, hw, hu⟩ := hd2 (pE v) ((hbase v).2 hv)
      exact ⟨w, (hd hh' w v).2 hw, fun w' hw' => hu w' ((hd hh' w' v).1 hw')⟩

end GlobalTheory.UnifPull

namespace GlobalTheory.UnifPull

variable {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {R R' : Type} [CommRing R]
  [CommRing R'] {σ : R →+* ℂ} {σ' : R' →+* ℂ} {Λ : Type} {F : Fam R O Λ g} {F' : Fam R' O Λ g} {N : ℕ}
  {f : F'.X ⟶ F.X} {φ : F'.A.left ⟶ F.A.left}

theorem unifAt_iff (hφ : IsGrpPullback F'.A F.A f φ) (hact : ∀ a, (F'.act a).left ≫ φ = φ ≫ (F.act a).left)
    (hL : LBIso F'.L (F.L.pull φ)) (heta : ∀ a, (F'.eta a).left ≫ φ = f ≫ (F.eta a).left) (D' : PLat O bar)
    (t : Λ → D'.La) (P : D'.La →+ (Fin g → ℂ)) (y' : Sp ℂ ⟶ F'.X) (hy' : y' ≫ F'.s = spMap σ')
    (hy : (y' ≫ f) ≫ F.s = spMap σ) (e' : (Fin g → ℂ) → (Over.mk y' ⟶ F'.A)) :
    UnifAt F' σ' ρ N D' t P y' e' ↔ UnifAt F σ ρ N D' t P (y' ≫ f) (fun z => push hφ.1.w rfl (e' z)) := by
  have hinj : Function.Injective (push hφ.1.w (t := y' ≫ f) rfl (t' := y')) := push_injective hφ.1 rfl
  have hker : ∀ z, push hφ.1.w (t := y' ≫ f) rfl (e' z) = 1 ↔ e' z = 1 := fun z => by
    rw [← push_one hφ y']
    exact hinj.eq_iff
  have hlin : ∀ a z, e' (ρ a *ᵥ z) = e' z ≫ F'.act a ↔
      push hφ.1.w (t := y' ≫ f) rfl (e' (ρ a *ᵥ z)) = push hφ.1.w rfl (e' z) ≫ F.act a := fun a z => by
    rw [← push_comp hφ.1.w rfl (hact a)]
    exact hinj.eq_iff.symm
  have hweil : ∀ (k : ℤ) (x x' : Over.mk y' ⟶ F'.A) (c : Γ(Sp ℂ, ⊤)ˣ), Out.WeilIs F'.A F'.L k x x' c ↔
      Out.WeilIs F.A F.L k (push hφ.1.w (t := y' ≫ f) rfl x) (push hφ.1.w rfl x') c := fun k x x' c =>
    GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ F.A F'.A f φ F.L F'.L F.isLB F'.isLB hφ hL (Over.mk y') k x x' _ _ c
      rfl rfl
  have hunit : ∀ a, push hφ.1.w (t := y' ≫ f) rfl (toUnit (Over.mk y') ≫ F'.eta a) =
      toUnit (Over.mk (y' ≫ f)) ≫ F.eta a := fun a => Over.OverMorphism.ext (by
    rw [push_left, Over.comp_left, Over.comp_left, Category.assoc, heta]
    simp)
  have heta' : ∀ a x, toUnit _ ≫ F'.eta a = x ↔ toUnit _ ≫ F.eta a = push hφ.1.w (t := y' ≫ f) rfl x :=
    fun a x => by
      rw [← hunit]
      exact hinj.eq_iff.symm
  constructor
  · rintro ⟨-, hP, hE, hK, hA, hW, hT⟩
    exact ⟨hy, hP, (isExp_iff hφ y' e').1 hE, fun z => (hker z).trans (hK z), fun a z => (hlin a z).1 (hA a z),
      fun k a b c hk hc => (hweil k _ _ _).1 (hW k a b c hk hc), fun a => (heta' a _).1 (hT a)⟩
  · rintro ⟨-, hP, hE, hK, hA, hW, hT⟩
    exact ⟨hy', hP, (isExp_iff hφ y' e').2 hE, fun z => (hker z).symm.trans (hK z), fun a z => (hlin a z).2 (hA a z),
      fun k a b c hk hc => (hweil k _ _ _).2 (hW k a b c hk hc), fun a => (heta' a _).2 (hT a)⟩

end GlobalTheory.UnifPull

open GlobalTheory.UnifPull in

theorem GlobalTheory.unifAt_correspond_of_cartesian : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* ℂ) (σ' : R' →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (F' : Fam R' O Λ g) (N : ℕ) (f : F'.X ⟶ F.X) (φ : F'.A.left ⟶ F.A.left), IsGrpPullback F'.A F.A f φ → (∀ a, (F'.act a).left ≫ φ = φ ≫ (F.act a).left) → LBIso F'.L (F.L.pull φ) → (∀ a, (F'.eta a).left ≫ φ = f ≫ (F.eta a).left) → ∀ (D' : PLat O bar) (t : Λ → D'.La) P (y' : Sp ℂ ⟶ F'.X), y' ≫ F'.s = spMap σ' → (y' ≫ f) ≫ F.s = spMap σ → (∀ e', UnifAt F' σ' ρ N D' t P y' e' → ∃ e, UnifAt F σ ρ N D' t P (y' ≫ f) e ∧ ∀ z, (e z).left = (e' z).left ≫ φ) ∧ ∀ e, UnifAt F σ ρ N D' t P (y' ≫ f) e → ∃ e', UnifAt F' σ' ρ N D' t P y' e' ∧ ∀ z, (e z).left = (e' z).left ≫ φ := by
  intro O _ bar g ρ R R' _ _ σ σ' Λ F F' N f φ hφ hact hL heta D' t P y' hy' hy
  refine ⟨fun e' he' => ⟨_, (unifAt_iff hφ hact hL heta D' t P y' hy' hy e').1 he', fun z => rfl⟩,
    fun e he => ⟨fun z => pull hφ.1 rfl (e z), ?_, fun z => (hφ.1.lift_fst _ _ _).symm⟩⟩
  have h : (fun z => push hφ.1.w (t := y' ≫ f) rfl (pull hφ.1 rfl (e z))) = e := funext fun z => push_pull hφ.1 rfl (e z)
  exact (unifAt_iff hφ hact hL heta D' t P y' hy' hy _).2 (by rw [h]; exact he)

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsClopenEqualizer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkCover

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

theorem exists_geomPt (X : Scheme.{0}) (g : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ X), ∀ q, x q = g :=
  ⟨AlgebraicClosure (X.residueField g), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField g) _)) ≫ X.fromSpecResidueField g,
    fun _ => Scheme.fromSpecResidueField_apply g _⟩

theorem exists_power {C S : Scheme.{0}} (c : C ⟶ S) [IsFinite c] [Etale c] (n : ℕ) :
    ∃ (P : Scheme.{0}) (π : P ⟶ S) (σ : Fin n → (P ⟶ C)), IsFinite π ∧ Etale π ∧ (∀ j, σ j ≫ c = π) ∧
      ∀ (T : Scheme.{0}) (x : T ⟶ S) (u : Fin n → (T ⟶ C)), (∀ j, u j ≫ c = x) →
        ∃ y : T ⟶ P, y ≫ π = x ∧ ∀ j, y ≫ σ j = u j := by
  induction n with
  | zero => exact ⟨S, 𝟙 S, Fin.elim0, inferInstance, inferInstance, fun j => j.elim0,
      fun T x u _ => ⟨x, by simp, fun j => j.elim0⟩⟩
  | succ n ih =>
    obtain ⟨P, π, σ, h₁, h₂, h₃, h₄⟩ := ih
    refine ⟨pullback π c, pullback.fst π c ≫ π,
      Fin.cons (pullback.snd π c) (fun j => pullback.fst π c ≫ σ j), inferInstance, inferInstance, fun j => ?_,
      fun T x u hu => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [pullback.condition]
      · simp [h₃]
    · obtain ⟨y, hy, hy'⟩ := h₄ T x (fun j => u j.succ) (fun j => hu _)
      refine ⟨pullback.lift y (u 0) (hy.trans (hu 0).symm), by simp [hy], fun j => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simp [hy']

theorem exists_eqLocus {P C S : Scheme.{0}} (c : C ⟶ S) [IsFinite c] [Etale c] (a b : P ⟶ C) (h : a ≫ c = b ≫ c) :
    ∃ U : Set P, IsClopen U ∧ ∀ (T : Scheme.{0}) (y : T ⟶ P), y ≫ a = y ≫ b ↔ Set.range y ⊆ U := by
  first
  | (rename_i h_4 h_5; revert P C S c h_4 h_5 a b h; exact @_root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer)
  | exact @_root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer
  | exact _root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer
  | (apply _root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer ..)

theorem exists_distinct {C S : Scheme.{0}} (c : C ⟶ S) [IsFinite c] [Etale c] (n : ℕ) :
    ∃ (P : Scheme.{0}) (π : P ⟶ S) (σ : Fin n → (P ⟶ C)), IsFinite π ∧ Etale π ∧ (∀ j, σ j ≫ c = π) ∧
      (∀ (k : Type) [Field k] (y : Sp k ⟶ P), Function.Injective fun j => y ≫ σ j) ∧
      ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (u : Fin n → (Sp k ⟶ C)), (∀ j, u j ≫ c = x) → Function.Injective u →
        ∃ y : Sp k ⟶ P, y ≫ π = x := by
  obtain ⟨P, π, σ, h₁, h₂, h₃, h₄⟩ := exists_power c n
  choose U hU hU' using fun a b : Fin n => exists_eqLocus c (σ a) (σ b) ((h₃ a).trans (h₃ b).symm)
  have hV : IsClopen (⋂ a, ⋂ b, ⋂ _ : a ≠ b, (U a b)ᶜ) :=
    isClopen_iInter_of_finite fun a => isClopen_iInter_of_finite fun b =>
      isClopen_iInter_of_finite fun _ => (hU a b).compl
  let V : P.Opens := ⟨_, hV.isOpen⟩
  have : IsClosedImmersion V.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hV.isClosed)
  refine ⟨V, V.ι ≫ π, fun j => V.ι ≫ σ j, inferInstance, inferInstance, fun j => by simp [h₃],
    fun k _ y a b e => ?_, fun k _ x u hu hi => ?_⟩
  · by_contra ne
    have q : Sp k := IsLocalRing.closedPoint k
    have m₁ : (y ≫ V.ι) q ∈ U a b := (hU' a b _ (y ≫ V.ι)).1 (by simpa using e) ⟨q, rfl⟩
    have m₂ : (y ≫ V.ι) q ∈ (V : Set P) := by
      rw [← Scheme.Opens.range_ι, Scheme.Hom.comp_apply]; exact ⟨_, rfl⟩
    exact (Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 m₂ a) b) ne) m₁
  · obtain ⟨y, hy, hy'⟩ := h₄ _ x u hu
    have hr : Set.range y ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨q, rfl⟩
      refine Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun b => Set.mem_iInter.2 fun ne m => ne (hi ?_)
      rw [← hy', ← hy', hU']
      rintro _ ⟨q', rfl⟩
      rwa [Subsingleton.elim q' q]
    exact ⟨IsOpenImmersion.lift V.ι y hr, by rw [← Category.assoc, IsOpenImmersion.lift_fac, hy]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

theorem comp_act_natCast (t : SAB H S) {T : Over S} (z : T ⟶ t.G) (n : ℕ) : z ≫ t.act.act (n : 𝓞 E) = z ^ n := by
  induction n with
  | zero =>
    have := t.act.add 0 0
    rw [add_zero] at this
    rw [Nat.cast_zero, pow_zero, show t.act.act 0 = 1 from left_eq_mul.1 this, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]

theorem pow_sq_eq_one (t : SAB H S) {T : Over S} {D : Datum H} {P : Ideal (𝓞 E)} {p i : ℕ} (hp : (p : 𝓞 E) ∈ P)
    {C : Subgroup (T ⟶ t.G)} (h : t.HeckeKer T D P p i C) {z : T ⟶ t.G} (hz : z ∈ C) : z ^ (p ^ 2) = 1 := by
  rw [← comp_act_natCast]
  refine h.2.2.1 hz _ ?_
  rw [Nat.cast_pow, sq]
  refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
  simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hp

end GlobalTheory.HkCover

open GlobalTheory.HkCover in

theorem GlobalTheory.exists_cover_lists_heckeSet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Ob D l s) (K : Set o.t.G.left), admitted l 𝔓 p → EtSet o.t.G K → HeckeSet D o.t 𝔓 p i K → ∃ (S' : Scheme.{0}) (π : S' ⟶ S) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π) (τ : Fin (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) → (𝟙_ (Over S') ⟶ o'.t.G)), IsFinite π ∧ Etale π ∧ Surjective π ∧ Lists (p ^ 2) τ (m.toSABMap.φ ⁻¹' K) := by
  intro E _ _ _ H D l P p i S _ s o K hA hE hK
  obtain ⟨C, j, h₁, h₂, h₃, rfl⟩ := hE
  have hn : p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) ≠ 0 := pow_ne_zero _ hA.2.2.1.ne_zero
  have hcard : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ Q : Subgroup (Over.mk x ⟶ o.t.G),
      (∀ z, z ∈ Q ↔ Set.range z.left ⊆ Set.range j.left) ∧ (∀ z ∈ Q, z ^ (p ^ 2) = 1) ∧
      Nat.card Q = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) := fun k _ _ x => by
    obtain ⟨Q, hQ, hq⟩ := hK k x
    exact ⟨Q, hQ, fun z hz => pow_sq_eq_one o.t hA.2.2.2.1 hq hz, hq.2.2.2.2.1⟩
  generalize p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) = n at hn hcard ⊢
  have wj : j.left ≫ o.t.G.hom = C.hom := Over.w j
  have rg : ∀ {T : Scheme.{0}} (u : T ⟶ C.left), Set.range (u ≫ j.left) ⊆ Set.range j.left := by
    rintro T u _ ⟨q, rfl⟩
    exact ⟨u q, (Scheme.Hom.comp_apply _ _ _).symm⟩

  have hj : j ^ (p ^ 2) = 1 := by
    have : IsReduced C.left := GlobalTheory.isReduced_of_smooth_of_isReduced C.hom
    have := o.proper
    refine Over.OverMorphism.ext (GlobalTheory.hom_ext_of_geometricPoints_dense o.t.G.hom _ _
      ((Over.w _).trans (Over.w _).symm) Set.univ dense_univ fun k _ _ x _ => ?_)
    obtain ⟨Q, hQ, hq, -⟩ := hcard k (x ≫ C.hom)
    let x' : Over.mk (x ≫ C.hom) ⟶ C := Over.homMk x rfl
    have e := hq (x' ≫ j) ((hQ _).2 (rg x))
    rw [← MonObj.comp_pow, ← MonObj.comp_one x'] at e
    exact congrArg (fun z => z.left) e
  obtain ⟨S', π, σ, f₁, f₂, f₃, f₄, f₅⟩ := exists_distinct C.hom n
  obtain ⟨o', ⟨m⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S S' s (π ≫ s) π rfl rfl
    (by simp [spMap]) o
  obtain ⟨ρ, e₀⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (𝟙_ (Over S'))
  let σ' : Fin n → (Over.mk ((𝟙_ (Over S')).hom ≫ π) ⟶ C) := fun a => Over.homMk (σ a) (by simpa using f₃ a)
  have e : ∀ a, (ρ.symm (σ' a ≫ j)).left ≫ m.toSABMap.φ = σ a ≫ j.left := fun a => by
    rw [← e₀, ρ.apply_symm_apply]; rfl
  have wτ : ∀ a, (ρ.symm (σ' a ≫ j)).left ≫ o'.t.G.hom = 𝟙 S' := fun a => Over.w _
  refine ⟨S', π, o', m, fun a => ρ.symm (σ' a ≫ j), f₁, f₂, ⟨fun g => ?_⟩, fun a => ?_, ?_, fun k _ _ y a b hab => ?_⟩
  · obtain ⟨k, _, _, x, hx⟩ := exists_geomPt S g
    obtain ⟨Q, hQ, -, hc⟩ := hcard k x
    have en : Q ≃ Fin n := Nat.equivFinOfCardPos (hc ▸ hn) |>.trans (finCongr hc)
    have : ∀ a : Fin n, ∃ u : Sp k ⟶ C.left, u ≫ j.left = (en.symm a).1.left := fun a =>
      GlobalTheory.exists_lift_closedImmersion_of_dense j.left _ Set.univ dense_univ
        fun q _ => (hQ _).1 (en.symm a).2 ⟨q, rfl⟩
    choose u hu using this
    obtain ⟨y, hy⟩ := f₅ k x u (fun a => by rw [← wj, ← Category.assoc, hu]; exact Over.w (en.symm a).1)
      fun a b hab => en.symm.injective (Subtype.ext (Over.OverMorphism.ext (by rw [← hu, ← hu, hab])))
    have q : Sp k := IsLocalRing.closedPoint k
    exact ⟨y q, by rw [← Scheme.Hom.comp_apply, hy, hx]⟩
  · rw [← map_pow, ← MonObj.comp_pow, hj, MonObj.comp_one, map_one]
  · refine Set.Subset.antisymm (fun g hg => ?_) (Set.iUnion_subset fun a => ?_)
    · obtain ⟨k, _, _, w, hw⟩ := exists_geomPt _ g
      obtain ⟨Q, hQ, -, hc⟩ := hcard k ((w ≫ o'.t.G.hom) ≫ π)
      let z : Fin n → Q := fun a => ⟨Over.homMk (((w ≫ o'.t.G.hom) ≫ σ a) ≫ j.left)
        (by simp [wj, f₃]), (hQ _).2 (rg _)⟩
      have zi : Function.Injective z := fun a b hab => f₄ k (w ≫ o'.t.G.hom)
        ((cancel_mono j.left).1 (congrArg (fun z : Q => z.1.left) hab))
      have : Finite Q := Nat.finite_of_card_ne_zero (hc ▸ hn)
      have zb := (Nat.bijective_iff_injective_and_card z).2 ⟨zi, by simp [hc]⟩
      obtain ⟨a, ha⟩ := zb.2 ⟨Over.homMk (w ≫ m.toSABMap.φ) (by simpa using congrArg (w ≫ ·) m.cart.1.w), (hQ _).2 (by
        rintro _ ⟨q, rfl⟩
        have : (w ≫ m.toSABMap.φ) q ∈ Set.range j.left := by rw [Scheme.Hom.comp_apply, hw]; exact hg
        exact this)⟩
      have ha' : ((w ≫ o'.t.G.hom) ≫ σ a) ≫ j.left = w ≫ m.toSABMap.φ := congrArg (fun z : Q => z.1.left) ha
      have hw' : (w ≫ o'.t.G.hom) ≫ (ρ.symm (σ' a ≫ j)).left = w := m.cart.1.hom_ext
        (by rw [Category.assoc, ← ha', Category.assoc _ (σ a)]; exact congrArg (_ ≫ ·) (e a))
        (by rw [Category.assoc, wτ]; exact Category.comp_id _)
      have q : Sp k := IsLocalRing.closedPoint k
      refine Set.mem_iUnion.2 ⟨a, (w ≫ o'.t.G.hom) q, ?_⟩
      rw [← hw q]
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun v : Sp k ⟶ _ => v q) hw')
    · rintro _ ⟨q, rfl⟩
      have := rg (σ a) ⟨q, rfl⟩
      rw [← e, Scheme.Hom.comp_apply] at this
      exact this
  · refine f₄ k y ((cancel_mono j.left).1 ?_)
    have := congrArg (· ≫ m.toSABMap.φ) hab
    simpa only [Category.assoc, e] using this

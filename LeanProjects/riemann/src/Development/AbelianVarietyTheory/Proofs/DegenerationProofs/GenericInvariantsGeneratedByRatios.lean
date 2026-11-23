import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfTorusBased
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsScalMulEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinearMapEqZeroOfOneTmulMemRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PullPullAndSplitPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.GenericInv
open SplitPull
open scoped TensorProduct

theorem exists_locus {S : Scheme.{0}} (X : Over S) {n : Type} (v w : n → Γ(X.left, ⊤)) :
    ∃ (E : Over S) (e : E ⟶ X), IsClosedImmersion e.left ∧
      (∀ l, e.left.appTop.hom (v l) = e.left.appTop.hom (w l)) ∧
      ∀ (Y : Over S) (m : Y ⟶ X), (∀ l, m.left.appTop.hom (v l) = m.left.appTop.hom (w l)) →
        ∃ q : Y ⟶ E, q ≫ e = m := by
  let A : Over S := Over.mk (𝔸(n; S) ↘ S)
  have : IsSeparated A.hom := inferInstanceAs (IsSeparated (𝔸(n; S) ↘ S))
  let f : X ⟶ A := Over.homMk (AffineSpace.homOfVector X.hom v) (AffineSpace.homOfVector_over _ _)
  let g : X ⟶ A := Over.homMk (AffineSpace.homOfVector X.hom w) (AffineSpace.homOfVector_over _ _)
  have key : ∀ (Y : Over S) (m : Y ⟶ X) (u : n → Γ(X.left, ⊤)) l,
      (m.left ≫ AffineSpace.homOfVector X.hom u).appTop.hom (AffineSpace.coord S l) =
        m.left.appTop.hom (u l) := by
    intro Y m u l
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    exact congrArg _ (AffineSpace.homOfVector_appTop_coord _ _ l)
  refine ⟨equalizer f g, equalizer.ι f g, inferInstance, fun l => ?_, fun Y m hm => ?_⟩
  · have h : (equalizer.ι f g).left ≫ AffineSpace.homOfVector X.hom v =
        (equalizer.ι f g).left ≫ AffineSpace.homOfVector X.hom w :=
      congrArg (fun k => k.left) (equalizer.condition f g)
    rw [← key, ← key, h]
  · refine ⟨equalizer.lift m ?_, equalizer.lift_ι _ _⟩
    refine Over.OverMorphism.ext (AffineSpace.hom_ext ((Over.w _).trans (Over.w _).symm) fun l => ?_)
    exact (key Y m v l).trans ((hm l).trans (key Y m w l).symm)

theorem exists_clear {R : Type} [CommRing R] [IsDomain R] {A A' : CommRingCat.{0}}
    {a : CommRingCat.of R ⟶ A} {p : A ⟶ A'} {q : CommRingCat.of (FractionRing R) ⟶ A'}
    (h : IsPushout a (CommRingCat.ofHom (algebraMap R (FractionRing R))) p q) (u : A') :
    ∃ (s : R) (x : A), s ≠ 0 ∧ p.hom (a.hom s) * u = p.hom x := by
  have hw : ∀ s, p.hom (a.hom s) = q.hom (algebraMap R (FractionRing R) s) :=
    fun s => congrArg (fun k => k.hom s) h.w
  have hu := (CommRingCat.closure_range_union_range_eq_top_of_isPushout h).ge (Subring.mem_top u)
  induction hu using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨x, rfl⟩ | ⟨z, rfl⟩
    · exact ⟨1, x, one_ne_zero, by simp⟩
    · obtain ⟨⟨r, s⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors R) (S := FractionRing R) z
      refine ⟨s, a.hom r, nonZeroDivisors.ne_zero s.2, ?_⟩
      rw [hw, hw, ← map_mul, _root_.mul_comm, hz]
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | one => exact ⟨1, 1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, x, hs, e⟩ := hy
    obtain ⟨s', x', hs', e'⟩ := hz
    refine ⟨s * s', a.hom s' * x + a.hom s * x', mul_ne_zero hs hs', ?_⟩
    simp only [map_mul, map_add, ← e, ← e']
    ring
  | neg y _ hy =>
    obtain ⟨s, x, hs, e⟩ := hy
    exact ⟨s, -x, hs, by rw [map_neg, ← e, mul_neg]⟩
  | mul y z _ _ hy hz =>
    obtain ⟨s, x, hs, e⟩ := hy
    obtain ⟨s', x', hs', e'⟩ := hz
    refine ⟨s * s', x * x', mul_ne_zero hs hs', ?_⟩
    simp only [map_mul, ← e, ← e']
    ring

theorem one_tmul_mem_range {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {A A' : CommRingCat.{0}}
    [Algebra R A] {p : A ⟶ A'} {q : CommRingCat.of K ⟶ A'}
    (h : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R K)) p q)
    (T : Set A) (x : A) (hx : p.hom x ∈ Subring.closure (Set.range q.hom ∪ p.hom '' T)) :
    (1 ⊗ₜ[R] x : K ⊗[R] A) ∈
      (Algebra.TensorProduct.map (AlgHom.id R K) (Algebra.adjoin R T).val).range := by
  let θ : A' ⟶ CommRingCat.of (K ⊗[R] A) := h.desc
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := A)).toRingHom)
    (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := K) (B := A)).toRingHom) (by
      ext r
      exact ((Algebra.TensorProduct.includeRight (R := R) (A := K) (B := A)).commutes r).trans
        ((Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := K) (B := A)).commutes r).symm)
  have hp : ∀ y, θ.hom (p.hom y) = (1 ⊗ₜ[R] y : K ⊗[R] A) := fun y =>
    congrArg (fun k : A ⟶ CommRingCat.of (K ⊗[R] A) => k.hom y) (h.inl_desc _ _ _ : p ≫ θ = _)
  have hq : ∀ y, θ.hom (q.hom y) = (y ⊗ₜ[R] 1 : K ⊗[R] A) := fun y =>
    congrArg (fun k : CommRingCat.of K ⟶ CommRingCat.of (K ⊗[R] A) => k.hom y) (h.inr_desc _ _ _ : q ≫ θ = _)
  rw [← hp]
  refine (Subring.closure_le (t := (Algebra.TensorProduct.map (AlgHom.id R K)
    (Algebra.adjoin R T).val).range.toSubring.comap θ.hom)).2 ?_ hx
  rintro _ (⟨y, rfl⟩ | ⟨y, hy, rfl⟩)
  · exact ⟨y ⊗ₜ 1, (hq y).symm⟩
  · exact ⟨1 ⊗ₜ ⟨y, Algebra.subset_adjoin hy⟩, (hp y).symm⟩

theorem isPushout_sections {R K : CommRingCat.{0}} (ψ : R ⟶ K) {X : Scheme.{0}} (π : X ⟶ Spec R)
    {V : X.Opens} (hV : IsAffineOpen V) :
    IsPushout ((Scheme.ΓSpecIso R).inv ≫ π.appLE ⊤ V le_top) ψ ((pullback.fst π (Spec.map ψ)).app V)
      ((Scheme.ΓSpecIso K).inv ≫ (pullback.snd π (Spec.map ψ)).appLE ⊤
        (pullback.fst π (Spec.map ψ) ⁻¹ᵁ V) le_top) := by
  have h := IsPullback.of_hasPullback π (Spec.map ψ)
  have po := ((isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := V)
    (UY := pullback.fst π (Spec.map ψ) ⁻¹ᵁ V) le_top
      le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
        (isAffineOpen_top _) hV))
  rw [Scheme.Hom.appLE_eq_app] at po
  refine po.of_iso (Scheme.ΓSpecIso R) (Iso.refl _) (Scheme.ΓSpecIso K) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · erw [Scheme.Hom.appLE_eq_app]
    exact Scheme.ΓSpecIso_naturality ψ
  · simp
  · simp

theorem appLE_congr {A B : Scheme.{0}} {r s : A ⟶ B} (e : r = s) (V : B.Opens) (k : ⊤ ≤ r ⁻¹ᵁ V)
    (k' : ⊤ ≤ s ⁻¹ᵁ V) (u : Γ(B, V)) : (r.appLE V ⊤ k).hom u = (s.appLE V ⊤ k').hom u := by
  subst e
  rfl

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

omit [GrpObj G] in
theorem le_comp {Y Y' : Over S} (m : Y' ⟶ Y) {k : Y ⟶ G} {V : G.left.Opens} (h : ⊤ ≤ k.left ⁻¹ᵁ V) :
    ⊤ ≤ (m ≫ k).left ⁻¹ᵁ V := m.left.preimage_mono h

theorem one_mem {V : G.left.Opens} (h : ⊤ ≤ eSec G ⁻¹ᵁ V) (Y : Over S) : ⊤ ≤ (1 : Y ⟶ G).left ⁻¹ᵁ V :=
  le_comp (toUnit Y) (k := η[G]) h

theorem inK_comp {C : Charts G.left} {a} {Y Y' : Over S} (m : Y' ⟶ Y) {k : Y ⟶ G} (h : C.InK a k) :
    C.InK a (m ≫ k) := by
  obtain ⟨h, h₁, e⟩ := h
  have e₁ : (1 : Y' ⟶ G).left = m.left ≫ (1 : Y ⟶ G).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  refine ⟨le_comp m h, e₁ ▸ m.left.preimage_mono h₁, fun j hj => ?_⟩
  rw [← appTop_appLE m.left k.left (m ≫ k).left rfl _ h, ← appTop_appLE m.left _ _ e₁ _ h₁, e j hj]

theorem inK_push {S' : Scheme.{0}} {f : S' ⟶ S} {G' : Over S'} [GrpObj G'] {F : G'.left ⟶ G.left} [IsAffineHom F]
    (hF : IsGrpPullback G' G f F) (C : Charts G.left) (a) {Y : Over S'} (k : Y ⟶ G') :
    (C.pull F).InK a k ↔ C.InK a (pushPt hF.1.w k) := by
  have e₁ : (1 : Over.mk (Y.hom ≫ f) ⟶ G).left = (1 : Y ⟶ G').left ≫ F :=
    (congrArg (fun z => z.left) (map_one (pushHom hF Y))).symm
  constructor
  · rintro ⟨h, h₁, e⟩
    have h₂ : ⊤ ≤ (1 : Over.mk (Y.hom ≫ f) ⟶ G).left ⁻¹ᵁ C.W a := by rw [e₁]; exact h₁
    refine ⟨h, h₂, fun j hj => ?_⟩
    exact (appLE_app k.left F _ rfl _ h h _).symm.trans ((e j hj).trans (appLE_app _ F _ e₁ _ h₁ h₂ _))
  · rintro ⟨h, h₂, e⟩
    have h₁ : ⊤ ≤ ((1 : Y ⟶ G').left ≫ F) ⁻¹ᵁ C.W a := by rw [← e₁]; exact h₂
    refine ⟨h, h₁, fun j hj => ?_⟩
    exact (appLE_app k.left F _ rfl _ h h _).trans ((e j hj).trans (appLE_app _ F _ e₁ _ h₁ h₂ _).symm)

theorem inK_torus {C : Charts G.left} {d : ℕ} {c : Fin d → C.Cl} {i : splitTorus S (Fin d → ℤ) ⟶ G}
    (hT : C.Torus c i) {a} {Y : Over S} (h₁ : ⊤ ≤ (1 : Y ⟶ G).left ⁻¹ᵁ C.W a)
    (t : Y ⟶ splitTorus S (Fin d → ℤ)) : C.InK a (t ≫ i) := by
  have h := hT.stable a Y t 1 h₁
  have e : ((t ≫ i) * 1).left = (t ≫ i).left := by rw [_root_.mul_one]
  refine ⟨e ▸ h, h₁, fun j hj => ?_⟩
  have h0 := hT.inv a j hj Y t 1 h₁ h
  rw [charUnit_zero_val, map_one, _root_.one_mul] at h0
  exact (appLE_congr e.symm _ _ _ _).trans h0

theorem exists_universal (C : Charts G.left) {a} (h₁ : ⊤ ≤ eSec G ⁻¹ᵁ C.W a) (V : G.left.Opens) :
    ∃ (E : Over S) (k₀ g₀ : E ⟶ G), IsImmersion (lift k₀ g₀).left ∧ C.InK a k₀ ∧ ⊤ ≤ g₀.left ⁻¹ᵁ V ∧
      ⊤ ≤ (k₀ * g₀).left ⁻¹ᵁ V ∧ ∀ (Y : Over S) (k g : Y ⟶ G), C.InK a k → ⊤ ≤ g.left ⁻¹ᵁ V →
        ⊤ ≤ (k * g).left ⁻¹ᵁ V → ∃ q : Y ⟶ E, q ≫ k₀ = k ∧ q ≫ g₀ = g := by
  let U : (G ⊗ G).left.Opens := (fst G G).left ⁻¹ᵁ C.W a ⊓ ((snd G G).left ⁻¹ᵁ V ⊓ (fst G G * snd G G).left ⁻¹ᵁ V)
  let X : Over S := Over.mk (U.ι ≫ (G ⊗ G).hom)
  let u : X ⟶ G ⊗ G := Over.homMk U.ι rfl
  have hu : ⊤ ≤ U.ι ⁻¹ᵁ U := U.ι_preimage_self.ge
  have k₁ : ⊤ ≤ (u ≫ fst G G).left ⁻¹ᵁ C.W a := hu.trans (U.ι.preimage_mono inf_le_left)
  have k₂ : ⊤ ≤ (u ≫ snd G G).left ⁻¹ᵁ V := hu.trans (U.ι.preimage_mono (inf_le_right.trans inf_le_left))
  have k₃ : ⊤ ≤ (u ≫ (fst G G * snd G G)).left ⁻¹ᵁ V :=
    hu.trans (U.ι.preimage_mono (inf_le_right.trans inf_le_right))
  obtain ⟨E, e, he, h, hE⟩ := exists_locus X (n := {l // C.wt l = C.c₀})
    (fun l => ((u ≫ fst G G).left.appLE _ ⊤ k₁).hom (C.r a l.1))
    (fun l => ((1 : X ⟶ G).left.appLE _ ⊤ (one_mem h₁ X)).hom (C.r a l.1))
  have one : ∀ {Y : Over S} (m : Y ⟶ X), (1 : Y ⟶ G).left = m.left ≫ (1 : X ⟶ G).left := fun m => by
    rw [← Over.comp_left, MonObj.comp_one]
  refine ⟨E, e ≫ u ≫ fst G G, e ≫ u ≫ snd G G, ?_, ⟨le_comp e k₁, one_mem h₁ E, fun j hj => ?_⟩,
    le_comp e k₂, ?_, fun Y k g hk hg hkg => ?_⟩
  · have : lift (e ≫ u ≫ fst G G) (e ≫ u ≫ snd G G) = e ≫ u := by ext1 <;> simp
    rw [this]
    exact inferInstanceAs (IsImmersion (e.left ≫ U.ι))
  · rw [← appTop_appLE e.left _ (e ≫ u ≫ fst G G).left rfl _ k₁, ← appTop_appLE e.left _ _ (one e) _ (one_mem h₁ X)]
    exact h ⟨j, hj⟩
  · rw [← MonObj.comp_mul, ← MonObj.comp_mul]
    exact le_comp e k₃
  · obtain ⟨hk, hk₁, hr⟩ := hk
    have hm : ⊤ ≤ (lift k g).left ⁻¹ᵁ U := by
      change ⊤ ≤ (lift k g ≫ fst G G).left ⁻¹ᵁ C.W a ⊓ ((lift k g ≫ snd G G).left ⁻¹ᵁ V ⊓
        (lift k g ≫ (fst G G * snd G G)).left ⁻¹ᵁ V)
      refine le_inf ?_ (le_inf ?_ ?_)
      · rwa [lift_fst]
      · rwa [lift_snd]
      · rwa [MonObj.comp_mul, lift_fst, lift_snd]
    have hr' : Set.range (lift k g).left ⊆ Set.range U.ι := by
      rintro _ ⟨y, rfl⟩
      rw [U.range_ι]
      exact hm (Set.mem_univ y)
    let m : Y ⟶ X := Over.homMk (IsOpenImmersion.lift U.ι (lift k g).left hr') (by
      change _ ≫ U.ι ≫ _ = _
      rw [IsOpenImmersion.lift_fac_assoc, Over.w])
    have hmu : m ≫ u = lift k g := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
    have hmk : k.left = m.left ≫ (u ≫ fst G G).left := by
      rw [← Over.comp_left, ← Category.assoc, hmu, lift_fst]
    obtain ⟨q, hq⟩ := hE Y m fun l => by
      rw [appTop_appLE m.left _ _ hmk _ k₁ hk, appTop_appLE m.left _ _ (one m) _ (one_mem h₁ X) hk₁]
      exact hr l.1 l.2
    exact ⟨q, by rw [← Category.assoc, hq, ← Category.assoc, hmu, lift_fst],
      by rw [← Category.assoc, hq, ← Category.assoc, hmu, lift_snd]⟩

end

theorem range_jK (R : Type) [CommRing R] [IsDomain R] :
    Set.range (Out.jK R) = {(⊥ : PrimeSpectrum R)} := by
  have key : ∀ y, Out.jK R y = (⊥ : PrimeSpectrum R) := fun y => by
    apply PrimeSpectrum.ext
    obtain rfl : y = (⊥ : PrimeSpectrum (FractionRing R)) :=
      Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact key y
  · rintro rfl
    exact ⟨(⊥ : PrimeSpectrum (FractionRing R)), key _⟩

theorem pull_eq {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {F : G'.left ⟶ G.left} [IsAffineHom F] (hF : IsGrpPullback G' G f F) (C : Charts G.left) {a}
    (V : G.left.Opens) (x : Γ(G.left, V))
    (H : ∀ (Y : Over S') (k g : Y ⟶ G'), (C.pull F).InK a k → ∀ h h',
      ((k * g).left.appLE (F ⁻¹ᵁ V) ⊤ h').hom ((F.app V).hom x) =
        (g.left.appLE (F ⁻¹ᵁ V) ⊤ h).hom ((F.app V).hom x))
    {E : Over S} {k₀ g₀ : E ⟶ G} (hk₀ : C.InK a k₀) (hg₀ : ⊤ ≤ g₀.left ⁻¹ᵁ V) (hm₀ : ⊤ ≤ (k₀ * g₀).left ⁻¹ᵁ V) :
    (pullback.fst E.hom f).appTop.hom (((k₀ * g₀).left.appLE V ⊤ hm₀).hom x) =
      (pullback.fst E.hom f).appTop.hom ((g₀.left.appLE V ⊤ hg₀).hom x) := by
  let Y : Over S' := Over.mk (pullback.snd E.hom f)
  let p : Over.mk (Y.hom ≫ f) ⟶ E := Over.homMk (pullback.fst E.hom f) pullback.condition
  have A : ∀ z : E ⟶ G, ∃ z' : Y ⟶ G', (p ≫ z).left = z'.left ≫ F := fun z =>
    ⟨Over.homMk (hF.1.lift _ _ (Over.w (p ≫ z))) (hF.1.lift_snd _ _ _), (hF.1.lift_fst _ _ _).symm⟩
  obtain ⟨k, Ak⟩ := A k₀
  obtain ⟨g, Ag⟩ := A g₀
  have hk : pushPt hF.1.w k = p ≫ k₀ := Over.OverMorphism.ext Ak.symm
  have hm := hF.2 Y _ _ _ _ Ak Ag
  rw [← MonObj.comp_mul] at hm
  have l₁ := le_comp p hg₀
  have l₂ := le_comp p hm₀
  have l₁' := l₁
  have l₂' := l₂
  rw [Ag] at l₁'
  rw [hm] at l₂'
  have h0 := H Y k g ((inK_push hF C a _).2 (hk ▸ inK_comp p hk₀)) l₁' l₂'
  exact (appTop_appLE p.left _ _ rfl V hm₀ l₂ x).trans <| (appLE_app _ _ _ hm V l₂' l₂ x).symm.trans <|
    h0.trans <| (appLE_app _ _ _ Ag V l₁' l₁ x).trans (appTop_appLE p.left _ _ rfl V hg₀ l₁ x).symm

theorem exists_scal_mul_inv {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {G : Over (Sp R)} [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (C : Charts G.left)
    [IsAffineHom (pullback.fst G.hom (Out.jK R))] {a} (h₁ : ⊤ ≤ eSec G ⁻¹ᵁ C.W a) (V : G.left.Opens)
    (x : Γ(G.left, V))
    (H : ∀ (Y : Over (Sp (FractionRing R))) (k g : Y ⟶ (Over.pullback (Out.jK R)).obj G),
      Charts.InK (H := (Over.pullback (Out.jK R)).obj G) (C.pull (pullback.fst G.hom (Out.jK R))) a k →
      ∀ h h', ((k * g).left.appLE (pullback.fst G.hom (Out.jK R) ⁻¹ᵁ V) ⊤ h').hom
          (((pullback.fst G.hom (Out.jK R)).app V).hom x) =
        (g.left.appLE (pullback.fst G.hom (Out.jK R) ⁻¹ᵁ V) ⊤ h).hom
          (((pullback.fst G.hom (Out.jK R)).app V).hom x)) :
    ∃ b : R, b ≠ 0 ∧ ∀ (Y : Over (Sp R)) (k g : Y ⟶ G), C.InK a k → ∀ h h',
      Out.scal Y.hom b * (((k * g).left.appLE V ⊤ h').hom x - (g.left.appLE V ⊤ h).hom x) = 0 := by
  obtain ⟨E, k₀, g₀, him, hk₀, hg₀, hm₀, hE⟩ := exists_universal C h₁ V
  have i₁ : LocallyOfFiniteType (G ⊗ G).hom := inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G.hom ≫ G.hom))
  have i₂ : QuasiCompact (G ⊗ G).hom := inferInstanceAs (QuasiCompact (pullback.fst G.hom G.hom ≫ G.hom))
  have : IsLocallyNoetherian (G ⊗ G).left := LocallyOfFiniteType.isLocallyNoetherian (G ⊗ G).hom
  have : CompactSpace (G ⊗ G).left := QuasiCompact.compactSpace_of_compactSpace (G ⊗ G).hom
  have : IsNoetherian (G ⊗ G).left := {}
  have : TopologicalSpace.NoetherianSpace E.left := (lift k₀ g₀).left.isEmbedding.isInducing.noetherianSpace
  have : LocallyOfFiniteType E.hom := by rw [← Over.w (lift k₀ g₀)]; infer_instance
  have : QuasiCompact E.hom := ⟨fun U _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hD : Dense ({(⊥ : PrimeSpectrum R)} : Set (Sp R)) := by
    change Dense ({(⊥ : PrimeSpectrum R)} : Set (PrimeSpectrum R))
    rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
    exact PrimeSpectrum.zeroLocus_bot
  obtain ⟨b, hb0, hb⟩ := GenericEq.exists_scal_mul_eq_zero R E _ hD
    (((k₀ * g₀).left.appLE V ⊤ hm₀).hom x - (g₀.left.appLE V ⊤ hg₀).hom x) (by
    rintro _ rfl
    refine ⟨FractionRing R, inferInstance, Out.jK R, range_jK R, ?_⟩
    rw [map_sub, sub_eq_zero]
    exact pull_eq (isGrpPullback_pullback G (Out.jK R)) C V x H hk₀ hg₀ hm₀)
  refine ⟨b, hb0, fun Y k g hk h h' => ?_⟩
  obtain ⟨q, rfl, rfl⟩ := hE Y k g hk h h'
  have h0 := congrArg q.left.appTop.hom hb
  rw [map_mul, map_zero, map_sub, GenericEq.appTop_scal, Over.w,
    appTop_appLE q.left _ (q ≫ g₀).left rfl V hg₀ h,
    appTop_appLE q.left _ ((q ≫ k₀) * (q ≫ g₀)).left (by rw [← MonObj.comp_mul]; rfl) V hm₀ h'] at h0
  exact h0

theorem hasWt_fibre {R K : Type} [CommRing R] [Field K] {G : Over (Sp R)} [GrpObj G] (C : Charts G.left)
    (ψ : CommRingCat.of R ⟶ CommRingCat.of K) [IsAffineHom (pullback.fst G.hom (Spec.map ψ))]
    {a} (h₁ : ⊤ ≤ eSec G ⁻¹ᵁ C.W a) {V : G.left.Opens} {x : Γ(G.left, V)} {b : R} (hb : ψ.hom b ≠ 0)
    (H : ∀ (Y : Over (Sp R)) (k g : Y ⟶ G), C.InK a k → ∀ h h',
      Out.scal Y.hom b * (((k * g).left.appLE V ⊤ h').hom x - (g.left.appLE V ⊤ h).hom x) = 0)
    {d : ℕ} {c : Fin d → C.Cl} {i : splitTorus (Sp K) (Fin d → ℤ) ⟶ (Over.pullback (Spec.map ψ)).obj G}
    (hT : Charts.Torus (H := (Over.pullback (Spec.map ψ)).obj G) (C.pull (pullback.fst G.hom (Spec.map ψ))) c i) :
    HasWt i (pullback.fst G.hom (Spec.map ψ) ⁻¹ᵁ V) (((pullback.fst G.hom (Spec.map ψ)).app V).hom x) 0 := by
  intro Y t g h h'
  have hF := isGrpPullback_pullback G (Spec.map ψ)
  have e₁ : (1 : Over.mk (Y.hom ≫ Spec.map ψ) ⟶ G).left =
      (1 : Y ⟶ (Over.pullback (Spec.map ψ)).obj G).left ≫ pullback.fst G.hom (Spec.map ψ) :=
    (congrArg (fun z => z.left) (map_one (pushHom hF Y))).symm
  have o := one_mem h₁ (Over.mk (Y.hom ≫ Spec.map ψ))
  rw [e₁] at o
  have hk := (inK_push hF C a _).1 (inK_torus hT (a := a) o t)
  have hm := hF.2 Y (t ≫ i) g (pushPt hF.1.w (t ≫ i)) (pushPt hF.1.w g) rfl rfl
  have l : ⊤ ≤ (pushPt hF.1.w (t ≫ i) * pushPt hF.1.w g).left ⁻¹ᵁ V := by rw [hm]; exact h'
  have h0 := H _ _ (pushPt hF.1.w g) hk h l
  have hu : IsUnit (Out.scal (Y.hom ≫ Spec.map ψ) b) := by
    rw [← GenericEq.appTop_scal]
    refine IsUnit.map _ ?_
    have n := congrArg (fun k => k.hom b) (Scheme.ΓSpecIso_inv_naturality ψ)
    exact (show Out.scal (Spec.map ψ) b = _ from n.symm) ▸ hb.isUnit.map (Scheme.ΓSpecIso (.of K)).inv.hom
  rw [charUnit_zero_val, map_one, _root_.one_mul]
  exact (appLE_app _ _ _ hm V h' l x).trans <| (sub_eq_zero.1 (hu.mul_right_eq_zero.1 h0)).trans
    (appLE_app g.left _ (pushPt hF.1.w g).left rfl V h h x).symm

theorem generic_invariants : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∀ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i → (∀ a', Stable i ((C.pull (pullback.fst G.hom (Out.jK R))).W a')) → ∀ a' (u : Γ(((Over.pullback (Out.jK R)).obj G).left, (C.pull (pullback.fst G.hom (Out.jK R))).W a')), HasWt i _ u 0 → u ∈ Subring.closure (Set.range (((Over.pullback (Out.jK R)).obj G).hom.appLE ⊤ ((C.pull (pullback.fst G.hom (Out.jK R))).W a') le_top).hom ∪ {v | ∃ j', C.wt j' = C.c₀ ∧ v = (C.pull (pullback.fst G.hom (Out.jK R))).r a' j'}) := by
  intro R _ _ _ G _ _ _ _ _ C d c Sg _ hD hS a j hB i hi _ a' u hu
  change Γ(pullback G.hom (Out.jK R), pullback.fst G.hom (Out.jK R) ⁻¹ᵁ C.W a') at u
  let φ : CommRingCat.of R ⟶ Γ(G.left, C.W a') := (Scheme.ΓSpecIso (.of R)).inv ≫ G.hom.appLE ⊤ (C.W a') le_top
  letI : Algebra R Γ(G.left, C.W a') := φ.hom.toAlgebra
  have : Algebra.FiniteType R Γ(G.left, C.W a') :=
    (G.hom.finiteType_appLE (isAffineOpen_top _) (C.aff a') le_top).comp
      (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).2)
  have po := isPushout_sections (CommRingCat.ofHom (algebraMap R (FractionRing R))) G.hom (C.aff a')
  obtain ⟨s, x, hs, hx⟩ := exists_clear po u
  set p := (pullback.fst G.hom (Out.jK R)).app (C.W a') with hp
  set q := (pullback.snd G.hom (Out.jK R)).appLE ⊤ (pullback.fst G.hom (Out.jK R) ⁻¹ᵁ C.W a') le_top with hq
  have hw : ∀ r : R, p.hom (φ.hom r) =
      q.hom ((Scheme.ΓSpecIso (.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r)) :=
    fun r => congrArg (fun k => k.hom r) po.w
  change p.hom (φ.hom s) * u = p.hom x at hx
  obtain ⟨b, hb0, hb⟩ := exists_scal_mul_inv C hB.1 (C.W a') x (by
    intro Y k g hk h h'
    obtain ⟨t, rfl⟩ := (hi.2.1 Y k).1 hk
    have h0 := hu Y t g h h'
    rw [charUnit_zero_val, map_one, _root_.one_mul] at h0
    have e : ∀ (z : Y ⟶ (Over.pullback (Out.jK R)).obj G) hz v,
        (z.left.appLE (pullback.fst G.hom (Out.jK R) ⁻¹ᵁ C.W a') ⊤ hz).hom (q.hom v) = Y.hom.appTop.hom v :=
      fun z hz v => appLE_appLE_top _ _ _ (Over.w z) _ _ _
    rw [← hp, ← hx, hw, map_mul, map_mul]
    exact congrArg₂ (· * ·) ((e _ _ _).trans (e _ _ _).symm) h0)
  let T : Set Γ(G.left, C.W a') := Set.range fun l : {l // C.wt l = C.c₀} => C.r a' l.1
  obtain ⟨r, hr0, hr⟩ := exists_smul_mem_of_dense_fibres R Γ(G.left, C.W a') (Algebra.adjoin R T) x
    (Sg ∩ (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum R)))
    (Subalgebra.fg_def.2 ⟨T, Set.finite_range _, rfl⟩)
    (Dense.inter_of_isOpen_right (X := PrimeSpectrum R) hD
      ((PrimeSpectrum.basicOpen b).isOpen.dense ⟨⊥, hb0⟩) (PrimeSpectrum.basicOpen b).isOpen) (by
    rintro P ⟨hP, hPb⟩
    obtain ⟨K, _, t, _, ht, -, i', hT⟩ := hS P hP
    obtain ⟨ψ, rfl⟩ := Spec.map_surjective t
    letI : Algebra R K := ψ.hom.toAlgebra
    have hker : RingHom.ker (algebraMap R K) = P.asIdeal := by
      have : Spec.map ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) = P := ht.le (Set.mem_range_self _)
      rw [← this]
      rfl
    refine ⟨K, inferInstance, inferInstance, hker, ?_⟩
    have hg := hT.gen a' _ (hasWt_fibre C ψ hB.1 (fun e => hPb (hker.le e)) hb hT)
    refine one_tmul_mem_range (isPushout_sections ψ G.hom (C.aff a')) T x (Subring.closure_mono ?_ hg)
    rintro _ (⟨w, rfl⟩ | ⟨l, hl, rfl⟩)
    · refine Or.inl ⟨(Scheme.ΓSpecIso (.of K)).hom.hom w, ?_⟩
      rw [CommRingCat.hom_comp, RingHom.comp_apply, Iso.hom_inv_id_apply]
      rfl
    · exact Or.inr ⟨_, ⟨⟨l, hl⟩, rfl⟩, rfl⟩)
  set B := Subring.closure (Set.range q.hom ∪ {v | ∃ j', C.wt j' = C.c₀ ∧ v = p.hom (C.r a' j')}) with hBdef
  change u ∈ B
  have h1 : ∀ y ∈ Algebra.adjoin R T, p.hom y ∈ B := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨l, rfl⟩ := hy
      exact Subring.subset_closure (Or.inr ⟨l.1, l.2, rfl⟩)
    | algebraMap r => exact Subring.subset_closure (Or.inl ⟨_, (hw r).symm⟩)
    | add y z _ _ hy hz => rw [map_add]; exact B.add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact B.mul_mem hy hz
  have h2 := h1 _ hr
  have hne : algebraMap R (FractionRing R) (r * s) ≠ 0 := fun e =>
    mul_ne_zero hr0 hs ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective R (FractionRing R)) _ e)
  have h3 : u = q.hom ((Scheme.ΓSpecIso (.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) (r * s))⁻¹) *
      p.hom (r • x) := by
    rw [Algebra.smul_def, map_mul p.hom, ← hx, ← _root_.mul_assoc, ← _root_.mul_assoc]
    change u = _ * p.hom (φ.hom r) * _ * _
    rw [hw, hw, ← map_mul q.hom, ← map_mul q.hom, ← map_mul, ← map_mul, _root_.mul_assoc _⁻¹, ← map_mul, inv_mul_cancel₀ hne,
      map_one, map_one, _root_.one_mul]
  rw [h3]
  exact B.mul_mem (Subring.subset_closure (Or.inl ⟨_, rfl⟩)) h2

end GlobalTheory.ZJ.GenericInv
end

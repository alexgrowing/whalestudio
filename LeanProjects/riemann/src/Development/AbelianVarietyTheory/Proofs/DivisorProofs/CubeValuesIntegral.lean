import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

theorem exists_smooth_chart {O : Type} [CommRing O] (X : Over (Sp O)) [Smooth X.hom] (W : X.left.Opens)
    (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B] (w : specO O B ⟶ X) (hw : InOpen W w) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : Algebra.Smooth O R) (θ : R →ₐ[O] B)
      (r : specO O R ⟶ X), ptMap θ ≫ r = w ∧ InOpen W r := by
  let w₀ : Spec (CommRingCat.of B) ⟶ X.left := w.left
  have hx : w₀ (IsLocalRing.closedPoint B) ∈ W := by
    have : IsLocalRing.closedPoint B ∈ w₀ ⁻¹ᵁ W := by
      rw [show w₀ ⁻¹ᵁ W = ⊤ from hw]; trivial
    exact this
  obtain ⟨R, f, hf, h1, h2⟩ := Scheme.exists_affine_mem_range_and_range_subset hx
  have hr : Set.range w₀ ⊆ Set.range f := by
    have : w₀ ⁻¹ᵁ f.opensRange = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem w₀ h1
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ w₀ ⁻¹ᵁ f.opensRange := by rw [this]; trivial
    exact hy
  let l := IsOpenImmersion.lift f w₀ hr
  have hl : l ≫ f = w₀ := IsOpenImmersion.lift_fac _ _ _
  let α : CommRingCat.of O ⟶ R := Spec.preimage (f ≫ X.hom)
  have hα : Spec.map α = f ≫ X.hom := Spec.map_preimage _
  letI : Algebra O R := α.hom.toAlgebra
  have hs : Smooth (Spec.map α) := by rw [hα]; infer_instance
  have hs' : α.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 hs
  let β : R ⟶ CommRingCat.of B := Spec.preimage l
  have hβ : Spec.map β = l := Spec.map_preimage _
  have hc : α ≫ β = CommRingCat.ofHom (algebraMap O B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, hβ, ← Category.assoc, hl]
    exact Over.w w
  let θ : R →ₐ[O] B := ⟨β.hom, fun a => congrArg (fun g => g.hom a) hc⟩
  refine ⟨R, inferInstance, inferInstance, hs', θ, Over.homMk f hα.symm, ?_, ?_⟩
  · ext1
    exact (congrArg (· ≫ f) hβ).trans hl
  · exact top_le_iff.1 fun y _ => h2 ⟨y, rfl⟩

theorem CubeIn.comp {S : Scheme.{0}} {X T T' : Over S} [GrpObj X] {U : X.left.Opens} {z a b c : T ⟶ X}
    (h : CubeIn U z a b c) (u : T' ⟶ T) : CubeIn U (u ≫ z) (u ≫ a) (u ≫ b) (u ≫ c) := by
  intro i j k hi hj hk
  have := (h i j k hi hj hk).comp u
  simpa only [MonObj.comp_mul, MonObj.comp_pow] using this

theorem exists_smooth_cube {O : Type} [CommRing O] (G : Over (Sp O)) [GrpObj G] [Smooth G.hom]
    (U : G.left.Opens) (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B] (z a b c : specO O B ⟶ G)
    (h : CubeIn U z a b c) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : Algebra.Smooth O R) (θ : R →ₐ[O] B)
      (z₀ a₀ b₀ c₀ : specO O R ⟶ G), ptMap θ ≫ z₀ = z ∧ ptMap θ ≫ a₀ = a ∧ ptMap θ ≫ b₀ = b ∧
        ptMap θ ≫ c₀ = c ∧ CubeIn U z₀ a₀ b₀ c₀ := by
  have h2 : ∀ X Y : Over (Sp O), Smooth X.hom → Smooth Y.hom → Smooth (X ⊗ Y).hom := by
    intro X Y hX hY
    have : Smooth (pullback.fst X.hom Y.hom) :=
      smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback X.hom Y.hom).flip hY
    exact inferInstanceAs (Smooth (pullback.fst X.hom Y.hom ≫ X.hom))
  let X : Over (Sp O) := (G ⊗ G) ⊗ (G ⊗ G)
  haveI : Smooth X.hom := h2 _ _ (h2 _ _ ‹_› ‹_›) (h2 _ _ ‹_› ‹_›)
  let p₁ : X ⟶ G := fst _ _ ≫ fst _ _
  let p₂ : X ⟶ G := fst _ _ ≫ snd _ _
  let p₃ : X ⟶ G := snd _ _ ≫ fst _ _
  let p₄ : X ⟶ G := snd _ _ ≫ snd _ _
  let w : specO O B ⟶ X := lift (lift z a) (lift b c)
  have e₁ : w ≫ p₁ = z := by simp [w, p₁]
  have e₂ : w ≫ p₂ = a := by simp [w, p₂]
  have e₃ : w ≫ p₃ = b := by simp [w, p₃]
  have e₄ : w ≫ p₄ = c := by simp [w, p₄]
  let V : ℕ × ℕ × ℕ → X.left.Opens := fun n => (p₁ * p₂ ^ n.1 * p₃ ^ n.2.1 * p₄ ^ n.2.2).left ⁻¹ᵁ U
  let s : Finset (ℕ × ℕ × ℕ) := Finset.Iic (1, 1, 1)
  have key : ∀ {T : Over (Sp O)} (r : T ⟶ X),
      InOpen (s.inf V) r ↔ CubeIn U (r ≫ p₁) (r ≫ p₂) (r ≫ p₃) (r ≫ p₄) := by
    intro T r
    have e : ∀ n : ℕ × ℕ × ℕ, InOpen (V n) r ↔
        InOpen U ((r ≫ p₁) * (r ≫ p₂) ^ n.1 * (r ≫ p₃) ^ n.2.1 * (r ≫ p₄) ^ n.2.2) := by
      intro n
      simp only [← MonObj.comp_pow, ← MonObj.comp_mul]
      unfold InOpen
      rw [Over.comp_left, Scheme.Hom.comp_preimage]
    constructor
    · intro hr i j k hi hj hk
      refine (e (i, j, k)).1 (top_le_iff.1 ?_)
      rw [← show r.left ⁻¹ᵁ s.inf V = ⊤ from hr]
      exact Scheme.Hom.preimage_mono _ (Finset.inf_le (by simp [s, hi, hj, hk]))
    · intro hr
      refine top_le_iff.1 fun y _ => ?_
      change r.left y ∈ ((s.inf V : X.left.Opens) : Set X.left)
      rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
      refine Set.mem_iInter₂.2 fun n hn => ?_
      obtain ⟨h1, h2, h3⟩ := Finset.mem_Iic.1 hn
      have : y ∈ r.left ⁻¹ᵁ V n := by
        rw [show r.left ⁻¹ᵁ V n = ⊤ from (e n).2 (hr _ _ _ h1 h2 h3)]; trivial
      exact this
  obtain ⟨R, _, _, _, θ, r, hr, hW⟩ := exists_smooth_chart X (s.inf V) B w
    ((key w).2 (by rwa [e₁, e₂, e₃, e₄]))
  refine ⟨R, _, _, ‹_›, θ, r ≫ p₁, r ≫ p₂, r ≫ p₃, r ≫ p₄, ?_, ?_, ?_, ?_, (key r).1 hW⟩ <;>
    rw [← Category.assoc, hr] <;> assumption

def pushPt {S S' : Scheme.{0}} {A : Over S'} [GrpObj A] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : A.left ⟶ G.left} (h : IsGrpPullback A G f φ) (T : Over S') :
    (T ⟶ A) →* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MonoidHom.mk' (fun x => Over.homMk (x.left ≫ φ) (by
      change (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]))
    fun x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

theorem exists_generic_cube {S S' : Scheme.{0}} {A : Over S'} [GrpObj A] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : A.left ⟶ G.left} (h : IsGrpPullback A G f φ) (T : Over S') (U : G.left.Opens)
    (z a b c : Over.mk (T.hom ≫ f) ⟶ G) (hc : CubeIn U z a b c) :
    ∃ z' a' b' c' : T ⟶ A, z'.left ≫ φ = z.left ∧ a'.left ≫ φ = a.left ∧ b'.left ≫ φ = b.left ∧
      c'.left ≫ φ = c.left ∧ CubeIn (φ ⁻¹ᵁ U) z' a' b' c' := by
  have hs : Function.Surjective (pushPt h T) := fun x =>
    ⟨Over.homMk (h.1.lift x.left T.hom (Over.w x)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  obtain ⟨z, rfl⟩ := hs z
  obtain ⟨a, rfl⟩ := hs a
  obtain ⟨b, rfl⟩ := hs b
  obtain ⟨c, rfl⟩ := hs c
  refine ⟨z, a, b, c, rfl, rfl, rfl, rfl, fun i j k hi hj hk => ?_⟩
  have := hc i j k hi hj hk
  simp only [← map_pow, ← map_mul] at this
  exact this

theorem exists_numerator {O C : Type} [CommRing O] [IsDomain O] [Field C] [Algebra O C] [IsFractionRing O C]
    (R : Type) [CommRing R] [Algebra O R] (s : (C ⊗[O] R)ˣ) :
    ∃ (f g : R) (c e : O), c ≠ 0 ∧ e ≠ 0 ∧ f * g = algebraMap O R c ∧
      (1 : C) ⊗ₜ[O] f = algebraMap O (C ⊗[O] R) e * s := by
  let m : R →ₗ[O] C ⊗[O] R := TensorProduct.mk O C R 1
  haveI : IsLocalizedModule (nonZeroDivisors O) m :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) C m).2 (TensorProduct.isBaseChange O R C)
  obtain ⟨⟨f, e₁⟩, hf⟩ := IsLocalizedModule.surj (nonZeroDivisors O) m (s : C ⊗[O] R)
  obtain ⟨⟨g, e₂⟩, hg⟩ := IsLocalizedModule.surj (nonZeroDivisors O) m (s⁻¹ : (C ⊗[O] R)ˣ)
  have hf' : (1 : C) ⊗ₜ[O] f = (e₁ : O) • (s : C ⊗[O] R) := hf.symm
  have hg' : (1 : C) ⊗ₜ[O] g = (e₂ : O) • ((s⁻¹ : (C ⊗[O] R)ˣ) : C ⊗[O] R) := hg.symm
  have h : m (f * g) = m (((e₁ : O) * e₂) • 1) := by
    have : m (f * g) = ((1 : C) ⊗ₜ[O] f) * ((1 : C) ⊗ₜ[O] g) := by simp [m]
    rw [this, hf', hg', smul_mul_smul_comm, Units.mul_inv, map_smul]
    rfl
  obtain ⟨e₃, h₃⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O) h
  have n := fun x : nonZeroDivisors O => nonZeroDivisors.coe_ne_zero x
  refine ⟨(e₃ : O) • f, g, e₃ * (e₁ * e₂), e₃ * e₁, mul_ne_zero (n _) (mul_ne_zero (n _) (n _)),
    mul_ne_zero (n _) (n _), ?_, ?_⟩
  · rw [smul_mul_assoc, Algebra.algebraMap_eq_smul_one, mul_smul]
    exact h₃
  · rw [TensorProduct.tmul_smul, hf', smul_smul, Algebra.smul_def]

theorem cubeValuesIntegral_of_localUnits {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0}
    {O : Type} [CommRing O] [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)
    (hL : LocalUnits O) : CubeValuesIntegral P := by
  rintro U Θ hΘ B _ _ _ _ _ ⟨ψ₀⟩ z a b c hcube
  have hinj := P.integers.hom_inj
  haveI : IsDomain O := hinj.isDomain (algebraMap O C)
  haveI : IsFractionRing O C := P.integers.isFractionRing
  haveI : Smooth P.G.hom := P.semi.smooth
  obtain ⟨R, _, _, _, θ, z₀, a₀, b₀, c₀, rfl, rfl, rfl, rfl, h₀⟩ := exists_smooth_cube P.G U B z a b c hcube
  let iC : C →+* C ⊗[O] R := Algebra.TensorProduct.includeLeftRingHom
  let iR : R →+* C ⊗[O] R := (Algebra.TensorProduct.includeRight (R := O) (A := C) (B := R)).toRingHom
  let t : Sp (C ⊗[O] R) ⟶ Sp C := spMap iC
  let m : Over.mk ((Over.mk t).hom ≫ spMap (algebraMap O C)) ⟶ specO O R := Over.homMk (spMap iR) (by
    change spMap iR ≫ spMap (algebraMap O R) = spMap iC ≫ spMap (algebraMap O C)
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm)
  obtain ⟨z₁, a₁, b₁, c₁, hz, ha, hb, hc, h₁⟩ :=
    exists_generic_cube P.gen_pull (Over.mk t) U _ _ _ _ (h₀.comp m)
  obtain ⟨f, g, k, e, hk, he, hfg, hf⟩ := exists_numerator R (Θ _ t z₁ a₁ b₁ c₁)
  obtain ⟨u, hu⟩ := hL R B θ ψ₀ f g k hk hfg
  have hd : ψ₀ (θ f) ≠ 0 := by
    have := congrArg (fun x => ψ₀ (θ x)) hfg
    simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at this
    exact left_ne_zero_of_mul (this ▸ hk)
  have he' : algebraMap O C e ≠ 0 := (map_ne_zero_iff _ hinj).2 he
  refine ⟨Units.mk0 (algebraMap O C (ψ₀ (θ f)) / algebraMap O C e)
    (div_ne_zero ((map_ne_zero_iff _ hinj).2 hd) he'), u, fun ψ z' a' b' c' hz' ha' hb' hc' => ?_⟩
  let φ : C ⊗[O] R →ₐ[O] C := Algebra.TensorProduct.lift (AlgHom.id O C)
    ((Algebra.ofId O C).comp (ψ.comp θ)) fun _ _ => Commute.all _ _
  have key : ∀ (x₀ : specO O R ⟶ P.G) (x₁ : Over.mk t ⟶ P.A.A) (x' : Pts P.A.A),
      x₁.left ≫ P.gen = (m ≫ x₀).left → IsGeneric P (ptMap ψ ≫ ptMap θ ≫ x₀) x' →
      x'.left = spMap φ.toRingHom ≫ x₁.left := by
    intro x₀ x₁ x' h h'
    refine P.gen_pull.1.hom_ext ?_ ?_
    · refine h'.trans ?_
      refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (spMap φ.toRingHom ≫ ·) h)).symm
      change spMap (algebraMap O C) ≫ spMap ψ.toRingHom ≫ spMap θ.toRingHom ≫ x₀.left =
        spMap φ.toRingHom ≫ spMap iR ≫ x₀.left
      simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      ext x
      simp [φ, iR]
    · refine (Over.w x').trans ?_
      refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (spMap φ.toRingHom ≫ ·) (Over.w x₁))).symm
      change 𝟙 (Sp C) = spMap φ.toRingHom ≫ spMap iC
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
      congr 1
      ext x
      simp [φ, iC]
  rw [hΘ _ _ φ.toRingHom t _ z₁ a₁ b₁ c₁ z' a' b' c' (key _ _ _ hz hz') (key _ _ _ ha ha') (key _ _ _ hb hb')
    (key _ _ _ hc hc') h₁]
  have h2 := congrArg φ hf
  rw [map_mul, AlgHom.commutes] at h2
  have h3 : φ ((1 : C) ⊗ₜ[O] f) = algebraMap O C (ψ (θ f)) := by simp [φ]
  have h4 : ψ (θ f) = ψ₀ (θ f) * ψ u := by
    conv_lhs => rw [hu]
    simp
  rw [h3, h4, map_mul] at h2
  change φ _ = _
  rw [Units.val_mk0, div_mul_eq_mul_div, h2, mul_div_cancel_left₀ _ he']

theorem cubeValuesIntegral (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ) : LocalUnits O → CubeValuesIntegral P :=
  cubeValuesIntegral_of_localUnits P

end GlobalTheory.WeilIntegral

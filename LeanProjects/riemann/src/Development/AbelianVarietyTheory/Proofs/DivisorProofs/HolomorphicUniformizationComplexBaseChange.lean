import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.UnifTan

theorem valR_comp_eq {A : Type} [CommRing A] {X Y : Scheme.{0}} (p : Sp A ⟶ X) (ψ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valR (p ≫ ψ) U f = valR p (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) := by
  first
  | exact @_root_.GlobalTheory.ValuationCompositionDivisor.valR_comp
  | exact _root_.GlobalTheory.ValuationCompositionDivisor.valR_comp
  | (apply _root_.GlobalTheory.ValuationCompositionDivisor.valR_comp <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationCompositionDivisor.valR_comp <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationCompositionDivisor.valR_comp <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationCompositionDivisor.valR_comp ..)

theorem valF_eq_valAt' {X : Scheme.{0}} (p : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valF p U f = valAt' p U f := by
  unfold valF valAt' valAt
  split_ifs <;> rfl

theorem valR_eq_valAt' {X : Scheme.{0}} (p : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valR p U f = valAt' p U f := by
  unfold valR valAt' valAt
  split_ifs <;> rfl

theorem valAt'_comp_eq {X Y : Scheme.{0}} (p : Sp ℂ ⟶ X) (ψ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (p ≫ ψ) U f = valAt' p (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) := by
  rw [← valR_eq_valAt', ← valR_eq_valAt', valR_comp_eq]

theorem prime_subsingleton : Subsingleton (PrimeSpectrum (DualNumber ℂ)) := by
  constructor
  have key : ∀ (P : PrimeSpectrum (DualNumber ℂ)) (z : DualNumber ℂ), z ∈ P.asIdeal ↔ z.fst = 0 := by
    intro P z
    constructor
    · intro hz
      by_contra hne
      have hu : IsUnit z := (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (isUnit_iff_ne_zero.2 hne)
      exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hz hu)
    · intro hz
      have h2 : z * z = 0 := by
        ext <;> simp [hz]
      have : z * z ∈ P.asIdeal := by rw [h2]; exact P.asIdeal.zero_mem
      rcases P.isPrime.mem_or_mem this with h | h <;> exact h
  intro P Q
  ext z
  rw [key P, key Q]

theorem top_le_of_red {X : Scheme.{0}} (p : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) (h : ⊤ ≤ (redE ℂ ≫ p) ⁻¹ᵁ U) :
    ⊤ ≤ p ⁻¹ᵁ U := by
  intro y _
  have hy : y = redE ℂ (IsLocalRing.closedPoint ℂ) := by
    haveI := prime_subsingleton
    exact Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) _ _
  have := h (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  rw [hy]
  exact this

theorem tf_hom (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] :
    (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := by
  simp only [TF, jFK, jK, Over.mk_hom, spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem ex_zero {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) :
    (u.ex 0).left = η[A].left := by
  have h1 : u.ex 0 = 1 := by
    have := u.ex_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  rw [h1, Hom.one_def]
  simp

theorem isD_iff_isDiff : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (N : NumD ℂ)
    (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g) (φ : x.P.A.left ⟶ D.P.A.left),
    IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ → (∀ z, (ν.eA (d.ex z)).left = (u.ex z).left ≫ φ) →
    ∀ (b' : epsR ℂ ⟶ x.P.A) (b : TE R ℂ ⟶ D.P.A), IsTangent b' → b'.left ≫ φ = b.left →
      ∀ W' : Fin g → ℂ, (IsD ν d W' b ↔ u.IsDiff W' b') := by
  intro R _ _ _ D N ν g d x u φ hφ hE b' b hb' hbb W'
  have hP : IsPullback x.P.A.hom φ (TF (R := R) ℂ).hom D.P.A.hom := by
    rw [tf_hom]; exact hφ.1.flip
  let e := hP.isoPullback
  let ψ : x.P.A.left ⟶ (DegPre.BF D ℂ).left := e.hom
  have hψi : ψ ≫ e.inv = 𝟙 _ := e.hom_inv_id
  have hpt : ∀ z, ptB ν d z = (u.ex z).left ≫ ψ := by
    intro z
    apply pullback.hom_ext
    · simp only [ptB, Over.lift_left, pullback.lift_fst, Category.assoc, ψ, e, IsPullback.isoPullback_hom_fst]
      have := Over.w (u.ex z)
      simpa using this.symm
    · simp only [ptB, Over.lift_left, pullback.lift_snd, Category.assoc, ψ, e, IsPullback.isoPullback_hom_snd]
      exact hE z
  have hb : (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left = b'.left ≫ ψ := by
    apply pullback.hom_ext
    · simp only [Over.lift_left, pullback.lift_fst, Category.assoc, ψ, e, IsPullback.isoPullback_hom_fst, Over.homMk_left]
      have := Over.w b'
      simpa using this.symm
    · simp only [Over.lift_left, pullback.lift_snd, Category.assoc, ψ, e, IsPullback.isoPullback_hom_snd]
      exact hbb.symm
  have hred : redE ℂ ≫ b'.left = (u.ex 0).left := by
    rw [ex_zero]; exact hb'
  have back : ∀ {A : Type} [CommRing A] (p : Sp A ⟶ x.P.A.left) (U' : x.P.A.left.Opens) (f' : Γ(x.P.A.left, U')),
      valR (p ≫ ψ) (e.inv ⁻¹ᵁ U') ((e.inv.app U').hom f') = valR p U' f' := by
    intro A _ p U' f'
    rw [← valR_comp_eq, Category.assoc, hψi, Category.comp_id]
  have valB : ∀ (U' : x.P.A.left.Opens) (h : ⊤ ≤ b'.left ⁻¹ᵁ U') (f' : Γ(x.P.A.left, U')),
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((b'.left.appLE U' ⊤ h).hom f') = valR b'.left U' f' := by
    intro U' h f'
    unfold valR
    rw [dif_pos h]
  constructor
  · intro hD U' h f'
    have h0 : ⊤ ≤ ptB ν d 0 ⁻¹ᵁ (e.inv ⁻¹ᵁ U') := by
      have hc : (((u.ex 0).left ≫ ψ) ≫ e.inv) = redE ℂ ≫ b'.left := by
        rw [Category.assoc, hψi, Category.comp_id, hred]
      rw [hpt 0]
      show ⊤ ≤ (((u.ex 0).left ≫ ψ) ≫ e.inv) ⁻¹ᵁ U'
      rw [hc]
      exact fun y _ => h (Set.mem_univ ((redE ℂ) y))
    have k := hD _ ((e.inv.app U').hom f') h0
    simp only [hb, hpt, valF_eq_valAt', ← valR_eq_valAt', back] at k
    rw [valB U' h f', k]
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, valR_eq_valAt']
  · intro hI U f h0
    have h1 : ⊤ ≤ b'.left ⁻¹ᵁ (ψ ⁻¹ᵁ U) := by
      apply top_le_of_red
      rw [hred]
      rw [hpt] at h0
      exact h0
    have hs := hI (ψ ⁻¹ᵁ U) h1 ((ψ.app U).hom f)
    rw [valB] at hs
    simp only [hb, hpt, valR_comp_eq, valF_eq_valAt', valAt'_comp_eq]
    ext
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
      rw [← hred, ← valR_eq_valAt', (GlobalTheory.ZH.CrdCalc.valR_spMap _ _ _ h1).2]
      rfl
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      exact hs

end GlobalTheory.UnifTan

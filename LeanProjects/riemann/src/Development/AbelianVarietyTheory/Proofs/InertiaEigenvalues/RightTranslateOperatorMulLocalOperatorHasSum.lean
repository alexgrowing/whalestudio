import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialLevelCosetRepresentativeMemLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eu

section Local
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem unitaryAdeleMatrix_injective (V : HSp D) : Function.Injective (Formalism.L2.Theta.mt V) := by
  intro g h hgh
  have h1 : matHom V g = matHom V h := Units.ext hgh
  exact (HR (AF D.host.F) D.sp.cm.sig V.gram).subtype_injective h1

theorem unitaryAdeleMatrix_mul (V : HSp D) (g h : GA D V) : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul]; rfl

theorem unitaryAdeleMatrix_one (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := rfl

theorem supportedAtIdempotent_iff_smul_matrix_sub_one (V : HSp D) (f : AE D) (g : GA D V) :
    SuppF V f g ↔ f • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 := by
  constructor
  · intro h; ext a b; rw [Matrix.smul_apply, smul_eq_mul]; exact h a b
  · intro h a b; have := congrFun (congrFun h a) b; rw [Matrix.smul_apply, smul_eq_mul] at this; exact this

theorem supportedAtAdeleIdempotent_mul_closed (V : HSp D) (f : AE D) {g h : GA D V} (hg : SuppF V f g) (hh : SuppF V f h) :
    SuppF V f (g * h) := by
  rw [supportedAtIdempotent_iff_smul_matrix_sub_one] at *
  have e : Formalism.L2.Theta.mt V (g * h) - 1 = (Formalism.L2.Theta.mt V g - 1) * (Formalism.L2.Theta.mt V h - 1) +
      (Formalism.L2.Theta.mt V g - 1) + (Formalism.L2.Theta.mt V h - 1) := by
    rw [unitaryAdeleMatrix_mul]; noncomm_ring
  rw [e, smul_add, smul_add, ← Matrix.smul_mul, hg, hh]

theorem supportedAtAdeleIdempotent_inv_closed (V : HSp D) (f : AE D) {g : GA D V} (hg : SuppF V f g) : SuppF V f g⁻¹ := by
  rw [supportedAtIdempotent_iff_smul_matrix_sub_one] at *
  have hm : Formalism.L2.Theta.mt V g⁻¹ * Formalism.L2.Theta.mt V g = 1 := by rw [← unitaryAdeleMatrix_mul, inv_mul_cancel]; rfl
  have e : Formalism.L2.Theta.mt V g⁻¹ - 1 = -(Formalism.L2.Theta.mt V g⁻¹ * (Formalism.L2.Theta.mt V g - 1)) := by
    rw [Matrix.mul_sub, hm]; noncomm_ring
  rw [e, smul_neg, ← Matrix.mul_smul, hg]

theorem supportedAtIdempotent_zero_eq_one (V : HSp D) {g : GA D V} (hg : SuppF V 0 g) : g = 1 := by
  rw [supportedAtIdempotent_iff_smul_matrix_sub_one, zero_smul] at hg
  apply unitaryAdeleMatrix_injective V
  rw [unitaryAdeleMatrix_one]
  exact (sub_eq_zero.mp hg.symm)

theorem rightTranslatePairingOperator_spec {R : RealDat D A Ks} {i : Fin D.R.m} (hTL : TransLaws R i) {γ : GA D (Wc D i)}
    (hγ : γ ∈ GfC (Wc D i)) : ∀ x y, trPair R i γ x y = ⟪x, Bop R i γ y⟫_ℂ := by
  have hex := hTL.2.2.1 γ hγ
  unfold Bop
  rw [dif_pos hex]
  exact hex.choose_spec.2

theorem rightTranslatePairingOperator_eq_of_forms {R : RealDat D A Ks} {i : Fin D.R.m} (hTL : TransLaws R i) {γ : GA D (Wc D i)}
    (hγ : γ ∈ GfC (Wc D i)) (B : (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H)
    (hB : ∀ x y, trPair R i γ x y = ⟪x, B y⟫_ℂ) : Bop R i γ = B := by
  apply ContinuousLinearMap.ext; intro y
  apply ext_inner_left ℂ; intro x
  rw [← rightTranslatePairingOperator_spec hTL hγ x y, hB]

theorem finite_mul_liftLevel_mem_finite {R : RealDat D A Ks} {i : Fin D.R.m} (hTL : TransLaws R i) {γ k : GA D (Wc D i)}
    (hγ : γ ∈ GfC (Wc D i)) (hk : k ∈ levW R i) (hγk : γ * k ∈ GfC (Wc D i)) : Bop R i (γ * k) = Bop R i γ := by
  apply rightTranslatePairingOperator_eq_of_forms hTL hγk
  intro x y
  have := hTL.2.2.2.1 γ hγ 1 (levW R i).one_mem k hk x y
  rw [one_mul] at this
  rw [this, rightTranslatePairingOperator_spec hTL hγ]

theorem rightTranslatePairingOperator_hecke_relation {R : RealDat D A Ks} {i : Fin D.R.m} (hTL : TransLaws R i) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {f : AE D} (hf : IsFinIdem D v f) {α : GA D (Wc D i)} (hα : SuppF (Wc D i) f α) (C : Finset (GA D (Wc D i)))
    (hCs : ∀ δ ∈ C, SuppF (Wc D i) f δ)
    (hC : IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C) {γ : GA D (Wc D i)}
    (hγ : γ ∈ GfC (Wc D i)) :
    Bop R i γ * ∑ δ ∈ C, Bop R i δ = ∑ δ ∈ C, Bop R i (γ * δ) := by
  have hCG : ∀ δ ∈ C, δ ∈ GfC (Wc D i) := fun δ hδ => (hC.1 δ hδ).1
  apply ContinuousLinearMap.ext; intro y
  obtain ⟨y', -, hy'⟩ := hTL.2.1 v f hf α hα C hCs hC y
  have e1 : y' = ∑ δ ∈ C, Bop R i δ y := by
    apply ext_inner_left ℂ; intro x
    rw [inner_sum, ← hTL.2.2.2.2.2 x y', hy' 1 (GfC (Wc D i)).one_mem x]
    refine Finset.sum_congr rfl fun δ hδ => ?_
    rw [one_mul, rightTranslatePairingOperator_spec hTL (hCG δ hδ)]
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, ← e1]
  apply ext_inner_left ℂ; intro x
  rw [inner_sum, ← rightTranslatePairingOperator_spec hTL hγ, hy' γ hγ x]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  rw [rightTranslatePairingOperator_spec hTL (mul_mem hγ (hCG δ hδ))]

def mkLX (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D (Wc D i))
    (hg : g ∈ locSet R i v) : LX R i v :=
  Quotient.mk _ ⟨g, hg⟩

theorem levelCosetRepresentative_mem_supportedSet {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) :
    rep x ∈ locSet R i v := (Quotient.out x).2

theorem placeSupportedLevelCoset_representative_eq {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) :
    mkLX R i v (rep x) (levelCosetRepresentative_mem_supportedSet x) = x := Quotient.out_eq x

theorem placeSupportedLevelCoset_eq_iff {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {g g' : GA D (Wc D i)} (hg : g ∈ locSet R i v) (hg' : g' ∈ locSet R i v) :
    mkLX R i v g hg = mkLX R i v g' hg' ↔ g⁻¹ * g' ∈ levW R i := by
  constructor
  · intro h
    have h2 := Quotient.exact h
    exact QuotientGroup.leftRel_apply.mp h2
  · intro h
    apply Quotient.sound
    exact QuotientGroup.leftRel_apply.mpr h

theorem representative_placeSupportedLevelCoset_rel {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {g : GA D (Wc D i)} (hg : g ∈ locSet R i v) : ∃ k ∈ levW R i, rep (mkLX R i v g hg) = g * k := by
  have h := placeSupportedLevelCoset_representative_eq (mkLX R i v g hg)
  rw [placeSupportedLevelCoset_eq_iff] at h
  refine ⟨g⁻¹ * rep (mkLX R i v g hg), ?_, by group⟩
  have := (levW R i).inv_mem h
  simpa using this

theorem levelCoset_eq_iff_representative_rel {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x y : LX R i v) :
    x = y ↔ (rep x)⁻¹ * rep y ∈ levW R i := by
  constructor
  · rintro rfl; rw [inv_mul_cancel]; exact (levW R i).one_mem
  · intro h
    have := (placeSupportedLevelCoset_eq_iff (levelCosetRepresentative_mem_supportedSet x) (levelCosetRepresentative_mem_supportedSet y)).mpr h
    rwa [placeSupportedLevelCoset_representative_eq, placeSupportedLevelCoset_representative_eq] at this

theorem eq_trivialLevelCoset_iff_representative_mem {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) :
    x = lx0 R i v ↔ rep x ∈ levW R i := by
  have e : lx0 R i v = mkLX R i v 1 (one_mem_locSet R i v) := rfl
  conv_lhs => rw [e, ← placeSupportedLevelCoset_representative_eq x]
  rw [placeSupportedLevelCoset_eq_iff, mul_one, inv_mem_iff]

theorem chosenFinitePlaceIdempotent_spec {v : HeightOneSpectrum (𝓞 D.host.F)} (h : ∃ f, IsFinIdem D v f) : IsFinIdem D v (fid D v) := by
  unfold fid; rw [dif_pos h]; exact h.choose_spec

theorem chosenFinitePlaceIdempotent_eq_zero_of_not_exists {v : HeightOneSpectrum (𝓞 D.host.F)} (h : ¬ ∃ f, IsFinIdem D v f) : fid D v = 0 := by
  unfold fid; rw [dif_neg h]

def dcSetoid (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) : Setoid (LX R i v) where
  r x y := ∃ k₁ ∈ {k | k ∈ levW R i ∧ SuppF (Wc D i) (fid D v) k}, ∃ k₂ ∈ {k | k ∈ levW R i ∧ SuppF (Wc D i) (fid D v) k},
    rep y = k₁ * rep x * k₂
  iseqv := by
    refine ⟨fun x => ⟨1, ⟨(levW R i).one_mem, (Model.trivAt_one _ _).2⟩, 1, ⟨(levW R i).one_mem, (Model.trivAt_one _ _).2⟩,
      by group⟩, ?_, ?_⟩
    · rintro x y ⟨k₁, ⟨h1l, h1s⟩, k₂, ⟨h2l, h2s⟩, h⟩
      refine ⟨k₁⁻¹, ⟨(levW R i).inv_mem h1l, supportedAtAdeleIdempotent_inv_closed _ _ h1s⟩, k₂⁻¹,
        ⟨(levW R i).inv_mem h2l, supportedAtAdeleIdempotent_inv_closed _ _ h2s⟩, ?_⟩
      rw [h]; group
    · rintro x y z ⟨k₁, ⟨h1l, h1s⟩, k₂, ⟨h2l, h2s⟩, h⟩ ⟨l₁, ⟨g1l, g1s⟩, l₂, ⟨g2l, g2s⟩, h'⟩
      refine ⟨l₁ * k₁, ⟨mul_mem g1l h1l, supportedAtAdeleIdempotent_mul_closed _ _ g1s h1s⟩, k₂ * l₂,
        ⟨mul_mem h2l g2l, supportedAtAdeleIdempotent_mul_closed _ _ h2s g2s⟩, ?_⟩
      rw [h', h]; group

def dcMap {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (C : Quotient (dcSetoid R i v) → Finset (GA D (Wc D i)))
    (hCs : ∀ b, ∀ δ ∈ C b, SuppF (Wc D i) (fid D v) δ)
    (hC : ∀ b, IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) (fid D v) k} (rep (Quotient.out b)) (C b))
    (p : Σ b, ↥(C b)) : LX R i v :=
  mkLX R i v p.2.1 ⟨((hC p.1).1 p.2.1 p.2.2).1, hCs p.1 p.2.1 p.2.2⟩

theorem placeSupportedDoubleCosetMap_bijective {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (C : Quotient (dcSetoid R i v) → Finset (GA D (Wc D i)))
    (hCs : ∀ b, ∀ δ ∈ C b, SuppF (Wc D i) (fid D v) δ)
    (hC : ∀ b, IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) (fid D v) k} (rep (Quotient.out b)) (C b)) :
    Function.Bijective (dcMap C hCs hC) := by
  constructor
  · rintro ⟨b, δ, hδ⟩ ⟨b', δ', hδ'⟩ h
    replace h : δ⁻¹ * δ' ∈ levW R i := (placeSupportedLevelCoset_eq_iff _ _).mp h
    have hs : SuppF (Wc D i) (fid D v) (δ⁻¹ * δ') := supportedAtAdeleIdempotent_mul_closed _ _ (supportedAtAdeleIdempotent_inv_closed _ _ (hCs b δ hδ)) (hCs b' δ' hδ')
    obtain ⟨-, k₁, ⟨h1l, h1s⟩, k₂, ⟨h2l, h2s⟩, e⟩ := (hC b).1 δ hδ
    obtain ⟨-, l₁, ⟨g1l, g1s⟩, l₂, ⟨g2l, g2s⟩, e'⟩ := (hC b').1 δ' hδ'
    have hbb : b = b' := by
      apply Quotient.out_equiv_out.mp
      refine ⟨l₁⁻¹ * k₁, ⟨mul_mem ((levW R i).inv_mem g1l) h1l, supportedAtAdeleIdempotent_mul_closed _ _ (supportedAtAdeleIdempotent_inv_closed _ _ g1s) h1s⟩,
        k₂ * (δ⁻¹ * δ') * l₂⁻¹, ⟨mul_mem (mul_mem h2l h) ((levW R i).inv_mem g2l),
          supportedAtAdeleIdempotent_mul_closed _ _ (supportedAtAdeleIdempotent_mul_closed _ _ h2s hs) (supportedAtAdeleIdempotent_inv_closed _ _ g2s)⟩, ?_⟩
      rw [e, e']; group
    subst hbb
    have hu := (hC b).2 δ' ⟨l₁, ⟨g1l, g1s⟩, l₂, ⟨g2l, g2s⟩, e'⟩
    have hdd : δ = δ' := hu.unique ⟨hδ, h, hs⟩ ⟨hδ', by rw [inv_mul_cancel]; exact (levW R i).one_mem,
      by rw [inv_mul_cancel]; exact (Model.trivAt_one _ _).2⟩
    subst hdd
    rfl
  · intro x
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := Quotient.mk_out (s := dcSetoid R i v) x
    obtain ⟨γ, ⟨hγC, hγK⟩, -⟩ := (hC (Quotient.mk _ x)).2 (rep x) ⟨k₁, hk₁, k₂, hk₂, e⟩
    refine ⟨⟨Quotient.mk _ x, γ, hγC⟩, ?_⟩
    unfold dcMap
    conv_rhs => rw [← placeSupportedLevelCoset_representative_eq x]
    exact (placeSupportedLevelCoset_eq_iff _ _).mpr hγK.1

theorem localCoefficient_summable_nontrivialCosets {R : RealDat D A Ks} {i : Fin D.R.m} {t : T} (hLS : LocSmall R i t)
    {μ : Measure (WO (Vc D i) (Wc D i))} {𝓕 : Set (WO (Vc D i) (Wc D i))}
    (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hf : IsFinIdem D v (fid D v)) : Summable (fun x : LX R i v => ‖acoef R i t μ 𝓕 v x‖) := by
  obtain ⟨s, -, -, hs⟩ := hLS μ 𝓕 hμ
  refine summable_of_sum_le (c := ‖acoef R i t μ 𝓕 v (lx0 R i v)‖ + s v) (fun _ => norm_nonneg _) ?_
  intro u
  rw [← Finset.sum_filter_add_sum_filter_not u (fun x => x = lx0 R i v)]
  gcongr
  · calc ∑ x ∈ u.filter (fun x => x = lx0 R i v), ‖acoef R i t μ 𝓕 v x‖
          ≤ ∑ x ∈ ({lx0 R i v} : Finset (LX R i v)), ‖acoef R i t μ 𝓕 v x‖ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx; rw [Finset.mem_filter] at hx; rw [Finset.mem_singleton]; exact hx.2
            · intros; exact norm_nonneg _
      _ = _ := Finset.sum_singleton _ _
  · have hinj : Set.InjOn (fun x : LX R i v => rep x) ↑(u.filter (fun x => ¬ x = lx0 R i v)) := by
      intro x _ y _ hxy
      rw [levelCoset_eq_iff_representative_rel]
      simp only at hxy
      rw [hxy, inv_mul_cancel]; exact (levW R i).one_mem
    have e := Finset.sum_image (f := fun g => ‖coef R i t μ 𝓕 g‖) hinj
    unfold acoef
    rw [← e]
    apply hs v (fid D v) hf
    · intro g hg
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
      rw [Finset.mem_filter] at hx
      exact ⟨(levelCosetRepresentative_mem_supportedSet x).2, fun h => hx.2 ((eq_trivialLevelCoset_iff_representative_mem x).mpr h)⟩
    · intro g hg g' hg' h
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hg'
      rw [(levelCoset_eq_iff_representative_rel x y).mpr h]

set_option maxHeartbeats 1000000 in
theorem localCoefficient_fiber_sum_eq {R : RealDat D A Ks} {i : Fin D.R.m} {t : T} (hTL : TransLaws R i) (hLF : LevFix R i t)
    {μ : Measure (WO (Vc D i) (Wc D i))} {𝓕 : Set (WO (Vc D i) (Wc D i))}
    (hleft : ∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hf : IsFinIdem D v (fid D v))
    (C : Quotient (dcSetoid R i v) → Finset (GA D (Wc D i)))
    (hCs : ∀ b, ∀ δ ∈ C b, SuppF (Wc D i) (fid D v) δ)
    (hC : ∀ b, IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) (fid D v) k} (rep (Quotient.out b)) (C b))
    {γ : GA D (Wc D i)} (hγ : γ ∈ GfC (Wc D i)) (b : Quotient (dcSetoid R i v)) :
    ∑ δ : ↥(C b), acoef R i t μ 𝓕 v (dcMap C hCs hC ⟨b, δ⟩) • Bop R i (γ * rep (dcMap C hCs hC ⟨b, δ⟩)) =
      ∑ δ : ↥(C b), Bop R i γ * (acoef R i t μ 𝓕 v (dcMap C hCs hC ⟨b, δ⟩) • Bop R i (rep (dcMap C hCs hC ⟨b, δ⟩))) := by
  have key : ∀ δ : ↥(C b), acoef R i t μ 𝓕 v (dcMap C hCs hC ⟨b, δ⟩) = coef R i t μ 𝓕 (rep (Quotient.out b)) ∧
      Bop R i (γ * rep (dcMap C hCs hC ⟨b, δ⟩)) = Bop R i (γ * δ.1) ∧
      Bop R i (rep (dcMap C hCs hC ⟨b, δ⟩)) = Bop R i δ.1 := by
    intro δ
    obtain ⟨k, hk, hrep⟩ : ∃ k ∈ levW R i, rep (dcMap C hCs hC ⟨b, δ⟩) = δ.1 * k := representative_placeSupportedLevelCoset_rel _
    have hδG : δ.1 ∈ GfC (Wc D i) := ((hC b).1 δ.1 δ.2).1
    obtain ⟨k₁, ⟨h1l, -⟩, k₂, ⟨h2l, -⟩, e⟩ := ((hC b).1 δ.1 δ.2).2
    have hrG : rep (dcMap C hCs hC ⟨b, δ⟩) ∈ GfC (Wc D i) := (levelCosetRepresentative_mem_supportedSet _).1
    refine ⟨?_, ?_, ?_⟩
    · unfold acoef
      rw [hrep, Model.coef_mul_lev R i t hLF μ 𝓕 _ _ hk, e, Model.coef_mul_lev R i t hLF μ 𝓕 _ _ h2l]
      exact hleft k₁ h1l _
    · rw [hrep, ← mul_assoc]
      refine finite_mul_liftLevel_mem_finite hTL (mul_mem hγ hδG) hk ?_
      rw [mul_assoc, ← hrep]; exact mul_mem hγ hrG
    · rw [hrep]
      exact finite_mul_liftLevel_mem_finite hTL hδG hk (hrep ▸ hrG)
  have hlast : ∀ δ : ↥(C b), Bop R i γ * (coef R i t μ 𝓕 (rep (Quotient.out b)) • Bop R i δ.1) =
      Bop R i γ * (acoef R i t μ 𝓕 v (dcMap C hCs hC ⟨b, δ⟩) • Bop R i (rep (dcMap C hCs hC ⟨b, δ⟩))) := by
    intro δ
    obtain ⟨h1, -, h2⟩ := key δ
    exact congrArg (Bop R i γ * ·) (congrArg₂ (· • ·) h1.symm h2.symm)
  calc ∑ δ : ↥(C b), acoef R i t μ 𝓕 v (dcMap C hCs hC ⟨b, δ⟩) • Bop R i (γ * rep (dcMap C hCs hC ⟨b, δ⟩))
        = ∑ δ : ↥(C b), coef R i t μ 𝓕 (rep (Quotient.out b)) • Bop R i (γ * δ.1) :=
          Finset.sum_congr rfl (fun δ _ => by rw [(key δ).1, (key δ).2.1])
    _ = coef R i t μ 𝓕 (rep (Quotient.out b)) • ∑ δ ∈ C b, Bop R i (γ * δ) := by
          rw [← Finset.smul_sum, Finset.sum_coe_sort (C b) (fun δ => Bop R i (γ * δ))]
    _ = coef R i t μ 𝓕 (rep (Quotient.out b)) • (Bop R i γ * ∑ δ ∈ C b, Bop R i δ) := by
          rw [rightTranslatePairingOperator_hecke_relation (R := R) hTL hf (α := rep (Quotient.out b)) (levelCosetRepresentative_mem_supportedSet (Quotient.out b)).2 (C b) (hCs b) (hC b) hγ]
    _ = ∑ δ ∈ C b, Bop R i γ * (coef R i t μ 𝓕 (rep (Quotient.out b)) • Bop R i δ) := by
          rw [Finset.mul_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl (fun δ _ => ?_)
          apply ContinuousLinearMap.ext; intro y
          show coef R i t μ 𝓕 (rep (Quotient.out b)) • Bop R i γ (Bop R i δ y) =
            Bop R i γ ((coef R i t μ 𝓕 (rep (Quotient.out b)) • Bop R i δ) y)
          rw [ContinuousLinearMap.smul_apply, map_smul]
    _ = ∑ δ : ↥(C b), Bop R i γ * (coef R i t μ 𝓕 (rep (Quotient.out b)) • Bop R i δ.1) :=
          (Finset.sum_coe_sort (C b) (fun δ => Bop R i γ * (coef R i t μ 𝓕 (rep (Quotient.out b)) • Bop R i δ))).symm
    _ = ∑ δ : ↥(C b), Bop R i γ * (acoef R i t μ 𝓕 v (dcMap C hCs hC ⟨b, δ⟩) • Bop R i (rep (dcMap C hCs hC ⟨b, δ⟩))) := by
          exact Finset.sum_congr rfl (fun δ _ => hlast δ)

end Local

set_option maxHeartbeats 1000000 in

theorem bop_mul_zop_hasSum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i t, LocSmall R i t → TransLaws R i → LevFix R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g) → ∀ v, ∀ γ ∈ GfC (Wc D i), HasSum (fun x : Eu.LX R i v => Eu.acoef R i t μ 𝓕 v x • Eu.Bop R i (γ * Eu.rep x)) (Eu.Bop R i γ * Eu.Zop R i t μ 𝓕 v) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t hLS hTL hLF μ 𝓕 hμ hleft v γ hγ
  by_cases hex : ∃ f, IsFinIdem D v f
  · have hf : IsFinIdem D v (fid D v) := chosenFinitePlaceIdempotent_spec hex
    have hsa := localCoefficient_summable_nontrivialCosets hLS hμ hf (R := R)
    have hs1 : Summable (fun x : LX R i v => acoef R i t μ 𝓕 v x • Bop R i (rep x)) := by
      refine Summable.of_norm_bounded hsa (fun x => ?_)
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) (bop_norm R i _)
    have hs2 : Summable (fun x : LX R i v => acoef R i t μ 𝓕 v x • Bop R i (γ * rep x)) := by
      refine Summable.of_norm_bounded hsa (fun x => ?_)
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) (bop_norm R i _)
    have h1 : HasSum (fun x : LX R i v => Bop R i γ * (acoef R i t μ 𝓕 v x • Bop R i (rep x)))
        (Bop R i γ * Zop R i t μ 𝓕 v) := hs1.hasSum.mul_left (Bop R i γ)
    choose C hCs hC using fun b : Quotient (dcSetoid R i v) =>
      hTL.1 v (fid D v) hf (rep (Quotient.out b)) (levelCosetRepresentative_mem_supportedSet (Quotient.out b)).2
    let e := Equiv.ofBijective (dcMap C hCs hC) (placeSupportedDoubleCosetMap_bijective C hCs hC)
    have g1 := (e.hasSum_iff).mpr h1
    have g2 := ((e.summable_iff).mpr hs2).hasSum
    have k1 := g1.sigma (fun b => hasSum_fintype _)
    have k2 := g2.sigma (fun b => hasSum_fintype _)
    have hfib := localCoefficient_fiber_sum_eq (R := R) hTL hLF hleft hf C hCs hC hγ
    have hfun : (fun b => ∑ c : ↥(C b),
          ((fun x : LX R i v => acoef R i t μ 𝓕 v x • Bop R i (γ * rep x)) ∘ e) ⟨b, c⟩) =
        (fun b => ∑ c : ↥(C b),
          ((fun x : LX R i v => Bop R i γ * (acoef R i t μ 𝓕 v x • Bop R i (rep x))) ∘ e) ⟨b, c⟩) :=
      funext fun b => hfib b
    rw [hfun] at k2
    have hk := k2.unique k1
    rw [← hk]
    exact (e.hasSum_iff).mp g2
  · have h0 := chosenFinitePlaceIdempotent_eq_zero_of_not_exists hex
    have hall : ∀ x : LX R i v, rep x = 1 := fun x => supportedAtIdempotent_zero_eq_one _ (h0 ▸ (levelCosetRepresentative_mem_supportedSet x).2)
    haveI : Subsingleton (LX R i v) := ⟨fun x y => (levelCoset_eq_iff_representative_rel x y).mpr (by
      rw [hall x, hall y, inv_one, one_mul]; exact (levW R i).one_mem)⟩
    have hs1 : Summable (fun x : LX R i v => acoef R i t μ 𝓕 v x • Bop R i (rep x)) := Summable.of_finite
    have hF : (fun x : LX R i v => acoef R i t μ 𝓕 v x • Bop R i (γ * rep x)) =
        fun x => Bop R i γ * (acoef R i t μ 𝓕 v x • Bop R i (rep x)) := by
      funext x
      rw [hall x, mul_one, bop_one hTL]
      apply ContinuousLinearMap.ext; intro y
      show (acoef R i t μ 𝓕 v x • Bop R i γ) y = Bop R i γ ((acoef R i t μ 𝓕 v x • (1 : (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H)) y)
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul]
      rfl
    rw [hF]
    exact hs1.hasSum.mul_left (Bop R i γ)

end GlobalTheory.RawLift.Eu

end

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecMInvariantEqBotOrUnivAtGeometricPoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqClosedPointOfNotMemRange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FrameBasis

open GlobalTheory.SecAff GlobalTheory.LN GlobalTheory.ThetaAct GlobalTheory.GeomPointSections

section Algebra

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

def IsBas (R : Type) [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {κ : Type} (v : κ → M) : Prop :=
  LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤

theorem isBas_iff_existsUnique {n : ℕ} (v : Fin n → M) :
    IsBas R v ↔ ∀ s, ∃! c : Fin n → R, s = ∑ i, c i • v i := by
  constructor
  · rintro ⟨h₁, h₂⟩ s
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (h₂.ge (Submodule.mem_top (x := s)))
    refine ⟨c, hc.symm, fun d hd => funext fun i => ?_⟩
    exact Fintype.linearIndependent_iffₛ.1 h₁ d c (hd.symm.trans hc.symm) i
  · intro h
    refine ⟨Fintype.linearIndependent_iffₛ.2 fun c d e i => ?_, eq_top_iff.2 fun s _ => ?_⟩
    · exact congrFun ((h (∑ i, d i • v i)).unique e.symm rfl) i
    · obtain ⟨c, hc, -⟩ := h s
      exact (Submodule.mem_span_range_iff_exists_fun R).2 ⟨c, hc.symm⟩

theorem IsBas.card_eq [Nontrivial R] {m n : ℕ} {e : Fin m → M} {b : Fin n → M} (he : IsBas R e) (hb : IsBas R b) :
    m = n := by
  simpa using Fintype.card_congr ((Module.Basis.mk he.1 he.2.ge).indexEquiv (Module.Basis.mk hb.1 hb.2.ge))

theorem IsBas.iff_det {n : ℕ} {e b : Fin n → M} (he : IsBas R e) (P : Matrix (Fin n) (Fin n) R)
    (hb : ∀ k, b k = ∑ j, P k j • e j) : IsBas R b ↔ IsUnit P.det := by
  let E := Module.Basis.mk he.1 he.2.ge
  have hE : ∀ j, e j = E j := fun j => (Module.Basis.mk_apply _ _ _).symm
  have : E.toMatrix b = P.transpose := by
    ext i j
    rw [Module.Basis.toMatrix_apply, hb]
    simp [hE, Finsupp.single_apply]
  rw [IsBas, E.is_basis_iff_det, Module.Basis.det_apply, this, Matrix.det_transpose]

theorem exists_trait_ring (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [CharZero A] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : A →+* W), CDvr W ∧ IsLocalHom φ := by
  by_cases h : IsField A
  · letI := h.toField
    refine ⟨PowerSeries A, inferInstance, inferInstance, inferInstance, PowerSeries.C, ⟨inferInstance, ?_, ?_⟩,
      inferInstance⟩
    · rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
    · exact charZero_of_injective_ringHom (f := PowerSeries.C (R := A)) (RingHom.injective _)
  · obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := exists_complete_discreteValuationRing_dominating A h
    exact ⟨O, inferInstance, inferInstance, inferInstance, φ,
      ⟨inferInstance, inferInstance, charZero_of_injective_ringHom h1⟩, h2⟩

end Algebra

theorem exists_trait {Z : Scheme.{0}} [IsLocallyNoetherian Z] (z : Z ⟶ Sp ℤ) [Flat z] (hZ : Geo.Tor.IsNormalScheme Z) (p : Z) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (χ : Sp W ⟶ Z),
      CDvr W ∧ χ (IsLocalRing.closedPoint W) = p := by
  have := (hZ p).1
  have := GlobalTheory.GenericExt.flat_fromSpecStalk Z p
  have : CharZero (Z.presheaf.stalk p) := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.fromSpecStalk p ≫ z)
    have hf : Flat (Spec.map φ) := by rw [hφ]; infer_instance
    have hf' : φ.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 hf
    have hf'' : Module.Flat ℤ (Z.presheaf.stalk p) := by
      rw [← RingHom.flat_algebraMap_iff]
      convert hf' using 1
      exact Subsingleton.elim _ _
    exact charZero_of_injective_algebraMap (R := ℤ) (FaithfulSMul.algebraMap_injective ℤ _)
  obtain ⟨W, _, _, _, φ, hW, _⟩ := exists_trait_ring (Z.presheaf.stalk p)
  refine ⟨W, inferInstance, inferInstance, inferInstance, spMap φ ≫ Z.fromSpecStalk p, hW, ?_⟩
  exact (Scheme.Hom.comp_apply _ _ _).trans
    (Eq.trans (congrArg (Z.fromSpecStalk p) (IsLocalRing.comap_closedPoint φ)) (Scheme.fromSpecStalk_closedPoint (x := p)))

section Sections

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {a : ℤ} {T T' : Over S}

theorem gs_pull_apply (h : T' ⟶ T) (v : SecM A L a T) {Z : Scheme.{0}} (r : Z ⟶ (T' ⊗ A).left) (z : Z)
    (j : Fin 1 → L.ι) (hz : r z ∈ LB.wchart L (fun _ : Fin 1 => (snd T' A).left) j) :
    gs r z (LB.wchart L (fun _ : Fin 1 => (snd T' A).left) j) ((pull A L a h v).1 j) =
      gs (r ≫ (h ▷ A).left) z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j) (v.1 j) :=
  gs_appLE (h ▷ A).left _ _ (chart_le A L a h j) r z hz _

theorem sv_pull (h : T' ⟶ T) (v : SecM A L a T) {Z : Scheme.{0}} (r : Z ⟶ (T' ⊗ A).left) (z : Z) {J}
    (hJ : Good L z J) : sv (pull A L a h v) r z J = sv v (r ≫ (h ▷ A).left) z J := by
  rw [sv, sv, sval_of (SecM.toSec A v) (r ≫ (h ▷ A).left) z J (fun _ => J (r ≫ (snd T' A).left))
    (fun _ => by rw [Category.assoc, whisker_snd_left])]
  exact gs_pull_apply h v r z _ (hJ.mem (fun _ : Fin 1 => (snd T' A).left) r)

theorem sv_sum {κ : Type} (I : Finset κ) (v : κ → SecM A L a T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}
    (hJ : Good L z J) : sv (∑ i ∈ I, v i) r z J = ∑ i ∈ I, sv (v i) r z J :=
  map_sum (AddMonoidHom.mk' (fun w : SecM A L a T => sv w r z J) fun x y => sv_add x y r z hJ) v I

theorem lin_iff (hL : L.IsLB) (N : ℕ) (h : T' ⟶ T) {n : ℕ} (b : Fin n → LB.Sec (LPow A L (N : ℤ) T))
    (c : Fin n → Γ(T'.left, ⊤)) (s : LB.Sec (LPow A L (N : ℤ) T')) :
    Lin A L N h b c s ↔ SecM.ofSec A s = ∑ i, c i • pull A L N h (SecM.ofSec A (b i)) := by
  have key : ∀ z J, Good L z J → sv (∑ i, c i • pull A L N h (SecM.ofSec A (b i))) (𝟙 _) z J =
      ∑ i, gs (fst T' A).left z ⊤ (c i) * sv (SecM.ofSec A (b i)) (h ▷ A).left z J := fun z J hJ => by
    rw [sv_sum _ _ _ _ hJ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sv_smul _ _ _ _ hJ, sv_pull _ _ _ _ hJ, Category.id_comp, Category.id_comp]
  exact ⟨fun H => sv_ext hL fun z J hJ => (H z J hJ).trans (key z J hJ).symm,
    fun H z J hJ => (congrArg (fun w => sv w (𝟙 _) z J) H).trans (key z J hJ)⟩

theorem basisAlong_iff (hL : L.IsLB) (N : ℕ) (h : T' ⟶ T) {n : ℕ} (b : Fin n → LB.Sec (LPow A L (N : ℤ) T)) :
    BasisAlong A L N h b ↔ IsBas Γ(T'.left, ⊤) fun i => pull A L N h (SecM.ofSec A (b i)) := by
  rw [isBas_iff_existsUnique, BasisAlong]
  simp only [lin_iff hL]
  exact ⟨fun H s => H (SecM.toSec A s), fun H s => H _⟩

def StableBas {κ : Type} (e : κ → SecM A L a T) : Prop :=
  ∀ (T' : Over S) [IsAffine T'.left] (h : T' ⟶ T), IsBas Γ(T'.left, ⊤) fun i => pull A L a h (e i)

theorem isBas_of_local [IsProper A.hom] [IsAffine T.left] (hL : L.IsLB) {n : ℕ} (b : Fin n → SecM A L a T)
    (H : ∀ x : T.left, ∃ r : Γ(T.left, ⊤), x ∈ T.left.basicOpen r ∧
      IsBas Γ((overRes (T.left.basicOpen r)).left, ⊤) fun i => pull A L a (overResι (T.left.basicOpen r)) (b i)) :
    IsBas Γ(T.left, ⊤) b := by
  choose r hr hb using H
  have hspan : Ideal.span (Set.range r) = ⊤ := by
    rw [← (isAffineOpen_top T.left).iSup_basicOpen_eq_self_iff]
    exact eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨r x, ⟨_, rfl⟩⟩, hr x⟩
  refine ⟨Fintype.linearIndependent_iff.2 fun c hc i => ?_, eq_top_iff.2 fun σ _ => ?_⟩
  · refine (Submodule.mem_bot Γ(T.left, ⊤)).1 (Submodule.mem_of_span_eq_top_of_smul_pow_mem ⊥ _ hspan (c i) ?_)
    rintro ⟨_, x, rfl⟩
    have e := congrArg (pull A L a (overResι (T.left.basicOpen (r x)))) hc
    rw [map_sum, map_zero] at e
    simp only [map_smulₛₗ] at e
    obtain ⟨N, hN⟩ := fun_kill (overResι (T.left.basicOpen (r x))).left (r x) (overResι_range _)
      (W := ⊤) isCompact_univ (W' := ⊤) (le_pre_top _) le_top (c i) (Fintype.linearIndependent_iff.1 (hb x).1 _ e i)
    rw [rs_self] at hN
    exact ⟨N, hN⟩
  · refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hspan σ ?_
    rintro ⟨_, x, rfl⟩
    refine pow_smul_mem A L a hL (overResι (T.left.basicOpen (r x))) (r x) (overResι_range _) _ σ ?_
    refine ((hb x).2.ge.trans (Submodule.span_mono ?_)) trivial
    rintro _ ⟨i, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨i, rfl⟩, rfl⟩

theorem stableBas_of_traits [IsProper A.hom] (hL : L.IsLB) {n : ℕ} (b : Fin n → SecM A L a T)
    (loc : ∀ p : S, ∃ (T₀ : Over S) (m : ℕ) (e : Fin m → SecM A L a T₀), IsOpenImmersion T₀.hom ∧
      p ∈ Set.range T₀.hom ∧ StableBas e)
    (tr : ∀ p : T.left, ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (χ : Sp W ⟶ T.left),
      χ (IsLocalRing.closedPoint W) = p ∧ IsBas Γ(Sp W, ⊤)
        fun i => pull A L a (Over.homMk χ rfl : Over.mk (χ ≫ T.hom) ⟶ T) (b i)) : StableBas b := by
  intro T' _ h
  refine isBas_of_local hL _ fun x => ?_
  obtain ⟨T₀, m, e, _, hp, he⟩ := loc (T.hom (h.left x))
  obtain ⟨V, hV, hxV, hVO⟩ := exists_isAffineOpen_mem_and_subset (X := T.left) (x := h.left x)
    (U := T.hom ⁻¹ᵁ T₀.hom.opensRange) hp
  have : IsAffine (overRes V).left := hV
  have hrange : Set.range (V.ι ≫ T.hom) ⊆ Set.range T₀.hom := by
    rintro _ ⟨y, rfl⟩
    exact hVO y.2
  let k : overRes V ⟶ T₀ := Over.homMk (IsOpenImmersion.lift T₀.hom (V.ι ≫ T.hom) hrange)
    (IsOpenImmersion.lift_fac _ _ _)
  choose P hP using fun i => (((isBas_iff_existsUnique _).1 (he _ k)) (pull A L a (overResι V) (b i))).exists
  have hP' : ∀ {T'' : Over S} (u : T'' ⟶ overRes V) i, pull A L a (u ≫ overResι V) (b i) =
      ∑ j, pa u.left (V := ⊤) (le_pre_top _) (P i j) • pull A L a (u ≫ k) (e j) := fun u i => by
    rw [← pull_pull, hP, map_sum]
    simp only [map_smulₛₗ, pull_pull]
  obtain ⟨W, _, _, χ, hχ, hW⟩ := tr (h.left x)
  obtain ⟨u₀, hu₀⟩ := exists_lift (Over.homMk χ rfl : Over.mk (χ ≫ T.hom) ⟶ T) V (fun y =>
    (congrArg (fun U => y ∈ U) (Scheme.preimage_eq_top_of_closedPoint_mem χ (U := V) (hχ ▸ hxV))).mpr trivial)
  have : IsAffine (Over.mk (χ ≫ T.hom)).left := inferInstanceAs (IsAffine (Sp W))
  have hW' : IsBas Γ((Over.mk (χ ≫ T.hom)).left, ⊤) fun i => pull A L a (u₀ ≫ overResι V) (b i) := by
    rw [hu₀]; exact hW
  have : Nontrivial Γ((Over.mk (χ ≫ T.hom)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain rfl : m = n := (he _ (u₀ ≫ k)).card_eq hW'
  have hdet : ∀ {T'' : Over S} [IsAffine T''.left] (u : T'' ⟶ overRes V),
      IsBas Γ(T''.left, ⊤) (fun i => pull A L a (u ≫ overResι V) (b i)) ↔
        IsUnit (pa u.left (V := ⊤) (le_pre_top _) (Matrix.det (Matrix.of P))) := fun u => by
    rw [RingHom.map_det]
    exact (he _ (u ≫ k)).iff_det _ (hP' u)
  let d : Γ((overRes V).left, ⊤) := Matrix.det (Matrix.of P)
  have hd : u₀.left (IsLocalRing.closedPoint W) ∈ (overRes V).left.basicOpen d := by
    have e₁ := Scheme.basicOpen_appLE u₀.left ⊤ ⊤ (le_pre_top _) d
    have e₂ := (Over.mk (χ ≫ T.hom)).left.basicOpen_of_isUnit ((hdet u₀).1 hW')
    exact ((e₁.symm.trans e₂).ge trivial).2
  have hx : x ∈ h.left ⁻¹ᵁ ((overResι V).left ''ᵁ (overRes V).left.basicOpen d) :=
    ⟨_, hd, (congrArg (fun q => q.left (IsLocalRing.closedPoint W)) hu₀).trans hχ⟩
  obtain ⟨r, hr, hxr⟩ := (isAffineOpen_top T'.left).exists_basicOpen_le ⟨x, hx⟩ trivial
  refine ⟨r, hxr, ?_⟩
  have : IsAffine (overRes (T'.left.basicOpen r)).left := (isAffineOpen_top T'.left).basicOpen r
  obtain ⟨u, hu⟩ := exists_lift (overResι (T'.left.basicOpen r) ≫ h) V (fun y => by
    obtain ⟨q, -, hq⟩ := hr y.2
    exact (congrArg (· ∈ V) hq).mp q.2)
  simp only [pull_pull]
  rw [← hu]
  refine (hdet u).2 (isUnit_pa u d fun y => ?_)
  obtain ⟨q, hq, hq'⟩ := hr y.2
  have : q = u.left y := (overResι V).left.isOpenEmbedding.injective
    (hq'.trans (congrArg (fun q => q.left y) hu).symm)
  exact this ▸ hq

end Sections

section Transport

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} {g : A'.left ⟶ A.left}

theorem exists_total (hg : IsPullback g A'.hom A.hom f) (T : Over S) (T' : Over S') (i : T'.left ⟶ T.left) [IsIso i]
    (hi : T'.hom ≫ f = i ≫ T.hom) : ∃ h : (T' ⊗ A').left ⟶ (T ⊗ A).left, IsIso h ∧
      h ≫ (fst T A).left = (fst T' A').left ≫ i ∧ h ≫ (snd T A).left = (snd T' A').left ≫ g := by
  have h₁ : IsPullback (snd T A).left (fst T A).left A.hom T.hom := (IsPullback.of_hasPullback T.hom A.hom).flip
  have h₂ : IsPullback (snd T' A').left (fst T' A').left A'.hom T'.hom :=
    (IsPullback.of_hasPullback T'.hom A'.hom).flip
  have h₃ : IsPullback ((snd T' A').left ≫ g) ((fst T' A').left ≫ i) A.hom T.hom :=
    (h₂.paste_horiz hg).of_iso (Iso.refl _) (Iso.refl _) (asIso i) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp [hi])
  exact ⟨(h₃.isoIsPullback _ _ h₁).hom, inferInstance, h₃.isoIsPullback_hom_snd _ _ h₁,
    h₃.isoIsPullback_hom_fst _ _ h₁⟩

variable [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {w : LB.Iso L' (L.pull g)} {a : ℤ}

theorem exists_stableBas_of_pullback (hg : IsPullback g A'.hom A.hom f) (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {T₀ : Over S'} {κ : Type} (e : κ → SecM A' L' a T₀) (he : StableBas e) :
    ∃ e' : κ → SecM A L a (Over.mk (T₀.hom ≫ f)), StableBas e' := by
  obtain ⟨h₀, _, f₀, s₀⟩ := exists_total hg (Over.mk (T₀.hom ≫ f)) T₀ (𝟙 _) (Category.id_comp _).symm
  rw [Category.comp_id] at f₀
  obtain ⟨E₀, -, R₀⟩ := exists_secEquiv hw hL hL' (IsIso.inv_hom_id h₀) (IsIso.hom_inv_id h₀) s₀.symm (fun c => c)
    (fun c => congrArg (fun q => q.appTop.hom c) f₀) a
  refine ⟨fun i => E₀ (e i), fun T _ u => ?_⟩
  let T' : Over S' := Over.mk (Y := T.left) (u.left ≫ T₀.hom)
  let u' : T' ⟶ T₀ := Over.homMk u.left rfl
  obtain ⟨h, _, f₁, s₁⟩ := exists_total hg T T' (𝟙 _)
    ((Category.assoc _ _ _).trans ((Over.w u).trans (Category.id_comp _).symm))
  rw [Category.comp_id] at f₁
  obtain ⟨E, hE, R⟩ := exists_secEquiv hw hL hL' (IsIso.inv_hom_id h) (IsIso.hom_inv_id h) s₁.symm (fun c => c)
    (fun c => congrArg (fun q => q.appTop.hom c) f₁) a
  have nat : h ≫ (u ▷ A).left = (u' ▷ A').left ≫ h₀ := by
    apply pullback.hom_ext
    · change (h ≫ (u ▷ A).left) ≫ (fst _ A).left = ((u' ▷ A').left ≫ h₀) ≫ (fst (Over.mk (T₀.hom ≫ f)) A).left
      rw [Category.assoc, whisker_fst_left, ← Category.assoc, f₁, Category.assoc, f₀, whisker_fst_left]
      rfl
    · change (h ≫ (u ▷ A).left) ≫ (snd _ A).left = ((u' ▷ A').left ≫ h₀) ≫ (snd (Over.mk (T₀.hom ≫ f)) A).left
      rw [Category.assoc, whisker_snd_left, s₁, Category.assoc, s₀, ← Category.assoc, whisker_snd_left]
  have comm : ∀ x, E (pull A' L' a u' x) = pull A L a u (E₀ x) := fun x => by
    refine Subtype.ext ((R _).unique_left hL' (IsIso.inv_hom_id h) fun Z r z p q hp hq => ?_)
    rw [gs_pull_apply u _ (r ≫ h) z p hp, gs_pull_apply u' _ r z q hq, Category.assoc, nat, ← Category.assoc,
      R₀ x Z (r ≫ (u' ▷ A').left) z p q ?_ (chart_le A' L' a u' q hq), ← pw_comp]
    · simp only [whisker_snd_left]
    · exact (congrArg (fun φ => φ (r z) ∈ LB.wchart L (fun _ : Fin 1 => (snd (Over.mk (T₀.hom ≫ f)) A).left) p)
        nat).mp (chart_le A L a u p hp)
  have : IsAffine T'.left := ‹IsAffine T.left›
  let E' : SecM A' L' a T' ≃ₗ[Γ(T.left, ⊤)] SecM A L a T := { E with map_smul' := hE }
  obtain ⟨b₁, b₂⟩ := he T' u'
  have e₁ : (fun i => pull A L a u (E₀ (e i))) = E'.toLinearMap ∘ fun i => pull A' L' a u' (e i) :=
    funext fun i => (comm _).symm
  rw [e₁]
  refine ⟨b₁.map' _ E'.ker, ?_⟩
  rw [Set.range_comp, ← Submodule.map_span]
  exact (congrArg (Submodule.map E'.toLinearMap) b₂).trans ((Submodule.map_top _).trans E'.range)

end Transport

theorem exists_stableBas_polAV (H : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) (n : ℕ) (hn : 1 ≤ n) (p : S) :
    ∃ V : S.Opens, p ∈ V ∧ ∃ e : Fin (n ^ P.g) → SecM P.A P.L n (overRes (T := baseOver S) V), StableBas e := by
  obtain ⟨V, hp, b, hb⟩ := H S P n hn p
  refine ⟨V, hp, fun i => SecM.ofSec P.A (b i), fun T' _ g => ?_⟩
  let t : Spec (CommRingCat.of Γ(T'.left, ⊤)) ⟶ (overRes (T := baseOver S) V).left := T'.left.isoSpec.inv ≫ g.left
  let e : baseAt t ⟶ T' := Over.homMk T'.left.isoSpec.inv (by
    change T'.left.isoSpec.inv ≫ T'.hom = (T'.left.isoSpec.inv ≫ g.left) ≫ _
    rw [Category.assoc, Over.w g])
  let e' : T' ⟶ baseAt t := Over.homMk T'.left.isoSpec.hom (by
    change T'.left.isoSpec.hom ≫ (T'.left.isoSpec.inv ≫ g.left) ≫ _ = T'.hom
    rw [Category.assoc, Over.w g, Iso.hom_inv_id_assoc])
  have h₁ : e' ≫ e = 𝟙 T' := Over.OverMorphism.ext T'.left.isoSpec.hom_inv_id
  have h₂ : e ≫ g = homAt t := Over.OverMorphism.ext rfl
  have h₃ : e' ≫ homAt t = g := by rw [← h₂, ← Category.assoc, h₁, Category.id_comp]
  have hb' := hb _ t (fun i => SecM.toSec P.A (pull P.A P.L n (homAt t) (SecM.ofSec P.A (b i))))
    (fun i => (isPullSec_iff P.A P.L n _ _ _).2 rfl)
  refine ⟨Fintype.linearIndependent_iff.2 fun c hc i => ?_,
    h₃ ▸ span_of_retract P.A P.L n e e' h₁ (homAt t) _ hb'.2⟩
  have q := congrArg (pull P.A P.L n e) hc
  rw [map_sum, map_zero] at q
  simp only [map_smulₛₗ, pull_pull, h₂] at q
  have q' := congrArg (pa e'.left (V := ⊤) (le_pre_top _)) (Fintype.linearIndependent_iff.1 hb'.1 _ q i)
  rw [map_zero, pa_pa _ _ _ _ (𝟙 _) (congrArg (fun u => u.left) h₁) (le_pre_top _), pa_id] at q'
  exact (rs_self _ _).symm.trans q'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_stableBas_local (hS : SecBaseChangeAnySt) {Z : Scheme.{0}} [IsLocallyNoetherian Z] (t : SAB H Z)
    (hp : IsProper t.G.hom) (hA : RelAmple t.G t.PP.L) (hK : KTriv t.G t.PP.L) (n : ℕ) (hn : 1 ≤ n) (p : Z) :
    ∃ (T₀ : Over Z) (m : ℕ) (e : Fin m → SecM t.G t.PP.L n T₀), IsOpenImmersion T₀.hom ∧
      p ∈ Set.range T₀.hom ∧ StableBas e := by
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤) (x := p) trivial
  have : IsAffine U := hU
  have : IsNoetherian U := {}
  let C : U.toScheme.Opens := ⟨connectedComponent (⟨p, hc⟩ : U), isOpen_connectedComponent_of_noetherianSpace _⟩
  have : ConnectedSpace C.toScheme := isConnected_iff_connectedSpace.1 isConnected_connectedComponent
  let q : C.toScheme := ⟨⟨p, hc⟩, mem_connectedComponent⟩
  obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H C.toScheme, Nonempty (SABMap t' t (C.ι ≫ U.ι)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (C.ι ≫ U.ι) t
    exact ⟨_, ⟨m⟩⟩
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  obtain ⟨w, g, -⟩ := m.lin
  have am := relAmple_pull m.cart.1 t.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) U hU (fun y => (C.ι y).2) hA
  have kt := kTriv_pull m.cart t.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) hK
  have : ConnectedSpace t'.G.left := GeometricallyConnected.connectedSpace t'.G.hom t'.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t'.G.hom (eSec t'.G q)
  obtain ⟨-, ws, gs', -⟩ := t'.sym
  let P : PolAV C.toScheme :=
    { A := t'.G, g := d, smoothDim := hd, L := t'.PP.L, isLB := t'.PP.isLB, ample := am, ktriv := kt
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp, ‹_›⟩
      rigid := ⟨t'.PP.rig, t'.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  obtain ⟨V, hV, e, he⟩ := exists_stableBas_polAV hS P n hn q
  obtain ⟨e', he'⟩ := exists_stableBas_of_pullback m.cart.1 ((isGen_iff w).1 g) t.PP.isLB t'.PP.isLB e he
  exact ⟨_, _, e', inferInstanceAs (IsOpenImmersion ((V.ι ≫ 𝟙 _) ≫ C.ι ≫ U.ι)), ⟨⟨q, hV⟩, rfl⟩, he'⟩

theorem basisAlong_of_ampFrames : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) [IsLocallyNoetherian Z] (z : Z ⟶ Sp ℤ) (t : SAB H Z) (N : ℕ) (A : GlobalTheory.LN.AmpFrames t.G t.PP.L N), 0 < N → Geo.Tor.IsNormalScheme Z → Flat z → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (i : A.A.ι) (R : Type) [CommRing R] (χ : Sp R ⟶ (A.A.U i).toScheme), GlobalTheory.LN.BasisAlong t.G t.PP.L 1 (Over.homMk χ rfl : Over.mk (χ ≫ (A.A.U i).ι) ⟶ Over.mk (A.A.U i).ι) (fun _ : Fin 1 => A.th i) ∧ GlobalTheory.LN.BasisAlong t.G t.PP.L N (Over.homMk χ rfl : Over.mk (χ ≫ (A.A.U i).ι) ⟶ Over.mk (A.A.U i).ι) (A.b i) := by
  intro _ h₂ E _ _ _ H Z _ z t N A hN hZ _ hp hA hK i R _ χ
  have hL := t.PP.isLB
  have tr : ∀ p : (A.A.U i).toScheme, ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (ψ : Sp W ⟶ (A.A.U i).toScheme),
      ψ (IsLocalRing.closedPoint W) = p ∧
      BasisAlong t.G t.PP.L 1 (Over.homMk ψ rfl : Over.mk (ψ ≫ (A.A.U i).ι) ⟶ Over.mk (A.A.U i).ι)
        (fun _ : Fin 1 => A.th i) ∧
      BasisAlong t.G t.PP.L N (Over.homMk ψ rfl : Over.mk (ψ ≫ (A.A.U i).ι) ⟶ Over.mk (A.A.U i).ι) (A.b i) := by
    intro p
    obtain ⟨W, _, _, _, ψ, hW, hψ⟩ := exists_trait z hZ p.1
    have hr : Set.range ψ ⊆ Set.range (A.A.U i).ι := by
      rintro _ ⟨y, rfl⟩
      exact ⟨⟨_, (congrArg (fun U => y ∈ U)
        (Scheme.preimage_eq_top_of_closedPoint_mem ψ (U := A.A.U i) (hψ ▸ p.2))).mpr trivial⟩, rfl⟩
    refine ⟨W, inferInstance, inferInstance, IsOpenImmersion.lift _ ψ hr, ?_, A.trait i W hW _ fun _ _ K _ _ x _ => inferInstance⟩
    exact (A.A.U i).ι.isOpenEmbedding.injective
      ((congrArg (fun q => q (IsLocalRing.closedPoint W)) (IsOpenImmersion.lift_fac _ ψ hr)).trans hψ)
  have : IsAffine (Over.mk (χ ≫ (A.A.U i).ι)).left := inferInstanceAs (IsAffine (Sp R))
  refine ⟨(basisAlong_iff hL _ _ _).2 (stableBas_of_traits hL _
      (exists_stableBas_local h₂.secBaseChangeAny t hp hA hK 1 le_rfl) (fun p => ?_) _ _),
    (basisAlong_iff hL _ _ _).2 (stableBas_of_traits hL _
      (exists_stableBas_local h₂.secBaseChangeAny t hp hA hK N hN) (fun p => ?_) _ _)⟩
  · obtain ⟨W, _, _, ψ, e, h, -⟩ := tr p
    exact ⟨W, inferInstance, inferInstance, ψ, e, (basisAlong_iff hL _ _ _).1 h⟩
  · obtain ⟨W, _, _, ψ, e, -, h⟩ := tr p
    exact ⟨W, inferInstance, inferInstance, ψ, e, (basisAlong_iff hL _ _ _).1 h⟩

end GlobalTheory.FrameBasis

import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.DataExtra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeftCosetsDoubleCosetInvEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicUnitarySupportedAtFinitePlaceEqLocalUnitar

namespace GlobalTheory.HeckeDual

section Group

open MeasureTheory

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

theorem exists_rep (K : Subgroup H) (ho : IsOpen (K : Set H)) (hc : IsCompact (K : Set H)) (b : H) :
    ∃ R : Finset H, (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * b * k₂) ∧
      ∀ x : H, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * b * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K := by
  classical
  haveI : DiscreteTopology (H ⧸ K) := QuotientGroup.discreteTopology ho
  have hf : ((fun k : H => ((k * b : H) : H ⧸ K)) '' (K : Set H)).Finite :=
    (hc.image (QuotientGroup.continuous_mk.comp (continuous_mul_const b))).finite_of_discrete
  refine ⟨hf.toFinset.image Quotient.out, fun γ hγ => ?_, ?_⟩
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hγ
    obtain ⟨k, hk, rfl⟩ := hf.mem_toFinset.1 hq
    obtain ⟨k', hk'⟩ := QuotientGroup.mk_out_eq_mul K (k * b)
    exact ⟨k, hk, k', k'.2, hk'⟩
  · rintro x ⟨k₁, h₁, k₂, h₂, rfl⟩
    have e : ((k₁ * b : H) : H ⧸ K) = ((k₁ * b * k₂ : H) : H ⧸ K) := (QuotientGroup.mk_mul_of_mem _ h₂).symm
    refine ⟨((k₁ * b : H) : H ⧸ K).out, ⟨Finset.mem_image_of_mem _ (hf.mem_toFinset.2 ⟨k₁, h₁, rfl⟩), ?_⟩, ?_⟩
    · rw [← QuotientGroup.eq, QuotientGroup.out_eq', e]
    · rintro γ ⟨hγ, h⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hγ
      rw [← QuotientGroup.eq, QuotientGroup.out_eq'] at h
      rw [h, e]

theorem exists_rep_inv [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (hmod : ∀ h : H, Measure.modularCharacter h = 1) {G : Type} [Group G] (ι : H →* G) (hι : Function.Injective ι)
    (K : Subgroup H) (ho : IsOpen (K : Set H)) (hc : IsCompact (K : Set H)) (KS : Set G)
    (hK : ∀ g, g ∈ KS ↔ ∃ k ∈ K, ι k = g) (a : H) (R : Finset G)
    (h1 : ∀ γ ∈ R, ∃ k₁ ∈ KS, ∃ k₂ ∈ KS, γ = k₁ * ι a * k₂)
    (h2 : ∀ x : G, (∃ k₁ ∈ KS, ∃ k₂ ∈ KS, x = k₁ * ι a * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ KS) :
    ∃ R' : Finset G, (∀ γ ∈ R', γ ∈ ι.range ∧ ∃ k₁ ∈ KS, ∃ k₂ ∈ KS, γ = k₁ * (ι a)⁻¹ * k₂) ∧
      (∀ x : G, (∃ k₁ ∈ KS, ∃ k₂ ∈ KS, x = k₁ * (ι a)⁻¹ * k₂) → ∃! γ, γ ∈ R' ∧ γ⁻¹ * x ∈ KS) ∧
      R'.card = R.card := by
  classical
  have hK' : ∀ k, ι k ∈ KS ↔ k ∈ K := fun k =>
    (hK _).trans ⟨fun ⟨k', h, e⟩ => hι e ▸ h, fun h => ⟨k, h, rfl⟩⟩
  have hdc : ∀ (b : H) (x : G), (∃ k₁ ∈ KS, ∃ k₂ ∈ KS, x = k₁ * ι b * k₂) ↔
      ∃ y, ι y = x ∧ ∃ k₁ ∈ K, ∃ k₂ ∈ K, y = k₁ * b * k₂ := fun b x => by
    constructor
    · rintro ⟨k₁, h₁, k₂, h₂, rfl⟩
      obtain ⟨l₁, g₁, rfl⟩ := (hK _).1 h₁
      obtain ⟨l₂, g₂, rfl⟩ := (hK _).1 h₂
      exact ⟨_, by rw [map_mul, map_mul], l₁, g₁, l₂, g₂, rfl⟩
    · rintro ⟨_, rfl, k₁, h₁, k₂, h₂, rfl⟩
      exact ⟨_, (hK' _).2 h₁, _, (hK' _).2 h₂, by rw [map_mul, map_mul]⟩
  obtain ⟨R', h3, h4⟩ := exists_rep K ho hc a⁻¹
  let μ : Measure H := Measure.haar
  haveI : μ.IsMulRightInvariant := ⟨fun g => by
    rw [GlobalTheory.AdelicUnimod.map_mul_right_eq, hmod, one_smul]⟩
  have hcard := GlobalTheory.card_leftCosets_doubleCoset_inv_eq μ K a (R.preimage ι hι.injOn) R' ho.measurableSet
    (ho.measure_pos μ ⟨1, one_mem _⟩).ne' hc.measure_lt_top.ne (fun γ hγ => by
      obtain ⟨y, e, h⟩ := (hdc _ _).1 (h1 _ (Finset.mem_preimage.1 hγ))
      exact hι e ▸ h) (fun x hx => by
      obtain ⟨γ, ⟨hγ, h⟩, hu⟩ := h2 (ι x) ((hdc _ _).2 ⟨x, rfl, hx⟩)
      obtain ⟨y, rfl, -⟩ := (hdc _ _).1 (h1 _ hγ)
      refine ⟨y, ⟨Finset.mem_preimage.2 hγ, (hK' _).1 (by rwa [map_mul, map_inv])⟩, fun z hz => hι (hu _
        ⟨Finset.mem_preimage.1 hz.1, ?_⟩)⟩
      rw [← map_inv, ← map_mul]
      exact (hK' _).2 hz.2) h3 h4
  rw [← map_inv]
  refine ⟨R'.image ι, fun γ hγ => ?_, fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hγ
    exact ⟨⟨y, rfl⟩, (hdc _ _).2 ⟨y, rfl, h3 y hy⟩⟩
  · obtain ⟨y, rfl, hy⟩ := (hdc _ _).1 hx
    obtain ⟨γ, ⟨hγ, h⟩, hu⟩ := h4 y hy
    refine ⟨ι γ, ⟨Finset.mem_image_of_mem _ hγ, ?_⟩, ?_⟩
    · rw [← map_inv, ← map_mul]
      exact (hK' _).2 h
    · rintro z ⟨hz, h'⟩
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz
      rw [hu w ⟨hw, (hK' _).1 (by rwa [map_mul, map_inv])⟩]
  · rw [Finset.card_image_of_injective _ hι, ← hcard, Finset.card_preimage, Finset.filter_true_of_mem]
    intro γ hγ
    obtain ⟨y, e, -⟩ := (hdc _ _).1 (h1 _ hγ)
    exact ⟨y, e⟩

end Group

section Local

open scoped TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.AdelicUnimod

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem modular_eq_one (hσ : ∀ x, σ (σ x) = x) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ) (hJ : IsHermND σ J)
    (v : HeightOneSpectrum (𝓞 F)) (g : GLoc σ J v) : Measure.modularCharacter g = 1 := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  haveI : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) _
  letI : Algebra ℚ (Fv F v ⊗[F] E) := ((inclR (F := F) (Fv F v)).comp (algebraMap ℚ E)).toAlgebra
  obtain ⟨M, hM⟩ := exists_framed (σ := (σ : E →+* E)) hσ (J := J) (by ext i j; exact hJ.1 i j) hJ.2
  have hF : Framed (sigR (Fv F v) σ) (JR (Fv F v) J) (M.map (inclR (Fv F v))) := hM.map fun x => rfl
  have hss : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [sigR, hσ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  obtain ⟨T, hTc, hT, hT'⟩ := exists_involution (GlobalTheory.AdelicUnitaryTop.continuous_sigR (Fv F v) σ) hss hF
  have hgen : Generic (sigR (Fv F v) σ) :=
    generic_of_semilocal (δ := inclR (Fv F v) δ) (hδ.isUnit.map _) (by
      rw [← map_neg, ← hσδ]; rfl)
  have key : ∀ T : GLoc σ J v →* GLoc σ J v, Continuous T → (∀ x, T (T x) = x) → ∀ x,
      Measure.modularCharacter (T x) = Measure.modularCharacter x := fun T => modular_involution T
  exact char_eq_one hss hF hgen (Measure.modularCharacter (G := GLoc σ J v)) (fun x x' h => by
    rw [hT' x x' h]
    exact key T hTc hT x) g

end Local

section Host

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem idem_of_isPrimeIdem {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f) :
    e * e = e ∧ ∃ v, GlobalTheory.PlaceComp.IsIdemOf D.host.E v f := by
  rcases h with ⟨⟨⟨he, -, v, ε, ⟨α, rfl, h1, h2⟩, hf⟩, -⟩, rfl⟩ | ⟨rfl, ⟨v, ε, ⟨α, rfl, h1, h2⟩, rfl⟩, -⟩
  · exact ⟨he, v, hf ▸ GlobalTheory.PlaceComp.isIdemOf_algebraMap h1 h2⟩
  · have h := GlobalTheory.PlaceComp.isIdemOf_algebraMap (E := D.host.E) h1 h2
    exact ⟨(GlobalTheory.SuppLocal.idem_mul_iff h _).2 ⟨h.1, h.2.2⟩, v, h⟩

theorem suppF_iff (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D}
    (hf : GlobalTheory.PlaceComp.IsIdemOf D.host.E v f) (g : GA D V) :
    SuppF V f g ↔ g ∈ (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v).range := by
  have h1 : ∀ w (g : GA D V), GlobalTheory.PlaceComp.locMat D.sp.cm V w g = 1 ↔
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram w g = 1 := fun w g => by
    rw [← GlobalTheory.AdelicU.projFinLoc_projFin]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg (HA.mat _ _ _) h⟩
  refine (GlobalTheory.SuppLocal.supp_iff D.sp.cm V hf g).trans ?_
  simp only [h1]
  constructor
  · rintro ⟨h2, h3⟩
    refine ⟨GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g, GlobalTheory.AdelicU.GAd_ext _ _ (fun w => ?_) fun u => ?_⟩
    · rw [GlobalTheory.AdelicU.projArch_emb, GlobalTheory.AdelicU.mem_finPts_iff_forall.1 h2 w]
    · by_cases e : u = v
      · rw [e, GlobalTheory.AdelicU.proj_emb_self]
      · rw [GlobalTheory.AdelicU.proj_emb_ne _ _ e, h3 u e]
  · rintro ⟨x, rfl⟩
    exact ⟨GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_emb _ _ v x), fun w hw => GlobalTheory.AdelicU.proj_emb_ne _ _ hw x⟩

theorem exists_skew (D : D7) : ∃ δ : D.host.E, δ ≠ 0 ∧ D.sp.cm.sig δ = -δ := by
  by_contra! h
  have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun a => (D.sp.cm.fixed a).1 (by
    by_contra hne
    exact h (star a - a) (sub_ne_zero.2 hne) (by show star _ = _; simp))
  have := (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E)
    ⟨(algebraMap D.host.F D.host.E).injective, hs⟩).finrank_eq
  rw [D.sp.cm.deg2, Module.finrank_self] at this
  omega

theorem isLattice_frameLat (V : HSp D) : Submodule.IsLattice D.host.E (GlobalTheory.AdelicU.frameLat V) := by
  refine ⟨GlobalTheory.AdelicU.frameLat_fg V, ?_⟩
  have : (GlobalTheory.AdelicU.frameLat V : Set (Fin V.rank → D.host.E)) =
      V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) :=
    (V.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
  rw [this, ← Submodule.map_span, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]

end Host

end GlobalTheory.HeckeDual

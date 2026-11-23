import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValues
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordValuationBoundLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordDegreeBoundCharZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.FinUnit

section Sizes

variable {L : Type} [Field L] [NumberField L] (v : FinitePlace L)

theorem size_int_le (a : 𝓞 L) : v (algebraMap (𝓞 L) L a) ≤ 1 := by
  rw [← FinitePlace.norm_embedding_eq]
  exact FinitePlace.norm_le_one L v.maximalIdeal a

theorem size_int_eq_one_iff (a : 𝓞 L) : v (algebraMap (𝓞 L) L a) = 1 ↔ a ∉ (primeOf v).asIdeal := by
  rw [← FinitePlace.norm_embedding_eq]
  exact FinitePlace.norm_eq_one_iff_notMem L v.maximalIdeal a

theorem local_sizes (A : Type) [CommRing A] [Algebra (𝓞 L) A] [IsLocalization.AtPrime A (primeOf v).asIdeal]
    [Algebra A L] [IsScalarTower (𝓞 L) A L] :
    (∀ r : A, v (algebraMap A L r) ≤ 1) ∧ ∀ r : A, v (algebraMap A L r) = 1 → IsUnit r := by
  have key : ∀ r : A, ∃ (a d : 𝓞 L), d ∉ (primeOf v).asIdeal ∧ r * algebraMap (𝓞 L) A d = algebraMap (𝓞 L) A a ∧
      v (algebraMap A L r) = v (algebraMap (𝓞 L) L a) := by
    intro r
    obtain ⟨a, d, rfl⟩ := IsLocalization.exists_mk'_eq (primeOf v).asIdeal.primeCompl r
    have e := IsLocalization.mk'_spec A a d
    refine ⟨a, d, d.2, e, ?_⟩
    have e' := congrArg (fun t => v (algebraMap A L t)) e
    simp only [map_mul, ← IsScalarTower.algebraMap_apply] at e'
    rwa [(size_int_eq_one_iff v d).2 d.2, _root_.mul_one] at e'
  refine ⟨fun r => ?_, fun r hr => ?_⟩
  · obtain ⟨a, d, -, -, e⟩ := key r
    rw [e]
    exact size_int_le v a
  · obtain ⟨a, d, -, e₁, e₂⟩ := key r
    have ha : a ∉ (primeOf v).asIdeal := (size_int_eq_one_iff v a).1 (e₂ ▸ hr)
    have hu : IsUnit (algebraMap (𝓞 L) A a) :=
      IsLocalization.map_units A (⟨a, ha⟩ : (primeOf v).asIdeal.primeCompl)
    rw [← e₁] at hu
    exact isUnit_of_mul_isUnit_left hu

end Sizes

section Centre

variable {X : Scheme.{0}} {L : Type} [Field L] [NumberField L] (v : FinitePlace L) (z : Sp (𝓞 L) ⟶ X)

theorem centre_local (A : Type) [CommRing A] [IsLocalRing A] [Algebra (𝓞 L) A]
    [IsLocalization.AtPrime A (primeOf v).asIdeal] :
    centre (spMap (algebraMap (𝓞 L) A) ≫ z) = z (primeOf v) := by
  have e : (spMap (algebraMap (𝓞 L) A)) (IsLocalRing.closedPoint A) = primeOf v := by
    apply PrimeSpectrum.ext
    exact IsLocalization.AtPrime.comap_maximalIdeal A (primeOf v).asIdeal
  exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg z e)

end Centre

section Det

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem div_mem_of_span_eq (R : Subring Ω) {t g : Ω} (ht : t ≠ 0) (hg : g ≠ 0)
    (h : Submodule.span R {t} = Submodule.span R {g}) : g / t ∈ R ∧ t / g ∈ R := by
  have h1 : t ∈ Submodule.span R {g} := h ▸ Submodule.mem_span_singleton_self _
  have h2 : g ∈ Submodule.span R {t} := h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨r₁, hr₁⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨r₂, hr₂⟩ := Submodule.mem_span_singleton.1 h2
  have e₁ : (r₁ : Ω) * g = t := hr₁
  have e₂ : (r₂ : Ω) * t = g := hr₂
  constructor
  · rw [← e₂, mul_div_cancel_right₀ _ ht]; exact r₂.2
  · rw [← e₁, mul_div_cancel_right₀ _ hg]; exact r₁.2

theorem detLat_isGenAt {E : Type} [AddCommGroup E] [Module Ω E] (V : Lat ξ E) {r : ℕ} {s b : Fin r → E}
    {T : Matrix (Fin r) (Fin r) Ω} {p : Cpt ξ} (hs : LinearIndependent Ω s) (hb : V.IsFrameAt b p)
    (hT : ∀ k, b k = ∑ k', T k' k • s k') (hdet : T.det ≠ 0) : (detLat V s).IsGenAt p T.det := by
  refine ⟨hdet, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)⟩
  · rintro t ⟨b₂, T₂, hb₂, hT₂, rfl⟩
    have hch : ∀ q, ∃ c : Fin r → regAt ξ p, b₂ q = ∑ i, (c i : Ω) • b i := fun q => by
      have hm : b₂ q ∈ V p := by rw [hb₂.2]; exact Submodule.subset_span ⟨q, rfl⟩
      rw [hb.2] at hm
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm
      exact ⟨c, hc.symm⟩
    choose c hc using hch
    let M : Matrix (Fin r) (Fin r) (regAt ξ p) := Matrix.of fun i q => c q i
    have hM : T₂ = T * M.map (regAt ξ p).subtype := by
      ext k' q
      have e : ∑ k', T₂ k' q • s k' = ∑ k', (T * M.map (regAt ξ p).subtype) k' q • s k' := by
        rw [← hT₂ q, hc q]
        simp only [hT, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp [M, _root_.mul_comm]
      have e' : ∑ k', (T₂ k' q - (T * M.map (regAt ξ p).subtype) k' q) • s k' = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self]
      exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hs _ e' k')
    refine Submodule.mem_span_singleton.2 ⟨M.det, ?_⟩
    show (M.det : Ω) * T.det = T₂.det
    have e : (M.det : Ω) = (M.map (regAt ξ p).subtype).det := RingHom.map_det (regAt ξ p).subtype M
    rw [hM, Matrix.det_mul, e, _root_.mul_comm]
  · rintro _ rfl
    exact ⟨b, T, hb, hT, rfl⟩

end Det

section Core

theorem valAt_det {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {F : Type} [CommRing F] [IsLocalRing F]
    {z : Sp F ⟶ X} (h : genPt ξ ⤳ centre z) {r : ℕ} {T' : Matrix (Fin r) (Fin r) Ω} {T : Matrix (Fin r) (Fin r) F}
    (hv : ∀ i j, ValAt ξ z (T' i j) (T i j)) : ValAt ξ z T'.det T.det := by
  have hex : ∀ i j, ∃ s, genMap ξ ⟨centre z, h⟩ s = T' i j ∧ (Scheme.stalkClosedPointTo z).hom s = T i j :=
    fun i j => by
      obtain ⟨_, s, h1, h2⟩ := hv i j
      exact ⟨s, h1, h2⟩
  choose S h1 h2 using hex
  let M : Matrix (Fin r) (Fin r) (X.presheaf.stalk (centre z)) := Matrix.of S
  have e1 : T' = M.map (genMap ξ ⟨centre z, h⟩) := by ext i j; exact (h1 i j).symm
  have e2 : T = M.map (Scheme.stalkClosedPointTo z).hom := by ext i j; exact (h2 i j).symm
  exact ⟨h, M.det, by rw [e1]; exact RingHom.map_det _ _, by rw [e2]; exact RingHom.map_det _ _⟩

theorem core (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (Ψ : Type) [Fintype Ψ] (Ei : Type) [AddCommGroup Ei] [Module Ω Ei]
    (Vl : Ψ → Lat ξ Ei) (m : ℕ) (s : Ψ → Fin m → Ei) (a : K → ℤ) (e₀ : Ω) (hall : ∀ q : X, genPt ξ ⤳ q)
    (hT : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (hs : ∀ τ, LinearIndependent Ω (s τ))
    (hdeg : (Lat.tens (fun τ => detLat (Vl τ) (s τ)) (fun _ => -1)).IsDegOn Set.univ y a e₀)
    (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X) (c₀ : (k : K) → J k) (g : L)
    (v : FinitePlace L) (b' : Ψ → Fin m → Ei) (T' : Ψ → Matrix (Fin m) (Fin m) Ω)
    (T : Ψ → Matrix (Fin m) (Fin m) L)
    (hC : CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w) (hw0 : ∀ k, w ⟨k, c₀ k⟩ ≠ 0)
    (hg : ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (e₀ * chartMono y c₀ a)⁻¹ g)
    (hfr : ∀ τ, (Vl τ).IsFrameAt (b' τ) ⟨z (primeOf v), hall _⟩)
    (hb : ∀ τ k, b' τ k = ∑ k', T' τ k' k • s τ k')
    (hval : ∀ τ i j, ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (T' τ i j) (T τ i j))
    (hdet : ∀ τ, (T τ).det ≠ 0)
    (A : Type) [CommRing A] [IsLocalRing A] [Algebra (𝓞 L) A] [IsLocalization.AtPrime A (primeOf v).asIdeal]
    [Algebra A L] [IsScalarTower (𝓞 L) A L] :
    (∏ τ, v (T τ).det) * GlobalTheory.CompanionTheory.Ar.RootHt.locRatio a w c₀ v = v g := by
  classical
  have hξ := hT.gen
  have he₀ : e₀ ≠ 0 := hdeg.1
  obtain ⟨hA₁, hA₂⟩ := local_sizes v A
  set zL : Sp L ⟶ X := spMap (algebraMap (𝓞 L) L) ≫ z with hzLdef
  set zA : Sp A ⟶ X := spMap (algebraMap (𝓞 L) A) ≫ z with hzA
  have hzL : zL = spMap (algebraMap A L) ≫ zA := by
    rw [hzLdef, hzA, ← Category.assoc, IsScalarTower.algebraMap_eq (𝓞 L) A L]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  obtain ⟨ch, h, hcne, hmax, hin⟩ := GlobalTheory.CompanionTheory.Ar.RootHt.bestChart_finite X Ω ξ K J y L w v A zA hall hT hA₁ hA₂
    (hzL ▸ hC)
  have hL : genPt ξ ⤳ centre zL := hall _
  have hP : (⟨z (primeOf v), hall _⟩ : Cpt ξ) = ⟨centre zA, h⟩ := Subtype.ext (centre_local v z A).symm
  have hfr' : ∀ τ, (Vl τ).IsFrameAt (b' τ) ⟨centre zA, h⟩ := fun τ => hP ▸ hfr τ

  have hdv : ∀ τ, ValAt ξ zL (T' τ).det (T τ).det := fun τ => valAt_det hL (hval τ)
  have hdet' : ∀ τ, (T' τ).det ≠ 0 := fun τ h0 => hdet τ <| by
    have h1 := hdv τ
    rw [h0] at h1
    exact LieTangent.valAt_unique hξ h1 ⟨hL, 0, map_zero _, map_zero _⟩
  have hgen : ∀ τ, (detLat (Vl τ) (s τ)).IsGenAt ⟨centre zA, h⟩ (T' τ).det := fun τ =>
    detLat_isGenAt (Vl τ) (hs τ) (hfr' τ) (hb τ) (hdet' τ)
  have htg := Flag.tens_gen (fun τ => detLat (Vl τ) (s τ)) (fun _ => -1) ⟨centre zA, h⟩ _ hgen

  have hdg := hdeg.2 ⟨centre zA, h⟩ trivial ch hin
  rw [htg.2] at hdg
  set D : Ω := ∏ τ, (T' τ).det with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => hdet' τ
  have ht : (∏ τ, (T' τ).det ^ (-1 : ℤ)) = D⁻¹ := by
    simp only [_root_.zpow_neg, zpow_one, hD, Finset.prod_inv_distrib]
  have hy : ∀ k, y ⟨k, ch k⟩ ≠ 0 := fun k => (hC.2 k (ch k) (isUnit_iff_ne_zero.2 (hcne k))).1
  have hy₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => (hC.2 k (c₀ k) (isUnit_iff_ne_zero.2 (hw0 k))).1
  set G : Ω := GlobalTheory.CompanionTheory.Ar.RootHt.gen y a e₀ ch with hG
  have hG0 : G ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) he₀
  have hsp : Submodule.span (regAt ξ ⟨centre zA, h⟩) {D⁻¹} = Submodule.span (regAt ξ ⟨centre zA, h⟩) {G} := by
    rw [← ht]
    exact hdg
  obtain ⟨hε, hε'⟩ := div_mem_of_span_eq _ (inv_ne_zero hD0) hG0 hsp

  obtain ⟨r, hr⟩ := GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.val_of_mem h hε
  obtain ⟨r', hr'⟩ := GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.val_of_mem h hε'
  have hrr : r * r' = 1 := by
    have h1 := GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.val_mul hr hr'
    have e : G / D⁻¹ * (D⁻¹ / G) = 1 := by field_simp
    rw [e] at h1
    exact LieTangent.valAt_unique hξ h1 (GlobalTheory.CompanionTheory.Ar.RootHt.valAt_one h)
  have hvr : v (algebraMap A L r) = 1 := by
    have h1 : v (algebraMap A L r) * v (algebraMap A L r') = 1 := by
      rw [← map_mul, ← map_mul, hrr, map_one, map_one]
    have h2 := hA₁ r
    have h3 := hA₁ r'
    nlinarith [apply_nonneg v (algebraMap A L r), apply_nonneg v (algebraMap A L r')]
  have hrL : ValAt ξ zL (G / D⁻¹) (algebraMap A L r) := by
    rw [hzL]; exact LieTangent.valAt_base hξ (algebraMap A L) hr

  have hτ := GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.val_gen_ratio hC hL a he₀ ch c₀ hcne hw0
  have hm₀ : chartMono y c₀ a ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy₀ k)
  have hgen₀ : GlobalTheory.CompanionTheory.Ar.RootHt.gen y a e₀ c₀ = e₀ * chartMono y c₀ a := _root_.mul_comm _ _
  have hid : G / D⁻¹ * (e₀ * chartMono y c₀ a)⁻¹ = D * (G / GlobalTheory.CompanionTheory.Ar.RootHt.gen y a e₀ c₀) := by
    rw [hgen₀]
    field_simp
  have hl := GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.val_mul hrL hg
  have hr₂ := GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.val_mul
    (GlobalTheory.CompanionTheory.Ar.RootHt.valAt_prod hL Finset.univ _ _ hdv) hτ
  rw [hid] at hl
  have hv := LieTangent.valAt_unique hξ hl hr₂
  have hn := congrArg v hv
  rw [map_mul, hvr, _root_.one_mul, map_mul, map_prod] at hn
  rw [hn]
  congr 1
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hsup : (⨆ i, v (w ⟨k, i⟩)) = v (w ⟨k, ch k⟩) :=
    le_antisymm (by haveI : Nonempty (J k) := ⟨ch k⟩; exact ciSup_le (hmax k))
      (le_ciSup (f := fun i => v (w ⟨k, i⟩)) (Set.finite_range _).bddAbove (ch k))
  rw [map_zpow₀, map_div₀, hsup]

end Core

theorem det_frames_size : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (Ψ : Type) [Fintype Ψ] (Ei : Type) [AddCommGroup Ei] [Module Ω Ei] (Vl : Ψ → Lat ξ Ei) (m : ℕ) (s : Ψ → Fin m → Ei) (a : K → ℤ) (e₀ : Ω) (hall : ∀ q : X, genPt ξ ⤳ q), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ τ, LinearIndependent Ω (s τ)) → (Lat.tens (fun τ => detLat (Vl τ) (s τ)) (fun _ => -1)).IsDegOn Set.univ y a e₀ → ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X) (c₀ : (k : K) → J k) (g : L) (v : FinitePlace L) (b' : Ψ → Fin m → Ei) (T' : Ψ → Matrix (Fin m) (Fin m) Ω) (T : Ψ → Matrix (Fin m) (Fin m) L), CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → (∀ k, w ⟨k, c₀ k⟩ ≠ 0) → ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (e₀ * chartMono y c₀ a)⁻¹ g → g ≠ 0 → (∀ τ, (Vl τ).IsFrameAt (b' τ) ⟨z (primeOf v), hall _⟩) → (∀ τ k, b' τ k = ∑ k', T' τ k' k • s τ k') → (∀ τ i j, ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (T' τ i j) (T τ i j)) → (∀ τ, (T τ).det ≠ 0) → (∏ τ, v (T τ).det) * GlobalTheory.CompanionTheory.Ar.RootHt.locRatio a w c₀ v = v g := by
  intro X Ω _ ξ K _ J _ y Ψ _ Ei _ _ Vl m s a e₀ hall hT hs hdeg L _ _ w z c₀ g v b' T' T hC hw0 hg _ hfr hb hval hdet
  have hu : ∀ d : (primeOf v).asIdeal.primeCompl, IsUnit (algebraMap (𝓞 L) L d) := fun d => by
    refine isUnit_iff_ne_zero.2 fun h0 => d.2 ?_
    have : (d : 𝓞 L) = 0 := (FaithfulSMul.algebraMap_injective (𝓞 L) L) (by rw [h0, map_zero])
    rw [this]
    exact zero_mem _
  letI : Algebra (Localization.AtPrime (primeOf v).asIdeal) L := (IsLocalization.lift hu).toAlgebra
  haveI : IsScalarTower (𝓞 L) (Localization.AtPrime (primeOf v).asIdeal) L :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hu x).symm
  exact core X Ω ξ K J y Ψ Ei Vl m s a e₀ hall hT hs hdeg L w z c₀ g v b' T' T hC hw0 hg hfr hb hval hdet
    (Localization.AtPrime (primeOf v).asIdeal)

end GlobalTheory.CompanionTheory.Ar.RootHt.FinUnit

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnCosSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackFrameSpanningFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleCarriesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackUnipotentFrameUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackUnipotentFrameIsFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagSpannedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagsSameFrameIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedFlagTriangularFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialChartOfFlagBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialPointFactorsThroughChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentTriangularFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularChangeSpansFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCellFrameOfSpans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtalePolynomialSubstitution

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)
open scoped ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineChart

theorem exists_cell (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → B.Modules)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (hfl : IsFlagBundle π E r fl)
    (hE : ∀ a, IsVB (E a) (r a)) (U : B.Opens) (hU : IsAffineOpen U) (eU : ∀ a, Fin (r a) → Γ(E a, U))
    (heU : ∀ a, IsFrame (eU a)) :
    ∃ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U), IsAffineOpen W ∧ ∃ n : (Σ a, Low (r a)) → Γ(Y, W),
      Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n) ∧
      (∀ a, Spans (fl a) W (pullCol π (eU a) hW (uniR fun s => n ⟨a, s⟩))) ∧
      ∀ (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (n' : (Σ a, Low (r a)) → Γ(Y, V)),
        (∀ a, Spans (fl a) V (pullCol π (eU a) hV (uniR fun s => n' ⟨a, s⟩))) → V ≤ W := by
  obtain ⟨W, hW, n, hSp, hMax⟩ := exists_cellLocus B Y π ι r E fl hE U eU heU
  let A := CommRingCat.of (MvPolynomial (Σ a, Low (r a)) Γ(B, U))
  let g : Spec A ⟶ B := Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : Γ(B, U) →+* MvPolynomial (Σ a, Low (r a)) Γ(B, U))) ≫ hU.fromSpec
  have hgU : (⊤ : (Spec A).Opens) ≤ g ⁻¹ᵁ U := by
    simp [g, Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
  let n' : (Σ a, Low (r a)) → Γ(Spec A, ⊤) := fun s => (Scheme.ΓSpecIso A).inv.hom (MvPolynomial.X s)
  have hfr : ∀ a, IsFrame (pullCol g (eU a) hgU (uniR fun s => n' ⟨a, s⟩)) := fun a =>
    UniColFrame.isFrame_pullCol_uniR _ _ g (E a) (r a) (hE a) U (eU a) (heU a) ⊤ hgU _
  choose fl' hfl' using fun a => exists_flag_spans_of_frame (Spec A) _ (r a) _ (hfr a)
  obtain ⟨ψ, ⟨w, hC⟩, -⟩ := hfl (Spec A) g fl'
  have hψ : (⊤ : (Spec A).Opens) ≤ ψ ⁻¹ᵁ W := by
    intro t _
    obtain ⟨V, hV, n₀, ht, hV'⟩ := CellOpen.spans_uniR_near_image B Y π ι r E fl hE U eU heU (Spec A) ψ g w fl' hC ⊤
      hgU n' hfl' t trivial
    obtain ⟨hVW, -⟩ := hMax V hV n₀ hV'
    exact hVW ht
  have hn : ∀ s, (ψ.appLE W ⊤ hψ).hom (n s) = (Scheme.ΓSpecIso A).inv.hom (MvPolynomial.X s) := by
    rintro ⟨a, s⟩
    have h1 := spans_pullCol_of_carries B Y (Spec A) π ι r E fl ψ g w fl' hC U a (eU a) W hW
      (uniR fun s => n ⟨a, s⟩) ⊤ hψ hgU (hSp a)
    rw [map_uniR] at h1
    exact congrFun (low_eq_of_spans_pullCol (Spec A) B g (E a) (r a) (hE a) U (eU a) (heU a) (fl' a) ⊤ hgU _ _ h1
      (hfl' a)) s
  let φ : W.toScheme ⟶ Spec A :=
    W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n))
  obtain ⟨hφg, hφn⟩ := cellToSpec B Y π U hU W hW _ n
  have hφg' : φ ≫ g = W.ι ≫ π := by simpa only [φ, g, Category.assoc] using hφg
  have hWU : (⊤ : W.toScheme.Opens) ≤ (W.ι ≫ π) ⁻¹ᵁ U := by
    intro x _
    exact hW x.2
  have h₁ : (⊤ : W.toScheme.Opens) ≤ φ ⁻¹ᵁ ⊤ := le_top.trans (by simp)
  have h₂ : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := fun x _ => x.2
  have hφC : Carries g E r fl' φ (W.ι ≫ π) hφg' (carried π E r fl W.ι (W.ι ≫ π) rfl) := by
    intro a i
    have k₁ := spans_pullCol_of_carries _ _ _ g ι r E fl' φ (W.ι ≫ π) hφg' _
      (carries_carried g E r fl' φ (W.ι ≫ π) hφg') U a (eU a) ⊤ hgU (uniR fun s => n' ⟨a, s⟩) ⊤ h₁ hWU (hfl' a)
    have k₂ := spans_pullCol_of_carries _ _ _ π ι r E fl W.ι (W.ι ≫ π) rfl _
      (carries_carried π E r fl W.ι (W.ι ≫ π) rfl) U a (eU a) W hW (uniR fun s => n ⟨a, s⟩) ⊤ h₂ hWU (hSp a)
    rw [map_uniR] at k₁ k₂
    have e : (fun s => (φ.appLE ⊤ ⊤ h₁).hom (n' ⟨a, s⟩)) = fun s => (W.ι.appLE W ⊤ h₂).hom (n ⟨a, s⟩) :=
      funext fun s => hφn h₁ h₂ _
    rw [e] at k₁
    obtain ⟨e, he⟩ := steps_iso_of_spans_top _ _ _ _ _ _ k₁ k₂ i
    exact ⟨e, by simpa [carried, Vert.Flag.ofIso, Vert.Flag.pull] using he⟩
  have huniq : W.ι = φ ≫ ψ := (hfl W.toScheme (W.ι ≫ π) (carried π E r fl W.ι (W.ι ≫ π) rfl)).unique
    ⟨rfl, carries_carried π E r fl W.ι (W.ι ≫ π) rfl⟩
    ⟨by rw [Category.assoc, w, hφg'], carries_comp π E r fl ψ g w fl' φ (W.ι ≫ π) hφg' _ _ hC hφC⟩
  obtain ⟨hAff, hBij⟩ := isAffineOpen_and_bijective_of_section B Y π U hU W hW _ n ψ w hψ hn
    (by simpa only [φ, Category.assoc] using huniq.symm)
  exact ⟨W, hW, hAff, n, hBij, hSp, fun V hV n₁ h => (hMax V hV n₁ h).1⟩

open MvPolynomial in

theorem etale_snoc {k A R N : Type} [CommRing k] [CommRing A] [CommRing R] (α : k →+* A) {d : ℕ} (t : Fin d → A)
    (f : A →+* R) (n : N → R) (s₀ : N) (hs : ∀ s, s = s₀) (hg : (eval₂Hom α t).Etale)
    (hΦ : Function.Bijective (eval₂Hom f n)) :
    (eval₂Hom (f.comp α) (Fin.snoc (α := fun _ => R) (fun j => f (t j)) (n s₀))).Etale := by
  let ι : MvPolynomial (Fin (d+1)) k →+* MvPolynomial N (MvPolynomial (Fin d) k) :=
    eval₂Hom (C.comp C) (Fin.snoc (α := fun _ => MvPolynomial N (MvPolynomial (Fin d) k)) (fun j => C (X j)) (X s₀))
  let κ : MvPolynomial N (MvPolynomial (Fin d) k) →+* MvPolynomial (Fin (d+1)) k :=
    eval₂Hom (eval₂Hom C (fun j => X j.castSucc)) (fun _ => X (Fin.last d))
  have h1 : κ.comp ι = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ι, κ]
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [ι, κ]
  have h2 : ι.comp κ = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r; simp [ι, κ]
      · intro j
        simp [ι, κ]
    · intro j
      simp [ι, κ, hs j]
  have hι : Function.Bijective ι :=
    Function.bijective_iff_has_inverse.2 ⟨κ, fun x => DFunLike.congr_fun h1 x, fun x => DFunLike.congr_fun h2 x⟩
  have key : eval₂Hom (f.comp α) (Fin.snoc (α := fun _ => R) (fun j => f (t j)) (n s₀)) =
      (eval₂Hom f n).comp ((MvPolynomial.map (eval₂Hom α t)).comp ι) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ι]
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [ι]
  rw [key]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hι) (etale_mvPolynomial_map_of_etale _ hg))
    (RingHom.Etale.of_bijective hΦ)

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {σ : k →+* ℂ}

theorem exists_chart_le {d : ℕ} (c₀ : AlgChart q σ d) {y : CxPts q σ} (hy : y ∈ c₀.e.source) (V : B.Opens)
    (hV : y ∈ ptsIn q σ V) : ∃ c : AlgChart q σ d, y ∈ c.e.source ∧ c.U ≤ V := by
  have hy0 : y ∈ ptsIn q σ c₀.U := c₀.source_subset hy
  obtain ⟨f, hfV, hf⟩ := c₀.affine.exists_basicOpen_le (V := V) ⟨_, mem_ptsIn.1 hV⟩ (mem_ptsIn.1 hy0)
  have hle : B.basicOpen f ≤ c₀.U := B.basicOpen_le f
  have hE : (MvPolynomial.eval₂Hom (algX q (B.basicOpen f)) (fun a => resG B hle (c₀.x a))).Etale := by
    have e : MvPolynomial.eval₂Hom (algX q (B.basicOpen f)) (fun a => resG B hle (c₀.x a)) =
        (resG B hle).comp (MvPolynomial.eval₂Hom (algX q c₀.U) c₀.x) := by
      rw [MvPolynomial.comp_eval₂Hom, GlobalTheory.TopForm.resG_comp_algX]
    rw [e]
    have hR : (resG B hle).Etale := by
      letI : Algebra Γ(B, c₀.U) Γ(B, B.basicOpen f) := (resG B hle).toAlgebra
      haveI : IsLocalization.Away f Γ(B, B.basicOpen f) := c₀.affine.isLocalization_basicOpen f
      exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway f)
    exact RingHom.Etale.stableUnderComposition _ _ c₀.etale hR
  obtain ⟨c, hc, hU, -⟩ := AlgChart.exists_of_etale (c₀.affine.basicOpen f) _ hE (mem_ptsIn.2 hf)
  exact ⟨c, hc, hU ▸ hfV⟩

theorem comp_algX (π : Y ⟶ B) (w : π ≫ q = p) {U : B.Opens} {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ U) :
    (π.appLE U W hW).hom.comp (algX q U) = algX p W := by
  subst w
  have e := Scheme.Hom.appLE_comp_appLE π q ⊤ U W le_top hW
  exact congrArg (fun f ↦ (CommRingCat.Hom.hom f).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) e

theorem exists_chart_over (π : Y ⟶ B) (w : π ≫ q = p) {d : ℕ} (c : AlgChart q σ d) {W : Y.Opens}
    (hW : W ≤ π ⁻¹ᵁ c.U) (hWa : IsAffineOpen W) {N : Type} (n : N → Γ(Y, W)) (s₀ : N) (hs : ∀ s, s = s₀)
    (hΦ : Function.Bijective (MvPolynomial.eval₂Hom (π.appLE c.U W hW).hom n)) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ W) :
    ∃ c' : AlgChart p σ (d + 1), y ∈ c'.e.source ∧ c'.e.source ⊆ ptsIn p σ W ∧ ∀ z ∈ c'.e.source,
      LineCos.fib (c'.e z) = ev p σ W (n s₀) z ∧ (PtsOver.map π w (spMap σ) z ∈ c.e.source →
        WithLp.toLp 2 (LineCos.base (c'.e z)) = c.e (PtsOver.map π w (spMap σ) z)) := by
  have h := etale_snoc (algX q c.U) c.x (π.appLE c.U W hW).hom n s₀ hs c.etale hΦ
  rw [comp_algX π w hW] at h
  obtain ⟨c', hc', hU, hx⟩ := AlgChart.exists_of_etale hWa _ h hy
  subst hU
  refine ⟨c', hc', c'.source_subset, fun z hz => ⟨?_, fun hb => ?_⟩⟩
  · rw [LineCos.fib, c'.apply_eq z hz, hx]
    simp
  · ext a
    rw [c.apply_eq _ hb]
    change c'.e z a.castSucc = _
    rw [c'.apply_eq z hz, hx]
    simp only [Fin.snoc_castSucc]
    exact valR_appLE z.1 π hW (c'.source_subset hz) _

theorem isFrame_of_spans {X : Scheme.{0}} {F : X.Modules} {m : ℕ} {fl : Vert.Flag F m} {V : X.Opens}
    {v : Fin m → Γ(F, V)} (h : Spans fl V v) : IsFrame v := by
  obtain ⟨s, hs, hv⟩ := h (Fin.last m)
  have := fl.isIso_last
  have e : v = fun j => (fl.ι (Fin.last m)).app V (s j) := funext fun j => (hv j).symm
  rw [e]
  exact hs.map_iso _

theorem exists_spans {X : Scheme.{0}} {F : X.Modules} {m : ℕ} (fl : Vert.Flag F m) (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ v : Fin m → Γ(F, V), Spans fl V v := by
  obtain ⟨W, hW, u, -, hs⟩ := FlagZ.Loc.exists_nested_frames fl x (Fin.last m)
  exact ⟨W, hW, fun j => (fl.ι (Fin.last _)).app W (u j), fun l => hs l l.is_le⟩

theorem isUnit_det_of_isFrame (π : Y ⟶ B) {E : B.Modules} [E.IsQuasicoherent] {U : B.Opens} {m : ℕ}
    {e : Fin m → Γ(E, U)} (he : IsFrame e) {V : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U) {A : Matrix (Fin m) (Fin m) Γ(Y, V)}
    (h : IsFrame (pullCol π e hV A)) : IsUnit A.det := by
  have hb := CellOpen.isFrame_pullbackSections π he hV
  have hu := (hb.detUnit h le_rfl le_rfl).isUnit
  rw [IsFrame.val_detUnit, Module.Basis.det_apply] at hu
  convert hu using 2
  ext i j
  have e₁ : resM _ le_rfl (pullCol π e hV A j) = ∑ l, A l j • hb.basis le_rfl l := by
    simp only [IsFrame.basis_apply, resM_self, pullCol]
  rw [Module.Basis.toMatrix_apply, e₁, Module.Basis.repr_sum_self]

theorem exists_uni (π : Y ⟶ B) {E : B.Modules} {U : B.Opens} (e : Fin 2 → Γ(E, U))
    {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2} {V : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U)
    {A : Matrix (Fin 2) (Fin 2) Γ(Y, V)} (hA : Spans fl V (pullCol π e hV A)) (hd : IsUnit A.det) {y : Y}
    (hy : y ∈ Y.basicOpen (A 0 0)) :
    ∃ (V' : Y.Opens) (hV' : V' ≤ π ⁻¹ᵁ U) (n : Low 2 → Γ(Y, V')), y ∈ V' ∧ Spans fl V' (pullCol π e hV' (uniR n)) := by
  have h₁ : Y.basicOpen (A 0 0) ≤ V := Y.basicOpen_le _
  have hunit : ∀ l : Fin (2 + 1),
      IsUnit ((A.map (resG Y h₁)).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
    intro l
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    fin_cases l
    · exact (show IsUnit (Matrix.det (n := Fin 0) _) by rw [Matrix.det_fin_zero]; exact isUnit_one).map _
    · have := CellOpen.isUnit_resG_of_le_basicOpen (A 0 0) le_rfl
      convert this using 2
      exact Matrix.det_fin_one _
    · exact hd.map _
  obtain ⟨n, M₁, hM₁t, hM₁d, hM₁⟩ := exists_lu _ 2 _ hunit
  refine ⟨_, h₁.trans hV, n, hy, ?_⟩
  have hs' : Spans fl _ (pullCol π e (h₁.trans hV) (uniR n * M₁)) := by
    have hs := hA.res h₁
    convert hs using 1
    funext j
    rw [pullCol_res, hM₁]
  haveI := M₁.invertibleOfIsUnitDet hM₁d
  have := Spans.mul_upper Y _ 2 fl _ _ M₁⁻¹ hs'
    (Matrix.blockTriangular_inv_of_blockTriangular hM₁t) (Matrix.isUnit_nonsing_inv_det _ hM₁d)
  convert this using 1
  funext j
  rw [CellOpen.sum_smul_pullCol, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hM₁d, Matrix.mul_one]

def sw (s : Bool) : Fin 2 ≃ Fin 2 := if s then Equiv.swap 0 1 else Equiv.refl _

theorem exists_uni_sw (π : Y ⟶ B) {E : B.Modules} (hE : IsVB E 2) {U : B.Opens} {e : Fin 2 → Γ(E, U)}
    (he : IsFrame e) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2) {y : Y} (hy : y ∈ π ⁻¹ᵁ U) :
    ∃ (s : Bool) (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (n : Low 2 → Γ(Y, V)),
      y ∈ V ∧ Spans fl V (pullCol π (e ∘ sw s) hV (uniR n)) := by
  have := hE.isQuasicoherent
  obtain ⟨W, hyW, v, hv⟩ := exists_spans fl y
  have hV : π ⁻¹ᵁ U ⊓ W ≤ π ⁻¹ᵁ U := inf_le_left
  obtain ⟨A, hA⟩ := CellOpen.exists_pullCol π he hV fun j => resM _ inf_le_right (v j)
  have hs : Spans fl _ (pullCol π e hV A) := by
    have := hv.res (inf_le_right : π ⁻¹ᵁ U ⊓ W ≤ W)
    rwa [funext hA] at this
  have hd := isUnit_det_of_isFrame π he hV (isFrame_of_spans hs)
  by_cases h₀ : y ∈ Y.basicOpen (A 0 0)
  · exact ⟨false, exists_uni π e hV hs hd h₀⟩
  have h₁ : y ∈ Y.basicOpen (A 1 0) := by
    by_contra h₁
    have hyV : y ∈ π ⁻¹ᵁ U ⊓ W := ⟨hy, hyW⟩
    have hu := hd.map (Y.presheaf.germ _ y hyV).hom
    rw [Y.mem_basicOpen _ _ hyV, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal] at h₀ h₁
    rw [Matrix.det_fin_two, map_sub, map_mul, map_mul] at hu
    exact (IsLocalRing.mem_maximalIdeal _).1
      (sub_mem (Ideal.mul_mem_right _ _ h₀) (Ideal.mul_mem_left _ _ h₁)) hu
  have e₁ : pullCol π (e ∘ sw true) hV (A.submatrix (Equiv.swap 0 1) id) = pullCol π e hV A := by
    funext j
    exact Equiv.sum_comp (Equiv.swap (0 : Fin 2) 1) fun l => A l j • pullbackSections π E hV (e l)
  refine ⟨true, exists_uni π _ hV (e₁ ▸ hs) ?_ h₁⟩
  rw [Matrix.det_permute]
  exact (Units.isUnit _ |>.map (Int.castRingHom _)).mul hd

def low : Low 2 := ⟨(1, 0), by decide⟩

theorem eq_low (s : Low 2) : s = low := by
  obtain ⟨⟨a, b⟩, h⟩ := s
  revert a b
  decide

theorem cos_eq (π : Y ⟶ B) (w : π ≫ q = p) {E : B.Modules} (h : Met q σ E 2) {flB : Vert.Flag E 2}
    {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2} (cE : Chart E 2) (hB : Spans flB cE.U cE.e) (s : Bool)
    {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ cE.U) (n : Low 2 → Γ(Y, W))
    (hs : Spans fl W (pullCol π (cE.e ∘ sw s) hW (uniR n))) {v : CxPts p σ → ℝ}
    (hv : CurveDens.IsCosSq (h.pull π w) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v)
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) :
    v y = LineCos.cosSq s (h.G cE (PtsOver.map π w (spMap σ) y)) (ev p σ W (n low) y) := by
  obtain ⟨t, -, ht⟩ := hs 1
  obtain ⟨m, -, hm⟩ := hB 1
  let M : Matrix (Fin 2) (Fin 2) Γ(Y, W) := if s then !![n low, 1; 1, 0] else !![1, 1; n low, 0]
  have e₀ : (fl.ι 1).app W (t ⟨0, Nat.one_pos⟩) = pullCol π cE.e hW M 0 := by
    refine (ht _).trans ?_
    change pullCol π (cE.e ∘ sw s) hW (uniR n) 0 = _
    simp only [pullCol, Fin.sum_univ_two]
    cases s
    · rfl
    · exact add_comm _ _
  have e₁ : ((Scheme.Modules.pullback π).map (flB.ι 1)).app W (pullbackSections π _ hW (m ⟨0, Nat.one_pos⟩)) =
      pullCol π cE.e hW M 1 := by
    rw [QCoh.pullback_map_app_pullbackSections, hm]
    have h₀ : M 0 1 = 1 := by cases s <;> rfl
    have h₁ : M 1 1 = 0 := by cases s <;> rfl
    simp only [pullCol, Fin.sum_univ_two, h₀, h₁, one_smul, zero_smul, add_zero]
    rfl
  have key := hv.symm W (pullbackSections π _ hW (m ⟨0, Nat.one_pos⟩)) (t ⟨0, Nat.one_pos⟩) y hy
  rw [e₀, e₁, form_pullCol π w h cE hW M hy, form_pullCol π w h cE hW M hy, form_pullCol π w h cE hW M hy] at key
  have hb : PtsOver.map π w (spMap σ) y ∈ ptsIn q σ cE.U := le_preimage_comp y.1 π hW hy
  have hG := h.posDef cE _ hb
  generalize h.G cE (PtsOver.map π w (spMap σ) y) = G at key hG ⊢
  have c₀ : (fun i => ev p σ W (M i 0) y) = LineCos.lineVec s (ev p σ W (n low) y) := by
    funext i
    cases s <;> fin_cases i <;> simp [M, LineCos.lineVec, ev_eq hy]
  have c₁ : (fun i => ev p σ W (M i 1) y) = Pi.single 0 1 := by
    funext i
    cases s <;> fin_cases i <;> simp [M, ev_eq hy]
  have hf (a b : Fin 2 → ℂ) : HermFrame.form G a b = LineCos.hform G a b := by
    rw [HermFrame.form_eq_sum, LineCos.hform]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_right_comm _ _ _
  simp only [HermFrame.chg_apply, Matrix.of_apply, c₀, c₁, hf] at key
  have h00 : LineCos.hform G (Pi.single 0 1) (Pi.single 0 1) = G 0 0 := by
    simp [LineCos.hform, Fin.sum_univ_two]
  have hp := mul_pos (LineCos.re_hform_pos hG (LineCos.lineVec_ne_zero s (ev p σ W (n low) y)))
    (LineCos.re_corner_pos hG)
  rw [LineCos.cosSq, key, h00, eq_div_iff hp.ne']
  ring

theorem exists_chart_cosSq : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (σ : k →+* ℂ) (v : CxPts p σ → ℝ),
    GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ y : CxPts p σ, ∃ (c : AlgChart p σ (d + 1)) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (s : Bool)
      (O : Set (ReciprocityTheory.L2DbarEstimates.V (d + 1))), y ∈ c.e.source ∧ IsOpen O ∧ c.e y ∈ O ∧ O ⊆ c.e.target ∧
      ContinuousOn (fun z => G (GlobalTheory.LineCos.base z)) O ∧
      ∀ z ∈ O, (G (GlobalTheory.LineCos.base z)).PosDef ∧
        v (c.e.symm z) = GlobalTheory.LineCos.cosSq s (G (GlobalTheory.LineCos.base z)) (GlobalTheory.LineCos.fib z) := by
  intro k _ B Y _ _ q p d hB _ π w E h H flB fl hfl σ v hv y
  let πσ : CxPts p σ → CxPts q σ := PtsOver.map π w (spMap σ)
  have hπ : Continuous πσ := PtsOver.continuous_map π w _
  obtain ⟨U₀, hU₀, e₀, he₀⟩ := exists_spans flB ((πσ y).1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨c₀, hc₀⟩ := (hB.atlas σ).cover (πσ y)
  obtain ⟨c, hc, hcU⟩ := exists_chart_le (d := d) c₀ hc₀ U₀ (mem_ptsIn.2 hU₀)
  have he := he₀.res hcU
  let cE : Chart E 2 := ⟨c.U, _, isFrame_of_spans he⟩
  obtain ⟨s, V, hV, n', hyV, hn'⟩ := exists_uni_sw π h.isVB cE.isFrame fl
    (y := y.1 (IsLocalRing.closedPoint ℂ)) (mem_ptsIn.1 (c.source_subset hc))
  obtain ⟨W, hW, hWa, n, hn, hs, hmax⟩ := exists_cell B Y π Unit (fun _ => 2) (fun _ => E) (fun _ => fl) hfl
    (fun _ => h.isVB) c.U c.affine (fun _ => cE.e ∘ sw s) fun _ => cE.isFrame.comp_equiv _
  have hyW : y ∈ ptsIn p σ W := mem_ptsIn.2 (hmax V hV (fun a => n' a.2) (fun _ => hn') hyV)
  obtain ⟨c', hy', hsrc, hc'⟩ := exists_chart_over π w c hW hWa n ⟨(), low⟩
    (fun ⟨_, a⟩ => by rw [eq_low a]) hn hyW
  have hO : IsOpen (πσ ⁻¹' c.e.source) := c.e.open_source.preimage hπ
  have hz : ∀ z ∈ c'.e.target ∩ c'.e.symm ⁻¹' (πσ ⁻¹' c.e.source),
      c.e.symm (WithLp.toLp 2 (LineCos.base z)) = πσ (c'.e.symm z) := fun z hz => by
    have := (hc' _ (c'.e.map_target hz.1)).2 hz.2
    rw [c'.e.right_inv hz.1] at this
    rw [this, c.e.left_inv hz.2]
  refine ⟨c', fun b => (h.met σ).G cE (c.e.symm (WithLp.toLp 2 b)), s,
    c'.e.target ∩ c'.e.symm ⁻¹' (πσ ⁻¹' c.e.source), hy', ChartGlue.isOpen_over c'.e hO,
    ChartGlue.mem_over c'.e hy' hc, Set.inter_subset_left, ?_, fun z hz' => ?_⟩
  · refine ContinuousOn.congr (f := fun z => (h.met σ).G cE (πσ (c'.e.symm z))) (fun z hz' => ?_)
      fun z hz' => by simp only [hz z hz']
    have h₁ : ContinuousAt ((h.met σ).G cE) (πσ (c'.e.symm z)) :=
      continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => (H σ cE _ (c.source_subset hz'.2) a b).continuousAt
    exact (h₁.comp (f := fun z => πσ (c'.e.symm z))
      (hπ.continuousAt.comp (c'.e.continuousAt_symm hz'.1))).continuousWithinAt
  · have h₁ := (hc' _ (c'.e.map_target hz'.1)).1
    rw [c'.e.right_inv hz'.1] at h₁
    simp only [hz z hz', h₁]
    exact ⟨(h.met σ).posDef cE _ (c.source_subset hz'.2),
      cos_eq π w (h.met σ) cE he s hW (fun a => n ⟨(), a⟩) (hs ()) hv (hsrc (c'.e.map_target hz'.1))⟩

end GlobalTheory.LineChart

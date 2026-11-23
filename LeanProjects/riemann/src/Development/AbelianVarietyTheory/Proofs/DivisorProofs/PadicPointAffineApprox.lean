import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartValues

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Pad.Guard GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.FlagEmb (StabBasis Tn)

namespace GlobalTheory.CovHt.Link.SemiCont

theorem exists_perturb {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) C) (hA : Function.Injective A.mulVec) :
    ∃ η : ℝ, 0 < η ∧ ∀ A' : Matrix (Fin n) (Fin m) C, (∀ j i, ‖A' j i - A j i‖ < η) →
      ∀ cf, (∀ j, ‖A'.mulVec cf j‖ ≤ 1) ↔ ∀ j, ‖A.mulVec cf j‖ ≤ 1 := by
  obtain ⟨B, hB⟩ := exists_left_inv A hA
  set K : ℝ := ∑ i, ∑ j, ‖B i j‖ with hK
  have hK0 : 0 ≤ K := by positivity
  have h1 : ∀ cf : Fin m → C, ∑ i, ‖cf i‖ ≤ K * ‖A.mulVec cf‖ := fun cf => by
    rw [hK, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h8 : cf i = ∑ j, B i j * A.mulVec cf j := by
      have := congrFun (Matrix.mulVec_mulVec cf B A) i
      rw [hB, Matrix.one_mulVec] at this
      exact this.symm
    rw [Finset.sum_mul]
    refine (le_of_eq (congrArg norm h8)).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm _ j) (norm_nonneg _)
  refine ⟨(2 * (K + 1))⁻¹, by positivity, fun A' hA' cf => ?_⟩
  have h2 : ∀ j, ‖A'.mulVec cf j - A.mulVec cf j‖ ≤ ‖A.mulVec cf‖ / 2 := fun j => by
    have e : A'.mulVec cf j - A.mulVec cf j = ∑ i, (A' j i - A j i) * cf i := by
      simp only [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
    have h3 : ‖A'.mulVec cf j - A.mulVec cf j‖ ≤ (2 * (K + 1))⁻¹ * ∑ i, ‖cf i‖ := by
      rw [e, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hA' j i).le (norm_nonneg _)
    refine h3.trans ?_
    rw [inv_mul_le_iff₀ (by positivity)]
    nlinarith [h1 cf, norm_nonneg (A.mulVec cf)]
  constructor
  · intro h
    have h4 : ‖A.mulVec cf‖ ≤ max 1 (‖A.mulVec cf‖ / 2) := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
      have e : A.mulVec cf j = A'.mulVec cf j + -(A'.mulVec cf j - A.mulVec cf j) := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (h j) ((norm_neg _).trans_le (h2 j)))
    intro j
    refine (norm_le_pi_norm _ j).trans ?_
    rcases le_max_iff.1 h4 with h5 | h5
    · exact h5
    · linarith
  · intro h j
    have h4 : ‖A.mulVec cf‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 h
    have e : A'.mulVec cf j = A.mulVec cf j + (A'.mulVec cf j - A.mulVec cf j) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h j) ((h2 j).trans (by linarith)))

theorem exists_generators (R : Type) [CommRing R] (h : (Int.castRingHom R).FiniteType) :
    ∃ G : Finset R, ∀ (C : Type) [NormedField C] [IsUltrametricDist C] (χ : R →+* C),
      (∀ g ∈ G, χ g ∈ intO C) → ∀ a, χ a ∈ intO C := by
  have h' : Algebra.FiniteType ℤ R := by
    have := RingHom.finiteType_algebraMap (A := ℤ) (B := R)
    rw [← this]
    exact h
  obtain ⟨G, hG⟩ := h'.out
  refine ⟨G, fun C _ _ χ hχ a => ?_⟩
  have h1 : Subring.closure (G : Set R) ≤ (intO C).comap χ := Subring.closure_le.2 fun g hg => hχ g hg
  have h2 : a ∈ Algebra.adjoin ℤ (G : Set R) := hG ▸ Algebra.mem_top
  rw [Algebra.adjoin_int] at h2
  exact h1 h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Norm

variable {X : Scheme.{0}} {t : SAB H X} {R₀ R C : Type} [CommRing R₀] [CommRing R] [NontriviallyNormedField C]
  [IsUltrametricDist C] {x₀ : Sp R₀ ⟶ X} {n m : ℕ} {v : Fin n → Tn t R₀} {ρ : R₀ →+* R} {u : Fin m → Tn t R}

theorem grNorm_eq_of_coord (hX : X.IsSeparated) (hv : StabBasis t x₀ v) {A : Matrix (Fin n) (Fin m) R}
    (hA : ∀ i, IsCombAtG t (spMap ρ ≫ x₀) (fun j => spMap (dualMap ρ) ≫ v j) (fun j => A j i) (u i))
    (ε : R →+* C) (hε : ∀ a, ε (ρ a) ∈ intO C) (i : Fin m) :
    grNorm t (spMap ε ≫ spMap ρ ≫ x₀) (latDR t (spMap ε ≫ spMap ρ ≫ x₀)) (fun l => spMap (dualMap ε) ≫ u l) i =
      sInf {r | ∃ cf : Fin m → C, cf i ≠ 0 ∧ (∀ k, i < k → cf k = 0) ∧ (∀ j, ‖(A.map ε).mulVec cf j‖ ≤ 1) ∧
        r = ‖cf i‖⁻¹} := by
  let φ : R₀ →+* ↥(intO C) := (ε.comp ρ).codRestrict _ hε
  have hφ : (intO C).subtype.comp φ = ε.comp ρ := rfl
  have hx : spMap (intO C).subtype ≫ spMap φ ≫ x₀ = spMap ε ≫ spMap ρ ≫ x₀ := by
    rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp, hφ]
  have hv' : ∀ j, IsTanAtG t (spMap ε ≫ spMap ρ ≫ x₀) (spMap (dualMap ε) ≫ spMap (dualMap ρ) ≫ v j) := fun j =>
    GlobalTheory.FactorDepth.isTanAtG_map t ε (GlobalTheory.FactorDepth.isTanAtG_map t ρ (hv.1 j))
  have hA' := fun i => GlobalTheory.LatDRFree.comb_map t ε (hA i)
  have lat : ∀ cf w, IsCombAtG t (spMap ε ≫ spMap ρ ≫ x₀) (fun l => spMap (dualMap ε) ≫ u l) cf w →
      (w ∈ latDR t (spMap ε ≫ spMap ρ ≫ x₀) ↔ ∀ j, ‖(A.map ε).mulVec cf j‖ ≤ 1) := fun cf w hw => by
    have h1 := tanLinG _ hv' _ (A.map ε) cf w hA' hw
    rw [← hx] at h1 ⊢
    simp only [GlobalTheory.HTPres.bc_bc, ← hφ] at h1
    exact GlobalTheory.HTPres.mem_latDR_iff t hX x₀ ⟨hv.1, hv.2⟩ C φ _ w h1
  refine congrArg sInf (Set.ext fun s => exists_congr fun cf => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_left fun _ => ⟨?_, fun hb => ?_⟩)
  · rintro ⟨w, hw, hc⟩
    exact (lat cf w hc).1 hw
  · obtain ⟨w, -, hc⟩ := exists_comb (fun l => comb_tan hv' (hA' l)) cf
    exact ⟨w, (lat cf w hc).2 hb, hc⟩

theorem exists_grNorm_eq (hX : X.IsSeparated) (hv : StabBasis t x₀ v) (hu : ∀ i, IsTanAtG t (spMap ρ ≫ x₀) (u i))
    (ε : R →+* C) (hε : ∀ a, ε (ρ a) ∈ intO C)
    (hi : Indep t (spMap ε ≫ spMap ρ ≫ x₀) fun l => spMap (dualMap ε) ≫ u l) :
    ∃ (T : Finset R) (η : ℝ), 0 < η ∧ ∀ ε' : R →+* C, (∀ a, ε' (ρ a) ∈ intO C) → (∀ h ∈ T, ‖ε' h - ε h‖ < η) → ∀ i,
      grNorm t (spMap ε' ≫ spMap ρ ≫ x₀) (latDR t (spMap ε' ≫ spMap ρ ≫ x₀)) (fun l => spMap (dualMap ε') ≫ u l) i =
        grNorm t (spMap ε ≫ spMap ρ ≫ x₀) (latDR t (spMap ε ≫ spMap ρ ≫ x₀)) (fun l => spMap (dualMap ε) ≫ u l) i := by
  classical
  choose a ha using fun i => (hv.2 R ρ _ (hu i)).exists
  let A : Matrix (Fin n) (Fin m) R := fun j i => a i j
  have hb := GlobalTheory.HTPres.isTanBasis_map t (GlobalTheory.HTPres.isTanBasis_map t ⟨hv.1, hv.2⟩ ρ) ε
  have hb' := (GlobalTheory.HTPres.isTanBasis_map t ⟨hv.1, hv.2⟩ ρ).2 C ε
  obtain ⟨η, hη, hp⟩ := exists_perturb (A.map ε)
    ((indep_iff hb.1 (indep_of_basis hb.1 hb') (A.map ε) fun i => GlobalTheory.LatDRFree.comb_map t ε (ha i)).1 hi)
  refine ⟨Finset.univ.image fun q : Fin n × Fin m => A q.1 q.2, η, hη, fun ε' hε' hc i => ?_⟩
  rw [grNorm_eq_of_coord hX hv (A := A) ha ε' hε', grNorm_eq_of_coord hX hv (A := A) ha ε hε]
  simp only [hp (A.map ε') fun j i => hc _ (Finset.mem_image_of_mem _ (Finset.mem_univ (j, i)))]

end Norm

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem eq_of_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {R : Type} [CommRing R]
    {a b : Γ(X, U) →+* R} (h : spMap a ≫ hU.fromSpec = spMap b ≫ hU.fromSpec) : a = b :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono hU.fromSpec).1 h))

section Frames

variable {O : Type} [CommRing O] {β : O →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

attribute [local instance] Over.cartesianMonoidalCategory in
open GlobalTheory.FactorDepth in

theorem indep_map {R K : Type} [CommRing R] [CommRing K] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x)
    (ψ : R →+* K) (τ : E →+* ℂ) : Indep Z.t (spMap ψ ≫ x) fun i => spMap (dualMap ψ) ≫ f.v τ i := by
  obtain ⟨g, hg⟩ := f.exists_isMap ψ rfl rfl
  rw [← funext (hg τ)]
  intro cf cf' w h1 h2
  refine (g.basis τ w (comb_tan (g.tan τ) h1) fun a => ?_).unique h1 h2
  rw [← (isCombAtG_iff Z.t _ (fun j => ovT (g.tan τ j)) _ _).1 h1]
  have := Z.t.act.hom a
  exact congrArg (fun f => f.left) (combT_eig _ (fun j => ovT (g.tan τ j)) (Z.t.act.act a) _
    (fun j => Over.OverMorphism.ext (g.eig τ j a)) cf)

theorem exists_tri {R K : Type} [CommRing R] [Field K] {ι : R →+* K} (hι : Function.Injective ι) {φ₁ φ : c.F →+* R}
    {x : Sp R ⟶ Z.X} {f₁ : EigFrame Z φ₁ x} {f : EigFrame Z φ x} {φ' : c.F →+* K} {x' : Sp K ⟶ Z.X}
    {g : EigFrame Z φ' x'} {t₁ t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ} (a₁ : f₁.Tri ι g t₁) (a : f.Tri ι g t) :
    ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Rˣ, (∀ τ i, t₁ τ i = t τ i * Units.map ι.toMonoidHom (u τ i)) ∧
      ∀ τ i, ∃ cf : Fin (Dw.mult τ) → R, cf i = u τ i ∧ (∀ k, i < k → cf k = 0) ∧
        IsCombAtG Z.t x (f₁.v τ) cf (f.v τ i) := by
  obtain rfl : φ₁ = φ := RingHom.ext fun x => hι ((RingHom.congr_fun a₁.2.1 x).symm.trans (RingHom.congr_fun a.2.1 x))
  obtain ⟨k₁, hk₁⟩ := f₁.exists_isMap _ a.2.1 a.1
  obtain ⟨k, hk⟩ := f.exists_isMap _ a.2.1 a.1
  have e1 (τ i d) : k₁.co g τ d i = ∑ j, k.co g τ j i * ι (f₁.co f τ d j) := by
    rw [← k₁.co_mul k, hk₁.co τ hk a.1, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hM (τ d i) (h : i < d) : f₁.co f τ d i = 0 := hι ((CoordUniq.tri_of_mul
    (M := fun i a => ι (f₁.co f τ a i)) (fun i a => (a₁.co τ hk₁).1 a i)
    (fun i a' => (a.co τ hk).1 a' i) (fun i => (a.co τ hk).2 i ▸ (t τ i).ne_zero) (e1 τ) i d h).trans (map_zero _).symm)
  have hu (τ i) : IsUnit (f₁.co f τ i i) := by
    have := f₁.isUnit_det_co f τ
    rw [Matrix.det_of_upperTriangular (M := f₁.co f τ) fun _ _ h => hM τ _ _ h] at this
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => f₁.co f τ i i) (Finset.mem_univ i)) this
  refine ⟨fun τ i => (hu τ i).unit, fun τ i => Units.ext ?_,
    fun τ i => ⟨fun a => f₁.co f τ a i, rfl, fun k hk => hM τ k i hk, f₁.co_spec f τ i⟩⟩
  rw [← (a₁.co τ hk₁).2, e1, Units.val_mul, ← (a.co τ hk).2]
  exact CoordUniq.diag_of_mul (M := fun i a => ι (f₁.co f τ a i))
    (fun i a' => (a.co τ hk).1 a' i) (fun i a h => by simp only [hM τ a i h, map_zero]) i

end Frames

section Model

variable (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) {C : Type} [NontriviallyNormedField C]
  [IsUltrametricDist C]

theorem exists_grNorm_locConst {Y : Scheme.{0}} (j : Y ⟶ Z.X) (x : Sp C ⟶ Y) :
    ∃ W₀ : Y.Opens, below x ∈ W₀ ∧ ∀ (W : Y.Opens) (hW : IsAffineOpen W), W ≤ W₀ → ∀ ε : Γ(Y, W) →+* C,
      x = spMap ε ≫ hW.fromSpec → ∀ (φ : c.F →+* Γ(Y, W)) (xW : Sp Γ(Y, W) ⟶ Z.X), xW = hW.fromSpec ≫ j →
      ∀ f : EigFrame Z φ xW, ∃ (T : Finset Γ(Y, W)) (η : ℝ), 0 < η ∧ ∀ ε' : Γ(Y, W) →+* C,
        (∀ h ∈ T, ‖ε' h - ε h‖ < η) → ∀ τ i,
          grNorm Z.t (spMap ε' ≫ xW) (latDR Z.t (spMap ε' ≫ xW)) (fun l => spMap (dualMap ε') ≫ f.v τ l) i =
            grNorm Z.t (spMap ε ≫ xW) (latDR Z.t (spMap ε ≫ xW)) (fun l => spMap (dualMap ε) ≫ f.v τ l) i := by
  classical
  have hp : IsProper Z.s := projProper _ _ _ Z.proj
  have hX : Z.X.IsSeparated := by
    constructor
    rw [← terminal.comp_from Z.s]
    infer_instance
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  have := GlobalTheory.LatDRFree.intO_isLocalRing C
  obtain ⟨xO, hxO, -⟩ := existsUnique_ext Z (x ≫ j)
  obtain ⟨U, n, v, hU, hv⟩ := GlobalTheory.FlagEmb.Stab.exists_stabBasis E H Z.X Z.t (xO (IsLocalRing.closedPoint ↥(intO C)))
  have hle : ⊤ ≤ xO ⁻¹ᵁ U.1 := fun y _ =>
    ((IsLocalRing.specializes_closedPoint y).map xO.continuous).mem_open U.1.isOpen hU
  obtain ⟨χ, hχ⟩ := GlobalTheory.FlagEmb.LineNorm.exists_fromSpec U.2 xO hle
  have hUa : IsAffineOpen U.1 := U.2
  have hft : (Int.castRingHom Γ(Z.X, U.1)).FiniteType := by
    obtain ⟨α, hα⟩ := GlobalTheory.FlagEmb.LineNorm.exists_spMap' (A := 𝓞 c.F) (B := Γ(Z.X, U.1)) (hUa.fromSpec ≫ Z.s)
    have h1 : LocallyOfFiniteType (spMap α) := hα ▸ (inferInstance : LocallyOfFiniteType (hUa.fromSpec ≫ Z.s))
    have h2 : α.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h1
    have h3 : (algebraMap ℤ (𝓞 c.F)).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
    exact (RingHom.ext_int (α.comp (algebraMap ℤ (𝓞 c.F))) (Int.castRingHom _)) ▸ h2.comp h3
  obtain ⟨G, hG⟩ := exists_generators _ hft
  refine ⟨j ⁻¹ᵁ U.1, ?_, fun W hW hWle ε hε φ xW hxW f => ?_⟩
  · show (x ≫ j) _ ∈ U.1
    rw [← hxO]
    exact hle (Set.mem_univ _)
  let ρ : Γ(Z.X, U.1) →+* Γ(Y, W) := (j.appLE U.1 W hWle).hom
  have hρ : spMap ρ ≫ (show Sp Γ(Z.X, U.1) ⟶ Z.X from U.2.fromSpec) = xW :=
    (IsAffineOpen.SpecMap_appLE_fromSpec j U.2 hW hWle).trans hxW.symm
  have h1 : spMap (ε.comp ρ) ≫ (show Sp Γ(Z.X, U.1) ⟶ Z.X from U.2.fromSpec) =
      spMap ((intO C).subtype.comp χ) ≫ (show Sp Γ(Z.X, U.1) ⟶ Z.X from U.2.fromSpec) := by
    rw [← sp_comp, ← sp_comp, Category.assoc, Category.assoc, hρ, hxW]
    refine Eq.trans ?_ (hxO.symm.trans (congrArg _ hχ.symm))
    rw [hε]
    exact (Category.assoc _ _ _).symm
  have h2 : ε.comp ρ = (intO C).subtype.comp χ :=
    eq_of_fromSpec hUa h1
  have hint : ∀ a, ε (ρ a) ∈ intO C := fun a => (RingHom.congr_fun h2 a) ▸ (χ a).2
  clear hxW
  subst hρ
  choose T η hη hT using fun τ => exists_grNorm_eq hX hv (f.tan τ) ε hint (indep_map f ε τ)
  obtain ⟨η₀, h0, h1, h2⟩ : ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ ∀ τ, η₀ ≤ η τ := by
    obtain ⟨τ₀, hτ₀⟩ := Finite.exists_min η
    exact ⟨min 1 (η τ₀), lt_min one_pos (hη τ₀), min_le_left _ _, fun τ => (min_le_right _ _).trans (hτ₀ τ)⟩
  refine ⟨G.image ρ ∪ Finset.univ.biUnion T, η₀, h0, fun ε' hc τ => hT τ ε' (hG C (ε'.comp ρ) fun g hg => ?_)
    fun h hh => (hc h (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨τ, Finset.mem_univ _, hh⟩))).trans_le (h2 τ)⟩
  have h3 : ε' (ρ g) - ε (ρ g) ∈ intO C :=
    ((hc _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hg))).trans_le h1).le
  simpa using (intO C).add_mem h3 (hint g)

end Model

section Formula

variable {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)} {F : Type} [Field F] {e : F ≃+* c.F}
  (Y : FlagCpt Z e)

theorem exists_formula (n : Letter Dw → ℤ) (f : Y.Y.Fn) (hf : ∀ y, (divOf Y n).RegularAt y f) (ξ : Y.Y.X)
    (W₀ : Y.Y.X.Opens) (hξ : ξ ∈ W₀) :
    ∃ (W : Y.Y.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(Y.Y.X, W)) (xW : Sp Γ(Y.Y.X, W) ⟶ Z.X)
      (fW : EigFrame Z φ xW) (r : Γ(Y.Y.X, W)), ξ ∈ W ∧ W ≤ W₀ ∧ xW = hW.fromSpec ≫ Y.π ≫ genι Z ∧
      ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (y : Y.Y.X) (ψ : Y.Y.X.presheaf.stalk y →+* C)
        (ε : Γ(Y.Y.X, W) →+* C), y ∈ W → spMap ψ ≫ stalkPt Y.Y y = spMap ε ≫ hW.fromSpec →
        ∀ (φ' : c.F →+* Y.Y.X.presheaf.stalk y) (g : EigFrame Z φ' (stalkPt Y.Y y ≫ Y.π ≫ genι Z))
          (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ),
          g.Tri (algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField) Y.f0 t →
        ∃ a : Y.Y.X.presheaf.stalk y, algebraMap _ Y.Y.X.functionField a =
            f * ((∏ z : Letter Dw, t z.1 z.2 ^ n z : Y.Y.Fnˣ) : Y.Y.Fn) ∧
          ‖ψ a‖ * Real.exp (∑ z : Letter Dw, (n z : ℝ) * Real.log (grNorm Z.t
            (spMap ψ ≫ stalkPt Y.Y y ≫ Y.π ≫ genι Z) (latDR Z.t (spMap ψ ≫ stalkPt Y.Y y ≫ Y.π ≫ genι Z))
            (fun i => spMap (dualMap ψ) ≫ g.v z.1 i) z.2)) =
        ‖ε r‖ * Real.exp (∑ z : Letter Dw, (n z : ℝ) * Real.log (grNorm Z.t (spMap ε ≫ xW)
          (latDR Z.t (spMap ε ≫ xW)) (fun i => spMap (dualMap ε) ≫ fW.v z.1 i) z.2)) := by
  obtain ⟨W, hW, hy, φ, fr, t₁, hle, -, hT, hE⟩ := Spread.exists_frame_nhds E H Dw l Xo c _ _ Z F e Y ξ W₀ hξ
  have hD : ∀ y ∈ W, (divOf Y n).IsEqn y (∏ z : Letter Dw, t₁ z.1 z.2 ^ n z) := fun y hy => by
    have hs : ∀ s : Finset (Letter Dw), (∑ z ∈ s, n z • Y.gr z.1 z.2).IsEqn y (∏ z ∈ s, t₁ z.1 z.2 ^ n z) := fun s => by
      classical
      induction s using Finset.induction_on with
      | empty => simpa using CartierDiv.isEqn_zero y
      | insert z s hz ih => rw [Finset.sum_insert hz, Finset.prod_insert hz]; exact ((hE y hy _ _).zsmul _).add ih
    exact hs Finset.univ
  obtain ⟨r, hr⟩ := exists_fnOf_eq (gen_mem hy) fun y hy => (hD y hy).regularAt_iff.1 (hf y)
  refine ⟨W, hW, φ, _, fr, r, hy, hle, Category.assoc _ _ _, fun C _ _ y ψ ε hb hx φ' g t hT' => ?_⟩
  let gm : Γ(Y.Y.X, W) →+* Y.Y.X.presheaf.stalk y := (Y.Y.X.presheaf.germ W y hb).hom
  have hgm : spMap gm ≫ (show Sp Γ(Y.Y.X, W) ⟶ Y.Y.X from hW.fromSpec) = stalkPt Y.Y y :=
    Spread.spMap_germ hW hb
  have hψ : ψ.comp gm = ε := eq_of_fromSpec hW (by
    refine Eq.trans ?_ hx
    rw [← hgm, ← Category.assoc, sp_comp])
  have hι : (algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField).comp gm = fnOf W (gen_mem hy) :=
    RingHom.ext fun a => algebraMap_germ hb a
  have hx₁ : stalkPt Y.Y y ≫ Y.π ≫ genι Z =
      spMap gm ≫ ((show Sp Γ(Y.Y.X, W) ⟶ Y.Y.X from hW.fromSpec) ≫ Y.π) ≫ genι Z := by
    rw [← hgm]; simp only [Category.assoc]
  obtain ⟨g₁, hg₁⟩ := fr.exists_isMap gm rfl hx₁
  have hT₁ : g₁.Tri (algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField) Y.f0 t₁ := by
    rw [← hι] at hT
    exact ⟨hT'.1, hT.2.1, fun τ i => by simpa only [hg₁ τ, GlobalTheory.HTPres.bc_bc] using hT.2.2 τ i⟩
  obtain ⟨u, hu, hc⟩ := exists_tri (IsFractionRing.injective _ _) hT₁ hT'
  have hx₂ : spMap ψ ≫ stalkPt Y.Y y ≫ Y.π ≫ genι Z =
      spMap ε ≫ ((show Sp Γ(Y.Y.X, W) ⟶ Y.Y.X from hW.fromSpec) ≫ Y.π) ≫ genι Z := by
    rw [hx₁, ← Category.assoc, sp_comp, hψ]
  have hv : ∀ τ, (fun i => spMap (dualMap ψ) ≫ g₁.v τ i) = fun i => spMap (dualMap ε) ≫ fr.v τ i := fun τ => by
    funext i
    rw [hg₁ τ i, ← hψ]
    exact GlobalTheory.HTPres.bc_bc _ _ _ _
  have hu0 : ∀ τ i, ψ (u τ i) ≠ 0 := fun τ i => ((u τ i).isUnit.map ψ).ne_zero
  have hn : ∀ z : Letter Dw, Real.log (grNorm Z.t (spMap ψ ≫ stalkPt Y.Y y ≫ Y.π ≫ genι Z)
      (latDR Z.t (spMap ψ ≫ stalkPt Y.Y y ≫ Y.π ≫ genι Z)) (fun i => spMap (dualMap ψ) ≫ g.v z.1 i) z.2) =
      Real.log ‖ψ (u z.1 z.2)‖ + Real.log (grNorm Z.t (spMap ψ ≫ stalkPt Y.Y y ≫ Y.π ≫ genι Z)
        (latDR Z.t (spMap ψ ≫ stalkPt Y.Y y ≫ Y.π ≫ genι Z))
        (fun i => spMap (dualMap ψ) ≫ g₁.v z.1 i) z.2) := fun z => by
    have htan := fun k => GlobalTheory.FactorDepth.isTanAtG_map _ ψ (g₁.tan z.1 k)
    rw [grNorm_tri (d := fun k => ψ (u z.1 k)) htan (hu0 z.1) (fun k => ?_) z.2,
      Real.log_mul (norm_ne_zero_iff.2 (hu0 _ _)) (grNorm_latDR_pos Z _ htan (indep_map g₁ ψ z.1) z.2).2.ne']
    obtain ⟨cf, e1, e2, e3⟩ := hc z.1 k
    exact ⟨fun a => ψ (cf a), congrArg ψ e1, fun a ha => (congrArg ψ (e2 a ha)).trans (map_zero ψ),
      GlobalTheory.LatDRFree.comb_map _ ψ e3⟩
  have hf' : f * ((∏ z : Letter Dw, t z.1 z.2 ^ n z : Y.Y.Fnˣ) : Y.Y.Fn) =
      algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField
        (gm r * ((∏ z : Letter Dw, u z.1 z.2 ^ n z)⁻¹ : (Y.Y.X.presheaf.stalk y)ˣ)) := by
    rw [map_mul, ← RingHom.comp_apply, hι, hr, map_units_inv, eq_mul_inv_iff_mul_eq₀ ((Units.isUnit _).map _).ne_zero]
    simp only [hu, mul_zpow, Finset.prod_mul_distrib, ← map_zpow, ← map_prod, Units.val_mul, _root_.mul_assoc]
    rfl
  have hp : ‖ψ ((∏ z : Letter Dw, u z.1 z.2 ^ n z : (Y.Y.X.presheaf.stalk y)ˣ) : _)‖ =
      Real.exp (∑ z : Letter Dw, (n z : ℝ) * Real.log ‖ψ (u z.1 z.2)‖) := by
    have e2 : ψ ((∏ z : Letter Dw, u z.1 z.2 ^ n z : (Y.Y.X.presheaf.stalk y)ˣ) : _) =
        ∏ z : Letter Dw, ψ (u z.1 z.2) ^ n z := by
      refine (congrArg Units.val (map_prod (Units.map ψ.toMonoidHom) _ _)).trans ?_
      simp only [map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val]
      rfl
    rw [e2, norm_prod, Real.exp_sum]
    refine Finset.prod_congr rfl fun z _ => ?_
    rw [← Real.log_zpow, Real.exp_log (zpow_pos (norm_pos_iff.2 (hu0 _ _)) _), norm_zpow]
  refine ⟨_, hf'.symm, ?_⟩
  rw [map_mul, ← RingHom.comp_apply, hψ, map_units_inv, norm_mul, norm_inv, hp]
  simp only [hn, mul_add, Finset.sum_add_distrib, Real.exp_add, hv]
  rw [hx₂, _root_.mul_assoc, inv_mul_cancel_left₀ (Real.exp_pos _).ne']

end Formula

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.AllWt in

theorem sum_drSym {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} (la : AllWt.Weight S.Dw) (G : Sym D.host.E → ℝ) :
    ((drSym la).sum fun a n => (n : ℝ) * G a) =
      ∑ z : Letter S.Dw, (expo S.Dw (drSym la) z : ℝ) * G (fun _ => false, none, .inl (z.1, z.2)) := by
  rw [expo_drSym, drSym, ← Finsupp.sum_finset_sum_index (by simp) (by simp [add_mul])]
  exact Finset.sum_congr rfl fun z _ => Finsupp.sum_single_index (by simp)

set_option maxHeartbeats 1600000 in
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.AllWt in

theorem drAt_lowerSemicont : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag)
    (k : s.Comp) (la : AllWt.Weight S.Dw) (f : (Φ.C k).Y.Fn), f ∈ (Φ.C k).Y.H0 ((Φ.C k).Lw la) →
    ∀ (p : ℕ) [Fact p.Prime] (x : Sp ℂ_[p] ⟶ (Φ.C k).Y.X) (δ : ℝ), 0 < δ →
    ∃ (U : (Φ.C k).Y.X.Opens) (hU : IsAffineOpen U) (ε : Γ((Φ.C k).Y.X, U) →+* ℂ_[p]), x = spMap ε ≫ hU.fromSpec ∧
      ∃ (t : Finset Γ((Φ.C k).Y.X, U)) (η : ℝ), 0 < η ∧ ∀ ε' : Γ((Φ.C k).Y.X, U) →+* ℂ_[p],
        (∀ h ∈ t, ‖ε' h - ε h‖ < η) → drAt Φ k la p x f - δ < drAt Φ k la p (spMap ε' ≫ hU.fromSpec) f := by
  intro D A N j S κ s Φ k la f hf p _ x δ hδ
  classical
  obtain ⟨W₀, hx0, hlc⟩ := exists_grNorm_locConst s.T.Z ((Φ.C k).π ≫ genι s.T.Z) x
  obtain ⟨W, hW, φ, xW, fW, r, hξ, hle, hxW, hform⟩ := exists_formula (Φ.C k) (expo S.Dw (drSym la)) f
    (by rw [divOf_drSym]; exact CartierDiv.mem_sections.1 hf) (below x) W₀ hx0
  have key : ∀ (z : Sp ℂ_[p] ⟶ (Φ.C k).Y.X) (ε : Γ((Φ.C k).Y.X, W) →+* ℂ_[p]), z = spMap ε ≫ hW.fromSpec →
      drAt Φ k la p z f = ‖ε r‖ * Real.exp (∑ b : Letter S.Dw, (expo S.Dw (drSym la) b : ℝ) *
        Real.log (grNorm s.T.Z.t (spMap ε ≫ xW) (latDR s.T.Z.t (spMap ε ≫ xW))
          (fun i => spMap (dualMap ε) ≫ fW.v b.1 i) b.2)) := fun z ε hz => by
    have hb : below z ∈ W := by
      have : below z ∈ Set.range hW.fromSpec := by rw [hz]; exact ⟨_, rfl⟩
      rwa [hW.range_fromSpec] at this
    obtain ⟨a, ha, he⟩ := hform ℂ_[p] (below z) (Scheme.stalkClosedPointTo z).hom ε hb
      ((Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).trans hz) _ _ _
      ((Φ.C k).gr_spec (below z)).choose_spec.choose_spec.choose_spec.1
    rw [← he, drAt, ← ha, Base.valAt_stalk, sum_drSym]
    refine congrArg (fun q => _ * Real.exp q) (Finset.sum_congr rfl fun b _ => congrArg _ ?_)
    simp only [lnStep, dif_pos b.2.isLt, lat, Bool.false_eq_true, false_and, if_false, sub_zero]
  obtain ⟨ε, hε⟩ := GlobalTheory.FlagEmb.LineNorm.exists_fromSpec hW x fun y _ => by
    rw [Subsingleton.elim y (IsLocalRing.closedPoint ℂ_[p])]
    exact hξ
  obtain ⟨T, η, hη, hc⟩ := hlc W hW hle ε hε.symm φ xW hxW fW
  have hx := key x ε hε.symm
  refine ⟨W, hW, ε, hε.symm, ?_⟩
  by_cases hr : ε r = 0
  · refine ⟨T, η, hη, fun ε' _ => ?_⟩
    rw [hr, norm_zero, zero_mul] at hx
    linarith [drAt_nonneg Φ k la p (spMap ε' ≫ hW.fromSpec) f]
  · refine ⟨insert r T, min η ‖ε r‖, lt_min hη (norm_pos_iff.2 hr), fun ε' hε' => ?_⟩
    have hgr := hc ε' fun h hh => (hε' h (Finset.mem_insert_of_mem hh)).trans_le (min_le_left _ _)
    have hnr : ‖ε' r‖ = ‖ε r‖ := by
      have hlt : ‖ε' r - ε r‖ < ‖ε r‖ := (hε' r (Finset.mem_insert_self _ _)).trans_le (min_le_right _ _)
      have e : ε' r = ε r + (ε' r - ε r) := by ring
      rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]
    have e1 := key _ ε' rfl
    simp only [hnr, hgr] at e1
    linarith

end GlobalTheory.CovHt.Link.SemiCont

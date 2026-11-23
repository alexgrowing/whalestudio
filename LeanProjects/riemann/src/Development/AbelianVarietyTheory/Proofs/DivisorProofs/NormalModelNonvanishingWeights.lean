import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveSubbundleCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedGraphClosure

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)

open GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier
open GlobalTheory.TrueGeo.SmallSec (fnMap fnMap_fnOf)

namespace GlobalTheory.CorankOneNormal

theorem exists_modification_sections {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (B : GlobalTheory.Vert.Model O) [hn : GlobalTheory.IsNormalScheme B.X] {U : B.X.Opens} (hU : genericPoint B.X ∈ U) {N : ℕ}
    (r : Fin (N + 1) → Γ(B.X, U)) (i₀ : Fin (N + 1)) (hr : r i₀ = 1) :
    ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (hη : f.f (genericPoint B'.X) = genericPoint B.X),
      GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ ∀ y : B'.X, ∃ i, fnOf U hU (r i) ≠ 0 ∧ ∀ j, ∃ g, RegAt y g ∧
        g * fnMap f.f (specializes_of_eq hη) (fnOf U hU (r i)) = fnMap f.f (specializes_of_eq hη) (fnOf U hU (r j)) := by
  have : Nonempty U := ⟨⟨_, hU⟩⟩
  have hP : IsProjOver (PSpace.str O N) := ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  have w : ProjSpace.ofCoords B.str U i₀ r ≫ PSpace.str O N = U.ι ≫ B.str ≫ spMap (RingHom.id O) := by
    rw [ProjSpace.ofCoords_str]
    simp [spMap]
  obtain ⟨X', f₁, q, c, hproj, hnorm, hflat, hpb, hdense, hc₂, -⟩ :=
    GlobalTheory.GraphClosure.exists_normalised_graph_closure O O (RingHom.id O) B.X (PSpace O N) B.str (PSpace.str O N) U
      (ProjSpace.ofCoords B.str U i₀ r) B.isProjOver hP (GlobalTheory.IsNormalScheme.pred B.X) inferInstance w
  have hN : GlobalTheory.IsNormalScheme X' := GlobalTheory.IsNormalScheme.of_pred hnorm
  have : IsOpenImmersion c := MorphismProperty.of_isPullback hpb.flip (inferInstance : IsOpenImmersion U.ι)
  have hc₁ : c ≫ f₁ = U.ι := by simpa using hpb.w
  have : IsReduced X' := isReduced_of_isReduced_stalk X'
  have : IrreducibleSpace X' := by
    have h1 : IsIrreducible (Set.range c) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image c c.continuous.continuousOn
    have h2 := h1.closure
    rw [hdense.closure_eq] at h2
    exact (irreducibleSpace_def _).2 h2
  have : IsIntegral X' := isIntegral_of_irreducibleSpace_of_isReduced X'
  let B' : GlobalTheory.Vert.Model O := { X := X', str := f₁ ≫ B.str, isProjOver := hproj }
  have : IsProper f₁ := GlobalTheory.Vert.Model.isProper_of_comp_str (Z := B) (Z₁ := B') (f := f₁) rfl
  have hcη : c (genericPoint U) = genericPoint X' := genericPoint_eq_of_isOpenImmersion c
  have hη : f₁ (genericPoint X') = genericPoint B.X := by
    rw [← hcη, ← Scheme.Hom.comp_apply, hc₁]
    exact genericPoint_eq_of_isOpenImmersion U.ι
  have : IsDominant f₁ := ⟨(dense_iff_closure_eq.2 (genericPoint_spec B.X)).mono
    (Set.singleton_subset_iff.2 ⟨_, hη⟩)⟩
  have : Surjective f₁ := surjective_of_isDominant_of_isClosed_range f₁ f₁.isClosedMap.isClosed_range
  let f : GlobalTheory.Vert.Model.Hom B' B := ⟨f₁, rfl⟩
  have hdeg : f₁.residueDegree (genericPoint X') ≠ 0 := by
    have e := CurveDegreesCompare.residueDegree_comp c f₁ (genericPoint U)
    rw [hc₁, CurveDegreesCompare.residueDegree_of_isOpenImmersion, hcη] at e
    exact left_ne_zero_of_mul_eq_one e.symm
  have hdim : B'.relDim ≤ B.relDim := by
    have h := GlobalTheory.ProperCover.dim_le_of_residueDegree_pos (Z' := B'.X) (Z := B.X) f₁ hη (Nat.pos_of_ne_zero hdeg)
    rw [B'.dim_eq, B.dim_eq] at h
    have h' : B'.relDim + 1 ≤ B.relDim + 1 := by exact_mod_cast h
    omega
  refine ⟨B', f, hη, hN, Nat.sub_eq_zero_of_le hdim, fun y => ?_⟩
  show ∃ i, fnOf U hU (r i) ≠ 0 ∧ ∀ j, ∃ g, RegAt y g ∧
    g * fnMap f₁ (specializes_of_eq hη) (fnOf U hU (r i)) = fnMap f₁ (specializes_of_eq hη) (fnOf U hU (r j))
  have h₁ : ⊤ ≤ (c ≫ q) ⁻¹ᵁ ProjSpace.chart O N i₀ := hc₂ ▸ ProjSpace.ofCoords_preimage_top B.str U i₀ r
  have hV : genericPoint X' ∈ q ⁻¹ᵁ ProjSpace.chart O N i₀ := hcη ▸ h₁ (Set.mem_univ (genericPoint U))
  have key (j) : fnOf _ hV (ProjSpace.pullRatio q _ i₀ le_rfl j) =
      fnMap f₁ (specializes_of_eq hη) (fnOf U hU (r j)) := by
    have h₂ : ⊤ ≤ c ⁻¹ᵁ f₁ ⁻¹ᵁ U := by
      rw [← Scheme.Hom.comp_preimage, hc₁]; exact U.ι_preimage_self.ge
    have h₃ : ⊤ ≤ c ⁻¹ᵁ q ⁻¹ᵁ ProjSpace.chart O N i₀ := h₁
    have hU' : genericPoint X' ∈ f₁ ⁻¹ᵁ U := show f₁ _ ∈ U from hη ▸ hU
    apply (fnMap c (specializes_of_eq hcη)).injective
    rw [GlobalTheory.CorankOne.fnMap_fnOf_appLE f₁ _ le_rfl hU hU',
      GlobalTheory.CorankOne.fnMap_fnOf_appLE c _ (V := ⊤) h₃ hV trivial,
      GlobalTheory.CorankOne.fnMap_fnOf_appLE c _ (V := ⊤) h₂ hU' trivial, ProjSpace.appLE_pullRatio, ProjSpace.appLE_appLE]
    congr 1
    have e₁ : c ≫ q = 𝟙 _ ≫ ProjSpace.ofCoords B.str U i₀ r := by rw [hc₂, Category.id_comp]
    have e₂ : c ≫ f₁ = 𝟙 _ ≫ U.ι := by rw [hc₁, Category.id_comp]
    rw [ProjSpace.pullRatio_of_eq e₁ _ (e₁ ▸ h₁), ProjSpace.appLE_of_eq e₂ _ _ _ (e₂ ▸ h₂)]
    exact ProjSpace.pullRatio_comp_ofCoords B.str U i₀ hr _ _ _ _ j
  obtain ⟨a, ha⟩ := ProjSpace.exists_mem_chart O N (q y)
  have hy : y ∈ q ⁻¹ᵁ ProjSpace.chart O N a := ha
  have hW := memInf hV (gen_mem hy)
  have mul (i j l : Fin (N + 1)) (hi : _ ≤ q ⁻¹ᵁ ProjSpace.chart O N i) (hj : _ ≤ q ⁻¹ᵁ ProjSpace.chart O N j) :=
    congrArg (fnOf _ hW) (ProjSpace.pullRatio_mul_pullRatio (φ := q) (hi := hi) (hj := hj) (k := l))
  refine ⟨a, fun h0 => ?_, fun j => ⟨_, regAt_fnOf hy (gen_mem hy) (ProjSpace.pullRatio q _ a le_rfl j), ?_⟩⟩
  · have e := mul i₀ a i₀ inf_le_left inf_le_right
    rw [ProjSpace.pullRatio_self, map_one, map_mul, ← ProjSpace.resG_pullRatio (hi := le_rfl) inf_le_left,
      fnOf_resG, key, h0, map_zero, zero_mul] at e
    exact zero_ne_one e
  · have e := mul i₀ a j inf_le_left inf_le_right
    rw [map_mul, ← ProjSpace.resG_pullRatio (hi := le_rfl) inf_le_left,
      ← ProjSpace.resG_pullRatio (hi := le_rfl) inf_le_right,
      ← ProjSpace.resG_pullRatio (hi := le_rfl) inf_le_left, fnOf_resG, fnOf_resG, fnOf_resG, key, key] at e
    rw [mul_comm, e]

theorem exists_modification : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (A ι : Type) [Finite A] [Finite ι]
    (w : A → ι → B.X.functionField), (∀ α, ∃ i, w α i ≠ 0) →
    ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (hη : f.f (genericPoint B'.X) = genericPoint B.X),
      GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ ∀ (y : B'.X) (α : A), ∃ i, w α i ≠ 0 ∧ ∀ j, ∃ g,
        GlobalTheory.Cartier.RegAt y g ∧ g * GlobalTheory.TrueGeo.SmallSec.fnMap f.f (specializes_of_eq hη) (w α i) =
          GlobalTheory.TrueGeo.SmallSec.fnMap f.f (specializes_of_eq hη) (w α j) := by
  intro O _ _ _ _ B hn A ι _ _ w hw
  classical
  have := Fintype.ofFinite A
  choose σ₀ hσ₀ using hw
  have : Nonempty (A → ι) := ⟨σ₀⟩
  obtain ⟨N, ⟨ε⟩⟩ : ∃ N, Nonempty (Fin (N + 1) ≃ (A → ι)) := by
    obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := A → ι)).ne'
    exact ⟨N, ⟨(Finite.equivFinOfCardEq hN).symm⟩⟩
  let P : (A → ι) → B.X.functionField := fun σ => ∏ α, w α (σ α)
  have hP₀ : P σ₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun α _ => hσ₀ α
  obtain ⟨U, hU, hr⟩ := InvertIdeal.exists_common_open (x := genericPoint B.X)
    fun i => regAt_genericPoint (P (ε i) / P σ₀)
  choose r hr using hr
  obtain ⟨B', f, hη, hN', h₀, h₃⟩ := exists_modification_sections B hU r (ε.symm σ₀)
    (fnOf_injective U hU (by rw [map_one]; refine (hr _).trans ?_; rw [ε.apply_symm_apply, div_self hP₀]))
  refine ⟨B', f, hη, hN', h₀, fun y α => ?_⟩
  obtain ⟨a, ha, hb⟩ := h₃ y
  have hr' (i) : fnOf U hU (r i) = P (ε i) / P σ₀ := hr i
  rw [hr'] at ha
  have hPa : P (ε a) ≠ 0 := left_ne_zero_of_mul (div_eq_mul_inv (P (ε a)) _ ▸ ha)
  refine ⟨ε a α, Finset.prod_ne_zero_iff.1 hPa α (Finset.mem_univ _), fun j => ?_⟩
  obtain ⟨g, hg, e⟩ := hb (ε.symm (Function.update (ε a) α j))
  refine ⟨g, hg, ?_⟩
  have e₁ : P (ε a) = w α (ε a α) * ∏ β ∈ Finset.univ.erase α, w β (ε a β) :=
    (Finset.mul_prod_erase _ (fun β => w β (ε a β)) (Finset.mem_univ α)).symm
  have e₂ : P (Function.update (ε a) α j) = w α j * ∏ β ∈ Finset.univ.erase α, w β (ε a β) := by
    refine (Finset.mul_prod_erase _ (fun β => w β (Function.update (ε a) α j β)) (Finset.mem_univ α)).symm.trans ?_
    rw [Function.update_self]
    exact congrArg _ (Finset.prod_congr rfl fun β hβ => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hβ)])
  rw [e₁, mul_div_assoc] at ha
  rw [hr', hr', ε.apply_symm_apply, e₁, e₂, mul_div_assoc, mul_div_assoc, map_mul, map_mul, ← mul_assoc] at e
  exact mul_right_cancel₀ ((map_ne_zero _).2 (right_ne_zero_of_mul ha)) e

end GlobalTheory.CorankOneNormal

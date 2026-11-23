import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenPtSSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulOfMapsInlMemS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HTensMixHalfS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtWAtPlSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartAlgebraMapLiftV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxGraphGraphHeis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdeleSupportedAtFinitePlaceOfSupportedAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNatDatumSquareFlip
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesSplitIdempotentSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergStableRelationOfVacuaStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch
open GlobalTheory.SmallDat
open GlobalTheory.BigDat (atW atW_atPl_self atW_atPl_ne atPl_one_mul map_atW_smul symplO_cA_smul symplO_zero_right' isHalf_smul_self
  smul_of_isHalf smul_eq_zero_of_isHalf map_infPart_of_isHalf)
open GlobalTheory.BigDat.GraphHeis

noncomputable section

namespace GlobalTheory.SmallPlaces

section Coord

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem mixCoS_eq (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E) (u : PtS G i j) :
    mixCoS B t e w u = fromCols (B.coord t w (X := (i, j + 1)) (Y := (i, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩
      ((mapA t e u).map (atW w)))
      (B.coord t w (X := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩ ((mapB e u).map (atW w)))ᵀ := rfl

theorem mixCoS_spec : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (B : Frames G) (t : T)
    (i j : Fin D.R.m) (e : Num G i j) (w : Pl D.host.E),
    (∀ u x : PtS G i j, mixCoS B t e w (u + x) = mixCoS B t e w u + mixCoS B t e w x) ∧
    (∀ z, ∃ x ∈ mixHalfS e (atPl w 1), mixCoS B t e w x = z) ∧
    (∀ u : PtS G i j, mixCoS B t e w (ofMaps t e (atPl w 1 • mapA t e u, atPl w 1 • mapB e u)) = mixCoS B t e w u) ∧
    ∀ w' : Pl D.host.E, w' ≠ w → ∀ x ∈ mixHalfS e (atPl w' 1), mixCoS B t e w x = 0 := by
  intro D T L sc G B t i j e w
  refine ⟨fun u x => ?_, fun z => ?_, fun u => ?_, fun w' hw x hx => ?_⟩
  · rw [mixCoS_eq, mixCoS_eq, mixCoS_eq, mapA_add, mapB_add, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _),
      GlobalTheory.BigDat.CoordinateMaps.coord_add, GlobalTheory.BigDat.CoordinateMaps.coord_add, transpose_add]
    exact Matrix.ext fun a b => by rcases b with b | b <;> rfl
  · obtain ⟨y₁, hy₁⟩ := GlobalTheory.BigDat.CoordinateMaps.coord_surj B t w (X := (i, j + 1)) (Y := (i, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩
      z.toCols₁
    obtain ⟨y₂, hy₂⟩ := GlobalTheory.BigDat.CoordinateMaps.coord_surj B t w (X := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩
      z.toCols₂ᵀ
    let x₁ : HomA G t i j := y₁.map (atPl w)
    let x₂ : HomB G i j := y₂.map (atPl w)
    have k₁ : mapA t e (ofMaps t e (x₁, x₂)) = x₁ := mapA_ofMaps t e _
    have k₂ : mapB e (ofMaps t e (x₁, x₂)) = x₂ := mapB_ofMaps t e _
    have m₁ : x₁.map (atW w) = y₁ := Matrix.ext fun a b => atW_atPl_self w _
    have m₂ : x₂.map (atW w) = y₂ := Matrix.ext fun a b => atW_atPl_self w _
    refine ⟨ofMaps t e (x₁, x₂), ⟨?_, ?_⟩, ?_⟩
    · show IsHalf _ (mapA t e _)
      rw [k₁]
      intro a b
      exact atPl_one_mul w _
    · show IsHalf _ (mapB e _)
      rw [k₂]
      intro a b
      exact atPl_one_mul w _
    · rw [mixCoS_eq, k₁, k₂, m₁, m₂, hy₁, hy₂, transpose_transpose, fromCols_toCols]
  · have k₁ : mapA t e (ofMaps t e (atPl w 1 • mapA t e u, atPl w 1 • mapB e u)) = atPl w 1 • mapA t e u := mapA_ofMaps t e _
    have k₂ : mapB e (ofMaps t e (atPl w 1 • mapA t e u, atPl w 1 • mapB e u)) = atPl w 1 • mapB e u := mapB_ofMaps t e _
    rw [mixCoS_eq, mixCoS_eq, k₁, k₂, map_atW_smul, map_atW_smul]
  · have h₁ : (mapA t e x).map (atW w) = 0 := by
      refine Matrix.ext fun a b => ?_
      calc atW w (mapA t e x a b) = atW w (atPl w' 1 * mapA t e x a b) := congrArg _ (hx.1 a b).symm
        _ = 0 := by rw [map_mul, atW_atPl_ne hw.symm, zero_mul]
    have h₂ : (mapB e x).map (atW w) = 0 := by
      refine Matrix.ext fun a b => ?_
      calc atW w (mapB e x a b) = atW w (atPl w' 1 * mapB e x a b) := congrArg _ (hx.2 a b).symm
        _ = 0 := by rw [map_mul, atW_atPl_ne hw.symm, zero_mul]
    rw [mixCoS_eq, h₁, h₂, GlobalTheory.BigDat.CoordinateMaps.coord_zero, GlobalTheory.BigDat.CoordinateMaps.coord_zero, transpose_zero, fromCols_zero]

end Coord

section Halves

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} {t : T}

theorem at_of_mixHalf (t : T) (e : Num G i j) (v : Pl D.host.F) {b : AE D}
    (hb : b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = b) {u : PtS G i j} (hu : u ∈ mixHalfS e b) :
    At (evFin D.host.F v) u := by
  intro c hc
  apply (maps t e).injective
  rw [map_smul, map_zero, maps_apply, Prod.smul_mk, smul_eq_zero_of_isHalf v hb hu.1 c hc,
    smul_eq_zero_of_isHalf v hb hu.2 c hc, Prod.mk_zero_zero]

theorem ofMaps_smul_mem (e : Num G i j) {b : AE D} (hb : b * b = b) (x₁ : HomA G t i j) (x₂ : HomB G i j) :
    ofMaps t e (b • x₁, b • x₂) ∈ mixHalfS e b := by
  refine ⟨?_, ?_⟩
  · show IsHalf b (mapA t e (ofMaps t e _))
    rw [mapA_ofMaps]
    exact isHalf_smul_self hb _
  · show IsHalf b (mapB e (ofMaps t e _))
    rw [mapB_ofMaps]
    exact isHalf_smul_self hb _

theorem ofMaps_add_ofMaps (e : Num G i j) (v : Pl D.host.F) {a : AE D}
    (hsum : a + cA D a = algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1)) {u : PtS G i j}
    (hu : At (evFin D.host.F v) u) :
    ofMaps t e (a • mapA t e u, a • mapB e u) + ofMaps t e (cA D a • mapA t e u, cA D a • mapB e u) = u := by
  have h1 : (1 - GlobalTheory.LatVac.liftV v 1) • u = 0 :=
    hu _ (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  have hℓu : GlobalTheory.LatVac.liftV v 1 • u = u := by
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    exact h1.symm
  apply (maps t e).injective
  refine Prod.ext ?_ ?_
  · show mapA t e (_ + _) = mapA t e u
    rw [mapA_add, mapA_ofMaps, mapA_ofMaps, ← add_smul, hsum, algebraMap_smul, ← mapA_smul, hℓu]
  · show mapB e (_ + _) = mapB e u
    rw [mapB_add, mapB_ofMaps, mapB_ofMaps, ← add_smul, hsum, algebraMap_smul, ← mapB_smul, hℓu]

theorem mapA_mem_latA_of_char (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram)
    (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e) {ψ : AddChar (AF D.host.F) ℂ} (hstd : IsStdChar D ψ (-1))
    (hS : IsSelfDualC (spW₁ G i j) (G.Λ (.grid i j)))
    (hT : IsSelfDualC (spV G i j) (G.Λ (.grid i (j + 1)))) (v : Pl D.host.F) {a : AE D}
    (ha1 : a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = a) (hcc : cA D a * cA D a = cA D a)
    (hc1 : cA D a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = cA D a) (hfc : finPart D (cA D a) ∈ intAE D)
    {x : PtS G i j} (hx : x ∈ mixHalfS e a)
    (hψ : ∀ y ∈ latPtS t e v, y ∈ mixHalfS e (cA D a) → ψ (sympS Γ x y) = 1) : mapA t e x ∈ latA G t i j := by
  refine GlobalTheory.LatVac.mem_of_char hstd hS hT (map_infPart_of_isHalf v ha1 hx.1) fun l hl => ?_
  have hy : ofMaps t e (cA D a • l, (0 : HomB G i j)) ∈ mixHalfS e (cA D a) := by
    refine ⟨?_, ?_⟩
    · show IsHalf _ (mapA t e (ofMaps t e _))
      rw [mapA_ofMaps]
      exact isHalf_smul_self hcc _
    · show IsHalf _ (mapB e (ofMaps t e _))
      rw [mapB_ofMaps]
      exact fun p q => mul_zero _
  have hyl : ofMaps t e (cA D a • l, (0 : HomB G i j)) ∈ latPtS t e v := by
    refine ⟨at_of_mixHalf t e v hc1 hy, ?_, ?_⟩
    · show mapA t e (ofMaps t e _) ∈ latA G t i j
      rw [mapA_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfc l hl
    · show mapB e (ofMaps t e _) ∈ latB G i j
      rw [mapB_ofMaps]
      exact zero_mem _
  have h := hψ _ hyl hy
  rw [sympS_eq t e Γ hW hWW, mapA_ofMaps, mapB_ofMaps, symplO_cA_smul, smul_of_isHalf hx.1, symplO_zero_right',
    add_zero] at h
  exact h

theorem mapB_mem_latB_of_char (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram)
    (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e) {ψ : AddChar (AF D.host.F) ℂ} (hstd : IsStdChar D ψ (-1))
    (hS : IsSelfDualC (negSp (spV₁ G i j)) (G.Λ (.grid (i + 1) j)))
    (hT : IsSelfDualC (spW₁ G i j) (G.Λ (.grid i j))) (v : Pl D.host.F) {a : AE D}
    (ha1 : a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = a) (hcc : cA D a * cA D a = cA D a)
    (hc1 : cA D a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = cA D a) (hfc : finPart D (cA D a) ∈ intAE D)
    {x : PtS G i j} (hx : x ∈ mixHalfS e a)
    (hψ : ∀ y ∈ latPtS t e v, y ∈ mixHalfS e (cA D a) → ψ (sympS Γ x y) = 1) : mapB e x ∈ latB G i j := by
  refine GlobalTheory.LatVac.mem_of_char hstd hS hT (map_infPart_of_isHalf v ha1 hx.2) fun l hl => ?_
  have hy : ofMaps t e ((0 : HomA G t i j), cA D a • l) ∈ mixHalfS e (cA D a) := by
    refine ⟨?_, ?_⟩
    · show IsHalf _ (mapA t e (ofMaps t e _))
      rw [mapA_ofMaps]
      exact fun p q => mul_zero _
    · show IsHalf _ (mapB e (ofMaps t e _))
      rw [mapB_ofMaps]
      exact isHalf_smul_self hcc _
  have hyl : ofMaps t e ((0 : HomA G t i j), cA D a • l) ∈ latPtS t e v := by
    refine ⟨at_of_mixHalf t e v hc1 hy, ?_, ?_⟩
    · show mapA t e (ofMaps t e _) ∈ latA G t i j
      rw [mapA_ofMaps]
      exact zero_mem _
    · show mapB e (ofMaps t e _) ∈ latB G i j
      rw [mapB_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfc l hl
  have h := hψ _ hyl hy
  rw [sympS_eq t e Γ hW hWW, mapA_ofMaps, mapB_ofMaps, symplO_cA_smul, smul_of_isHalf hx.2, symplO_zero_right',
    zero_add] at h
  exact h

theorem halves_split : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram → Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e → ∀ (v : Pl D.host.F) (a : AE D), IsSplitIdem D a →
    a + cA D a = algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) →
    (∀ u ∈ mixHalfS e a, At (evFin D.host.F v) u) ∧ (∀ u ∈ mixHalfS e (cA D a), At (evFin D.host.F v) u) ∧
    (∀ u : PtS G i j, At (evFin D.host.F v) u → ∃ x ∈ mixHalfS e a, ∃ y ∈ mixHalfS e (cA D a), u = x + y) ∧
    (∀ x ∈ mixHalfS e a, (∀ y ∈ latPtS t e v, y ∈ mixHalfS e (cA D a) → W.ψ (sympS Γ x y) = 1) → x ∈ latPtS t e v) ∧
    ∀ u : PtS G i j, ofMaps t e (a • mapA t e u, a • mapB e u) ∈ mixHalfS e a ∧
      (∀ y ∈ mixHalfS e (cA D a), sympS Γ u y = sympS Γ (ofMaps t e (a • mapA t e u, a • mapB e u)) y) ∧
      (mapA t e u ∈ latA G t i j → mapB e u ∈ latB G i j → ofMaps t e (a • mapA t e u, a • mapB e u) ∈ latPtS t e v) := by
  intro D T L sc G μ₀ hL W t i j e Γ hW hWW v a ha hsum
  obtain ⟨haa, hac, -⟩ := ha
  have hcc : cA D a * cA D a = cA D a := by rw [← map_mul, haa]
  have hca : cA D a * a = 0 := by rw [mul_comm, hac]
  have ha1 : a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = a := by
    rw [← hsum, mul_add, haa, hac, add_zero]
  have hc1 : cA D a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = cA D a := by
    rw [← hsum, mul_add, hca, hcc, zero_add]
  have hfa : finPart D a ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, haa])
  have hfc : finPart D (cA D a) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hcc])
  have hS : IsSelfDualC (spW₁ G i j) (G.Λ (.grid (i : ℕ) (j : ℕ))) :=
    (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have hT : IsSelfDualC (spV G i j) (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have hS₁ : IsSelfDualC (negSp (spV₁ G i j)) (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ))) :=
    isSelfDualC_neg (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  have hT₁ : IsSelfDualC (spW₁ G i j) (G.Λ (.grid (i : ℕ) (j : ℕ))) :=
    (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  refine ⟨fun u hu => at_of_mixHalf t e v ha1 hu, fun u hu => at_of_mixHalf t e v hc1 hu, fun u hu =>
    ⟨_, ofMaps_smul_mem e haa _ _, _, ofMaps_smul_mem e hcc _ _, (ofMaps_add_ofMaps (t := t) e v hsum hu).symm⟩,
    fun x hx hψ => ⟨at_of_mixHalf t e v ha1 hx,
      mapA_mem_latA_of_char e Γ hW hWW W.ψ_std hS hT v ha1 hcc hc1 hfc hx hψ,
      mapB_mem_latB_of_char e Γ hW hWW W.ψ_std hS₁ hT₁ v ha1 hcc hc1 hfc hx hψ⟩, fun u => ?_⟩
  refine ⟨ofMaps_smul_mem e haa _ _, fun y hy => ?_, fun hV hW' => ?_⟩
  · rw [sympS_eq t e Γ hW hWW, sympS_eq t e Γ hW hWW, mapA_ofMaps, mapB_ofMaps, ← symplO_cA_smul, ← symplO_cA_smul,
      smul_of_isHalf hy.1, smul_of_isHalf hy.2]
  · refine ⟨at_of_mixHalf t e v ha1 (ofMaps_smul_mem e haa _ _), ?_, ?_⟩
    · show mapA t e (ofMaps t e _) ∈ latA G t i j
      rw [mapA_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfa _ hV
    · show mapB e (ofMaps t e _) ∈ latB G i j
      rw [mapB_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfa _ hW'

def boxGraph (t : T) (e : Num G i j) (ε : AE D) (T₁ : (HomA G t i j → ℂ) →ₗ[ℂ] (HomA G t i j → ℂ))
    (T₂ : (HomB G i j → ℂ) →ₗ[ℂ] (HomB G i j → ℂ)) : Submodule ℂ ((PtS G i j → ℂ) × (PtS G i j → ℂ)) :=
  Submodule.span ℂ {p | ∃ φ₁ φ₂, IsSBHalf ε (latA G t i j) φ₁ ∧ IsSBHalf ε (latB G i j) φ₂ ∧
    p = (boxS t e φ₁ φ₂, boxS t e (T₁ φ₁) (T₂ φ₂))}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

def graphMap (t : T) (e : Num G i j) (T₁ : (HomA G t i j → ℂ) →ₗ[ℂ] (HomA G t i j → ℂ))
    (T₂ : (HomB G i j → ℂ) →ₗ[ℂ] (HomB G i j → ℂ)) : (PtS G i j → ℂ) →ₗ[ℂ] (PtS G i j → ℂ) where
  toFun g u := T₁ (fun x => T₂ (fun y => g (ofMaps t e (x, y))) (mapB e u)) (mapA t e u)
  map_add' g g' := funext fun u => by
    have h : (fun x => T₂ (fun y => (g + g') (ofMaps t e (x, y))) (mapB e u)) =
        (fun x => T₂ (fun y => g (ofMaps t e (x, y))) (mapB e u)) + fun x => T₂ (fun y => g' (ofMaps t e (x, y))) (mapB e u) :=
      funext fun x => by
        show T₂ ((fun y => g (ofMaps t e (x, y))) + fun y => g' (ofMaps t e (x, y))) (mapB e u) = _
        rw [map_add]; rfl
    show T₁ (fun x => T₂ (fun y => (g + g') (ofMaps t e (x, y))) (mapB e u)) (mapA t e u) = _
    rw [h, map_add]; rfl
  map_smul' c g := funext fun u => by
    have h : (fun x => T₂ (fun y => (c • g) (ofMaps t e (x, y))) (mapB e u)) =
        c • fun x => T₂ (fun y => g (ofMaps t e (x, y))) (mapB e u) :=
      funext fun x => by
        show T₂ (c • fun y => g (ofMaps t e (x, y))) (mapB e u) = _
        rw [map_smul]; rfl
    show T₁ (fun x => T₂ (fun y => (c • g) (ofMaps t e (x, y))) (mapB e u)) (mapA t e u) = _
    rw [h, map_smul]; rfl

theorem graphMap_box (e : Num G i j) (T₁ : (HomA G t i j → ℂ) →ₗ[ℂ] (HomA G t i j → ℂ))
    (T₂ : (HomB G i j → ℂ) →ₗ[ℂ] (HomB G i j → ℂ)) (φ₁ : HomA G t i j → ℂ) (φ₂ : HomB G i j → ℂ) :
    graphMap t e T₁ T₂ (boxS t e φ₁ φ₂) = boxS t e (T₁ φ₁) (T₂ φ₂) := funext fun u => by
  have e2 : ∀ x, (fun y => boxS t e φ₁ φ₂ (ofMaps t e (x, y))) = φ₁ x • φ₂ := fun x => funext fun y => by
    show φ₁ (mapA t e (ofMaps t e (x, y))) * φ₂ (mapB e (ofMaps t e (x, y))) = φ₁ x * φ₂ y
    rw [mapA_ofMaps, mapB_ofMaps]
  have e1 : (fun x => T₂ (fun y => boxS t e φ₁ φ₂ (ofMaps t e (x, y))) (mapB e u)) = T₂ φ₂ (mapB e u) • φ₁ :=
    funext fun x => by
      rw [e2, map_smul]
      show φ₁ x * T₂ φ₂ (mapB e u) = T₂ φ₂ (mapB e u) * φ₁ x
      exact mul_comm _ _
  show T₁ (fun x => T₂ (fun y => boxS t e φ₁ φ₂ (ofMaps t e (x, y))) (mapB e u)) (mapA t e u) = T₁ φ₁ (mapA t e u) * T₂ φ₂ (mapB e u)
  rw [e1, map_smul]
  show T₂ φ₂ (mapB e u) * T₁ φ₁ (mapA t e u) = _
  exact mul_comm _ _

def transPair (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (x : PtS G i j) :
    ((PtS G i j → ℂ) × (PtS G i j → ℂ)) →ₗ[ℂ] ((PtS G i j → ℂ) × (PtS G i j → ℂ)) where
  toFun p := (fun u => p.1 (u + x), heisS Γ ψ x p.2)
  map_add' p q := Prod.ext rfl (funext fun u => mul_add _ _ _)
  map_smul' c p := Prod.ext rfl (funext fun u => mul_left_comm _ _ _)

def modulPair (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (y : PtS G i j) :
    ((PtS G i j → ℂ) × (PtS G i j → ℂ)) →ₗ[ℂ] ((PtS G i j → ℂ) × (PtS G i j → ℂ)) where
  toFun p := (fun u => ψ (sympS Γ u y) * p.1 u, heisS Γ ψ y p.2)
  map_add' p q := Prod.ext (funext fun u => mul_add _ _ _) (funext fun u => mul_add _ _ _)
  map_smul' c p := Prod.ext (funext fun u => mul_left_comm _ _ _) (funext fun u => mul_left_comm _ _ _)

theorem boxGraph_graph_heis : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram → Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e → ∀ (ε : AE D) (P : Finset (Pl D.host.E)), IsIdemSum ε P →
    ∀ (f₁ : HomA G t i j → ℂ) (f₂ : HomB G i j → ℂ) (T₁ : (HomA G t i j → ℂ) →ₗ[ℂ] (HomA G t i j → ℂ))
      (T₂ : (HomB G i j → ℂ) →ₗ[ℂ] (HomB G i j → ℂ)),
    IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) ε (latA G t i j) 1 f₁ T₁ →
    IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) ε (latB G i j) 1 f₂ T₂ →
    (∀ f, (0, f) ∈ boxGraph t e ε T₁ T₂ → f = 0) ∧
    (∀ x ∈ mixHalfS e ε, ∀ p ∈ boxGraph t e ε T₁ T₂, (fun u => p.1 (u + x), heisS Γ W.ψ x p.2) ∈ boxGraph t e ε T₁ T₂) ∧
    ∀ y ∈ mixHalfS e (cA D ε), ∀ p ∈ boxGraph t e ε T₁ T₂,
      (fun u => W.ψ (sympS Γ u y) * p.1 u, heisS Γ W.ψ y p.2) ∈ boxGraph t e ε T₁ T₂ := by
  intro D T L sc G μ₀ hL W t i j e Γ hW hWW ε P hε f₁ f₂ T₁ T₂ h₁ h₂
  have hinf : infPart D ε = 0 := GlobalTheory.PlaceVec.idemSum_infPart hε
  have hinf' : infPart D (cA D ε) = 0 := GlobalTheory.PlaceVec.infPart_cA hinf
  have sdW : IsSelfDualC (spW₁ G i j) (G.Λ (.grid (i : ℕ) (j : ℕ))) :=
    (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have sdV : IsSelfDualC (spV G i j) (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have sdV₁ : IsSelfDualC (negSp (spV₁ G i j)) (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ))) :=
    isSelfDualC_neg (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  have sdW' : IsSelfDualC (spW₁ G i j) (G.Λ (.grid (i : ℕ) (j : ℕ))) := sdW
  refine ⟨fun f hf => ?_, fun x hx p hp => ?_, fun y hy p hp => ?_⟩
  · have key : boxGraph t e ε T₁ T₂ ≤ LinearMap.ker (LinearMap.snd ℂ _ _ - graphMap t e T₁ T₂ ∘ₗ LinearMap.fst ℂ _ _) := by
      refine Submodule.span_le.2 fun p hp => ?_
      obtain ⟨φ₁, φ₂, -, -, rfl⟩ := hp
      show boxS t e (T₁ φ₁) (T₂ φ₂) - graphMap t e T₁ T₂ (boxS t e φ₁ φ₂) = 0
      rw [graphMap_box, sub_self]
    have h0 := key hf
    rw [LinearMap.mem_ker] at h0
    have h1 : f - graphMap t e T₁ T₂ 0 = 0 := h0
    rwa [map_zero, sub_zero] at h1
  · have key : boxGraph t e ε T₁ T₂ ≤ (boxGraph t e ε T₁ T₂).comap (transPair Γ W.ψ x) := by
      refine Submodule.span_le.2 fun p hp => ?_
      obtain ⟨φ₁, φ₂, hφ₁, hφ₂, rfl⟩ := hp
      have hx₁ : IsHalf ε (mapA t e x) := hx.1
      have hx₂ : IsHalf ε (mapB e x) := hx.2
      have s₁ : IsSBHalf ε (latA G t i j) (fun y' => φ₁ (y' + mapA t e x)) :=
        sb_trans_latO (S := spW₁ G i j) (T := spV G i j) (ΛS := G.Λ (.grid (i : ℕ) (j : ℕ)))
          (ΛT := G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) sdW'.1 sdV.1 hinf hφ₁ hx₁
      have s₂ : IsSBHalf ε (latB G i j) (fun y' => φ₂ (y' + mapB e x)) :=
        sb_trans_latO (S := negSp (spV₁ G i j)) (T := spW₁ G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) (j : ℕ)))
          (ΛT := G.Λ (.grid (i : ℕ) (j : ℕ))) sdV₁.1 sdW.1 hinf hφ₂ hx₂
      show (fun u => boxS t e φ₁ φ₂ (u + x), heisS Γ W.ψ x (boxS t e (T₁ φ₁) (T₂ φ₂))) ∈ boxGraph t e ε T₁ T₂
      rw [heisS_box t e Γ hW hWW]
      refine Submodule.subset_span ⟨_, _, s₁, s₂, ?_⟩
      rw [h₁.trans φ₁ hφ₁ _ hx₁, h₂.trans φ₂ hφ₂ _ hx₂]
      refine Prod.ext (funext fun u => ?_) rfl
      show φ₁ (mapA t e (u + x)) * φ₂ (mapB e (u + x)) = φ₁ (mapA t e u + mapA t e x) * φ₂ (mapB e u + mapB e x)
      rw [mapA_add, mapB_add]
    exact key hp
  · have key : boxGraph t e ε T₁ T₂ ≤ (boxGraph t e ε T₁ T₂).comap (modulPair Γ W.ψ y) := by
      refine Submodule.span_le.2 fun p hp => ?_
      obtain ⟨φ₁, φ₂, hφ₁, hφ₂, rfl⟩ := hp
      have hy₁ : IsHalf (cA D ε) (mapA t e y) := hy.1
      have hy₂ : IsHalf (cA D ε) (mapB e y) := hy.2
      have s₁ : IsSBHalf ε (latA G t i j) (fun y' => W.ψ (symplO _ _ y' (mapA t e y)) * φ₁ y') :=
        sb_modul_latO (S := spW₁ G i j) (T := spV G i j) (ΛS := G.Λ (.grid (i : ℕ) (j : ℕ)))
          (ΛT := G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) W.ψ_std sdW' sdV hinf' hφ₁ hy₁
      have s₂ : IsSBHalf ε (latB G i j) (fun y' => W.ψ (symplO _ _ y' (mapB e y)) * φ₂ y') :=
        sb_modul_latO (S := negSp (spV₁ G i j)) (T := spW₁ G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) (j : ℕ)))
          (ΛT := G.Λ (.grid (i : ℕ) (j : ℕ))) W.ψ_std sdV₁ sdW hinf' hφ₂ hy₂
      show (fun u => W.ψ (sympS Γ u y) * boxS t e φ₁ φ₂ u, heisS Γ W.ψ y (boxS t e (T₁ φ₁) (T₂ φ₂))) ∈ boxGraph t e ε T₁ T₂
      rw [heisS_box t e Γ hW hWW]
      refine Submodule.subset_span ⟨_, _, s₁, s₂, ?_⟩
      rw [h₁.modul φ₁ hφ₁ _ hy₁, h₂.modul φ₂ hφ₂ _ hy₂]
      refine Prod.ext (funext fun u => ?_) rfl
      show W.ψ (sympS Γ u y) * (φ₁ (mapA t e u) * φ₂ (mapB e u)) =
        (W.ψ (symplO _ _ (mapA t e u) (mapA t e y)) * φ₁ (mapA t e u)) * (W.ψ (symplO _ _ (mapB e u) (mapB e y)) * φ₂ (mapB e u))
      rw [sympS_eq t e Γ hW hWW, AddChar.map_add_eq_mul]
      ring
    exact key hp

end Halves

theorem lagr_vac {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {Y : Spc F E d} {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} {v : HeightOneSpectrum (𝓞 F)} {A A' : Set _}
    {Z : Type} [TopologicalSpace Z] [AddGroup Z] {co ι} (h : IsLagrModel (Z := Z) M ψ v A A' co ι)
    {φ : (Fin n × Fin d → Fv F v) → ℂ} (hφ : φ ∈ GlobalTheory.WeilM.SB _) (h0 : φ ≠ 0) (Λ : Set _)
    (hfix : ∀ γ ∈ Λ, γ ∈ A ∨ γ ∈ A' → Acts (evFin F v) (M.co.rho ψ γ) φ φ) (hon : ∀ z, ∃ x ∈ A, co x = z)
    (hd : ∀ x ∈ A, (∀ y ∈ Λ, y ∈ A' → ψ (symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x y) = 1) → x ∈ Λ) :
    ι φ 0 ≠ 0 ∧ ∀ x ∈ A, ι φ (co x) = Λ.indicator (fun _ => ι φ 0) x := by
  have key : ∀ x ∈ A, ι φ (co x) = Λ.indicator (fun _ => ι φ 0) x := fun x hx => by
    by_cases hΛ : x ∈ Λ
    · rw [Set.indicator_of_mem hΛ, h.2.1 x hx φ hφ φ hφ (hfix x hΛ (.inl hx)) 0, zero_add]
    · rw [Set.indicator_of_notMem hΛ]
      by_contra hne
      exact hΛ (hd x hx fun y hy hy' =>
        mul_right_cancel₀ hne ((h.2.2 y hy' φ hφ φ hφ (hfix y hy (.inr hy')) x hx).symm.trans (one_mul _).symm))
  refine ⟨fun h1 => h0 (h.1.injOn hφ (zero_mem _) (funext fun z => ?_)), key⟩
  obtain ⟨x, hx, rfl⟩ := hon z
  rw [key x hx, h1, map_zero]
  exact congrFun (Set.indicator_zero _ _) x

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem splitIdem_conj {a : AE D} (h : IsSplitIdem D a) : IsSplitIdem D (cA D a) := by
  obtain ⟨h1, h2, v, ε, h3, h4⟩ := h
  refine ⟨by rw [← RingHom.map_mul, h1], ?_, v, ε, h3, ?_⟩
  · rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2]
  · rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h4]

def halfPt {i j : ℕ} (t : T) (e : Num G i j) (ε : AE D) : AddSubgroup (PtS G i j) :=
  ((GlobalTheory.PlaceModel.half _ _ ε).prod (GlobalTheory.PlaceModel.half _ _ ε)).comap (maps t e).toLinearMap.toAddMonoidHom

theorem mem_halfPt {i j : ℕ} {t : T} {e : Num G i j} {ε : AE D} {u : PtS G i j} : u ∈ halfPt t e ε ↔ u ∈ mixHalfS e ε :=
  and_congr (GlobalTheory.PlaceModel.isHalf_iff _ _).symm (GlobalTheory.PlaceModel.isHalf_iff _ _).symm

theorem isHalf_mono {m n : ℕ} {a ε : AE D} (h : ε * a = a) {x : Mx D m n} (hx : IsHalf a x) : IsHalf ε x := fun p q => by
  rw [← hx p q, ← mul_assoc, h]

theorem mem_of_sum_smul {m n : ℕ} {ι : Type} {P : Finset ι} {a : ι → AE D} {x : Mx D m n} (hx : IsHalf (∑ w ∈ P, a w) x)
    {Λ : AddSubgroup (Mx D m n)} (h : ∀ w ∈ P, a w • x ∈ Λ) : x ∈ Λ := by
  have : x = ∑ w ∈ P, a w • x := by
    rw [← Finset.sum_smul]
    exact Matrix.ext fun p q => (hx p q).symm
  rw [this]
  exact sum_mem h

set_option maxHeartbeats 1600000 in

theorem exists_scalar_datum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X →
    ∀ f₀, IsDatumB (t := t) W e Γ (Finsupp.single (((), ρ.vT i j), ρ.vX i j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M'.vac) →
    ∀ ι : ∀ w : Pl D.host.E, ((Fin (spW₁ G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ]
      (Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ),
    (∀ w ∈ locPl G t, IsLagrModel Γ.M' W.ψ (w.under (𝓞 D.host.F)) (mixHalfS e (atPl w 1)) (mixHalfS e (cA D (atPl w 1))) (mixCoS B t e w) (ι w)) →
    ∃ s : ℂ, s ≠ 0 ∧ ∀ ε, IsIdemSum ε (locPl G t) → ∀ (n : Pl D.host.E → ℕ) Ψ (τ : TotT G (routeSmall t i j)),
      (∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Ψ w)) →
      HasLocal B t ε (X := (i, j + 1)) (M := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩
        (IsLocVec W (.mu t i j) ε (ρ.vT i j)) (IsLocVec W (.chi i j) ε (ρ.vX i j)) τ Ψ →
      ∀ φ, IsFinPart Γ.M' X.T φ → (∀ w ∈ locPl G t, ι w (φ (w.under (𝓞 D.host.F))) = Ψ w) →
        IsDatumB W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (s • f₀) φ) := by
  intro D T L sc G μ₀ hL W B ρ t i j M _ e Bs Γ X om om' h hT hti f hf₀ I hI
  classical
  have h₁ := ρ.vT_is t i j i.2.le j.2
  have h₂ := ρ.vX_is i j i.2 j.2.le
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  have hG : Γ.M'.IsGood W.ψ := h.ψ ▸ hT.geo.hM'
  have hadd : ∀ Φ ∈ schA D.host.F (IxS G i j), ∀ Φ' ∈ schA D.host.F (IxS G i j),
      thetaS Γ W.ψ (Φ + Φ') = thetaS Γ W.ψ Φ + thetaS Γ W.ψ Φ' := fun Φ hΦ Φ' hΦ' => funext fun u =>
    (tsum_congr fun _ => mul_add _ _ _).trans
      ((summable_of_mem_schA _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd u _ hΦ)).tsum_add
        (summable_of_mem_schA _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd u _ hΦ')))
  have hf : thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M'.vac) = boxS t e (ρ.vT i j) (ρ.vX i j) :=
    funext fun u => (hf₀.2 u).trans ((Finsupp.sum_single_index (zero_mul _)).trans (one_mul _))
  obtain ⟨hid, hsumid⟩ := GlobalTheory.T.gridLocalTensorPlaces_splitIdempotent_sum hL (G := G) t
  have hh := fun w hw => halves_split hL W t i j e Γ h.JW₁ h.JWW _ _ (hid w hw).1 (hid w hw).2
  have hco := mixCoS_spec B t i j e
  have hv := fun w hw => lagr_vac (hI w hw) (hG.vac _).1 (hG.vac _).2.1 (latPtS t e (w.under (𝓞 D.host.F)) : Set _)
    (fun γ hγ hγ' => VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT _ (latPtS_le_latAtV t i j e Bs Γ X hti _) γ (.inr ⟨hγ, hγ'.elim
      (fun h => ⟨_, (hid w hw).1, h⟩) fun h => ⟨_, splitIdem_conj (hid w hw).1, h⟩⟩)) (hco w).2.1 (hh w hw).2.2.2.1
  set c := ∏ w ∈ locPl G t, I w (Γ.M'.vac _) 0 with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun w hw => (hv w hw).1
  refine ⟨c, hc0, fun ε hε n Ψ τ _ ⟨φ₁, φ₂, hmem, hsum⟩ φ hφ hΨ => ?_⟩
  have hb : thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) Γ.M'.vac) = c • boxS t e (ρ.vT i j) (ρ.vX i j) := by
    rw [← hf]
    exact funext fun u => (congrArg (thetaS Γ W.ψ · u) (funext fun _ => mul_assoc _ _ _)).trans (thetaS_smul _ _ _ _ u)
  have sW := (node_isV G hL (X := .grid i j) ⟨i.2.le, j.2.le⟩).sd
  obtain ⟨T₁, hT₁⟩ := (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _ sW
    (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd _ ε hε _ h₁.2.theta h₁.2.lat).1
  obtain ⟨T₂, hT₂⟩ := (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _
    (isSelfDualC_neg (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd) sW _ ε hε _ h₂.2.theta h₂.2.lat).1
  obtain ⟨g0, g1, g2⟩ := boxGraph_graph_heis hL W t i j e Γ h.JW₁ h.JWW ε _ hε _ _ T₁ T₂ hT₁ hT₂
  obtain ⟨hεs, hεw⟩ := hsumid ε hε
  let R : Submodule ℂ ((PtS G i j → ℂ) × ((IxS G i j → AF D.host.F) → ℂ)) :=
    { carrier := {p | p.2 ∈ schA D.host.F _ ∧ (p.1, thetaS Γ W.ψ p.2) ∈ boxGraph t e ε T₁ T₂}
      zero_mem' := ⟨zero_mem _, by
        have : thetaS Γ W.ψ 0 = 0 := funext fun u => by simpa using thetaS_smul Γ W.ψ 0 0 u
        rw [Prod.snd_zero, this]; exact zero_mem _⟩
      add_mem' := fun {p q} hp hq => ⟨add_mem hp.1 hq.1, by
        rw [Prod.snd_add, hadd _ hp.1 _ hq.1]; exact add_mem hp.2 hq.2⟩
      smul_mem' := fun a p hp => ⟨Submodule.smul_mem _ a hp.1, by
        rw [Prod.smul_snd, show thetaS Γ W.ψ (a • p.2) = a • thetaS Γ W.ψ p.2 from funext (thetaS_smul _ _ _ _)]
        exact Submodule.smul_mem _ a hp.2⟩ }
  have hA : ∀ w ∈ locPl G t, ∀ x ∈ mixHalfS e (atPl w 1), x ∈ mixHalfS e ε := fun w hw x hx =>
    ⟨isHalf_mono (hεw w hw) hx.1, isHalf_mono (hεw w hw) hx.2⟩
  have hA' : ∀ w ∈ locPl G t, ∀ x ∈ mixHalfS e (cA D (atPl w 1)), x ∈ mixHalfS e (cA D ε) := fun w hw x hx =>
    have : cA D ε * cA D (atPl w 1) = cA D (atPl w 1) := by rw [← RingHom.map_mul, hεw w hw]
    ⟨isHalf_mono this hx.1, isHalf_mono this hx.2⟩
  have hbase : (Set.indicator (halfPt t e ε : Set _) fun u => ∏ w ∈ locPl G t, I w (Γ.M'.vac _) (mixCoS B t e w u)) =
      c • boxS t e (halfInd ε (latA G t i j)) (halfInd ε (latB G i j)) := by
    funext u
    rw [Pi.smul_apply, smul_eq_mul, boxS, halfInd, halfInd]
    by_cases hu : u ∈ mixHalfS e ε
    · rw [Set.indicator_of_mem (mem_halfPt.2 hu), Finset.prod_congr rfl fun w hw =>
        (congrArg _ ((hco w).2.2.1 u).symm).trans ((hv w hw).2 _ ((hh w hw).2.2.2.2 u).1)]
      by_cases hl : mapA t e u ∈ latA G t i j ∧ mapB e u ∈ latB G i j
      · rw [if_pos ⟨hl.1, hu.1⟩, if_pos ⟨hl.2, hu.2⟩, mul_one, mul_one]
        exact Finset.prod_congr rfl fun w hw => Set.indicator_of_mem (((hh w hw).2.2.2.2 u).2.2 hl.1 hl.2) _
      · have : ∃ w ∈ locPl G t, ofMaps t e (atPl w 1 • mapA t e u, atPl w 1 • mapB e u) ∉ latPtS t e (w.under (𝓞 D.host.F)) := by
          by_contra! hall
          exact hl ⟨mem_of_sum_smul (hεs ▸ hu.1) fun w hw => (mapA_ofMaps t e _ ▸ (hall w hw).2.1 :),
            mem_of_sum_smul (hεs ▸ hu.2) fun w hw => (mapB_ofMaps t e _ ▸ (hall w hw).2.2 :)⟩
        obtain ⟨w, hw, hn⟩ := this
        rw [Finset.prod_eq_zero hw (Set.indicator_of_notMem hn _)]
        rcases not_and_or.1 hl with hl | hl
        · rw [if_neg fun h => hl h.1, zero_mul, mul_zero]
        · rw [if_neg fun h : _ ∧ IsHalf ε (mapB e u) => hl h.1, mul_zero, mul_zero]
    · rw [Set.indicator_of_notMem (mt mem_halfPt.1 hu)]
      rcases not_and_or.1 hu with hl | hl
      · rw [if_neg fun h => hl h.2, zero_mul, mul_zero]
      · rw [if_neg fun h : _ ∧ IsHalf ε (mapB e u) => hl h.2, mul_zero, mul_zero]
  have hR := GlobalTheory.T.heisenbergStableRelation_of_vacua Γ.M' W.ψ hstd hG (locPl G t) (fun w => w.under (𝓞 D.host.F)) (Good.under_injOn hL G t) _
    (fun w => mixHalfS e (atPl w 1)) (fun w => mixHalfS e (cA D (atPl w 1))) (mixCoS B t e) I (halfPt t e ε) R (c • f)
    hI (fun w hw u hu => ⟨(hh w hw).1 u hu, mem_halfPt.2 (hA w hw u hu)⟩) (fun w hw => (hh w hw).2.1)
    (fun w hw => (hh w hw).2.2.1) (fun w _ x _ u => (hco w).1 u x)
    (fun w _ w' _ hne x hx u => by rw [(hco w').1, (hco w').2.2.2 w hne.symm x hx, add_zero])
    (fun w hw u => ⟨_, ((hh w hw).2.2.2.2 u).1, (hco w).2.2.1 u, ((hh w hw).2.2.2.2 u).2.1⟩)
    (fun w hw x hx p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd x _ hp.1, by
      have := g1 x (hA w hw x hx) _ hp.2
      rwa [← thetaS_rho] at this⟩)
    (fun w hw x hx p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd x _ hp.1, by
      have := g2 x (hA' w hw x hx) _ hp.2
      rwa [← thetaS_rho] at this⟩)
    ⟨(isFinPart_vac hG ∅).fam.mem hG _, by
      have := (boxGraph t e ε T₁ T₂).smul_mem c (Submodule.subset_span
        ⟨_, _, GlobalTheory.isSBHalf_halfInd ε _, GlobalTheory.isSBHalf_halfInd ε _, rfl⟩)
      rw [(congrArg T₁ (one_smul ℂ _).symm).trans hT₁.vac, (congrArg T₂ (one_smul ℂ _).symm).trans hT₂.vac] at this
      show (_, thetaS Γ W.ψ _) ∈ _
      rw [hbase, hb]
      exact this⟩
    φ hφ.1 fun v hv => hφ.2 v fun hm => let ⟨w, hw, e⟩ := (hti.1.2.2.1 v).1 hm; hv w hw e
  have hτ : (∑ d ∈ τ.support, τ d • (boxS t e (φ₁ d) (φ₂ d), boxS t e d.1.2 d.2)) ∈ boxGraph t e ε T₁ T₂ :=
    sum_mem fun d hd => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, (hmem d hd).1.1, (hmem d hd).2.1, by
      rw [← (hmem d hd).1.2.2 T₁ hT₁, ← (hmem d hd).2.2.2 T₂ hT₂]⟩)
  have hfst : (Set.indicator (halfPt t e ε : Set _) fun u => ∏ w ∈ locPl G t, I w (φ _) (mixCoS B t e w u)) =
      (∑ d ∈ τ.support, τ d • (boxS t e (φ₁ d) (φ₂ d), boxS t e d.1.2 d.2)).1 := by
    funext u
    rw [Prod.fst_sum, Finset.sum_apply]
    by_cases hu : u ∈ mixHalfS e ε
    · rw [Set.indicator_of_mem (mem_halfPt.2 hu), Finset.prod_congr rfl fun w hw => congrFun (hΨ w hw) _]
      exact (hsum _ _ hu.1 hu.2).symm
    · rw [Set.indicator_of_notMem (mt mem_halfPt.1 hu)]
      refine (Finset.sum_eq_zero fun d hd => mul_eq_zero_of_right _ ?_).symm
      by_contra hne
      exact hu ⟨(hmem d hd).1.1.1 _ (left_ne_zero_of_mul hne), (hmem d hd).2.1.1 _ (right_ne_zero_of_mul hne)⟩
  refine ⟨hR.1, fun u => ?_⟩
  have := g0 _ (by
    have := sub_mem hR.2 hτ
    rwa [← Prod.mk.eta (p := Finset.sum _ _), Prod.mk_sub_mk, ← hfst, sub_self] at this)
  have := congrFun (sub_eq_zero.1 this) u
  rw [Prod.snd_sum, Finset.sum_apply] at this
  exact this

end GlobalTheory.SmallPlaces

end

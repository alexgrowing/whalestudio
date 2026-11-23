import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.BigDat

section Halves

variable {D : D7}

theorem hO_cA_smul (S₁ S₂ : HSp D) (a : AE D) (z y : WO S₁ S₂) : hO S₁ S₂ z (cA D a • y) = hO S₁ S₂ (a • z) y := by
  unfold hO
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun s _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, GlobalTheory.DualPairCheck.cA_cA]
  ring

theorem symplO_cA_smul (S₁ S₂ : HSp D) (a : AE D) (z y : WO S₁ S₂) :
    symplO S₁ S₂ z (cA D a • y) = symplO S₁ S₂ (a • z) y := by
  unfold symplO
  rw [hO_cA_smul]

theorem symplO_zero_right' (S₁ S₂ : HSp D) (z : WO S₁ S₂) : symplO S₁ S₂ z 0 = 0 := by
  simp [symplO, hO]

theorem isHalf_smul_self {m n : ℕ} {b : AE D} (hb : b * b = b) (x : Matrix (Fin m) (Fin n) (AE D)) : IsHalf b (b • x) :=
  fun p q => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hb]

theorem smul_of_isHalf {m n : ℕ} {b : AE D} {x : Matrix (Fin m) (Fin n) (AE D)} (hx : IsHalf b x) : b • x = x :=
  Matrix.ext fun p q => hx p q

theorem smul_eq_zero_of_isHalf (v : Pl D.host.F) {b : AE D}
    (hb : b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = b) {m n : ℕ} {x : Matrix (Fin m) (Fin n) (AE D)}
    (hx : IsHalf b x) (c : AF D.host.F) (hc : evFin D.host.F v c = 0) : c • x = 0 := by
  have h0 : c * GlobalTheory.LatVac.liftV v 1 = 0 := GlobalTheory.LatVac.at_liftV v 1 c hc
  ext p q
  rw [Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def]
  have e : algebraMap (AF D.host.F) (AE D) c * x p q =
      b * algebraMap (AF D.host.F) (AE D) (c * GlobalTheory.LatVac.liftV v 1) * x p q := by
    conv_lhs => rw [← hx p q, ← hb]
    rw [map_mul]
    ring
  rw [e, h0, map_zero, mul_zero, zero_mul]

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem at_of_mixHalf (e : Num G i j) (v : Pl D.host.F) {b : AE D}
    (hb : b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = b) {u : Pt G i j} (hu : u ∈ mixHalf e b) :
    At (evFin D.host.F v) u := by
  intro c hc
  apply (maps e).injective
  rw [map_smul, map_zero, maps_apply, Prod.smul_mk, smul_eq_zero_of_isHalf v hb hu.1 c hc,
    smul_eq_zero_of_isHalf v hb hu.2 c hc, Prod.mk_zero_zero]

theorem ofMaps_smul_mem (e : Num G i j) {b : AE D} (hb : b * b = b) (x₁ : HomV G i j) (x₂ : HomW G i j) :
    ofMaps e (b • x₁, b • x₂) ∈ mixHalf e b := by
  refine ⟨?_, ?_⟩
  · show IsHalf b (mapV e (ofMaps e _))
    rw [mapV_ofMaps]
    exact isHalf_smul_self hb _
  · show IsHalf b (mapW e (ofMaps e _))
    rw [mapW_ofMaps]
    exact isHalf_smul_self hb _

theorem ofMaps_add_ofMaps (e : Num G i j) (v : Pl D.host.F) {a : AE D}
    (hsum : a + cA D a = algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1)) {u : Pt G i j}
    (hu : At (evFin D.host.F v) u) :
    ofMaps e (a • mapV e u, a • mapW e u) + ofMaps e (cA D a • mapV e u, cA D a • mapW e u) = u := by
  have h1 : (1 - GlobalTheory.LatVac.liftV v 1) • u = 0 :=
    hu _ (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  have hℓu : GlobalTheory.LatVac.liftV v 1 • u = u := by
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    exact h1.symm
  apply (maps e).injective
  refine Prod.ext ?_ ?_
  · show mapV e (_ + _) = mapV e u
    rw [mapV_add, mapV_ofMaps, mapV_ofMaps, ← add_smul, hsum, algebraMap_smul, ← mapV_smul, hℓu]
  · show mapW e (_ + _) = mapW e u
    rw [mapW_add, mapW_ofMaps, mapW_ofMaps, ← add_smul, hsum, algebraMap_smul, ← mapW_smul, hℓu]

theorem infPart_algebraMap_liftV (v : Pl D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1)) = 0 :=
  GlobalTheory.LatVac.infPart_pair (GlobalTheory.AdelicU.singleFin v 1) 1

theorem map_infPart_of_isHalf (v : Pl D.host.F) {b : AE D}
    (hb : b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = b) {m n : ℕ} {x : Matrix (Fin m) (Fin n) (AE D)}
    (hx : IsHalf b x) : x.map (infPart D) = 0 := by
  ext p q
  rw [Matrix.map_apply, Matrix.zero_apply, ← hx p q, ← hb, map_mul, map_mul, infPart_algebraMap_liftV, mul_zero, zero_mul]

theorem mapV_mem_latV_of_char (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram)
    (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e) {ψ : AddChar (AF D.host.F) ℂ} (hstd : IsStdChar D ψ (-1))
    (hS : IsSelfDualC (negSp (spW G i j)) (G.Λ (.grid (i + 1) (j + 1))))
    (hT : IsSelfDualC (spV G i j) (G.Λ (.grid i (j + 1)))) (v : Pl D.host.F) {a : AE D}
    (ha1 : a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = a) (hcc : cA D a * cA D a = cA D a)
    (hc1 : cA D a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = cA D a) (hfc : finPart D (cA D a) ∈ intAE D)
    {x : Pt G i j} (hx : x ∈ mixHalf e a)
    (hψ : ∀ y ∈ latPt e v, y ∈ mixHalf e (cA D a) → ψ (sympPt Γ x y) = 1) : mapV e x ∈ latV G i j := by
  refine GlobalTheory.LatVac.mem_of_char hstd hS hT (map_infPart_of_isHalf v ha1 hx.1) fun l hl => ?_
  have hy : ofMaps e (cA D a • l, (0 : HomW G i j)) ∈ mixHalf e (cA D a) := by
    refine ⟨?_, ?_⟩
    · show IsHalf _ (mapV e (ofMaps e _))
      rw [mapV_ofMaps]
      exact isHalf_smul_self hcc _
    · show IsHalf _ (mapW e (ofMaps e _))
      rw [mapW_ofMaps]
      exact fun p q => mul_zero _
  have hyl : ofMaps e (cA D a • l, (0 : HomW G i j)) ∈ latPt e v := by
    refine ⟨at_of_mixHalf e v hc1 hy, ?_, ?_⟩
    · show mapV e (ofMaps e _) ∈ latV G i j
      rw [mapV_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfc l hl
    · show mapW e (ofMaps e _) ∈ latW G i j
      rw [mapW_ofMaps]
      exact zero_mem _
  have h := hψ _ hyl hy
  rw [symp_eq e Γ hW hWW, mapV_ofMaps, mapW_ofMaps, symplO_cA_smul, smul_of_isHalf hx.1, symplO_zero_right',
    add_zero] at h
  exact h

theorem mapW_mem_latW_of_char (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram)
    (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e) {ψ : AddChar (AF D.host.F) ℂ} (hstd : IsStdChar D ψ (-1))
    (hS : IsSelfDualC (spV₁ G i j) (G.Λ (.grid (i + 1) j)))
    (hT : IsSelfDualC (spW G i j) (G.Λ (.grid (i + 1) (j + 1)))) (v : Pl D.host.F) {a : AE D}
    (ha1 : a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = a) (hcc : cA D a * cA D a = cA D a)
    (hc1 : cA D a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = cA D a) (hfc : finPart D (cA D a) ∈ intAE D)
    {x : Pt G i j} (hx : x ∈ mixHalf e a)
    (hψ : ∀ y ∈ latPt e v, y ∈ mixHalf e (cA D a) → ψ (sympPt Γ x y) = 1) : mapW e x ∈ latW G i j := by
  refine GlobalTheory.LatVac.mem_of_char hstd hS hT (map_infPart_of_isHalf v ha1 hx.2) fun l hl => ?_
  have hy : ofMaps e ((0 : HomV G i j), cA D a • l) ∈ mixHalf e (cA D a) := by
    refine ⟨?_, ?_⟩
    · show IsHalf _ (mapV e (ofMaps e _))
      rw [mapV_ofMaps]
      exact fun p q => mul_zero _
    · show IsHalf _ (mapW e (ofMaps e _))
      rw [mapW_ofMaps]
      exact isHalf_smul_self hcc _
  have hyl : ofMaps e ((0 : HomV G i j), cA D a • l) ∈ latPt e v := by
    refine ⟨at_of_mixHalf e v hc1 hy, ?_, ?_⟩
    · show mapV e (ofMaps e _) ∈ latV G i j
      rw [mapV_ofMaps]
      exact zero_mem _
    · show mapW e (ofMaps e _) ∈ latW G i j
      rw [mapW_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfc l hl
  have h := hψ _ hyl hy
  rw [symp_eq e Γ hW hWW, mapV_ofMaps, mapW_ofMaps, symplO_cA_smul, smul_of_isHalf hx.2, symplO_zero_right',
    zero_add] at h
  exact h

theorem halves_split : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e → ∀ (v : Pl D.host.F) (a : AE D), IsSplitIdem D a →
    a + cA D a = algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) →
    (∀ u ∈ mixHalf e a, At (evFin D.host.F v) u) ∧ (∀ u ∈ mixHalf e (cA D a), At (evFin D.host.F v) u) ∧
    (∀ u : Pt G i j, At (evFin D.host.F v) u → ∃ x ∈ mixHalf e a, ∃ y ∈ mixHalf e (cA D a), u = x + y) ∧
    (∀ x ∈ mixHalf e a, (∀ y ∈ latPt e v, y ∈ mixHalf e (cA D a) → W.ψ (sympPt Γ x y) = 1) → x ∈ latPt e v) ∧
    ∀ u : Pt G i j, ofMaps e (a • mapV e u, a • mapW e u) ∈ mixHalf e a ∧
      (∀ y ∈ mixHalf e (cA D a), sympPt Γ u y = sympPt Γ (ofMaps e (a • mapV e u, a • mapW e u)) y) ∧
      (mapV e u ∈ latV G i j → mapW e u ∈ latW G i j → ofMaps e (a • mapV e u, a • mapW e u) ∈ latPt e v) := by
  intro D T L sc G μ₀ hL W i j e Γ hW hWW v a ha hsum
  obtain ⟨haa, hac, -⟩ := ha
  have hcc : cA D a * cA D a = cA D a := by rw [← map_mul, haa]
  have hca : cA D a * a = 0 := by rw [mul_comm, hac]
  have ha1 : a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = a := by
    rw [← hsum, mul_add, haa, hac, add_zero]
  have hc1 : cA D a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = cA D a := by
    rw [← hsum, mul_add, hca, hcc, zero_add]
  have hfa : finPart D a ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, haa])
  have hfc : finPart D (cA D a) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hcc])
  have hS : IsSelfDualC (negSp (spW G i j)) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) :=
    isSelfDualC_neg (node_isV G hL (X := .grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).sd
  have hT : IsSelfDualC (spV G i j) (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have hS₁ : IsSelfDualC (spV₁ G i j) (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  have hT₁ : IsSelfDualC (spW G i j) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).sd
  refine ⟨fun u hu => at_of_mixHalf e v ha1 hu, fun u hu => at_of_mixHalf e v hc1 hu, fun u hu =>
    ⟨_, ofMaps_smul_mem e haa _ _, _, ofMaps_smul_mem e hcc _ _, (ofMaps_add_ofMaps e v hsum hu).symm⟩,
    fun x hx hψ => ⟨at_of_mixHalf e v ha1 hx,
      mapV_mem_latV_of_char e Γ hW hWW W.ψ_std hS hT v ha1 hcc hc1 hfc hx hψ,
      mapW_mem_latW_of_char e Γ hW hWW W.ψ_std hS₁ hT₁ v ha1 hcc hc1 hfc hx hψ⟩, fun u => ?_⟩
  refine ⟨ofMaps_smul_mem e haa _ _, fun y hy => ?_, fun hV hW' => ?_⟩
  · rw [symp_eq e Γ hW hWW, symp_eq e Γ hW hWW, mapV_ofMaps, mapW_ofMaps, ← symplO_cA_smul, ← symplO_cA_smul,
      smul_of_isHalf hy.1, smul_of_isHalf hy.2]
  · refine ⟨at_of_mixHalf e v ha1 (ofMaps_smul_mem e haa _ _), ?_, ?_⟩
    · show mapV e (ofMaps e _) ∈ latV G i j
      rw [mapV_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfa _ hV
    · show mapW e (ofMaps e _) ∈ latW G i j
      rw [mapW_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfa _ hW'

end Halves

end GlobalTheory.BigDat

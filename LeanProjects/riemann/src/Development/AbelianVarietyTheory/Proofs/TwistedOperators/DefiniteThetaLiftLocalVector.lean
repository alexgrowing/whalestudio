import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonvanishingFiniteDatumDefiniteLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeOnePrimeReductionSplitPlaceDictionary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentBaseFunctionIdentityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionSplitProductDatumIsPureTensorStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.AdjVecLocal

variable {D : D7}

section Pure

variable {v : FinPl D} {k : Type} [CommRing k] {n a t : ℕ}

def upper {κ : Type} (ht : a + t = n) (y : Matrix (Fin n) (Fin a) κ) : Matrix (Fin a) (Fin a) κ :=
  (rowsTB ht y).submatrix Sum.inl id

theorem topL_eq_upper {κ : Type} [Zero κ] (ht : a + t = n) (y : Matrix (Fin n) (Fin a) κ) : topL a y = upper ht y := by
  ext i j
  have h1 : i.val < n ∧ j.val < a := ⟨by omega, j.2⟩
  unfold topL
  rw [dif_pos h1]
  rfl

theorem lowZero_iff {κ : Type} [Zero κ] (ht : a + t = n) (y : Matrix (Fin n) (Fin a) κ) :
    LowZero a y ↔ ∀ i j, rowsTB ht y (Sum.inr i) j = 0 := by
  constructor
  · intro h i j
    exact h _ j (Nat.le_add_right _ _) j.2
  · intro h i j hi _
    have := h ⟨i.val - a, by omega⟩ j
    have e : i = Fin.cast ht (finSumFinEquiv (Sum.inr ⟨i.val - a, by omega⟩)) := Fin.ext (by simp; omega)
    rw [e]
    exact this

theorem int_of_phi_ne_zero (ht : a + t = n) (P : Subgroup (GL (Fin a) (v.adicCompletionIntegers D.host.F))) (lam : P →* ℂˣ)
    (mu : (Fv D.host.F v)ˣ →* ℂˣ) (u : Matrix (Fin n) (Fin a) (Fv D.host.F v))
    (h : localNewformFunction v P lam mu (rowsTB ht u) ≠ 0) (i : Fin n) (j : Fin a) : u i j ∈ v.adicCompletionIntegers D.host.F := by
  unfold localNewformFunction at h
  split_ifs at h with hc
  · obtain ⟨⟨g, hg⟩, h2⟩ := hc
    have key : ∀ s, rowsTB ht u s j ∈ v.adicCompletionIntegers D.host.F := by
      rintro (s | s)
      · have := congrFun (congrFun hg s) j
        exact (show _ = rowsTB ht u (Sum.inl s) j from this) ▸ Subtype.property _
      · exact (h2 s j).1
    simpa [rowsTB] using key (finSumFinEquiv.symm (Fin.cast ht.symm i))
  · exact absurd rfl h

variable (r : v.adicCompletionIntegers D.host.F →+* k)
  (hr : ∀ x : v.adicCompletionIntegers D.host.F, r x = 0 ↔ Valued.v (x : Fv D.host.F v) < 1)
include hr

theorem phi_pos (ht : a + t = n) (P : Subgroup (GL (Fin a) (v.adicCompletionIntegers D.host.F)))
    (mu : (Fv D.host.F v)ˣ →* ℂˣ) (y : Matrix (Fin n) (Fin a) (v.adicCompletionIntegers D.host.F))
    (g : GL (Fin a) (v.adicCompletionIntegers D.host.F)) (hg : g ∈ P) (hy : g.val = upper ht y)
    (hl : LowZero a (y.map r)) :
    localNewformFunction v P 1 mu (rowsTB ht (y.map (algebraMap _ (Fv D.host.F v)))) =
      ((mu (Units.map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)).toMonoidHom
        (Matrix.GeneralLinearGroup.det g)) : ℂˣ) : ℂ)⁻¹ := by
  unfold localNewformFunction
  have h : ∃ k : P, ((k : GL (Fin a) (v.adicCompletionIntegers D.host.F)) : Matrix (Fin a) (Fin a) _).map
      (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)) =
      (rowsTB ht (y.map (algebraMap _ (Fv D.host.F v)))).submatrix Sum.inl id := ⟨⟨g, hg⟩, by rw [hy]; rfl⟩
  rw [dif_pos ⟨h, fun i j => ⟨Subtype.property _, (hr _).1 ((lowZero_iff ht _).1 hl i j)⟩⟩]
  have e : (h.choose : GL (Fin a) (v.adicCompletionIntegers D.host.F)) = g := by
    refine Units.ext (Matrix.ext fun i j => Subtype.ext ?_)
    rw [hy]
    exact congrFun (congrFun h.choose_spec i) j
  rw [e]
  simp

theorem phi_neg (ht : a + t = n) (P : Subgroup (GL (Fin a) (v.adicCompletionIntegers D.host.F)))
    (mu : (Fv D.host.F v)ˣ →* ℂˣ) (y : Matrix (Fin n) (Fin a) (v.adicCompletionIntegers D.host.F))
    (h : ¬ (LowZero a (y.map r) ∧ ∃ g ∈ P, g.val = upper ht y)) :
    localNewformFunction v P 1 mu (rowsTB ht (y.map (algebraMap _ (Fv D.host.F v)))) = 0 := by
  unfold localNewformFunction
  rw [dif_neg]
  rintro ⟨⟨g, hg⟩, h2⟩
  exact h ⟨(lowZero_iff ht _).2 fun i j => (hr _).2 (h2 i j).2, g, g.2,
    Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hg i) j)⟩

theorem red_eq_zero_iff (x : v.adicCompletionIntegers D.host.F) : r x = 0 ↔ IsLocalRing.residue _ x = 0 := by
  rw [hr, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  exact ((Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one)

theorem isUnit_of_red {x : v.adicCompletionIntegers D.host.F} (h : IsUnit (r x)) : IsUnit x := by
  by_contra hx
  have h0 : r x = 0 := (red_eq_zero_iff r hr x).2 ((IsLocalRing.residue_eq_zero_iff _).2 hx)
  rw [h0, isUnit_zero_iff] at h
  have := (hr 1).1 (by rw [map_one, h])
  simp at this

theorem map_eq_one_iff (z : Matrix (Fin a) (Fin a) (v.adicCompletionIntegers D.host.F)) :
    z.map r = 1 ↔ z.map (IsLocalRing.residue _) = 1 := by
  have : ∀ {k' : Type} [CommRing k'] (s : v.adicCompletionIntegers D.host.F →+* k'),
      z.map s = 1 ↔ ∀ i j, s ((z - 1) i j) = 0 := fun s => by
    rw [← Matrix.map_one s (map_zero s) (map_one s), ← Matrix.ext_iff]
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, sub_eq_zero]
  rw [this, this]
  simp only [red_eq_zero_iff r hr]

open Classical in

theorem phi_princ (ht : a + t = n) (mu : (Fv D.host.F v)ˣ →* ℂˣ)
    (hmu : ∀ u : (Fv D.host.F v)ˣ, Valued.v ((u : Fv D.host.F v) - 1) < 1 → mu u = 1)
    (y : Matrix (Fin n) (Fin a) (v.adicCompletionIntegers D.host.F)) :
    localNewformFunction v (princ v a) 1 mu (rowsTB ht (y.map (algebraMap _ (Fv D.host.F v)))) =
      if LowZero a (y.map r) ∧ topL a (y.map r) = 1 then 1 else 0 := by
  have e : topL a (y.map r) = (upper ht y).map r := topL_eq_upper ht _
  rw [e]
  split_ifs with h
  · have hd : r (upper ht y).det = 1 := by rw [RingHom.map_det, RingHom.mapMatrix_apply, h.2, det_one]
    have hu : IsUnit (upper ht y) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_red r hr (hd ▸ isUnit_one))
    rw [phi_pos r hr ht _ mu y hu.unit (Units.ext ((map_eq_one_iff r hr _).1 h.2)) rfl h.1, hmu]
    · simp
    · exact (hr ((upper ht y).det - 1)).1 (by rw [map_sub, hd, map_one, sub_self])
  · refine phi_neg r hr ht _ mu y fun ⟨h1, g, hg, h2⟩ => h ⟨h1, (map_eq_one_iff r hr _).2 ?_⟩
    rw [← h2]
    exact congrArg Units.val hg

open Classical in

theorem phi_top (ht : a + t = n) (mu : (Fv D.host.F v)ˣ →* ℂˣ) (ξ : kˣ →* ℂˣ)
    (hmu : ∀ (u : (Fv D.host.F v)ˣ) (b : kˣ) (h : (u : Fv D.host.F v) ∈ v.adicCompletionIntegers D.host.F),
      r ⟨u, h⟩ = b → mu u = ξ b)
    (y : Matrix (Fin n) (Fin a) (v.adicCompletionIntegers D.host.F)) :
    localNewformFunction v ⊤ 1 mu (rowsTB ht (y.map (algebraMap _ (Fv D.host.F v)))) =
      if h : LowZero a (y.map r) ∧ IsUnit (topL a (y.map r)).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0 := by
  have e : (topL a (y.map r)).det = r (upper ht y).det := by
    rw [RingHom.map_det, topL_eq_upper ht]; rfl
  split_ifs with h
  · have hu : IsUnit (upper ht y) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_red r hr (e ▸ h.2))
    have key : ∀ (w : (v.adicCompletionIntegers D.host.F)ˣ) (b : kˣ), r w = b →
        mu (Units.map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)).toMonoidHom w) = ξ b :=
      fun w b hw => hmu _ b (Subtype.property w.val) hw
    rw [phi_pos r hr ht _ mu y hu.unit (Subgroup.mem_top _) hu.unit_spec h.1, _root_.zpow_neg_one, key _ h.2.unit]
    rw [Matrix.GeneralLinearGroup.val_det_apply, hu.unit_spec, IsUnit.unit_spec, e]
  · refine phi_neg r hr ht _ mu y fun ⟨h1, g, _, h2⟩ => h ⟨h1, ?_⟩
    rw [e, ← h2]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).map r

end Pure

section Local

open Classical in

def locK {k : Type} [CommRing k] {n a : ℕ} (y : Matrix (Fin n) (Fin a) k) : ℂ :=
  if LowZero a y ∧ topL a y = 1 then 1 else 0

open Classical in

def locQ {k : Type} [CommRing k] {n a : ℕ} (ξ : kˣ →* ℂˣ) (y : Matrix (Fin n) (Fin a) k) : ℂ :=
  if h : LowZero a y ∧ IsUnit (topL a y).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0

theorem omegaK_eq {n a : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin n) (Fin a) (Formalism.L2.DIV.kP PP)) :
    omegaK Pg y = ∏ PP ∈ Pg, locK (y PP) := by
  unfold omegaK locK
  split_ifs with h
  · exact (Finset.prod_eq_one fun PP hPP => if_pos (h PP hPP)).symm
  · push_neg at h
    obtain ⟨PP, hPP, h⟩ := h
    exact (Finset.prod_eq_zero hPP (if_neg fun h' => h h'.1 h'.2)).symm

theorem omegaQ_eq {n a : ℕ} (Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin n) (Fin a) (Formalism.L2.DIV.kP PP)) :
    omegaQ Q a ξ (-1) y = ∏ PP ∈ Q, locQ (ξ PP) (y PP) := by
  unfold omegaQ
  split_ifs with h
  · rw [← Finset.prod_attach Q]
    exact Finset.prod_congr rfl fun PP _ => by rw [locQ, dif_pos (h PP.1 PP.2)]
  · obtain ⟨PP, h⟩ := not_forall.1 h
    obtain ⟨hPP, h⟩ := Classical.not_imp.1 h
    exact (Finset.prod_eq_zero hPP (dif_neg h)).symm

variable (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))

theorem frMapAdj_smul (e : AE D) (x : WO S T) :
    frMapAdj S T βS βT (cA D e • x) = toEAf D e • frMapAdj S T βS βT x := by
  have h : (((cA D e • x).map (toEAf D)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      toEAf D e • ((x.map (toEAf D)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ := Matrix.ext fun i j => by
    change GlobalTheory.AdelicLatMove.cF D (toEAf D (cA D e * x j i)) = toEAf D e * GlobalTheory.AdelicLatMove.cF D (toEAf D (x j i))
    rw [RingHom.map_mul, RingHom.map_mul, GlobalTheory.AdelicLatMove.toEAf_cA, GlobalTheory.PlaceVec.cF_cF_toEAf]
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.frMapAdj_eq, h, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_half {e : AE D} {x : WO S T} (hx : IsHalf (cA D e) x) (i : Fin S.rank) (j : Fin T.rank) :
    toEAf D e * frMapAdj S T βS βT x i j = frMapAdj S T βS βT x i j := by
  have h : cA D e • x = x := Matrix.ext hx
  have := frMapAdj_smul S T βS βT e x
  rw [h] at this
  exact (congrFun (congrFun this i) j).symm

theorem adjCo_eq {v : FinPl D} (φ : SplitProj D v) (hφ : ∀ a : AE D, rdE φ (toEAf D a) = rdA φ a) (x : WO S T) :
    adjCo φ S T (frCo φ βS) (frCo φ βT) x = (frMapAdj S T βS βT x).map (rdE φ) := by
  unfold adjCo frMapAdj
  rw [Matrix.map_mul (f := rdE φ), Matrix.map_mul (f := rdE φ), Matrix.map_map,
    show (rdE φ) ∘ (toEAf D) = rdA φ from funext hφ]
  rfl

theorem mem_int_of_rdE {v : FinPl D} {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) {N : EAf D}
    (hN : toEAf D e * N = N) (h : rdE φ N ∈ v.adicCompletionIntegers D.host.F) :
    N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨hc, hφ, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  obtain ⟨w, rfl⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective N
  rw [← hN, ← RingHom.map_mul]
  rw [hφ] at h
  exact GlobalTheory.IdemRes.toEAf_mem_of_finPart ((hc.2.2.2 w).2 (GlobalTheory.SplitHecke.isInt_Ov.2 h))

open Classical in

def redFun (a : AE D) (PP : Formalism.L2.DIV.Pl D.host.E) (ω : Matrix (Fin S.rank) (Fin T.rank) (Formalism.L2.DIV.kP PP) → ℂ) :
    WO S T → ℂ :=
  fun x => if IsHalf a x ∧ IsIntM (frMapAdj S T βS βT x) then ω (redM PP (frMapAdj S T βS βT x)) else 0

theorem onHalfAdj_eq {v : FinPl D} {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP)
    (hr : ∀ (N : EAf D) (hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∃ h : rdE φ N ∈ v.adicCompletionIntegers D.host.F,
      r ⟨rdE φ N, h⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨N, hN⟩)
    (Φ : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) → ℂ)
    (ω : Matrix (Fin S.rank) (Fin T.rank) (Formalism.L2.DIV.kP PP) → ℂ)
    (h0 : ∀ u, Φ u ≠ 0 → ∀ i j, u i j ∈ v.adicCompletionIntegers D.host.F)
    (h1 : ∀ y : Matrix (Fin S.rank) (Fin T.rank) (v.adicCompletionIntegers D.host.F),
      Φ (y.map (algebraMap _ (Fv D.host.F v))) = ω (y.map r)) :
    onHalfAdj φ S T (frCo φ βS) (frCo φ βT) e Φ = redFun S T βS βT (cA D e) PP ω := by
  funext x
  unfold onHalfAdj redFun
  rw [adjCo_eq S T βS βT φ (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).2.1]
  by_cases hx : IsHalf (cA D e) x
  · rw [if_pos hx]
    by_cases hi : IsIntM (frMapAdj S T βS βT x)
    · rw [if_pos ⟨hx, hi⟩]
      choose h hh using fun i j => hr _ (hi i j)
      refine (h1 (Matrix.of fun i j => ⟨_, h i j⟩)).trans (congrArg ω (Matrix.ext fun i j => ?_))
      exact (hh i j).trans (by rw [redM, dif_pos (hi i j)])
    · rw [if_neg fun h => hi h.2]
      by_contra hne
      exact hi fun i j => mem_int_of_rdE he (frMapAdj_half S T βS βT hx i j) (h0 _ hne i j)
  · rw [if_neg hx, if_neg fun h => hx h.1]

theorem onHalfAdj_princ {v : FinPl D} {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) {PP : Formalism.L2.DIV.Pl D.host.E}
    (hP : IsProjAt φ PP) {t : ℕ} (ht : T.rank + t = S.rank) (mu : (Fv D.host.F v)ˣ →* ℂˣ)
    (hmu : ∀ u : (Fv D.host.F v)ˣ, Valued.v ((u : Fv D.host.F v) - 1) < 1 → mu u = 1) :
    onHalfAdj φ S T (frCo φ βS) (frCo φ βT) e (fun u => localNewformFunction v (princ v T.rank) 1 mu (rowsTB ht u)) =
      redFun S T βS βT (cA D e) PP locK := by
  obtain ⟨⟨r, -, h1, -, h3⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hP
  exact onHalfAdj_eq S T βS βT he PP r h3 _ _ (int_of_phi_ne_zero ht _ _ _) (phi_princ r h1 ht mu hmu)

theorem onHalfAdj_top {v : FinPl D} {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) {PP : Formalism.L2.DIV.Pl D.host.E}
    (hP : IsProjAt φ PP) {t : ℕ} (ht : T.rank + t = S.rank) (mu : (Fv D.host.F v)ˣ →* ℂˣ)
    (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (hmu : LiftsChar φ PP mu ξ) :
    onHalfAdj φ S T (frCo φ βS) (frCo φ βT) e (fun u => localNewformFunction v ⊤ 1 mu (rowsTB ht u)) =
      redFun S T βS βT (cA D e) PP (locQ ξ) := by
  obtain ⟨⟨r, -, h1, h2, h3⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hP
  exact onHalfAdj_eq S T βS βT he PP r h3 _ _ (int_of_phi_ne_zero ht _ _ _)
    (phi_top r h1 ht mu ξ fun u b h hb => hmu u b ((h2 _ _).2 ⟨h, hb⟩))

theorem isSBHalf_redFun {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {a : AE D}
    (ha : infPart D a = 0) (PP : Formalism.L2.DIV.Pl D.host.E) (ω : Matrix (Fin S.rank) (Fin T.rank) (Formalism.L2.DIV.kP PP) → ℂ) :
    IsSBHalf a (latO S T ΛS ΛT fun _ => True) (redFun S T βS βT a PP ω) :=
  GlobalTheory.PlaceVec.isSBHalf_of_red hS.1 hT.1 ha (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)
    (GlobalTheory.PlaceVec.frMapAdj_up S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_down S T βS βT) {PP} (fun y => ω (y PP))
    fun _ _ h => by rw [h PP (Finset.mem_singleton_self _)]

open Classical in

theorem prod_redFun (s : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D)
    (hes : ∀ PP ∈ s, Formalism.L2.NTheta.IsIdemAt (es PP) PP)
    (ω : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (Formalism.L2.DIV.kP PP) → ℂ) (x : WO S T)
    (hx : IsHalf (cA D (∑ PP ∈ s, es PP)) x) :
    ∏ PP ∈ s, redFun S T βS βT (cA D (es PP)) PP (ω PP) (cA D (es PP) • x) =
      if IsIntM (frMapAdj S T βS βT x) then ∏ PP ∈ s, ω PP (redM PP (frMapAdj S T βS βT x)) else 0 := by
  split_ifs with hi
  · refine Finset.prod_congr rfl fun PP hPP => ?_
    obtain ⟨h1, h2⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (hes PP hPP)
    have h3 : IsIntM (toEAf D (es PP) • frMapAdj S T βS βT x) := fun i j => mul_mem h1 (hi i j)
    have h4 : IsHalf (cA D (es PP)) (cA D (es PP) • x) := fun i j => by
      change cA D (es PP) * (cA D (es PP) * x i j) = cA D (es PP) * x i j
      rw [← mul_assoc, ← RingHom.map_mul, (hes PP hPP).1.1]
    unfold redFun
    rw [frMapAdj_smul, if_pos ⟨h4, h3⟩]
    refine congrArg (ω PP) (Matrix.ext fun i j => ?_)
    refine (dif_pos (h3 i j)).trans (Eq.trans ?_ (dif_pos (hi i j)).symm)
    have := (Formalism.L2.DIV.resS D.host.F PP).map_mul ⟨_, h1⟩ ⟨_, hi i j⟩
    rw [h2, one_mul] at this
    exact this
  · have : ∃ PP ∈ s, ¬ IsIntM (toEAf D (es PP) • frMapAdj S T βS βT x) := by
      by_contra h
      push_neg at h
      refine hi fun i j => ?_
      rw [← frMapAdj_half S T βS βT hx i j, map_sum, Finset.sum_mul]
      exact sum_mem fun PP hPP => h PP hPP i j
    obtain ⟨PP, hPP, h⟩ := this
    refine Finset.prod_eq_zero hPP ?_
    unfold redFun
    rw [frMapAdj_smul, if_neg fun h' => h h'.2]

end Local

theorem isSplitIdem_cA {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, h3, h4⟩ := h
  refine ⟨by rw [← RingHom.map_mul, h1], ?_, v, ε, h3, ?_⟩
  · rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2]
  · rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h4]

theorem thetaVecLocal : ∀ D : D7, ThetaVecLocal D := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f μ 𝓕 t ht hB hμ _ _ hdis hv
  classical
  obtain ⟨-, e, ⟨⟨es, hes, rfl⟩, hc⟩, hf⟩ := hv
  obtain ⟨d1, d2⟩ := GlobalTheory.SplitIdemDict.idem_dictionary D
  have hS := hB.2.2.1
  have hT := hB.2.2.2.1
  let ω : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (Formalism.L2.DIV.kP PP) → ℂ :=
    fun PP => if PP ∈ Pg then locK else locQ (ξ PP)
  have ω1 : ∀ PP ∈ Pg, ω PP = locK := fun PP h => if_pos h
  have ω2 : ∀ PP ∈ Q, ω PP = locQ (ξ PP) := fun PP h => if_neg fun h' => Finset.disjoint_left.1 hdis h' h
  let v : Formalism.L2.DIV.Pl D.host.E → FinPl D := fun PP => PP.under (𝓞 D.host.F)
  have hvφ : ∀ {w : FinPl D} {φ : SplitProj D w} {PP}, IsProjAt φ PP → w = v PP := fun h =>
    HeightOneSpectrum.ext (d2 _ _ _ h).1.symm
  have hφ : ∀ PP ∈ Pg ∪ Q, ∃ φ : SplitProj D (v PP), IsIdemOf φ (es PP) ∧ IsProjAt φ PP := fun PP h => by
    obtain ⟨w, φ, h1, h2⟩ := d1 _ _ (hes PP h)
    obtain rfl := hvφ h2
    exact ⟨φ, h1, h2⟩
  have hsum : ∀ PP ∈ Pg ∪ Q, es PP + cA D (es PP) = idem D (.inl (v PP)) := fun PP h => (hφ PP h).choose_spec.1.2.1
  have ha : ∀ PP ∈ Pg ∪ Q, IsSplitIdem D (cA D (es PP)) ∧ cA D (es PP) + cA D (cA D (es PP)) = idem D (.inl (v PP)) :=
    fun PP h => ⟨isSplitIdem_cA (hes PP h).1, by rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, hsum PP h]⟩
  have hcross := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es _
    (fun i hi => (hes i hi).1.1) hc
  have hinj : Set.InjOn v (Pg ∪ Q : Finset _) := fun i hi j hj hij => by
    have hi' := Finset.mem_coe.1 hi
    have hj' := Finset.mem_coe.1 hj
    have : es i = es j := GlobalTheory.PlaceDatum.idempotent_eq_of_orthogonal_decomp (hes i hi').1.1 (hes i hi').1.2.1 (hes j hj').1.1 (hes j hj').1.2.1
      (by rw [hsum i hi', hsum j hj', hij]) (hcross i hi' j hj') (hcross j hj' i hi')
    exact GlobalTheory.PlaceVec.isIdemAt_inj (hes i hi') (this ▸ hes j hj')
  have hSB : ∀ PP ∈ Pg ∪ Q, IsSBHalf (cA D (es PP)) (latO S T ΛS ΛT fun _ => True)
      (redFun S T βS βT (cA D (es PP)) PP (ω PP)) := fun PP h =>
    isSBHalf_redFun S T βS βT hS hT (GlobalTheory.SplitScalar.infPart_splitIdem (ha PP h).1) PP _
  refine ⟨?_, fun x hx => ?_⟩
  · choose g hg using fun PP : ↥(Pg ∪ Q) => GlobalTheory.PlaceVec.exists_isThetaAt (base_std hB) hS hT (ha PP.1 PP.2).1.1
      (GlobalTheory.SplitScalar.infPart_splitIdem (ha PP.1 PP.2).1)
      (GlobalTheory.T.split_idempotent_base_function_identity D ψ θ S T sS sT ΛS ΛT f₀ hB _ _ (ha PP.1 PP.2).1 (ha PP.1 PP.2).2).1 (hSB PP.1 PP.2)
    have hi : Function.Injective fun PP : ↥(Pg ∪ Q) => (Sum.inl (v PP.1) : Place D) := fun i j h =>
      Subtype.ext (hinj (Finset.mem_coe.2 i.2) (Finset.mem_coe.2 j.2) (Sum.inl_injective h))
    have key : ∀ (w : FinPl D) (φ : SplitProj D w) (e : AE D), IsIdemOf φ e → ∀ PP ∈ Pg ∪ Q, IsProjAt φ PP →
        IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀
          (redFun S T βS βT (cA D e) PP (ω PP))
          (Function.extend (fun PP : ↥(Pg ∪ Q) => (Sum.inl (v PP.1) : Place D)) g (fun _ => f₀) (.inl w)) := by
      intro w φ e he PP h hP
      obtain rfl := ((d2 _ _ _ hP).2.2 e he).2.1 _ (hes PP h)
      obtain rfl := hvφ hP
      rw [hi.extend_apply g _ ⟨PP, h⟩]
      exact hg ⟨PP, h⟩
    refine ⟨Function.extend (fun PP : ↥(Pg ∪ Q) => (Sum.inl (v PP.1) : Place D)) g fun _ => f₀,
      ⟨fun τ => Function.extend_apply' _ _ _ (by rintro ⟨_, ⟨⟩⟩), fun w hw => Function.extend_apply' _ _ _ ?_⟩,
      fun w φ e he mu => ⟨fun PP h hP hmu => ?_, fun PP h hP hmu => ?_⟩⟩
    · rintro ⟨PP, h⟩
      obtain rfl := Sum.inl_injective h
      exact hw PP.1 PP.2 rfl
    · rw [onHalfAdj_princ S T βS βT he hP ht mu hmu, ← ω1 PP h]
      exact key w φ e he PP (Finset.mem_union_left _ h) hP
    · rw [onHalfAdj_top S T βS βT he hP ht mu _ hmu, ← ω2 PP h]
      exact key w φ e he PP (Finset.mem_union_right _ h) hP
  · obtain ⟨⟨b1, b2⟩, hx⟩ := hx
    have hcs : cA D (∑ PP ∈ Pg ∪ Q, es PP) = ∑ PP ∈ Pg ∪ Q, cA D (es PP) := map_sum _ _ _
    refine GlobalTheory.T.thetaFunction_splitProductDatum_isPureTensor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ _ (Pg ∪ Q) v (fun PP => cA D (es PP)) ha hinj _ hSB x f _
      (fun PP h => ?_) (fun p hp => ?_) (fun y hy => ?_) (fun y hy => ?_) (hcs ▸ hf)
    · obtain ⟨φ, h1, h2⟩ := hφ PP h
      rcases Finset.mem_union.1 h with h | h
      · rw [ω1 PP h, ← onHalfAdj_princ S T βS βT h1 h2 ht 1 fun _ _ => rfl]
        exact (hx _ φ _ h1 1).1 PP h h2 fun _ _ => rfl
      · obtain ⟨mu, hmu⟩ := (GlobalTheory.PlaceRed.red_dict D _ φ PP h2).2 (ξ PP)
        rw [ω2 PP h, ← onHalfAdj_top S T βS βT h1 h2 ht mu _ hmu]
        exact (hx _ φ _ h1 mu).2 PP h h2 hmu
    · rcases p with w | τ
      · exact b2 w fun PP h h' => hp PP h (congrArg Sum.inl (HeightOneSpectrum.ext h'.symm))
      · exact b1 τ
    · rw [prod_redFun S T βS βT _ es hes ω y (hcs ▸ hy)]
      by_cases hi : IsIntM (frMapAdj S T βS βT y)
      · rw [if_pos ⟨hy, hi⟩, if_pos hi, omegaK_eq, omegaQ_eq, Finset.prod_union hdis]
        congr 1
        · exact Finset.prod_congr rfl fun PP h => by rw [ω1 PP h]
        · exact Finset.prod_congr rfl fun PP h => by rw [ω2 PP h]
      · rw [if_neg fun h => hi h.2, if_neg hi]
    · exact if_neg fun h => hy h.1

end GlobalTheory.AdjVecLocal

end

import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarMulSelfOfPair
import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatCopyIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.Move

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

theorem cj_phs (X : RealSide D) (j : Fin D.R.m) : cj (twAt D.what₂.embLL X.A3.A.v0) (X.R.phs j) = 1 := by
  rw [X.phs j, map_one]

theorem isNorm_iff (X : RealSide D) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (ν : ℂ) :
    IsNorm X.R X.geo.v₀ B ν ↔ ν ≠ 0 ∧ ∃ c, IsScale X.R X.geo.v₀ B c ∧ ∃ n : ℕ, n ≠ 0 ∧ ν ^ n = c ^ n := by
  unfold IsNorm
  simp only [cj_phs, one_mul]

theorem CopyTw.rank_eq (h : CopyTw D D' ι e) (j : Fin D.R.m) :
    (Vc D j).rank = (Vc D' (h.cm j)).rank ∧ (Wc D j).rank = (Wc D' (h.cm j)).rank := by
  have key : ∀ {R R' : Ranks} {H : Host R} {H' : Host R'} (s : Spaces R H.F H.E) (s' : Spaces R' H'.F H'.E),
      R = R' → HEq H H' → HEq s s' → ∀ k, (s.V k).rank = (s'.V k).rank ∧ (s.W k).rank = (s'.W k).rank := by
    intro R R' H H' s s' h1 h2 h3 k
    subst h1; cases h2; cases h3
    exact ⟨rfl, rfl⟩
  exact key D.sp D'.sp h.gal.R h.gal.host h.sp _

theorem CopyTw.glr_eq (h : CopyTw D D' ι e) (j : Fin D.R.m) : GLR D (Vc D j).rank = GLR D' (Vc D' (h.cm j)).rank := by
  show (D.what₂.Tau → GL (Fin (Vc D j).rank) ℂ) = (D'.what₂.Tau → GL (Fin (Vc D' (h.cm j)).rank) ℂ)
  rw [h.Tau, (h.rank_eq j).1]

theorem CopyTw.pol_eq (h : CopyTw D D' ι e) (j : Fin D.R.m) :
    Formalism.L2.DIV.Pol D'.what₂.LL D.what₂.Tau (Vc D j).rank = Formalism.L2.DIV.Pol D'.what₂.LL D'.what₂.Tau (Vc D' (h.cm j)).rank := by
  rw [h.Tau, (h.rank_eq j).1]

section Coef

variable {n : ℕ} {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n)

theorem coefFn_add (F G : Formalism.L2.DIV.Pol K D.what₂.Tau n) (x : GLR D n) :
    coefFn σ lam (F + G) x = coefFn σ lam F x + coefFn σ lam G x := by
  simp only [coefFn, map_add, mul_add]

theorem coefFn_zero (x : GLR D n) : coefFn σ lam (0 : Formalism.L2.DIV.Pol K D.what₂.Tau n) x = 0 := by
  simp only [coefFn, map_zero, mul_zero]

theorem coefFn_smul (a : K) (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) (x : GLR D n) :
    coefFn σ lam (a • F) x = σ a * coefFn σ lam F x := by
  simp only [coefFn, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C]
  ring

end Coef

theorem extremalVector_mem_lowestKType (X : RealSide D) {j : Fin D.R.m}
    (hv : FWT.IsChosenExtremalVector X.R.toRealDat j (sg0 D X.A3.A) (X.geo.v₀ j _)) (τ : D.what₂.Tau) :
    X.geo.v₀ j (sg0 D X.A3.A) τ ∈ lowT (model X j) τ :=
  (hv.1 τ).2.1

set_option maxHeartbeats 4000000 in

theorem harm_move (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} (hs : SameSetup ρ ρ') (i : D.ntw.Tw)
    (i' : D'.ntw.Tw) (hi : HEq i i') (j : Fin D.R.m) (b : Bool) (P : PolF D (Wc D j).rank (Vc D j).rank)
    (P' : PolF D' (Wc D' (h.cm j)).rank (Vc D' (h.cm j)).rank) (hP : HEq P P') (x : GLR D (Vc D j).rank)
    (x' : GLR D' (Vc D' (h.cm j)).rank) (hx : HEq x x') :
    harmFn (Wc D' (h.cm j)).rank (ρ'.B i' (h.cm j) b).w (ρ'.B i' (h.cm j) b).F.BS P' x' =
      harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P x := by
  have hB := hs.B i i' hi j (h.cm j) rfl b
  obtain ⟨r, rfl⟩ := h.exists_rest
  have e1 : (ρ'.B i' (h.cm j) b).w.p = (ρ.B i j b).w.p := (eq_of_heq hB.p).symm
  have e2 : (ρ'.B i' (h.cm j) b).w.c = (ρ.B i j b).w.c := (eq_of_heq hB.c).symm
  have e3 : (ρ'.B i' (h.cm j) b).F.BS = (ρ.B i j b).F.BS := (eq_of_heq hB.BS).symm
  have e4 : P' = P := (eq_of_heq hP).symm
  have e5 : x' = x := (eq_of_heq hx).symm
  rw [harmFn_apply, harmFn_apply, e1, e2, e3, e4, e5]
  rfl

theorem coefFn_move (h : CopyTw D D' ι e) (j : Fin D.R.m) (P : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)
    (P' : Formalism.L2.DIV.Pol D'.what₂.LL D'.what₂.Tau (Vc D' (h.cm j)).rank) (hP : HEq (MvPolynomial.map ι P) P')
    (x : GLR D (Vc D j).rank) (x' : GLR D' (Vc D' (h.cm j)).rank) (hx : HEq x x') :
    coefFn D'.what₂.embLL (FWT.lamV D' (h.cm j)) P' x' = coefFn D.what₂.embLL (FWT.lamV D j) P x := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  obtain rfl : P' = MvPolynomial.map ι P := (eq_of_heq hP).symm
  obtain rfl : x' = x := (eq_of_heq hx).symm
  unfold coefFn
  congr 1
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom]
  exact (MvPolynomial.eval₂_map ι _ _ P).trans (by rw [h.embLL_comp]; rfl)

theorem VV_map_mem (h : CopyTw D D' ι e) (j : Fin D.R.m) (P : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)
    (P' : Formalism.L2.DIV.Pol D'.what₂.LL D'.what₂.Tau (Vc D' (h.cm j)).rank) (hP : HEq (MvPolynomial.map ι P) P')
    (hmem : P ∈ VV D.what₂.LL (FWT.lamV D j)) : P' ∈ VV D'.what₂.LL (FWT.lamV D' (h.cm j)) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  obtain rfl : P' = MvPolynomial.map ι P := (eq_of_heq hP).symm
  exact ((baseChangeSpace_holds _ _ ι _ _ (FWT.lamV D j)).1 P).1 hmem

theorem VV_le_span (h : CopyTw D D' ι e) (j : Fin D.R.m) :
    VV D'.what₂.LL (FWT.lamV D' (h.cm j)) ≤ Submodule.span D'.what₂.LL
      {P' | ∃ P ∈ VV D.what₂.LL (FWT.lamV D j), HEq (MvPolynomial.map ι P) P'} := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  refine (le_of_eq (baseChangeSpace_holds _ _ ι _ _ (FWT.lamV D j)).2.symm).trans (Submodule.span_mono ?_)
  rintro _ ⟨P, hP, rfl⟩
  exact ⟨P, hP, HEq.rfl⟩

set_option maxHeartbeats 6000000 in
theorem scale_fwd (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {ρ : Setup D.ntw}
    {ρ' : Setup D'.ntw} (hs : SameSetup ρ ρ')
    (hv' : ∀ j, FWT.IsChosenExtremalVector X'.R.toRealDat j (sg0 D' X'.A3.A) (X'.geo.v₀ j _)) (i : D.ntw.Tw) (i' : D'.ntw.Tw)
    (hi : HEq i i') (j : Fin D.R.m) (b : Bool) {c : ℂ} (hc : IsScale X.R X.geo.v₀ (ρ.B i j b) c) :
    ∃ c', IsScale X'.R X'.geo.v₀ (ρ'.B i' (h.cm j) b) c' ∧ ∃ n : ℕ, n ≠ 0 ∧ c' ^ n = c ^ n := by
  obtain ⟨g₁, r₁, c₁, hT₁, u, hu, hF⟩ := hc
  obtain ⟨c0, c0', hc0, hc0', hio⟩ := m.io
  obtain ⟨ζ, n, hn, hζ, hζF⟩ := GlobalTheory.CoefUniq.exists_root_of_unity D X c0 c₁ hc0 ⟨g₁, r₁, hT₁⟩ j
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hζ
    exact zero_ne_one hζ
  refine ⟨ζ⁻¹ * c, ?_, n, hn, by rw [mul_pow, inv_pow, hζ, inv_one, one_mul]⟩
  obtain ⟨g', r', hT'⟩ := hc0'
  let u' : ∀ τ, lowT (model X' (h.cm j)) τ := fun τ => ⟨_, extremalVector_mem_lowestKType X' (hv' (h.cm j)) τ⟩
  refine ⟨g', r', c0', hT', u', fun τ => rfl, ?_⟩
  have hsv : SameVec (M := model X j) (M' := model X' (h.cm j)) (fun τ => u τ) (fun τ => u' τ) := by
    intro τ τ' hτ
    have h1 := m.v₀ j (h.cm j) rfl τ τ' hτ
    have h2 := hu τ
    simp only at h2 ⊢
    rw [h2]
    exact h1
  have hG : Submodule.span D'.what₂.LL {P' | ∃ P ∈ VV D.what₂.LL (FWT.lamV D j), HEq (MvPolynomial.map ι P) P'} ≤
      VV D'.what₂.LL (FWT.lamV D' (h.cm j)) := by
    refine Submodule.span_le.2 ?_
    rintro P' ⟨P, hP, hPP'⟩
    exact VV_map_mem h j P P' hPP' hP
  have key : ∀ z ∈ Submodule.span D'.what₂.LL {P' | ∃ P ∈ VV D.what₂.LL (FWT.lamV D j), HEq (MvPolynomial.map ι P) P'},
      ∀ hz : z ∈ VV D'.what₂.LL (FWT.lamV D' (h.cm j)),
      harmFn (Wc D' (h.cm j)).rank (ρ'.B i' (h.cm j) b).w (ρ'.B i' (h.cm j) b).F.BS
          (X'.R.ioP (h.cm j) (PiTensorProduct.tprod ℂ u') (c0' (h.cm j) ⟨z, hz⟩)) =
        (ζ⁻¹ * c) • coefFn D'.what₂.embLL (FWT.lamV D' (h.cm j)) z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨P, hP, hPz⟩ := hz
      intro hz'
      funext x'
      have hx : HEq (cast (h.glr_eq j).symm x') x' := cast_heq _ _
      have e1 := harm_move h hs i i' hi j b (X.R.ioP j (PiTensorProduct.tprod ℂ u) (c0 j ⟨P, hP⟩))
        (X'.R.ioP (h.cm j) (PiTensorProduct.tprod ℂ u') (c0' (h.cm j) ⟨z, hz'⟩))
        (hio j (h.cm j) rfl u u' hsv ⟨P, hP⟩ ⟨z, hz'⟩ hPz) _ x' hx
      have e2 := congrFun (hF ⟨P, hP⟩) (cast (h.glr_eq j).symm x')
      rw [show (c₁ j) ⟨P, hP⟩ = ζ • (c0 j) ⟨P, hP⟩ from hζF _, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at e2
      have e3 := coefFn_move h j P z hPz _ x' hx
      have e2' : ζ * harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS (X.R.ioP j (PiTensorProduct.tprod ℂ u) (c0 j ⟨P, hP⟩))
          (cast (h.glr_eq j).symm x') = c * coefFn D.what₂.embLL (FWT.lamV D j) P (cast (h.glr_eq j).symm x') := e2
      rw [e1, Pi.smul_apply, smul_eq_mul, e3, mul_assoc, ← e2', ← mul_assoc, inv_mul_cancel₀ hζ0, one_mul]
    | zero =>
      intro hz
      rw [show (⟨0, hz⟩ : ↥(VV D'.what₂.LL (FWT.lamV D' (h.cm j)))) = 0 from rfl, map_zero, map_zero, map_zero]
      funext x'
      rw [Pi.smul_apply, coefFn_zero, smul_zero, Pi.zero_apply]
    | add x y hx hy ihx ihy =>
      intro hxy
      have hx' := hG hx
      have hy' := hG hy
      rw [show (⟨x + y, hxy⟩ : ↥(VV D'.what₂.LL (FWT.lamV D' (h.cm j)))) = ⟨x, hx'⟩ + ⟨y, hy'⟩ from rfl, map_add, map_add,
        map_add, ihx hx', ihy hy']
      funext x'
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coefFn_add, mul_add]
    | smul a x hx ih =>
      intro hax
      have hx' := hG hx
      rw [show (⟨a • x, hax⟩ : ↥(VV D'.what₂.LL (FWT.lamV D' (h.cm j)))) = a • ⟨x, hx'⟩ from rfl, map_smulₛₗ, map_smul,
        map_smul, ih hx']
      funext x'
      simp only [Pi.smul_apply, smul_eq_mul, coefFn_smul]
      ring
  intro F'
  exact key F' (VV_le_span h j F'.2) F'.2

set_option maxHeartbeats 6000000 in
theorem scale_bwd (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {ρ : Setup D.ntw}
    {ρ' : Setup D'.ntw} (hs : SameSetup ρ ρ')
    (hv : ∀ j, FWT.IsChosenExtremalVector X.R.toRealDat j (sg0 D X.A3.A) (X.geo.v₀ j _)) (i : D.ntw.Tw) (i' : D'.ntw.Tw)
    (hi : HEq i i') (j : Fin D.R.m) (b : Bool) {c' : ℂ} (hc : IsScale X'.R X'.geo.v₀ (ρ'.B i' (h.cm j) b) c') :
    ∃ c, IsScale X.R X.geo.v₀ (ρ.B i j b) c ∧ ∃ n : ℕ, n ≠ 0 ∧ c ^ n = c' ^ n := by
  obtain ⟨g₁, r₁, c₁, hT₁, u', hu', hF⟩ := hc
  obtain ⟨c0, c0', hc0, hc0', hio⟩ := m.io
  obtain ⟨ζ, n, hn, hζ, hζF⟩ := GlobalTheory.CoefUniq.exists_root_of_unity D' X' c0' c₁ hc0' ⟨g₁, r₁, hT₁⟩ (h.cm j)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hζ
    exact zero_ne_one hζ
  refine ⟨ζ⁻¹ * c', ?_, n, hn, by rw [mul_pow, inv_pow, hζ, inv_one, one_mul]⟩
  obtain ⟨g, r, hT⟩ := hc0
  obtain ⟨u, hu⟩ : ∃ u : ∀ τ, lowT (model X j) τ, ∀ τ, (u τ : (model X j).sm τ) = X.geo.v₀ j (sg0 D X.A3.A) τ :=
    ⟨fun τ => ⟨_, extremalVector_mem_lowestKType X (hv j) τ⟩, fun τ => rfl⟩
  refine ⟨g, r, c0, hT, u, hu, ?_⟩
  have hsv : SameVec (M := model X j) (M' := model X' (h.cm j)) (fun τ => u τ) (fun τ => u' τ) := by
    intro τ τ' hτ
    have h1 := m.v₀ j (h.cm j) rfl τ τ' hτ
    have h2 := hu' τ'
    have h3 := hu τ
    simp only at h2 h3 ⊢
    rw [h2, h3]
    exact h1
  rintro ⟨P, hP⟩
  funext x
  obtain ⟨P', hPP'⟩ : ∃ P' : Formalism.L2.DIV.Pol D'.what₂.LL D'.what₂.Tau (Vc D' (h.cm j)).rank, HEq (MvPolynomial.map ι P) P' :=
    ⟨cast (h.pol_eq j) (MvPolynomial.map ι P), (cast_heq _ _).symm⟩
  have hP' : P' ∈ VV D'.what₂.LL (FWT.lamV D' (h.cm j)) := VV_map_mem h j P P' hPP' hP
  obtain ⟨x', hx⟩ : ∃ x' : GLR D' (Vc D' (h.cm j)).rank, HEq x x' := ⟨cast (h.glr_eq j) x, (cast_heq _ _).symm⟩
  have e1 := harm_move h hs i i' hi j b (X.R.ioP j (PiTensorProduct.tprod ℂ u) (c0 j ⟨P, hP⟩))
    (X'.R.ioP (h.cm j) (PiTensorProduct.tprod ℂ u') (c0' (h.cm j) ⟨P', hP'⟩))
    (hio j (h.cm j) rfl u u' hsv ⟨P, hP⟩ ⟨P', hP'⟩ hPP') x x' hx
  have e2 : ζ * harmFn (Wc D' (h.cm j)).rank (ρ'.B i' (h.cm j) b).w (ρ'.B i' (h.cm j) b).F.BS
      (X'.R.ioP (h.cm j) (PiTensorProduct.tprod ℂ u') (c0' (h.cm j) ⟨P', hP'⟩)) x' =
      c' * coefFn D'.what₂.embLL (FWT.lamV D' (h.cm j)) P' x' := by
    have := congrFun (hF ⟨P', hP'⟩) x'
    rw [show (c₁ (h.cm j)) ⟨P', hP'⟩ = ζ • (c0' (h.cm j)) ⟨P', hP'⟩ from hζF _, map_smul, map_smul] at this
    exact this
  have e3 := coefFn_move h j P P' hPP' x x' hx
  show _ = (ζ⁻¹ * c') * coefFn D.what₂.embLL (FWT.lamV D j) P x
  refine e1.symm.trans ?_
  rw [← e3, mul_assoc, ← e2, ← mul_assoc, inv_mul_cancel₀ hζ0, one_mul]

theorem isNorm_move_iff (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {ρ : Setup D.ntw}
    {ρ' : Setup D'.ntw} (hs : SameSetup ρ ρ')
    (hv : ∀ j, FWT.IsChosenExtremalVector X.R.toRealDat j (sg0 D X.A3.A) (X.geo.v₀ j _))
    (hv' : ∀ j, FWT.IsChosenExtremalVector X'.R.toRealDat j (sg0 D' X'.A3.A) (X'.geo.v₀ j _)) (i : D.ntw.Tw) (i' : D'.ntw.Tw)
    (hi : HEq i i') (j : Fin D.R.m) (b : Bool) (ν : ℂ) :
    IsNorm X.R X.geo.v₀ (ρ.B i j b) ν ↔ IsNorm X'.R X'.geo.v₀ (ρ'.B i' (h.cm j) b) ν := by
  rw [isNorm_iff, isNorm_iff]
  constructor
  · rintro ⟨hν, c, hc, n, hn, hνc⟩
    obtain ⟨c', hc', k, hk, hcc⟩ := scale_fwd h m hs hv' i i' hi j b hc
    refine ⟨hν, c', hc', n * k, mul_ne_zero hn hk, ?_⟩
    rw [pow_mul, hνc, ← pow_mul, mul_comm, pow_mul, ← hcc, ← pow_mul, mul_comm, pow_mul]
  · rintro ⟨hν, c', hc', n, hn, hνc⟩
    obtain ⟨c, hc, k, hk, hcc⟩ := scale_bwd h m hs hv i i' hi j b hc'
    refine ⟨hν, c, hc, n * k, mul_ne_zero hn hk, ?_⟩
    rw [pow_mul, hνc, ← pow_mul, mul_comm, pow_mul, ← hcc, ← pow_mul, mul_comm, pow_mul]

theorem scalar_move : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {S : NX.RatDat D.ntw} {YS : NX.NExpRealS X.R X.cG S} {S' : NX.RatDat D'.ntw}
    {YS' : NX.NExpRealS X'.R X'.cG S'} {ρ : Setup D.ntw} {ρ' : Setup D'.ntw}, SameSetup ρ ρ' → ∀ (hρ : ρ.Good) (hρ' : ρ'.Good),
    RealPin X.R X.cG ρ → RealPin X'.R X'.cG ρ' →
    (∀ j, FWT.IsChosenExtremalVector X.R.toRealDat j (sg0 D X.A3.A) (X.geo.v₀ j _)) →
    (∀ j, FWT.IsChosenExtremalVector X'.R.toRealDat j (sg0 D' X'.A3.A) (X'.geo.v₀ j _)) →
    (∀ c : ℂ, RdRel h (fun i j b => realRd YS X.geo.v₀ hρ i j b c) (fun i j b => realRd YS' X'.geo.v₀ hρ' i j b c)) →
    ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) b (ν : ℂ),
      IsScalar YS X.geo.v₀ hρ i j b ν → IsScalar YS' X'.geo.v₀ hρ' i' (h.cm j) b ν := by
  intro D D' ι e h X X' m S YS S' YS' ρ ρ' hs hρ hρ' _ _ hv hv' hrd i i' hi j b ν hS
  have hN := fun ν => isNorm_move_iff h m hs hv hv' i i' hi j b ν
  have hR := fun c => RatUp.rat_copy_iff h hs hρ hρ' _ _ (hrd c) i i' hi j b
  exact ⟨hS.ne, fun ⟨ν', h'⟩ => (hN ν).1 (hS.norm ⟨ν', (hN ν').2 h'⟩),
    fun ⟨ν', hn', hr'⟩ => (hR ν).1 (hS.rat ⟨ν', (hN ν').2 hn', (hR ν').2 hr'⟩)⟩

end GlobalTheory.TwInputs.Move

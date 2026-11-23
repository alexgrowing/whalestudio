import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspLatticeAnyLevel
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SupremumLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LMLatOfLIntegral

noncomputable section

namespace GlobalTheory.GoodLat.Road

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Arith Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents GlobalTheory.IndefiniteRowSideFullHecke.SupremumLattice

abbrev kapRows (D : D7) : Rows.Data D.R :=
  { D.what₂ with
    kaBig := fun j τ i => (DV.aPlusQ_int D j τ i).choose
    kaSmall := fun j τ c => -(DV.aMinusQ_int D j τ c).choose }

set_option maxHeartbeats 4000000 in

def kapRec (D : D7) : D7 :=
  { D with
    what₂ := kapRows D
    nd := { D.nd with }
    ntw := { D.ntw with }
    naut := { D.naut with }
    nbc := { D.nbc with }
    nexp := { D.nexp with }
    ntypes := { D.ntypes with }
    nth := { D.nth with } }

theorem kapDef_kapRec (D : D7) : DV.KapDef (kapRec D) := fun j _ _ τ =>
  ⟨fun i => (DV.aPlusQ_int D j τ i).choose_spec.symm, fun c => by
    show ((-(DV.aMinusQ_int D j τ c).choose : ℤ) : ℚ) = -DV.aMinusQ D j τ c
    rw [Int.cast_neg, ← (DV.aMinusQ_int D j τ c).choose_spec]⟩

def kapCore {D : D7} (T : Core D) : Core (kapRec D) :=
  { T with Q := { T.Q with } }

theorem volPair_kapRec (D : D7) (V : TH.HSp D) : volPair (D := kapRec D) V = volPair (D := D) V := by
  unfold volPair; rfl

theorem muQ_kapRec (D : D7) (V : TH.HSp D) : muQ (D := kapRec D) V = muQ (D := D) V :=
  congrArg (fun p : MeasureTheory.Measure (Formalism.L2.Theta.GA D V) × Set (Formalism.L2.Theta.GA D V) =>
    (p.1.restrict p.2).map (autMk (D := D) V)) (volPair_kapRec D V)

open Classical in
theorem muQ1_congr_datum (D : D7) (V : TH.HSp D) : muQ1 (D := kapRec D) V = muQ1 (D := D) V :=
  congrArg (fun μ : MeasureTheory.Measure (AutQ (D := D) V) =>
    if μ Set.univ ≠ 0 ∧ μ Set.univ ≠ ⊤ then (μ Set.univ)⁻¹ • μ else MeasureTheory.Measure.dirac (autMk (D := D) V 1))
    (muQ_kapRec D V)

theorem finVol_kapRec {D : D7} {V : TH.HSp D} (h : FinVol (D := D) V) : FinVol (D := kapRec D) V :=
  (congrArg (fun μ : MeasureTheory.Measure (AutQ (D := D) V) => μ Set.univ ≠ 0 ∧ μ Set.univ ≠ ⊤)
    (muQ_kapRec D V)).mpr h

theorem memLp_kapRec {D : D7} {V : TH.HSp D} {φ : AutQ (D := D) V → ℂ}
    (h : MeasureTheory.MemLp φ 2 (muQ1 (D := D) V)) : MeasureTheory.MemLp φ 2 (muQ1 (D := kapRec D) V) :=
  (congrArg (fun μ : MeasureTheory.Measure (AutQ (D := D) V) => MeasureTheory.MemLp φ 2 μ) (muQ1_congr_datum D V)).mpr h

theorem norm_toLp_congr {α : Type} [MeasurableSpace α] {μ ν : MeasureTheory.Measure α} (e : μ = ν) {φ : α → ℂ}
    (h : MeasureTheory.MemLp φ 2 μ) (h' : MeasureTheory.MemLp φ 2 ν) : ‖h.toLp φ‖ = ‖h'.toLp φ‖ := by
  subst e; rfl

section Readings

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type} (V : TH.HSp D)
  {K : Type} [Field K] {C : Type} [AddCommGroup C] [Module K C] (σ : K →+* ℂ)
  {X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r} (rd : C →ₛₗ[σ] FDSec X)
  (dict : Formalism.L2.Theta.GA D V → Σ c, ReciprocityTheory.ChartRestriction.G.FD.Frame (X c).Ψ r) (mu : Formalism.L2.Theta.GA D V → ℂ)

theorem j_mem_l2_under_datum_change (h : JMemL2 (D := D) V σ rd dict mu) : JMemL2 (D := kapRec D) V σ rd dict mu := fun f =>
  memLp_kapRec (φ := jFn (D := D) V σ rd dict mu f) (h f)

theorem jMemL2_congr_datum (h : JMemL2 (D := D) V σ rd dict mu) (h' : JMemL2 (D := kapRec D) V σ rd dict mu)
    (hd : L2Definite (D := D) V σ rd dict mu h) : L2Definite (D := kapRec D) V σ rd dict mu h' := fun f h0 =>
  hd f ((norm_toLp_congr (φ := jFn (D := D) V σ rd dict mu f) (muQ1_congr_datum D V) (h' f) (h f)).symm.trans h0)

end Readings

theorem cusp_l2_under_datum_change {D : D7} {T : Core D} (h : LawsM T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) : CuspL2 (D := kapRec D) (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ) := fun a n hd =>
  j_mem_l2_under_datum_change (D := D) (T.V j σ) σ (rdC (T.U j) σ a n) (T.dict j σ) (T.mu j σ) (h.cuspidalL2Subspace j hj σ hσ a n hd)

theorem cuspL2_congr_core_of_lawsM {D : D7} {T : Core D} (h : LawsM T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (h' : CuspL2 (D := kapRec D) (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ)) :
    L2DefiniteCuspForms (D := kapRec D) (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ) h' := fun a n hd =>
  jMemL2_congr_datum (D := D) (T.V j σ) σ (rdC (T.U j) σ a n) (T.dict j σ) (T.mu j σ) _ (h' a n hd)
    (h.l2Def j hj σ hσ a n hd)

set_option maxHeartbeats 1000000 in

theorem lawsM_kapCore {D : D7} {T : Core D} (h : LawsM T) : LawsM (kapCore T) where
  pins := h.pins
  half := h.half
  evalWD := h.evalWD
  unf := h.unf
  unTest := h.unTest
  chiTriv := h.chiTriv
  dictU := h.dictU
  spaceW := h.spaceW
  levelK := h.levelK
  xiAbs := h.xiAbs
  muUnit := h.muUnit
  muCont := h.muCont
  finVol j hj σ hσ := finVol_kapRec (D := D) (V := T.V j σ) (h.finVol j hj σ hσ)
  cuspFD := h.cuspFD
  supDef := h.supDef
  cuspidalL2Subspace j hj σ hσ := cusp_l2_under_datum_change (D := D) (T := T) h j hj σ hσ
  l2Def j hj σ hσ := cuspL2_congr_core_of_lawsM (D := D) (T := T) h j hj σ hσ _
  unitIndep := h.unitIndep
  ptNe := h.ptNe

theorem wtA_eq {D : D7} {j : ℕ} (hj : InR D j) {w : WeightFamilies.Wt D j} (hw : IsKappa D j w) (hn : Even D.R.nV) :
    kappaExp (kapRec D) (kapDef_kapRec D) hn j = wtA w := by
  obtain ⟨-, h⟩ := isKappa_kaWt (D := kapRec D) (kapDef_kapRec D) hn hj
  have hP : (DIV.Cons.kaWt (kapRec D) (kapDef_kapRec D) hn j).aP = w.aP := by
    funext τ i
    exact_mod_cast ((h τ).1 i).trans ((hw.2 τ).1 i).symm
  have hM : (DIV.Cons.kaWt (kapRec D) (kapDef_kapRec D) hn j).aM = w.aM := by
    funext τ c
    obtain ⟨c, rfl⟩ := Fin.rev_surjective c
    exact_mod_cast ((h τ).2 c).trans ((hw.2 τ).2 c).symm
  funext x
  unfold kappaExp wtA
  rw [hP, hM]
  rfl

set_option maxHeartbeats 1000000 in
theorem supLatticeFullAt_kapCore {D : D7} (T : Core D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    SupLatticeFullAt (kapCore T) j a n ↔ SupLatticeFullAt T j a n := Iff.rfl

theorem fullLat_of_kappa (H : IntegralCuspFormsFullLattice) {D : D7} (T : Core D) (hT : LawsM T) {j : ℕ} (hj : InR D j)
    {w : WeightFamilies.Wt D j} (hw : IsKappa D j w) :
    FullLat (T.cuspA j (wtA w) w.n) (valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)) fun la => isVal_valSet la := by
  have hn : Even D.R.nV := hw.1 ▸ w.n_even
  have h := H (kapRec D) (kapDef_kapRec D) hn (kapCore T) (lawsM_kapCore hT) j hj
  have h' := (supLatticeFullAt_kapCore T j _ _).1 h
  rw [wtA_eq hj hw hn] at h'
  have h'' : SupLatticeFullAt T j (wtA w) w.n := by rw [hw.1]; exact h'
  exact (supIn_full_iff _ _ _).1 h''

section Abstract

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G : Type} [Group G] [Fintype G]

omit [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [Fintype G] in

theorem isKsForm_of_isBaseChange (A : FormsL LL Ks WL W G) {C : Type} [AddCommGroup C] [Module Ks C]
    [FiniteDimensional Ks C] (ι : C →ₗ[Ks] WL) (hι : IsBaseChange LL ι) (hW : A.WK = LinearMap.range ι) :
    A.IsKsForm := by
  let b := Module.finBasis Ks C
  let B := (Algebra.TensorProduct.basis LL b).map hι.equiv
  have e : ∀ i, B i = ι (b i) := fun i => by
    simp [B, Algebra.TensorProduct.basis_apply]
  have e' : (fun i => ι (b i)) = B := funext fun i => (e i).symm
  refine ⟨_, fun i => ι (b i), fun i => hW ▸ ⟨b i, rfl⟩, ?_, ?_, e' ▸ B.linearIndependent, e' ▸ B.span_eq⟩
  · rw [e']
    exact B.linearIndependent.restrict_scalars' Ks
  · show Submodule.span Ks (Set.range (ι ∘ b)) = _
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top, hW]

theorem mjFull_of_full (A : FormsL LL Ks WL W G) (hK : A.IsKsForm) (hM : A.MKFull) (J0 : Subgroup G)
    (lam0 : J0 →* LLˣ) (eC : G → LL) : MjFull A J0 lam0 eC := by
  refine ⟨?_, fun d b hb => isLattice_Mcoord A hK hM J0 lam0 eC b hb.1 fun i =>
    hb.2 ▸ Submodule.subset_span ⟨i, rfl⟩⟩
  obtain ⟨n, b, -, -, -, h3, h4⟩ := hK
  have : FiniteDimensional LL WL := (Module.Basis.mk h3 h4.ge).finiteDimensional_of_finite
  infer_instance

end Abstract

section Comparison₂

variable {D : D7} (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j)
variable {LL : Type} [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 T.Q.c.F) WL] [IsScalarTower (𝓞 T.Q.c.F) T.Q.c.F WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G : Type} [Group G] [Fintype G]

theorem mjFull_of_fullLat (A : FormsL LL T.Q.c.F WL W G) (ι : Cusp T j w →ₗ[T.Q.c.F] WL) (hA : CarriesCusp T j w A ι)
    (hl : FullLat (T.cuspA j (wtA w) w.n) (valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c))
      fun la => isVal_valSet la)
    (J0 : Subgroup G) (lam0 : J0 →* LLˣ) (eC : G → LL) : MjFull A J0 lam0 eC := by
  obtain ⟨hι, hW, hN⟩ := hA
  have hfd : FiniteDimensional T.Q.c.F (Cusp T j w) := by
    obtain ⟨s, hs⟩ := hl.fg
    refine ⟨s, ?_⟩
    rw [← hl.span_eq_top, ← hs, Submodule.span_span_of_tower]
  refine mjFull_of_full A (isKsForm_of_isBaseChange A ι hι hW) (mkFull_of A ι hW (fun x => ?_) hl) J0 lam0 eC
  constructor
  · rintro ⟨hx, h⟩
    obtain ⟨f, rfl⟩ := hW ▸ hx
    exact ⟨f, fun la v hv => (T.nrmM_le_one_iff j la ⟨v, hv⟩ _).1 ((hN la f hx).1 (h la) ⟨v, hv⟩), rfl⟩
  · rintro ⟨f, hf, rfl⟩
    have hx : ι f ∈ A.WK := hW ▸ ⟨f, rfl⟩
    exact ⟨hx, fun la => (hN la f hx).2 fun y => (T.nrmM_le_one_iff j la y _).2 (hf la y.1 y.2)⟩

end Comparison₂

theorem mLatAnyLevel_of_fullLattice (H : IntegralCuspFormsFullLattice) : MLatAnyLevel := by
  intro D T hT j hj w hw LL _ _ _ WL _ _ _ _ _ _ _ _ W _ _ G _ _ A ι hA J0 lam0 eC
  exact mjFull_of_fullLat T j w A ι hA (fullLat_of_kappa H T hT hj hw) J0 lam0 eC

theorem mLat_of_fullLattice (H : IntegralCuspFormsFullLattice) : MLat :=
  MLat.of_anyLevel (mLatAnyLevel_of_fullLattice H)

end GlobalTheory.GoodLat.Road

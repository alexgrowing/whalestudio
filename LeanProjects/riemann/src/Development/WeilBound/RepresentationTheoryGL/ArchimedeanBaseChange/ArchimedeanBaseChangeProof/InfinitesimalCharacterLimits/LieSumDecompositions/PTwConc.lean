import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SplitInv
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.TwShift

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin GlobalTheory.SmGL PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.TwistConcentration

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in
theorem chiDet_unip {a r : ℕ} (χ : Formalism.L2.Host.HChar E) (x : BlockIx a r → Ad E) : chiDet a χ (unip x) = 1 := by
  change (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det (unip x)) = 1
  rw [det_unip, map_one]

omit [IsCMField E] in
theorem chiDet_lev {r s : ℕ} (χ : Formalism.L2.Host.HChar E) (m : GA E r × GA E s) :
    chiDet (r + s) χ (lev (Ad E) r s m) = chiDet r χ m.1 * chiDet s χ m.2 := by
  change (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det (lev (Ad E) r s m)) =
    (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det m.1) *
      (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det m.2)
  rw [← map_mul]
  congr 1
  exact det_emb₂ _ _ m

omit [IsCMField E] in
theorem chiDet_zero (χ : Formalism.L2.Host.HChar E) (g : GA E 0) : chiDet 0 χ g = 1 := by
  have h : Matrix.GeneralLinearGroup.det g = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_isEmpty]
  change (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det g) = 1
  rw [h, map_one]

theorem mulChi_mulChi {n : ℕ} (a b : ℂ) (φ : Sm E n) :
    mulChi n (Model.absC E b) (mulChi n (Model.absC E a) φ) = mulChi n (Model.absC E (a + b)) φ := by
  refine Subtype.ext (funext fun g => ?_)
  rw [mulChi_apply, mulChi_apply, mulChi_apply, ExponentTwist.chiDet_absC_val, ExponentTwist.chiDet_absC_val,
    ExponentTwist.chiDet_absC_val, mul_assoc, ← Complex.exp_add, add_mul]

theorem tw_tw {n : ℕ} (V : Submodule ℂ (Sm E n)) (a b : ℂ) : tw (tw V a) b = tw V (a + b) := by
  unfold tw
  rw [← Submodule.map_comp]
  congr 1
  ext φ : 1
  exact mulChi_mulChi a b φ

theorem tw_zero_dim (V : Submodule ℂ (Sm E 0)) (z : ℂ) : tw V z = V := by
  have h : (mulChi 0 (Model.absC E z)).toLinearMap = LinearMap.id := by
    ext φ : 1
    refine Subtype.ext (funext fun g => ?_)
    rw [LinearEquiv.coe_coe, mulChi_apply, chiDet_zero, Units.val_one, mul_one]
    rfl
  unfold tw
  rw [h, Submodule.map_id]

theorem tw_zero' {n : ℕ} (V : Submodule ℂ (Sm E n)) : tw V 0 = V := by
  have h : (mulChi n (Model.absC E 0)).toLinearMap = LinearMap.id := by
    ext φ : 1
    refine Subtype.ext (funext fun g => ?_)
    rw [LinearEquiv.coe_coe, mulChi_apply, ExponentTwist.chiDet_absC_val, zero_mul, Complex.exp_zero, mul_one]
    rfl
  unfold tw
  rw [h, Submodule.map_id]

variable {r s : ℕ}

theorem tensor_span_mul_det_character {W₁ : Submodule ℂ (Sm E r)} {W₂ : Submodule ℂ (Sm E s)} (z : ℂ) {F : GA E r × GA E s → ℂ}
    (hF : F ∈ tens2 W₁ W₂) :
    (fun m => F m * (((chiDet r (Model.absC E z) m.1 : ℂˣ) : ℂ) * ((chiDet s (Model.absC E z) m.2 : ℂˣ) : ℂ))) ∈
      tens2 (tw W₁ z) (tw W₂ z) := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hF
    refine Submodule.subset_span ⟨mulChi r (Model.absC E z) φ₁, ⟨φ₁, h₁, rfl⟩, mulChi s (Model.absC E z) φ₂,
      ⟨φ₂, h₂, rfl⟩, funext fun m => ?_⟩
    simp only [mulChi_apply]
    ring
  | zero =>
    convert zero_mem (tens2 (tw W₁ z) (tw W₂ z)) using 1
    funext m
    simp
  | add F G _ _ hF hG =>
    convert add_mem hF hG using 1
    funext m
    simp [add_mul]
  | smul c F _ hF =>
    convert Submodule.smul_mem _ c hF using 1
    funext m
    simp [mul_assoc]

theorem memInd2_tw {W₁ : Submodule ℂ (Sm E r)} {W₂ : Submodule ℂ (Sm E s)} (z : ℂ) {φ : Sm E (r + s)}
    (hφ : MemInd2 W₁ W₂ φ) : MemInd2 (tw W₁ z) (tw W₂ z) (mulChi (r + s) (Model.absC E z) φ) := by
  refine ⟨fun x g => ?_, fun k g => ?_⟩
  · rw [mulChi_apply, mulChi_apply, hφ.1 x g, map_mul, chiDet_unip, one_mul]
  · set y := infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g
    have h1 := Submodule.smul_mem _ ((chiDet (r + s) (Model.absC E z) y : ℂˣ) : ℂ) (tensor_span_mul_det_character z (hφ.2 k g))
    convert h1 using 1
    funext m
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mulChi_apply, map_mul, chiDet_lev, Units.val_mul, Units.val_mul]
    ring

theorem memInd2_tw_iff {W₁ : Submodule ℂ (Sm E r)} {W₂ : Submodule ℂ (Sm E s)} (z : ℂ) (ψ : Sm E (r + s)) :
    (MemInd2 (tw W₁ z) (tw W₂ z) ψ ∧ ψ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))) ↔
      ∃ φ, (MemInd2 W₁ W₂ φ ∧ φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))) ∧ mulChi (r + s) (Model.absC E z) φ = ψ := by
  constructor
  · rintro ⟨h, hK⟩
    refine ⟨mulChi (r + s) (Model.absC E (-z)) ψ, ⟨?_, Trees.mulChi_mem_finVec _ hK⟩, ParabolicProjection.mulChi_absC_neg' _ z ψ⟩
    have h2 := memInd2_tw (-z) h
    rwa [tw_tw, tw_tw, add_neg_cancel, tw_zero', tw_zero'] at h2
  · rintro ⟨φ, ⟨hφ, hK⟩, rfl⟩
    exact ⟨memInd2_tw z hφ, Trees.mulChi_mem_finVec _ hK⟩

theorem span_memInd2_tw (W₁ : Submodule ℂ (Sm E r)) (W₂ : Submodule ℂ (Sm E s)) (z : ℂ) :
    Submodule.span ℂ {φ | MemInd2 (tw W₁ z) (tw W₂ z) φ ∧ φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))} =
      tw (Submodule.span ℂ {φ | MemInd2 W₁ W₂ φ ∧ φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))}) z := by
  rw [show tw (Submodule.span ℂ {φ | MemInd2 W₁ W₂ φ ∧ φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))}) z =
    (Submodule.span ℂ {φ | MemInd2 W₁ W₂ φ ∧ φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))}).map
      (mulChi (r + s) (Model.absC E z)).toLinearMap from rfl,
    Submodule.map_span]
  congr 1
  ext ψ
  exact memInd2_tw_iff z ψ

def twT (z : ℂ) : {N : ℕ} → Tr E N → Tr E N
  | M, .leaf V w => .leaf V (if M = 0 then w else w + z)
  | _, .node t₁ t₂ => .node (twT z t₁) (twT z t₂)

theorem space_twT (z : ℂ) {N : ℕ} (t : Tr E N) : (twT z t).space = tw t.space z := by
  induction t with
  | @leaf M V w =>
    by_cases hM : M = 0
    · subst hM
      simp only [twT, Tr.space, tw_zero_dim]
    · simp only [twT, if_neg hM, Tr.space]
      rw [tw_tw]
  | @node r s t₁ t₂ ih₁ ih₂ =>
    simp only [twT, Tr.space]
    rw [ih₁, ih₂, tw_tw, tw_tw, add_comm z, add_comm z, ← tw_tw _ _ z, ← tw_tw _ _ z, span_memInd2_tw]

theorem good_twT {z : ℂ} (hz : z.re = 0) {N : ℕ} (t : Tr E N) (ht : t.Good) : (twT z t).Good := by
  induction t with
  | @leaf M V w =>
    rcases ht with ⟨hM, hV, hw⟩ | ⟨hM, hV, hw⟩
    · subst hM
      simp only [twT]
      exact Or.inl ⟨rfl, hV, hw⟩
    · simp only [twT, if_neg hM.ne']
      exact Or.inr ⟨hM, hV, by rw [Complex.add_re, hw, hz, add_zero]⟩
  | @node r s t₁ t₂ ih₁ ih₂ =>
    exact ⟨ih₁ ht.1, ih₂ ht.2⟩

theorem pos_twT (z : ℂ) {N : ℕ} (t : Tr E N) (ht : t.AllLeaves (fun M _ => 0 < M)) :
    (twT z t).AllLeaves (fun M _ => 0 < M) := by
  induction t with
  | @leaf M V w => exact ht
  | @node r s t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ ht.1, ih₂ ht.2⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.TwistConcentration

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

open TwistConcentration in
theorem twConc_holds : TwConc := by
  intro E _ _ _ N U z hz hU φ _ hc
  obtain ⟨t, T, ht, hpos, hTe, hTm, hT0⟩ := hc
  refine ⟨twT z t, ParabolicProjection.twMap N z T, good_twT hz t ht, pos_twT z t hpos, ParabolicProjection.twMap_equiv hU.1 hTe, fun ψ hψ => ?_, ?_⟩
  · rw [space_twT]
    exact ParabolicProjection.twMap_mem hTm ψ hψ
  · rw [ParabolicProjection.twMap_apply, ParabolicProjection.mulChi_absC_neg]
    exact (LinearEquiv.map_ne_zero_iff _).2 hT0

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

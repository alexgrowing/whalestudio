import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArithStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoClosedImmersionsSameGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveHeightFormulaRhsTransportIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightUniqueRestrictClosedSubschemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductiveRhsSymmIsometryInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductionIndependentOfSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveDegreeIndependentOfSectionStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.StepVal

variable {k : Type} [CommRing k]

theorem isometric_pull_pull' {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    {s : Z ⟶ Sp k} (L : HermLB p) (f : Y ⟶ X) (hf : f ≫ p = q) (g : Z ⟶ Y) (hg : g ≫ q = s) (c : Z ⟶ X)
    (hc : c ≫ p = s) (e : g ≫ f = c) : ((L.pull f hf).pull g hg).Isometric (L.pull c hc) := by
  subst e
  have R := L.refines_pull_pull f hf g hg hc
  exact HermLB.isometric_of_chart _ R.le (fun x => R.g Z (𝟙 Z) x) fun σ c y hy =>
    ((R.φ σ c y hy).trans (add_zero _)).symm

theorem recVal_congr {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} {e : ℕ}
    {h h' : Y → ℝ} (H : ∀ z : Y, Order.coheight z = 1 → h z = h' z) (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : recVal h L M hr = recVal h' L M hr := by
  unfold recVal
  congr 1
  refine finsum_congr fun z => ?_
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  · rw [H z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)]

theorem dim_of_genericPoint {X Y : Scheme.{0}} [IsIntegral Y] {p : X ⟶ Sp k} (hp : IsAmb p) (i : Y ⟶ X)
    [IsClosedImmersion i] {x : X} {d : ℕ} (hx : HasDim x d) (hg : i (genericPoint Y) = x) :
    topologicalKrullDim Y = d := by
  have H := (GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hp).2.2.2.2
  rw [← H.2 Y d, ← H.1 Y i (genericPoint Y) d, hg]
  exact hx

theorem recVal_indep_section (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ) {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) (hY : topologicalKrullDim Y = (m + 1 : ℕ)) {T}
    (hT : IsMix q m T) (L : Fin m → HermLB q) (N : HermLB q) {r r' : N.B.ι → Y.functionFieldˣ} (hr : IsRatSec N.B r)
    (hr' : IsRatSec N.B r') : recVal (T m L) L N hr = recVal (T m L) L N hr' := by
  cases m with
  | zero =>
    have H : ∀ z : Y, Order.coheight z = 1 → T 0 L z = Real.log (Nat.card (Y.residueField z)) := fun z hz =>
      hT.zero L z (((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq 0 hY).1 z).1 hz)
    rw [recVal_congr H, recVal_congr H]
    exact GlobalTheory.T.arithmetic_curve_degree_independent_of_section k Y q hq hY N L r hr r' hr'
  | succ e => exact GlobalTheory.T.mixedHeightInduction_independent_of_section hInt hRec k Y q hq e hY T hT N L r hr r' hr'

theorem recVal_indep (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ) {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) (hY : topologicalKrullDim Y = (m + 1 : ℕ)) {T}
    (hT : IsMix q m T) (L L' : Fin m → HermLB q) (hL : ∀ a, (L a).Isometric (L' a)) (M M' : HermLB q)
    (hM : M.Isometric M') {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) {r' : M'.B.ι → Y.functionFieldˣ}
    (hr' : IsRatSec M'.B r') : recVal (T m L) L M hr = recVal (T m L') L' M' hr' := by
  have H := GlobalTheory.T.mixedHeight_inductive_rhs_symm_isometry_invariant hInt k Y q hq m hY T hT M r hr
  obtain ⟨r₃, hr₃, e₃⟩ := H.2.2 L' M' hM
  rw [H.1 L L' hL, ← e₃]
  exact recVal_indep_section hInt hRec m hq hY hT L' M' hr₃ hr'

end GlobalTheory.MixHt.StepVal

namespace GlobalTheory.MixHt.StepVal

variable {k : Type} [CommRing k]

theorem recVal_eq_of_same (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ)
    (hall : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T)
    {X : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsAmb p) {T} (hT : IsMix p m T) {x : X} (hx : HasDim x (m + 1))
    (M : HermLB p) (L : Fin m → HermLB p) {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k}
    (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ p = q) (hg : i (genericPoint Y) = x)
    (M' M'' : HermLB q) (L' L'' : Fin m → HermLB q) (hM' : (M.pull i hi).Isometric M')
    (hM'' : (M.pull i hi).Isometric M'') (hL' : ∀ a, ((L a).pull i hi).Isometric (L' a))
    (hL'' : ∀ a, ((L a).pull i hi).Isometric (L'' a)) {r' : M'.B.ι → Y.functionFieldˣ} (hr' : IsRatSec M'.B r')
    {r'' : M''.B.ι → Y.functionFieldˣ} (hr'' : IsRatSec M''.B r'') :
    recVal (fun z => T m L (i z)) L' M' hr' = recVal (fun z => T m L (i z)) L'' M'' hr'' := by
  have hq : IsAmb q := by subst hi; exact hp.sub i
  have hY := dim_of_genericPoint hp i hx hg
  obtain ⟨T', hT'⟩ := hall k Y q hq
  have E : ∀ N : Fin m → HermLB q, (∀ a, ((L a).pull i hi).Isometric (N a)) → ∀ z : Y, Order.coheight z = 1 →
      T m L (i z) = T' m N z := fun N hN z hz =>
    GlobalTheory.T.mixedHeight_unique_restrict_closedSubscheme k X Y p q hp i hi m m T T' hT hT' m le_rfl le_rfl L N hN z
      (((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq m hY).1 z).1 hz)
  rw [recVal_congr (E L' hL'), recVal_congr (E L'' hL'')]
  exact recVal_indep hInt hRec m hq hY hT' L' L'' (fun a => (hL' a).symm.trans (hL'' a)) M' M''
    (hM'.symm.trans hM'') hr' hr''

theorem recVal_eq_of_two (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ)
    (hall : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T)
    {X : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsAmb p) {T} (hT : IsMix p m T) {x : X} (hx : HasDim x (m + 1))
    (M : HermLB p) (L : Fin m → HermLB p)
    {Y₁ : Scheme.{0}} [IsIntegral Y₁] [IsLocallyNoetherian Y₁] {q₁ : Y₁ ⟶ Sp k}
    (i₁ : Y₁ ⟶ X) [IsClosedImmersion i₁] (hi₁ : i₁ ≫ p = q₁) (hg₁ : i₁ (genericPoint Y₁) = x)
    (M₁ : HermLB q₁) (L₁ : Fin m → HermLB q₁) (hM₁ : (M.pull i₁ hi₁).Isometric M₁)
    (hL₁ : ∀ a, ((L a).pull i₁ hi₁).Isometric (L₁ a)) {r₁ : M₁.B.ι → Y₁.functionFieldˣ} (hr₁ : IsRatSec M₁.B r₁)
    {Y₂ : Scheme.{0}} [IsIntegral Y₂] [IsLocallyNoetherian Y₂] {q₂ : Y₂ ⟶ Sp k}
    (i₂ : Y₂ ⟶ X) [IsClosedImmersion i₂] (hi₂ : i₂ ≫ p = q₂) (hg₂ : i₂ (genericPoint Y₂) = x)
    (M₂ : HermLB q₂) (L₂ : Fin m → HermLB q₂) (hM₂ : (M.pull i₂ hi₂).Isometric M₂)
    (hL₂ : ∀ a, ((L a).pull i₂ hi₂).Isometric (L₂ a)) {r₂ : M₂.B.ι → Y₂.functionFieldˣ} (hr₂ : IsRatSec M₂.B r₂) :
    recVal (fun z => T m L (i₁ z)) L₁ M₁ hr₁ = recVal (fun z => T m L (i₂ z)) L₂ M₂ hr₂ := by
  obtain ⟨g, hiso, hgi, hη⟩ := GlobalTheory.T.exists_iso_closedImmersions_same_genericPoint X Y₁ Y₂ i₁ i₂ (hg₁.trans hg₂.symm)
  have hgq : g ≫ q₁ = q₂ := by rw [← hi₁, ← hi₂, ← Category.assoc, hgi]
  have hq₁ : IsAmb q₁ := by subst hi₁; exact hp.sub i₁
  have hq₂ : IsAmb q₂ := by subst hi₂; exact hp.sub i₂
  have hY₁ := dim_of_genericPoint hp i₁ hx hg₁
  have tr := GlobalTheory.T.inductive_height_formula_rhs_transport_iso k Y₁ Y₂ q₁ q₂ hq₁ hq₂ g hgq hη hiso m hY₁ (fun z => T m L (i₁ z)) L₁ M₁ r₁ hr₁
  rw [← tr]
  have hfun : (fun w => T m L (i₁ (g w))) = fun w => T m L (i₂ w) := by
    funext w
    rw [← hgi]
    simp
  rw [hfun]
  refine recVal_eq_of_same hInt hRec m hall hp hT hx M L i₂ hi₂ hg₂ _ _ _ _ ?_ hM₂ (fun a => ?_) hL₂ _ hr₂
  · exact (isometric_pull_pull' M i₁ hi₁ g hgq i₂ hi₂ hgi).symm.trans (hM₁.pull g hgq)
  · exact (isometric_pull_pull' (L a) i₁ hi₁ g hgq i₂ hi₂ hgi).symm.trans ((hL₁ a).pull g hgq)

theorem step_val : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k),
    IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ T,
    IsMix p m T → ∀ (x : X), HasDim x (m + 1) → ∀ (M : HermLB p) (L : Fin m → HermLB p), ∃ v : ℝ,
    ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ p = q), i (genericPoint Y) = x → ∀ (M' : HermLB q) (L' : Fin m → HermLB q),
    (M.pull i hi).Isometric M' → (∀ a, ((L a).pull i hi).Isometric (L' a)) →
    ∀ (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r), v = recVal (fun z => T m L (i z)) L' M' hr := by
  intro hInt hRec m hall k _ X p hp T hT x hx M L
  classical
  by_cases H : ∃ v : ℝ, ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (q : Y ⟶ Sp k)
      (i : Y ⟶ X) (_ : IsClosedImmersion i) (hi : i ≫ p = q) (_ : i (genericPoint Y) = x) (M' : HermLB q)
      (L' : Fin m → HermLB q) (_ : (M.pull i hi).Isometric M') (_ : ∀ a, ((L a).pull i hi).Isometric (L' a))
      (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r), v = recVal (fun z => T m L (i z)) L' M' hr
  · obtain ⟨v, Y₁, _, _, q₁, i₁, _, hi₁, hg₁, M₁, L₁, hM₁, hL₁, r₁, hr₁, rfl⟩ := H
    exact ⟨_, fun Y _ _ q i _ hi hg M' L' hM hL r hr =>
      recVal_eq_of_two hInt hRec m hall hp hT hx M L i₁ hi₁ hg₁ M₁ L₁ hM₁ hL₁ hr₁ i hi hg M' L' hM hL hr⟩
  · exact ⟨0, fun Y _ _ q i _ hi hg M' L' hM hL r hr =>
      absurd ⟨_, Y, ‹_›, ‹_›, q, i, ‹_›, hi, hg, M', L', hM, hL, r, hr, rfl⟩ H⟩

end GlobalTheory.MixHt.StepVal

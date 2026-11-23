import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedAtPlaceOfIsHalfSplitPoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationEqOnVacuaOfEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricTestFunctionIntegralAdelicReductionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameMovedBackIsLatticeBasisStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralFrameMatrixIffMemSplitHalfHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ListConvolutionDistinctPlacesSupportedAndComposiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseEqOfSameIdempotentPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QVec
open GlobalTheory.LocMod.StepVec
open Formalism.L2.DIV (kP resS)

variable {D : D7} {S T : HSp D}

def datum (e : AE D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (om : (∀ w : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP w)) → ℂ) : WO S T → ℂ :=
  fun x => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then om (fun w => redM w (frMapO S T βS βT x)) else 0

section One
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem model (q : GlobalTheory.FinPl.SplitPt D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT)
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    {w : Formalism.L2.DIV.Pl D.host.E} (hw : w ∈ P) (hq : Formalism.L2.NTheta.IsIdemAt q.e w) {π' : EAf D →+* k}
    (hint : ∀ z : EAf D, z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' z ∈ 𝒪[k])
    (hres : ∀ w' : Formalism.L2.DIV.Pl D.host.E, w' ≠ w → ∀ (z : EAf D) (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
      (hz' : (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
      resS D.host.F w' ⟨(1 - toEAf D q.e) * z, hz'⟩ = resS D.host.F w' ⟨z, hz⟩)
    (W : (∀ w : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP w)) → ℂ)
    (hW : ∀ y y', (∀ w' ∈ P.erase w, y w' = y' w') → W y = W y')
    {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀) {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm) :
    ∃ T₁, (ofSplit q).IsModel ψ FS FT T₁ ∧ ∀ om (Φ₀ : Matrix (Fin T.rank) (Fin S.rank) k → ℂ),
      (∀ z, Φ₀ z ≠ 0 → ∀ i j, z i j ∈ 𝒪[k]) →
      (∀ N, IsIntM N → om (fun w => redM w N) = Φ₀ (N.map π') * W fun w => redM w N) → ∀ Φ : SB (Matrix Y Y' k),
      (∀ x, Φ.1 ((ofSplit q).down FS FT x) = Φ₀ ((frMapO S T βS βT x).map π')) → Tm (datum e βS βT om) = T₁ Φ := by
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hqe := idem_mul he hw hq
  have hinf' : infPart D (e - q.e) = 0 := by
    rw [← hqe, RingHom.map_sub, RingHom.map_mul, hinf, mul_zero, sub_zero]
  have hΩ := GlobalTheory.PlaceDatum.isSBHalf_of_red (e - q.e) (latO S T ΛS ΛT fun _ => True) (frMapO S T βS βT)
    (GlobalTheory.PlaceDatum.frMapO_add βS βT) (GlobalTheory.PlaceDatum.exists_den_frMapO hS.fg hT.fg βS βT)
    (by
      obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO hS hT βS βT
      exact ⟨K, hK, fun t ht => h t (GlobalTheory.PlaceDatum.infPart_of_half hinf' ht)⟩) (P.erase w) W hW
  refine ⟨_, isModel_extend (ofSplit q) FS FT hqe hTm
    (GlobalTheory.DiagLiftFix.isTheta_placeModel hψ hS hT hee he.2 hinf hf₀ Tm hTm) _
    (GlobalTheory.T.isSchwartzBruhatHalf_splitPlace_product D k q Y Y' S T FS FT ΛS ΛT hS hT e hee hqe _ hΩ), fun om Φ₀ h0 h1 Φ hΦ => ?_⟩
  refine congrArg Tm (funext fun x => ?_)
  rw [extend_apply, hΦ]
  have h3 : ∀ i j, frMapO S T βS βT ((1 - q.e) • x) i j = (1 - toEAf D q.e) * frMapO S T βS βT x i j :=
    fun i j => by rw [frMapO_smul, RingHom.map_sub, RingHom.map_one]
  have h4 : IsIntM (frMapO S T βS βT x) → IsIntM (frMapO S T βS βT ((1 - q.e) • x)) := fun hi i j => by
    rw [h3]; exact ((hint _).1 (hi i j)).1
  have h6 : Φ₀ ((frMapO S T βS βT x).map π') ≠ 0 → IsIntM (frMapO S T βS βT ((1 - q.e) • x)) → IsIntM (frMapO S T βS βT x) :=
    fun h5 h6 i j => (hint _).2 ⟨by rw [← h3]; exact h6 i j, h0 _ h5 i j⟩
  have h2 : IsHalf e x → IsHalf (e - q.e) ((1 - q.e) • x) := fun hx i j => idempotent_sub_mul_complement_eq_complement (hx i j) q.split.1 hqe
  exact ite_and_eq_ite_mul_ite_of_implications h4 (h1 _) (fun hi => hW _ _ fun w' hw' => redM_eq hi (h4 hi) h3 (hres w' (Finset.ne_of_mem_erase hw'))) h6 h2

end One

def Puts (ψ : AddChar (AF D.host.F) ℂ) (A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (e : AE D) (βS : GL (Fin S.rank) (EAf D))
    (βT : GL (Fin T.rank) (EAf D)) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (w : Formalism.L2.DIV.Pl D.host.E)
    (loc : Matrix (Fin T.rank) (Fin S.rank) (kP w) → ℂ) (c : WO S T →₀ ℂ) : Prop :=
  ∀ W : (∀ w : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP w)) → ℂ,
    (∀ y y', (∀ w' ∈ P.erase w, y w' = y' w') → W y = W y') →
    A (datum e βS βT fun y => loc (y w) * W y) = comb ψ S T c (A (datum e βS βT W))

section Two
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem puts (q : GlobalTheory.FinPl.SplitPt D k) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {χS χT} {om : Om S T}
    (hom : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT)
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    {w : Formalism.L2.DIV.Pl D.host.E} (hw : w ∈ P) (hq : Formalism.L2.NTheta.IsIdemAt q.e w)
    {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀) {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm)
    {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (ea : ι' ≃ Fin S.rank) (eb : ι ≃ Fin T.rank)
    (Φι : Matrix ι ι' k → ℂ) (h0 : ∀ z, Φι z ≠ 0 → ∀ i j, z i j ∈ 𝒪[k]) (loc : Matrix (Fin T.rank) (Fin S.rank) (kP w) → ℂ)
    (h1 : ∀ π' : EAf D →+* k, (∀ a, π' (toEAf D a) = q.pr a) →
      GlobalTheory.FunObj.Comparison₂.IsRed (resS D.host.F w) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) →
      ∀ N : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E),
      Φι ((N.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix eb ea) = loc (N.map (resS D.host.F w)))
    (GS : Frame k S.rank Y') (GT : Frame k T.rank Y) (oS : ι' ≃ Y') (oT : ι ≃ Y) (g : GA D S) (h : GA D T)
    (mS : MovedTo (ofSplit q) S g βS (GS.β.submatrix id fun i => oS (ea.symm i)))
    (mT : MovedTo (ofSplit q) T h βT (GT.β.submatrix id fun i => oT (eb.symm i)))
    {Ξ : Matrix Y Y' k → ℂ} (hΞ : Ξ ∈ SB (Matrix Y Y' k))
    (hΞ' : Ξ = (⟨oT, 1⟩ : LatFrame k ι Y).transport (⟨oS, 1⟩ : LatFrame k ι' Y') Φι)
    {c : WO S T →₀ ℂ} (hc : (ofSplit q).IsCombAt ψ GS GT c Ξ) :
    Puts ψ (om (g, h) ∘ₗ Tm) e βS βT P w loc c := by
  intro W hW
  obtain ⟨π', hπ, hred, hint, hres⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D k q w hq
  obtain ⟨T₁, hT₁, hT'⟩ := model q (moved (ofSplit q) GS g⁻¹) (moved (ofSplit q) GT h⁻¹) hom.std hS hT βS βT he hw hq hint hres W hW
    hf₀ hTm
  obtain ⟨T₂, hT₂, hT''⟩ := GlobalTheory.T.isLocalModel_creation_weilAction_moved_frames D k (ofSplit q) Y Y' S T _ GS _ GT ψ θ _ _ om hθ hom g h
    (β_eq_moved _ GS g) (β_eq_moved _ GT h) 0 0 0 0 1 T₁ hT₁
  simp only [GlobalTheory.FiniteFock.pureTensorO_one] at hT''
  have hco := coords_down (ofSplit q) (moved (ofSplit q) GS g⁻¹) (moved (ofSplit q) GT h⁻¹) hπ
    (⟨oS, 1⟩ : LatFrame k ι' Y') (⟨oT, 1⟩ : LatFrame k ι Y) ea eb
    (map_eq_of_movedTo _ GS hπ 1 _ (by rw [Matrix.mul_one]; exact mS))
    (map_eq_of_movedTo _ GT hπ 1 _ (by rw [Matrix.mul_one]; exact mT))
  obtain ⟨O, hO⟩ := GlobalTheory.BiComb.exists_isOne (k := k) Y Y'
  have e1 := hT' (fun y => loc (y w) * W y) (fun z => Φι (z.submatrix eb ea))
    (fun z hz i j => by simpa using h0 _ hz (eb.symm i) (ea.symm j))
    (fun N hN => by
      beta_reduce
      rw [redM_eq_map w hN, ← h1 π' hπ hred]
      rfl) ⟨Ξ, hΞ⟩ (fun x => by rw [← hco x]; exact congrFun hΞ' _)
  have e2 := hT' W (fun z => if ∀ i j, z i j ∈ 𝒪[k] then 1 else 0)
    (fun z hz => by_contra fun h => hz (if_neg h))
    (fun N hN => by
      rw [if_pos (show ∀ i j, N.map π' i j ∈ 𝒪[k] from fun i j => ((hint _).1 (hN i j)).2), one_mul]) O (fun x => by
      have h5 := hco x
      simp only [LatFrame.coords, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at h5
      rw [hO, Set.indicator_apply]
      refine if_congr ⟨fun H i j => ?_, fun H i j => ?_⟩ rfl rfl
      · have h6 := congrFun (congrFun h5 (eb.symm i)) (ea.symm j)
        simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply] at h6
        rw [← h6]; exact H _ _
      · have h6 := congrFun (congrFun h5 (oT.symm i)) (oS.symm j)
        simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply] at h6
        rw [h6]; exact H _ _)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, e2, ← hT'', ← hT'']
  exact hc.2 T₂ hT₂ O _ hO rfl

end Two

def locQ {κ : Type} [CommRing κ] {a b : ℕ} (r : ℕ) (ξ : κˣ →* ℂˣ) (y : Matrix (Fin b) (Fin a) κ) : ℂ :=
  if H : LowZero r y ∧ IsUnit (topL r y).det then ((ξ H.2.unit : ℂˣ) : ℂ) else 0

theorem iterate {ψ : AddChar (AF D.host.F) ℂ} {A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} {e : AE D} {βS : GL (Fin S.rank) (EAf D)}
    {βT : GL (Fin T.rank) (EAf D)} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {ι : Type} {pl : ι → Formalism.L2.DIV.Pl D.host.E}
    (hpl : Function.Injective pl) (hP : ∀ i, pl i ∈ P) (loc : ∀ i, Matrix (Fin T.rank) (Fin S.rank) (kP (pl i)) → ℂ)
    (c : ι → WO S T →₀ ℂ) (h : ∀ i, Puts ψ A e βS βT P (pl i) (loc i) (c i)) (L : List ι) (hL : L.Nodup) :
    A (datum e βS βT fun y => (L.map fun i => loc i (y (pl i))).prod) =
      L.foldr (fun i g => comb ψ S T (c i) g) (A (datum e βS βT fun _ => 1)) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    rw [List.nodup_cons] at hL
    simp only [List.map_cons, List.prod_cons, List.foldr_cons]
    rw [← ih hL.2]
    refine h i _ fun y y' hy => congrArg List.prod (List.map_congr_left fun i' hi' => ?_)
    rw [hy (pl i') (Finset.mem_erase.2 ⟨fun H => hL.1 (hpl H ▸ hi'), hP i'⟩)]

theorem omegaG_of_empty {a b : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ a) (hL : L.Pg = ∅) (χj)
    (y : ∀ w : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (kP w)) : omegaG L χj y = 1 := by
  haveI : IsEmpty L.Pg := ⟨fun w => Finset.notMem_empty w.1 (hL ▸ w.2)⟩
  rw [omegaG, dif_pos ⟨fun w hw => isEmptyElim (⟨w, hw⟩ : L.Pg), fun w => isEmptyElim w, fun w => isEmptyElim w,
    fun w => isEmptyElim w, by convert L.P.H.one_mem using 1⟩]
  rw [Fintype.prod_empty, Fintype.prod_empty, mul_one, mul_one, Subsingleton.elim (⟨_, _⟩ : L.P.H) 1, map_one, Units.val_one]

theorem om_comb {ψ : AddChar (AF D.host.F) ℂ} {χS χT} {om : Om S T} (hom : IsWeilDatumO ψ S T χS χT om) (g : GA D S) (h : GA D T)
    (c : WO S T →₀ ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (comb ψ S T (c.mapDomain (actO S T g⁻¹ h⁻¹)) f) = comb ψ S T c (om (g, h) f) := by
  change om (g, h) ((c.mapDomain _).sum fun u a => a • heisO ψ S T u f) = c.sum fun u a => a • heisO ψ S T u (om (g, h) f)
  rw [Finsupp.sum_mapDomain_index (h := fun u (a : ℂ) => a • heisO ψ S T u f) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _), Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_smul, hom.om_heis g h _ f hf, GlobalTheory.LocModMove.actO_actO_inv'']

theorem combAt_mapDomain {P : GlobalTheory.FinPl.Pl D → Prop} {c : WO S T →₀ ℂ} (hc : GlobalTheory.FinPl.CombAt P c) (g : GA D S) (h : GA D T) :
    GlobalTheory.FinPl.CombAt P (c.mapDomain (actO S T g h)) := by
  intro u hu i j
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
  rw [actO, Matrix.mul_apply]
  refine Ideal.sum_mem _ fun a _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (hc x hx b a)

theorem gen {r : ℕ} {k : Fin r → Type} [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i))
    (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (hq : ∀ i, Formalism.L2.NTheta.IsIdemAt (q i).e (pl i)) (hU : ∀ i, (q i).UnitAA)
    (hv : Function.Injective fun i => (q i).v) {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (hQ : ∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP)
    {P : GlobalTheory.FinPl.Pl D → Prop} (hP : ∀ p, P p ↔ ∃ i, (q i).v = p) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT}
    {om : Om S T} (hom : IsWeilDatumO ψ S T χS χT om) {ΛS : GlobalTheory.FinPl.Lat S} {ΛT : GlobalTheory.FinPl.Lat T} (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)} (g : GA D S) (h : GA D T)
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank} (hL : L.Pg = ∅) {sS sT χj ξ vac} {d : WO S T →₀ ℂ} (h0 : vac ≠ 0)
    (hd : GlobalTheory.FinPl.CombAt P d)
    (hst : IsStepVecOf ψ θ S T sS sT (ΛS : Set _) (ΛT : Set _) βS βT L χj Q ξ vac (comb ψ S T d vac))
    (c : Fin r → WO S T →₀ ℂ) (hc : ∀ i, ∀ u ∈ (c i).support, IsHalf ((q i).e + cA D (q i).e) u)
    (hlat : ∀ i (π' : EAf D →+* k i), (∀ a, π' (toEAf D a) = (q i).pr a) →
      (∀ y : Fin S.rank → k i, (∀ a, y a ∈ 𝒪[k i]) ↔
        (fun a => (q i).sec ((βS.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV S ΛS (· = (q i).v)) ∧
      ∀ y : Fin T.rank → k i, (∀ a, y a ∈ 𝒪[k i]) ↔
        (fun a => (q i).sec ((βT.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV T ΛT (· = (q i).v))
    (hput : ∀ e, IsIdemSum e Q → ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 vac Tm →
      ∀ i, Puts ψ (om (g, h) ∘ₗ Tm) e βS βT Q (pl i) (locQ L.r (ξ (pl i))) (c i))
    (f : WO S T → ℂ) (hf : GlobalTheory.FinPl.Vac ψ S T ΛS ΛT P f) :
    om (g, h) (comb ψ S T d f) = comb ψ S T (aconv (List.ofFn c)) (om (g, h) f) := by
  obtain ⟨hvac, e, he, ⟨Tm, hTm⟩, hall⟩ := hst
  rw [hL, Finset.empty_union] at he
  have hpl : Function.Injective pl := fun i i' H => hv (GlobalTheory.T.splitPlace_baseEq_of_same_idempotentPrime D _ _ (q i) (q i') _ (hq i) (H ▸ hq i'))
  have hcv := GlobalTheory.T.listConvolution_distinctPlaces_supported_and_composition D ψ S T (Fin r) (fun i => (q i).v) c hv
    (fun i u hu => GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above D _ (q i) _ _ u (hc i u hu)) (List.finRange r) (List.nodup_finRange r)
  rw [← List.ofFn_eq_map] at hcv
  have hcP : GlobalTheory.FinPl.CombAt P (aconv (List.ofFn c)) := by
    have : P = fun p => ∃ i ∈ List.finRange r, (q i).v = p := funext fun p => propext (by simpa using hP p)
    rw [this]; exact hcv.1
  have e0 : Tm (datum e βS βT fun _ => 1) = vac := by
    rw [← hTm.vac, one_smul]
    refine congrArg Tm (funext fun x => if_congr ?_ rfl rfl)
    rw [and_comm]
    exact and_congr_left fun hx => GlobalTheory.T.integralFrameMatrix_iff_mem_splitHalfHomLattice D r k q pl Q e hq hU hpl hQ he S T ΛS ΛT hS hT βS βT hlat x hx
  have e1 : comb ψ S T d vac = Tm (datum e βS βT fun y => ((List.finRange r).map fun i => locQ L.r (ξ (pl i)) (y (pl i))).prod) := by
    refine (hall Tm hTm).trans (congrArg Tm (funext fun x => if_congr Iff.rfl ?_ rfl))
    have hQ' : Q = Finset.univ.image pl := Finset.ext fun w => by simpa using hQ w
    rw [omegaG_of_empty L hL, one_mul, GlobalTheory.FunObj.Comparison₂.omegaQ_eq_prod, hQ', Finset.prod_image fun _ _ _ _ H => hpl H,
      Fin.prod_univ_def]
    rfl
  have e2 := iterate hpl (fun i => (hQ _).2 ⟨i, rfl⟩) _ c (hput e he Tm hTm) (List.finRange r) (List.nodup_finRange r)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← e1, e0, ← hcv.2, ← om_comb hom g h _ hvac.2.theta] at e2
  have e3 := congrArg (om (g, h)⁻¹) e2
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    Module.End.one_apply] at e3
  have hle : latO S T (ΛS : Set _) (ΛT : Set _) P ≤ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True :=
    AddSubgroup.closure_mono fun w ⟨α, hα, _, hw⟩ => ⟨α, hα, fun _ h => absurd trivial h, hw⟩
  rw [GlobalTheory.T.heisenbergCombination_eq_on_vacua_of_eq_one D r k q P hv hP ψ hom.std S T ΛS ΛT hS hT d _ hd (combAt_mapDomain hcP g⁻¹ h⁻¹) vac
    ⟨hvac.2.theta, fun u hu => hvac.2.lat.1 u (hle hu), fun e he u hu hh => hvac.2.lat.2 e he u (hle hu) hh⟩ h0 e3 f hf,
    om_comb hom g h _ hf.1]

theorem lat_of_movedTo {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {g : GA D S} {Λ N : GlobalTheory.FinPl.Lat S}
    {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) (hΛ : IsSelfDualC S Λ) (hN : IsSelfDualC S N) (hm : GlobalTheory.FinPl.Moves S g Λ N P)
    {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (σ : Fin S.rank ≃ Y) {β : GL (Fin S.rank) (EAf D)}
    (hβ : MovedTo (ofSplit q) S g β (F.β.submatrix id σ))
    (hF : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S N (· = q.v))
    (π' : EAf D →+* k) (hπ : ∀ a, π' (toEAf D a) = q.pr a) (y : Fin S.rank → k) :
    (∀ a, y a ∈ 𝒪[k]) ↔ (fun a => q.sec ((β.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV S Λ (· = q.v) := by
  have h1 := map_eq_of_movedTo (ofSplit q) F hπ 1 σ (by rw [Matrix.mul_one]; exact hβ)
  have h2 := GlobalTheory.T.splitPlaceFrame_movedBack_isLatticeBasis D k q S g Λ N P hP hΛ hN hm Y _ _ (β_eq_moved (ofSplit q) F g) hF (y ∘ σ.symm)
  rw [h1, Matrix.mul_one, Matrix.submatrix_mulVec_equiv]
  refine Iff.trans ⟨fun H i => H _, fun H a => ?_⟩ h2
  simpa using H (σ a)

theorem int_of_parPhi {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a s s' : Type} [Fintype a] [DecidableEq a] [Fintype s'] [DecidableEq s']
    (δ : kˣ →* ℂˣ) (z : Matrix (a ⊕ s) (a ⊕ s') k) (hz : parPhi δ z ≠ 0) (i j) : z i j ∈ 𝒪[k] := by
  obtain ⟨⟨g, hg, e⟩, h1, h2, h3⟩ := (parPhi_ne_zero_iff δ).1 hz
  rcases i with i | i <;> rcases j with j | j
  · have := intM_of_mem_KO hg i j
    rw [e] at this
    exact this
  · exact h2 i j
  · exact h1.intM i j
  · exact h3 i j

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (χ : ℕ → (AE D)ˣ →* Circle), c.Is → v.Is → ∀ (r : ℕ) (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (G : ∀ i, QGeo v B (pl i)) (E : ∀ i, QExt (G i) χ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (S : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (G i).q.v) → (∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP) → (∀ p, S p ↔ ∃ i, (G i).q.v = p) → (∀ i, (G i).Res (E i).δ (ξ (pl i))) → (∀ i, D.R.r = D.R.k + ((G i).s + 1)) → ∀ j, j + 1 < D.R.m → GlobalTheory.FinPl.Moves (c.V j) (B.b j) (B.Λ j) (v.N j) S → GlobalTheory.FinPl.Moves (c.V (j + 1)) (B.b (j + 1)) (B.Λ (j + 1)) (v.N (j + 1)) S → B.b j ∈ GfC (c.V j) → B.b (j + 1) ∈ GfC (c.V (j + 1)) → IsSelfDualC _ (B.Λ j) → IsSelfDualC _ (B.Λ (j + 1)) → ∀ sS sT (LS : Formalism.L2.DIV.LevDat D.host.E ℂ (c.V j).rank) χj vac (d : WO (c.V j) (c.V (j + 1)) →₀ ℂ), LS.Pg = ∅ → LS.r = D.R.r → vac ≠ 0 → GlobalTheory.FinPl.CombAt S d → IsStepVecOf c.ψ c.θ (c.V j) (c.V (j + 1)) sS sT (B.Λ j : Set _) (B.Λ (j + 1) : Set _) (B.β j) (B.β (j + 1)) LS χj Q ξ vac (comb c.ψ _ _ d vac) → ∀ χS χT om, IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) χS χT om → ∀ g, GlobalTheory.FinPl.Vac c.ψ _ _ (B.Λ j) (B.Λ (j + 1)) S g → om (B.b j, B.b (j + 1)) (comb c.ψ _ _ d g) = comb c.ψ _ _ (aconv (List.ofFn fun i => (E i).eL j)) (om (B.b j, B.b (j + 1)) g) := by
  intro D c v B χ hc hv r pl G E ξ Q S hinj hQ hS hres hrk j hj hmv hmv' hb hb' hsd hsd' sS sT LS χj vac d hPg hLr hvac hd hstep
    χS χT om hom g hg
  have hn : ∀ i, ∃ n, j + n = (G i).s := fun i => ⟨(G i).s - j, by have := (G i).hs; omega⟩
  refine gen (fun i => (G i).q) pl (fun i => (G i).idem) (fun i => (G i).unit) hinj hQ hS hom hsd hsd' _ _ hPg hvac hd hstep
    (fun i => (E i).eL j) (fun i => ?_) (fun i π' hπ => ?_) (fun e he Tm hTm i => ?_) g hg
  · obtain ⟨n, hn⟩ := hn i
    exact ((E i).eL_at j n hn).1
  · obtain ⟨n, hn⟩ := hn i
    obtain ⟨ea, -, mS⟩ := (G i).frame j (n + 1) (by omega)
    obtain ⟨eb, -, mT⟩ := (G i).frame (j + 1) n (by omega)
    exact ⟨lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd (hv.sd j (by omega)) hmv _ (ea.symm.trans (stdOrd _ _ j (n + 1) (by omega))) mS
        ((G i).latY j (n + 1) _) π' hπ,
      lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd' (hv.sd (j + 1) hj) hmv' _ (eb.symm.trans (stdOrd _ _ (j + 1) n (by omega))) mT
        ((G i).latY (j + 1) n _) π' hπ⟩
  · obtain ⟨n, hn⟩ := hn i
    obtain ⟨ea, ha, mS⟩ := (G i).frame j (n + 1) (by omega)
    obtain ⟨eb, hb, mT⟩ := (G i).frame (j + 1) n (by omega)
    exact puts (G i).q hstep.1.2.inf hom hsd.1 hsd'.1 _ _ he ((hQ _).2 ⟨i, rfl⟩) (G i).idem hstep.1.2.theta hTm ea eb
      (parPhi (E i).δ) (int_of_parPhi _) _
      (fun π' hπ hred N => GlobalTheory.T.parahoricTestFunction_integralAdelic_reduction D _ (G i).q (pl i) π' hπ hred _ (E i).tame _ (hres i) _ _ _ _ _ _ _ _
        (hLr.trans (hrk i)) ea eb ha hb N) _ _ _ _ _ _ mS mT ((E i).reg.1 j n hn) rfl ((E i).eL_at j n hn)

end GlobalTheory.QVec
end

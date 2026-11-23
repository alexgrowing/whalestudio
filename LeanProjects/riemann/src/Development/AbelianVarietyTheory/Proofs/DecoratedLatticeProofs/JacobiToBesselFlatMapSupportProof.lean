import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionSelfDualWittSplitAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSeStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SuppShift

variable {D : D7}

theorem mulVec_latA {S T : HSp D} {L : Lat S} {L' : Lat T} {P : Pl D → Prop} (M : Mx D T.rank S.rank)
    (hM : ∀ y ∈ latV S L P, M *ᵥ y ∈ latV T L' P) {z : Fin S.rank → AE D} (hz : z ∈ latA S L P) :
    M *ᵥ z ∈ latA T L' P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    set u : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hu
    have hu' : u ∈ latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have heq : M *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
        fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (M *ᵥ u) k := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hu]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
      rw [h1]; ring
    rw [heq]
    exact VacFlat.smul_mem_latA ha (hM u hu')
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem latA_supp {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D} (hy : y ∈ latA S L P)
    (i : Fin S.rank) : y i ∈ idAt D P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, -, hα, c, -, x, -, rfl⟩ := hy
    exact LatMem.tmul_mem_idAt hα _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem smul_latV {S : HSp D} {L : Lat S} {P : Pl D → Prop} {w : AE D} (hw : finPart D w ∈ intAE D)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : w • y ∈ latV S L P := LatIndHalf.mul_mem_latV hw hy

theorem smul_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {w : AE D} (hw : finPart D w ∈ intAE D)
    {y : Fin S.rank → AE D} (hy : y ∈ latA S L P) : w • y ∈ latA S L P := by
  have h := mulVec_latA (L := L) (L' := L) (P := P) (w • (1 : Mx D S.rank S.rank))
    (fun y hy => by rw [Matrix.smul_mulVec, Matrix.one_mulVec]; exact smul_latV hw hy) hy
  rwa [Matrix.smul_mulVec, Matrix.one_mulVec] at h

theorem smul_latO {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    {P : Pl D → Prop} {w : AE D} (hw : finPart D w ∈ intAE D) {u : WO S T}
    (hu : u ∈ latO S T (LS : Set _) (LT : Set _) P) : w • u ∈ latO S T (LS : Set _) (LT : Set _) P := by
  refine (LatMem.mem_latO_iff D S T LS LT hS hT P _).2
    ⟨fun i j => Ideal.mul_mem_left _ _ (LatMem.latO_mxAt hu i j), fun y hy => ?_⟩
  change (w • u) *ᵥ y ∈ _
  rw [Matrix.smul_mulVec]
  exact smul_latA hw (LatMem.latO_maps hS hu hy)

theorem mxAt_mul_left {P : Pl D → Prop} {l m n : ℕ} (A : Mx D l m) {x : Mx D m n} (hx : MxAt P x) : MxAt P (A ⬝ x) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hx k j)

theorem mxAt_mul_right {P : Pl D → Prop} {l m n : ℕ} {x : Mx D l m} (hx : MxAt P x) (A : Mx D m n) : MxAt P (x ⬝ A) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hx i k)

theorem mxAt_smul {P : Pl D → Prop} {m n : ℕ} (c : AE D) {x : Mx D m n} (hx : MxAt P x) : MxAt P (c • x) :=
  fun i j => Ideal.mul_mem_left _ _ (hx i j)

theorem sandwich_latO {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    {P : Pl D → Prop} (A : Mx D T.rank T.rank) (hA : ∀ y ∈ latV T LT P, A *ᵥ y ∈ latV T LT P) (B : Mx D S.rank S.rank)
    (hB : ∀ y ∈ latV S LS P, B *ᵥ y ∈ latV S LS P) {u : WO S T}
    (hu : u ∈ latO S T (LS : Set _) (LT : Set _) P) : A ⬝ (u ⬝ B) ∈ latO S T (LS : Set _) (LT : Set _) P := by
  refine (LatMem.mem_latO_iff D S T LS LT hS hT P _).2
    ⟨mxAt_mul_left _ (mxAt_mul_right (LatMem.latO_mxAt hu) _), fun y hy => ?_⟩
  change (A ⬝ (u ⬝ B)) *ᵥ y ∈ _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact mulVec_latA A hA (LatMem.latO_maps hS hu (hB y hy))

def eps (v : Pl D) : AE D := algebraMap (AF D.host.F) (AE D) (SelfDualAt.cP (· = v))

theorem eps_mul {v : Pl D} {a : AE D} (ha : a ∈ idAt D (· = v)) : eps v * a = a := SelfDualAt.algebraMap_placeIdempotent_mul _ a ha

theorem eps_idAt (v : Pl D) : eps v ∈ idAt D (· = v) := by
  change pairA D.host.F 0 (SelfDualAt.indP (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E) ∈ _
  refine LatMem.tmul_mem_idAt (fun w hw => ?_) _
  rw [SelfDualAt.evalV_indP, if_neg hw]

theorem int_of_idem {e : AE D} (he : e * e = e) : finPart D e ∈ intAE D :=
  AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he])

theorem eps_int (v : Pl D) : finPart D (eps v) ∈ intAE D := int_of_idem (eps_mul (eps_idAt v))

def intSub (v : Pl D) : AddSubgroup (AE D) :=
  (idAt D (· = v)).toAddSubgroup ⊓ (intAE D).comap (finPart D).toAddMonoidHom

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  rw [heisO, symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]

set_option maxHeartbeats 800000 in

theorem exists_parts {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) {v : Pl D} (hv : Tame D v) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT (· = v) f) :
    ∃ a b : AE D, a + b = 1 ∧ ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = v),
      heisO ψ S T (a • u) f = f ∧ heisO ψ S T (b • u) f = f := by
  rcases hv.2 with h2 | ⟨e, ε, he, hε, hsum⟩
  · refine ⟨1, 0, add_zero _, fun u hu => ⟨?_, by rw [zero_smul, heisO_zero]⟩⟩
    have h2' : ((2 : ℤ) : 𝓞 D.host.F) ∉ v.asIdeal := by exact_mod_cast h2
    have hint := AeUnit.inv_smul_singleV_mem v 2 h2'
    set α : Af D.host.F := ((2 : ℤ) : D.host.F)⁻¹ • singleV D.host.F v 1 with hα
    have hw : finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAE D :=
      AddSubgroup.subset_closure ⟨α, hint, 1, rfl⟩
    have hpl : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
      ⟨_, rfl, GlobalTheory.LatVac.evalV_singleV_same _ _, fun w hw => GlobalTheory.LatVac.evalV_singleV_ne _ v w hw⟩
    have hαα : α + α = singleV D.host.F v 1 := by
      rw [hα, ← add_smul, show ((2 : ℤ) : D.host.F)⁻¹ + ((2 : ℤ) : D.host.F)⁻¹ = 1 by push_cast; norm_num, one_smul]
    have hww : pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) + pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) =
        algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := by
      rw [← TensorProduct.add_tmul, ← hαα]
      change _ = pairA D.host.F 0 (α + α) ⊗ₜ[D.host.F] (1 : D.host.E)
      congr 1
      exact Prod.ext (add_zero _) rfl
    have h := hf.2.1 _ (smul_latO hS hT hw hu)
    have e2 : 2 • ((pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • u) = (1 : AE D) • u := by
      rw [two_smul, ← add_smul, hww, one_smul]
      ext i j
      exact ((placeIdem_acts D v _ hpl).1 _).1 (LatMem.latO_mxAt hu i j)
    rwa [e2] at h
  · have hce : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he.1]
    have he' : IsSplitIdem D (cA D e) :=
      ⟨hce, by rw [cA_cA, mul_comm]; exact he.2.1, v, ε, hε, by rw [cA_cA, add_comm]; exact hsum⟩
    refine ⟨e, 1 - e, by ring, fun u hu => ⟨?_, ?_⟩⟩
    · refine hf.2.2 e he _ (smul_latO hS hT (int_of_idem he.1) hu) fun i j => ?_
      change e * (e * u i j) = e * u i j
      rw [← mul_assoc, he.1]
    · have e2 : (1 - e) • u = cA D e • u := by
        ext i j
        have h := ((placeIdem_acts D v _ hε).1 _).1 (LatMem.latO_mxAt hu i j)
        rw [← hsum] at h
        rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, sub_mul, one_mul, sub_eq_iff_eq_add', ← add_mul, h]
      rw [e2]
      refine hf.2.2 _ he' _ (smul_latO hS hT (int_of_idem hce) hu) fun i j => ?_
      change cA D e * (cA D e * u i j) = cA D e * u i j
      rw [← mul_assoc, hce]

theorem exists_parts_om {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hom : IsWeilDatumO ψ S T χS χT om) {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) {v : Pl D} (hv : Tame D v) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT (· = v) f) (g : GA D T) :
    ∃ a b : AE D, a + b = 1 ∧ ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = v),
      heisO ψ S T (a • (mt T g ⬝ u)) (om (1, g) f) = om (1, g) f ∧
        heisO ψ S T (b • (mt T g ⬝ u)) (om (1, g) f) = om (1, g) f := by
  obtain ⟨a, b, hab, h⟩ := exists_parts hS hT hv hf
  have key : ∀ (c : AE D) (u : WO S T), heisO ψ S T (c • u) f = f →
      heisO ψ S T (c • (mt T g ⬝ u)) (om (1, g) f) = om (1, g) f := fun c u hc => by
    have h1 := hom.om_heis 1 g (c • u) f hf.1
    rw [hc, actO_eq, inv_one, mt_one, Matrix.mul_one, Matrix.mul_smul] at h1
    exact h1.symm
  exact ⟨a, b, hab, fun u hu => ⟨key a u (h u hu).1, key b u (h u hu).2⟩⟩

theorem colMul_mul {m n : ℕ} (x : Mx D m n) (i : Fin n) (c a : AE D) : colMul x i (c * a) = c • colMul x i a :=
  funext fun _ => mul_assoc _ _ _

theorem single_mulVec' {m n l : ℕ} (x : Mx D m n) (i : Fin n) (j : Fin l) (s : AE D) (y : Fin l → AE D) :
    (x ⬝ (Matrix.single i j s : Mx D n l)) *ᵥ y = colMul x i (s * y j) := by
  rw [← Matrix.mulVec_mulVec, Matrix.single_mulVec]
  funext k
  simp [Matrix.mulVec, dotProduct, colMul, Function.update_apply, mul_comm]

theorem mulVec_colMul {l m n : ℕ} (A : Mx D l m) (x : Mx D m n) (i : Fin n) (a : AE D) :
    A *ᵥ colMul x i a = colMul (A ⬝ x) i a := by
  funext k
  simp only [Matrix.mulVec, dotProduct, colMul, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem pX_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (a : AE D) :
    (d.pX *ᵥ colMul d.jX i a) i = a := by
  rw [mulVec_colMul, d.pX_jX, colMul, Matrix.one_apply_eq, mul_one]

theorem idAt_of_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {P : Pl D → Prop} {i : Fin ρ} {a : AE D}
    (h : colMul d.jX i a ∈ latV S L P) : a ∈ idAt D P := by
  rw [← pX_colMul d i a]
  exact IwaPlace.mulVec_mem_idAt _ (FrameLat.latV_supp h) i

theorem psi_parts (ψ : AddChar (AF D.host.F) ℂ) {a b : AE D} (hab : a + b = 1) {s : AE D} (ha : psiE ψ (a * s) = 1)
    (hb : psiE ψ (b * s) = 1) : psiE ψ s = 1 := by
  unfold psiE at *
  rw [← one_mul s, ← hab, add_mul, map_add, AddChar.map_add_eq_mul, ha, hb, one_mul]

theorem hO_extX {V V₀ W : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) (x : Mx D W.rank ρ) (u : WO V W) :
    hO V W (dV.extX W x) u = pairS W x (u ⬝ dV.jY) := by
  rw [dV.hO_coordS]
  simp only [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, HypDec.pX_j0, HypDec.pX_jY, Matrix.mul_one,
    Matrix.mul_zero, hO_eq_trace V₀, pairS, Matrix.trace_zero, add_zero]

theorem smul_eq_self {α : Type} {F : α → ℂ} (hF : F ≠ 0) {c : ℂ} (h : F = c • F) : c = 1 := by
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hF
  have := congrFun h w
  rw [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hw (this.symm.trans (one_mul _).symm)

set_option maxHeartbeats 1600000 in

theorem dual_col {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V₀ W : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ)
    {LV : Lat V} {LV₀ : Lat V₀} {LW : Lat W} (hV : IsSelfDualC V LV) (hW : IsSelfDualC W LW) {v : Pl D}
    (hm : MonoAt dV LV LV₀ v) (x : Mx D W.rank ρ) {β : Type} (𝔉 : (WO V W → ℂ) → β → ℂ) (G : WO V W → ℂ) (hne : 𝔉 G ≠ 0)
    (hdual : ∀ a : Mx D W.rank ρ, MxAt (· = v) a → UInv W x a →
      𝔉 (heisO ψ V W (dV.extY W a) G) = ψ (symplO V W (dV.extX W x) (dV.extY W a)) • 𝔉 G)
    (g : GA D W) {a b : AE D} (hab : a + b = 1) (hfix : ∀ u ∈ latO V W (LV : Set _) (LW : Set _) (· = v),
      heisO ψ V W (a • (mt W g ⬝ u)) G = G ∧ heisO ψ V W (b • (mt W g ⬝ u)) G = G)
    (p p' : Mx D W.rank W.rank) (hp : adj p' ⬝ gA W = gA W ⬝ p) (hp' : ∀ y ∈ latV W LW (· = v), p' *ᵥ y ∈ latV W LW (· = v))
    (i : Fin ρ) (hi : ∀ j < i, ∀ k, (p ⬝ (mt W g⁻¹ ⬝ x)) k j = 0) (c : AE D) (hc : colMul dV.jX i c ∈ latV V LV (· = v)) :
    colMul (p ⬝ (mt W g⁻¹ ⬝ x)) i c ∈ latA W LW (· = v) := by
  set E : Mx D ρ ρ := Matrix.single i i 1 with hE
  set y : Mx D W.rank ρ := p ⬝ (mt W g⁻¹ ⬝ x) with hy
  have hadjE : adj E = E := by
    ext k l
    change cA D (E l k) = E k l
    simp only [hE, Matrix.single_apply, and_comm]
    split_ifs
    · exact map_one _
    · exact map_zero _
  have hg : adj (mt W g) ⬝ gA W = gA W ⬝ mt W g⁻¹ := by rw [mt_inv, gA_giA_cancel]
  have hU : SelfDualAt.cP (· = v) • dV.extX W (y ⬝ E) ∈ latO V W (LV : Set _) (LW : Set _) (· = v) := by
    refine (SelfDualAt.latO_ann_at D ψ hψ V W LV LW hV hW (· = v) _ fun k l => ?_).2 fun u hu => ?_
    · rw [Matrix.smul_apply, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (eps_idAt v)
    have hux := LatMem.latO_mxAt hu
    have hfixu : SelfDualAt.cP (· = v) • u = u := by
      ext k l
      rw [Matrix.smul_apply, Algebra.smul_def]
      exact eps_mul (hux k l)
    rw [← SelfDualAt.symplO_smul_swap, hfixu, symplO_eq, hO_extX]
    have hπ : p' ⬝ (u ⬝ (dV.jY ⬝ E ⬝ dV.pY)) ∈ latO V W (LV : Set _) (LW : Set _) (· = v) := by
      refine sandwich_latO hV hW p' hp' _ (fun z hz => ?_) hu
      rw [← Matrix.mulVec_mulVec, hE, single_mulVec', one_mul]
      exact ((hm z).1 hz).2.1 i
    set A : Mx D W.rank ρ := mt W g ⬝ (p' ⬝ (u ⬝ (dV.jY ⬝ E))) with hA
    have hpair : ∀ (c : AE D) (x' : Mx D W.rank ρ),
        pairS W x' (c • A) = cA D c * pairS W (p ⬝ (mt W g⁻¹ ⬝ x') ⬝ E) (u ⬝ dV.jY) := fun c x' => by
      rw [pairS, pairS, adj_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hA]
      congr 1
      simp only [adj_mul, hadjE, Matrix.mul_assoc, cancel₂ hg, cancel₂ hp]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    have key : ∀ c : AE D, heisO ψ V W (c • (mt W g ⬝ (p' ⬝ (u ⬝ (dV.jY ⬝ E ⬝ dV.pY))))) G = G →
        psiE ψ (cA D c * (incA D D.host.xi0 * pairS W (y ⬝ E) (u ⬝ dV.jY))) = 1 := fun c hcf => by
      have e1 : c • (mt W g ⬝ (p' ⬝ (u ⬝ (dV.jY ⬝ E ⬝ dV.pY)))) = dV.extY W (c • A) := by
        simp only [HypDec.extY_apply, hA, Matrix.smul_mul, Matrix.mul_assoc]
      have h1 := hdual (c • A) (mxAt_smul _ (mxAt_mul_left _ (mxAt_mul_left _ (mxAt_mul_right hux _)))) fun w => by
        rw [hpair, hpair]
        congr 2
        rw [← Matrix.mul_assoc (mt W g⁻¹), ← Matrix.mul_assoc p, ← hy]
        ext k l
        by_cases hl : l = i
        · subst hl
          rw [hE, Matrix.mul_single_apply_same, Matrix.mul_single_apply_same, Matrix.mul_apply,
            Finset.sum_eq_single l]
          · rw [(w.2 l l).2, mul_one]
          · intro j _ hj
            rcases lt_or_gt_of_ne hj with h | h
            · rw [hi j h k, zero_mul]
            · rw [(w.2 j l).1 h, mul_zero]
          · intro h; exact absurd (Finset.mem_univ l) h
        · rw [hE, Matrix.mul_single_apply_of_ne _ _ _ _ _ hl, Matrix.mul_single_apply_of_ne _ _ _ _ _ hl]
      rw [← e1, hcf] at h1
      have h2 := smul_eq_self hne h1
      rw [e1, symplO_eq, hO_extX, HypDec.extY_apply, Matrix.mul_assoc, dV.pY_jY, Matrix.mul_one, hpair] at h2
      rw [mul_left_comm]
      exact h2
    exact psi_parts ψ (a := cA D a) (b := cA D b) (by rw [← RingHom.map_add, hab, RingHom.map_one])
      (key a (hfix _ hπ).1) (key b (hfix _ hπ).2)
  have h := LatMem.latO_maps hV hU hc
  have e : (SelfDualAt.cP (· = v) • dV.extX W (y ⬝ E)) *ᵥ colMul dV.jX i c = colMul y i c := by
    have e0 : SelfDualAt.cP (· = v) • dV.extX W (y ⬝ E) = eps v • dV.extX W (y ⬝ E) := by
      ext k l
      rw [Matrix.smul_apply, Algebra.smul_def]
      rfl
    rw [e0, Matrix.smul_mulVec, HypDec.extX_apply, ← Matrix.mulVec_mulVec, hE, single_mulVec', one_mul, pX_colMul,
      ← colMul_mul, eps_mul (idAt_of_colMul dV hc)]
  rwa [e] at h

theorem shift_one {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ)
    {Λ : AddSubgroup (WO V W)} {v : Pl D} (x : Mx D W.rank ρ) {β : Type} (𝔉 : (WO V W → ℂ) → β → ℂ) (G : WO V W → ℂ)
    (hne : 𝔉 G ≠ 0) (hsh : ∀ N : Mx D ρ ρ, MxAt (· = v) N → (∀ i j, j ≤ i → N i j = 0) →
      𝔉 (heisO ψ V W (dV.extX W (x ⬝ N)) G) = psiE ψ (upSum N) • 𝔉 G)
    (g : GA D W) {a b : AE D} (hab : a + b = 1) (hfix : ∀ u ∈ Λ,
      heisO ψ V W (a • (mt W g ⬝ u)) G = G ∧ heisO ψ V W (b • (mt W g ⬝ u)) G = G)
    (i j : Fin ρ) (hij : j.1 = i.1 + 1) (s : AE D) (hs : s ∈ idAt D (· = v))
    (hu : dV.extX W (mt W g⁻¹ ⬝ x ⬝ (Matrix.single i j s : Mx D ρ ρ)) ∈ Λ) : psiE ψ s = 1 := by
  have key : ∀ c : AE D, heisO ψ V W (c • (mt W g ⬝ dV.extX W (mt W g⁻¹ ⬝ x ⬝ (Matrix.single i j s : Mx D ρ ρ)))) G = G →
      psiE ψ (c * s) = 1 := fun c hc => by
    have e1 : c • (mt W g ⬝ dV.extX W (mt W g⁻¹ ⬝ x ⬝ (Matrix.single i j s : Mx D ρ ρ))) =
        dV.extX W (x ⬝ (Matrix.single i j (c * s) : Mx D ρ ρ)) := by
      rw [← smul_eq_mul, ← Matrix.smul_single]
      simp only [HypDec.extX_apply, Matrix.mul_assoc, cancel₂ (mt_mul_inv W g), Matrix.one_mul, Matrix.mul_smul,
        Matrix.smul_mul]
    have h1 := hsh (Matrix.single i j (c * s)) (fun k l => by
        rw [Matrix.single_apply]
        split_ifs
        · exact Ideal.mul_mem_left _ _ hs
        · exact zero_mem _) fun k l hkl => by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      rw [Fin.le_def] at hkl
      omega
    rw [← e1, hc] at h1
    have h2 := smul_eq_self hne h1
    have e2 : upSum (Matrix.single i j (c * s) : Mx D ρ ρ) = c * s := by
      unfold upSum
      rw [Finset.sum_eq_single i, Finset.sum_eq_single j, if_pos hij, Matrix.single_apply_same]
      · intro l _ hl; rw [Matrix.single_apply_of_col_ne _ _ hl.symm, ite_self]
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro k _ hk
        exact Finset.sum_eq_zero fun l _ => by rw [Matrix.single_apply_of_row_ne hk.symm, ite_self]
      · intro h; exact absurd (Finset.mem_univ _) h
    rwa [e2] at h2
  exact psi_parts ψ hab (key a (hfix _ hu).1) (key b (hfix _ hu).2)

theorem eps_mem_of_products {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} (hL : IsSelfDualC S L)
    {v : Pl D} (hm : MonoAt d L L₀ v) (i : Fin ρ) (H : AddSubgroup (AE D))
    (hH : ∀ α β : AE D, colMul d.jX i α ∈ latV S L (· = v) →
      (∀ a, colMul d.jX i a ∈ latV S L (· = v) → β * a ∈ intAt D (· = v)) → α * β ∈ H) : eps v ∈ H := by
  obtain ⟨m, s, s', hs, hs', hd⟩ := FrameLat.exists_expansion hL
  have h1 : colMul d.jX i (eps v) = ∑ l, FrameLat.pairing S (s' l) (colMul d.jX i 1) •
      fun k => eps v * incA D (s l k) := by
    funext k
    rw [Finset.sum_apply, ← mul_one (eps v), colMul_mul, Pi.smul_apply, hd (colMul d.jX i 1) k, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    ring
  rw [← pX_colMul d i (eps v), h1, Matrix.mulVec_sum, Finset.sum_apply]
  refine sum_mem fun l _ => ?_
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  refine hH _ _ (((hm _).1 (FrameLat.int_mul_mem ⟨eps_idAt v, eps_int v⟩ (hs l))).1 i) fun a ha =>
    ⟨Ideal.mul_mem_left _ _ (idAt_of_colMul d ha), ?_⟩
  have h2 : FrameLat.pairing S (s' l) (colMul d.jX i 1) * a = FrameLat.pairing S (s' l) (colMul d.jX i a) := by
    simp only [FrameLat.pairing, colMul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h2]
  exact FrameLat.pairing_int hL (hs' l) ha

theorem int_of_stable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} (hL : IsSelfDualC S L)
    {v : Pl D} (hm : MonoAt d L L₀ v) (i : Fin ρ) {c : AE D} (hc1 : c - 1 ∈ idAt D (· = v))
    (hc : ∀ a, colMul d.jX i a ∈ latV S L (· = v) → colMul d.jX i (c * a) ∈ latV S L (· = v)) :
    finPart D c ∈ intAE D := by
  have h := eps_mem_of_products d hL hm i ((intSub v).comap (AddMonoidHom.mulLeft c)) fun α β hα hβ => by
    change c * (α * β) ∈ intAt D (· = v)
    rw [show c * (α * β) = β * (c * α) by ring]
    exact hβ _ (hc α hα)
  have h' : finPart D (c * eps v) ∈ intAE D := h.2
  have e : c = c * eps v - eps v + 1 := by
    have := eps_mul hc1
    linear_combination -this
  rw [e, RingHom.map_add, RingHom.map_sub]
  exact add_mem (sub_mem h' (eps_int v)) (int_of_idem (one_mul 1))

theorem stable_of_prim {ψ : AddChar (AF D.host.F) ℂ} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : IsSelfDualC S L) {v : Pl D} (hm : MonoAt d L L₀ v) (hp : PrimAt ψ d L v) (i j : Fin ρ) (hij : j.1 = i.1 + 1)
    {c : AE D} (hc : ∀ s ∈ idAt D (· = v), (∀ a, colMul d.jX j a ∈ latV S L (· = v) →
      colMul d.jX i (s * a) ∈ latV S L (· = v)) → psiE ψ (c * s) = 1) (a : AE D)
    (ha : colMul d.jX i a ∈ latV S L (· = v)) : colMul d.jX i (c * a) ∈ latV S L (· = v) := by
  have ha' := idAt_of_colMul d ha
  let φ : AE D →+ (Fin S.rank → AE D) :=
    AddMonoidHom.mk' (fun h => colMul d.jX i (c * a * h)) fun x y => funext fun k => by
      simp only [colMul, Pi.add_apply]; ring
  have h := eps_mem_of_products d hL hm j ((latV S L (· = v)).comap φ) fun α β hα hβ => by
    change colMul d.jX i (c * a * (α * β)) ∈ latV S L (· = v)
    rw [show c * a * (α * β) = c * (a * β) * α by ring]
    have hs : a * β ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ ha'
    refine (hp i j hij _ (Ideal.mul_mem_left _ _ hs)).2 (fun o ho => ?_) α hα
    rw [mul_assoc]
    refine hc _ (Ideal.mul_mem_right _ _ hs) fun a' h' => ?_
    rw [show a * β * o * a' = o * (β * a' * a) by ring, colMul_mul, colMul_mul]
    exact smul_latV ho.2 (smul_latV (hβ a' h').2 ha)
  change colMul d.jX i (c * a * eps v) ∈ latV S L (· = v) at h
  rwa [mul_assoc, mul_comm a, eps_mul ha'] at h

theorem diag_mulVec {ρ : ℕ} {t : Mx D ρ ρ} (ht : ∀ i j, i ≠ j → t i j = 0) (y : Fin ρ → AE D) (i : Fin ρ) :
    (t *ᵥ y) i = t i i * y i := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · intro j _ hj; rw [ht i j hj.symm, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mul_diag {m ρ : ℕ} (x : Mx D m ρ) {t : Mx D ρ ρ} (ht : ∀ i j, i ≠ j → t i j = 0) (k : Fin m) (i : Fin ρ) :
    (x ⬝ t) k i = x k i * t i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj; rw [ht j i hj, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem inv_diag_mul {ρ : ℕ} {t : GL (Fin ρ) (AE D)} (ht : ∀ i j, i ≠ j → t.1 i j = 0) (i : Fin ρ) :
    (t⁻¹).1 i i * t.1 i i = 1 := by
  rw [← mul_diag _ ht, Units.inv_mul, Matrix.one_apply_eq]

theorem inv_diag {ρ : ℕ} {t : GL (Fin ρ) (AE D)} (ht : ∀ i j, i ≠ j → t.1 i j = 0) (i j : Fin ρ) (h : i ≠ j) :
    (t⁻¹).1 i j = 0 := by
  have h1 : (t⁻¹).1 i j * t.1 j j = 0 := by rw [← mul_diag _ ht, Units.inv_mul, Matrix.one_apply_ne h]
  have h2 := inv_diag_mul ht j
  linear_combination (t⁻¹).1 j j * h1 - (t⁻¹).1 i j * h2

theorem levi_entry {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {P : Pl D → Prop} {t : GL (Fin ρ) (AE D)}
    (ht : d.levi t ∈ grpAt S P) (i : Fin ρ) : t.1 i i - 1 ∈ idAt D P := by
  have h : MxAt P (mt S (d.levi t) - 1) := (IwaPlace.mem_congGrp_iff S _ _).1 ht
  have h1 := mxAt_mul_left d.pX (mxAt_mul_right h d.jX) i i
  rwa [Matrix.sub_mul, Matrix.mul_sub, d.levi_jX, Matrix.one_mul, cancel₂ d.pX_jX, Matrix.one_mul, d.pX_jX,
    Matrix.sub_apply, Matrix.one_apply_eq] at h1

theorem levi_mulVec_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {t : GL (Fin ρ) (AE D)} (ht : ∀ i j, i ≠ j → t.1 i j = 0)
    (h1 : ∀ i, finPart D (t.1 i i) ∈ intAE D) (h2 : ∀ i, finPart D ((t⁻¹).1 i i) ∈ intAE D) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L (· = v)) : mt S (d.levi t) *ᵥ y ∈ latV S L (· = v) := by
  obtain ⟨hX, hY, h0⟩ := (hm y).1 hy
  refine (hm _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, d.pX_levi, ← Matrix.mulVec_mulVec, diag_mulVec ht, colMul_mul]
    exact smul_latV (h1 i) (hX i)
  · rw [Matrix.mulVec_mulVec, d.pY_levi, ← Matrix.mulVec_mulVec, diag_mulVec (t := adj (t⁻¹).1) (fun k l h => by
      change cA D ((t⁻¹).1 l k) = 0
      rw [inv_diag ht l k h.symm, RingHom.map_zero]), colMul_mul]
    exact smul_latV ((FrameLat.cA_int_iff _).2 (h2 i)) (hY i)
  · rw [Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_levi]
    exact h0

theorem inK_levi {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {t : GL (Fin ρ) (AE D)} (ht : ∀ i j, i ≠ j → t.1 i j = 0) (hg : d.levi t ∈ grpAt S (· = v))
    (h1 : ∀ i, finPart D (t.1 i i) ∈ intAE D) (h2 : ∀ i, finPart D ((t⁻¹).1 i i) ∈ intAE D) :
    InK S L (· = v) (d.levi t) := by
  refine ⟨hg, fun y _ => ⟨levi_mulVec_mem d hm ht h1 h2, fun hy => ?_⟩⟩
  have h := levi_mulVec_mem d hm (inv_diag ht) h2 (by rwa [inv_inv]) hy
  rwa [Matrix.mulVec_mulVec, map_inv, mt_inv_mul, Matrix.one_mulVec] at h

theorem inK_mul {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a b : GA D S} (ha : InK S L P a) (hb : InK S L P b) :
    InK S L P (a * b) :=
  ⟨mul_mem ha.1 hb.1, fun y hy => by
    rw [mt_mul, ← Matrix.mulVec_mulVec, ← ha.2 _ (IwaPlace.mulVec_mem_idAt _ hy), hb.2 y hy]⟩

theorem mul_xLast_castSucc {T T₀ : HSp D} {σ m : ℕ} (d : HypDec T T₀ σ) (z : Fin T₀.rank → D.host.E) (M : Mx D m T.rank)
    (k : Fin m) (i : Fin σ) : (M ⬝ xLast d z) k i.castSucc = (M ⬝ d.jX) k i := by
  simp only [Matrix.mul_apply, xLast, Matrix.of_apply, Fin.snoc_castSucc]

theorem mul_xLast_last {T T₀ : HSp D} {σ m : ℕ} (d : HypDec T T₀ σ) (z : Fin T₀.rank → D.host.E) (M : Mx D m T.rank)
    (k : Fin m) : (M ⬝ xLast d z) k (Fin.last σ) = ((M ⬝ d.j0) *ᵥ ratV z) k := by
  rw [← Matrix.mulVec_mulVec]
  simp only [Matrix.mul_apply, xLast, Matrix.of_apply, Fin.snoc_last]
  rfl

theorem xLast_castSucc {T T₀ : HSp D} {σ : ℕ} (d : HypDec T T₀ σ) (z : Fin T₀.rank → D.host.E) (k : Fin T.rank)
    (i : Fin σ) : xLast d z k i.castSucc = d.jX k i := by
  simp only [xLast, Matrix.of_apply, Fin.snoc_castSucc]

theorem xLast_last {T T₀ : HSp D} {σ : ℕ} (d : HypDec T T₀ σ) (z : Fin T₀.rank → D.host.E) (k : Fin T.rank) :
    xLast d z k (Fin.last σ) = (d.j0 *ᵥ ratV z) k := by
  simp only [xLast, Matrix.of_apply, Fin.snoc_last]

set_option maxHeartbeats 1600000 in

theorem support_parts {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B)
    {LV : Lat J.W} {LV₀ : Lat J.W₀} {LW : Lat B.V} {LW₀ : Lat B.V₀} {v : Pl D} (hA : AdaptFB ψ J B LV LV₀ LW LW₀ v)
    {𝔉 : (WO J.W B.V → ℂ) → (WO J.W₀ B.V₀ → ℂ)} (h𝔉 : IsFlatFB s (· = v) 𝔉)
    (hsh : ShiftLaw ψ J.d (xLast B.d (vecB B.o B.ζ)) (· = v) 𝔉) {f : WO J.W B.V → ℂ} (hf : Vac ψ J.W B.V LV LW (· = v) f)
    {t : GL (Fin σ) (AE D)} (ht : ∀ i j, i ≠ j → t.1 i j = 0) (htG : B.d.levi t ∈ grpAt B.V (· = v)) (γ : GA D B.V₀)
    (hne : 𝔉 (s.om (1, B.d.levi t * B.d.emb0 γ) f) ≠ 0) :
    InK B.V LW (· = v) (B.d.levi t) ∧ ∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ LW₀ (· = v) →
      mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ LW₀ (· = v) := by
  set g := B.d.levi t * B.d.emb0 γ with hg
  set z := vecB B.o B.ζ with hz
  have hθ : IsThetaFunO ψ J.W B.V (s.om (1, g) f) := s.weil.om_pres _ _ hf.1
  obtain ⟨a, b, hab, hfix⟩ := exists_parts_om s.weil hA.sdV hA.sdW hA.tame hf g
  have hgX : mt B.V g⁻¹ ⬝ B.d.jX = B.d.jX ⬝ (t⁻¹).1 := by
    rw [hg, _root_.mul_inv_rev, ← map_inv, ← map_inv, mt_mul, Matrix.mul_assoc, B.d.levi_jX, cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclX _)]
  have hg0 : mt B.V g⁻¹ ⬝ B.d.j0 = B.d.j0 ⬝ mt B.V₀ γ⁻¹ := by
    rw [hg, _root_.mul_inv_rev, ← map_inv, ← map_inv, mt_mul, Matrix.mul_assoc, B.d.wittDecomp_levi_inclAnisotropic, B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  have hD := dual_col s.weil.std J.d hA.sdV hA.sdW hA.monoV (xLast B.d z) 𝔉 _ hne (h𝔉.Heisenberg₂.dual _ hθ) g hab hfix
  have hti := inv_diag ht
  refine ⟨inK_levi B.d hA.monoW ht htG (fun i => ?_) fun i => ?_, fun c hc => ?_⟩
  · refine int_of_stable J.d hA.sdV hA.monoV i.castSucc (levi_entry B.d htG i) ?_
    refine stable_of_prim J.d hA.sdV hA.monoV hA.prim i.castSucc i.succ (by simp) fun s' hs' hr => ?_
    refine shift_one J.d (xLast B.d z) 𝔉 _ hne (hsh _ hθ) g hab hfix i.castSucc i.succ (by simp) _
      (Ideal.mul_mem_left _ _ hs') ?_
    refine (LatMem.mem_latO_iff D _ _ LV LW hA.sdV hA.sdW (· = v) _).2
      ⟨mxAt_mul_right (mxAt_mul_left _ fun k l => ?_) _, fun y hy => ?_⟩
    · rw [Matrix.single_apply]
      split_ifs
      · exact Ideal.mul_mem_left _ _ hs'
      · exact zero_mem _
    · change (mt B.V g⁻¹ ⬝ xLast B.d z ⬝ (Matrix.single i.castSucc i.succ (t.1 i i * s') : Mx D (σ + 1) (σ + 1)) ⬝
        J.d.pX) *ᵥ y ∈ _
      rw [← Matrix.mulVec_mulVec, single_mulVec']
      have h1 := hr _ (((hA.monoV y).1 hy).1 i.succ)
      have h2 := (hA.cols _ _ (idAt_of_colMul J.d h1)).1 h1
      convert h2 using 1
      funext k
      rw [colMul, colMul, mul_xLast_castSucc, hgX, mul_diag _ hti, xLast_castSucc]
      linear_combination (s' * (J.d.pX *ᵥ y) i.succ * B.d.jX k i) * inv_diag_mul ht i
  · refine int_of_stable J.d hA.sdV hA.monoV i.castSucc (levi_entry B.d (by rw [map_inv]; exact inv_mem htG) i)
      fun c hc => ?_
    have hadjE : adj (Matrix.single i i 1 : Mx D σ σ) = Matrix.single i i 1 := by
      ext k l
      change cA D ((Matrix.single i i 1 : Mx D σ σ) l k) = _
      simp only [Matrix.single_apply, and_comm]
      split_ifs
      · exact map_one _
      · exact map_zero _
    have hcol : ∀ k (j : Fin σ), (B.d.jX ⬝ (Matrix.single i i 1 : Mx D σ σ) ⬝ B.d.pX ⬝ (mt B.V g⁻¹ ⬝ xLast B.d z)) k
        j.castSucc = B.d.jX k i * (t⁻¹).1 i j := fun k j => by
      rw [← Matrix.mul_assoc, mul_xLast_castSucc, Matrix.mul_assoc, hgX, Matrix.mul_assoc, cancel₂ B.d.pX_jX,
        Matrix.one_mul, Matrix.mul_apply, Finset.sum_eq_single i, Matrix.mul_single_apply_same, mul_one]
      · intro l _ hl; rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hl, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have h1 := hD (B.d.jX ⬝ (Matrix.single i i 1 : Mx D σ σ) ⬝ B.d.pX) (B.d.jY ⬝ (Matrix.single i i 1 : Mx D σ σ) ⬝ B.d.pY)
      (by simp only [adj_mul, hadjE, B.d.pX_eq, B.d.pY_eq, adj_adj, adj_gA, Matrix.mul_assoc])
      (fun y hy => by
        rw [← Matrix.mulVec_mulVec, single_mulVec', one_mul]
        exact ((hA.monoW y).1 hy).2.1 i) i.castSucc
      (fun j hj k => by
        obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt hj)
        rw [hcol, hti i j (Fin.castSucc_lt_castSucc_iff.1 hj).ne', mul_zero]) c hc
    refine (hA.cols _ _ (Ideal.mul_mem_left _ _ (idAt_of_colMul J.d hc))).2 ?_
    convert h1 using 1
    funext k
    rw [colMul, colMul, hcol, xLast_castSucc]
    ring
  · have hε : (eps v * c) • ratV z = c • ratV z := by
      rw [mul_smul]
      funext k
      exact eps_mul (latA_supp hc k)
    have h0 : colMul (xLast B.d z) (Fin.last σ) (eps v * c) ∈ latA B.V LW (· = v) := by
      have h := VacFlat.wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace B.d hA.monoW hc
      rw [← hε, Matrix.mulVec_smul] at h
      convert h using 1
      funext k
      rw [colMul, xLast_last]
      rfl
    have h1 := hD (B.d.j0 ⬝ B.d.p0) (B.d.j0 ⬝ B.d.p0)
      (by simp only [adj_mul, B.d.p0_eq, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc])
      (fun y hy => by
        rw [← Matrix.mulVec_mulVec]
        exact VacFlat.wittCoreInclusion_mem_latticeCompletionAtPlace B.d hA.monoW ((hA.monoW y).1 hy).2.2) (Fin.last σ)
      (fun j hj k => by
        obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hj.ne
        rw [← Matrix.mul_assoc, mul_xLast_castSucc, Matrix.mul_assoc, hgX, Matrix.mul_assoc, cancel₂ B.d.p0_jX,
          Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_apply]) _
      ((hA.cols _ _ (Ideal.mul_mem_right _ _ (eps_idAt v))).2 h0)
    have h2 := mulVec_latA B.d.p0 (fun y hy => ((hA.monoW y).1 hy).2.2) h1
    rw [mulVec_colMul] at h2
    rw [← hε, Matrix.mulVec_smul]
    convert h2 using 1
    funext k
    rw [colMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_xLast_last, Matrix.mul_assoc, hg0, cancel₂ B.d.p0_j0,
      Matrix.one_mul, cancel₂ B.d.p0_j0, Matrix.one_mul]
    rfl

end GlobalTheory.FinPl.SuppShift

namespace GlobalTheory.FinPl

open SuppShift in

theorem supportShift : ∀ D : D7, GlobalTheory.FinPl.SupportShift D := by
  intro D ψ σ J B s LV LV₀ LW LW₀ v hA hU 𝔉 h𝔉 hsh f hf
  refine ⟨?_, fun h hh hne => ?_⟩
  · obtain ⟨hθ, h2, hh⟩ := hf
    have hmem : ∀ w ∈ latO J.W₀ B.V₀ (LV₀ : Set _) (LW₀ : Set _) (· = v),
        J.d.ext0 B.V (B.d.inc0 J.W₀ w) ∈ latO J.W B.V (LV : Set _) (LW : Set _) (· = v) := fun w hw =>
      VacFlat.wittExt_wittInc_mem_completed_hom_lattice J.d B.d hA.sdV hA.sdW hA.sdV₀ hA.monoV hA.monoW hw
    refine ⟨h𝔉.Heisenberg₂.theta f hθ, fun w hw => ?_, fun e he w hw hwe => ?_⟩
    · have hx : MxAt (· = v) (2 • w) := fun i j => by
        rw [Matrix.smul_apply]
        exact nsmul_mem (LatMem.latO_mxAt hw i j) 2
      rw [← h𝔉.Heisenberg₂.core f hθ (2 • w) hx, map_nsmul, map_nsmul, h2 _ (hmem w hw)]
    · rw [← h𝔉.Heisenberg₂.core f hθ w (LatMem.latO_mxAt hw), hh e he _ (hmem w hw) (VacFlat.wittExt_wittInc_isHalf J.d B.d hwe)]
  · obtain ⟨n, hnN, hnG, t, ht, htG, γ, hγ, κ, hκ, rfl⟩ :=
      GlobalTheory.T.iwasawa_decomposition_selfDual_wittSplit_at_place D B.V B.V₀ σ B.d LW LW₀ v hA.tame hA.sdW hA.sdW₀ hA.monoW h hh
    have hmul : s.om (1, n * B.d.levi t * B.d.emb0 γ * κ) f =
        s.om (1, n) (s.om (1, B.d.levi t * B.d.emb0 γ) (s.om (1, κ) f)) := by
      have : ((1 : GA D J.W), n * B.d.levi t * B.d.emb0 γ * κ) = (1, n) * (1, B.d.levi t * B.d.emb0 γ) * (1, κ) := by
        simp only [Prod.mk_mul_mk, mul_one, mul_assoc]
      rw [this, map_mul, map_mul]; rfl
    have hκf : s.om (1, κ) f = f := by
      refine GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ J.W B.V s.χV s.χW s.om s.weil LV LW hA.sdV hA.sdW (· = v) ?_ f hf 1 κ ?_ hκ
      · rintro w rfl; exact ⟨hA.tame, hU.1, hU.2⟩
      · exact ⟨one_mem _, fun y _ => by rw [mt_one, Matrix.one_mulVec]⟩
    have h1 := h𝔉.equiv _ (s.weil.om_pres (1, B.d.levi t * B.d.emb0 γ) _ hf.1) n hnN hnG 1 (one_mem _)
    have he : B.o.emb (1, 1) = 1 := map_one B.o.emb
    have he₀ : s.om₀ ((1 : GA D J.W₀), (1 : GA D B.V₀)) = 1 := map_one s.om₀
    rw [map_one, mul_one, he, he₀, Module.End.one_apply] at h1
    rw [hmul, hκf, h1] at hne
    obtain ⟨hK, hz⟩ := support_parts s hA h𝔉 hsh hf ht htG γ (right_ne_zero_of_smul hne)
    refine ⟨n, hnN, hnG, γ, hγ, B.d.levi t * κ, inK_mul hK hκ, ?_, hz⟩
    rw [mul_assoc n (B.d.levi t), ← B.d.wittHyperbolic_anisotropic_commute_levi γ t]
    simp only [mul_assoc]

end GlobalTheory.FinPl

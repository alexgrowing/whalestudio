import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrConjApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleModelsIsoMemIntegralOfOhEStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedColumnLatticeIntegralFrameCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMulVecCompletedIdealMemCompletedIdealLatticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeMapIdealMulTransportStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.FrameTransport.Cong

variable {D : D7}

theorem adSwap_mem_intAf (x : StandardLatticesGL3.AE D) (hx : x ∈ StandardLatticesGL3.OhE D) :
    adSwap D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := GlobalTheory.T.finiteAdeleModelsIso_mem_integral_of_OhE x hx

theorem adSwap_inc (e : D.host.E) : adSwap D (StandardLatticesGL3.inc D e) = inclEAf D e := by
  have h1 : GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D e) = algebraMap D.host.E _ e := by
    show GlobalTheory.LFun.toFinAd ℚ D.host.E ((1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ⊗ₜ e) = _
    rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]
  have h2 : GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D e) = (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ e := by
    show (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D e)) = _
    rw [h1, RingEquiv.symm_apply_eq]
    show _ = GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ e)
    rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]
  show Lev.swapAE D (GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D e)) = _
  rw [h2]
  rfl

theorem intG_entries {n : ℕ} (k : StandardLatticesGL3.GA D n) (hk : k ∈ GlobalTheory.NormSum.intG D n) : StandardLatticesGL3.IntG D k.1 := by
  have hmul : ∀ a b : GL (Fin n) (StandardLatticesGL3.AE D), (∀ i j, a.val i j ∈ StandardLatticesGL3.OhE D) → (∀ i j, b.val i j ∈ StandardLatticesGL3.OhE D) →
      ∀ i j, (a * b).val i j ∈ StandardLatticesGL3.OhE D := fun a b ha hb i j => by
    rw [Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (ha i l) (hb l j)
  let H : Subgroup (StandardLatticesGL3.GA D n) :=
    { carrier := {k | StandardLatticesGL3.IntG D k.1}
      mul_mem' := fun {a b} ha hb i j => by
        refine ⟨hmul a.1 b.1 (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j, ?_⟩
        have e : ((a * b : StandardLatticesGL3.GA D n) : GL (Fin n) (StandardLatticesGL3.AE D))⁻¹ = b.1⁻¹ * a.1⁻¹ := by
          rw [Subgroup.coe_mul, _root_.mul_inv_rev]
        rw [e]
        exact hmul _ _ (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j
      one_mem' := fun i j => by
        have h1 : ∀ i j : Fin n, (1 : Matrix (Fin n) (Fin n) (StandardLatticesGL3.AE D)) i j ∈ StandardLatticesGL3.OhE D := fun i j => by
          rw [Matrix.one_apply]
          split_ifs
          exacts [Subring.one_mem _, Subring.zero_mem _]
        exact ⟨h1 i j, by rw [Subgroup.coe_one, inv_one]; exact h1 i j⟩
      inv_mem' := fun {a} ha i j => by
        refine ⟨(ha i j).2, ?_⟩
        rw [Subgroup.coe_inv, inv_inv]
        exact (ha i j).1 }
  exact (Subgroup.closure_le H).2 (fun k hk => hk) hk

theorem hatL_colLat_int {n : ℕ} (fr : GL (Fin n) D.host.E) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) (i : Fin n) :
    ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  GlobalTheory.T.completedColumnLattice_integral_frameCoords fr y hy i

theorem col_mem_hatL {n : ℕ} (fr : GL (Fin n) D.host.E) (j : Fin n) :
    (fun i => inclEAf D (fr.val i j)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) :=
  Submodule.subset_span ⟨fun a => fr.val a j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩

theorem eaf_mul_comm (a b : Lev.EAf D) : a * b = b * a := mul_comm a b

set_option maxHeartbeats 1000000 in
theorem hatL_colLat_of_int {n : ℕ} (fr : GL (Fin n) D.host.E) (z : Fin n → Lev.EAf D)
    (hz : ∀ i, z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    (Formalism.UG.bc (inclEAf D) fr).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := by
  have e : (Formalism.UG.bc (inclEAf D) fr).val *ᵥ z =
      ∑ j, (⟨z j, hz j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) • (fun i => inclEAf D (fr.val i j)) := by
    funext i
    rw [Finset.sum_apply]
    show ∑ j, (Formalism.UG.bc (inclEAf D) fr).val i j * z j =
      ∑ j, ((⟨z j, hz j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) • (fun i => inclEAf D (fr.val i j))) i
    exact Finset.sum_congr rfl fun j _ => eaf_mul_comm _ _
  exact (congrArg (fun v => v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) e).mpr
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (col_mem_hatL fr j))

theorem mul_mem_spanIncl (𝔪 : Ideal (𝓞 D.host.E)) (a z : Lev.EAf D)
    (ha : a ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E))))
    (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    a * z ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E))) := by
  have h3 := Submodule.smul_mem _ (⟨z, hz⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ha
  have e : (⟨z, hz⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) • a = a * z := mul_comm z a
  exact e ▸ h3

theorem adSwap_hatId (𝔪 : Ideal (𝓞 D.host.E)) (c : StandardLatticesGL3.AE D) (hc : c ∈ SqNum.hatId D 𝔪) :
    adSwap D c ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E))) := by
  have hle : SqNum.hatId D 𝔪 ≤ (Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))).toAddSubgroup.comap
        (adSwap D).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 fun y hy => ?_
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    have e : adSwap D (StandardLatticesGL3.inc D (b : D.host.E) * s) = inclEAf D (b : D.host.E) * adSwap D s :=
      (map_mul (adSwap D) _ _).trans (congrArg (· * adSwap D s) (adSwap_inc _))
    exact (congrArg (fun v => v ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) e).mpr
      (mul_mem_spanIncl 𝔪 _ _ (Submodule.subset_span ⟨b, hb, rfl⟩) (adSwap_mem_intAf s hs))
  exact hle hc

theorem hatL_smul_colLat {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin n → Lev.EAf D)
    (hw : ∀ i, w i ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) :
    (Formalism.UG.bc (inclEAf D) fr).val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) :=
  GlobalTheory.T.frame_mulVec_completedIdeal_mem_completedIdealLattice fr 𝔪 w hw

theorem hatL_transport {n : ℕ} (uf : GL (Fin n) (Lev.EAf D)) (L Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (h : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (𝔪 : Ideal (𝓞 D.host.E)) (y : Fin n → Lev.EAf D) (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • L)) :
    uf.val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) :=
  GlobalTheory.T.completedLatticeMap_idealMul_transport uf L Λ h 𝔪 y hy

theorem frConj_val {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D)) (y : Fin n → Lev.EAf D) :
    (frConj fr k).val *ᵥ y = (Formalism.UG.bc (inclEAf D) fr).val *ᵥ ((Formalism.UG.bc (adSwap D) k).val *ᵥ
      ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y)) := by
  rw [frConj_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem bc_adSwap_apply {n : ℕ} (k : GL (Fin n) (StandardLatticesGL3.AE D)) (i j : Fin n) :
    (Formalism.UG.bc (adSwap D) k).val i j = adSwap D (k.val i j) := rfl

theorem GL_mulVec_inv {A : Type} [CommRing A] {n : ℕ} (P : GL (Fin n) A) (y : Fin n → A) :
    P.val *ᵥ (P⁻¹.val *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem GL_inv_mulVec {A : Type} [CommRing A] {n : ℕ} (P : GL (Fin n) A) (y : Fin n → A) :
    P⁻¹.val *ᵥ (P.val *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem frConj_sub {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D)) (y : Fin n → Lev.EAf D) :
    (frConj fr k).val *ᵥ y - y = (Formalism.UG.bc (inclEAf D) fr).val *ᵥ
      (((Formalism.UG.bc (adSwap D) k).val - 1) *ᵥ ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y)) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, GL_mulVec_inv (Formalism.UG.bc (inclEAf D) fr) y,
    frConj_val fr k y]

theorem bc_adSwap_sub_one_apply {n : ℕ} (k : GL (Fin n) (StandardLatticesGL3.AE D)) (i j : Fin n) :
    ((Formalism.UG.bc (adSwap D) k).val - 1) i j = adSwap D ((k.val - 1) i j) := by
  rw [Matrix.sub_apply, Matrix.sub_apply, map_sub]
  congr 1
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  exacts [(map_one (adSwap D)).symm, (map_zero (adSwap D)).symm]

theorem frConj_stab {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D))
    (hk : ∀ i j, k.val i j ∈ StandardLatticesGL3.OhE D) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) :
    (frConj fr k).val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := by
  rw [frConj_val]
  refine hatL_colLat_of_int fr _ fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (by rw [bc_adSwap_apply]; exact adSwap_mem_intAf _ (hk i j))
    (hatL_colLat_int fr y hy j)

theorem frConj_stab_iff {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D))
    (hk : StandardLatticesGL3.IntG D k) (y : Fin n → Lev.EAf D) :
    y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
      (frConj fr k).val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := by
  refine ⟨frConj_stab fr k (fun i j => (hk i j).1) y, fun h => ?_⟩
  have h2 := frConj_stab fr k⁻¹ (fun i j => (hk i j).2) _ h
  have e : (frConj fr k⁻¹).val *ᵥ ((frConj fr k).val *ᵥ y) = y := by
    rw [map_inv]; exact GL_inv_mulVec _ y
  exact e ▸ h2

theorem frConj_cong {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (k : GL (Fin n) (StandardLatticesGL3.AE D))
    (hk : ∀ i j, (k.val - 1) i j ∈ SqNum.hatId D 𝔪) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) :
    (frConj fr k).val *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  rw [frConj_sub fr k y]
  refine hatL_smul_colLat fr 𝔪 _ fun i => ?_
  show (∑ j, ((Formalism.UG.bc (adSwap D) k).val - 1) i j * ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y) j) ∈ _
  refine Submodule.sum_mem _ fun j _ => ?_
  have h4 := mul_mem_spanIncl 𝔪 _ _ (adSwap_hatId 𝔪 _ (hk i j)) (hatL_colLat_int fr y hy j)
  rw [bc_adSwap_sub_one_apply k i j]
  exact h4

set_option maxHeartbeats 1000000 in

theorem conj_mem_congLev : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (uf : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (colLat fr) ↔ uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (k : StandardLatticesGL3.GA D V.rank), k ∈ GlobalTheory.NormSum.intG D V.rank → GlobalTheory.FunObj.SqNum.CongOne D 𝔪 k → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  intro D V fr uf Λ hL 𝔪 k hk hc hU
  have hM : ∀ x, x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔
      uf⁻¹.val *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := fun x =>
    ((hL (uf⁻¹.val *ᵥ x)).trans (by rw [GL_mulVec_inv uf x])).symm
  have hg : ∀ x, (uf * frConj fr k.1 * uf⁻¹).val *ᵥ x = uf.val *ᵥ ((frConj fr k.1).val *ᵥ (uf⁻¹.val *ᵥ x)) := by
    intro x
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hg' : ∀ x, uf⁻¹.val *ᵥ ((uf * frConj fr k.1 * uf⁻¹).val *ᵥ x) = (frConj fr k.1).val *ᵥ (uf⁻¹.val *ᵥ x) := by
    intro x
    rw [hg x, GL_inv_mulVec]
  refine ⟨hU, fun x => ?_, fun x hx => ?_⟩
  · refine (hM x).trans ((frConj_stab_iff fr k.1 (intG_entries k hk) _).trans ?_)
    exact ((hM ((uf * frConj fr k.1 * uf⁻¹).val *ᵥ x)).trans
      (Iff.of_eq (congrArg (fun v => v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) (hg' x)))).symm
  · have hy := (hM x).1 hx
    have h5 := hatL_transport uf (colLat fr) Λ (fun v hv => (hL v).1 hv) 𝔪 _ (frConj_cong fr 𝔪 k.1 hc _ hy)
    have e : uf.val *ᵥ ((frConj fr k.1).val *ᵥ (uf⁻¹.val *ᵥ x) - uf⁻¹.val *ᵥ x) =
        (uf * frConj fr k.1 * uf⁻¹).val *ᵥ x - x := by
      exact (Matrix.mulVec_sub uf.val _ _).trans (congrArg₂ HSub.hSub (hg x).symm (GL_mulVec_inv uf x))
    exact Eq.mp (congrArg (fun v => v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ)) e) h5

end GlobalTheory.FrameTransport.Cong

import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.StdHalfLat

variable {D : D7}

theorem idemSum_mul_eq_zero {P P' : Finset (Pl D.host.E)} {e e' : AE D} (he : IsIdemSum e P) (he' : IsIdemSum e' P')
    (hPP : ∀ w ∈ P, ∀ w' ∈ P', w ≠ w' ∧ ¬ Formalism.IndefR.Lev.IsConjPl (D := D) w w') : e * (e' + cA D e') = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := he'
  rw [map_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_eq_zero fun w' hw' => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun w hw => ?_
  obtain ⟨h1, h2⟩ := hPP w hw w' hw'
  rw [mul_add, Formalism.IndefR.Fin.idem_orth (Formalism.IndefR.Fin.idemAt_split (hes w hw)) (hes w hw) (hes' w' hw') h1,
    Formalism.IndefR.Fin.idem_orth_conj (Formalism.IndefR.Fin.idemAt_split (hes w hw)) (hes w hw) (hes' w' hw') h2, add_zero]

theorem ne_and_not_conj {S : Finset ℕ} {w w' : Pl D.host.E} (hw : ¬ Off S w) (hw' : Off S w') :
    w ≠ w' ∧ ¬ Formalism.IndefR.Lev.IsConjPl (D := D) w w' := by
  unfold Off at hw hw'
  push_neg at hw
  obtain ⟨q, hq, hqw⟩ := hw
  refine ⟨fun h => hw' q hq (h ▸ hqw), fun h => ?_⟩
  obtain ⟨c', hc', hc'eq⟩ := h _ hqw
  apply hw' q hq
  have : c' = (q : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    rw [hc'eq]
    simp
  rwa [this] at hc'

theorem actO_eq_self_of_half {S T : HSp D} {e a b : AE D} (ha : e * (a + cA D a) = 0) (hb : e * (b + cA D b) = 0)
    {g : GA D S} {h : GA D T} (hg : SuppAt a S g) (hh : SuppAt b T h) {x : WO S T} (hx : IsHalf e x) :
    actO S T g h x = x := by
  have hx' : ∀ c : AE D, e * c = 0 → (1 - c) • x = x := fun c hc => by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← hx i j, ← mul_assoc, sub_mul, one_mul, mul_comm c e, hc, sub_zero]
  unfold actO
  have k1 : HMul.hMul (mt T h) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    conv_lhs => rw [← hx' _ hb]
    rw [Matrix.mul_smul, ← Matrix.smul_mul, GlobalTheory.SplitScalar.off_smul_mt hh, Matrix.smul_mul, Matrix.one_mul, hx' _ hb]
  rw [k1]
  conv_lhs => rw [← hx' _ ha]
  rw [Matrix.smul_mul, ← Matrix.mul_smul, GlobalTheory.SplitScalar.off_smul_mt_inv hg, Matrix.mul_smul, Matrix.mul_one, hx' _ ha]

theorem suppAt_inv' {a : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt a V g) : SuppAt a V g⁻¹ := by
  have h := GlobalTheory.SplitScalar.off_smul_mt_inv hg
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, sub_eq_zero] at h
  exact fun i j => (congrFun (congrFun h i) j).symm

end GlobalTheory.StdHalfLat

namespace GlobalTheory.StdHalfLat

open Matrix

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

variable {D : D7}

theorem actO_mem_latO_of_hat {S T : HSp D} (g : GA D S) (h : GA D T)
    {ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS,
      (mt S g).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS')
    (hT : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT,
      (mt T h).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT')
    {u : WO S T} (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    actO S T g h u ∈ latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := GlobalTheory.AdelicLatMove.rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    rw [← e, GlobalTheory.AdelicLatMove.actO_rankOne]
    exact GlobalTheory.AdelicLatMove.rankOne_mem_latO S T ΛS' ΛT' a ha _
      (hS _ (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (hT _ (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛT α hα t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem mem_latO_iff_of_half {S T : HSp D} (g : GA D S) (h : GA D T)
    {ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS,
      (mt S g).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS')
    (hS' : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS',
      (mt S g⁻¹).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS)
    (hT : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT,
      (mt T h).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT')
    (hT' : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT',
      (mt T h⁻¹).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT)
    {e a b : AE D} (ha : e * (a + cA D a) = 0) (hb : e * (b + cA D b) = 0) (hg : SuppAt a S g) (hh : SuppAt b T h)
    {x : WO S T} (hx : IsHalf e x) :
    x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      x ∈ latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  constructor
  · intro hm
    have := actO_mem_latO_of_hat g h hS hT hm
    rwa [actO_eq_self_of_half ha hb hg hh hx] at this
  · intro hm
    have := actO_mem_latO_of_hat g⁻¹ h⁻¹ hS' hT' hm
    rwa [actO_eq_self_of_half ha hb (suppAt_inv' hg) (suppAt_inv' hh) hx] at this

theorem half_nsmul {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (k : ℕ) : IsHalf e (k • x) := fun i j => by
  have h := hx i j
  simp only [Matrix.smul_apply, nsmul_eq_mul]
  linear_combination (k : AE D) * h

end GlobalTheory.StdHalfLat

namespace GlobalTheory.StdHalfLat

open Matrix

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem hat_moves {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T} (N : Std G U)
    {X : Node} (hX : DefNode D.R.m X) :
    (∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr X)),
      (mt (G.V X) (N.u X).1).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X)) ∧
    ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X),
      (mt (G.V X) (N.u X).1⁻¹).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr X)) := by
  refine ⟨fun v hv => (N.u_lat X hX v).1 hv, fun v hv => (N.u_lat X hX _).2 ?_⟩
  have e : (Formalism.IndefR.Lev.finE (G.V X) (N.u X).1).1 *ᵥ ((mt (G.V X) (N.u X).1⁻¹).map (toEAf D) *ᵥ v) = v := by
    rw [show (mt (G.V X) (N.u X).1⁻¹).map (toEAf D) = (Formalism.IndefR.Lev.finE (G.V X) (N.u X).1⁻¹).1 from rfl,
      Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  rw [e]
  exact hv

theorem exists_kill {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T} (N : Std G U)
    {t : T} (ht : t ∈ U) {p : Pair T} (d : FinDatum G t p) {X : Node} (hX : DefNode D.R.m X) :
    ∃ a : AE D, d.e * (a + cA D a) = 0 ∧ SuppAt a (G.V X) (N.u X).1 := by
  obtain ⟨P', e', he', hsupp, hoff⟩ := N.u_supp X hX
  refine ⟨e', idemSum_mul_eq_zero d.e_is he' fun w hw w' hw' => ne_and_not_conj ?_ (hoff w' hw'), hsupp⟩
  intro hw0
  have h3 := N.off w hw0
  rcases d.P_over w hw with h | ⟨w'', hw'', h⟩
  · exact h3.1 h
  · exact h3.2.1 t ht w'' hw'' h

end GlobalTheory.StdHalfLat

namespace GlobalTheory.LastVertexMove

open GlobalTheory.StdHalfLat

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem isSBHalf_stdLat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ {p : Pair T}, DefPair D.R.m p → ∀ d : FinDatum G t p,
    d.P = locPl G t → IsSBHalf d.e (stdLat S p) d.fn := by
  intro D T L sc G W U S t ht p hp d _
  have key : ∀ x, IsHalf d.e x →
      (x ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) (fun _ => True) ↔ x ∈ stdLat S p) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hp.nodes
    rcases p with ⟨i, j⟩ | ⟨t', i, j⟩ | i | ⟨t', j⟩
    · obtain ⟨a, ha, hga⟩ := exists_kill S.N ht d h2
      obtain ⟨b, hb, hgb⟩ := exists_kill S.N ht d h1
      have m2 := hat_moves S.N h2
      have m1 := hat_moves S.N h1
      exact (mem_latO_iff_of_half (negGA _ (S.N.u (.grid (i + 1) j)).1) (S.N.u (.grid i j)).1
        m2.1 (fun v hv => by rw [← map_inv]; exact m2.2 v hv) m1.1 m1.2 ha hb hga hgb hx).symm
    · exact hp.elim
    · exact hp.elim
    · obtain ⟨a, ha, hga⟩ := exists_kill S.N ht d h1
      obtain ⟨b, hb, hgb⟩ := exists_kill S.N ht d h2
      have m1 := hat_moves S.N h1
      have m2 := hat_moves S.N h2
      exact (mem_latO_iff_of_half (S.N.u (.top j)).1 (S.N.u (.top (j + 1))).1
        m1.1 m1.2 m2.1 m2.2 ha hb hga hgb hx).symm
  obtain ⟨hsupp, k, hk, hinv, hfin⟩ := d.sb
  refine ⟨hsupp, k, hk, fun u hu hub y => hinv u ((key u hub).2 hu) hub y, fun y hy => ?_⟩
  exact (key _ (half_nsmul (hsupp y hy) k)).1 (hfin y hy)

end GlobalTheory.LastVertexMove

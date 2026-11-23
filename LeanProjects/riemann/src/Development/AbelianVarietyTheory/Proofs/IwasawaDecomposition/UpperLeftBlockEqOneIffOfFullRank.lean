import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodAtOfFixRed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateMaximalCompactMemParahoricLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteUnitarySelfDualFrameToBaseLatticeFra
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubOneIffEntries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CrdLatEqLatFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceCoverProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRadicalSpanGMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe.TrPt

open Formalism.L2.SG.RowsJoinPinned (castGA)

section Unif

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.RedBasicsPf PIW.AdelClassFin

theorem core_unif (I : Formalism.MainNotions.S.AutInst) (w : HeightOneSpectrum (𝓞 I.E)) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.L2.Herm.Af I.F)) (hβ : IsFrame (F := I.F) β I.L)
    (iso : ZMod p ≃+* kP w) (m : ℕ) (hm : m = I.n) :
    ∃ b : Fin m → (Fin I.n → I.E), IsRedBasis0 I w b ∧ ∀ x ∈ I.Kset, ∀ i,
      I.fmat x *ᵥ (fun k => Formalism.UG.inclE (F := I.F) (Af I.F) (b i k)) -
        ∑ j, ((((Matrix.of fun i j : Fin m =>
          iso.symm (((redFn (F := I.F) β w (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.L2.Herm.Af I.F)) :
            GL (Fin I.n) (kP w)) : Matrix (Fin I.n) (Fin I.n) (kP w)) (Fin.cast hm i) (Fin.cast hm j))) j i).val : ℕ) :
            I.E ⊗[I.F] Af I.F) • (fun k => Formalism.UG.inclE (F := I.F) (Af I.F) (b j k)) ∈
        lamAf (F := I.F) (wLat0 I w) := by
  subst hm
  have : NeZero p := ⟨hp.ne_zero⟩
  have hL : ∀ u, u ∈ Formalism.L2.Herm.hatL (F := I.F) I.L ↔ u ∈ I.Lf := by
    intro u
    have e : ((fun x i => Formalism.UG.inclE (F := I.F) (Formalism.L2.Herm.Af I.F) (x i)) '' (I.L : Set (Fin I.n → I.E))) =
        Set.range (fun x : I.L => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((x : Fin I.n → I.E) i)) := by
      ext v; simp
    show u ∈ Submodule.span _ _ ↔ u ∈ Submodule.span _ _
    rw [e]
  set col : Fin I.n → (Fin I.n → I.E ⊗[I.F] Af I.F) := fun j => β.1 *ᵥ Pi.single j 1 with hcol_def
  have hβsum : ∀ v, β.1 *ᵥ v = ∑ j, v j • col j := by
    intro v
    funext k
    simp [col, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply, mul_comm]
  have hcol : ∀ j, col j ∈ I.Lf := by
    intro j
    refine (hL _).1 ((hβ _).2 fun k => ?_)
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have hres : ∀ c : Formalism.L2.Herm.intAf I.F I.E, resS I.F w c = 0 → ∀ u ∈ I.Lf,
      (c : I.E ⊗[I.F] Af I.F) • u ∈ lamAf (F := I.F) (wLat0 I w) := by
    intro c hc
    have hc' : c ∈ Submodule.span (Formalism.L2.Herm.intAf I.F I.E) ((oToS I.F I.E) '' (w.asIdeal : Set (𝓞 I.E))) := by
      have h1 : ((RingEquiv.ofBijective (cmpS I.F w.asIdeal) (cmpS_bij (F := I.F) w.asIdeal w.ne_bot)).symm
        (Ideal.Quotient.mk (idS I.F w.asIdeal) c)) = 0 := hc
      have h2 := (map_eq_zero_iff _ (RingEquiv.injective _)).1 h1
      exact Ideal.Quotient.eq_zero_iff_mem.1 h2
    refine Submodule.span_induction (p := fun (c : Formalism.L2.Herm.intAf I.F I.E) _ => ∀ u ∈ I.Lf,
      ((c : Formalism.L2.Herm.intAf I.F I.E) : I.E ⊗[I.F] Af I.F) • u ∈ lamAf (F := I.F) (wLat0 I w)) ?_ ?_ ?_ ?_ hc'
    · rintro _ ⟨a, ha, rfl⟩ u hu
      exact smul_mem I w ha hu
    · intro u _; simp
    · intro a b _ _ ha hb u hu
      rw [AddMemClass.coe_add, add_smul]; exact add_mem (ha u hu) (hb u hu)
    · intro s a _ ha u hu
      rw [smul_eq_mul, MulMemClass.coe_mul, mul_smul]
      exact Submodule.smul_mem _ s (ha u hu)
  choose b hbL hb using fun i => dense I w hp hcard (hcol i)
  refine ⟨b, ⟨hbL, ?_⟩, ?_⟩
  · intro z hz
    have hd : ∀ i, ((β⁻¹).1 *ᵥ iv I z) i ∈ Formalism.L2.Herm.intAf I.F I.E :=
      (hβ _).1 ((hL _).2 (DictLat.iv_mem I hz))
    choose c hc using fun i => int_surj I w hp hcard (resS I.F w ⟨_, hd i⟩)
    refine ⟨c, inter I w ?_⟩
    rw [iv_lin]
    have e1 : iv I z = ∑ i, ((β⁻¹).1 *ᵥ iv I z) i • col i := by
      rw [← hβsum, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have e2 : iv I z - ∑ i, (c i : I.E ⊗[I.F] Af I.F) • iv I (b i) =
        ∑ i, ((⟨_, hd i⟩ - (c i : Formalism.L2.Herm.intAf I.F I.E) : Formalism.L2.Herm.intAf I.F I.E) : I.E ⊗[I.F] Af I.F) • col i +
          ∑ i, (c i : I.E ⊗[I.F] Af I.F) • (col i - iv I (b i)) := by
      conv_lhs => rw [e1]
      simp only [AddSubgroupClass.coe_sub, SubringClass.coe_intCast, sub_smul, smul_sub, Finset.sum_sub_distrib]
      abel
    rw [e2]
    refine add_mem (Submodule.sum_mem _ fun i _ => hres _ ?_ _ (hcol i))
      (Submodule.sum_mem _ fun i _ => ?_)
    · rw [map_sub, ← hc i, map_intCast, sub_self]
    · rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem (hb i) _
  · intro x hx i
    have hx' : ∀ v, v ∈ I.Lf ↔ I.fmat x *ᵥ v ∈ I.Lf := hx
    have hxi : ∀ v, v ∈ I.Lf ↔ (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v ∈ I.Lf := (Formalism.UG.stabGL I.Lf).inv_mem hx
    have hS : (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.L2.Herm.Af I.F)) ∈ St β :=
      (GlobalTheory.LevSplit.mem_St_iff β I.L hβ _).2 ⟨fun v hv => (hL _).2 ((hx' _).1 ((hL _).1 hv)),
        fun v hv => (hL _).2 ((hxi _).1 ((hL _).1 hv))⟩
    obtain ⟨y, hy⟩ := hS
    rw [← hy, redFn_frGL]
    have hfm : I.fmat x = β.1 * (intGL I.F I.E I.n y).1 * (β⁻¹).1 := by
      show ((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) = _
      rw [← hy]; rfl
    have hact : ∀ i, I.fmat x *ᵥ col i = ∑ j, ((y.1 j i : Formalism.L2.Herm.intAf I.F I.E) : I.E ⊗[I.F] Af I.F) • col j := by
      intro i
      rw [hfm, ← hβsum]
      simp only [col, Matrix.mulVec_mulVec]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mulVec_mulVec]
      congr 1
      funext j
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rfl
    show I.fmat x *ᵥ iv I (b i) - ∑ j, (((iso.symm (resS I.F w (y.1 j i))).val : ℕ) : I.E ⊗[I.F] Af I.F) •
      iv I (b j) ∈ lamAf (F := I.F) (wLat0 I w)
    have hv : ∀ j, resS I.F w (y.1 j i - (((iso.symm (resS I.F w (y.1 j i))).val : ℕ) :
        Formalism.L2.Herm.intAf I.F I.E)) = 0 := by
      intro j
      rw [map_sub, map_natCast, ← map_natCast iso, ZMod.natCast_zmod_val, RingEquiv.apply_symm_apply, sub_self]
    have key : I.fmat x *ᵥ iv I (b i) - ∑ j, (((iso.symm (resS I.F w (y.1 j i))).val : ℕ) : I.E ⊗[I.F] Af I.F) •
        iv I (b j) = (∑ j, ((y.1 j i - (((iso.symm (resS I.F w (y.1 j i))).val : ℕ) :
          Formalism.L2.Herm.intAf I.F I.E) : Formalism.L2.Herm.intAf I.F I.E) : I.E ⊗[I.F] Af I.F) • col j +
          ∑ j, (((iso.symm (resS I.F w (y.1 j i))).val : ℕ) : I.E ⊗[I.F] Af I.F) • (col j - iv I (b j))) -
          I.fmat x *ᵥ (col i - iv I (b i)) := by
      rw [Matrix.mulVec_sub, hact i]
      simp only [AddSubgroupClass.coe_sub, SubringClass.coe_natCast, sub_smul, smul_sub, Finset.sum_sub_distrib]
      abel
    rw [key]
    exact sub_mem (add_mem (Submodule.sum_mem _ fun j _ => hres _ (hv j) _ (hcol j))
      (Submodule.sum_mem _ fun j _ => by rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem (hb j) _))
      (stab_w I w hx (hb i))

end Unif

end GlobalTheory.Mem.SRe.TrPt

namespace GlobalTheory.Mem.SRe.TrPt

open Formalism.L2.SG.RowsJoinPinned (castGA)

variable {D : D7}

theorem iotaX_symm_eq' {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (x : I.GA) :
    ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)).symm x = (Formalism.IndefR.RationalEmbedding.iota D).symm (castGA h x) := by
  subst h; rfl

theorem castGA_mem' {I I' : Formalism.MainNotions.S.AutInst} (h : I = I') (k : I.Gf) (g : ℕ) :
    (k ∈ I.Kset ↔ (castGA h (1, k)).2 ∈ I'.Kset) ∧ (k ∈ I.Kg g ↔ (castGA h (1, k)).2 ∈ I'.Kg g) := by
  subst h; exact ⟨Iff.rfl, Iff.rfl⟩

abbrev kmatI (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) : GL (Fin (Yc D 0).rank) (EAf D) := x.1

theorem finE_kap' (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (Yc D 0))
    (k : X.B.I.Gf) :
    finE (Yc D 0) (kap X h t k) = (finE (Yc D 0) t)⁻¹ * kmatI (castGA h (1, k)).2 * finE (Yc D 0) t := by
  have e0 : kap X h t k = (t⁻¹ * (show GA D (Yc D 0) from (iotaX X h).symm (1, k)) * t) := rfl
  rw [e0, map_mul, map_mul, map_inv]
  congr 2
  have e : (iotaX X h).symm (1, k) = (Formalism.IndefR.RationalEmbedding.iota D).symm (castGA h (1, k)) := iotaX_symm_eq' h (1, k)
  rw [e]
  exact Formalism.L2.SG.EvalTIota.finE_brg_i (castGA h (1, k))

theorem kap_mul (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (k k' : X.B.I.Gf) : kap X h t (k * k') = kap X h t k * kap X h t k' := by
  have e : ((1 : X.B.I.Ginf), k * k') = ((1 : X.B.I.Ginf), k) * (1, k') := by
    rw [Prod.mk_mul_mk, one_mul]
  show (t⁻¹ * (iotaX X h).symm ((1 : X.B.I.Ginf), k * k') * t : GA D (D.sp.Y 0)) =
    (t⁻¹ * (iotaX X h).symm ((1 : X.B.I.Ginf), k) * t : GA D (D.sp.Y 0)) * (t⁻¹ * (iotaX X h).symm (1, k') * t)
  rw [e, map_mul]
  group

theorem glue_unif (I : Formalism.MainNotions.S.AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (ιE : I.E ≃+* D.host.E)
    (hιE : ∀ x, HEq (ιE x) x) (w' : HeightOneSpectrum (𝓞 I.E)) (PP : Pl D.host.E)
    (hw' : ∀ a : 𝓞 I.E, a ∈ w'.asIdeal ↔ RingOfIntegers.mapRingEquiv ιE a ∈ PP.asIdeal)
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card (kP PP) = p) (iso : ZMod p ≃+* kP PP)
    (t : GA D (D.sp.Y 0)) (β : GL (Fin (Yc D 0).rank) (EAf D))
    (hFr : IsFrame (finE (Yc D 0) t * β) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0))
    (hr : D.R.r ≤ (Yc D 0).rank) (hn : I.n = D.R.r) :
    ∃ b : Fin D.R.r → (Fin I.n → I.E), Formalism.L2.SG.Pf.RowDictPf.IsRedBasis0 I w' b ∧ ∀ k ∈ I.Kset, ∀ i,
      I.fmat k *ᵥ (fun l => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (b i l)) -
        ∑ j, (((iso.symm (((redFn β PP (finE (Yc D 0)
          (t⁻¹ * ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)).symm (1, k) * t)) : GL (Fin (Yc D 0).rank) (kP PP)) :
            Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (kP PP)) (Fin.castLE hr j) (Fin.castLE hr i))).val : ℕ) :
            I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (fun l => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (b j l)) ∈
        Formalism.MainNotions.S.lamAf (F := I.F) (Formalism.L2.SG.Pf.RowDictPf.wLat0 I w') := by
  subst h
  have hid : ∀ x, ιE x = x := fun x => eq_of_heq (hιE x)
  obtain rfl := GlobalTheory.RedFrame.hw_eq ιE hid w' PP hw'
  have hL : IsFrame (F := (Formalism.L2.SG.InstExistsPf.instOf D).F) (finE (Yc D 0) t * β)
      (Formalism.L2.SG.InstExistsPf.instOf D).L := by
    rw [GlobalTheory.RedFrame.Lv_eq]; exact hFr
  obtain ⟨b, hb1, hb2⟩ := core_unif (Formalism.L2.SG.InstExistsPf.instOf D) w' hp hcard (finE (Yc D 0) t * β) hL iso
    D.R.r hn.symm
  refine ⟨b, hb1, fun k hk i => ?_⟩
  have hk1 : finE (Yc D 0) (t⁻¹ * ((Formalism.IndefR.RationalEmbedding.iota D).trans
      (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _))).symm (1, k) * t) =
      (finE (Yc D 0) t)⁻¹ * GlobalTheory.RedFrame.finPt D k * finE (Yc D 0) t := by
    show finE (D.sp.Y 0) (t⁻¹ * ((Formalism.IndefR.RationalEmbedding.iota D).trans
      (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _))).symm (1, k) * t) = _
    rw [map_mul, map_mul, map_inv]
    congr 2
    exact Units.ext (GlobalTheory.RedFrame.finE_iota_symm D k)
  have hc := GlobalTheory.RedFrame.redFn_conj (finE (Yc D 0) t) β (GlobalTheory.RedFrame.finPt D k) w'
  rw [hk1, hc]
  exact hb2 k hk i

end GlobalTheory.Mem.SRe.TrPt

namespace GlobalTheory.Mem.SRe.TrPt

open Formalism.L2.SG.RowsJoinPinned (castGA)
open GlobalTheory.KapLevel

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def redK (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (eR : G' ≃* G0g D.nd)
    (t : GA D (D.sp.Y 0)) (k : X.B.I.Gf) : G0g D.nd :=
  eR (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))))

theorem kap_mem' (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (D.sp.Y 0)) (ht : t ∈ GfC (Yc D 0))
    (hF : IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) (k : X.B.I.Gf)
    (hk : k ∈ X.B.I.Kset) : kap X h t k ∈ GfC (Yc D 0) ∧
      finE (Yc D 0) (kap X h t k) ∈ Formalism.L2.DIV.parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) := by
  obtain ⟨hy1, hy2⟩ := cast_one_fin h.symm k hk
  have hkap : kap X h t k = (@id (GA D (D.sp.Y 0)) t)⁻¹ * (Formalism.IndefR.RationalEmbedding.iota D).symm
      ((Formalism.L2.SG.RowsJoinPinned.castGA h.symm).symm (1, k)) * @id (GA D (D.sp.Y 0)) t := rfl
  refine ⟨?_, ?_⟩
  · rw [hkap]
    exact mul_mem (mul_mem (inv_mem ht) ((Formalism.L2.SG.EvalTIota.brg_mem_GfC_i _).2 hy1)) ht
  · have hU := GlobalTheory.LevSplit.finE_mem_UA (Yc D 0) (kap X h t k)
    have hfin0 : Formalism.IndefR.Lev.finE (D.sp.Y 0) (kap X h t k) = (Formalism.IndefR.Lev.finE (D.sp.Y 0) t)⁻¹ *
        @id (GL (Fin (D.sp.Y 0).rank) (Formalism.IndefR.Lev.EAf D)) ((Formalism.L2.SG.RowsJoinPinned.castGA h.symm).symm (1, k)).2.1 *
        Formalism.IndefR.Lev.finE (D.sp.Y 0) t := by
      rw [hkap, map_mul, map_mul, map_inv, Formalism.L2.SG.EvalTIota.finE_brg_i]
      rfl
    have hfin : Formalism.IndefR.Lev.finE (Yc D 0) (kap X h t k) = (Formalism.IndefR.Lev.finE (Yc D 0) t)⁻¹ *
        @id (GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) ((Formalism.L2.SG.RowsJoinPinned.castGA h.symm).symm (1, k)).2.1 *
        Formalism.IndefR.Lev.finE (Yc D 0) t := hfin0
    rw [hfin] at hU ⊢
    obtain ⟨s0, s1⟩ := kset_stab _ hy2 _ rfl
    have hr : ∀ a : Fin (Yc D 0).rank, (a : ℕ) < (R.dat0 R.triv).r := fun a =>
      lt_of_lt_of_eq a.2 (Formalism.L2.SG.InstExistsPf.rank_eq D)
    refine Formalism.L2.DIV.mem_parLev.2 ⟨hU, st_of_stab _ _ _ hF s0 s1, fun PP _ => ?_, fun PP hP => ?_⟩
    · rw [Formalism.L2.DIV.mem_blockTri]
      intro i j hij
      exfalso
      unfold Formalism.L2.DIV.blkOf at hij
      rw [if_pos (hr i), if_pos (hr j)] at hij
      exact lt_irrefl 0 hij
    · exact absurd hP (Finset.notMem_empty PP)

end GlobalTheory.Mem.SRe.TrPt

namespace GlobalTheory.Mem.SRe.TrPt

open Formalism.L2.SG.RowsJoinPinned (castGA)

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem redK_entry (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (eR : G' ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg)
    (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1)
    (hpe : ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv))
    (t : GA D (D.sp.Y 0)) (hrank : (Yc D 0).rank ≤ D.R.r) (k : X.B.I.Gf) (kv : Σ k : Fin 2, D.nd.PlG k)
    (i j : Fin D.R.r) :
    (((redK R X h eR t k kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) _) i j) =
      (iso kv).symm (((redFn (R.βY 0) (plg kv).1 (finE (Yc D 0) (kap X h t k)) : GL (Fin (Yc D 0).rank) (kP (plg kv).1)) :
        Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (kP (plg kv).1))
          (Fin.castLE (R.dat0 R.triv).hr i) (Fin.castLE (R.dat0 R.triv).hr j)) := by
  have hcomp : ∀ (x : G0 R.Pg D.R.r),
      (((eR (R.eG.symm x)) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) _) =
        ((x (plg kv) : GL (Fin D.R.r) (kP (plg kv).1)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP (plg kv).1)).map
          (iso kv).symm := by
    intro x
    obtain ⟨g, rfl⟩ := R.eG.surjective x
    rw [MulEquiv.symm_apply_apply, hpe g kv]
    ext a b
    simp [Formalism.UG.bc]
  unfold redK
  refine (congrFun (congrFun (hcomp (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k)))) i) j).trans ?_
  simp only [Matrix.map_apply]
  congr 1
  exact congrFun (congrFun (GlobalTheory.RedFrame.upperLeftBlock_eq_submatrix_of_rank_eq (R.dat0 R.triv).hr hrank _) i) j

open Formalism.L2.SG.Pf.RowDictPf in

theorem fixRed_redK (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (hιE : ∀ x : X.B.I.E, HEq (X.ιE x) x)
    (eR : G' ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg)
    (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1)
    (hplw : ∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2)
    (hpe : ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv))
    (t : GA D (D.sp.Y 0))
    (hFr : IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) :
    ∃ b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E, FixRed X (redK R X h eR t) b := by
  have hr := (R.dat0 R.triv).hr
  have hrank : (Yc D 0).rank ≤ D.R.r := by
    have e : X.B.I.n = D.R.r := X.n_eq
    rw [h] at e
    exact e.le
  have hG := fun kv : (Σ k : Fin 2, D.nd.PlG k) =>
    glue_unif X.B.I h X.ιE hιE (wB X (plg kv).1) (plg kv).1 (fun a => Iff.rfl) (D.host.g_prime kv.1)
      (by rw [hplw kv]; exact card_res_host kv.1 kv.2) (iso kv) t (R.βY 0) hFr hr X.n_eq
  choose b hb1 hb2 using hG
  refine ⟨b, fun kv => ⟨?_, fun k hk i => ?_⟩⟩
  · rw [← hplw kv]
    unfold IsRedBasis
    rw [wLat_eq X]
    exact hb1 kv
  · rw [← hplw kv]
    unfold wLf
    rw [wLat_eq X]
    simp only [redK_entry R X h eR plg iso hpe t hrank]
    exact hb2 kv k hk i

end GlobalTheory.Mem.SRe.TrPt

namespace GlobalTheory.Mem.SRe.TrPt

open Formalism.L2.SG.RowsJoinPinned (castGA)

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem upperLeftBlock_eq_one_iff_of_full_rank {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (hn : n ≤ r) (g : GL (Fin n) κ) :
    Formalism.L2.DIV.upperLeftBlock hr g = 1 ↔ g = 1 := by
  have hmem : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
    intro i j hij
    exfalso
    have hi := i.2
    have hj := j.2
    unfold Formalism.L2.DIV.blk2 at hij
    split_ifs at hij <;> omega
  constructor
  · intro h
    have h2 := congrArg (fun u : GL (Fin r) κ => (u : Matrix (Fin r) (Fin r) κ)) h
    rw [Formalism.L2.DIV.upper_block_val_submatrix hr hmem] at h2
    apply Units.ext
    ext i j
    have := congrFun (congrFun h2 ⟨i.1, by omega⟩) ⟨j.1, by omega⟩
    simpa [Matrix.one_apply, Fin.ext_iff] using this
  · rintro rfl
    unfold Formalism.L2.DIV.upperLeftBlock
    exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _

theorem rank_le_of (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) : (Yc D 0).rank ≤ D.R.r := by
  have e : X.B.I.n = D.R.r := X.n_eq
  rw [h] at e
  exact e.le

theorem redK_mul (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (eR : G' ≃* G0g D.nd) (t : GA D (D.sp.Y 0)) (ht : t ∈ GfC (Yc D 0))
    (hF : IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0))
    (k : X.B.I.Gf) (hk : k ∈ X.B.I.Kset) (k' : X.B.I.Gf) (hk' : k' ∈ X.B.I.Kset) :
    redK R X h eR t (k * k') = redK R X h eR t k * redK R X h eR t k' := by
  unfold redK
  rw [kap_mul, map_mul, Formalism.L2.DIV.rTup_mul (kap_mem' R X h t ht hF k hk).2 (kap_mem' R X h t ht hF k' hk').2]
  exact (congrArg eR (R.eG.symm.map_mul _ _)).trans (eR.map_mul _ _)

theorem redK_eq_one_iff (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (eR : G' ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg)
    (hplg : ∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) (t : GA D (D.sp.Y 0))
    (hfr : IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0))
    (k : X.B.I.Gf) (hk : k ∈ X.B.I.Kset) : redK R X h eR t k = 1 ↔ k ∈ X.B.I.Kg X.B.g := by
  unfold redK
  have e1 : ∀ x : G0 R.Pg D.R.r, eR (R.eG.symm x) = 1 ↔ x = 1 := fun x => by
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
  refine (e1 _).trans ?_
  rw [finE_kap' X h t k]
  obtain ⟨hK, hKg⟩ := castGA_mem' h k X.B.g
  rw [hKg, X.g_eq]
  have hx := hK.1 hk
  have hrank := rank_le_of X h
  generalize (castGA h (1, k)).2 = x at hx ⊢
  have hin : ∀ PP ∈ R.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hP
    have e := hplg (plg.symm ⟨PP, hP⟩)
    rw [Equiv.apply_symm_apply] at e
    have := Formalism.L2.SG.Pf.RowDictPf.level_mem X (plg.symm ⟨PP, hP⟩)
    rw [X.g_eq] at this
    rw [show PP = D.naut.plGw _ _ from e]
    exact this
  have hg : 1 ≤ D.host.g 0 * D.host.g 1 :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have hcore : x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kg (D.host.g 0 * D.host.g 1) ↔
      ∀ PP ∈ R.Pg, Formalism.L2.DIV.redFn (finE (Yc D 0) t * R.βY 0) PP x.1 = 1 := by
    rw [GlobalTheory.KgFrame.mem_Kg_iff_redFn D _ x _ hfr hx hg (GlobalTheory.TypePrimesRadical.isRadical_span_g_mul D)]
    constructor
    · exact fun H PP hP => H PP (hin PP hP)
    · intro H PP hPP
      rcases GlobalTheory.TypeProductCover.place_cover_prod D R.Pg plg hplg PP hPP with h1 | ⟨PP', hP', hc⟩
      · exact H PP h1
      · exact GlobalTheory.ConjPlaceRed.redFn_conj_eq_one D _ x PP PP' hfr hx hc (H PP' hP')
  rw [hcore]
  constructor
  · intro H PP hP
    have h1 : Formalism.L2.DIV.upperLeftBlock (R.dat0 R.triv).hr (Formalism.L2.DIV.redFn (R.βY 0) PP
        (((finE (Yc D 0)) t)⁻¹ * kmatI x * (finE (Yc D 0)) t)) = 1 := congrFun H ⟨PP, hP⟩
    have := (upperLeftBlock_eq_one_iff_of_full_rank _ hrank _).1 h1
    rwa [GlobalTheory.RedFrame.redFn_conj] at this
  · intro H
    funext PP
    show Formalism.L2.DIV.upperLeftBlock (R.dat0 R.triv).hr (Formalism.L2.DIV.redFn (R.βY 0) PP.1
        (((finE (Yc D 0)) t)⁻¹ * kmatI x * (finE (Yc D 0)) t)) = 1
    refine (upperLeftBlock_eq_one_iff_of_full_rank _ hrank _).2 ?_
    rw [GlobalTheory.RedFrame.redFn_conj]
    exact H PP.1 PP.2

theorem redK_onto (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (eR : G' ≃* G0g D.nd) (hLev : R.toLevCh.Is A.μ0) (t : GA D (Yc D 0)) (ht : t ∈ GfC (Yc D 0))
    (hFrame : IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) (γ : G0g D.nd) :
    ∃ k ∈ X.B.I.Kset, redK R X h eR t k = γ := by
  obtain ⟨κ, hκf, hκp, hκr⟩ := GlobalTheory.LevelRowsObj.liftsExist hLev (R.eG (eR.symm γ))
  set y : GA D (Yc D 0) := t * κ * t⁻¹ with hydef
  have hy : y ∈ GfC (Yc D 0) := (GfC _).mul_mem ((GfC _).mul_mem ht hκf) ((GfC _).inv_mem ht)
  have h1 := GlobalTheory.SeeMatchOnto.real_one X h y hy
  have hy' : (iotaX X h).symm (1, (iotaX X h y).2) = y := by
    rw [← h1]; exact (iotaX X h).symm_apply_apply y
  refine ⟨(iotaX X h y).2, ?_, ?_⟩
  · have hS : finE (Yc D 0) y ∈ Formalism.L2.DIV.St (finE (Yc D 0) t * R.βY 0) := by
      rw [hydef, map_mul, map_mul, map_inv]
      exact GlobalTheory.SeeMatchOnto.conj_mem_St (Formalism.L2.DIV.parLev_St hκp)
    exact GlobalTheory.SeeMatchOnto.castGA_snd_Kset h.symm _ (GlobalTheory.SeeMatchOnto.iota_snd_mem_Kset _ hFrame y hS)
  · have hk : kap X h t (iotaX X h y).2 = κ := by
      unfold kap
      rw [hy']
      show (t⁻¹ * (t * κ * t⁻¹) * t : GA D (Yc D 0)) = κ
      group
    unfold redK
    rw [hk, hκr, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

end GlobalTheory.Mem.SRe.TrPt

namespace GlobalTheory.Mem.SRe.TrPt

open Formalism.L2.SG.RowsJoinPinned (castGA)

theorem exists_trans : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (eR : G' ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ x : X.B.I.E, HEq (X.ιE x) x) → R.toLevCh.Is A.μ0 → (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) → (∀ kv, R.C.P.Div kv.1 (plg kv).1) → (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) → ∃ t₀ : GA D (D.sp.Y 0), t₀ ∈ GfC (Yc D 0) ∧ ∃ (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), IsRedHom X red ∧ FixRed X red b ∧ (∀ k ∈ X.B.I.Kset, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (eR.symm (red k))) (kap X h t₀ k)) ∧ ∀ y ∈ levG (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)), ∃ k ∈ X.B.I.Kset, y = kap X h t₀ k := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R X h eR plg iso hιE hLev hplw _ hpe
  have hm : 0 < D.R.m := lt_of_lt_of_le (by norm_num) D.R.two_le_m
  obtain ⟨t, ht, hF⟩ := GlobalTheory.SelfDualFrameConj.frame_conj (Yc D 0) (R.βY 0) (R.ΛY 0) _ (hLev.βY 0 hm)
  obtain ⟨b, hb⟩ := fixRed_redK R X h hιE eR plg iso hplw hpe t hF
  refine ⟨t, ht, redK R X h eR t, b, ⟨goodAt_of_fixRed hb, fun k hk k' hk' => redK_mul R X h eR t ht hF k hk k' hk',
    fun γ => redK_onto R X h eR hLev t ht hF γ, fun k hk => redK_eq_one_iff R X h eR plg hplw t hF k hk⟩, hb,
    fun k hk => ?_, fun y hy => ?_⟩
  · obtain ⟨h1, h2⟩ := kap_mem' R X h t ht hF k hk
    exact ⟨h1, h2, (R.eG.apply_symm_apply _).symm.trans (congrArg R.eG (eR.symm_apply_apply _).symm)⟩
  · have hyG : y ∈ GfC (Yc D 0) := hy.1
    have hyS : finE (Yc D 0) y ∈ Formalism.L2.DIV.St (R.βY 0) := Formalism.L2.DIV.parLev_St hy.2.1
    set y' : GA D (Yc D 0) := t * y * t⁻¹ with hydef
    have hy'G : y' ∈ GfC (Yc D 0) := (GfC _).mul_mem ((GfC _).mul_mem ht hyG) ((GfC _).inv_mem ht)
    have h1 := GlobalTheory.SeeMatchOnto.real_one X h y' hy'G
    have hy' : (iotaX X h).symm (1, (iotaX X h y').2) = y' := by
      rw [← h1]; exact (iotaX X h).symm_apply_apply y'
    refine ⟨(iotaX X h y').2, ?_, ?_⟩
    · have hS : finE (Yc D 0) y' ∈ Formalism.L2.DIV.St (finE (Yc D 0) t * R.βY 0) := by
        rw [hydef, map_mul, map_mul, map_inv]
        exact GlobalTheory.SeeMatchOnto.conj_mem_St hyS
      exact GlobalTheory.SeeMatchOnto.castGA_snd_Kset h.symm _ (GlobalTheory.SeeMatchOnto.iota_snd_mem_Kset _ hF y' hS)
    · unfold kap
      rw [hy']
      show y = (t⁻¹ * (t * y * t⁻¹) * t : GA D (Yc D 0))
      group

end GlobalTheory.Mem.SRe.TrPt

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsOrb.ModelIso

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem fixedFrameOfWord_castSucc_eq_hyperbolic (a : Fin D.R.rS) : (GlobalTheory.TypeAsm.F0 X u).e a.castSucc = X.eX a := by
  show (lf D (X.Fu u)).fl.fvec a.castSucc = X.eX a
  rw [GlobalTheory.TypeAsm.fv_cast]
  exact congrFun (X.Fu_e u) a

theorem fixedFrameOfWord_last_eq_anisotropic : (GlobalTheory.TypeAsm.F0 X u).e (Fin.last _) = X.zu u := by
  show (lf D (X.Fu u)).fl.fvec (Fin.last _) = X.zu u
  rw [GlobalTheory.TypeAsm.fv_last]
  exact X.flagZVector u

theorem fixedFrameOfWord_isotropicSpan_eq : (GlobalTheory.TypeAsm.F0 X u).X = Submodule.span D.host.E (Set.range X.eX) := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.X Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range, fixedFrameOfWord_castSucc_eq_hyperbolic]
  exact ⟨fun ⟨b, _, h⟩ => ⟨b, h⟩, fun ⟨b, h⟩ => ⟨b, b.isLt, h⟩⟩

theorem hT_span_left {v : (VS D).V} (hv : ∀ a, (VS D).hT (X.eX a) v = 0) {y : (VS D).V}
    (hy : y ∈ Submodule.span D.host.E (Set.range X.eX)) : (VS D).hT y v = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy
  simp [map_sum, hv]

theorem hT_span_span {y y' : (VS D).V} (hy : y ∈ Submodule.span D.host.E (Set.range X.eX))
    (hy' : y' ∈ Submodule.span D.host.E (Set.range X.eX)) : (VS D).hT y y' = 0 := by
  refine hT_span_left X (fun a => ?_) hy
  exact p_symm_zero (VS D) (hT_span_left X (fun b => X.ee b a) hy')

theorem hT_f_e (a b : Fin D.R.rS) : (VS D).hT (X.fY b) (X.eX a) = if a = b then 1 else 0 := by
  rw [a_herm (S := VS D) (X.eX a) (X.fY b), X.ef a b]
  split_ifs <;> simp

theorem span_eq_zero {d : (VS D).V} (hd : d ∈ Submodule.span D.host.E (Set.range X.eX))
    (h : ∀ b, (VS D).hT (X.fY b) d = 0) : d = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hd
  have hc : ∀ b, c b = 0 := by
    intro b
    have := h b
    simpa [map_sum, hT_f_e] using this
  simp [hc]

end GlobalTheory.RowsOrb.ModelIso

namespace GlobalTheory.RowsOrb.ModelIso

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def corr (W : Submodule D.host.E (VS D).V) : W →ₗ[D.host.E] (VS D).V :=
  ∑ a, LinearMap.smulRight (((VS D).hT (X.fY a)).comp W.subtype) (X.eX a)

theorem corr_apply (W : Submodule D.host.E (VS D).V) (w : W) :
    corr X W w = ∑ a, (VS D).hT (X.fY a) (w : (VS D).V) • X.eX a := by
  simp [corr, LinearMap.sum_apply]

theorem corr_mem (W : Submodule D.host.E (VS D).V) (w : W) :
    corr X W w ∈ Submodule.span D.host.E (Set.range X.eX) := by
  rw [corr_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end GlobalTheory.RowsOrb.ModelIso

open GlobalTheory.RowsOrb.ModelIso in

theorem GlobalTheory.RowsOrb.ub_equiv_model : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (W : Submodule D.host.E (VS D).V)
    (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (GlobalTheory.TypeAsm.F0 X u) HW W.subtype →
    ∃ e : GlobalTheory.RowsOrb.Ub X u ≃ₗ[D.host.E] W, (∀ x y, HW.B.flip (e x) (e y) = GlobalTheory.RowsOrb.hU X u x y) ∧
      ∀ x : GlobalTheory.RowsOrb.Ub X u, ((e x : W) : (VS D).V) - ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ (GlobalTheory.TypeAsm.F0 X u).X := by
  intro D X u W HW hE

  have hWe : ∀ (w : W) a, (VS D).hT (X.eX a) (w : (VS D).V) = 0 := by
    intro w a
    have h := ((hE.2 (w : (VS D).V)).2 (Submodule.mem_sup_left ⟨w, rfl⟩)) a.castSucc
    change (VS D).hT (w : (VS D).V) ((GlobalTheory.TypeAsm.F0 X u).e a.castSucc) = 0 at h
    rw [fixedFrameOfWord_castSucc_eq_hyperbolic] at h
    exact p_symm_zero (VS D) h
  have hWz : ∀ w : W, (VS D).hT (X.zu u) (w : (VS D).V) = 0 := by
    intro w
    have h := ((hE.2 (w : (VS D).V)).2 (Submodule.mem_sup_left ⟨w, rfl⟩)) (Fin.last _)
    change (VS D).hT (w : (VS D).V) ((GlobalTheory.TypeAsm.F0 X u).e (Fin.last _)) = 0 at h
    rw [fixedFrameOfWord_last_eq_anisotropic] at h
    exact p_symm_zero (VS D) h
  have hXW : ∀ (w : W) {y : (VS D).V}, y ∈ Submodule.span D.host.E (Set.range X.eX) →
      (VS D).hT y (w : (VS D).V) = 0 ∧ (VS D).hT (w : (VS D).V) y = 0 := by
    intro w y hy
    have h := hT_span_left X (hWe w) hy
    exact ⟨h, p_symm_zero (VS D) h⟩
  have hBW : ∀ x y : W, HW.B x y = (VS D).hT (y : (VS D).V) (x : (VS D).V) := fun x y => (hE.1 x y).symm

  have hmWb : ∀ w : W, (w : (VS D).V) - corr X W w ∈ GlobalTheory.RowsOrb.Wb X := by
    intro w
    rw [GlobalTheory.RowsOrb.mem_Wb]
    intro b
    have hc := corr_mem X W w
    refine ⟨?_, ?_⟩
    · rw [map_sub, hWe w b, zero_sub, neg_eq_zero]
      exact p_symm_zero (VS D) (hT_span_left X (fun a => X.ee a b) hc)
    · rw [map_sub, corr_apply, map_sum]
      simp only [map_smul, hT_f_e, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, sub_self]
  have hmUb : ∀ w : W, (⟨(w : (VS D).V) - corr X W w, hmWb w⟩ : GlobalTheory.RowsOrb.Wb X) ∈ GlobalTheory.RowsOrb.Ub X u := by
    intro w
    rw [GlobalTheory.RowsOrb.mem_Ub]
    change (VS D).hT (X.zu u) ((w : (VS D).V) - corr X W w) = 0
    rw [map_sub, hWz w, zero_sub, neg_eq_zero]
    refine p_symm_zero (VS D) (hT_span_left X (fun a => (X.zu_orth u a).1) (corr_mem X W w))
  let g : W →ₗ[D.host.E] GlobalTheory.RowsOrb.Ub X u :=
    { toFun := fun w => ⟨⟨(w : (VS D).V) - corr X W w, hmWb w⟩, hmUb w⟩
      map_add' := fun x y => by ext; simp only [Submodule.coe_add, map_add]; abel
      map_smul' := fun c x => by ext; simp [smul_sub] }
  have hg : ∀ w, (((g w : GlobalTheory.RowsOrb.Wb X)) : (VS D).V) = (w : (VS D).V) - corr X W w := fun _ => rfl
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h0 : (w : (VS D).V) = corr X W w := by
      have := congrArg (fun x : GlobalTheory.RowsOrb.Ub X u => ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V)) hw
      simp only [hg, ZeroMemClass.coe_zero] at this
      exact sub_eq_zero.1 this
    have hmem : (w : (VS D).V) ∈ Submodule.span D.host.E (Set.range X.eX) := h0 ▸ corr_mem X W w
    exact HW.nondeg w fun y => by rw [hBW]; exact (hXW y hmem).2
  have hsurj : Function.Surjective g := by
    intro x
    have hv : ∀ a : Fin (D.R.rS + 1), (GlobalTheory.TypeAsm.HV D).B ((GlobalTheory.TypeAsm.F0 X u).e a) ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = 0 := by
      intro a
      change (VS D).hT _ ((GlobalTheory.TypeAsm.F0 X u).e a) = 0
      refine Fin.lastCases ?_ (fun b => ?_) a
      · rw [fixedFrameOfWord_last_eq_anisotropic]; exact p_symm_zero (VS D) ((GlobalTheory.RowsOrb.mem_Ub X u _).1 x.2)
      · rw [fixedFrameOfWord_castSucc_eq_hyperbolic]; exact p_symm_zero (VS D) ((((x : GlobalTheory.RowsOrb.Wb X)).2 b).1)
    obtain ⟨y, ⟨w, rfl⟩, z, hz, hyz⟩ := Submodule.mem_sup.1 ((hE.2 _).1 hv)
    refine ⟨w, ?_⟩
    rw [fixedFrameOfWord_isotropicSpan_eq] at hz
    have hd : ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) - ((g w : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = 0 := by
      apply span_eq_zero X
      · rw [hg, ← hyz]
        have : (W.subtype w + z) - ((w : (VS D).V) - corr X W w) = z + corr X W w := by
          simp only [Submodule.subtype_apply]; abel
        rw [this]
        exact Submodule.add_mem _ hz (corr_mem X W w)
      · intro b
        exact ((Submodule.sub_mem _ (x : GlobalTheory.RowsOrb.Wb X).2 (g w : GlobalTheory.RowsOrb.Wb X).2) b).2
    ext
    exact (sub_eq_zero.1 hd).symm
  let e := (LinearEquiv.ofBijective g ⟨hinj, hsurj⟩).symm
  have hge : ∀ x, g (e x) = x := fun x => (LinearEquiv.ofBijective g ⟨hinj, hsurj⟩).apply_symm_apply x
  have hxe : ∀ x : GlobalTheory.RowsOrb.Ub X u, ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = ((e x : W) : (VS D).V) - corr X W (e x) := by
    intro x
    rw [← hg (e x), hge x]
  refine ⟨e, fun x y => ?_, fun x => ?_⟩
  · rw [LinearMap.flip_apply, hBW, GlobalTheory.RowsOrb.hU_apply, hxe x, hxe y]
    have h1 := (hXW (e y) (corr_mem X W (e x))).1
    have h2 := (hXW (e x) (corr_mem X W (e y))).2
    have h3 := hT_span_span X (corr_mem X W (e x)) (corr_mem X W (e y))
    simp only [map_sub, LinearMap.sub_apply, h1, h2, h3, sub_zero]
  · rw [hxe x, sub_sub_cancel, fixedFrameOfWord_isotropicSpan_eq]
    exact corr_mem X W (e x)

import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLab
import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.R3.LabCount

theorem card_filter_eq_finrank {V Q ι : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Fintype ι] [Fintype Q] [DecidableEq Q] (x : ι → V) (hx : LinearIndependent ℂ x) (lab : ι → Q)
    (P : Q → Submodule ℂ V) (hmem : ∀ k, x k ∈ P (lab k))
    (hsum : ∑ q, Module.finrank ℂ (P q) ≤ Fintype.card ι) (p : Q) :
    (Finset.univ.filter (fun k => lab k = p)).card = Module.finrank ℂ (P p) := by
  have hle : ∀ q, (Finset.univ.filter (fun k => lab k = q)).card ≤ Module.finrank ℂ (P q) := by
    intro q
    let y : {k // lab k = q} → P q := fun k => ⟨x k.1, by have h := hmem k.1; rwa [k.2] at h⟩
    have hy : LinearIndependent ℂ y := by
      apply LinearIndependent.of_comp (P q).subtype
      exact hx.comp Subtype.val Subtype.val_injective
    have := hy.fintype_card_le_finrank
    rwa [Fintype.card_subtype] at this
  have htot : ∑ q, (Finset.univ.filter (fun k => lab k = q)).card = Fintype.card ι := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (fun k _ => Finset.mem_univ (lab k))]
  by_contra hne
  have hlt : (Finset.univ.filter (fun k => lab k = p)).card < Module.finrank ℂ (P p) := lt_of_le_of_ne (hle p) hne
  have : ∑ q, (Finset.univ.filter (fun k => lab k = q)).card < ∑ q, Module.finrank ℂ (P q) :=
    Finset.sum_lt_sum (fun q _ => hle q) ⟨p, Finset.mem_univ _, hlt⟩
  omega

theorem finrank_twSub (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) :
    Module.finrank ℂ (Tw.sub s V) = Module.finrank ℂ V := by
  let j : (Tw.sub s V) ≃+ V :=
    { toFun := fun x => ⟨Tw.out x.1, x.2⟩
      invFun := fun x => ⟨Tw.mk s x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hb : Function.Bijective (cj s) :=
    Function.bijective_iff_has_inverse.2 ⟨cj s, cj_cj s, cj_cj s⟩
  have h := rank_eq_of_equiv_equiv (cj s) j hb (fun _ _ => rfl)
  unfold Module.finrank
  rw [h]

theorem twSub_inf (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V W : Submodule ℂ E) :
    Tw.sub s (V ⊓ W) = Tw.sub s V ⊓ Tw.sub s W := Submodule.ext fun _ => Iff.rfl

theorem cnt : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ cOf : D.what₂.FT → A3.fam3.base3.Ix, (∀ σ, HasLab Y σ (cOf σ)) → ∀ p : A3.fam3.base3.Ix, ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = p), D.what₂.nRows0 σ = Module.finrank D.what₂.LL ((s0Of R F).Ep p) := by
  intro hWe hDs hHC hCu D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hHo hHost cOf hLab p
  have hR := complex_data_conditions_base_level_of_primitive_links hHo.ok hHo.sep hP.char hHo.prim
  have hRow := hR.rowHyp false
  have hE : (R.toCx3 F).PartsE false := hHo.prim.sumE false
  have hinj : Function.Injective R.HE.e := hP.char.base.models.HE.1
  set L : Submodule ℂ R.HE.H := (R.toRealDat.EEat (R.toRealDat.levR F.lv2 false)).comap R.HE.e with hL
  have hpart : ∀ q, Module.finrank ℂ ((R.toCx3 F).EEp q ⊓ (R.toCx3 F).EEl false : Submodule ℂ (R.toCx3 F).EE) =
      Module.finrank ℂ (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H) := by
    intro q
    rw [← finrank_twSub (twAt D.what₂.embLL A3.A.v0) (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H), twSub_inf]
    rfl
  have hEp : Module.finrank D.what₂.LL ((s0Of R F).Ep p) = Module.finrank ℂ (R.EEp3 p ⊓ L : Submodule ℂ R.HE.H) := by
    rw [← hpart p]
    exact (R.toCx3 F).finrank_Ep F.cr false hRow.wf hRow.h2 hRow.h3 hE p
  let C := toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop
  let lf : Mult.MMap (R.MY 0) ≃ₗ[ℂ] C.Amb 0 := PiTensorProduct.lift
  let φ : R.HE.H →ₗ[ℂ] C.Amb 0 := lf.toLinearMap ∘ₗ R.HE.e
  have hφ : Function.Injective φ := lf.injective.comp hinj
  have hmemL : ∀ y : R.HE.H, φ y ∈ C.EEc false → y ∈ L := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 hy
    have : z = R.HE.e y := lf.injective hzy
    subst this
    exact hz
  choose x hxP hxe using fun k => (hLab (D.what₂.ft0 k)).2 k rfl
  have hxφ : ∀ k, φ (x k) = (Y.Iz.jE (D.what₂.onb0 k)).1 := fun k => (hxe k).symm
  have hli0 : LinearIndependent ℂ (fun k => ((Y.Iz.jE (D.what₂.onb0 k)).1 : C.Amb 0)) := by
    have h1 := D.what₂.onb0.toBasis.linearIndependent.map' Y.Iz.jE.toLinearMap Y.Iz.jE.ker
    have h2 := h1.map' (C.EEc false).subtype (Submodule.ker_subtype _)
    exact h2
  have hli : LinearIndependent ℂ x := by
    apply LinearIndependent.of_comp φ
    convert hli0 using 1
    funext k
    exact hxφ k
  have hxL : ∀ k, x k ∈ L := fun k => hmemL _ (by rw [hxφ k]; exact (Y.Iz.jE (D.what₂.onb0 k)).2)

  have hDim : Module.finrank ℂ L ≤ Fintype.card (Fin D.what₂.D0) := by
    let g0 : L →ₗ[ℂ] C.EEc false :=
      (φ.domRestrict L).codRestrict (C.EEc false) (fun y => Submodule.mem_map_of_mem (f := lf.toLinearMap) y.2)
    let g : L →ₗ[ℂ] D.what₂.EE0 := Y.Iz.jE.symm.toLinearMap ∘ₗ g0
    have hg : Function.Injective g := by
      intro a b h
      have h1 : g0 a = g0 b := Y.Iz.jE.symm.injective h
      have h2 : φ a = φ b := congrArg Subtype.val h1
      exact Subtype.ext (hφ h2)
    calc Module.finrank ℂ L ≤ Module.finrank ℂ D.what₂.EE0 := LinearMap.finrank_le_finrank_of_injective hg
      _ = Fintype.card (Fin D.what₂.D0) := Module.finrank_eq_card_basis D.what₂.onb0.toBasis
  have hsum : ∑ q, Module.finrank ℂ (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H) ≤ Fintype.card (Fin D.what₂.D0) := by
    calc ∑ q, Module.finrank ℂ (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H)
        = ∑ q, Module.finrank ℂ ((R.toCx3 F).EEp q ⊓ (R.toCx3 F).EEl false : Submodule ℂ (R.toCx3 F).EE) :=
          Finset.sum_congr rfl fun q _ => (hpart q).symm
      _ = Module.finrank ℂ (⨆ q, (R.toCx3 F).EEp q ⊓ (R.toCx3 F).EEl false : Submodule ℂ (R.toCx3 F).EE) :=
          (Formalism.IndefR.Cx.finrank_iSup_eq_sum _ (CxData.indep_of_orth _ hE.1)).symm
      _ ≤ Module.finrank ℂ ((R.toCx3 F).EEl false) := Submodule.finrank_mono (iSup_le fun q => inf_le_right)
      _ = Module.finrank ℂ L := finrank_twSub _ L
      _ ≤ Fintype.card (Fin D.what₂.D0) := hDim
  have hcard := card_filter_eq_finrank x hli (fun k => cOf (D.what₂.ft0 k)) (fun q => (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H))
    (fun k => ⟨hxP k, hxL k⟩) hsum p
  have hcount : ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = p), D.what₂.nRows0 σ =
      (Finset.univ.filter (fun k => cOf (D.what₂.ft0 k) = p)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := D.what₂.ft0) (t := Finset.univ.filter (fun σ => cOf σ = p))
      (fun k hk => by simpa using hk)]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [Finset.mem_filter] at hσ
    rw [Formalism.BasicNotions.Rows.Data.nRows0, Fintype.card_subtype, Finset.filter_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ hσ.2, h⟩
    · intro h; exact h.2
  rw [hEp, ← hcard]
  exact hcount

end GlobalTheory.Mem.R3.LabCount

end

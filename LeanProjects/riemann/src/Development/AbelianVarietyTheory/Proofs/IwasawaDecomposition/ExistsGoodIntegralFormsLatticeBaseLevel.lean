import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanGoodEqMj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LMLatOfLIntegral

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.GoodLatFree

theorem mem_of_span {S V H : Type} [Semiring S] [AddCommGroup V] [Module S V] [AddCommGroup H] [Module ℂ H]
    (f : V →+ H) (τ : S → ℂ) (hfs : ∀ (b : S) (x : V), f (b • x) = τ b • f x) (P : Submodule ℂ H) (X : Set V)
    (hX : ∀ x ∈ X, f x ∈ P) : ∀ v ∈ Submodule.span S X, f v ∈ P := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hX x hx
  | zero => rw [map_zero]; exact P.zero_mem
  | add _ _ _ _ h1 h2 => rw [map_add]; exact P.add_mem h1 h2
  | smul b x _ h => rw [hfs]; exact P.smul_mem _ h

theorem int_span {L V H : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup H] [Module ℂ H] {σ : L →+* ℂ}
    {iZ : Module ℤ V} (j : V →ₛₗ[σ] H) (X : Set V) (P : Submodule ℂ H) (hX : ∀ x ∈ X, j x ∈ P) :
    ∀ v ∈ @Submodule.span ℤ V _ _ iZ X, j v ∈ P := by
  obtain rfl : iZ = AddCommGroup.toIntModule V := Subsingleton.elim _ _
  exact mem_of_span j.toAddMonoidHom (fun n : ℤ => (n : ℂ)) (fun n x => by
    show j (n • x) = (n : ℂ) • j x
    rw [map_zsmul, Int.cast_smul_eq_zsmul]) P X hX

theorem ring_span {L V H : Type} [Field L] [NumberField L] [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
    [IsScalarTower (𝓞 L) L V] [AddCommGroup H] [Module ℂ H] {σ : L →+* ℂ}
    (j : V →ₛₗ[σ] H) (X : Set V) (P : Submodule ℂ H) (hX : ∀ x ∈ X, j x ∈ P) : ∀ v ∈ Submodule.span (𝓞 L) X, j v ∈ P :=
  mem_of_span j.toAddMonoidHom (fun a : 𝓞 L => σ (a : L)) (fun a x => by
    show j (a • x) = σ (a : L) • j x
    rw [← algebraMap_smul L a x, map_smulₛₗ]) P X hX

theorem field_span {L V H : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup H] [Module ℂ H] {σ : L →+* ℂ}
    (j : V →ₛₗ[σ] H) (X : Set V) (P : Submodule ℂ H) (hX : ∀ x ∈ X, j x ∈ P) : ∀ v ∈ Submodule.span L X, j v ∈ P :=
  mem_of_span j.toAddMonoidHom (fun a : L => σ a) (fun a x => j.map_smulₛₗ a x) P X hX

theorem chiKs_of_pins : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ i : Fin D.R.m, (R.FW i).ChiKs := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH i g
  have hL := hP.char.base.lev
  have h : ((Formalism.IndefR.FWT.chiC R.toRealDat i g : ℂˣ) : ℂ) ∈ (D.what₂.embLL.comp (algebraMap Ks D.what₂.LL)).fieldRange := by
    unfold Formalism.IndefR.FWT.chiC
    rw [Units.coe_prod]
    refine prod_mem fun PP _ => ?_
    refine GlobalTheory.ChiDetValues.res_mem _ _ _ (hL.mu0 i) (fun x hx => ?_) _ _ (hL.chi i _ PP.2) _
    obtain ⟨y, hy⟩ := hP.keep.valKs i x hx
    exact ⟨y, hy.symm⟩
  obtain ⟨y, hy⟩ := h
  exact ⟨y, D.what₂.embLL.injective (hy.trans ((Units.coe_prod _ _).trans (hP.char.base.grp.chiW i g).symm))⟩

set_option maxHeartbeats 2000000 in

theorem exists_oLat_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (E : M →ₗ[ℂ] (R.toRealDat.HW i (sg0 D A3.A)).H), Function.Injective E → LinearMap.range E = (R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap (R.toRealDat.HW i (sg0 D A3.A)).e → ∃ L : Rows.OLat D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) M, ∀ x, x ∈ L.carrier ↔ ∃ v ∈ (R.toRealDat.FW i).MK, v ∈ (R.toRealDat.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) ∧ E x = (R.toRealDat.FW i).j (sg0 D A3.A) v := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hO _ hP hH i M _ _ _ E hinj hrange
  classical
  have hI := hH.aux.integral i
  have hχ := chiKs_of_pins D G Pl0 I0 T A3 Ks R F cG hP hH i
  have hspan := GlobalTheory.GoodLatDescent.span_MK_good (R.FW i) hI.1 (fun g f => (hI.2.2 g f).1) hχ F.lv2.P0 F.lv2.ψ0⁻¹
    (fun g => (idemOf A3.A.X).coeff g) (fun p => ?_) hP.keep.levKs.2
  swap
  · obtain ⟨y, hy⟩ := hP.keep.levKs.1 p
    exact ⟨y⁻¹, by rw [map_inv₀, hy, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]⟩
  have hsa : ∀ a, sg0 D A3.A a = D.what₂.embLL a := fun a => by rw [sg0, sgAt_mk _ R.hv0]

  obtain ⟨S0, hS0⟩ := GlobalTheory.GoodLatDescent.fg_MK_good (R.FW i) hI.2.1 F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)
  have hfg : ((Submodule.span (𝓞 Ks) (S0 : Set (Fin (R.nW i) → D.what₂.LL))).restrictScalars ℤ).FG :=
    Submodule.FG.restrictScalars ⟨S0, rfl⟩
  obtain ⟨T0, hT0⟩ := hfg
  have hT : ∀ y, y ∈ Submodule.span ℤ (T0 : Set (Fin (R.nW i) → D.what₂.LL)) ↔
      y ∈ (R.FW i).MK ∧ y ∈ (R.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) := by
    intro y
    rw [hT0]
    show y ∈ ((Submodule.span (𝓞 Ks) (S0 : Set (Fin (R.nW i) → D.what₂.LL))) : Set _) ↔ _
    rw [hS0]; rfl

  have hWS : LinearMap.range E = R.toRealDat.WS F.lv2 false i (sg0 D A3.A) := by
    rw [hrange]; exact (hH.aux.levelW false i _).symm
  have hjW : ∀ y ∈ (R.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g),
      (R.FW i).j (sg0 D A3.A) y ∈ LinearMap.range E := by
    intro y hy
    rw [hWS, ← GlobalTheory.Mem.LiftTheta.goodForm_span R.toRealDat F.lv2 false i]
    have hyW : y ∈ R.toRealDat.WL F.lv2 false i := hy
    have hs : ∑ k, (Module.finBasis D.what₂.LL (R.toRealDat.WL F.lv2 false i)).repr ⟨y, hyW⟩ k •
        R.toRealDat.bL F.lv2 false i k = y := by
      have h := congrArg (R.toRealDat.WL F.lv2 false i).subtype
        ((Module.finBasis D.what₂.LL (R.toRealDat.WL F.lv2 false i)).sum_repr ⟨y, hyW⟩)
      rw [map_sum] at h
      exact h
    rw [← hs, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smulₛₗ, ← GlobalTheory.Mem.LiftTheta.goodForm_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

  have hex : ∀ t, ∃ x : M, t ∈ T0 → E x = (R.FW i).j (sg0 D A3.A) t := by
    intro t
    by_cases ht : t ∈ T0
    · obtain ⟨x, hx⟩ := hjW t ((hT t).1 (Submodule.subset_span (Finset.mem_coe.2 ht))).2
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose g hg using hex

  have hA : ∀ y, y ∈ (R.FW i).MK ∧ y ∈ (R.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) →
      (R.FW i).j (sg0 D A3.A) y ∈ Submodule.span ℂ ((R.FW i).j (sg0 D A3.A) '' (T0 : Set _)) := by
    intro y hy
    have h1 : y ∈ Submodule.span ℤ (T0 : Set (Fin (R.nW i) → D.what₂.LL)) := (hT y).2 hy
    have h2 : ∀ x ∈ (T0 : Set (Fin (R.nW i) → D.what₂.LL)), (R.FW i).j (sg0 D A3.A) x ∈
        Submodule.span ℂ ((R.FW i).j (sg0 D A3.A) '' (T0 : Set _)) :=
      fun x hx => Submodule.subset_span (Set.mem_image_of_mem _ hx)
    have h1' : y ∈ @Submodule.span ℤ (Fin (R.nW i) → D.what₂.LL) _ _ (AddCommGroup.toIntModule _) (T0 : Set (Fin (R.nW i) → D.what₂.LL)) := by
      convert h1
    have h3 := int_span (L := D.what₂.LL) (V := Fin (R.nW i) → D.what₂.LL) (iZ := AddCommGroup.toIntModule _) ((R.FW i).j (sg0 D A3.A)) (T0 : Set _) _ h2
    exact h3 y h1'
  have hB : ∀ y ∈ (R.FW i).Mj F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g),
      (R.FW i).j (sg0 D A3.A) y ∈ Submodule.span ℂ ((R.FW i).j (sg0 D A3.A) '' (T0 : Set _)) := by
    intro y hy
    rw [← hspan] at hy
    exact ring_span ((R.FW i).j (sg0 D A3.A)) _ _ (fun x hx => hA x hx) y hy
  have hC : ∀ y ∈ (R.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g),
      (R.FW i).j (sg0 D A3.A) y ∈ Submodule.span ℂ ((R.FW i).j (sg0 D A3.A) '' (T0 : Set _)) := by
    intro y hy
    rw [← (GlobalTheory.GoodLat.mj_full (R.FW i) hI.1 hI.2.1 F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)).2] at hy
    exact field_span ((R.FW i).j (sg0 D A3.A)) _ _ (fun x hx => hB x hx) y hy
  have hgen : Submodule.span ℂ ((T0.image g : Finset M) : Set M) = ⊤ := by
    apply Submodule.map_injective_of_injective hinj
    rw [Submodule.map_top, Submodule.map_span, Finset.coe_image, Set.image_image]
    have him : (fun t => E (g t)) '' (T0 : Set _) = (R.FW i).j (sg0 D A3.A) '' (T0 : Set _) :=
      Set.image_congr fun t ht => hg t ht
    rw [him]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨t, ht, rfl⟩
      exact hjW t ((hT t).1 (Submodule.subset_span ht)).2
    · rw [hWS, ← GlobalTheory.Mem.LiftTheta.goodForm_span R.toRealDat F.lv2 false i, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe]
      beta_reduce
      rw [GlobalTheory.Mem.LiftTheta.goodForm_single]
      exact hC _ (Module.finBasis D.what₂.LL (R.toRealDat.WL F.lv2 false i) k).2
  refine ⟨⟨T0.image g, hgen⟩, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨c, rfl⟩
    rw [map_sum]
    refine Finset.sum_induction _
      (fun w => ∃ v ∈ (R.FW i).MK, v ∈ (R.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) ∧
        w = (R.FW i).j (sg0 D A3.A) v) ?_ ?_ ?_
    · rintro _ _ ⟨v1, h1, h1', rfl⟩ ⟨v2, h2, h2', rfl⟩
      exact ⟨v1 + v2, Submodule.add_mem _ h1 h2, Submodule.add_mem _ h1' h2', (map_add _ _ _).symm⟩
    · exact ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, (map_zero _).symm⟩
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
      have htg := (hT t).1 (Submodule.subset_span (Finset.mem_coe.2 ht))
      obtain ⟨k, hk⟩ := hO (c (g t))
      have hint : IsIntegral ℤ k := by
        have h1 : IsIntegral ℤ (D.what₂.OtoLL (c (g t))) := D.O_int (c (g t))
        rw [← hk] at h1
        exact (isIntegral_algHom_iff (algebraMap Ks D.what₂.LL).toIntAlgHom (algebraMap Ks D.what₂.LL).injective).1 h1
      let kk : 𝓞 Ks := ⟨k, hint⟩
      have hkk : D.what₂.OtoLL (c (g t)) • t = kk • t := by
        rw [← hk, algebraMap_smul, ← algebraMap_smul Ks kk t]
        rfl
      refine ⟨D.what₂.OtoLL (c (g t)) • t, ?_, Submodule.smul_mem _ _ htg.2, ?_⟩
      · rw [hkk]; exact Submodule.smul_mem _ _ htg.1
      · rw [map_smul, hg t ht, map_smulₛₗ, hsa]
        rfl
  · rintro ⟨v, hv1, hv2, hxv⟩
    obtain ⟨n, -, hn⟩ := Submodule.mem_span_finset.1 ((hT v).2 ⟨hv1, hv2⟩)
    have hx : x = ∑ t ∈ T0, ((n t : ℤ) : ℂ) • g t := by
      apply hinj
      rw [hxv, ← hn, map_sum, map_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [map_zsmul, map_smul, hg t ht, Int.cast_smul_eq_zsmul]
    refine ⟨fun y => ∑ t ∈ T0 with g t = y, (n t : D.what₂.O), ?_⟩
    rw [hx]
    symm
    refine Finset.sum_image' _ fun t _ => ?_
    rw [map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun t' ht' => ?_
    rw [(Finset.mem_filter.1 ht').2, map_intCast]

end GlobalTheory.Mem.GoodLatFree

import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMapHilbertModelEqConcreteThetaMapFamilyThreStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelFormOrthogonalKilledByThetaMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCuspFormSpaceThetaMapEqDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.PartSpan

theorem mem_span_rat {K V E : Type} [Field K] [AddCommGroup V] [Module ℂ V] [AddCommGroup E] [Module ℂ E]
    {τ : K →+* ℂ} {n : ℕ} (u : (Fin n → K) →ₛₗ[τ] V) (Φ : V →ₗ[ℂ] E) (P : Submodule ℂ E)
    (hinj : ∀ c : Fin n → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) = 0 → c = 0)
    (hspan : ∀ c : Fin n → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) ∈ P →
      Φ (∑ k, c k • u (Pi.single k 1)) ∈ Submodule.span ℂ (Φ '' {y | ∃ a, Φ (u a) ∈ P ∧ u a = y}))
    (x : V) (hx : x ∈ Submodule.span ℂ (Set.range u)) (hP : Φ x ∈ P) :
    x ∈ Submodule.span ℂ {y | ∃ a, Φ (u a) ∈ P ∧ u a = y} := by
  have hexp : ∀ a : Fin n → K, u a = ∑ k, τ (a k) • u (Pi.single k 1) := by
    intro a
    have ha : a = ∑ k, a k • (Pi.single k 1 : Fin n → K) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [ha]
    simp only [map_sum, map_smulₛₗ]
  have hsp : ∀ z ∈ Submodule.span ℂ (Set.range u), ∃ c : Fin n → ℂ, z = ∑ k, c k • u (Pi.single k 1) := by
    intro z hz
    have hle : Submodule.span ℂ (Set.range u) ≤ Submodule.span ℂ (Set.range fun k => u (Pi.single k 1)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, hexp]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hle hz)
    exact ⟨c, hc.symm⟩
  obtain ⟨c, rfl⟩ := hsp x hx
  have h1 := hspan c hP
  rw [← Submodule.map_span] at h1
  obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.1 h1
  have hsS : Submodule.span ℂ {y | ∃ a, Φ (u a) ∈ P ∧ u a = y} ≤ Submodule.span ℂ (Set.range u) :=
    Submodule.span_mono (by rintro _ ⟨a, -, rfl⟩; exact ⟨a, rfl⟩)
  obtain ⟨d, rfl⟩ := hsp w (hsS hw)
  have hcd : c - d = 0 := by
    apply hinj
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, map_sub, hwe, sub_self]
  rw [sub_eq_zero.1 hcd]
  exact hw

set_option maxHeartbeats 4000000 in

theorem mem_span_part : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix), ∀ x ∈ Submodule.span ℂ (Set.range fun a => D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x) ∈ R.Wp3 i p → x ∈ Submodule.span ℂ {y | ∃ a, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p ∧ D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)) = y} := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t p x hx hW
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hOk := hH.ok.ok2
  have e1 := GlobalTheory.T.thetaMap_hilbertModel_eq_concreteThetaMap_familyThree D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t
  have h5 := hR.lifts0.1
  let Φ : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A3.A)).H :=
    (Y.mj.eW i).comp (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1))
  let u := ((D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)).comp (Y.eMt i t).toLinearMap).comp
    (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVecLin
  let m : (R.HW i (sg0 D A3.A)).H →ₛₗ[cj (twAt D.what₂.embLL A3.A.v0)] (R.toCx3 F).W i := Tw.mkL (twAt D.what₂.embLL A3.A.v0) _
  have hcon : ∀ a, m (Φ (u a)) =
      (R.toCx3 F).tC F.cr false i t (cpt A3.fam3.base3.v0.embedding a) := by
    intro a
    refine Eq.trans ?_ ((R.toCx3 F).tC_cpt_eq F.cr false i t a).symm
    show Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)
        (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))))) =
      R.phs i • Tw.map _ (R.thG i t) (Tw.semi _ R.toRealDat.emb0 (R.jV i t) (F.cr.toL (R.toCx3 F).zs false i t a))
    have h3' : F.cr.toL (R.toCx3 F).zs false i t a =
        LiftForms.lvlForm (A3.A.fam.L i t).S (A3.A.fam.L i t).r (A3.A.fam.lvlA F.P0 F.ψ0).P (A3.A.fam.lvlA F.P0 F.ψ0).ψ
          (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a) :=
      (GlobalTheory.Mem.LiftTheta.levelFormCoordinateMap_levelZero F.lv2 hOk (A3.fam3.toSub2 (zsOf R F)) i t a).symm
    rw [hP.phs i, one_smul, e1, h3']
    rfl

  have hsing : ∀ k : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)),
      cpt A3.fam3.base3.v0.embedding (Pi.single k (1 : D.what₂.LL)) = Pi.single k 1 := by
    intro k
    funext j
    by_cases h : j = k
    · subst h; simp [cpt]
    · simp [cpt, Pi.single_apply, h]
  have hsum : ∀ c : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) → ℂ, m (Φ (∑ k, c k • u (Pi.single k 1))) =
      (R.toCx3 F).tC F.cr false i t (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k)) := by
    intro c
    have hc : (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k)) =
        ∑ k, cj (twAt D.what₂.embLL A3.A.v0) (c k) • (Pi.single k 1 : Fin _ → ℂ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    refine Eq.trans ?_ (congrArg ((R.toCx3 F).tC F.cr false i t) hc).symm
    rw [map_sum, map_sum]
    refine Eq.trans ?_ (map_sum ((R.toCx3 F).tC F.cr false i t) (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k) • (Pi.single k 1 : Fin _ → ℂ)) Finset.univ).symm
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smulₛₗ]
    refine Eq.trans ?_ (map_smul ((R.toCx3 F).tC F.cr false i t) _ _).symm
    exact congrArg (fun z => cj (twAt D.what₂.embLL A3.A.v0) (c k) • z)
      ((hcon (Pi.single k 1)).trans (congrArg ((R.toCx3 F).tC F.cr false i t) (hsing k)))

  have hinj : ∀ c : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) = 0 → c = 0 := by
    intro c hc
    have h0 : (R.toCx3 F).tC F.cr false i t (fun k => cj (twAt D.what₂.embLL A3.A.v0) (c k)) =
        0 := by
      rw [← hsum c]
      show Tw.mk _ (Φ _) = 0
      rw [hc]
      rfl
    have h1 := (h5 i t).1 (h0.trans (map_zero _).symm)
    funext k
    have hk := congrArg (cj (twAt D.what₂.embLL A3.A.v0)) (congrFun h1 k)
    rw [Links.cj_cj] at hk
    exact hk.trans (map_zero (cj (twAt D.what₂.embLL A3.A.v0)))
  have hw0 := (R.toCx3 F).principal_form_injective false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) i
  have hC : (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≤
      Submodule.span ℂ (m '' (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y})) := by
    have hSpW : Submodule.span ℂ (m '' (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y})) ≤
        (R.toCx3 F).Wp i p := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩
      exact ha
    have hle := finrank_le_cpt A3.fam3.base3.v0.embedding ((R.toCx3 F).w0C false i) hw0
      (Submodule.span ℂ (m '' (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y})))
      ((R.toCx3 F).WpK false i p) (fun y hy => by
        obtain ⟨a, rfl⟩ := ((R.toCx3 F).liftMat_bij F.cr false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) h5 hR.ratTh i t).2 y
        have hk := (R.toCx3 F).key_lift F.cr false h5 hR.ratTh i t a
        have hy' : (R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding ((R.toCx3 F).liftMat F.cr false i t *ᵥ a)) ∈
            (R.toCx3 F).Wp i p := hy
        rw [hk, ← hcon a] at hy'
        rw [hk, ← hcon a]
        exact Submodule.subset_span ⟨Φ (u a), ⟨u a, ⟨a, hy', rfl⟩, rfl⟩, rfl⟩)
    rw [(R.toCx3 F).finrank_WpK F.cr false hR.h4pos hR.kForm hR.ewNorm hR.types0 h5 hR.ratTh hR.liftHyp0.h3W hR.partsW i p] at hle
    have heq := Submodule.eq_of_le_of_finrank_le (inf_le_inf_right _ hSpW) hle
    exact heq.symm.le.trans inf_le_left
  have hspan : ∀ c : Fin ((A3.A.fam.L i t).dZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) → ℂ, Φ (∑ k, c k • u (Pi.single k 1)) ∈ R.Wp3 i p →
      Φ (∑ k, c k • u (Pi.single k 1)) ∈ Submodule.span ℂ (Φ '' {y | ∃ a, Φ (u a) ∈ R.Wp3 i p ∧ u a = y}) := by
    intro c hc
    have hm : m (Φ (∑ k, c k • u (Pi.single k 1))) ∈
        (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) := by
      refine ⟨hc, ?_⟩
      rw [← (h5 i t).2]
      exact ⟨_, (hsum c).symm⟩
    have h1 := hC hm
    rw [← Submodule.map_span] at h1
    obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.1 h1
    have hwe' : w = Φ (∑ k, c k • u (Pi.single k 1)) := hwe
    rw [← hwe']
    exact hw
  exact mem_span_rat u Φ (R.Wp3 i p) hinj hspan x hx hW

end GlobalTheory.Mem.R3.PartSpan

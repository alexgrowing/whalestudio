import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeakStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CarriedPartEigensystemPassageOfTypeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodProjectorUnitaryFormsModelLaws
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBaseLevelVectorInGoodAlgebraicFormsSpanStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemISupTypePartsOfGoodBaseFormsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.Back

theorem exists_level_vec_in_parts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → (R.toCx3 F).PartsW false → ∀ j c, R.Wc' j c ≠ ⊥ → ∃ w ∈ R.Wc' j c, w ≠ 0 ∧ w ∈ ⨆ p, R.Wp3 j p := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hCW hEx hSch s hOk hGG hLU hParts j c h0
  obtain ⟨w, hw, hw0, hws⟩ := GlobalTheory.T.exists_baseLevel_vector_in_goodAlgebraicForms_span R F hCW hEx hSch s hOk hGG hLU j c h0
  exact ⟨w, hw, hw0, GlobalTheory.T.mem_iSup_type_parts_of_good_base_forms R F hParts j w hws⟩

theorem blockProd_ne_zero {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (P : B.Pl) : B.blockProd P ≠ 0 := by
  unfold BlockDat.blockProd
  rw [ne_eq, List.prod_eq_zero_iff]
  simp only [List.mem_map, not_exists, not_and]
  intro ν _ h
  unfold Formalism.L2.Col.blockPoly at h
  rw [Finset.prod_eq_zero_iff] at h
  obtain ⟨c, _, hc⟩ := h
  have := congrArg (fun q => Polynomial.coeff q 0) hc
  simp at this

theorem eig_in_sum {H : Type} [AddCommGroup H] [Module ℂ H] [FiniteDimensional ℂ H] {Q J K : Type} (ok : Q → Prop)
    (h : Q → J → Module.End ℂ H) (ev : K → Q → J → ℂ) (V : K → Submodule ℂ H) (S : K → Prop) (k0 : K)
    (hc : ∀ P P', ok P → ok P' → ∀ c c', Commute (h P c) (h P' c'))
    (hev : ∀ k P, ok P → ∀ cc, ∀ x ∈ V k, h P cc x = ev k P cc • x)
    (w : H) (hw : w ∈ V k0) (hw0 : w ≠ 0) (hwS : w ∈ ⨆ (k : K) (_ : S k), V k) :
    ∃ k, S k ∧ ∀ P, ok P → ∀ cc, ev k P cc = ev k0 P cc := by
  classical
  let op : {P // ok P} × J → Module.End ℂ H := fun i => h i.1.1 i.2
  have hpc : Formalism.L2.Col.PairComm op := fun i i' => hc _ _ i.1.2 i'.1.2 _ _
  let χ : K → {P // ok P} × J → ℂ := fun k i => ev k i.1.1 i.2
  have hV : ∀ k, V k ≤ Formalism.L2.Col.eigAt op (χ k) := fun k x hx =>
    Formalism.L2.Col.mem_eigAt_of_forall_apply fun i => hev k i.1.1 i.1.2 i.2 x hx
  by_contra hne
  push_neg at hne
  have h1 : (⨆ (k : K) (_ : S k), V k) ≤ Formalism.L2.Col.eigSum op (fun x => x ≠ χ k0) := by
    refine iSup₂_le fun k hk => (hV k).trans (Formalism.L2.Col.eigAt_le_eigSum ?_)
    intro he
    obtain ⟨P, hP, cc, hcc⟩ := hne k hk
    exact hcc (congrFun he (⟨P, hP⟩, cc))
  have h2 : V k0 ≤ Formalism.L2.Col.eigSum op (fun x => x = χ k0) :=
    (hV k0).trans (Formalism.L2.Col.eigAt_le_eigSum rfl)
  have hd := Formalism.L2.Col.disjoint_eigSum (op := op) hpc (C := fun x => x = χ k0) (C' := fun x => x ≠ χ k0)
    (fun x h h' => h' h)
  exact hw0 ((Submodule.disjoint_def.1 hd) w (h2 hw) (h1 hwS))

theorem types_eq {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} (hSep : A3.fam3.TypesSep3) (j : Fin D.R.m)
    (p p' : A3.fam3.base3.Ix) (y : (A3.liftI j A3.A.μ0).OpIx → ℂ)
    (hp : cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) y)
    (hp' : cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p'.1)) y) : p = p' := by
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨x', hx', hxx⟩ := hp'
  have hxe : x = x' := funext fun i => D.what₂.embLL.injective (congrFun hxx i)
  subst hxe
  by_contra hne
  have hne' : p.1 ≠ p'.1 := fun h => hne (Subtype.ext h)
  rcases hSep p.1 p.2 p'.1 p'.2 hne' j with ⟨P, hP⟩ | ⟨k, hk⟩
  · apply hP
    have h1 := hx.1 P
    have h2 := hx'.1 P
    rw [h1] at h2
    exact mul_right_cancel₀ (blockProd_ne_zero _ P) h2
  · exact hk ((hx.2 k).symm.trans (hx'.2 k))

theorem wc_le_wp_of_passage : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.TrISem F A3.trI → (R.toCx3 F).PartsW false → A3.fam3.TypesSep3 → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ (p : A3.fam3.base3.Ix) c, cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) (labW j pl cW c) → R.Wc' j c ≤ R.Wp3 j p := by
  intro hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hLI hCW hEx hSch hJunk s hOk hGG hLU hPGU hPGE hPLW hA hPos hB hTr hParts hSep j pl cV cW hLD p c hsys
  obtain ⟨hcoreF, hSF, -, -, -, hWeq, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hCW
  have hcore := hcoreF hEx
  obtain ⟨h, -, hNorm, -, hsum, -, hev, hchar⟩ :=
    GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hcore hSch hOk.ok2.irr R.SF hSF j
  have hidem := (eH_laws R.toRealDat F.lv2 hcore hOk.ok2.irr j).1
  by_cases h0 : R.Wc' j c = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨w, hwc, hw0, hwp⟩ := exists_level_vec_in_parts R F hCW hEx hSch s hOk hGG hLU hParts j c h0
  have hwp' : w ∈ ⨆ (c' : Pl D.host.E → List ℤ → ℂ) (_ : ∃ p', R.Carries p' c'), Wcc R.toRealDat R.SF j c' := by
    have hle : (⨆ p, R.Wp3 j p) ≤
        ⨆ (c' : Pl D.host.E → List ℤ → ℂ) (_ : ∃ p', R.Carries p' c'), Wcc R.toRealDat R.SF j c' := by
      refine iSup_le fun p' => iSup₂_le fun c' hc' => ?_
      rw [hWeq]
      exact le_iSup₂_of_le (f := fun c' (_ : ∃ p', R.Carries p' c') => Wcc R.toRealDat R.SF j c') c' ⟨p', hc'⟩ le_rfl
    exact hle hwp
  rw [hWeq] at hwc
  obtain ⟨c', ⟨p', hcar⟩, hag⟩ := eig_in_sum (Good R.toRealDat A3.A.μ0) h
    (fun c P cc => evC (Wc D j) P (c P) cc) (Wcc R.toRealDat R.SF j) (fun c' => ∃ p', R.Carries p' c') c hNorm.1
    (fun k P hP cc x hx => hev k P hP cc x hx) w hwc hw0 hwp'
  have hsub : Wcc R.toRealDat R.SF j c ≤ Wcc R.toRealDat R.SF j c' := by
    intro x hx
    refine hchar c' x ?_ ?_
    · have hr : x ∈ LinearMap.range (eH R.toRealDat j) := hsum ▸ (le_iSup (Wcc R.toRealDat R.SF j) c hx)
      obtain ⟨y, rfl⟩ := hr
      rw [← Module.End.mul_apply, hidem]
    · intro P d hP hd
      rw [hev c P hP _ x hx, ← hag P hP]
      simp [evC, hd]
  have hne : R.Wc' j c' ≠ ⊥ := by
    rw [hWeq]
    intro hb
    exact hw0 ((Submodule.eq_bot_iff _).1 hb w (hsub hwc))
  have hfwd := GlobalTheory.T.carriedPart_eigensystem_passage_of_type hHowe R F hLI hCW hEx hSch hJunk s hOk hGG hLU hPGU hPGE hPLW hA hPos hB hTr j pl cV cW hLD p' c' hcar hne
  have hlab : labW j pl cW c' = labW j pl cW c := funext fun i => hag (pl i) (hLD.good i) (cW i)
  rw [hlab] at hfwd
  have hpp : p' = p := types_eq hSep j p' p _ hfwd hsys
  subst hpp
  rw [hWeq]
  refine hsub.trans ?_
  rw [← hWeq]
  exact le_iSup₂_of_le (f := fun c (_ : R.Carries p' c) => R.Wc' j c) c' hcar le_rfl

end GlobalTheory.Hk3.Back

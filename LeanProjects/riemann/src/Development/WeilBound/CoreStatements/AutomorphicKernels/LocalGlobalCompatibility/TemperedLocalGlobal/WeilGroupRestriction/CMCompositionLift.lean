import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.UnitaryBC GlobalTheory.HeckeGal Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N
open PositivityTheory.Pf1.CLGD.DescRes

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.CLGD.K

namespace CMCompositionLift

abbrev cmComp {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (X : CMExt E Ω) (Y : CMExt X.M Ω) : CMExt E Ω :=
  letI : Algebra E Y.M := ((algebraMap X.M Y.M).comp (algebraMap E X.M)).toAlgebra
  { M := Y.M
    tower := IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply E X.M Ω x, IsScalarTower.algebraMap_apply X.M Y.M Ω]
      rfl }

theorem resG_comp {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (X : CMExt E Ω) (Y : CMExt X.M Ω)
    (g : G (cmComp X Y).M Ω) :
    resG E (E' := (cmComp X Y).M) (Ω := Ω) g = resG E (E' := X.M) (Ω := Ω) (resG X.M (E' := Y.M) (Ω := Ω) g) := by
  ext x
  rfl

theorem resW_comp {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (X : CMExt E Ω) (Y : CMExt X.M Ω) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {w' : HeightOneSpectrum (𝓞 X.M)} {w'' : HeightOneSpectrum (𝓞 (cmComp X Y).M)}
    (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (h'' : IsPlaceOver A w'') :
    resW (E' := (cmComp X Y).M) h h'' = (resW h h').comp (resW (E := X.M) (E' := Y.M) h' h'') :=
  MonoidHom.ext fun _ => Subtype.ext (AlgEquiv.ext fun _ => rfl)

theorem isLift_comp (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) {E Ω : Type} [Field E] [NumberField E] [IsCMField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {a : ℕ} (ha : 1 ≤ a) {X : CMExt E Ω} {Y : CMExt X.M Ω}
    {π : CuspSub E a} {P : CuspSub X.M a} {P₂ : CuspSub Y.M a}
    (h₁ : IsLift Ω X π P) (h₂ : IsLift Ω Y P P₂) : IsLift Ω (cmComp X Y) π P₂ := by
  refine ⟨h₂.csd, h₂.reg, ?_⟩
  intro l _ ι r wt HT r₂ wt₂ HT₂ hr hr₂
  obtain ⟨r₁, wt₁, HT₁, hr₁⟩ := hG.of_isCsd Ω ι ha h₁.reg h₁.csd
  obtain ⟨p₁, hp₁⟩ := h₁.res l ι r wt HT r₁ wt₁ HT₁ hr hr₁
  obtain ⟨p₂, hp₂⟩ := h₂.res l ι r₁ wt₁ HT₁ r₂ wt₂ HT₂ hr₁ hr₂
  refine ⟨p₂ * p₁, fun g => ?_⟩
  rw [hp₂ g, hp₁, resG_comp X Y g]
  simp only [mul_inv_rev, mul_assoc]

end CMCompositionLift

open CMCompositionLift in
theorem cm_composition_lift_holds : WeakLiftRestriction := by
  intro hG hFS hFSp hK2c hK3a hT E Ω _ _ _ _ _ _ a ha π hc hreg A w h U hU
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  induction hU with
  | top =>
    obtain ⟨r, wt, HT, hr⟩ := hG.of_isCsd Ω ι ha hreg hc
    obtain ⟨N, hN, hNo, hTr⟩ := hK3a E Ω 2 a ha r hr.cont
    obtain ⟨H, hgood, hHN, hDec, hsp⟩ := hFSp E Ω A w h N hN hNo
    obtain ⟨X, P, hXr, hXl⟩ := hT E Ω a ha π hc hreg 2 ι r wt HT hr H hgood (hTr H hHN)
    obtain ⟨w', h', -, -, hW⟩ := hK2c E Ω A w h X
    refine ⟨X, P, w', h', ?_, hsp X hXr w' h', hXl⟩
    rw [eq_top_iff]
    intro σ _
    rw [hW, hXr]
    obtain ⟨a', b', hσ⟩ := σ.2
    exact hDec hσ.1
  | @step U V _ hVU hn hp hs ih =>
    obtain ⟨X, P, w', h', hXr, hsp, hXl⟩ := ih
    obtain ⟨r₁, wt₁, HT₁, hr₁⟩ := hG.of_isCsd Ω ι ha hXl.reg hXl.csd
    obtain ⟨N, hN, hNo, hTr⟩ := hK3a X.M Ω 2 a ha r₁ hr₁.cont
    have hVn : (V.comap (resW h h')).Normal := ⟨fun n hn0 g => by
      have hn0' : resW h h' n ∈ V := hn0
      have hgU : resW h h' g ∈ U := by rw [← hXr]; exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
      have key := hn.conj_mem (⟨resW h h' n, hVU hn0'⟩ : U) (Subgroup.mem_subgroupOf.mpr hn0')
        (⟨resW h h' g, hgU⟩ : U)
      rw [Subgroup.mem_subgroupOf] at key
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      simpa using key⟩
    have hVi : (V.comap (resW h h')).index.Prime := by
      rw [Subgroup.index_comap, hXr]; exact hp
    have hVs : SmoothSub (V.comap (resW h h')) := by
      obtain ⟨O, hO, hOV⟩ := hs
      refine ⟨O.comap (resG E), continuous_resG.isOpen_preimage (O : Set (G E Ω)) hO, fun σ hσ hσO => ?_⟩
      rw [Subgroup.mem_comap]
      apply hOV
      · rw [deg_resW, hσ, mul_zero]
      · exact hσO
    obtain ⟨H, hgood, hHN, hiff⟩ := hFS X.M Ω A w' h' hsp (V.comap (resW h h')) hVn hVi hVs N hN hNo
    obtain ⟨Y, P₂, hYr, hYl⟩ := hT X.M Ω a ha P hXl.csd hXl.reg 2 ι r₁ wt₁ HT₁ hr₁ H hgood (hTr H hHN)
    obtain ⟨w'', h'', hsp', -, hW⟩ := hK2c X.M Ω A w' h' Y
    have hR : (resW h' h'').range = V.comap (resW h h') := by
      ext σ
      rw [hW, hYr, hiff]
    refine ⟨cmComp X Y, P₂, w'', h'', ?_, hsp' hsp, isLift_comp hG ha hXl hYl⟩
    rw [resW_comp X Y h h' h'', MonoidHom.range_comp, hR, Subgroup.map_comap_eq, hXr, inf_of_le_right hVU]

end PositivityTheory.Pf1.CLGD.K

end

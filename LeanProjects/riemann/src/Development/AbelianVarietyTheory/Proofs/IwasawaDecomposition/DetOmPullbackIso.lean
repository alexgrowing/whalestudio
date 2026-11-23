import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartLieBasisMatrices
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsRestrictAlongBaseChangeStatement

noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.DetOmPull

open GlobalTheory.FlagMod GlobalTheory.Reg

theorem dualMapR_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (g.comp f) =
      (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR g).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) := by
  apply RingHom.ext
  intro a
  ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]
  rfl

theorem alg_dualMapR {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ spMap (algebraMap A (DualNumber A)) =
      spMap (algebraMap B (DualNumber B)) ≫ spMap f := by
  rw [← spMap_comp_ring, ← spMap_comp_ring]
  congr 1
  apply RingHom.ext
  intro a
  ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem lie_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (X Z : GMod Xo c) (π : Z.X ⟶ X.X) (m : SABMap Z.t X.t π) (M : MChart X)
    (V : Z.X.Opens) (hV : IsAffineOpen V) (hVM : V ≤ π ⁻¹ᵁ M.U) :
    ∃ v₀ : Fin M.n → (Sp (DualNumber Γ(Z.X, V)) ⟶ Z.t.G.left),
      ∀ (R' : Type) [CommRing R'] (f : Γ(Z.X, V) →+* R') (t' : SAB H (Sp R'))
        (m' : SABMap t' Z.t (spMap f ≫ hV.fromSpec)), ∃ v' : Fin M.n → (epsR R' ⟶ t'.G),
          (∀ j, (v' j).left ≫ m'.φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ v₀ j) ∧ IsLieBasis v' ∧
            ∀ a j, IsLieComb (fun i => f (((M.ρ a).map (π.appLE M.U V hVM).hom) i j)) v' (v' j ≫ t'.act.act a) := by
  set r : Γ(X.X, M.U) →+* Γ(Z.X, V) := (π.appLE M.U V hVM).hom with hr_def
  have hr : spMap r ≫ M.hU.fromSpec = hV.fromSpec ≫ π :=
    IsAffineOpen.SpecMap_appLE_fromSpec π M.hU hV hVM
  have hp : ∃ t₀ : SAB H (Sp Γ(Z.X, V)), Nonempty (SABMap t₀ Z.t hV.fromSpec) := by
    obtain ⟨PP', cub, sym, adj, prim, m₀, -⟩ :=
      sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull hV.fromSpec Z.t
    exact ⟨_, ⟨m₀⟩⟩
  obtain ⟨t₀, ⟨m₀⟩⟩ := hp
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.LevelCover.sab_comp m₀ m (e := spMap r ≫ M.hU.fromSpec) hr.symm
  obtain ⟨w, hw, -, -⟩ := M.lie Γ(Z.X, V) r t₀ n₀
  refine ⟨fun j => (w j).left ≫ m₀.φ, fun R' _ f t' m' => ?_⟩
  have he : (spMap f ≫ hV.fromSpec) ≫ π = spMap (f.comp r) ≫ M.hU.fromSpec := by
    rw [spMap_comp_ring, Category.assoc, Category.assoc, hr]
  obtain ⟨n, hn⟩ := GlobalTheory.LevelCover.sab_comp m' m he
  obtain ⟨v', hv', hb, ha⟩ := M.lie R' (f.comp r) t' n
  refine ⟨v', fun j => ?_, hb, fun a j => ha a j⟩
  apply m.cart.1.hom_ext
  · rw [Category.assoc, ← hn, hv', Category.assoc, Category.assoc, ← hn₀, hw, dualMapR_comp, spMap_comp_ring,
      Category.assoc]
  · have w1 : (v' j).left ≫ t'.G.hom = spMap (algebraMap R' (DualNumber R')) := Over.w (v' j)
    have w2 : (w j).left ≫ t₀.G.hom = spMap (algebraMap Γ(Z.X, V) (DualNumber Γ(Z.X, V))) := Over.w (w j)
    rw [Category.assoc, m'.cart.1.w, ← Category.assoc, w1, Category.assoc, Category.assoc, m₀.cart.1.w,
      ← Category.assoc (w j).left, w2]
    simp only [← Category.assoc, alg_dualMapR]

theorem charts_cover {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (X Z : GMod Xo c) (π : Z.X ⟶ X.X) (m : SABMap Z.t X.t π)
    (hX : ⨆ M : MChart X, M.U = ⊤) : ⨆ M : MChart Z, M.U = ⊤ := by
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  have : GlobalTheory.IsNormalScheme Z.X := GlobalTheory.IsNormalScheme.of_pred Z.normal
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨M, hM⟩ : ∃ M : MChart X, π z ∈ M.U := Opens.mem_iSup.1 (hX.ge trivial)
  obtain ⟨W, hzW, hW⟩ := GlobalTheory.ModelChart.exists_open_isDomain Z.X z
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hle⟩ := Z.X.isBasis_affineOpens.exists_subset_of_mem_open
    (show z ∈ ((π ⁻¹ᵁ M.U ⊓ W : Z.X.Opens) : Set Z.X) from ⟨hM, hzW⟩) (π ⁻¹ᵁ M.U ⊓ W).isOpen
  have hVM : V ≤ π ⁻¹ᵁ M.U := fun q hq => (hle hq).1
  have hVW : V ≤ W := fun q hq => (hle hq).2
  obtain ⟨θ, hθ, nz⟩ := GlobalTheory.T.sections_restrict_along_base_change X.t Z.t π m M.U V hVM M.θ M.θ_mem M.θ_ne
  obtain ⟨v₀, hlie⟩ := lie_pull X Z π m M V hV hVM
  exact Opens.mem_iSup.2 ⟨⟨V, hV, hW V hzV hVW, θ, hθ, nz, M.n, v₀,
    fun a => (M.ρ a).map (π.appLE M.U V hVM).hom, hlie⟩, hzV⟩

theorem detOm_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Nonempty (SABMap Z.t X.t π) → (GlobalTheory.FlagMod.detOm X).IsLB → (GlobalTheory.FlagMod.detOm Z).IsLB ∧ LBIso (GlobalTheory.FlagMod.detOm Z) ((GlobalTheory.FlagMod.detOm X).pull π) := by
  intro E _ _ _ H D l Xo c X Z π ⟨m⟩ hX
  have hLX : (detLie X).IsLB := isLB_of_ev _ hX.cover fun i j k _ _ z => ev_detChg_mul i j k z
  have hLZ : (detLie Z).IsLB :=
    isLB_of_ev _ (charts_cover X Z π m hX.cover) fun i j k _ _ z => ev_detChg_mul i j k z
  have hOZ : (detOm Z).IsLB := CechPic.isLB_dual hLZ
  refine ⟨hOZ, ?_⟩
  have e₁ : LBIso ((detLie X).pull π) (detLie Z) := PolFin.lbIso_detLie m.cart
  have c₁ := (CechPic.cls_eq_iff (pull_isLB hLX π) hLZ).2 e₁
  refine (CechPic.cls_eq_iff hOZ (pull_isLB hX π)).1 ?_
  calc CechPic.cls (detOm Z) hOZ = -CechPic.cls (detLie Z) hLZ := CechPic.cls_dual hLZ hOZ
    _ = -CechPic.cls ((detLie X).pull π) (pull_isLB hLX π) := by rw [c₁]
    _ = -CechPic.pull π (CechPic.cls (detLie X) hLX) := by rw [CechPic.cls_pull hLX π]
    _ = CechPic.pull π (-CechPic.cls (detLie X) hLX) := (map_neg _ _).symm
    _ = CechPic.pull π (CechPic.cls (detOm X) hX) := congrArg _ (CechPic.cls_dual hLX hX).symm
    _ = CechPic.cls ((detOm X).pull π) (pull_isLB hX π) := (CechPic.cls_pull hX π _).symm

end GlobalTheory.DetOmPull

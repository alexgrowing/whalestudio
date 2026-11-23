import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementCoversStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinedMetrizedBundleNefAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefHermitianBundlePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOfSurjectivePullbackNefStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtNef

open ReciprocityTheory.ChartRestriction.G GlobalTheory.CechPic in

theorem nefOver_iff_of_isometric {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {L L' : HermLB p}
    (h : L.Isometric L') (l : ℕ) : NefOver L l ↔ NefOver L' l := by
  obtain ⟨w, hw, -⟩ := h
  have e : cls L.B L.isLB = cls L'.B L'.isLB := (cls_eq_iff _ _).2 ⟨w, hw⟩
  have key : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) (κ : Type) [Field κ] [Algebra κ Γ(Z, ⊤)],
      topSelfIntersection κ (L.B.pull i) 1 = topSelfIntersection κ (L'.B.pull i) 1 := fun Z i κ _ _ =>
    interNum_congr_cls κ _ (fun _ => LB.isLB_pull L.isLB i) (fun _ => LB.isLB_pull L'.isLB i) fun _ => by
      rw [cls_pull L.isLB, cls_pull L'.isLB, e]
  constructor <;> intro H Z i _ _ κ _ _ _ _ hd
  · rw [← key]; exact H Z i κ hd
  · rw [key]; exact H Z i κ hd

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem map_genericPoint {V' V : Cover Y} (g : V'.G ⟶ V.G) (h : g ≫ V.π = V'.π) :
    g (genericPoint V'.G) = genericPoint V.G := by
  have key (W : Cover Y) : W.π (genericPoint W.G) = genericPoint Y.X := by
    have := (genericPoint_spec W.G).image W.π.continuous
    rw [Set.image_univ, W.π.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec _)
  obtain ⟨U, hU, e⟩ := isDiscrete_iff_forall_exists_isOpen.mp (V.π.isDiscrete_preimage_singleton (genericPoint Y.X))
    (g (genericPoint V'.G)) (by rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, h, key]; rfl)
  have h₁ : g (genericPoint V'.G) ∈ U := (e.ge rfl).1
  exact (e.le ⟨(genericPoint_specializes _).mem_open hU h₁, key V⟩).symm

theorem surjective_of_lies {V' V : Cover Y} (π : V'.X ⟶ V.X) (hπ : π ≫ V.p = V'.p) (h : Lies V' V π) :
    Function.Surjective π := by
  obtain ⟨g, h₁, h₂⟩ := h
  have hη := (GlobalTheory.CoverDeg.map_genericPoint_and_deg F Y V V' π hπ g h₁.symm h₂ (map_genericPoint g h₂)).1
  have : IsProper V.p := (isProper_and_exists_isAmpleLB_of_isProjOver V.ar.isProjOver).1
  have : IsProper V'.p := (isProper_and_exists_isAmpleLB_of_isProjOver V'.ar.isProjOver).1
  have : IsProper (π ≫ V.p) := by rw [hπ]; infer_instance
  have : IsProper π := IsProper.of_comp π V.p
  have hc : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
  have hm : genericPoint V.X ∈ Set.range π := ⟨_, hη⟩
  have : closure {genericPoint V.X} ⊆ Set.range π := hc.closure_subset_iff.2 (Set.singleton_subset_iff.2 hm)
  rw [(genericPoint_spec V.X).def] at this
  exact fun z => this (Set.mem_univ z)

end GlobalTheory.HtNef

open GlobalTheory.HtNef in

theorem GlobalTheory.HtNef.nefOver_comb_root : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (V : Cover (O.var c)) (L : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (L x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) → ∀ n : D.what₂.Tau → Fin O.N → ℤ, (∀ τ, Antitone (n τ)) → ∀ l ∈ Q, l.Prime → NefOver (ArInt.comb L fun x => -n x.1 x.2) l := by
  intro hP hH D O hC hf A T H h c Q V L hL n hn l hlQ hl
  obtain ⟨V₀, M, hM, hMn⟩ := GlobalTheory.T.combined_metrized_bundle_nef_antitone hP hH D O hC hf A T H h c Q l hlQ hl
  obtain ⟨V', π, π₀, hπ, hπ₀, l₁, l₀⟩ := GlobalTheory.T.common_refinement_covers _ _ V V₀
  have hs := surjective_of_lies π hπ l₁
  obtain ⟨g₁, e₁, f₁⟩ := l₁
  obtain ⟨g₀, e₀, f₀⟩ := l₀
  have hL' x := GlobalTheory.T.norms_pullback_along_cover _ _ V V' π hπ g₁ e₁.symm f₁ (map_genericPoint g₁ f₁) (L x) _ _ _ (hL x)
  have hM' x := GlobalTheory.T.norms_pullback_along_cover _ _ V₀ V' π₀ hπ₀ g₀ e₀.symm f₀ (map_genericPoint g₀ f₀) (M x) _ _ _ (hM x)
  have iso x := GlobalTheory.T.isometric_of_same_norms _ _ V' _ _ _ _ _ (hL' x) (hM' x)
  have n₀ : NefOver ((ArInt.comb M fun x => -n x.1 x.2).pull π₀ hπ₀) l :=
    GlobalTheory.T.nef_hermitian_bundle_pullback _ _ _ _ _ V₀.ar.isProjOver V'.ar.isProjOver π₀ hπ₀ _ l hl (hMn n hn)
  have i₁ := (isometric_comb_pull M (fun x => -n x.1 x.2) π₀ hπ₀).symm
  have i₂ := (isometric_comb_congr iso (fun x => -n x.1 x.2)).symm
  have i₃ := isometric_comb_pull L (fun x => -n x.1 x.2) π hπ
  have n₁ := (nefOver_iff_of_isometric (i₁.trans (i₂.trans i₃)) l).1 n₀
  exact GlobalTheory.T.nef_of_surjective_pullback_nef _ _ _ _ _ V.ar.isProjOver V'.ar.isProjOver π hπ hs _ l hl n₁

end

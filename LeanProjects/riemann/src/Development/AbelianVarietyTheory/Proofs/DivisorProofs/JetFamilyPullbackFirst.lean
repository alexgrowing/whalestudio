import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetMorphismIsBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFiltrationSpannedCorrespondenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentDividedPowersCompatibleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatJet.BaseChangeFil

variable {R R' : Type} [CommRing R] [CommRing R'] {I : Type} [Fintype I] {n : ℕ}

theorem repr_algebraMap (J : JetRing R I n) (r : R) :
    J.b.repr (algebraMap R J.B r) = Finsupp.single ⟨0, by simp⟩ r := by
  rw [Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, Module.Basis.repr_self, Finsupp.smul_single_one]

theorem map_algebraMap (σ : R →+* R') (J : JetRing R I n) (J' : JetRing R' I n) (τ : J.B →+* J'.B)
    (hτ : ∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) (r : R) :
    τ (algebraMap R J.B r) = algebraMap R' J'.B (σ r) := by
  refine J'.b.ext_elem fun ν ↦ ?_
  rw [hτ, repr_algebraMap, repr_algebraMap, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

theorem map_t (σ : R →+* R') (J : JetRing R I n) (J' : JetRing R' I n) (τ : J.B →+* J'.B)
    (hτ : ∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) (i : I) : τ (J.t i) = J'.t i := by
  refine J'.b.ext_elem fun ν ↦ ?_
  rw [hτ, JetRing.t, JetRing.t, Module.Basis.repr_self, Module.Basis.repr_self, Finsupp.single_apply,
    Finsupp.single_apply]
  split_ifs <;> simp

theorem π_surjective (J : JetRing R I n) : Function.Surjective J.π := fun r ↦
  ⟨algebraMap R J.B r, by rw [J.π_eq, repr_algebraMap, Finsupp.single_eq_same]⟩

theorem comp_π (σ : R →+* R') (J : JetRing R I n) (J' : JetRing R' I n) (τ : J.B →+* J'.B)
    (hτ : ∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) : σ.comp J.π = J'.π.comp τ :=
  RingHom.ext fun x ↦ by simp only [RingHom.comp_apply, J.π_eq, J'.π_eq, hτ]

end GlobalTheory.LatJet.BaseChangeFil

open GlobalTheory.LatJet.BaseChangeFil in

theorem GlobalTheory.LatJet.baseChange_liftFil : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (J' : JetRing R' I n) {X₀ : Obj F 𝔠 (Sp R)} {δ₀ : X₀.DetGen}
    {N : I → Module.End R (HdR X₀.A)} (Y : Family J X₀ δ₀ N) {X₁ : Obj F 𝔠 (Sp R')}
    {N₁ : I → Module.End R' (HdR X₁.A)} {p : X₁.A.left ⟶ X₀.A.left}, X₁.IsPullBy X₀ (spMap σ) p →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 R') (𝟙 _) X₁.A σ (spMap σ) p),
    (∀ i x₀ x, m.Corr x₀ x → m.Corr (N i x₀) (N₁ i x)) → ∀ (τ : J.B →+* J'.B),
    (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) → IsDPMorphism J.κ J'.κ τ →
    ∀ {Z' : Obj F 𝔠 (Sp J'.B)} {q : Z'.A.left ⟶ Y.X'.A.left}, Z'.IsPullBy Y.X' (spMap τ) q →
    ∀ {i' : X₁.A.left ⟶ Z'.A.left} (hi' : X₁.IsPullBy Z' (spMap J'.π) i'), i' ≫ q = p ≫ Y.i →
    ∀ (mor' : GrpMor (dp0 R') (𝟙 _) X₁.A J'.κ (spMap J'.π) X₁.A (algebraMap R' J'.B) (𝟙 _) (Over.Hom.left (𝟙 X₁.A))),
    ∀ x ∈ Fil X₁.A, ∀ d, IsJetElt J' X₁ N₁ mor' x d → d ∈ liftFil J'.κ hi'.grp := by
  intro hAb F _ _ 𝔠 R R' _ _ σ I _ n J J' X₀ δ₀ N Y X₁ N₁ p hp m hN τ hτ hτdp Z' q hq i' hi' hiq mor'
  have hbc0 := GlobalTheory.T.jet_morphism_is_base_change hAb J X₀ Y.mor
  have hbc1 := GlobalTheory.T.jet_morphism_is_base_change hAb J' X₁ mor'
  have hspan := GlobalTheory.T.lie_filtration_spanned_correspondence hAb σ hp m
  have hb : spMap σ ≫ spMap J.π = spMap J'.π ≫ spMap τ := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp, comp_π σ J J' τ hτ]
  have M : GrpMor J.κ (spMap J.π) X₀.A J'.κ (spMap J'.π) X₁.A τ (spMap σ) p :=
    GrpMor.of_isGrpPullback hτdp hb hp.grp
  have nq : GrpMor (dp0 J.B) (𝟙 _) Y.X'.A (dp0 J'.B) (𝟙 _) Z'.A τ (spMap τ) q :=
    GrpMor.of_isGrpPullback (Cris.isDPMorphism_of_eq_bot _ rfl _ _) (by simp) hq.grp
  have hspanq := GlobalTheory.T.lie_filtration_spanned_correspondence hAb τ hq nq

  have hprim : ∀ c, c ∈ Submodule.span R' (Set.range m.pull) := by
    letI := σ.toAlgebra
    have hbc := (hAb.2.2.1 R X₀.A _ X₀.ab X₀.dim R' X₁.A p hp.grp).1
    intro c
    obtain ⟨z, rfl⟩ := hbc.2 c
    induction z with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul r c₀ => rw [liftSemi_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c₀, rfl⟩)
  have key : ∀ x₀ ∈ Fil X₀.A, ∀ x, m.Corr x₀ x →
      ∃ d ∈ liftFil J'.κ hi'.grp, IsJetElt J' X₁ N₁ mor' x d := by
    intro x₀ hx₀ x hx
    obtain ⟨e0, he0⟩ := hbc0.exists x₀
    choose e he using fun i ↦ hbc0.exists (N i x₀)
    have hd₀ : IsJetElt J X₀ N Y.mor x₀ (e0 + ∑ i, J.t i • e i) := fun c ↦ by
      simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, he0 c, fun i ↦ he i c]
    have hd₀F := Y.fil x₀ hx₀ _ hd₀
    obtain ⟨d', hd'⟩ := GlobalTheory.T.nilpotent_divided_powers_compatible hAb J.κ J'.κ J.nil J'.nil J.π J'.π (π_surjective J)
      (π_surjective J') rfl rfl τ σ Y.pull hi' hq hiq M (e0 + ∑ i, J.t i • e i)
    refine ⟨d', hspanq.2.2 _ _ hd₀F (crysToDR_corr J.κ Y.pull.grp hi'.grp M nq hiq hd'), ?_⟩
    intro c
    induction hprim c using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨c₀, rfl⟩ := hc
      have e1 : mor'.pull (m.pull c₀) = M.pull (Y.mor.pull c₀) :=
        (GrpMor.pull_pull m mor' (m.comp mor') (fun _ ↦ rfl) rfl c₀).trans
          (GrpMor.pull_pull Y.mor M (m.comp mor') (fun r ↦ map_algebraMap σ J J' τ hτ r)
            (by simp) c₀).symm
      rw [e1, hd', hd₀ c₀, hx c₀]
      simp only [map_add, map_sum, map_mul, map_algebraMap σ J J' τ hτ, map_t σ J J' τ hτ,
        fun i ↦ hN i x₀ x hx c₀]
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [map_add, ha, hb, Finset.sum_add_distrib, mul_add]
      ring
    | smul r a _ ha =>
      simp only [map_smulₛₗ, LinearMap.map_smul, smul_eq_mul, ha, map_mul, mul_add, Finset.mul_sum,
        RingHom.id_apply]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ by ring
  intro x hx d hd
  have hP : ∀ x ∈ Submodule.span R' {x' | ∃ x₀ ∈ Fil X₀.A, m.Corr x₀ x'},
      ∃ d ∈ liftFil J'.κ hi'.grp, IsJetElt J' X₁ N₁ mor' x d := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨x₀, hx₀, hc⟩ := h
      exact key x₀ hx₀ x hc
    | zero => exact ⟨0, zero_mem _, fun c ↦ by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      refine ⟨a + b, add_mem ha hb, fun c ↦ ?_⟩
      simp only [LinearMap.add_apply, ha' c, hb' c, map_add, Finset.sum_add_distrib, mul_add]
      ring
    | smul r x _ hx =>
      obtain ⟨a, ha, ha'⟩ := hx
      refine ⟨algebraMap R' J'.B r • a, Submodule.smul_mem _ _ ha, fun c ↦ ?_⟩
      simp only [LinearMap.smul_apply, ha' c, map_smul, smul_eq_mul, map_mul, mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ by ring
  obtain ⟨d', hd'F, hd'⟩ := hP x (hspan.2.1 hx)
  have h0 : mor'.Corr 0 (d - d') := fun c ↦ by
    rw [LinearMap.sub_apply, hd c, hd' c, sub_self, LinearMap.zero_apply, map_zero]
  have h00 : mor'.Corr 0 0 := fun c ↦ by simp
  rw [sub_eq_zero.1 (hbc1.unique h0 h00)]
  exact hd'F

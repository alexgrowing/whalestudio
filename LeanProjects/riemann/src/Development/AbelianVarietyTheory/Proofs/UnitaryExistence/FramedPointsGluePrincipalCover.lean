import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TanBasisLocalStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMapStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIffStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EigenBasisIffTangentBasisStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionNowhereZeroOfGeneratesStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueGlueSectionsPrincipalCoverStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueGlueDualStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionGeneratesOfNowhereZeroStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionNonvanishingIff

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames.Glue

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    (dualMap ψ).comp (dualMap φ) = dualMap (ψ.comp φ) :=
  RingHom.ext fun x => by ext <;> simp [dualMap]

theorem dual_eps {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) :
    (dualMap φ).comp (epsMul a) = (epsMul (φ a)).comp (dualMap φ) :=
  RingHom.ext fun x => by
    ext <;> simp [dualMap, epsMul, mul_comm]

theorem dual_ext {S : Type} [CommRing S] {Y : Scheme.{0}} {n : ℕ} {h : Fin n → S}
    (hh : Ideal.span (Set.range h) = ⊤) (f g : Sp (DualNumber S) ⟶ Y)
    (e : ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ f =
      spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ g) : f = g := by
  have := GlobalTheory.T.existsUnique_glue_dualNumber S Y n h hh (fun i => spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ g) (by
    intro i j α β hα hβ
    rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp, dual_comp, dual_comp, hα, hβ])
  exact this.unique e fun _ => rfl

theorem exists_lift {S : Type} [CommRing S] {n : ℕ} {h : Fin n → S}
    (hh : Ideal.span (Set.range h) = ⊤) (p : Sp S) :
    ∃ (i : Fin n) (p' : Sp (Localization.Away (h i))), spMap (algebraMap S (Localization.Away (h i))) p' = p := by
  have hp : ∃ i, h i ∉ (show PrimeSpectrum S from p).asIdeal := by
    by_contra hc
    push Not at hc
    apply (show PrimeSpectrum S from p).isPrime.ne_top
    rw [eq_top_iff, ← hh, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hc i
  obtain ⟨i, hi⟩ := hp
  have hr := PrimeSpectrum.localization_away_comap_range (Localization.Away (h i)) (h i)
  have : (show PrimeSpectrum S from p) ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away (h i)))) := by
    rw [hr]; exact hi
  obtain ⟨p', hp'⟩ := this
  exact ⟨i, p', hp'⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem chart_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem secBC_unique {S T : Type} [CommRing S] [CommRing T] {φ : S →+* T} {a : S} {x : Sp S ⟶ Xo.X}
    {x' : Sp T ⟶ Xo.X} {s : LB.Sec (PPx x)} {t t' : LB.Sec (PPx x')} (h₁ : SecBC φ a x x' s t)
    (h₂ : SecBC φ a x x' s t') : t = t' := by
  obtain ⟨p₁, s₁, f₁, a₁⟩ := h₁
  obtain ⟨p₂, s₂, f₂, a₂⟩ := h₂
  have e : p₁ = p₂ := by
    apply pullback.hom_ext
    · exact f₁.trans f₂.symm
    · exact s₁.trans s₂.symm
  subst e
  obtain ⟨t, ht⟩ := t
  obtain ⟨t', ht'⟩ := t'
  congr 1
  funext i
  exact (a₁ i (chart_le p₁ s₁ i)).symm.trans (a₂ i (chart_le p₁ s₁ i))

theorem secBC_transport {S S' T : Type} [CommRing S] [CommRing S'] [CommRing T] {φ : S →+* T} {ψ : S' →+* T}
    {x : Sp S ⟶ Xo.X} {x' : Sp S' ⟶ Xo.X} {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x')} {w w' : Sp T ⟶ Xo.X}
    (hw : w = w') {r : LB.Sec (PPx w)} (h₁ : SecBC φ 1 x w s r) (h₂ : SecBC ψ 1 x' w s' r)
    (t : LB.Sec (PPx w')) (ht : SecBC φ 1 x w' s t) : SecBC ψ 1 x' w' s' t := by
  subst hw
  rw [secBC_unique ht h₁]
  exact h₂

def algOf {K S A B : Type} [CommRing K] [CommRing S] [CommRing A] [CommRing B] [Algebra K S] [Algebra S A]
    [Algebra S B] [Algebra K A] [Algebra K B] [IsScalarTower K S A] [IsScalarTower K S B] (α : A →+* B)
    (hα : α.comp (algebraMap S A) = algebraMap S B) : A →ₐ[K] B :=
  { α with
    commutes' := fun r => by
      rw [IsScalarTower.algebraMap_apply K S A, IsScalarTower.algebraMap_apply K S B, ← hα]
      rfl }

end GlobalTheory.Frames.Glue

open GlobalTheory.Frames.Glue in

theorem GlobalTheory.Frames.frPt_glue : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X), x ≫ Xo.s = sOf c S → ∀ (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ y : ∀ i, FrPt Xo c (Localization.Away (h i)), (∀ i, (y i).x = spMap (algebraMap S (Localization.Away (h i))) ≫ x) → (∀ i j (α : Localization.Away (h i) →ₐ[c.F] Localization.Away (h i * h j)) (β : Localization.Away (h j) →ₐ[c.F] Localization.Away (h i * h j)), α.toRingHom.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) → β.toRingHom.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) → ∀ z, FrMap α (y i) z → FrMap β (y j) z) → ∃ y₀ : FrPt Xo c S, y₀.x = x ∧ ∀ i, FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away (h i))) y₀ (y i) := by
  intro hB E _ _ _ H Dw l Xo c S _ _ x hx n h hh y hy hov
  classical

  have ovl : ∀ i j (α : Localization.Away (h i) →+* Localization.Away (h i * h j))
      (β : Localization.Away (h j) →+* Localization.Away (h i * h j)),
      α.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) →
      β.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) →
      ∃ z : FrPt Xo c (Localization.Away (h i * h j)),
        z.x = spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x ∧
        (∀ τ k, z.u τ k = spMap (dualMap α) ≫ (y i).u τ k) ∧ (∀ τ k, z.u τ k = spMap (dualMap β) ≫ (y j).u τ k) ∧
        SecBC α 1 _ _ (y i).s z.s ∧ SecBC β 1 _ _ (y j).s z.s := by
    intro i j α β hα hβ
    obtain ⟨z, hz⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hB E H Dw l Xo c _ _ (algOf (K := c.F) α hα) (y i)
    have hz' := hov i j (algOf α hα) (algOf β hβ) hα hβ z hz
    have e₁ := ((GlobalTheory.T.framedPoint_baseChange_unique_refl_iff E H Dw l Xo c _ _ _ (y i)).2.2 z).1 hz
    have e₂ := ((GlobalTheory.T.framedPoint_baseChange_unique_refl_iff E H Dw l Xo c _ _ _ (y j)).2.2 z).1 hz'
    refine ⟨z, ?_, e₁.2.1, e₂.2.1, e₁.2.2, e₂.2.2⟩
    rw [e₁.1, hy i, ← Category.assoc, sp_comp, ← hα]
    rfl

  have nf : ∀ i, ∃ ov u tan eig basis s gen,
      y i = ⟨spMap (algebraMap S (Localization.Away (h i))) ≫ x, ov, u, tan, eig, basis, s, gen⟩ := by
    intro i
    have hi := hy i
    generalize y i = w at hi
    obtain ⟨wx, ov, u, tan, eig, basis, s, gen⟩ := w
    dsimp only at hi
    subst hi
    exact ⟨ov, u, tan, eig, basis, s, gen, rfl⟩
  choose ov u tan eig basis s gen hyy using nf
  obtain rfl : y = fun i => ⟨_, ov i, u i, tan i, eig i, basis i, s i, gen i⟩ := funext hyy
  dsimp only at ovl

  have hu : ∀ τ k, ∃ w₀ : Sp (DualNumber S) ⟶ Xo.univ.t.G.left,
      ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w₀ = u i τ k := by
    intro τ k
    refine (GlobalTheory.T.existsUnique_glue_dualNumber S _ n h hh (fun i => u i τ k) ?_).exists
    intro i j α β hα hβ
    obtain ⟨z, -, h₁, h₂, -⟩ := ovl i j α β hα hβ
    exact (h₁ τ k).symm.trans (h₂ τ k)
  choose u₀ hu₀ using hu
  have eig₀ : ∀ τ k, IsEigAt c τ (u₀ τ k) := by
    intro τ k a
    refine dual_ext hh _ _ fun i => ?_
    rw [← Category.assoc, hu₀, eig i τ k a, ← hu₀ τ k i, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp,
      dual_eps, ← IsScalarTower.algebraMap_apply]
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  have tb : TanBasis x (fun j => u₀ (e j).1 (e j).2) := by
    refine GlobalTheory.T.tanBasis_of_local_tanBasis E H Dw l Xo S x n h hh _ _ fun i => ?_
    have := (GlobalTheory.T.eigenBasis_iff_tangentBasis E H Dw l Xo c _ _ (u i) _ e (tan i) (eig i)).1 (basis i)
    simpa only [hu₀] using this
  have tan₀ : ∀ τ k, IsTanAt x (u₀ τ k) := by
    intro τ k
    have := tb.1 (e.symm ⟨τ, k⟩)
    dsimp only at this
    rw [e.apply_symm_apply] at this
    exact this
  have basis₀ := (GlobalTheory.T.eigenBasis_iff_tangentBasis E H Dw l Xo c S x u₀ _ e tan₀ eig₀).2 tb

  obtain ⟨s₀, hs₀⟩ := (GlobalTheory.T.existsUnique_glue_sections_principal_cover E H Dw l Xo S x n h hh s (by
    intro i j α β hα hβ t ht
    obtain ⟨z, hz, -, -, h₁, h₂⟩ := ovl i j α β hα hβ
    exact secBC_transport hz h₁ h₂ t ht)).exists
  have nz : SecNZ x s₀ := by
    intro p
    obtain ⟨i, p', rfl⟩ := exists_lift hh p
    exact (GlobalTheory.Frames.secBC_nonvanishing_iff E H Dw l Xo S _ _ x _ rfl s₀ (s i) (hs₀ i) p').1
      (GlobalTheory.T.fibreSectionNowhereZero_of_generates hB E H Dw l Xo _ _ (s i) (gen i) p')
  refine ⟨⟨x, hx, u₀, tan₀, eig₀, basis₀, s₀, GlobalTheory.T.fibreSectionGenerates_of_nowhereZero hB E H Dw l Xo S x s₀ nz⟩, rfl, fun i => ?_⟩
  refine ((GlobalTheory.T.framedPoint_baseChange_unique_refl_iff E H Dw l Xo c _ _ _ _).2.2 _).2 ⟨rfl, fun τ k => (hu₀ τ k i).symm, hs₀ i⟩

import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FTors
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FNiCoh
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FRiCalc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FibInit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FResLe

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

lemma gl_res_one {R : Type} [CommRing R] {K : Cx.{w} R} {M : Type w'} [AddCommGroup M] [Module R M]
    (ε : M →ₗ[R] K.X 0) (s : R) (h : K.ResUpTo 1 ε) : K.ResUpTo s ε := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨h0, fun x hx => by rw [← one_smul R x, h1 x hx, smul_zero], fun y hy => ?_, fun m y hy => ?_⟩
  · obtain ⟨x, hx⟩ := h2 y hy
    exact ⟨s • x, by rw [map_smul, hx, one_smul]⟩
  · obtain ⟨x, hx⟩ := h3 m y hy
    exact ⟨s • x, by rw [map_smul, hx, one_smul]⟩

lemma gl_desc_id {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) (s : R) :
    Desc s F (𝟭 C) := by
  intro T
  have hI : Limits.IsInitial (StructuredArrow.mk (𝟙 T) : StructuredArrow T (𝟭 C)) :=
    StructuredArrow.mkIdInitial (T := 𝟭 C) (Y := T)
  have h := CrystallineSemistableComparison.P.initial (StructuredArrow.proj T (𝟭 C) ⋙ 𝟭 C ⋙ F) _ hI
  have e : (aug (StructuredArrow.proj T (𝟭 C) ⋙ 𝟭 C ⋙ F) fun x =>
      ((StructuredArrow.proj T (𝟭 C) ⋙ 𝟭 C ⋙ F).map (hI.to x)).hom) = unAug F (𝟭 C) T := by
    unfold unAug
    congr 1
    funext x
    have hx : (hI.to x).right = x.hom := by simpa using StructuredArrow.w (hI.to x)
    change (F.map (hI.to x).right).hom = _
    rw [hx]
  rw [← e]
  exact gl_res_one _ s h

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.glue : ∀ d n : ℕ, ∃ N : ℕ, ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E] {E₀ : Type u''} [Category.{v''} E₀] (F : C ⥤ ModuleCat.{w} R) (G : E ⥤ C) (j : E₀ ⥤ E) [j.Full] [j.Faithful] (U : UF C) (D : C) (A : Act (𝟭 C) U d D) (L : Line (𝟭 C) U) (U' : UF E) (D' : E) (A' : Act j U' d D') (L' : Line j U') (θ : D ⟶ G.obj D') (h : ∀ a, (A.γ a : D ⟶ D) ≫ θ = θ ≫ G.map (A'.γ a)) (s : R), (∀ T, Acyc1 s (F.map (L.i.app T)).hom (F.map (L.γ.app T)).hom) → Desc s (G ⋙ F) j → (∀ T, Acyc1 s ((G ⋙ F).map (L'.i.app T)).hom ((G ⋙ F).map (L'.γ.app T)).hom) → NI s (Functor.whiskerRight (⟨fun _ => θ, fun _ _ a => h a⟩ : A.ι ⟶ A'.ι ⋙ G) F) → RI (s ^ N) n F (j ⋙ G) := by
  intro d n
  obtain ⟨N₁, h₁⟩ := CrystallineSemistableComparison.B.P.tors.{w, v, u, v, u} d n
  obtain ⟨N₂, h₂⟩ := CrystallineSemistableComparison.B.P.tors.{w, v', u', v'', u''} d n
  refine ⟨N₂ + (N₁ + 2) + (2 * n + 3), ?_⟩
  intro R _ C _ E _ E₀ _ F G j _ _ U D A L U' D' A' L' θ h s hL hD hL' hN
  let θn : A.ι ⟶ A'.ι ⋙ G := ⟨fun _ => θ, fun _ _ a => h a⟩
  have t1 : RI (s ^ N₁) n F A.ι := h₁ F (𝟭 C) U D A L s (gl_desc_id F s) hL
  have t2 : RI (s ^ N₂) n (G ⋙ F) A'.ι := h₂ (G ⋙ F) j U' D' A' L' s hD hL'
  have t3 : RI (s ^ N₁ * s ^ 2) n F (A'.ι ⋙ G) := by
    intro i hi
    have hp : (Mor.restrict F (A'.ι ⋙ G)).pull i =
        ((Mor.ofNatTrans (Functor.whiskerRight θn F)).pull i).comp ((Mor.restrict F A.ι).pull i) := by
      rw [← rc_pull_comp]
      exact (LinearMap.ext fun x => CrystallineSemistableComparison.P.prism ((Mor.restrict F A.ι).comp (Mor.ofNatTrans (Functor.whiskerRight θn F)))
        (Mor.restrict F (A'.ι ⋙ G)) θn (fun T x => rfl) i x).symm
    rw [hp]
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ _ _).1 (t1 i hi) (P.ni_coh s (Functor.whiskerRight θn F) hN n i hi)
  have t4 : RI (s ^ N₂ * (s ^ N₁ * s ^ 2)) n F G := (P.ri_calc F G A'.ι _ _ n).2.2.1 t2 t3
  have t5 : RI (s ^ (2 * n + 3)) n (G ⋙ F) j := P.fib (Mor.restrict (G ⋙ F) j) s hD n
  have t6 := (P.ri_calc F G j _ _ n).1 t4 t5
  have he : s ^ (N₂ + (N₁ + 2) + (2 * n + 3)) = s ^ N₂ * (s ^ N₁ * s ^ 2) * s ^ (2 * n + 3) := by ring
  rw [he]
  exact t6

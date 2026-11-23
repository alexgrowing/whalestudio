import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyCartierOfLocallyPrincipalStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

open GlobalTheory.LB GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin
open GlobalTheory.Adelic (cutIdeal)

namespace GlobalTheory.CompHS

def Cartier.pullOfInt {Y T : Scheme.{0}} [IsIntegral T] {I : Y.IdealSheafData} (Δ : Cartier I) (r : T ⟶ Y) {z₀ : T}
    (hz : r z₀ ∉ I.support) : Cartier (I.comap r) :=
  { Cartier.ofSec (LB.isLB_pull Δ.isLB r) (secPull Δ.t r) (y₀ := z₀)
      (by rw [nonzeroLocus_secPull]; exact (Δ.mem_nonzeroLocus _).2 hz) with
    cut := (GlobalTheory.Vanishing.eq_comap_of_stalk
      (fun z => GlobalTheory.Vanishing.stalkId_cutIdeal_secPull Δ.isLB (fun _ : Unit => Δ.t) z)).trans (by rw [Δ.cut]) }

theorem ne_bot_of_notMem {Y : Scheme.{0}} {I : Y.IdealSheafData} {y : Y} (h : y ∉ I.support) : I ≠ ⊥ := fun e => by
  rw [e, Scheme.IdealSheafData.support_bot] at h
  exact h trivial

theorem nonempty_resol (hPr : GlobalTheory.Published.Principalisation) {F : Type} [Field F] [NumberField F] {Y : Scheme.{0}}
    {p : Y ⟶ Sp F} {D : ℕ} (hs : SmoothOfRelativeDimension D p) (hp : IsProjOver p) (hc : GeometricallyConnected p)
    {U : Y.Opens} (hU : (U : Set Y).Nonempty) {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) {a₁ a₂ : Λ}
    {W₁ : Submodule F (H0 p (B a₁) ⊤)} {W₂ : Submodule F (H0 p (B a₂) ⊤)}
    (h₁ : NoBase (C.isLB a₁) W₁ U) (h₂ : NoBase (C.isLB a₂) W₂ U) : Nonempty (Resol C U D W₁ W₂) := by
  have : Smooth p := SmoothOfRelativeDimension.smooth D p
  have : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres p
  have hY : IsIntegral Y := GeometricallyIntegral.geometrically_isIntegral (f := p) (K := F) (𝟙 _) (𝟙 Y) p IsPullback.of_id_fst
  obtain ⟨u, hu⟩ := hU
  obtain ⟨Y₁, s₁, hi₁, hs₁, hp₁, hb₁, -, hc₁, -⟩ :=
    hPr F D Y p hY hs hp (baseIdeal (C.isLB a₁) W₁) (ne_bot_of_notMem (h₁ u hu))
  have iso₁ : IsIso (s₁ ∣_ U) := hb₁.isIso_restrict U h₁
  obtain ⟨z₁, hz₁⟩ : ∃ z : Y₁, z ∈ s₁ ⁻¹ᵁ U :=
    let z := inv (s₁ ∣_ U) ⟨u, hu⟩
    ⟨z.1, z.2⟩
  let M₁ : Modif p U D := ⟨Y₁, s₁, hs₁, hp₁, iso₁, (s₁ ⁻¹ᵁ U).isOpen.dense ⟨z₁, hz₁⟩⟩
  have off₂ : ∀ y ∈ s₁ ⁻¹ᵁ U, y ∉ ((baseIdeal (C.isLB a₂) W₂).comap s₁).support := fun y hy h => by
    rw [Scheme.IdealSheafData.support_comap] at h
    exact h₂ _ hy h
  obtain ⟨Y₂, s₂, hi₂, hs₂, hp₂, hb₂, -, hc₂, -⟩ :=
    hPr F D Y₁ (s₁ ≫ p) hi₁ hs₁ hp₁ _ (ne_bot_of_notMem (off₂ z₁ hz₁))
  have iso₂ : IsIso (s₂ ∣_ (s₁ ⁻¹ᵁ U)) := hb₂.isIso_restrict _ off₂
  obtain ⟨z₂, hz₂⟩ : ∃ z : Y₂, z ∈ s₂ ⁻¹ᵁ (s₁ ⁻¹ᵁ U) :=
    let z := inv (s₂ ∣_ (s₁ ⁻¹ᵁ U)) ⟨z₁, hz₁⟩
    ⟨z.1, z.2⟩
  let M₂ : Modif M₁.str M₁.opn D := ⟨Y₂, s₂, hs₂, hp₂, iso₂, (s₂ ⁻¹ᵁ (s₁ ⁻¹ᵁ U)).isOpen.dense ⟨z₂, hz₂⟩⟩
  have Δ₂ : Cartier ((baseIdeal (C.isLB a₂) W₂).comap (s₂ ≫ s₁)) := by
    rw [Scheme.IdealSheafData.comap_comp]; exact (GlobalTheory.T.nonempty_cartier_of_locally_principal' _ _ hc₂).some
  have Δ₁ : Cartier ((baseIdeal (C.isLB a₁) W₁).comap (s₂ ≫ s₁)) := by
    rw [Scheme.IdealSheafData.comap_comp]
    exact (GlobalTheory.T.nonempty_cartier_of_locally_principal' _ _ hc₁).some.pullOfInt s₂ (z₀ := z₂) (by
      rw [Scheme.IdealSheafData.support_comap]; exact h₁ _ hz₂)
  exact ⟨{ toModif := M₁.trans M₂, Δ₁ := Δ₁, Δ₂ := Δ₂ }⟩

end GlobalTheory.CompHS

open GlobalTheory.CompHS in

theorem GlobalTheory.CompHS.nonempty_choice : GlobalTheory.Published.Principalisation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw), IsVariety₀ TF.X Z → FreeOnOpen TF.X Z U P.u₁ → FreeOnOpen TF.X Z U P.u₂ → Nonempty (Choice TF.X Z U P) := by
  intro hPr E _ _ _ H Dw l Xo c TF Z r U P hv h₁ h₂
  obtain ⟨hs, hp, hc⟩ := hv
  have : ConnectedSpace (Y₀ TF.X Z) := GeometricallyConnected.connectedSpace_of_subsingleton (str₀ TF.X Z)
  exact nonempty_resol hPr hs hp hc (dense_U₀ TF.X Z).nonempty (common₀ TF.X Z) h₁ h₂

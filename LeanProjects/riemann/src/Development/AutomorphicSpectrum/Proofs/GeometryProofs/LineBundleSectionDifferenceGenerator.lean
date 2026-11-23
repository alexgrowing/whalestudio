import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

section TauGen

variable {X Y Z : Scheme.{0}} (L : LB X)

def gUnit (h : Y ⟶ X) (a b : L.ι) {V : Y.Opens} (hV : V ≤ h ⁻¹ᵁ (L.U a ⊓ L.U b)) : Γ(Y, V)ˣ :=
  res hV (pullU h _ (L.g a b))

theorem gm_gUnit (h : Y ⟶ X) (a b : L.ι) {V : Y.Opens} (hV : V ≤ h ⁻¹ᵁ (L.U a ⊓ L.U b)) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ V) : gm r z V (gUnit L h a b hV) = gm (r ≫ h) z _ (L.g a b) :=
  (gm_res r z hV hz _).trans (gm_pull r h z _ (hV hz) _)

def chartGen (f f' : Y ⟶ X) (b : L.ι) (hb : ∀ y, f y ∈ L.U b) (hb' : ∀ y, f' y ∈ L.U b) :
    LB.Gen (LB.LinComb L (K := Fin 2) ![f, f'] ![1, -1]) where
  s := fun i =>
    gUnit L f (i 0) b (V := LB.wchart L ![f, f'] i) (fun y hy => ⟨LB.wchart_le L ![f, f'] i 0 hy, hb y⟩) *
    (gUnit L f' (i 1) b (V := LB.wchart L ![f, f'] i) (fun y hy => ⟨LB.wchart_le L ![f, f'] i 1 hy, hb' y⟩))⁻¹

theorem gm_chartGen (f f' : Y ⟶ X) (b : L.ι) (hb : ∀ y, f y ∈ L.U b) (hb' : ∀ y, f' y ∈ L.U b)
    (i : Fin 2 → L.ι) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ LB.wchart L ![f, f'] i) :
    gm r z (LB.wchart L ![f, f'] i) ((chartGen L f f' b hb hb').s i) =
      gm (r ≫ f) z _ (L.g (i 0) b) * (gm (r ≫ f') z _ (L.g (i 1) b))⁻¹ :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_gUnit L f _ _ _ r z hz)
    ((map_inv _ _).trans (congrArg _ (gm_gUnit L f' _ _ _ r z hz))))

theorem chartGen_isGen (hL : L.IsLB) (f f' : Y ⟶ X) (b : L.ι) (hb : ∀ y, f y ∈ L.U b) (hb' : ∀ y, f' y ∈ L.U b) :
    (chartGen L f f' b hb hb').IsGen := by
  intro (i : Fin 2 → L.ι) (j : Fin 2 → L.ι)
  refine unit_ext fun y hy => ?_
  have hi : (𝟙 Y) y ∈ LB.wchart L ![f, f'] i := hy.1
  have hj : (𝟙 Y) y ∈ LB.wchart L ![f, f'] j := hy.2
  have hi0 : (𝟙 Y ≫ f) y ∈ L.U (i 0) := LB.wchart_le L ![f, f'] i 0 hy.1
  have hi1 : (𝟙 Y ≫ f') y ∈ L.U (i 1) := LB.wchart_le L ![f, f'] i 1 hy.1
  have hj0 : (𝟙 Y ≫ f) y ∈ L.U (j 0) := LB.wchart_le L ![f, f'] j 0 hy.2
  have hj1 : (𝟙 Y ≫ f') y ∈ L.U (j 1) := LB.wchart_le L ![f, f'] j 1 hy.2
  have hb0 : (𝟙 Y ≫ f) y ∈ L.U b := hb y
  have hb1 : (𝟙 Y ≫ f') y ∈ L.U b := hb' y
  have A := gm_chartGen L f f' b hb hb' i (𝟙 Y) y hi
  have B := gm_chartGen L f f' b hb hb' j (𝟙 Y) y hj
  have C := gm_linComb L ![f, f'] ![1, -1] (𝟙 Y) y i j hi hj
  refine ((gm_res _ y _ hy _).trans A).trans (Eq.symm ((map_mul _ _ _).trans
    ((congrArg₂ (· * ·) C ((gm_res _ y _ hy _).trans B)).trans ?_)))
  have T : (∏ k, gm (𝟙 Y ≫ (![f, f'] : Fin 2 → (Y ⟶ X)) k) y (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)) ^
      (![1, -1] : Fin 2 → ℤ) k) = gm (𝟙 Y ≫ f) y _ (L.g (i 0) (j 0)) * (gm (𝟙 Y ≫ f') y _ (L.g (i 1) (j 1)))⁻¹ :=
    (Fin.prod_univ_two _).trans (congrArg₂ (· * ·) (zpow_one _) (zpow_neg_one _))
  rw [T, ← gm_cocycle hL (𝟙 Y ≫ f) y hi0 hj0 hb0, ← gm_cocycle hL (𝟙 Y ≫ f') y hi1 hj1 hb1, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

end TauGen

theorem jetPair_gen : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (k : Type) [Field k] (p : ℕ) (f f' : Sp (Jet k Unit p) ⟶ X), spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ f = spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ f' → ∃ τ : LB.Gen (LB.LinComb L (K := Fin 2) ![f, f'] ![1, -1]), τ.IsGen ∧ ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ X) → L.ι), Good L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1 := by
  intro X L hL k _ p f f' e
  obtain ⟨s₀⟩ : Nonempty (Sp k) := inferInstance
  set w₀ : Sp (Jet k Unit p) := (spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) s₀ with hw
  have hq : ∀ q : Sp (Jet k Unit p), q = w₀ := fun q => (jet_pt p q s₀).symm
  have e₀ : f' w₀ = f w₀ := by
    have := congrArg (fun m => m s₀) e
    simpa using this.symm
  obtain ⟨b, hb₀⟩ := exists_chart hL (f w₀)
  have hb : ∀ y, f y ∈ L.U b := fun y => by rw [hq y]; exact hb₀
  have hb' : ∀ y, f' y ∈ L.U b := fun y => by rw [hq y, e₀]; exact hb₀
  refine ⟨chartGen L f f' b hb hb', chartGen_isGen L hL f f' b hb hb', ?_⟩
  intro Z' r z J hJ
  set ρ := r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) with hρ
  have eρ : ρ ≫ f = ρ ≫ f' := by rw [hρ, Category.assoc, Category.assoc, e]
  have hz := hJ.mem ![f, f'] ρ
  rw [val]
  refine (gm_chartGen L f f' b hb hb' _ ρ z hz).trans ?_
  have key : ∀ ψ ψ' : Z' ⟶ X, ψ = ψ' → gm ψ z (L.U (J ψ) ⊓ L.U b) (L.g (J ψ) b) =
      gm ψ' z (L.U (J ψ') ⊓ L.U b) (L.g (J ψ') b) := by
    rintro _ _ rfl
    rfl
  exact mul_inv_eq_one.2 (key _ _ eρ)

end GlobalTheory.CompanionTheory.Ar.Coc

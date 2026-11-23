import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AdExExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.GaloisLiftMemFirstOrderDeformations
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LcOfOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PolZCases
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AdicLC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PhiSub

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem finTw_lc {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  have hs : ∀ i j, ∀ x, ∀ᶠ y in nhds x, f y i j = f x i j := fun i j =>
    (IsLocallyConstant.iff_eventually_eq _).1 (h i j)
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have hall : ∀ᶠ y in nhds x, ∀ i j, f y i j = f x i j := by
    simp only [Filter.eventually_all]
    exact fun i j => hs i j x
  filter_upwards [hall] with y hy
  ext i j
  exact hy i j

theorem UpperTheory.V.Pa.finTw :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (m : ℕ), PhiCond G0.Γ l → (TwZ k (x.Am m)).Finite := by
  intro l _ L G0 n x k m hΦ
  obtain ⟨_, _, hfinR, _, hlR, _, htR, _, _⟩ := finAm l G0.frame n x m k.g
  let χ : G0.Γ →* x.A := (algebraMap ℤ_[l] x.A).toMonoidHom.comp ((Units.coeHom ℤ_[l]).comp G0.ε)
  have hok := (ok1 l L G0 G0 (Glob.Hom.refl G0) n x k (x.Am m) χ).2.1
  obtain ⟨rep, hrep⟩ := adEx l G0.frame x.A (DD (x.Am m) k.g) n _ _ _ hok
  obtain ⟨_, hlce, hLC⟩ := lc1 l L G0 G0 (Glob.Hom.refl G0) n x k m
  have hLCrep := hLC _ _ rep hlce hrep
  haveI : Finite (DD (x.Am m) k.g) := hfinR
  have hl : ∀ v : pairedDualFirstOrderDualMatrixSpace n x.A (x.Am m) k.g x.a, l • v = 0 := by
    intro v
    apply Subtype.ext
    funext i j
    simp [hlR]
  obtain ⟨hfin, _⟩ := finZ l x.A G0.Γ (pairedDualFirstOrderDualMatrixSpace n x.A (x.Am m) k.g x.a) rep hΦ hLCrep hl
  have key : ∀ z ∈ TwZ k (x.Am m), ∃ y ∈ Zl rep, y G0.c = 0 ∧
      ∀ g : G0.frame.G₀, (y (g : G0.Γ) : Matrix _ _ _) = z g := by
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    refine (polZ l G0.frame x.A (DD (x.Am m) k.g) n _ _ _ rep hrep).1 z h1 ?_ h3 h4
    apply finTw_lc
    intro i j
    exact (adicLC G0.frame.G₀ (DD (x.Am m) k.g) _ m _ htR).1 (h2 i j)
  let φ : TwZ k (x.Am m) → Zl rep := fun z => ⟨(key z.1 z.2).choose, (key z.1 z.2).choose_spec.1⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    funext g
    have ha := (key a.1 a.2).choose_spec.2.2 g
    have hb := (key b.1 b.2).choose_spec.2.2 g
    have he : (key a.1 a.2).choose = (key b.1 b.2).choose := congrArg Subtype.val hab
    rw [← ha, ← hb, he]
  exact Set.finite_coe_iff.mp (Finite.of_injective φ hinj)

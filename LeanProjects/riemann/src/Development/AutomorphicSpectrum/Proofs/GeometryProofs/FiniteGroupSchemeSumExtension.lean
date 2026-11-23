import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem gm_comp_spMap_unitOn {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (u : Rˣ) {Z : Scheme.{0}}
    (r : Z ⟶ Sp R') (z : Z) :
    gm (r ≫ spMap f) z ⊤ (unitOn u) = gm r z ⊤ (unitOn (Units.map f.toMonoidHom u)) := by
  refine (gm_pull r (spMap f) z ⊤ trivial (unitOn u)).symm.trans (congrArg (gm r z ⊤) ?_)
  apply Units.ext
  exact (congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

def FG.scaled {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) (a : FG M Y) (c : Γ(Y, ⊤)ˣ) : FG M Y :=
  ⟨a.K, a.φ, a.ε, scaleGen a.t c, scaleGen_isGen hM a.t a.ht c⟩

theorem FG.v_scaled {X Y Z : Scheme.{0}} {M : LB X} (hM : M.IsLB) (a : FG M Y) (c : Γ(Y, ⊤)ˣ) (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X) → M.ι} (hJ : Good M z J) : (a.scaled hM c).v r z J = gm r z ⊤ c * a.v r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ (hJ.mem a.φ r) _) rfl)

theorem exists_root_in_ext (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 1 ≤ n) (c : Kˣ) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (u : K'ˣ),
      u ^ n = Units.map (algebraMap K K').toMonoidHom c := by
  let P : Polynomial K := Polynomial.X ^ n - Polynomial.C (c : K)
  have hdeg : P.degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C (by omega)]
    exact_mod_cast (by omega : n ≠ 0)
  have : FiniteDimensional ℚ P.SplittingField := Module.Finite.trans K _
  obtain ⟨ρ, hρ⟩ := (Polynomial.IsSplittingField.splits P.SplittingField P).exists_eval_eq_zero
    (by rwa [Polynomial.degree_map])
  have hρn : ρ ^ n = algebraMap K P.SplittingField (c : K) := by
    simpa [P, sub_eq_zero, Polynomial.eval_map] using hρ
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hρn
    exact (map_ne_zero _).2 c.ne_zero hρn.symm
  refine ⟨P.SplittingField, inferInstance, NumberField.mk, inferInstance, Units.mk0 ρ hρ0, Units.ext ?_⟩
  simpa using hρn

theorem exists_gen_normalised {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Field K] [NumberField K] (n : ℕ)
    (hn : 1 ≤ n) (xl : Sp K ⟶ X) (A : FG M (Sp K))
    (hA : ∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ X) → U), A.sum U h = (h xl ^ n)⁻¹) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (e : FG M (Sp K')),
      (∀ (U : Type) [CommGroup U] (h : (Sp K' ⟶ X) → U), e.sum U h = h (spMap (algebraMap K K') ≫ xl)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp K') (z : Z) (J), Good M z J →
        e.v r z J ^ n * A.v (r ≫ spMap (algebraMap K K')) z J = 1 := by
  obtain ⟨z₀⟩ : Nonempty (Sp K) := inferInstance
  choose d hd using fun χ : Sp K ⟶ X => exists_chart hM (χ z₀)
  have hJ₀ : Good M z₀ d := hd
  obtain ⟨t₀, ht₀, -⟩ := GlobalTheory.ThetaInValues.exists_gen_of_value hM (fun _ : PUnit => xl) (fun _ => (1 : ℤ)) hJ₀ (1 : Kˣ)
  let e₀ : FG M (Sp K) := ⟨PUnit, _, _, t₀, ht₀⟩
  have hs₀ : ∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ X) → U), e₀.sum U h = h xl := by
    intro U _ h
    show ∏ _k : PUnit, h xl ^ (1 : ℤ) = _
    simp
  have hg : ∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ X) → U), ((e₀.pow n).mul A).sum U h = 1 := by
    intro U _ h
    rw [FG.sum_mul, FG.sum_pow, hs₀, hA]
    exact _root_.mul_inv_cancel _
  obtain ⟨c, hc⟩ := FG.exists_unit hM _ hg
  let c₀ : Kˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom c
  have hcc : unitOn c₀ = c := by
    apply Units.ext
    exact Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of K)) c.val
  obtain ⟨K', iF, iN, iA, u, hu⟩ := exists_root_in_ext K n hn c₀⁻¹
  refine ⟨K', iF, iN, iA, (e₀.pull (spMap (algebraMap K K'))).scaled hM (unitOn u), ?_, ?_⟩
  · intro U _ h
    exact hs₀ U fun q => h (spMap (algebraMap K K') ≫ q)
  · intro Z r z J hJ
    have key : unitOn u ^ n * unitOn (Units.map (algebraMap K K').toMonoidHom c₀) = 1 := by
      have e1 : unitOn u ^ n = unitOn (u ^ n) := (map_pow _ _ _).symm
      have e2 : ∀ a b : K'ˣ, unitOn a * unitOn b = unitOn (a * b) := fun a b => (map_mul _ _ _).symm
      rw [e1, e2, hu, ← map_mul, inv_mul_cancel, map_one]
      exact map_one _
    rw [FG.v_scaled hM _ _ r hJ, FG.v_pull hJ, _root_.mul_pow, _root_.mul_assoc, ← FG.v_pow hJ, ← FG.v_mul hJ,
      hc Z _ z J hJ, ← hcc, gm_comp_spMap_unitOn, ← map_pow, ← map_mul, key, map_one]

end GlobalTheory.CompanionTheory.Ar.Sl.Transl

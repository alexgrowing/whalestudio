import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OverPointsExtOfInjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SpreadLevel

theorem appTop_unitOn {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (u : Rˣ) (u₀ : Kˣ)
    (h : f u = u₀) : Units.map (spMap f).appTop.hom.toMonoidHom (unitOn u) = unitOn u₀ := by
  apply Units.ext
  have := congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [h] at this
  exact this.symm

theorem appTop_injective {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (hf : Function.Injective f) :
    Function.Injective (spMap f).appTop.hom := by
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
  intro a b hab
  have ha := congrArg (fun q => q.hom a) e
  have hb := congrArg (fun q => q.hom b) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at ha hb
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  apply hf
  exact ha.symm.trans ((congrArg _ hab).trans hb)

theorem linComb_pow {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ}
    (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) (M : ℕ) (h : ∀ i, y i ^ M = 1) : linComb y a ^ M = 1 := by
  unfold linComb
  rw [List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, h, one_pow]

theorem stdSymp_cast {g g' : ℕ} (h : g = g') (i j : Fin (2 * g)) (i' j' : Fin (2 * g')) (hi : (i' : ℕ) = i)
    (hj : (j' : ℕ) = j) : stdSymp g' i' j' = stdSymp g i j := by
  subst h
  rw [Fin.ext hi, Fin.ext hj]

end SpreadLevel

open SpreadLevel in

theorem level_of_generic_of_indep : Laws → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (P : PolAV (Sp R)) (P₀ : PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A (spMap (algebraMap R K)) φ → LBIso P₀.L (P.L.pull φ) → P.g = P₀.g → ∀ (M : ℕ) (ze : Rˣ) (ze₀ : Kˣ), IsUnit (M : R) → algebraMap R K ze = ze₀ → ∀ (lev₀ : Out.Level P₀ M (unitOn ze₀)) (y : Fin (2 * P.g) → (baseOver (Sp R) ⟶ P.A)), (∀ (i₀ : Fin (2 * P₀.g)) (i : Fin (2 * P.g)), (i₀ : ℕ) = i → (lev₀.pt i₀).left ≫ φ = spMap (algebraMap R K) ≫ (y i).left) → (∀ (F : Type) [Field F] [IsAlgClosed F] (s : Spec (CommRingCat.of F) ⟶ Sp R) (c c' : Fin (2 * P.g) → Fin M), linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)) = linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c' i : ℕ)) → c = c') → ∃ lev : Out.Level P M (unitOn ze), lev.pt = y := by
  intro hL R K _ _ _ _ _ _ P P₀ φ hp hw hg M ze ze₀ hM hze lev₀ y hy hind
  obtain ⟨w, hw⟩ := hw
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hu := appTop_unitOn (algebraMap R K) ze ze₀ hze
  have hΓ : Function.Injective (Units.map (spMap (algebraMap R K)).appTop.hom.toMonoidHom) :=
    Units.map_injective (appTop_injective _ hinj)
  have := P.isAb.comm
  have := P.isAb.proper
  let cs : Fin (2 * P.g) → Fin (2 * P₀.g) := Fin.cast (by rw [hg])
  have hy' : ∀ i, spMap (algebraMap R K) ≫ (y i).left = (lev₀.pt (cs i)).left ≫ φ := fun i => (hy (cs i) i rfl).symm
  let U : Over.mk ((baseOver (Sp K)).hom ≫ spMap (algebraMap R K)) ⟶ baseOver (Sp R) :=
    Over.homMk (spMap (algebraMap R K)) (by simp)
  have tor : ∀ i, y i ^ M = 1 := fun i => by
    have e : U ≫ y i = pushHom hp (baseOver (Sp K)) (lev₀.pt (cs i)) := Over.OverMorphism.ext (hy' i)
    have e₁ : U ≫ (y i ^ M) = U ≫ 1 := by
      rw [MonObj.comp_pow, MonObj.comp_one, e]
      exact (map_pow (pushHom hp _) _ M).symm.trans ((congrArg _ (lev₀.torsion _)).trans (map_one _))
    exact over_points_ext_of_injective _ P.A R K _ hinj _ _ _ (congrArg (fun q => q.left) e₁)
  refine ⟨⟨y, ?_, tor, hind, ?_, ?_⟩, rfl⟩
  · have := lev₀.prim
    rw [← hu] at this
    exact this.of_map_of_injective hΓ
  · intro F _ _ s x hx
    have hF : (M : F) ≠ 0 := by
      have := hM.map (Spec.preimage s).hom
      rw [map_natCast] at this
      exact this.ne_zero
    have hM0 : 1 ≤ M := Nat.pos_of_ne_zero (by rintro rfl; exact hF Nat.cast_zero)
    have hc := (hL.mulN _ P M hM0).2.2.2.2 F s hF
    let Φ : (Fin (2 * P.g) → Fin M) → {x : Over.mk s ⟶ P.A // x ^ M = 1} := fun c =>
      ⟨linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)),
        linComb_pow _ _ M fun i => by rw [← MonObj.comp_pow, tor, MonObj.comp_one]⟩
    have hΦ : Function.Injective Φ := fun c c' h => hind F s c c' (congrArg Subtype.val h)
    have : Finite {x : Over.mk s ⟶ P.A // x ^ M = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
    have hb := hΦ.bijective_of_nat_card_le (by rw [hc]; simp)
    obtain ⟨c, h⟩ := hb.2 ⟨x, hx⟩
    exact ⟨c, congrArg Subtype.val h⟩
  · intro i j
    obtain ⟨c, hc, -⟩ := (hL.weil _ P M (baseOver (Sp R))).1 (y i) (y j) (tor i) (tor j)
    obtain ⟨r, hr, ⟨cu⟩⟩ := PolAV_exists_cubical hL.cube P₀
    have := P₀.isAb.comm
    have h₁ := WeilCube.weilIs_pull cu hL.globalFns P₀.isAb P.isLB hp w hw (T := baseOver (Sp K))
      (T₀ := baseOver (Sp R)) (spMap (algebraMap R K)) (by simp) (lev₀.torsion (cs i)) (lev₀.torsion (cs j))
      (hy' i) (hy' j) hc
    have h₂ := ((hL.weil _ P₀ M (baseOver (Sp K))).1 _ _ (lev₀.torsion (cs i)) (lev₀.torsion (cs j))).unique h₁
      (lev₀.pairing _ _)
    rw [stdSymp_cast hg i j (cs i) (cs j) rfl rfl, ← hu] at h₂
    have h₃ : c = unitOn ze ^ stdSymp P.g i j := hΓ (h₂.trans (map_zpow _ _ _).symm)
    exact h₃ ▸ hc

end GlobalTheory

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsExistAffineZeroSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsOfDeRhamClassesUniqueStatement

set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CatCoh GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem perCl_add' {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
    (p q r : Λ →+ Hol F.V) (h : ∀ l, r l = p l + q l) : K.perCl r = K.perCl p + K.perCl q := by
  unfold Charts.perCl
  rw [← map_add]
  congr 1
  refine Subtype.ext ?_
  funext T T' f
  change algebraMap (Hol F.V) T'.C (r f.deg) = algebraMap (Hol F.V) T'.C (p f.deg) + algebraMap (Hol F.V) T'.C (q f.deg)
  rw [h, map_add]

theorem perCl_smul' {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
    (a : Hol F.V) (p r : Λ →+ Hol F.V) (h : ∀ l, r l = a * p l) : K.perCl r = a • K.perCl p := by
  refine Eq.trans ?_ ((H1.mk K.Oc).map_smul a (K.perZ p))
  refine congrArg (H1.mk K.Oc) (Subtype.ext ?_)
  funext T T' f
  change algebraMap (Hol F.V) T'.C (r f.deg) = a • algebraMap (Hol F.V) T'.C (p f.deg)
  rw [h, map_mul, Algebra.smul_def]

theorem hol_point (f : Hol (⊤ : Opens (Empty → ℂ))) : algebraMap ℂ _ (f.fn 0) = f :=
  Hol.ext_fn fun p hp ↦ by rw [Hol.fn_algebraMap _ hp, Subsingleton.elim p 0]

theorem pHom_of (hE : PExist) (hU : PUniq) : PHom := by
  intro A _ g hA L u
  have : IsProper A.hom := hA.proper
  have : IsSeparated (A.hom ≫ 𝟙 _) := inferInstance
  have hB : (fibUnif u).Based := by
    let f : Sp ℂ ⟶ A.left := (u.ex 0).left
    have hs : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
    let pt : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := (A.left.isBasis_affineOpens).exists_subset_of_mem_open
      (Set.mem_univ (f pt)) isOpen_univ
    refine ⟨U, hU, fun z _ q _ ↦ ?_⟩
    rw [Subsingleton.elim q pt]
    exact hx
  choose per hper using fun c : primDR A ↦ hE _ _ _ _ _ _ _ _ (fibUnif u) hB c.1
  have hadd : ∀ c c' : primDR A, per (c + c') = per c + per c' := fun c c' ↦
    hU _ _ _ _ _ _ _ _ (fibUnif u) _ _ _ (hper (c + c')) fun K r hr ↦ by
      rw [perCl_add' K (per c) (per c') _ fun _ ↦ rfl, ← hper c K r hr, ← hper c' K r hr, ← map_add]
      rfl
  have hsmul : ∀ (a : ℂ) (c : primDR A), per (a • c) =
      (AddMonoidHom.mulLeft (algebraMap ℂ (Hol (fibFam u).V) a)).comp (per c) := fun a c ↦
    hU _ _ _ _ _ _ _ _ (fibUnif u) _ _ _ (hper (a • c)) fun K r hr ↦ by
      rw [perCl_smul' K (algebraMap ℂ (Hol (fibFam u).V) a) (per c) _ fun _ ↦ rfl, ← hper c K r hr, ← map_smulₛₗ]
      rfl
  let ev : Hol (fibFam u).V →ₐ[ℂ] ℂ := Hol.ev 0 trivial
  refine ⟨{ toFun x :=
              { toFun c := ev (per c x)
                map_add' c c' := by rw [hadd, AddMonoidHom.add_apply, map_add]
                map_smul' a c := by
                  rw [hsmul]
                  change ev (algebraMap ℂ _ a * per c x) = a * _
                  rw [map_mul, AlgHom.commutes]; rfl }
            map_zero' := LinearMap.ext fun c ↦ by
              change ev (per c 0) = 0
              rw [map_zero, map_zero]
            map_add' x y := LinearMap.ext fun c ↦ by
              change ev (per c (x + y)) = ev (per c x) + ev (per c y)
              rw [map_add, map_add] }, fun c ↦ ?_⟩
  convert hper c using 1
  refine AddMonoidHom.ext fun x ↦ ?_
  change algebraMap ℂ (Hol (fibFam u).V) (ev (per c x)) = per c x
  exact (congrArg _ (Hol.ev_apply (W := (fibFam u).V) 0 trivial (per c x))).trans (hol_point _)

theorem pHom : PHom := pHom_of GlobalTheory.T.periods_exist_affine_zero_section GlobalTheory.T.periods_of_deRham_classes_unique

end GlobalTheory.AnPer

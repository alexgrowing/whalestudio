import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass
import Development.AbelianVarietyTheory.Definitions.Divisors.NontrivialOfArtinQE

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem list_prod_ofFn_eq_of_eq_one_of_ne' {M : Type*} [Monoid M] :
    ∀ {m : ℕ} (f : Fin m → M) (i : Fin m), (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i := by
  intro m
  induction m with
  | zero => intro f i; exact i.elim0
  | succ m ih =>
    intro f i hf
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun i' => ?_) i hf
    · intro hf0
      rw [List.prod_eq_one, _root_.mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      exact hf0 _ (Fin.succ_ne_zero j)
    · intro hfs
      rw [hfs 0 (Fin.succ_ne_zero i').symm, _root_.one_mul]
      exact ih (fun j => f j.succ) i' (fun j hj => hfs _ (fun h => hj (Fin.succ_injective _ h)))

private theorem matEnd_diagonal_pr {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ}
    (d : Fin m → O) (i : Fin m) :
    GlobalTheory.KS.matEnd act (Matrix.diagonal d) ≫ GlobalTheory.KS.pr A i = GlobalTheory.KS.pr A i ≫ act.act (d i) := by
  unfold GlobalTheory.KS.matEnd GlobalTheory.KS.pr
  rw [Pi.lift_π]
  rw [list_prod_ofFn_eq_of_eq_one_of_ne' _ i]
  · simp
  · intro j hj
    simp [Matrix.diagonal_apply_ne' d hj, GlobalTheory.KS.Model.act_zero, Hom.one_def]

theorem UpperTheory.Gal.W2.pwOver_of :
    UpperTheory.Gal.W2.PwOver := by
  intro p _ D G L gb N N' h X X' c k
  have hpw : c.pw k ≫ (KS.pow X.univ.A k).hom = (KS.pow X'.univ.A k).hom ≫ c.q := by
    delta Leg.pw
    exact KS.Model.powMap_over _ _ _ k
  have hpr : ∀ i : Fin k,
      c.pw k ≫ Over.Hom.left (KS.pr X.univ.A i) = Over.Hom.left (KS.pr X'.univ.A i) ≫ c.tot := by
    intro i
    delta Leg.pw
    exact KS.Model.powMap_pr _ _ _ k i
  refine ⟨hpw, hpr, ?_, fun α => ⟨?_, fun i => ?_⟩⟩
  · intro b
    delta Leg.tot
    have h1 := congrArg Over.Hom.left (c.tr.2.1 b)
    simp only [Over.comp_left] at h1
    rw [← Category.assoc, h1, Category.assoc, c.φ.act b, Category.assoc]
  · delta Leg.tw
    rw [Category.assoc, Over.w, hpw]
  · have hm := congrArg Over.Hom.left
      (matEnd_diagonal_pr X.univ.act (fun s => (algebraMap (𝓞 D.F) D.O (α s) : D.toG.O)) i)
    rw [Over.comp_left, Over.comp_left] at hm
    delta Leg.tw
    refine (Category.assoc _ _ _).trans ((congrArg (c.pw k ≫ ·) hm).trans ?_)
    rw [← Category.assoc, hpr, Category.assoc]

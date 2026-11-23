import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjByOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecBasisTransfer

def chartPullUnLinComb {X X' Y Y' : Scheme.{0}} (L : LB X) (F : X' ⟶ X) {K : Type} [Fintype K]
    (ψ' : K → (Y' ⟶ X')) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (g : Y ⟶ Y') (hc : ∀ k, g ≫ ψ' k ≫ F = ψ k) :
    ChartPull (LB.LinComb L ψ ε) (LB.LinComb (L.pull F) ψ' ε) g :=
  have pt : ∀ k (y : Y), F (ψ' k (g y)) = ψ k y := fun k y => by
    rw [← hc k]; rfl
  have le : ∀ j : K → L.ι, LB.wchart L ψ j ≤ g ⁻¹ᵁ LB.wchart (L.pull F) ψ' (fun k _ => j k) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull.2 (by
      show F (ψ' k (g y)) ∈ L.U (j k)
      rw [pt k y]; exact Set.mem_iInter.1 hy k)
  { idx := fun j k _ => j k
    le := le
    g := fun y j j' hj hj' => by
      have m : g y ∈ LB.wchart (L.pull F) ψ' (fun k _ => j k) := le j hj
      have m' : g y ∈ LB.wchart (L.pull F) ψ' (fun k _ => j' k) := le j' hj'
      refine (gm_linComb L ψ ε (𝟙 Y) y j j' hj hj').trans
        (Eq.trans (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
          (gm_linComb (L.pull F) ψ' ε g y _ _ m m').symm)
      refine Eq.trans ?_ (gm_pull_g L F (g ≫ ψ' k) y (fun _ => j k) (fun _ => j' k)
        (Set.mem_iInter.1 m k) (Set.mem_iInter.1 m' k)).symm
      rw [Category.assoc, hc k, Category.id_comp] }

theorem sec_eq_of_f {Y : Scheme.{0}} {N : LB Y} {s t : LB.Sec N} (e : s.f = t.f) : s = t := by
  obtain ⟨a, ha⟩ := s
  obtain ⟨b, hb⟩ := t
  cases e
  rfl

theorem pullSec_pullSec {Y Y' : Scheme.{0}} {M : LB Y} {M' : LB Y'} {g : Y ⟶ Y'} {h : Y' ⟶ Y}
    (c' : ChartPull M M' g) (c : ChartPull M' M h) (hh : g ≫ h = 𝟙 Y) (hidx : ∀ j, c.idx (c'.idx j) = j)
    (s : LB.Sec M) : GlobalTheory.SecTwist.pullSec c' (GlobalTheory.SecTwist.pullSec c s) = s := by
  refine sec_eq_of_f (funext fun j => fn_ext fun y hy => ?_)
  have hy' : (𝟙 Y ≫ g) y ∈ M'.U (c'.idx j) := c'.le j hy
  rw [GlobalTheory.SecTwist.gs_pullSec c' _ (𝟙 Y) y j hy, GlobalTheory.SecTwist.gs_pullSec c s (𝟙 Y ≫ g) y _ hy',
    Category.id_comp, hh, hidx j]

theorem gs_liftHom {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} {Z : Scheme.{0}}
    (f : Z ⟶ (T ⊗ A).left) (z : Z) (W : (T ⊗ A).left.Opens) (hz : f z ∈ W) (r : Γ(T.left, ⊤)) :
    gs f z W (liftHom A W r) = gs (f ≫ (fst T A).left) z ⊤ r :=
  (gs_res f z le_top hz _).trans (gs_pull f (fst T A).left z ⊤ trivial _)

def pullLin {S S' Z : Scheme.{0}} (A : Over S) [GrpObj A] (A' : Over S') [GrpObj A'] (L : LB A.left)
    (L' : LB A'.left) (k k' : ℤ) (y : Z ⟶ S) (x : Z ⟶ S') {h : (Over.mk x ⊗ A').left ⟶ (Over.mk y ⊗ A).left}
    (c : ChartPull (LPow A' L' k' (Over.mk x)) (LPow A L k (Over.mk y)) h)
    (hfst : h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) A').left) :
    SecM A L k (Over.mk y) →ₗ[Γ(Z, ⊤)] SecM A' L' k' (Over.mk x) where
  toFun m := SecM.ofSec A' (GlobalTheory.SecTwist.pullSec c (SecM.toSec A m))
  map_add' m₁ m₂ := Subtype.ext (funext fun i => fn_ext fun z hz => by
    have hz' : (𝟙 _ ≫ h) z ∈ (LPow A L k (Over.mk y)).U (c.idx i) := c.le i hz
    show gs (𝟙 _) z _ ((GlobalTheory.SecTwist.pullSec c (SecM.toSec A (m₁ + m₂))).f i) =
      gs (𝟙 _) z _ ((GlobalTheory.SecTwist.pullSec c (SecM.toSec A m₁)).f i +
        (GlobalTheory.SecTwist.pullSec c (SecM.toSec A m₂)).f i)
    rw [gs_add _ z _ hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz,
      GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz]
    exact gs_add _ z _ hz' _ _)
  map_smul' r m := Subtype.ext (funext fun i => fn_ext fun z hz => by
    have hz' : (𝟙 _ ≫ h) z ∈ (LPow A L k (Over.mk y)).U (c.idx i) := c.le i hz
    show gs (𝟙 _) z _ ((GlobalTheory.SecTwist.pullSec c (SecM.toSec A (r • m))).f i) =
      gs (𝟙 _) z _ (liftHom A' _ r * (GlobalTheory.SecTwist.pullSec c (SecM.toSec A m)).f i)
    rw [gs_mul _ z _ hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz]
    refine (gs_mul _ z _ hz' (liftHom A _ r) _).trans (congrArg (· * _) ?_)
    rw [gs_liftHom A _ z _ hz' r, gs_liftHom A' (𝟙 _) z _ hz r, Category.assoc, hfst])

theorem li_span_map {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] {I : Type*} (E : M ≃ₗ[R] M') (v : I → M) (hli : LinearIndependent R v)
    (hsp : Submodule.span R (Set.range v) = ⊤) :
    LinearIndependent R (E ∘ v) ∧ Submodule.span R (Set.range (E ∘ v)) = ⊤ := by
  refine ⟨hli.map' E.toLinearMap E.ker, ?_⟩
  rw [Set.range_comp, ← E.coe_toLinearMap, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]

theorem bases_transfer : ∀ {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (Ag : Over S') [GrpObj Ag] (φ : Ag.left ⟶ A.left) (L : LB A.left), L.IsLB → ∀ (k : ℤ) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (y : Spec (CommRingCat.of R) ⟶ S) (h : (Over.mk x ⊗ Ag).left ⟶ (Over.mk y ⊗ A).left) (hc : ∀ _ : Fin 1, (snd (Over.mk x) Ag).left ≫ φ = h ≫ (snd (Over.mk y) A).left), IsIso h → h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) Ag).left → ∀ (m : ℕ) (b : Fin m → LB.Sec (LPow A L k (Over.mk y))) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) k (Over.mk x))), (∀ i, b' i = GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left) (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) h hc) (b i)) → LinearIndependent Γ((Over.mk y).left, ⊤) (fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) → Submodule.span Γ((Over.mk y).left, ⊤) (Set.range fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) = ⊤ → LinearIndependent Γ((Over.mk x).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) ∧ Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) = ⊤ := by
  intro S S' A _ Ag _ φ L _ k R _ x y h hc _ hfst m b b' hb' hli hsp
  let c := chartPullLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left)
    (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) h hc
  have hc' : ∀ _ : Fin 1, inv h ≫ (snd (Over.mk x) Ag).left ≫ φ = (snd (Over.mk y) A).left := fun _ => by
    rw [hc 0, IsIso.inv_hom_id_assoc]
  let c' := chartPullUnLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left)
    (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) (inv h) hc'
  have hfst' : inv h ≫ (fst (Over.mk x) Ag).left = (fst (Over.mk y) A).left := by
    rw [← hfst, IsIso.inv_hom_id_assoc]
  let F := pullLin A Ag L (L.pull φ) k k y x c hfst
  let G := pullLin Ag A (L.pull φ) L k k x y c' hfst'
  have GF : ∀ s : LB.Sec (LPow A L k (Over.mk y)),
      GlobalTheory.SecTwist.pullSec c' (GlobalTheory.SecTwist.pullSec c s) = s :=
    pullSec_pullSec c' c (IsIso.inv_hom_id h) (fun _ => rfl)
  have FG : ∀ s : LB.Sec (LPow Ag (L.pull φ) k (Over.mk x)),
      GlobalTheory.SecTwist.pullSec c (GlobalTheory.SecTwist.pullSec c' s) = s :=
    pullSec_pullSec c c' (IsIso.hom_inv_id h) (fun _ => rfl)
  let E : SecM A L k (Over.mk y) ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)] SecM Ag (L.pull φ) k (Over.mk x) :=
    { F with
      invFun := G
      left_inv := fun n => congrArg (SecM.ofSec A) (GF (SecM.toSec A n))
      right_inv := fun n => congrArg (SecM.ofSec Ag) (FG (SecM.toSec Ag n)) }
  have hv : (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) =
      E ∘ fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y)) :=
    funext fun i => by rw [hb' i]; rfl
  have key := li_span_map E _ hli hsp
  rw [← hv] at key
  exact key

end GlobalTheory.SecBasisTransfer

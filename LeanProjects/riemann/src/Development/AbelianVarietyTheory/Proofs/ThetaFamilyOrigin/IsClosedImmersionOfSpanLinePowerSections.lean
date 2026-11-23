import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionBySectionsOfSpan
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowSec

open Out in

theorem immBy_down_of_span : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) [Fintype J] (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left), 4 ≤ N → Submodule.span Γ((Out.baseOver (Sp K)).left, ⊤) (Set.range fun a => (Out.SecM.ofSec P.A (t a) : Out.SecM P.A P.L N (Out.baseOver (Sp K)))) = ⊤ → ImmBy P.A.hom (lbPow P.L N) (fun a => PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)) Set.univ := by
  intro h K _ _ P n J _ t ρ ρ₂ hn hspan
  let T : Over (Sp K) := baseOver (Sp K)
  let c : Γ(T.left, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have ρ₁ : ρ ≫ (fst T P.A).left = P.A.hom :=
    ((congrArg (ρ ≫ ·) ((Category.comp_id _).symm.trans pullback.condition)).trans
      (Category.assoc _ _ _).symm).trans ((congrArg (· ≫ P.A.hom) ρ₂).trans (Category.id_comp _))
  have ρ₃ : (snd T P.A).left ≫ ρ = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (pullback.condition.symm.trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  haveI : IsIso ρ := ⟨_, ρ₂, ρ₃⟩
  let b : J → SecM P.A P.L n T := fun a => SecM.ofSec P.A (t a)
  let D : SecM P.A P.L n T → (lbPow P.L n).Sec := fun v =>
    down P.L (snd T P.A).left ρ ρ₂ n (SecM.toSec P.A v)
  have hlin : ∀ (a : J → K) j,
      (D (∑ i, c.symm (a i) • b i)).f j = ∑ i, constFn P.A.hom _ (a i) * (D (b i)).f j := by
    intro a j
    show (ρ.appLE _ _ (chart_eq P.L (snd T P.A).left ρ ρ₂ j).le).hom
      ((∑ i, c.symm (a i) • b i : SecM P.A P.L n T).1 (fun _ => j PUnit.unit)) = _
    rw [Submodule.coe_sum]
    refine (congrArg _ (Finset.sum_apply _ _ _)).trans ?_
    refine (map_sum (ρ.appLE _ _ (chart_eq P.L (snd T P.A).left ρ ρ₂ j).le).hom _ _).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    refine (map_mul _ (liftHom P.A _ (c.symm (a i))) ((b i).1 fun _ => j PUnit.unit)).trans (congrArg₂ (· * ·) ?_ rfl)
    have h1 := (Scheme.Hom.appLE_comp_appLE ρ (fst T P.A).left ⊤ _ _ (fun _ _ => trivial)
      (chart_eq P.L (snd T P.A).left ρ ρ₂ j).le).trans (appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))
    exact congrArg (fun φ => φ.hom (c.symm (a i))) h1
  obtain ⟨m, s, hcov, hs⟩ := veryAmple_lbPow h.ample K P n hn
  have himm : ImmBy P.A.hom (lbPow P.L n) s Set.univ := by
    refine ⟨by simpa only [Set.mem_univ, iSup_pos] using hcov, fun i _ => ?_⟩
    obtain ⟨haff, r, hr, hsurj⟩ := hs i
    refine ⟨haff, r, hr, (SpanImm.closure_eq_top_iff
      (RingHom.comp (P.A.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) r).2 fun f => ?_⟩
    obtain ⟨F, hF⟩ := hsurj f
    exact ⟨F, hF.symm⟩
  haveI := P.isAb.proper
  refine SpanImm.immBy_of_span K _ P.A.hom _ (LB.isLB_linComb P.isLB _ _) _ J s _ himm fun i => ?_
  obtain ⟨w, hw⟩ := down_surjective P.L (snd T P.A).left ρ ρ₂ n (s i)
  have hw' : D (SecM.ofSec P.A w) = s i := hw
  have hm : (SecM.ofSec P.A w : SecM P.A P.L n T) ∈ Submodule.span Γ(T.left, ⊤) (Set.range b) :=
    hspan.ge Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm
  refine ⟨fun i => c (a i), fun j => ?_⟩
  have := hlin (fun i => c (a i)) j
  simp only [RingEquiv.symm_apply_apply] at this
  rw [ha, hw'] at this
  exact this

end GlobalTheory.PowSec

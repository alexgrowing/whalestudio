import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BoxLeOfComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyLinearEquivOfRel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxFamLinearIndependent
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ImportsBis
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalBoxSecGPre
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RankAndGOfIsPowDeg
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsBoxSecKOfPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UniformisationPowerWithoutExpansionStatement

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifPowAdm

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Comb

variable {K : Type} [CommRing K] {Y Y' : Scheme.{0}}

def cstHom (π : Y ⟶ Spec (CommRingCat.of K)) (W : Y.Opens) : K →+* Γ(Y, W) :=
  (Y.presheaf.map (homOfLE le_top).op).hom.comp
    (π.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

theorem res_cstHom (π : Y ⟶ Spec (CommRingCat.of K)) {W W' : Y.Opens} (h : W' ≤ W) (c : K) :
    (Y.presheaf.map (homOfLE h).op).hom (cstHom π W c) = cstHom π W' c :=
  SecOps.resTop_res h _

theorem app_cstHom (π : Y ⟶ Spec (CommRingCat.of K)) (q : Y' ⟶ Y) (W : Y.Opens) (c : K) :
    (q.app W).hom (cstHom π W c) = cstHom (q ≫ π) (q ⁻¹ᵁ W) c := by
  have e := congrArg (fun f => f.hom (scal π c)) (q.naturality (homOfLE (le_top : W ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

def IsComb (π : Y ⟶ Spec (CommRingCat.of K)) {M : LB Y} {Λ : Type} [Fintype Λ] (s : LB.Sec M) (c : Λ → K)
    (t : Λ → LB.Sec M) : Prop :=
  ∀ jj, s.f jj = ∑ l, cstHom π (M.U jj) (c l) * (t l).f jj

variable (π : Y ⟶ Spec (CommRingCat.of K)) {M : LB Y} {Λ Λ' : Type} [Fintype Λ] [Fintype Λ']

theorem exists_isComb (c : Λ → K) (t : Λ → LB.Sec M) : ∃ s, IsComb π s c t :=
  ⟨⟨fun jj => ∑ l, cstHom π (M.U jj) (c l) * (t l).f jj, fun i j => by
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, (t l).compat, res_cstHom, map_mul, res_cstHom, mul_left_comm]⟩, fun _ => rfl⟩

variable {π}

theorem IsComb.trans {s : LB.Sec M} {c : Λ → K} {t : Λ → LB.Sec M} {d : Λ → Λ' → K} {u : Λ' → LB.Sec M}
    (h : IsComb π s c t) (h' : ∀ l, IsComb π (t l) (d l) u) : IsComb π s (fun a => ∑ l, c l * d l a) u := by
  intro jj
  rw [h jj]
  simp only [h' _ jj, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

theorem IsComb.unique {s s' : LB.Sec M} {c : Λ → K} {t : Λ → LB.Sec M}
    (h : IsComb π s c t) (h' : IsComb π s' c t) : s = s' :=
  SecOps.sec_ext fun jj => (h jj).trans (h' jj).symm

end Comb

section Box

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {LG : LB G.left} {LG' : LB G'.left}

theorem prK_snd (pG : IsPowGrp G' G j) (i : Fin j) :
    prK pG i ≫ pullback.snd G.hom (jK R) = pullback.snd G'.hom (jK R) :=
  Over.w ((Over.pullback (jK R)).map (pG.pr i))

theorem box_multilinear (hL : LG.IsLB) (pG : IsPowGrp G' G j) (w : LB.Iso LG' (boxLB LG pG.pr)) (k : ℕ)
    {Λ : Type} [Fintype Λ]
    (σ : Λ → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))))
    (σ' : (Fin j → Λ) →
      LB.Sec (LB.LinComb LG' (K := Fin 1) (fun _ => pullback.fst G'.hom (jK R)) (fun _ => (k : ℤ))))
    (hσ : ∀ a, IsBoxSecK pG w k (σ' a) (fun i => σ (a i)))
    (s : Fin j → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))))
    (s' : LB.Sec (LB.LinComb LG' (K := Fin 1) (fun _ => pullback.fst G'.hom (jK R)) (fun _ => (k : ℤ))))
    (hs : IsBoxSecK pG w k s' s) (c : Fin j → Λ → FractionRing R)
    (hc : ∀ i, IsComb (pullback.snd G.hom (jK R)) (s i) (c i) σ) :
    IsComb (pullback.snd G'.hom (jK R)) s' (fun a => ∏ i, c i (a i)) σ' := by
  classical
  intro jj
  obtain ⟨jL, rfl⟩ : ∃ jL, jj = fun _ => jL := ⟨jj 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  refine fn_ext fun y hy => ?_
  choose jN hN using fun i => exists_chart hL ((pG.pr i).left (pullback.fst G'.hom (jK R) y))
  have hW : (𝟙 (pullback G'.hom (jK R)) : _ ⟶ _) y ∈
      pullback.fst G'.hom (jK R) ⁻¹ᵁ (LB.div (boxLB LG pG.pr) LG').U (jN, jL) :=
    ⟨Set.mem_iInter.2 hN, Set.mem_iInter.1 hy 0⟩
  refine (gs_res _ y (boxSec_le_a pG jN jL) hW _).symm.trans
    (Eq.trans (congrArg _ ?_) (gs_res _ y (boxSec_le_a pG jN jL) hW _))
  refine (Units.mul_right_inj
    ((pullU (Y := pullback G'.hom (jK R)) (pullback.fst G'.hom (jK R)) _ (w.s (jN, jL))) ^ k)).1 ?_
  refine (hs jN jL).trans ?_
  erw [map_sum, Finset.mul_sum]
  have e : ∀ i, ((pullback G'.hom (jK R)).presheaf.map (homOfLE (boxSec_le_b pG jN jL i)).op).hom
      (((prK pG i).app _).hom ((s i).f (fun _ => jN i))) =
      ∑ l, cstHom (pullback.snd G'.hom (jK R)) _ (c i l) *
        ((pullback G'.hom (jK R)).presheaf.map (homOfLE (boxSec_le_b pG jN jL i)).op).hom
          (((prK pG i).app _).hom ((σ l).f (fun _ => jN i))) := fun i => by
    erw [hc i (fun _ => jN i), map_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    erw [map_mul, map_mul, app_cstHom, res_cstHom, prK_snd]
  rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod]
  erw [map_mul, mul_left_comm]
  exact congrArg₂ (· * ·) (res_cstHom _ _ _).symm (hσ a jN jL).symm

end Box

section Exp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ)

theorem expands_comb {Λ : Type} [Fintype Λ] {c : Λ → FractionRing R} {s : Λ → U.SecK k}
    {E : Λ → Fam D.toPre (FractionRing R) k} {s₀ : U.SecK k} (h : ∀ l, U.Expands k (s l) (E l))
    (h₀ : IsComb (pullback.snd G.hom (jK R)) s₀ c s) : U.Expands k s₀ (∑ l, c l • E l) := by
  have e := (Fintype.equivFin Λ).symm
  rw [← e.sum_comp]
  exact ExpandsFracLinear.main R I D A G U k _ (fun l => c (e l)) (fun l => s (e l)) (fun l => E (e l)) s₀
    (fun l => h _) (fun jj => (h₀ jj).trans (e.sum_comp _).symm)

theorem expands_functional (hR : AdmBase R I) {s : U.SecK k} {E E' : Fam D.toPre (FractionRing R) k}
    (h : U.Expands k s E) (h' : U.Expands k s E') : E = E' := by
  have h₀ : U.Expands k SecOps.secZero (∑ l : Fin 2, (![1, -1] : Fin 2 → FractionRing R) l • ![E, E'] l) :=
    expands_comb U k (s := fun _ => s) (fun l => by fin_cases l; exacts [h, h']) (fun jj => by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_neg, map_one, neg_mul, add_neg_cancel]
      rfl)
  have h₁ := GlobalTheory.ExpZero.main R I D A G U k hR _ _ (fun _ => rfl) h₀
  rw [Fin.sum_univ_two] at h₁
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at h₁
  exact add_neg_eq_zero.1 h₁

theorem expBij_of_basis (hR : AdmBase R I) {Λ : Type} [Fintype Λ]
    (b : Module.Basis Λ (FractionRing R) (Fam D.toPre (FractionRing R) k)) (σ : Λ → U.SecK k)
    (hσ : ∀ l, U.Expands k (σ l) (b l)) (hspan : ∀ s, ∃ c, IsComb (pullback.snd G.hom (jK R)) s c σ) :
    U.ExpBij k := by
  refine ⟨fun s => ?_, fun E => ?_⟩
  · obtain ⟨c, hc⟩ := hspan s
    exact ⟨_, expands_comb U k hσ hc, fun E hE => expands_functional U k hR hE (expands_comb U k hσ hc)⟩
  · obtain ⟨s, hs⟩ := exists_isComb (pullback.snd G.hom (jK R)) (b.equivFun E) σ
    refine ⟨s, ?_, fun t ht => ?_⟩
    · have := expands_comb U k hσ hs
      rwa [b.sum_equivFun] at this
    · obtain ⟨c, hc⟩ := hspan t
      have e := expands_functional U k hR ht (expands_comb U k hσ hc)
      have e' : b.equivFun E = c := by rw [e, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
      exact hc.unique (e' ▸ hs)

theorem span_of_expBij (h : U.ExpBij k) {Λ : Type} [Fintype Λ]
    (b : Module.Basis Λ (FractionRing R) (Fam D.toPre (FractionRing R) k)) (σ : Λ → U.SecK k)
    (hσ : ∀ l, U.Expands k (σ l) (b l)) (s : U.SecK k) : ∃ c, IsComb (pullback.snd G.hom (jK R)) s c σ := by
  obtain ⟨E, hE⟩ := (h.1 s).exists
  obtain ⟨t, ht⟩ := exists_isComb (pullback.snd G.hom (jK R)) (b.equivFun E) σ
  have := expands_comb U k hσ ht
  rw [b.sum_equivFun] at this
  exact ⟨_, (h.2 E).unique this hE ▸ ht⟩

end Exp

theorem unifPow_full (hL : Laws) (hL₂ : Laws2) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R)
    (hR : AdmBase R I) : UnifPowSt3 (R := R) (I := I) := by
  intro D A G _ _ U j D' A' G' _ _ pD pA pG
  obtain ⟨U', wL, H⟩ := GlobalTheory.T.uniformisation_power_without_expansion hL.globalFns R I j D D' A A' G G' pD pA pG U.toUnifPre
  have hexp : ∀ k : ℕ, 1 ≤ k → U'.ExpBij k := by
    intro k hk
    classical
    obtain ⟨hf, hd⟩ := GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D (FractionRing R) k hk
    obtain ⟨hf', hd'⟩ := GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D' (FractionRing R) k hk
    obtain ⟨hr, hg⟩ := rank_and_g_of_isPowDeg R j D.toPre D'.toPre pD
    obtain ⟨hex, hsp⟩ := GenericBoxSpan.main hL R I j D D' A A' G G' pD pA pG U' U.toUnifPre wL H k hk
    let b := Module.finBasisOfFinrankEq (FractionRing R) (Fam D.toPre (FractionRing R) k) hd
    choose σ hσ using fun l => ((U.expand k hk).2 (b l)).exists
    choose b' hb' using fun a : Fin j → Fin _ =>
      BoxFamily.exists_isBoxFam hL.globalFns R j D.toPre D'.toPre pD (FractionRing R) k (fun i => b (a i))
    choose σ' hσ' using fun a : Fin j → Fin _ => hex (fun i => σ (a i))
    have hli := boxFam_linearIndependent R j D.toPre D'.toPre pD (FractionRing R) k _ b b.linearIndependent b' hb'
    have hcard : Fintype.card (Fin j → Fin (k ^ (D.toPre.rank + D.toPre.P.g))) =
        Module.finrank (FractionRing R) (Fam D'.toPre (FractionRing R) k) := by
      rw [hd', hr, hg, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul, ← mul_add, mul_comm]
    haveI : Nonempty (Fin (k ^ (D.toPre.rank + D.toPre.P.g))) := ⟨⟨0, pow_pos hk _⟩⟩
    refine expBij_of_basis U' k hR (basisOfLinearIndependentOfCardEqFinrank hli hcard) σ' (fun a => ?_) (fun s₀ => ?_)
    · rw [coe_basisOfLinearIndependentOfCardEqFinrank]
      exact ExpandsBoxPre.main R I j D D' A A' G G' pD pA pG U' U.toUnifPre wL H k _ _ (fun i => hσ (a i)) _ _
        (hσ' a) (hb' a)
    · obtain ⟨n, c, s, s', hs, h₀⟩ := hsp s₀
      choose d hd using fun l i => span_of_expBij U.toUnifPre k (U.expand k hk) b σ hσ (s l i)
      exact ⟨_, IsComb.trans (c := c) (t := s') h₀ fun l =>
        box_multilinear U.LG.isLB pG wL k σ σ' hσ' (s l) (s' l) (hs l) (d l) (hd l)⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := H
  exact ⟨⟨U', hexp⟩, ⟨⟨⟨⟨h₁, wL, h₂, h₃, h₄⟩, h₅⟩, h₆⟩⟩⟩

theorem main : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → UnifPowSt3 (R := R) (I := I) ∧ UnifPowSt2 (R := R) (I := I) ∧ UnifPowSt (R := R) (I := I) := by
  intro hL hL₂ R _ _ I hR
  have h := unifPow_full hL hL₂ R I hR
  refine ⟨h, ?_, ?_⟩
  · intro D A G _ _ U j D' A' G' _ _ pD pA pG
    obtain ⟨U', ⟨P⟩⟩ := h D A G U j D' A' G' pD pA pG
    exact ⟨U', ⟨P.toUnifPowOf2⟩⟩
  · intro D A G _ _ U j D' A' G' _ _ pD pA pG
    obtain ⟨U', ⟨P⟩⟩ := h D A G U j D' A' G' pD pA pG
    exact ⟨U', ⟨P.toUnifPowOf2.toUnifPowOf⟩⟩

end GlobalTheory.UnifPowAdm

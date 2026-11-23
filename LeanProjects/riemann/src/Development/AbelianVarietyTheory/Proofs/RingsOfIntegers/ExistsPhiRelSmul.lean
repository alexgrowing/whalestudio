import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSecPowExt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SpanEqTopOfCard
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSec
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsFSum

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ProdTorsion

open Geo.Tor in

theorem val_scale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (c : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) :
    val (scaleGen c t) r z J = gm r z ⊤ c * val t r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)

open Geo.Tor in

theorem exists_phiRel_smul (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (ζ : F) (hζ : ζ ≠ 0) :
    ∃ w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)), w'.IsGen ∧
      ∀ s t : Fam D F k, PhiRel D F k p w s t → PhiRel D F k p w' s (ζ • t) := by
  let u : Γ((TF (R := R) F).left, ⊤)ˣ :=
    ((Ne.isUnit hζ).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).unit
  have hw' := scaleGen_isGen u w hw
  refine ⟨scaleGen u w, hw', fun s t h => (phiRel_iff hG p _ hw' s _).2 ?_⟩
  intro a' β hβ T ρ z' J hJ
  have h1 := (phiRel_iff hG p w hw s t).1 h a' β hβ T ρ z' J hJ
  have hu : gs (ρ.left ≫ (fst (TF (R := R) F) D.P.A).left) z' ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) =
      (gm (ρ ≫ fst (TF (R := R) F) D.P.A).left z' ⊤ u).val :=
    gs_unit _ z' ⊤ trivial u
  rw [sval_smul ζ t β ρ.left z' hJ, h1, val_mul hJ, val_mul hJ, val_scale hJ, hu]
  simp only [Units.val_mul]
  ring

theorem pow_eq_one_of_pr {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j)
    {T : Over S} (x : T ⟶ G') (k : ℕ) (h : ∀ i, (x ≫ p.pr i) ^ k = 1) : x ^ k = 1 :=
  Fan.IsLimit.hom_ext p.lim _ _ fun i => by
    haveI := p.hom i
    show (x ^ k) ≫ p.pr i = 1 ≫ p.pr i
    rw [MonObj.pow_comp, MonObj.one_comp, h]

theorem equiv_comb {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (f : M ≃ₗ[B] M) {I : Type} [Fintype I]
    (a : I → B) (v : I → M) : f (∑ l, a l • v l) = ∑ l, a l • f (v l) := by
  simp only [map_sum, map_smul]

theorem act_comb (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) (k : ℤ) (T : Over S) (θ : ThetaGrp P.A P.L k T)
    {I : Type} [Fintype I] (a : I → Γ(T.left, ⊤)) (c : Γ(T.left, ⊤)) (t u : I → LB.Sec (LPow P.A P.L k T))
    (t₀ t₁ : LB.Sec (LPow P.A P.L k T)) (h₀ : ∀ jj, t₀.f jj = ∑ l, liftFun P.A _ (a l) * (t l).f jj)
    (hu : ∀ l t', IsActOf P.A P.L k θ (t l) t' → ∀ jj, t'.f jj = liftFun P.A _ c * (u l).f jj)
    (ha : IsActOf P.A P.L k θ t₀ t₁) (jj) : t₁.f jj = ∑ l, liftFun P.A _ (a l * c) * (u l).f jj := by
  obtain ⟨ρ, hρ, -⟩ := thetaGrp_acts_linearly hG _ P k T
  have h0 : SecM.ofSec P.A t₀ = ∑ l, a l • SecM.ofSec P.A (t l) :=
    Subtype.ext (funext fun jj => (h₀ jj).trans
      (BoxSpan.comb_apply P.A P.L k _ _ (fun l => SecM.ofSec P.A (t l)) jj).symm)
  have h1 := (equiv_comb (ρ θ) _ _).symm.trans ((congrArg (ρ θ) h0).symm.trans ((hρ _ _ _).1 ha))
  refine ((congrFun (congrArg Subtype.val h1) jj).symm.trans (BoxSpan.comb_apply P.A P.L k _ _ _ jj)).trans
    (Finset.sum_congr rfl fun l _ => ?_)
  have e := hu l (SecM.toSec P.A (ρ θ (SecM.ofSec P.A (t l)))) ((hρ _ _ _).2 rfl) jj
  refine (congrArg (liftFun P.A _ (a l) * ·) e).trans ((_root_.mul_assoc _ _ _).symm.trans
    (congrArg (· * (u l).f jj) ?_))
  exact (map_mul (liftHom P.A _) _ _).symm

theorem qkToAk_box : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) (P : UnifPowOf3 pD pA pG U' U), Geo.Tor.ExpBijF U.toUnifPre → Geo.Tor.ExpBijF U'.toUnifPre → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (p' : QkPt D'.toPre F k) (p : Fin j → QkPt D.toPre F k), IsBoxQk pD F k p' p → ∀ (x' : TFK (R := R) F ⟶ A'.A) (x : Fin j → (TFK (R := R) F ⟶ A.A)), (∀ i, x' ≫ pA.pr i = x i) → (∀ i, QkToAkU U.toUnifPre F k (p i) (x i)) → QkToAkU U'.toUnifPre F k p' x' := by
  intro hL R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U P hB hB' F _ _ k hk p' p hp x' x hx h w' hw'
  have hG := hL.globalFns
  obtain ⟨w, hw⟩ := U.ext
  have hk1 : x' ^ k = 1 := pow_eq_one_of_pr pA.toIsPowGrp x' k fun i => by
    rw [hx i]; exact (h i w hw).1
  refine ⟨hk1, fun θ' hθ' => ?_⟩
  obtain ⟨θ, c, hc, hθ, hact⟩ := BoxTheta.box_theta_act hL R j A A' pA F k hk θ' (hθ' ▸ hk1)
  choose v hv hΦ using fun i => (h i w hw).2 (θ i) ((hθ i).trans (hθ' ▸ hx i))
  obtain ⟨V, hV, hVΦ⟩ := BoxPhi.phiRel_box hG R j D.toPre D'.toPre pD F k p' p hp v hv
  obtain ⟨Φ, hΦl⟩ := phiFun_of_globalFns hG R I D' F k hk p' V hV
  obtain ⟨V', hV', hV'Φ⟩ := exists_phiRel_smul hG p' V hV c hc
  obtain ⟨c₀, -, hexp⟩ := BoxExpansion.main hG R I j D D' A A' G G' pD pA pG U' U P w hw w' hw' F k
  obtain ⟨ρ, hρ, -⟩ := thetaGrp_acts_linearly hG _ A k (TFK (R := R) F)
  refine ⟨V', hV', fun t₀ t₁ s₀ s₁ e₀ e₁ ha => ?_⟩
  obtain ⟨n, a, t, t', hbox, hsum⟩ := boxProduct_span hL R j A A' pA F k hk t₀
  let u : Fin n → Fin j → LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) :=
    fun l i => SecM.toSec A.A (ρ (θ i) (SecM.ofSec A.A (t l i)))
  have hu : ∀ l i, IsActOf A.A A.L (k : ℤ) (θ i) (t l i) (u l i) := fun l i => (hρ _ _ _).2 rfl
  choose u' hu' using fun l => exists_boxSec_pow_ext R j A A' pA F k (u l)
  choose s hs using fun l i => ((hB F k hk w hw).1 (t l i)).exists
  choose r hr using fun l i => ((hB F k hk w hw).1 (u l i)).exists
  choose S hS using fun l => BoxFamily.exists_isBoxFam hG R j D.toPre D'.toPre pD F k (s l)
  choose S₁ hS₁ using fun l => BoxFamily.exists_isBoxFam hG R j D.toPre D'.toPre pD F k (r l)
  have hSS : ∀ l, S₁ l = Φ (S l) := fun l => (hΦl _ _).1
    (hVΦ (s l) (r l) _ _ (fun i => hΦ i _ _ _ _ (hs l i) (hr l i) (hu l i)) (hS l) (hS₁ l))
  have E₀ := ExpansionLinear.expandsF_sum R I D' A' G' U'.toUnifPre F k w' hw' n a t' (fun l => c₀ • S l) t₀
    (fun l => hexp (t l) (s l) (t' l) (S l) (hs l) (hbox l) (hS l)) hsum
  have hsum₁ := act_comb hG A' k (TFK (R := R) F) θ' (fun l => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a l))
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) t' u' t₀ t₁ hsum
    (fun l t'' h'' => hact (t l) (u l) (t' l) (u' l) t'' (hbox l) (hu' l) (hu l) h'') ha
  have E₁ := ExpansionLinear.expandsF_sum R I D' A' G' U'.toUnifPre F k w' hw' n (fun l => a l * c) u'
    (fun l => c₀ • S₁ l) t₁ (fun l => hexp (u l) (r l) (u' l) (S₁ l) (hr l) (hu' l) (hS₁ l))
    (fun jj => (hsum₁ jj).trans (Finset.sum_congr rfl fun l _ => by rw [map_mul]; rfl))
  have q₀ := ((hB' F k hk w' hw').1 t₀).unique e₀ E₀
  have q₁ := ((hB' F k hk w' hw').1 t₁).unique e₁ E₁
  have q : s₁ = c • Φ s₀ := by
    rw [q₁, q₀, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hSS, map_smul, map_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  rw [q]
  exact hV'Φ _ _ ((hΦl _ _).2 rfl)

end GlobalTheory.ProdTorsion

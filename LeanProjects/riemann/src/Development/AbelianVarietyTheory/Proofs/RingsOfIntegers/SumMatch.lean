import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.MemFinsetInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ESecStruct

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullExpLoc

theorem sum_match {Γ : Type} [CommRing Γ] {K : Type} (S S'' : Finset K) (g : K → K) (hg : Function.Injective g)
    (F T A T' ρ : K → Γ) (ξ : Γ) (hF : ∀ χ, F (g χ) = A χ * (ξ * ρ χ)) (hT : ∀ χ, T (g χ) * ρ χ = T' χ)
    (hoff : ∀ β, (∀ χ, β ≠ g χ) → F β = 0) (h'' : ∀ β ∉ S'', F β = 0) (h : ∀ χ ∉ S, A χ = 0) :
    ∑ β ∈ S'', F β * T β = ξ * ∑ χ ∈ S, A χ * T' χ := by
  classical
  have e₁ : ∑ β ∈ S'', F β * T β = ∑ β ∈ S'' ∪ S.image g, F β * T β :=
    Finset.sum_subset Finset.subset_union_left fun β _ hβ => by rw [h'' β hβ, zero_mul]
  have e₂ : ∑ β ∈ S.image g, F β * T β = ∑ β ∈ S'' ∪ S.image g, F β * T β :=
    Finset.sum_subset Finset.subset_union_right fun β _ hβ => by
      by_cases hx : ∃ χ, β = g χ
      · obtain ⟨χ, rfl⟩ := hx
        rw [hF, h χ fun hχ => hβ (Finset.mem_image_of_mem g hχ), zero_mul, zero_mul]
      · rw [hoff β fun χ e => hx ⟨χ, e⟩, zero_mul]
  rw [e₁, ← e₂, Finset.sum_image fun x _ y _ e => hg e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [hF, ← hT]
  ring

theorem tG_lin (hGF : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
    {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    {ιD : D.OAct O} {ιA : A.OAct O} {ιG : RingAct G O} (hlin : U.OLinear O ιD ιA ιG) (e : ℕ) (a : O)
    (u : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))
    (hu : u.IsGen)
    (hu0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (χ : D.toPre.X) {Z : Scheme.{0}} (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J)
    (hJ : Geo.Tor.Good D.toPre.P.L z J) :
    Geo.Tor.val (tG U e (star a • χ)) r z J *
      Geo.Tor.val (LB.pullGen D.toPre.P.L _ _ u (lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A)).left)
        (r ≫ pGl U e) z J =
      Geo.Tor.val (tG U e χ) (r ≫ ((Over.pullback (thick R I e)).map (ιG.act a)).left) z J := by
  have H := Geo.Tor.val_corr hJ (TLinPf.tLin_of hGF R I O D A G U ιD ιA ιG hlin e a u hu hu0 χ) r
  have E : (U.gt e).pG ≫ lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A) =
      lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG := by
    rw [comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
  have E' : (r ≫ pGl U e) ≫ (lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A)).left =
      r ≫ (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left :=
    (Category.assoc _ _ _).trans (congrArg (fun q => r ≫ q.left) E)
  refine Eq.trans ?_ (H.trans (Geo.Tor.val_pull hJ _ _ r))
  refine Eq.trans ?_ (Geo.Tor.val_mul hJ _ _ r).symm
  refine congrArg _ ?_
  refine (Geo.Tor.val_pull hJ _ _ _).trans (Eq.trans ?_ (Geo.Tor.val_pull hJ _ _ r).symm)
  rw [E']

theorem main : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (X : LB.Gen (LB.LinComb P.D.toPre.P.L (K := Fin 2) ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])), ∀ uR : LB.Gen (LB.LinComb P.D.toPre.P.L (rosatiφ P.D.toPre.P.A (P.oD.onB.act (star a)) (P.oD.onB.act a)) rosatiε), uR.IsGen → LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ uR (zero2 P.D.toPre.P.A)) (LB.oneGen P.D.toPre.P.L) → ∀ (e k : ℕ) (σ'' : H0 P.U.LG.L (k * N)) (τ : H0 P.U.LG.L k) (f'' : ∀ α : P.D.toPre.X, P.D.toPre.SecB (k * N) α) (f : ∀ α : P.D.toPre.X, P.D.toPre.SecB k α), P.U.ExpandsAt e (k * N) σ'' f'' → P.U.ExpandsAt e k τ f → ((∀ (χ : P.D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ P.D.toPre.P.A.left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → Geo.Tor.sval (f'' (star a • χ)) r z J = Geo.Tor.sval (f χ) (r ≫ (P.oD.onB.act a).left) z J * (Geo.Tor.val X r z J ^ k * Geo.Tor.val (LB.pullGen P.D.toPre.P.L _ _ uR (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c χ) (𝟙 P.D.toPre.P.A)).left) r z J).val) ∧ ∀ β : P.D.toPre.X, (∀ χ, β ≠ star a • χ) → ∀ j, (f'' β).f j = 0) → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (maximalIdeal V) e t.G).left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → ∀ jL jL', (r ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL → ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL' → (wv P.U.toUnifPre e r z (J (r ≫ pGl P.U.toUnifPre e)) jL ^ (k * N)).val * sv P.U.toUnifPre (k * N) σ'' (r ≫ fGl (maximalIdeal V) t.G e) z jL = (Geo.Tor.val X (r ≫ pGl P.U.toUnifPre e) z J ^ k).val * ((wv P.U.toUnifPre e (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z (J ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e)) jL' ^ k).val * sv P.U.toUnifPre k τ ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z jL')) := by
  intro hGF V _ _ _ E _ _ _ H t P a N hN hN0 X uR huR huR0 e k σ'' τ f'' f h'' hf hrel Z r z J hJ jL jL' hL hL'
  letI := H.starRing
  obtain ⟨S'', hS''⟩ := expandsAt_val P.U.toUnifPre e (k * N) σ'' f'' h''
  obtain ⟨S, hS⟩ := expandsAt_val P.U.toUnifPre e k τ f hf
  obtain ⟨a₁, a₂⟩ := hS'' Z r z J hJ
  obtain ⟨b₁, b₂⟩ := hS Z (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z J hJ
  have hp : (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e =
      (r ≫ pGl P.U.toUnifPre e) ≫ (P.oD.onB.act a).left :=
    (Category.assoc _ _ _).trans ((congrArg (fun q => r ≫ q) (pG_act P.U.toUnifPre P.lin e a)).trans
      (Category.assoc _ _ _).symm)
  refine (a₂ jL hL).trans (Eq.trans ?_ (congrArg _ (b₂ jL' hL')).symm)
  refine sum_match S S'' (fun χ => star a • χ) (fun _ _ h => smul_star_inj a N hN hN0 h) _ _ _ _
    (fun χ => (Geo.Tor.val (LB.pullGen P.D.toPre.P.L _ _ uR
      (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c χ) (𝟙 P.D.toPre.P.A)).left) (r ≫ pGl P.U.toUnifPre e) z J).val) _
    (fun χ => ?_) (fun χ => ?_) (fun β hβ => ?_) a₁ b₁
  · rw [hp]
    exact (hrel.1 χ Z _ z J hJ).trans (congrArg _ (Units.val_mul _ _))
  · exact (Units.val_mul _ _).symm.trans
      (congrArg Units.val (tG_lin hGF P.U.toUnifPre P.lin e a uR huR huR0 χ r z J hJ))
  · exact (congrArg (Geo.Tor.gs _ z _) (hrel.2 β hβ _)).trans (gs_zero _ z _ (hJ.mem _ _))

end GlobalTheory.PullExpLoc

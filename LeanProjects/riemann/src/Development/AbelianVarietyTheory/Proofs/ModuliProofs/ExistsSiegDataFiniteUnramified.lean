import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClassifyingFiniteUnramified

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegClause

theorem lbIso_pull_pull {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {φ : X' ⟶ X} (h : LBIso L' (L.pull φ))
    (ψ : X'' ⟶ X') : LBIso (L'.pull ψ) (L.pull (ψ ≫ φ)) :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L' ψ ψ rfl) (chartPullSame L _ _ _ ψ fun _ => rfl) h

theorem lbIso_lam_pull {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (e : A ⟶ B) [IsMonHom e] {L : LB A.left} {M : LB B.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso L (M.pull e.left)) : LBIso (abelian₂ A L) ((abelian₂ B M).pull (e ⊗ₘ e).left) := by
  have pa : ∀ I : Finset (Fin 2), psum A (x2 A) I ≫ e = (e ⊗ₘ e) ≫ psum B (x2 B) I := by
    intro I
    refine (psum_hom (MonoidHom.mk' (fun z : G2 A ⟶ A => z ≫ e) fun a b => MonObj.mul_comp a b _) _ I).trans
      (Eq.trans (congrArg (fun z => psum B z I) (funext fun k => ?_)) (psum_hom (preHom (e ⊗ₘ e)) _ I).symm)
    fin_cases k
    · exact (tensorHom_fst e e).symm
    · exact (tensorHom_snd e e).symm
  have hB : (abelian₂ B M).IsLB := DVR.linComb_isLB M hM _ _
  have r : LBIso (abelian₂ B M) (abelian₂ B M) := GlobalTheory.PolBaseChange.lbIso_refl hB
  have h₁ : LBIso (abelian₂ A L) (abelian₂ A (M.pull e.left)) := GlobalTheory.PowPrimitive.lbIso_linComb h _ _
  have h₂ : LBIso (abelian₂ A (M.pull e.left)) ((abelian₂ B M).pull (e ⊗ₘ e).left) :=
    LBIso.chartPull (chartPullLinComb M e.left (K := ULift.{0} (Finset (Fin 2)))
      (fun I => (psum A (x2 A) I.down).left) (fun I => (psum B (x2 B) I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) (e ⊗ₘ e).left (fun I => congrArg (fun z => z.left) (pa I.down)))
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (abelian₂ B M) _ _ rfl) r
  exact LBIso.trans (DVR.linComb_isLB L hL _ _) (DVR.linComb_isLB _ (pull_isLB hM _) _ _) (pull_isLB hB _) h₁ h₂

theorem eq_of_basis {κ La Γ : Type} [Fintype κ] [DecidableEq κ] [AddCommGroup La] [CommGroup Γ]
    (bas : (κ → ℤ) ≃ₗ[ℤ] La) (F F' : La → Γ) (hF : ∀ x y, F (x + y) = F x * F y)
    (hF' : ∀ x y, F' (x + y) = F' x * F' y) (h : ∀ i, F (bas (Pi.single i 1)) = F' (bas (Pi.single i 1))) : F = F' := by
  let G : La →+ Additive Γ := AddMonoidHom.mk' (fun x => Additive.ofMul (F x)) fun x y => congrArg _ (hF x y)
  let G' : La →+ Additive Γ := AddMonoidHom.mk' (fun x => Additive.ofMul (F' x)) fun x y => congrArg _ (hF' x y)
  have e : G.toIntLinearMap ∘ₗ bas.toLinearMap = G'.toIntLinearMap ∘ₗ bas.toLinearMap :=
    (Pi.basisFun ℤ κ).ext fun i => by
      rw [Pi.basisFun_apply]
      exact congrArg Additive.ofMul (h i)
  funext x
  obtain ⟨y, rfl⟩ := bas.surjective x
  exact Additive.ofMul.injective (LinearMap.congr_fun e y)

theorem mul_of_isGrpPullback {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [GrpObj G']
    {f : B' ⟶ B} {φ : G'.left ⟶ G.left} (H : IsGrpPullback G' G f φ) (x y z : 𝟙_ (Over B') ⟶ G')
    (x₀ y₀ : 𝟙_ (Over B) ⟶ G) (hx : x.left ≫ φ = f ≫ x₀.left) (hy : y.left ≫ φ = f ≫ y₀.left)
    (hz : z.left ≫ φ = f ≫ (x₀ * y₀).left) : z = x * y := by
  let U : Over.mk ((𝟙_ (Over B')).hom ≫ f) ⟶ 𝟙_ (Over B) := Over.homMk f (by simp)
  have e := H.2 (𝟙_ (Over B')) x y (U ≫ x₀) (U ≫ y₀) hx.symm hy.symm
  rw [← MonObj.comp_mul] at e
  refine Over.OverMorphism.ext (H.1.hom_ext (hz.trans e) ?_)
  rw [Over.w, Over.w]

theorem exists_siegData_finite_unramified : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (ρ : o), Odd k → 3 ≤ k → (∃ N' : ℕ, k = N' ^ 2) → em ρ = H.rt0 → em (b.ζ : o) = zeta k → ArBase em → ∀ (X : Scheme.{0}) (s : X ⟶ Sp o) (t : TObj g k J b s) (τ : SAB H X), PELRep D a bas ρ t → IsPEL D a bas ρ t τ → ∀ (p : ℕ) (Ag : SiegelFamily g p k), p.Prime → k.Coprime p → SRep Ag → ∀ (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), (∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y) → ∀ lev : D.La → (𝟙_ (Over X) ⟶ τ.G), LevUnder D a bas t τ lev → ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p k →+* O) (bb : o →+* O), Function.Injective i → GlobalTheory.Models.IsInc (ZP p k).subtype i z → GlobalTheory.Models.IsInc em i bb → ∀ (T : Scheme.{0}) (sT : T ⟶ Sp O) (f : T ⟶ X) (tT : SAB H T) (ν : SABMap tT τ f) (levT : D.La → (𝟙_ (Over T) ⟶ tT.G)), IsPullback f sT s (spMap bb) → (∀ x, (levT x).left ≫ ν.φ = f ≫ (lev x).left) → ∃ u : T ⟶ pullback Ag.s (spMap z), GlobalTheory.Models.SiegData sT tT levT Ag z bas' u ∧ IsFinite u ∧ FormallyUnramified u := by
  intro hL hL2 hTh E _ _ _ H D g J _ a w w' bas hpq hbas hw hw' hcl k o _ b em ρ hodd h3 hsq hρ hζ hAr X s t τ hrep hpel
    p Ag hp hkp hS bas' hbas' lev hlev O _ i z bb hi hz hbb T sT f tT ν levT hpb hlevT
  obtain ⟨t', ht'⟩ := GlobalTheory.tObj_pull o g k J b X T s (sT ≫ spMap bb) f t hpb.w
  obtain ⟨c, u, hc, hu, hpbS, hfin, hunr⟩ := GlobalTheory.SiegelClassify.exists_classifying_finite_unramified hL hL2 hTh E H D g J a w w' bas hpq hbas hw hw' hcl k o b em ρ
    hodd h3 hsq hρ hζ hAr X s t τ hrep hpel p Ag hp hkp hS bas' hbas' O i z bb hi hz hbb T sT f hpb t' ht'
  refine ⟨u, ?_, hfin, hunr⟩
  obtain ⟨ψ, hψ, hψL, hψp, -⟩ := ht'
  obtain ⟨φ₀, hφ₀, hφL, -, hadd, hφp⟩ := hlev
  letI := t'.ab.comm
  obtain ⟨χ, hχ, hχL, hχp⟩ := hc
  have hcart : IsGrpPullback tT.G t.A f (ν.φ ≫ φ₀.hom.left) :=
    (ν.cart.comp (isGrpPullback_of_iso φ₀)).congr (Category.comp_id _) rfl
  obtain ⟨e, he, hee⟩ := grpPullback_iso hψ hcart
  have hν : LBIso tT.PP.L (τ.PP.L.pull ν.φ) := ν.lin.imp fun _ h => h.1
  have h₁ : LBIso tT.PP.L (t.L.pull (ν.φ ≫ φ₀.hom.left)) :=
    LBIso.trans tT.PP.isLB (pull_isLB τ.PP.isLB _) (pull_isLB t.isLB _) hν (lbIso_pull_pull hφL _)
  have h₂ : LBIso t'.L (tT.PP.L.pull e.hom.left) := by
    have := lbIso_pull_pull h₁ e.hom.left
    rw [hee] at this
    exact LBIso.trans t'.isLB (pull_isLB t.isLB _) (pull_isLB tT.PP.isLB _) hψL this.symm
  have h₃ := lbIso_pull_pull (lbIso_lam_pull e.hom t'.isLB tT.PP.isLB h₂) (χ.hom ⊗ₘ χ.hom).left
  have hm : IsMonHom (χ ≪≫ e).hom := inferInstanceAs (IsMonHom (χ.hom ≫ e.hom))
  have haddT : ∀ x y, levT (x + y) = levT x * levT y := fun x y =>
    mul_of_isGrpPullback ν.cart _ _ _ (lev x) (lev y) (hlevT x) (hlevT y) (by rw [← hadd]; exact hlevT _)
  have key : (fun x => c.lev (bas'.symm x) ≫ χ.hom ≫ e.hom) = levT := by
    refine eq_of_basis bas _ _ (fun x y => ?_) haddT fun j => ?_
    · rw [map_add, c.lev_add, MonObj.mul_comp]
    · refine Over.OverMorphism.ext (hcart.1.hom_ext ?_ (by rw [Over.w, Over.w]))
      have q₁ : (levT (bas (Pi.single j 1))).left ≫ ν.φ ≫ φ₀.hom.left = f ≫ (t.pt j).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ₀.hom.left) (hlevT _)).trans
          ((Category.assoc _ _ _).trans (congrArg (f ≫ ·) (hφp j))))
      have q₂ : (c.lev (bas'.symm (bas (Pi.single j 1))) ≫ χ.hom).left ≫ e.hom.left ≫ ν.φ ≫ φ₀.hom.left =
          f ≫ (t.pt j).left := by
        rw [hee, hχp]
        exact hψp j
      refine Eq.trans ?_ (q₂.trans q₁.symm)
      simp only [Over.comp_left, Category.assoc]
  refine ⟨c, (χ ≪≫ e).hom.left, (χ.hom ⊗ₘ χ.hom).left ≫ (e.hom ⊗ₘ e.hom).left, isGrpPullback_of_iso _, ⟨?_, ?_⟩,
    LBIso.trans c.isLB (pull_isLB (DVR.linComb_isLB _ t'.isLB _ _) _) (pull_isLB (DVR.linComb_isLB _ tT.PP.isLB _ _) _)
      hχL h₃, fun v => ?_, hu, hpbS⟩
  · rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left]
    simp
  · rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left]
    simp
  · rw [← key]
    simp

end GlobalTheory.ZM.SiegClause

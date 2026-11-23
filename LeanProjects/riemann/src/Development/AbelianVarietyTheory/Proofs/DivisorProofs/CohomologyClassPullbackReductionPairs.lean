import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePullbackIffPreimageAffineHomStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

section PairNat

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' Y Y' : Scheme.{0}}
  {φ : X' ⟶ X} {χ : Y' ⟶ Y} {ψ : Y ⟶ X} {ψ' : Y' ⟶ X'}

theorem pre_le_pre (e : ψ' ≫ φ = χ ≫ ψ) {V : Y.Opens} {U : X.Opens} (hp : V ≤ ψ ⁻¹ᵁ U) :
    χ ⁻¹ᵁ V ≤ ψ' ⁻¹ᵁ (φ ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, e, Scheme.Hom.comp_preimage]
  exact fun x hx ↦ hp hx

variable [IsAffineHom φ] [IsAffineHom χ]

def prePairMap (e : ψ' ≫ φ = χ ≫ ψ) (p : Pair ψ) : Pair ψ' :=
  ⟨(preU χ p.1.1, preU φ p.1.2), pre_le_pre e p.2⟩

theorem prePairMap_mono (e : ψ' ≫ φ = χ ≫ ψ) : Monotone (prePairMap e) := fun _ _ h ↦
  show _ ∧ _ from ⟨preU_mono χ (Pair.le_fst h), preU_mono φ (Pair.le_snd h)⟩

def preFun (e : ψ' ≫ φ = χ ≫ ψ) : (Pair ψ)ᵒᵖ ⥤ (Pair ψ')ᵒᵖ := (prePairMap_mono e).functor.op

variable {s' : X' ⟶ Sp R'} {q' : Y' ⟶ Sp R'}

variable (s' q') in

def preCoefPair (e : ψ' ≫ φ = χ ≫ ψ) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) :
    CoefMap (RingHom.id R') (OPre φ s') (pairFst ψ ⋙ OPre χ q') where
  G := pairSnd ψ
  α p := secPull s' q' (prePairMap e p.unop)
  naturality a b := (pairPull w').naturality ((preFun e).map a) b
  smul p := semiHom_secPull w' (prePairMap e p.unop)

end PairNat

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem red_preimage_pairs : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X X' Y Y' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (φ : X' ⟶ X) (χ : Y' ⟶ Y) [IsAffineHom χ] (h : φ ≫ s = s' ≫ spMap σ) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')), ψ' ≫ φ = χ ≫ ψ → IsAffineHom φ → (∀ (f : C1 (OAff s)) (x : HO1 s'), Red1 h f x → ∃ c : Z1 (pairFst ψ ⋙ OPre χ q'), (∀ a b (u : a ⟶ b), c.1 a b u = preα χ q q' ((pairFst ψ).obj b) ((pairPull w).α b (f _ _ ((pairPull w).G.map u)))) ∧ GlobalTheory.CatCoh.H1.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 (pullHO1 w' x)) ∧ ∀ (v : C2 (OAff s)) (z : HO2 s'), Red2 h v z → ∃ c : Z2 (pairFst ψ ⋙ OPre χ q'), (∀ a b d (u : a ⟶ b) (u' : b ⟶ d), c.1 a b d u u' = preα χ q q' ((pairFst ψ).obj d) ((pairPull w).α d (v _ _ _ ((pairPull w).G.map u) ((pairPull w).G.map u')))) ∧ GlobalTheory.CatCoh.H2.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 (pullHO2 w' z) := by
  intro R R' _ _ σ X X' Y Y' s s' q q' φ χ _ h ψ ψ' w w' e hφ
  haveI := hφ
  have H := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h
  let m := preCoefPair s' q' e w'
  let Φ := preFun (φ := φ) (χ := χ) e
  have hα : ∀ (p : (Pair ψ)ᵒᵖ) (b : (OAff s).obj ((pairSnd ψ).obj p)),
      m.α p (preα φ s s' ((pairSnd ψ).obj p) b) =
        preα χ q q' ((pairFst ψ).obj p) ((pairPull w).α p b) := by
    intro p b
    have k1 := congrArg (fun t ↦ t.hom b) (Scheme.Hom.appLE_comp_appLE ψ' φ _ _ _
      (prePair φ p.unop.1.2).2 (prePairMap e p.unop).2)
    have k2 := congrArg (fun t ↦ t.hom b) (Scheme.Hom.appLE_comp_appLE χ ψ _ _ _
      p.unop.2 (prePair χ p.unop.1.1).2)
    have k3 : ∀ (g₁ g₂ : Y' ⟶ X) (_ : g₁ = g₂) (h1 : (preU χ p.unop.1.1).1 ≤ g₁ ⁻¹ᵁ p.unop.1.2.1)
        (h2 : (preU χ p.unop.1.1).1 ≤ g₂ ⁻¹ᵁ p.unop.1.2.1) (x : Γ(X, p.unop.1.2.1)),
        (g₁.appLE _ _ h1).hom x = (g₂.appLE _ _ h2).hom x := by
      rintro _ _ rfl _ _ _; rfl
    refine k1.trans (Eq.trans ?_ k2.symm)
    exact k3 _ _ e _ _ b
  let θ1 : ((preRes φ s').comp m).G ⟶ ((pairPull w').comp (CoefMap.restrict (OPair ψ' q') Φ)).G :=
    { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ Subsingleton.elim _ _ }
  let θ2 : ((pairRes ψ' q').comp (CoefMap.restrict (OPair ψ' q') Φ)).G ⟶
      (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).G :=
    { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ Subsingleton.elim _ _ }
  have h1 : ∀ T b, ((pairPull w').comp (CoefMap.restrict (OPair ψ' q') Φ)).α T
      (mp (OAff s') (θ1.app T) b) = ((preRes φ s').comp m).α T b := fun T b ↦ by
    exact congrArg (((pairPull w').comp (CoefMap.restrict (OPair ψ' q') Φ)).α T) (mp_id (OAff s') _ b)
  have h2 : ∀ T b, (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).α T
      (mp (OAff q') (θ2.app T) b) = ((pairRes ψ' q').comp (CoefMap.restrict (OPair ψ' q') Φ)).α T b :=
    fun T b ↦ by
      exact congrArg ((CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).α T) (mp_id (OAff q') _ b)
  refine ⟨fun f x hr ↦ ?_, fun v z hr ↦ ?_⟩
  · obtain ⟨c0, hc0, hcl⟩ := (H.1 f x).1 hr
    refine ⟨m.pullbackOneCocycle c0, fun a b u ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleOne_apply, hc0]; exact hα b _
    · rw [← CoefMap.pullCohomologyOne_class, hcl, ← CoefMap.pullCohomologyOne_comp]
      exact (CoefMap.pullCohomologyOne_eq_of_natTrans _ _ θ1 h1 x).trans ((CoefMap.pullCohomologyOne_comp _ _ x).trans
        ((congrArg _ (isPullO_pullHO1 w' x)).trans ((CoefMap.pullCohomologyOne_comp _ _ _).symm.trans
          (CoefMap.pullCohomologyOne_eq_of_natTrans _ _ θ2 h2 _))))
  · obtain ⟨c0, hc0, hcl⟩ := (H.2.1 v z).1 hr
    have k : (pairRes ψ' q').pull2 (pullHO2 w' z) = (pairPull w').pull2 z :=
      (LinearEquiv.ofBijective _ (pairRes_pull2_bijective ψ' q')).apply_symm_apply _
    refine ⟨m.pullbackTwoCocycle c0, fun a b d u u' ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleTwo_apply, hc0]; exact hα d _
    · rw [← CoefMap.pullCohomologyTwo_class, hcl, ← CoefMap.pullCohomologyTwo_comp]
      exact (CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ θ1 h1 z).trans ((CoefMap.pullCohomologyTwo_comp _ _ z).trans
        ((congrArg _ k.symm).trans ((CoefMap.pullCohomologyTwo_comp _ _ _).symm.trans
          (CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ θ2 h2 _))))

end GlobalTheory.AbCoh

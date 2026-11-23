import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ThetaRep

theorem finrank_secM (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {n : ℕ}
    (hn : 1 ≤ n) {F : Type} [Field F] (q : Spec (CommRingCat.of F) ⟶ S) :
    Module.finrank Γ((Over.mk q).left, ⊤) (SecM P.A P.L n (Over.mk q)) = n ^ P.g := by
  obtain ⟨U, hU, b, hb⟩ := hS S P n hn (q (IsLocalRing.closedPoint F))
  have hr : Set.range q ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    obtain rfl : y = IsLocalRing.closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
    exact ⟨⟨_, hU⟩, rfl⟩
  let t : Spec (CommRingCat.of F) ⟶ (overRes (T := baseOver S) U).left := IsOpenImmersion.lift U.ι q hr
  have ht : t ≫ (overRes (T := baseOver S) U).hom = q := by
    show IsOpenImmersion.lift U.ι q hr ≫ (U.ι ≫ 𝟙 _) = q
    rw [Category.comp_id, IsOpenImmersion.lift_fac]
  have pull : ∀ i, ∃ b' : LB.Sec (LPow P.A P.L n (baseAt t)),
      IsPullSec P.A P.L n (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i) b' := fun i => by
    obtain ⟨s', hs'⟩ := IndivisibleSection.exists_pull_chart (K := Fin 1) (b i) (homAt t ▷ P.A).left
      (fun _ => (snd (baseAt t) P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A))
    exact ⟨s', fun j => hs' j _⟩
  choose b' hb' using pull
  obtain ⟨h₁, h₂⟩ := hb F t b' hb'
  rw [← ht]
  haveI : Nontrivial Γ((baseAt t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  exact (Module.finrank_eq_card_basis (Module.Basis.mk h₁ h₂.ge)).trans (Fintype.card_fin _)

theorem eq_one_of_weilIs (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {F : Type} [Field F]
    [IsAlgClosed F] (q : Spec (CommRingCat.of F) ⟶ S) {n : ℕ} (hn : (n : F) ≠ 0) (x : Over.mk q ⟶ P.A)
    (hx : x ^ n = 1) (h : ∀ y : Over.mk q ⟶ P.A, y ^ n = 1 → WeilIs P.A P.L n x y 1) : x = 1 := by
  obtain ⟨P', g, hg, -, hm, t, ht⟩ := hL.polBaseChange S _ q P
  have hp : IsGrpPullback P'.A P.A q g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hm]
    rfl⟩
  obtain ⟨w, hw⟩ := LBIso.symm (⟨t, ht⟩ : LBIso _ _)
  let ρ : Over.mk q ⟶ Over.mk (𝟙 _ ≫ q) := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
  let Φ : (baseOver (Spec (CommRingCat.of F)) ⟶ P'.A) →* (Over.mk q ⟶ P.A) :=
    MonoidHom.mk' (fun y => ρ ≫ toBase hg.w y) (fun a b => by rw [hm, MonObj.comp_mul])
  have hΦ : ∀ y, (Φ y).left = y.left ≫ g := fun y => Category.id_comp _
  have inj : Function.Injective Φ := fun a b e => Over.OverMorphism.ext (hg.hom_ext
    ((hΦ a).symm.trans ((congrArg CommaMorphism.left e).trans (hΦ b))) ((Over.w a).trans (Over.w b).symm))
  let x' : baseOver (Spec (CommRingCat.of F)) ⟶ P'.A :=
    Over.homMk (hg.lift x.left (𝟙 _) ((Over.w x).trans (Category.id_comp q).symm)) (hg.lift_snd _ _ _)
  have ex : Φ x' = x := Over.OverMorphism.ext ((hΦ x').trans (hg.lift_fst _ _ _))
  have hx' : x' ^ n = 1 := inj (by rw [map_pow, ex, hx, map_one])
  have := hL.weilNondeg F P' n hn x' hx' fun y hy =>
    (GlobalTheory.weilIs_grpPullback_iff hL.globalFns hL.cube P P' hp w hw (t := q) (t' := 𝟙 _) (Category.id_comp q).symm n x' y hx' hy x (Φ y)
      ((congrArg CommaMorphism.left ex).symm.trans (hΦ x')) (hΦ y) 1).1 (h _ (by rw [← map_pow, hy, map_one]))
  rw [← ex, this, map_one]

theorem exists_projective_rep : Laws → Laws2 → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), (N : F) ≠ 0 → ∃ (Φ : {x : Over.mk p ⟶ P.A // x ^ N = 1} → (SecM P.A P.L N (Over.mk p) ≃ₗ[Γ((Over.mk p).left, ⊤)] SecM P.A P.L N (Over.mk p))) (e : {x : Over.mk p ⟶ P.A // x ^ N = 1} → {x : Over.mk p ⟶ P.A // x ^ N = 1} → Γ((Over.mk p).left, ⊤)ˣ), Module.finrank Γ((Over.mk p).left, ⊤) (SecM P.A P.L N (Over.mk p)) = N ^ P.g ∧ (∀ a, ∃ θ : ThetaGrp P.A P.L N (Over.mk p), θ.pt = a.1 ∧ ∀ v, IsActOf P.A P.L N θ (SecM.toSec P.A v) (SecM.toSec P.A (Φ a v))) ∧ (∀ a b c, c.1 = a.1 * b.1 → ∃ r : Γ((Over.mk p).left, ⊤)ˣ, ∀ v, Φ c v = r.val • Φ a (Φ b v)) ∧ (∀ a b, WeilIs P.A P.L N a.1 b.1 (e a b) ∧ ∀ v, Φ a (Φ b v) = (e a b).val • Φ b (Φ a v)) ∧ ∀ a, (∀ b, e a b = 1) → a.1 = 1) := by
  intro hL _ S _ P F _ _ p N hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 fun e => hN (by rw [e, Nat.cast_zero])
  haveI : Subsingleton (Over.mk p).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  haveI : Nonempty (Over.mk p).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of F)))
  obtain ⟨ρ, hact, hcomm, hrat, hmul⟩ := thetaGrp_acts_linearly hL.globalFns S P N (Over.mk p)
  choose θ hθ using fun a : {x : Over.mk p ⟶ P.A // x ^ N = 1} =>
    BoxTheta.exists_theta hL.kerPow P hN1 (T := Over.mk p) a.1 a.2
  choose e he using fun a b : {x : Over.mk p ⟶ P.A // x ^ N = 1} =>
    ((hL.weil S P N (Over.mk p)).1 a.1 b.1 a.2 b.2).exists
  refine ⟨fun a => ρ (θ a), e, finrank_secM hL.secBaseChange P hN1 p,
    fun a => ⟨θ a, hθ a, fun v => (hact _ _ _).2 rfl⟩, fun a b c hc => ?_, fun a b => ⟨he a b, ?_⟩, fun a ha => ?_⟩
  · obtain ⟨θ', h₁, h₂⟩ := hmul (θ a) (θ b)
    obtain ⟨r, hr⟩ := hrat θ' (θ c) (by rw [h₁, hθ, hθ, hθ, hc])
    exact ⟨r, fun v => by rw [← h₂]; exact hr v⟩
  · refine hcomm _ _ _ ((GlobalLift.weilIs_iff_commIsOf hL.globalFns P.isAb P.isLB _ _ _).1 ?_)
    rw [hθ, hθ]
    exact he a b
  · exact eq_one_of_weilIs hL P p hN a.1 a.2 fun y hy => ha ⟨y, hy⟩ ▸ he a ⟨y, hy⟩

end GlobalTheory.ThetaRep

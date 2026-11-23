import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRepresentativesModNsmul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfEq
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FamEqOnClassOfEq
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFie
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralFamilyPrescribedTermUnitAtPrime
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralFamiliesSpanPullDegeneration

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamGen

open GlobalTheory.FamSpan GlobalTheory.FieldBaseChange

theorem constVal_mul {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a b : R) :
    constVal q z (a * b) = constVal q z a * constVal q z b := by
  rw [constVal, map_mul, gs_mul q z ⊤ trivial]; rfl

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem comb_term {S : Type} [CommRing S] (σ : R →+* S) (ιF : S →+* F)
    (ρ : TF (R := R) F ⟶ Over.mk (specOf σ)) (hρ : ρ.left = specOf ιF) (k : ℕ) (α : D.X) {m : ℕ}
    (b g : Fin m → D.SecB k α)
    (hb : IsSecBasis (T := Over.mk (specOf σ)) (A := D.P.A) _ (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k)
      (b i) (snd (Over.mk (specOf σ)) D.P.A).left))
    (r : Fin m → R) (hr : ∀ i, IsUnit (σ (r i)))
    (hg : ∀ i j, (g i).f j = resTop _ (scal D.P.A.hom (r i)) * (b i).f j)
    (G : Fin m → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (hG : ∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (G i) (D.famφB α)
      (DegPre.famε k) (g i) (DegPre.prB D F).left 1)
    (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (sg : LB.Sec (LB.LinComb D.P.L (fun i => (snd (Over.mk (specOf σ)) D.P.A).left ≫ D.famφB α i) (DegPre.famε k)))
    (hsg : GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) s
      (fun i => (snd (Over.mk (specOf σ)) D.P.A).left ≫ D.famφB α i) (DegPre.famε k) sg (ρ ▷ D.P.A).left 1) :
    ∃ c : Fin m → S, ∀ j, s.f j = ∑ i, resTop _ (DVR.gF D F (ιF (c i))) * (G i).f j := by
  obtain ⟨c, hc, -⟩ := hb sg
  choose u hu using fun i => (hr i).exists_left_inv
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i) * u i,
    IntegralCoord.lin_of_sval D.P.isLB _ G fun y J hJ => ?_⟩
  have a₁ : (𝟙 _ ≫ (ρ ▷ D.P.A).left) ≫ (snd (Over.mk (specOf σ)) D.P.A).left = 𝟙 _ ≫ (DegPre.prB D F).left := by
    rw [Category.assoc, ← Over.comp_left, whiskerRight_snd]
  have a₂ : (𝟙 _ ≫ (ρ ▷ D.P.A).left) ≫ (fst (Over.mk (specOf σ)) D.P.A).left =
      (𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) ≫ specOf ιF := by
    rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, hρ, Category.assoc]
  have a₃ : (𝟙 _ ≫ (DegPre.prB D F).left) ≫ D.P.A.hom =
      ((𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) ≫ specOf ιF) ≫ specOf σ := by
    rw [← a₂, ← a₁]
    simp only [Category.assoc]
    rw [Over.w (snd (Over.mk (specOf σ)) D.P.A)]
    exact congrArg _ (congrArg _ (Over.w (fst (Over.mk (specOf σ)) D.P.A)).symm)
  rw [← secScal_sval hsg _ y hJ]
  refine (sval_lin (fun i => scal (fst (Over.mk (specOf σ)) D.P.A).left
    ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i))) _ (fun j => (hc j).trans (Finset.sum_congr rfl fun i _ =>
      congrArg₂ (· * ·) (congrArg _ (congrArg _ (Iso.hom_inv_id_apply _ _).symm)) rfl)) _ y hJ).trans
    (Finset.sum_congr rfl fun i _ => ?_)
  have e₃ : sval (g i) (𝟙 _ ≫ (DegPre.prB D F).left) y J =
      gs (𝟙 _ ≫ (DegPre.prB D F).left) y ⊤ (scal D.P.A.hom (r i)) * sval (b i) (𝟙 _ ≫ (DegPre.prB D F).left) y J := by
    have hm := hJ.mem (D.famφB α) (𝟙 _ ≫ (DegPre.prB D F).left)
    exact (congrArg (gs _ y _) (hg i _)).trans ((gs_mul _ y _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hm _) rfl))
  have e₄ : gs (𝟙 _) y ⊤ (DVR.gF D F (ιF ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i) * u i))) =
      constVal (𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) y
        (ιF ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i) * u i)) :=
    gs_scal (fst (TF (R := R) F) D.P.A).left _ y _
  rw [sval_pullSec _ _ _ _ _ y hJ, a₁, ← secScal_sval (hG i) _ y hJ, e₃, e₄, gs_scal, gs_scal, a₂, a₃,
    constVal_specMap, constVal_specMap, constVal_specMap, ← _root_.mul_assoc, ← constVal_mul, ← map_mul,
    _root_.mul_assoc _ (u i), hu, _root_.mul_one]

theorem zero_term {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ψ : K → (Y' ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} {g : LB.Sec (LB.LinComb L φ ε)} (hg : ∀ j, g.f j = 0)
    {G : LB.Sec (LB.LinComb L ψ ε)} (hG : GeneratorPullback.SecScal L ψ ε G φ ε g h 1) (j) : G.f j = 0 := by
  refine sec_ext_val hL (s' := DVR.SecOps.secZero) (fun y J hJ => ?_) j
  rw [← secScal_sval hG _ y hJ, DVR.UUA.sval_zero_of hg _ y J (hJ.mem _ _),
    DVR.UUA.sval_zero_of (s := DVR.SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]

open DVR in

theorem exists_span_generate : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R), AdmBase R I → ∀ (φ : R →+* R') (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg φ D.toPre D') (k : ℕ), 1 ≤ k → ∃ (n : ℕ) (F₀ : Fin n → Fam D.toPre (FractionRing R) k) (f : Fin n → ∀ α, D.toPre.SecB k α) (F₁ : Fin n → Fam D' (FractionRing R') k) (f' : Fin n → ∀ α, D'.SecB k α), (∀ i, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((F₀ i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) ((F₁ i).s α) (D'.famφB α) (DegPre.famε k) (f' i α) (DegPre.prB D' (FractionRing R')).left 1) ∧ (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) z (LB.wchart D.toPre.P.L (D.toPre.famφB (hD.xe x)) p) ((f i (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' i x).f q)))) ∧ Submodule.span (FractionRing R') (Set.range F₁) = ⊤ ∧ (∀ (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] (σ : R →+* S) (F : Type) [Field F] [Algebra (FractionRing R) F] (ιF : S →+* F), Function.Injective ιF → ∀ (ρ : TF (R := R) F ⟶ (Over.mk (specOf σ))), ρ.left = specOf ιF → ∀ (F' : Type) [Field F'] [Algebra (FractionRing R') F'] (π : S →+* F'), IsLocalHom π → (∀ r : R, π (σ r) = algebraMap (FractionRing R') F' (algebraMap R' (FractionRing R') (φ r))) → ∀ s : Fam D.toPre F k, (∃ g : ∀ α, LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k)), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) (g α) (ρ ▷ D.toPre.P.A).left 1)) → ∃ c : Fin n → S, ∀ α, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (D.toPre.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (ιF (c i)))) := by
  intro hP hG hT R R' _ _ _ _ I hA φ D D' hD k hk
  classical
  have : IsNoetherianRing R := hA.1
  let pt : (TK R').left := genericPoint (Spec (CommRingCat.of (FractionRing R')))
  let P : Spec (CommRingCat.of R) := (jK R' ≫ specOf φ) pt
  have hPW : P ∈ hD.W := by
    show (jK R' ≫ specOf φ) pt ∈ hD.W
    rw [← hD.g_comm]
    exact (hD.g pt).2
  have hne : ∀ r : R, r ∉ P.asIdeal → algebraMap R' (FractionRing R') (φ r) ≠ 0 := fun r hr h => hr (by
    show algebraMap R' (FractionRing R') (φ r) ∈ PrimeSpectrum.asIdeal pt
    rw [h]; exact Ideal.zero_mem _)
  have hgen : genericPoint (Spec (CommRingCat.of R)) ∈ hD.W :=
    (genericPoint_specializes P).mem_open hD.W.isOpen hPW
  have := P.isPrime
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D'.X k hk
  choose b hb using fun α => GlobalTheory.TwistLoc.exists_basis_off_prime hP hG hT R D.toPre ⟨hD.W, hgen, ⟨hD.psiW⟩⟩ P.asIdeal k hk α
  choose r hr F f hF hfρ hf0 using fun q : Fin (k ^ Module.finrank ℤ D'.X) × Fin (k ^ D.toPre.P.g) =>
    integralFamily_at_prime hG R I hA D hD.W ⟨hD.psiW⟩ P hPW k hk (hD.xe (e q.1)) (b (hD.xe (e q.1)) q.2)
  choose f' hf' using fun q x => (SecPull.existsUnique_secPull _ _ _ _ D.toPre.P.L D'.P.L _ D.toPre.P.isLB D'.P.isLB
    hD.w hD.w_gen (Fin 4) (D'.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) _ (famφB_comm hD x)
    (f q (hD.xe x))).exists
  choose F' hF' using fun q => exists_fam_of_isPullDeg hG R R' φ D.toPre D' hD k (F q) (f q) (f' q) (hF q) (hf' q)
  let en := (finProdFinEquiv (m := k ^ Module.finrank ℤ D'.X) (n := k ^ D.toPre.P.g)).symm
  have hoff : ∀ i i' l, i' ≠ i → ∀ j, (f (i', l) (hD.xe (e i))).f j = 0 := fun i i' l hi =>
    hf0 (i', l) _ fun mu hmu => hi ((he (e i)).unique ⟨hD.xe.symm mu, hD.xe.injective (by
      rw [map_add, map_nsmul, AddEquiv.apply_symm_apply]; exact hmu.symm)⟩ ⟨0, by rw [smul_zero, add_zero]⟩)
  refine ⟨_, fun i => F (en i), fun i => f (en i), fun i => F' (en i), fun i => f' (en i),
    fun i => ⟨hF _, hF' _, hf' _⟩, ?_, ?_⟩
  · have hrange : Set.range (fun i => F' (en i)) = Set.range F' := en.surjective.range_comp F'
    rw [hrange, eq_top_iff]
    rintro s -
    choose c hc using fun i => span_term hD k (e i) (b (hD.xe (e i))) (fun l => f (i, l) (hD.xe (e i)))
      (hb _ _ _ (fun t ht => (hne t ht).isUnit) _ (fun _ _ => rfl)) (fun l => r (i, l)) (fun l => hne _ (hr (i, l)))
      (fun l => hfρ (i, l)) (fun l => f' (i, l) (e i))
      (fun l y J J' hJ hJ' => val_of_rel (famφB_comm hD (e i)) (hf' (i, l) (e i)) _ y hJ hJ')
      (fun l => (F' (i, l)).s (e i)) (fun l => hF' (i, l) (e i)) (s.s (e i))
    have hs : s = ∑ q : Fin (k ^ Module.finrank ℤ D'.X) × Fin (k ^ D.toPre.P.g), c q.1 q.2 • F' q := by
      refine fam_ext fun χ j => ?_
      obtain ⟨i, ⟨m, rfl⟩, -⟩ := he χ
      refine fam_eq_on_class_of_eq hG R' D' _ k s _ (e i) (fun j => ?_) m j
      rw [sum_f, Fintype.sum_prod_type, Finset.sum_eq_single i, hc i j]
      · rfl
      · intro i' _ hi
        refine Finset.sum_eq_zero fun l _ => ?_
        have h0 := zero_sec D.toPre.P.isLB D'.P.isLB (DegPre.prB D' (FractionRing R')).left (f (i', l) (hD.xe (e i)))
          (hoff i i' l hi) (f' (i', l) (e i))
          (fun y J J' hJ hJ' => val_of_rel (famφB_comm hD (e i)) (hf' (i', l) (e i)) _ y hJ hJ')
          ((F' (i', l)).s (e i)) (hF' (i', l) (e i)) j
        rw [smul_f, h0, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hs]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  · rintro S _ _ _ σ E _ _ ιE - ρ hρ E' _ _ π hπ hπσ s ⟨sg, hsg⟩
    have hun : ∀ t : R, t ∉ P.asIdeal → IsUnit (σ t) := fun t ht => hπ.map_nonunit _ (by
      rw [hπσ]
      exact ((hne t ht).isUnit).map _)
    choose θ hθ using fun q => FamBaseChange.main hG R I D k (F q) (f q) (hF q) E
    choose c hc using fun i => comb_term σ ιE ρ hρ k (hD.xe (e i)) (b (hD.xe (e i))) (fun l => f (i, l) (hD.xe (e i)))
      (hb _ _ _ hun _ (fun _ _ => rfl)) (fun l => r (i, l)) (fun l => hun _ (hr (i, l))) (fun l => hfρ (i, l))
      (fun l => (θ (i, l)).s (hD.xe (e i))) (fun l => hθ (i, l) _) (s.s (hD.xe (e i))) (sg _) (hsg _)
    have hs : s = ∑ q : Fin (k ^ Module.finrank ℤ D'.X) × Fin (k ^ D.toPre.P.g), ιE (c q.1 q.2) • θ q := by
      refine fam_ext fun χ j => ?_
      obtain ⟨i, ⟨m, hm⟩, -⟩ := he (hD.xe.symm χ)
      obtain rfl : χ = hD.xe (e i) + k • hD.xe m := by
        rw [← map_nsmul, ← map_add, ← hm, AddEquiv.apply_symm_apply]
      refine fam_eq_on_class_of_eq hG R D.toPre _ k s _ (hD.xe (e i)) (fun j => ?_) _ j
      rw [sum_f, Fintype.sum_prod_type, Finset.sum_eq_single i, hc i j]
      · rfl
      · intro i' _ hi
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [smul_f, zero_term D.toPre.P.isLB (hoff i i' l hi) (hθ (i', l) _) j, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [← en.sum_comp] at hs
    refine ⟨fun i => c (en i).1 (en i).2, fun α => (secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_⟩
    refine (sval_lin (fun i => gF D.toPre E (ιE (c (en i).1 (en i).2))) (fun i => (θ (en i)).s α)
      (fun j => (congrArg (fun t : Fam D.toPre E k => (t.s α).f j) hs).trans (sum_f _ _ α j)) _ y hJ).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    rw [secScal_sval (hθ (en i) α) _ y hJ]
    rfl

end GlobalTheory.FamGen

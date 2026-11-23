import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyPerfectSectionsComplexOfNoetherianStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.SecAdicSum

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw

theorem sumI_of_ker {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) {a b : ℕ}
    (A : Matrix (Fin b) (Fin a) R) {E Ix : Type} [AddCommGroup E] [Module R E] (ev : (Fin a → R) →ₗ[R] E)
    (v : Ix → Fin a → R) (v₀ : Fin a → R) (hv : ∀ i, A.mulVec (v i) = 0) (hv₀ : A.mulVec v₀ = 0)
    (h : ∀ e : ℕ, ∃ S : Finset Ix, ∀ T : Finset Ix, S ⊆ T → ∀ k, (v₀ - ∑ i ∈ T, v i) k ∈ I ^ (e + 1)) :
    SumI I (fun i => ev (v i)) (ev v₀) := by
  let N : Submodule R (Fin a → R) := LinearMap.ker A.mulVecLin
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I N
  refine ⟨N.map ev, (IsNoetherian.noetherian N).map ev, ⟨v₀, hv₀, rfl⟩, fun i => ⟨v i, hv i, rfl⟩, fun n => ?_⟩
  obtain ⟨S, hS⟩ := h (n + c)
  refine ⟨S, fun T hT => ?_⟩
  have m₁ : v₀ - ∑ i ∈ T, v i ∈ N := N.sub_mem hv₀ (N.sum_mem fun i _ => hv i)
  have m₂ : v₀ - ∑ i ∈ T, v i ∈ I ^ (n + c) • (⊤ : Submodule R (Fin a → R)) := by
    rw [pi_eq_sum_univ (v₀ - ∑ i ∈ T, v i)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul
      (Ideal.pow_le_pow_right (Nat.le_succ _) (hS T hT k)) Submodule.mem_top
  have m₃ := (hc (n + c) (Nat.le_add_left _ _)).le ⟨m₂, m₁⟩
  rw [Nat.add_sub_cancel] at m₃
  rw [← map_sum, ← map_sub, ← Submodule.map_smul'']
  exact ⟨_, Submodule.smul_mono le_rfl inf_le_right m₃, rfl⟩

section
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X}
  (P : Perf f M)

theorem exists_vec (s : LB.Sec M) :
    ∃ v : Fin P.a → R, P.D₀.mulVec v = 0 ∧ ∀ i, AbLaw.rs X (P.le i) (s.f (P.ch i)) = loc₀ P v i := by
  have h : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E, hE⟩ := P.sec R (RingHom.id R) X (𝟙 X) f h
  have le : ∀ j : PUnit → M.ι, (M.pull (𝟙 X)).U j ≤ M.U (j PUnit.unit) := fun j y hy =>
    Set.mem_iInter.1 hy PUnit.unit
  let t : LB.Sec (M.pull (𝟙 X)) := ⟨fun j => AbLaw.rs X (le j) (s.f (j PUnit.unit)), fun j j' => fn_ext fun y hy => by
    have hm : y ∈ M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit) := ⟨le j hy.1, le j' hy.2⟩
    refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y _ hy.1 _)).trans (Eq.trans ?_
      ((gs_mul (𝟙 X) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans
        (congrArg Units.val (gm_linComb M _ _ (𝟙 X) y j j' hy.1 hy.2)))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y _ hy.2 _)))).symm)
    rw [Fintype.prod_unique, zpow_one]
    exact (gs_res (𝟙 X) y _ hm _).symm.trans ((congrArg (gs (𝟙 X) y _) (s.compat _ _)).trans
      ((gs_mul (𝟙 X) y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 X) y _ hm _) (gs_res (𝟙 X) y _ hm _))))⟩
  obtain ⟨v, hv⟩ := E.surjective t
  refine ⟨v.1, v.2, fun i => ?_⟩
  have e := hE v i
  rw [hv] at e
  exact (AbLaw.rs_rs _ _ _).symm.trans e

theorem comp_eq_zero {g : R →+* R'} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
    (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) (v : Fin P.a → R) (hv : P.D₀.mulVec v = 0)
    (h0 : ∀ i y, π y ∈ P.W i → gs π y _ (loc₀ P v i) = 0) : g ∘ v = 0 := by
  obtain ⟨E, hE⟩ := P.sec R' g X' π f' h
  have k₁ : (P.D₀.map g).mulVec (g ∘ v) = 0 := funext fun j =>
    (RingHom.map_mulVec g _ _ j).symm.trans ((congrArg g (congrFun hv j)).trans (map_zero g))
  refine congrArg Subtype.val (E.injective (a₁ := ⟨_, k₁⟩) (a₂ := ⟨0, Matrix.mulVec_zero _⟩) ?_)
  refine Seesaw.sec_ext _ _ (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.ch i) (fun i => le_pull M π (P.le i))
    (fun y => exists_mem P (π y)) fun i => ?_
  refine (hE _ i).trans (Eq.trans ?_ (hE _ i).symm)
  refine (loc_comp P h v i).trans (Eq.trans (fn_ext (b := 0) fun y hy => ?_) (by simp))
  refine (gs_pull (𝟙 X') π y _ hy _).trans ?_
  rw [Category.id_comp, h0 i y hy, gs_eq (𝟙 X') y (π ⁻¹ᵁ P.W i) hy, map_zero, map_zero]

theorem loc₀_sub_sum {Ix : Type} (v₀ : Fin P.a → R) (v : Ix → Fin P.a → R) (T : Finset Ix) (i : P.I) :
    loc₀ P (v₀ - ∑ j ∈ T, v j) i = loc₀ P v₀ i - ∑ j ∈ T, loc₀ P (v j) i := by
  simp only [loc₀, Pi.sub_apply, Finset.sum_apply, map_sub, map_sum, sub_mul, Finset.sum_mul,
    Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

end

section
variable {X Y Z : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {φ : K → (X ⟶ Y)} {ε : K → ℤ} {R : Type} [CommRing R]
  {f : X ⟶ Spec (CommRingCat.of R)} (P : Perf f (LB.LinComb L φ ε))

theorem gs_loc₀ {s : LB.Sec (LB.LinComb L φ ε)} {v : Fin P.a → R}
    (h : ∀ i, AbLaw.rs X (P.le i) (s.f (P.ch i)) = loc₀ P v i) (r : Z ⟶ X) (z : Z) {i : P.I} (hi : r z ∈ P.W i)
    {J : (Z ⟶ Y) → L.ι} (hJ : Good L z J) :
    gs r z _ (loc₀ P v i) = (trF φ ε r z (P.ch i) fun k => J (r ≫ φ k)).val * sval s r z J := by
  rw [← h i]
  exact (gs_res r z (P.le i) hi _).trans (sec_trans s r z (P.le i hi) (hJ.mem φ r))

end

theorem gs_cst_point {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    {B : Over (Spec (CommRingCat.of R))} (b : TF (R := R) F ⟶ B) (z : (TF (R := R) F).left) (W : B.left.Opens)
    (hz : b.left z ∈ W) (c : R) : gs b.left z W (AbLaw.cst B.hom W c) =
      CoefBasic.cstH z (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) c)) := by
  have w : b.left ≫ B.hom = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom
      ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
    rw [Over.w b, Category.id_comp, CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  rw [gs_eq b.left z W hz, app_cst w W c]
  exact TopCat.Presheaf.germ_res_apply (TF (R := R) F).left.presheaf _ z hz _

theorem sumF_of_sum_on_thickenings : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (ε : K → ℤ) (Ix : Type) (n : Ix → LB.Sec (LB.LinComb D.toPre.P.L φ ε)) (n₀ : LB.Sec (LB.LinComb D.toPre.P.L φ ε)), (∀ e : ℕ, ∃ S : Finset Ix, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J → (∀ i ∉ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J = 0) ∧ sval n₀ (r ≫ (D.toPre.prBe I e).left) z J = ∑ i ∈ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J) → ∀ (b : TF (R := R) F ⟶ D.toPre.P.A) (τ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => b.left ≫ φ i) ε)), τ.IsGen → ∀ (x : Ix → F) (x₀ : F), (∀ z J, Good D.toPre.P.L z J → (∀ i, sval (n i) b.left z J = cst F z (x i) * (val τ (𝟙 _) z J).val) ∧ sval n₀ b.left z J = cst F z x₀ * (val τ (𝟙 _) z J).val) → SumF I F x x₀ := by
  intro _ R _ _ _ I hR D F _ _ _ K _ φ ε Ix n n₀ hS b τ _ x x₀ hx
  have := hR.1
  have := D.toPre.P.isAb.smooth
  have hL := D.toPre.P.isLB
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_noetherian R _ D.toPre.P.A.hom inferInstance
    (GlobalTheory.AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ (LB.isLB_linComb hL φ ε)
  choose v hv hv' using fun i => exists_vec P (n i)
  obtain ⟨v₀, hv₀, hv₀'⟩ := exists_vec P n₀
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' hL z
  obtain ⟨i₀, hi₀⟩ := exists_mem P (b.left z)
  let t := trF φ ε b.left z (P.ch i₀) (fun k => J (b.left ≫ φ k)) * val τ (𝟙 _) z J
  choose y hy using fun k => CoefBasic.cstH_surj z (gs b.left z _ (P.u k i₀) * (t⁻¹).val)
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  let ev : (Fin P.a → R) →ₗ[R] F := Fintype.linearCombination R y
  have key : ∀ (s : LB.Sec (LB.LinComb D.toPre.P.L φ ε)) (w : Fin P.a → R) (c : F),
      (∀ i, AbLaw.rs _ (P.le i) (s.f (P.ch i)) = loc₀ P w i) →
      sval s b.left z J = UT.cst F z c * (val τ (𝟙 _) z J).val → c = ev w := fun s w c h₁ h₂ => by
    have e := gs_loc₀ P h₁ b.left z hi₀ hJ
    rw [h₂, mul_left_comm, ← Units.val_mul, CoefBasic.cst_eq] at e
    refine CoefBasic.cstH_inj (R := R) z ?_
    have e' : CoefBasic.cstH z c = gs b.left z _ (loc₀ P w i₀) * (t⁻¹).val :=
      (Units.eq_mul_inv_iff_mul_eq t).2 e.symm
    have hs : ∀ a : Fin P.a → Γ(D.toPre.P.A.left, P.W i₀), gs b.left z _ (∑ k, a k) = ∑ k, gs b.left z _ (a k) :=
      fun a => by simp only [gs_eq b.left z _ hi₀, map_sum]
    rw [e', loc₀, hs, Finset.sum_mul]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (map_sum _ (fun k => w k • y k) _).symm
    rw [gs_mul b.left z _ hi₀, gs_cst_point b z _ hi₀, _root_.mul_assoc, ← hy, ← map_mul, ← Algebra.smul_def]
    rfl
  obtain rfl : x = fun i => ev (v i) := funext fun i => key _ _ _ (hv' i) ((hx z J hJ).1 i)
  obtain rfl : x₀ = ev v₀ := key _ _ _ hv₀' (hx z J hJ).2
  refine sumI_of_ker I P.D₀ ev v v₀ hv hv₀ fun e => ?_
  obtain ⟨S, hS⟩ := hS e
  refine ⟨S, fun T hT k => Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (comp_eq_zero P
    (IsPullback.of_hasPullback D.toPre.P.A.hom (thick R I e)) (v₀ - ∑ i ∈ T, v i) ?_ fun i p hp => ?_) k)⟩
  · simp only [Matrix.mulVec_sub, Matrix.mulVec_sum, hv, hv₀, Finset.sum_const_zero, sub_zero]
  · obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' hL p
    obtain ⟨h₁, h₂⟩ := hS _ (𝟙 _) p J' hJ'
    rw [Category.id_comp] at h₁ h₂
    have h₃ := h₂.trans (Finset.sum_subset hT fun j _ hj => h₁ j hj)
    have e₀ := gs_loc₀ P hv₀' _ p hp hJ'
    have e₁ := fun j => gs_loc₀ P (hv' j) _ p hp hJ'
    rw [gs_eq _ p _ hp] at e₀
    simp only [gs_eq _ p _ hp] at e₁
    rw [loc₀_sub_sum, gs_eq _ p _ hp, map_sub, map_sub, map_sum, map_sum, e₀, Finset.sum_congr rfl fun j _ => e₁ j,
      ← Finset.mul_sum]
    exact sub_eq_zero.2 (congrArg _ h₃)

end GlobalTheory.SecAdicSum

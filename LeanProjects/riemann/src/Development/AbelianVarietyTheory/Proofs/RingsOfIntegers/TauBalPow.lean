import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RatioTrans

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TauBalBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D D' : DegPre R}

theorem tau_val (D : DegPre R) {Z : Scheme.{0}} {y : Z} {J} (hJ : Good D.P.L y J) (p q : D.X) (r : Z ⟶ (TK R).left) :
    val (D.tau p q) r y J = val (D.psi (p + q)) r y J * (val (D.psi p) r y J)⁻¹ * (val (D.psi q) r y J)⁻¹ *
      (val D.rigK r y J)⁻¹ := by
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv]

private theorem inv_mul_mul_mul_inv_mul_eq_commGroup {G : Type*} [CommGroup G] (A B C E a b c e : G) :
    A⁻¹ * B * C * E⁻¹ * (a * b⁻¹ * c⁻¹ * e⁻¹) = A⁻¹ * a * (B⁻¹ * b)⁻¹ * (C⁻¹ * c)⁻¹ * (E * e)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem tau_box (pD : IsPowDeg D' D j) {y : (TK R).left} {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J')
    (p q : D'.X) :
    ((om pD.w y J J' (cP D' (TK R) p * cP D' (TK R) q).left)⁻¹ * om pD.w y J J' (cP D' (TK R) p).left *
      om pD.w y J J' (cP D' (TK R) q).left *
      (om pD.w y J J' (𝟙 _ ≫ (toUnit (TK R)).left ≫ eSec D'.P.A))⁻¹) * val (D'.tau p q) (𝟙 _) y J' =
      ∏ i, val (D.tau (pD.xe p i) (pD.xe q i)) (𝟙 _) y J := by
  have hc : ∀ x : D'.X, 𝟙 _ ≫ D'.xK x = (cP D' (TK R) x).left := fun x => by
    simp only [Category.id_comp, DegPre.xK, ptK, cP]
  have hpq : cP D' (TK R) (p + q) = cP D' (TK R) p * cP D' (TK R) q := by
    unfold cP
    rw [D'.c_add, padd, comp_lift_assoc]
    rfl
  have h1 := psi_val pD hJ hJ' (p + q) (𝟙 _)
  have h2 := psi_val pD hJ hJ' p (𝟙 _)
  have h3 := psi_val pD hJ hJ' q (𝟙 _)
  have h4 := rig_val pD hJ hJ' (𝟙 _)
  rw [hc, hpq] at h1
  rw [hc] at h2 h3
  have e : ∀ i, val (D.tau (pD.xe p i) (pD.xe q i)) (𝟙 _) y J =
      val (D.psi (pD.xe (p + q) i)) (𝟙 _) y J * (val (D.psi (pD.xe p i)) (𝟙 _) y J)⁻¹ *
        (val (D.psi (pD.xe q i)) (𝟙 _) y J)⁻¹ * (val D.rigK (𝟙 _) y J)⁻¹ := fun i => by
    rw [tau_val D hJ, map_add, Pi.add_apply]
  rw [Finset.prod_congr rfl (fun i _ => e i), Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_inv_distrib, Finset.prod_inv_distrib, ← h1, ← h2,
    ← h3, ← h4, tau_val D' hJ' p q (𝟙 _)]
  exact inv_mul_mul_mul_inv_mul_eq_commGroup _ _ _ _ _ _ _ _

theorem rosatiφ_pr {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (π : A' ⟶ A) [IsMonHom π] {f g : A ⟶ A} {f' g' : A' ⟶ A'} (hf : f' ≫ π = π ≫ f) (hg : g' ≫ π = π ≫ g)
    (a : Fin 6) : rosatiφ A' f' g' a ≫ π.left = (π ⊗ₘ π).left ≫ rosatiφ A f g a := by
  fin_cases a <;>
    simp [rosatiφ, padd, ← Over.comp_left, comp_lift_assoc, IsMonHom.mul_hom, lift_map_assoc, hf, hg,
      tensorHom_fst_assoc, tensorHom_snd_assoc, tensorHom_fst, tensorHom_snd]

private theorem mul_eq_of_four_relations_commGroup {G : Type*} [CommGroup G] (X1 X2 X3 X4 LinearSubstitution X6 Eo t1 t2 U P1 P2 PU : G)
    (hT1 : X1⁻¹ * X2 * X3 * Eo⁻¹ * t1 = P1) (hT2 : X4⁻¹ * LinearSubstitution * X6 * Eo⁻¹ * t2 = P2)
    (hBU : X1 * X2⁻¹ * X3⁻¹ * X4⁻¹ * LinearSubstitution * X6 * U = PU) (hB : P1 * PU = P2) : t1 * U = t2 := by
  subst hT1 hBU hB
  apply mul_left_cancel (a := X4⁻¹ * LinearSubstitution * X6 * Eo⁻¹)
  rw [hT2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem mul_inv_inv_inv_mul_mul_eq_one {G : Type*} [CommGroup G] (x : G) : x * x⁻¹ * x⁻¹ * x⁻¹ * x * x = 1 := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem tauBal_pow : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (f g : D.P.A ⟶ D.P.A) (f' g' : D'.P.A ⟶ D'.P.A), IsMonHom f → IsMonHom g → IsMonHom f' → IsMonHom g' → (∀ i, f' ≫ pD.pw.pr i = pD.pw.pr i ≫ f) → (∀ i, g' ≫ pD.pw.pr i = pD.pw.pr i ≫ g) → RosatiAdj D.P.A D.P.L f g → ∀ (a a' : D.X → D.X) (b b' : D'.X → D'.X), (∀ x i, pD.xe (b x) i = a (pD.xe x i)) → (∀ x i, pD.xe (b' x) i = a' (pD.xe x i)) → (∀ y, D.c (a y) = D.c y ≫ f) → (∀ y, D.c (a' y) = D.c y ≫ g) → D.TauBal f g a a' → D'.TauBal f' g' b b' := by
  intro hG R _ _ j D D' pD f g f' g' hfm hgm hfm' hgm' hf hg hr a a' b b' hb hb' ca ca' hB
  have hcb : ∀ x, cP D' (TK R) x ≫ f' = cP D' (TK R) (b x) := fun x => by
    unfold cP
    rw [Category.assoc]
    congr 1
    refine pD.pw.lim.hom_ext (fun k => ?_)
    rcases k with ⟨i⟩
    simp only [Fan.mk_π_app, Category.assoc, hf i, pD.c_pr, ← reassoc_of% (pD.c_pr x i), hb, ca]
  have hcb' : ∀ x, cP D' (TK R) x ≫ g' = cP D' (TK R) (b' x) := fun x => by
    unfold cP
    rw [Category.assoc]
    congr 1
    refine pD.pw.lim.hom_ext (fun k => ?_)
    rcases k with ⟨i⟩
    simp only [Fan.mk_π_app, Category.assoc, hg i, pD.c_pr, ← reassoc_of% (pD.c_pr x i), hb', ca']
  unfold DegPre.TauBal
  intro u' hu' h0' y y'
  obtain ⟨u, hu, h0⟩ := exists_ros hG D.P.isAb D.P.isLB f g hr
  apply corr_of_val D'.P.isLB
  intro z J' hJ'
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB z
  rw [val_mul hJ', val_pull hJ', Category.id_comp]
  have T1 := tau_box pD hJ hJ' (b y) y'
  have T2 := tau_box pD hJ hJ' y (b' y')
  have HB : ∀ i, val (D.tau (pD.xe (b y) i) (pD.xe y' i)) (𝟙 _) z J *
      val u (D.pt2 (pD.xe y i) (pD.xe y' i)) z J = val (D.tau (pD.xe y i) (pD.xe (b' y') i)) (𝟙 _) z J := fun i => by
    rw [hb, hb']
    have := val_corr hJ (hB u hu h0 (pD.xe y i) (pD.xe y' i)) (𝟙 _)
    rwa [val_mul hJ, val_pull hJ, Category.id_comp] at this
  have hpt : ∀ i, D'.pt2 y y' ≫ (pD.pw.pr i ⊗ₘ pD.pw.pr i).left = D.pt2 (pD.xe y i) (pD.xe y' i) := fun i => by
    show (lift (cP D' (TK R) y) (cP D' (TK R) y')).left ≫ _ = (lift (cP D (TK R) _) (cP D (TK R) _)).left
    rw [← Over.comp_left, lift_map, cPoint_pr pD, cPoint_pr pD]
  have hψ : ∀ i k, rosatiφ D'.P.A f' g' k ≫ (pD.pw.pr i).left =
      (pD.pw.pr i ⊗ₘ pD.pw.pr i).left ≫ rosatiφ D.P.A f g k := fun i k => by
    have := pD.pw.hom i
    exact rosatiφ_pr (pD.pw.pr i) (hf i) (hg i) k
  have hp : Function.Surjective (D'.P.A ⊗ D'.P.A).hom.appTop.hom := by
    have h1 := surj_comp (surj_snd hG D'.P.isAb D'.P.A) (hG _ D'.P.A D'.P.isAb).2
    rwa [Over.w] at h1
  have hone : ∀ {Z : Scheme.{0}} (z₀ : Z) (J₀ : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z₀ J₀ → ∀ (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left), val u' (r ≫ zero2 D'.P.A) z₀ J₀ = 1 := by
    intro Z z₀ J₀ hJ₀ r
    have := val_corr hJ₀ h0' r
    rwa [val_pull hJ₀, val_one] at this
  have hcond : ∀ (y₀ : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) J₀ J₀', Good D.P.L y₀ J₀ → Good D'.P.L y₀ J₀' →
      (∏ k, bw pD.w (zero2 D'.P.A ≫ rosatiφ D'.P.A f' g' k) y₀
        (fun i => J₀ ((zero2 D'.P.A ≫ rosatiφ D'.P.A f' g' k) ≫ (pD.pw.pr i).left))
        (J₀' (zero2 D'.P.A ≫ rosatiφ D'.P.A f' g' k)) ^ rosatiε k) * val u' (zero2 D'.P.A) y₀ J₀' =
      ∏ i, val u (zero2 D'.P.A ≫ (pD.pw.pr i ⊗ₘ pD.pw.pr i).left) y₀ J₀ := by
    intro y₀ J₀ J₀' hJ₀ hJ₀'
    have hz : ∀ i, zero2 D'.P.A ≫ (pD.pw.pr i ⊗ₘ pD.pw.pr i).left = 𝟙 _ ≫ zero2 D.P.A := fun i => by
      have := pD.pw.hom i
      rw [Category.id_comp]
      unfold zero2
      rw [← Over.comp_left, lift_map, IsMonHom.one_hom]
    have hz' := hone y₀ J₀' hJ₀' (𝟙 _)
    rw [Category.id_comp] at hz'
    have hu0 : val u (𝟙 _ ≫ zero2 D.P.A) y₀ J₀ = 1 := by
      have := val_corr hJ₀ h0 (𝟙 _)
      rwa [val_pull hJ₀, val_one] at this
    simp only [hz, hu0, Finset.prod_const_one, hz', _root_.mul_one]
    have PR0 := prod_ros f' g' (η[D'.P.A]) (η[D'.P.A]) (fun ψ => om pD.w y₀ J₀ J₀' ψ)
    beta_reduce at PR0
    have e1 : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) = η[D'.P.A] := by
      show toUnit _ ≫ η[D'.P.A] = η[D'.P.A]
      rw [toUnit_unit, Category.id_comp]
    have e2 : η[D'.P.A] * η[D'.P.A] = η[D'.P.A] := by rw [← e1, _root_.mul_one]
    rw [IsMonHom.one_hom, IsMonHom.one_hom, e2] at PR0
    exact PR0.trans (mul_inv_inv_inv_mul_mul_eq_one _)
  have BU := CubBox.box_unique D.P.isLB D'.P.isLB pD.w pD.w_gen hψ hu' hu ((D'.P.A ⊗ D'.P.A).hom) (zero2 D'.P.A)
    (by unfold zero2; exact Over.w (lift η[D'.P.A] η[D'.P.A])) hp hcond (TK R).left (D'.pt2 y y') z J J' hJ hJ'
  simp only [hpt] at BU
  have BU2 : (∏ k, om pD.w z J J' ((lift (cP D' (TK R) y) (cP D' (TK R) y')).left ≫ rosatiφ D'.P.A f' g' k) ^
      rosatiε k) * val u' (D'.pt2 y y') z J' = ∏ i, val u (D.pt2 (pD.xe y i) (pD.xe y' i)) z J := BU
  have PR := prod_ros f' g' (cP D' (TK R) y) (cP D' (TK R) y') (fun ψ => om pD.w z J J' ψ)
  beta_reduce at PR
  rw [hcb, hcb'] at PR
  rw [PR] at BU2
  exact mul_eq_of_four_relations_commGroup _ _ _ _ _ _ _ _ _ _ _ _ _ T1 T2 BU2
    (by rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun i _ => HB i))

end GlobalTheory.TauBalBox

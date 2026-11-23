import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.QuadIff

variable {R : Type} [CommRing R] [IsDomain R]

def germU (z : (TK R).left) : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ :=
  (gm (𝟙 (TK R).left) z ⊤).comp (Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom.toMonoidHom)

theorem germU_injective (z : (TK R).left) : Function.Injective (germU z) := by
  let ev : FractionRing R →+* (TK R).left.presheaf.stalk z :=
    ((TK R).left.presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
  have e : ∀ k : (FractionRing R)ˣ, (germU z k).val = ev k.val := fun k =>
    (gs_unit (𝟙 (TK R).left) z ⊤ trivial (unitOn k)).symm.trans ((gs_eq _ z ⊤ trivial _).trans rfl)
  intro a b h
  exact Units.ext (ev.injective ((e a).symm.trans ((congrArg Units.val h).trans (e b))))

theorem exists_good_pt (D : DegPre R) : ∃ (z : (TK R).left) (J : _), Good D.P.L z J := by
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  choose J hJ using fun χ : (TK R).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  exact ⟨z, J, hJ⟩

theorem even_iff (D : DegPre R) : D.PsiEven ↔ ∀ (χ : D.X) z J, Good D.P.L z J →
    val (D.psi (-χ)) (𝟙 _) z J * val (LB.pullGen D.P.L _ _ D.sym (D.xK χ)) (𝟙 _) z J = val (D.psi χ) (𝟙 _) z J :=
  ⟨fun h χ _ _ hJ => (val_mul hJ _ _ _).symm.trans (val_corr hJ (h χ) (𝟙 _)),
    fun h χ => corr_of_val D.P.isLB fun y J hJ => (val_mul hJ _ _ _).trans (h χ y J hJ)⟩

theorem bimult_iff (D : DegPre R) : D.TauBimult ↔ ∀ (a a' b : D.X) z J, Good D.P.L z J →
    val (D.tau (a + a') b) (𝟙 _) z J *
      val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J =
      val (D.tau a b) (𝟙 _) z J * val (D.tau a' b) (𝟙 _) z J :=
  ⟨fun h a a' b _ _ hJ => (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h a a' b) (𝟙 _)).trans (val_mul hJ _ _ _)),
    fun h a a' b => corr_of_val D.P.isLB fun y J hJ =>
      (val_mul hJ _ _ _).trans ((h a a' b y J hJ).trans (val_mul hJ _ _ _).symm)⟩

theorem val_tau_eq (D : DegPre R) {z : (TK R).left} {J} (hJ : Good D.P.L z J) (a b : D.X) :
    val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem val_psi_rescale (D : DegPre R) (g : D.X → (FractionRing R)ˣ) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (χ : D.X) : val ((rescale D g).psi χ) (𝟙 (TK R).left) z J =
      germU z (g χ) * val (D.psi χ) (𝟙 (TK R).left) z J :=
  GlobalTheory.UU.val_scaleGen (Y := (TK R).left) (L := D.P.L) (unitOn (g χ)) (D.psi χ) (𝟙 _) hJ

theorem val_tau_rescale (D : DegPre R) (g : D.X → (FractionRing R)ˣ) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (a b : D.X) : val ((rescale D g).tau a b) (𝟙 (TK R).left) z J =
      germU z (g (a + b)) * (germU z (g a))⁻¹ * (germU z (g b))⁻¹ * val (D.tau a b) (𝟙 (TK R).left) z J := by
  have key : ∀ (A B C p q r s : ((TK R).left.presheaf.stalk z)ˣ),
      A * p * (B * q)⁻¹ * (C * r)⁻¹ * s = A * B⁻¹ * C⁻¹ * (p * q⁻¹ * r⁻¹ * s) := fun A B C p q r s => by
    simp only [_root_.mul_inv]
    ac_rfl
  refine (val_tau_eq (rescale D g) hJ a b).trans (Eq.trans ?_ (congrArg (_ * ·) (val_tau_eq D hJ a b)).symm)
  refine Eq.trans ?_ (key _ _ _ _ _ _ _)
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (val_psi_rescale D g hJ (a + b))
    (congrArg (·⁻¹) (val_psi_rescale D g hJ a))) (congrArg (·⁻¹) (val_psi_rescale D g hJ b))) rfl

theorem alg_even {G : Type*} [CommGroup G] {A B m s p : G} (h : m * s = p) : A * m * s = B * p ↔ A = B := by
  rw [_root_.mul_assoc, h, mul_left_inj]

theorem alg_cube {G : Type*} [CommGroup G] {S P A A' B Q Q' t c u v : G} (h : t * c = u * v) :
    S * P⁻¹ * B⁻¹ * t * c = Q * A⁻¹ * B⁻¹ * u * (Q' * A'⁻¹ * B⁻¹ * v) ↔ S * A * A' * B = P * Q * Q' := by
  have a := congrArg Additive.ofMul h
  constructor <;> intro e <;> apply Additive.ofMul.injective <;> have b := congrArg Additive.ofMul e <;>
    simp only [ofMul_mul, ofMul_inv] at a b ⊢
  · linear_combination (norm := abel) b - a
  · linear_combination (norm := abel) b + a

theorem even_at (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (h : D.PsiEven) (χ : D.X) {z : (TK R).left} {J}
    (hJ : Good D.P.L z J) :
    val ((rescale D g).psi (-χ : D.X)) (𝟙 _) z J * val (LB.pullGen D.P.L _ _ D.sym (D.xK χ)) (𝟙 _) z J =
      val ((rescale D g).psi χ) (𝟙 _) z J ↔ g (-χ) = g χ := by
  rw [val_psi_rescale D g hJ, val_psi_rescale D g hJ, alg_even ((even_iff D).1 h χ z J hJ)]
  exact (germU_injective z).eq_iff

theorem bimult_at (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (h : D.TauBimult) (a a' b : D.X) {z : (TK R).left} {J}
    (hJ : Good D.P.L z J) :
    val ((rescale D g).tau (a + a' : D.X) b) (𝟙 _) z J *
      val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J =
      val ((rescale D g).tau a b) (𝟙 _) z J * val ((rescale D g).tau a' b) (𝟙 _) z J ↔
      g (a + a' + b) * g a * g a' * g b = g (a + a') * g (a + b) * g (a' + b) := by
  rw [val_tau_rescale D g hJ, val_tau_rescale D g hJ, val_tau_rescale D g hJ,
    alg_cube ((bimult_iff D).1 h a a' b z J hJ)]
  simp only [← map_mul]
  exact (germU_injective z).eq_iff

theorem rescale_even_bimult_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ),
    (D.PsiEven → ((GlobalTheory.PolDeg.rescale D g).PsiEven ↔ ∀ a : D.X, g (-a) = g a)) ∧
    (D.TauBimult → ((GlobalTheory.PolDeg.rescale D g).TauBimult ↔
      (∀ a a' b : D.X, g (a + a' + b) * g a * g a' * g b = g (a + a') * g (a + b) * g (a' + b)))) := by
  intro R _ _ D g
  obtain ⟨z, J, hJ⟩ := exists_good_pt D
  refine ⟨fun h => ⟨fun H a => ?_, fun H => ?_⟩, fun h => ⟨fun H a a' b => ?_, fun H => ?_⟩⟩
  · exact (even_at D g h a hJ).1 ((even_iff (rescale D g)).1 H a z J hJ)
  · exact (even_iff (rescale D g)).2 fun χ _ _ hJ' => (even_at D g h χ hJ').2 (H χ)
  · exact (bimult_at D g h a a' b hJ).1 ((bimult_iff (rescale D g)).1 H a a' b z J hJ)
  · exact (bimult_iff (rescale D g)).2 fun a a' b _ _ hJ' => (bimult_at D g h a a' b hJ').2 (H a a' b)

end GlobalTheory.PolDeg.QuadIff

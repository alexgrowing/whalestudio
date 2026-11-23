import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.DegeneratingToriPeriodMapEqBaseOfYEqZero

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace AnArc

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

def perFactor (w : ℂ) (la : A.La) (v : A.V) : ℂ :=
  A.ah la.l (v.2 + A.ct la.y) * (A.psi la.y * eTwoPi (v.1 la.y) * eTwoPi (w * A.q la.y))⁻¹

theorem perFactor_ne_zero (w : ℂ) (la : A.La) (v : A.V) : A.perFactor w la v ≠ 0 :=
  mul_ne_zero (A.ah_ne_zero _ _)
    (inv_ne_zero (mul_ne_zero (mul_ne_zero (A.psi _).ne_zero (e_ne_zero _)) (e_ne_zero _)))

open AlgebraicGeometry CategoryTheory Limits in
variable {O : Type} [CommRing O] [StarRing O] (A : _root_.GlobalTheory.AnArc O) in
open _root_.GlobalTheory.AnArc.La in

theorem _root_.GlobalTheory.AnArc.term_add_period {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (w : ℂ)
    (la : A.La) (μ : A.X) (v : A.V) :
    A.term j α th μ (v + A.Pw w la) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α μ) =
      A.perFactor w la v ^ j *
        (A.term j α th (μ + la.y) v *
          _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α (μ + la.y))) := by
  set y := la.y with hy
  set n := la.n with hn
  set l := la.l with hl
  set L : A.La := _root_.GlobalTheory.AnArc.La.mk 0 0 l
  set M : A.La := _root_.GlobalTheory.AnArc.La.mk 0 n 0
  set Y : A.La := _root_.GlobalTheory.AnArc.La.mk y 0 0
  have hPw : A.Pw w la = A.Pw w Y + A.P0 M + A.P0 L := by
    conv_lhs => rw [eq_add_parts la]
    rw [map_add, map_add, _root_.GlobalTheory.AnArc.degeneratingTori_periodMap_eq_base_of_y_eq_zero _ _ (mk_y _ _ _),
      _root_.GlobalTheory.AnArc.degeneratingTori_periodMap_eq_base_of_y_eq_zero _ _ (mk_y _ _ _)]
  set v' : A.V := v + A.P0 L + A.P0 M
  have hv : v + A.Pw w la = v' + A.Pw w Y := by
    rw [hPw]
    simp only [v']
    abel
  have key := A.term_add_Pw_y j α th w μ y v'
  rw [← hv] at key
  have hterm : A.term j α th (μ + y) v' =
      (A.chi l * Complex.exp (Real.pi * A.H v.2 l + Real.pi / 2 * A.H l l)) ^ j *
        A.term j α th (μ + y) v := by
    rw [_root_.GlobalTheory.AnArc.term_add_P0_n,
      _root_.GlobalTheory.AnArc.term_add_P0_l A h]
  have hv1 : v'.1 y = v.1 y + (n y : ℂ) + -(A.H (A.ct y) l / (2 * Complex.I)) := by
    simp [v', L, M, Prod.fst_add, _root_.GlobalTheory.AnArc.degeneratingTori_basePeriodMap_fst_apply, mk_y, mk_n, mk_l]
    ring
  set X : ℂ := A.psi y * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (v.1 y) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.q y)
  set X' : ℂ := A.psi y * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (v'.1 y) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.q y)
  have hX' : X' = X * Complex.exp (-(Real.pi * A.H (A.ct y) l)) := by
    simp only [X', X, hv1, _root_.GlobalTheory.AnArc.e_add, _root_.GlobalTheory.AnArc.e_intCast, _root_.GlobalTheory.AnArc.e_neg_div]
    ring
  have hX'0 : X' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Units.ne_zero _) (_root_.GlobalTheory.AnArc.e_ne_zero _)) (_root_.GlobalTheory.AnArc.e_ne_zero _)
  have hfac : A.perFactor w la v =
      A.chi l * Complex.exp (Real.pi * A.H v.2 l + Real.pi / 2 * A.H l l) * X'⁻¹ := by
    rw [_root_.GlobalTheory.AnArc.perFactor, ← hy, ← hl, _root_.GlobalTheory.AnArc.ah_add, hX']
    simp only [mul_inv, ← Complex.exp_neg, neg_neg, _root_.GlobalTheory.AnArc.ah, X]
    ring
  calc A.term j α th μ (v + A.Pw w la) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α μ)
      = (X' ^ j)⁻¹ *
          (X' ^ j * (A.term j α th μ (v + A.Pw w la) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α μ))) := by
        rw [inv_mul_cancel_left₀ (pow_ne_zero _ hX'0)]
    _ = _ := by
        rw [key, hterm, hfac]
        ring

open AlgebraicGeometry CategoryTheory Limits in
variable {O : Type} [CommRing O] [StarRing O] (A : _root_.GlobalTheory.AnArc O) in

theorem _root_.GlobalTheory.AnArc.Sum_add_period {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (w : ℂ)
    (la : A.La) (v : A.V) :
    A.Sum j α th w (v + A.Pw w la) = A.perFactor w la v ^ j * A.Sum j α th w v := by
  simp only [_root_.GlobalTheory.AnArc.Sum, A.term_add_period h w la]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addRight la.y).tsum_eq
    fun μ => A.term j α th μ v * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α μ)

def FSumDeriv (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (v z₀ : A.V) : LaurentSeries ℂ :=
  HahnSeries.ofSuppBddBelow (fun n => ∑ μ ∈ A.level j α n, fderiv ℂ (A.term j α th μ) v z₀)
    ⟨-A.be α α, fun n hn => by
      by_contra h
      exact hn (by simp only [A.level_eq_empty (not_le.1 h), Finset.sum_empty])⟩

def FSumShift (k : ℕ) [NeZero k] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (la : A.La) (z : A.V) : LaurentSeries ℂ :=
  HahnSeries.ofSuppBddBelow
    (fun n => ∑ μ ∈ A.level k (α + la.y) (n - A.be la.y α / k), A.term k α th μ (z + (k : ℂ)⁻¹ • A.P0 la))
    ⟨-A.be (α + la.y) (α + la.y) + A.be la.y α / k, fun n hn => by
      by_contra h
      exact hn (by simp only [A.level_eq_empty (j := k) (α := α + la.y) (n := n - A.be la.y α / k) (by omega),
        Finset.sum_empty])⟩

theorem coeff_FSumShift (k : ℕ) [NeZero k] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (la : A.La) (z : A.V) (n : ℤ) :
    (A.FSumShift k α th la z).coeff n =
      ∑ μ ∈ A.level k (α + la.y) (n - A.be la.y α / k), A.term k α th μ (z + (k : ℂ)⁻¹ • A.P0 la) := rfl

example (τ₀ w : ℂ) (v : (tate τ₀).V) :
    (tate τ₀).perFactor w (La.mk (A := tate τ₀) (1 : ℤ) 0 0) v = eTwoPi (-((τ₀ + 2 * w) / 2 + v.1 (1 : ℤ))) := by
  have h1 : (tate τ₀).ah 0 (v.2 + (tate τ₀).ct (1 : ℤ)) = 1 := by simp [ah]
  change (tate τ₀).ah 0 (v.2 + (tate τ₀).ct (1 : ℤ)) *
    ((psiInt τ₀ 1 : ℂ) * eTwoPi (v.1 (1 : ℤ)) * eTwoPi (w * ((1 : ℤ) : ℂ)))⁻¹ = _
  rw [h1, one_mul, coe_psiInt, ← e_add, ← e_add, eTwoPi, eTwoPi, ← Complex.exp_neg]
  congr 1; push_cast; ring

end AnArc

section Along

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def IsDerivAtZero {X : Scheme.{0}} (e : V → (Sp ℂ ⟶ X)) (w : V) (v : Sp (DualNumber ℂ) ⟶ X) : Prop :=
  spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 ∧
    ∀ (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)),
      TrivSqZeroExt.snd (show DualNumber ℂ from
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE U ⊤ h).hom f)) =
        fderiv ℂ (fun z => valAt' (e z) U f) 0 w

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

def IsRigFrame (L : RigLB G) (y : Sp ℂ ⟶ S) (e : V → (Sp ℂ ⟶ G.left)) (fr : L.L.ι → V → ℂ) : Prop :=
  (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.L.U j}) ∧ (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.L.U j → fr j z ≠ 0) ∧
    (∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.L.U j ⊓ L.L.U j') →
      fr j z = valAt' (e z) (L.L.U j ⊓ L.L.U j') (L.L.g j j').val * fr j' z) ∧
    ∀ j, ⊤ ≤ e 0 ⁻¹ᵁ L.L.U j → fr j 0 = valAt' y ((L.L.pull (eSec G)).U (fun _ => j)) (L.rig.s (fun _ => j)).val

def IsAlgebraicIn (L : RigLB G) (y : Sp ℂ ⟶ S) (e : V → (Sp ℂ ⟶ G.left)) (θ : V → ℂ) (fr : L.L.ι → V → ℂ) : Prop :=
  ∃ s : (L.L.pull (pullback.fst G.hom y)).Sec, ∀ j z (x : Sp ℂ ⟶ pullback G.hom y),
    x ≫ pullback.fst _ _ = e z → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ e z ⁻¹ᵁ L.L.U j →
    valAt' x ((L.L.pull (pullback.fst G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z

variable {V' : Type} [NormedAddCommGroup V'] [NormedSpace ℂ V']

theorem IsRigFrame.comp {L : RigLB G} {y : Sp ℂ ⟶ S} {e : V → (Sp ℂ ⟶ G.left)} {fr : L.L.ι → V → ℂ}
    (H : IsRigFrame L y e fr) (h : V' →L[ℂ] V) : IsRigFrame L y (fun z => e (h z)) (fun j z => fr j (h z)) :=
  ⟨fun j => (H.1 j).comp h.differentiable.differentiableOn fun _ hz => hz, fun j z => H.2.1 j (h z),
    fun j j' z => H.2.2.1 j j' (h z), fun j hj => by
      simp only [map_zero] at hj ⊢
      exact H.2.2.2 j hj⟩

omit [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V'] in

theorem IsAlgebraicIn.comp {L : RigLB G} {y : Sp ℂ ⟶ S} {e : V → (Sp ℂ ⟶ G.left)} {θ : V → ℂ}
    {fr : L.L.ι → V → ℂ} (H : IsAlgebraicIn L y e θ fr) (h : V' → V) :
    IsAlgebraicIn L y (fun z => e (h z)) (fun z => θ (h z)) (fun j z => fr j (h z)) :=
  H.imp fun _ hs j z => hs j (h z)

end Along

end GlobalTheory

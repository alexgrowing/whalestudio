import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.DegeneratingToriPeriodMapEqBaseOfYEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfForallExistsLsumETwoPi
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]

section Val
variable {Z Z' : Scheme.{0}} {R : Type} [CommRing R]

abbrev SecP (L : LB Z) (p : Z' ⟶ Z) (m : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (m : ℤ)))

def sval {L : LB Z} {p : Z' ⟶ Z} {m : ℕ} (σ : SecP L p m) (x : Sp R ⟶ Z') (j : L.ι) : R :=
  valR x (LB.wchart L (fun _ : Fin 1 => p) (fun _ => j)) (σ.f (fun _ => j))

def HasVal {L : LB Z} {p : Z' ⟶ Z} {m : ℕ} (σ : SecP L p m) (x : Sp R ⟶ Z') (τ : L.ι → R) (r : R) : Prop :=
  ∀ j, ⊤ ≤ (x ≫ p) ⁻¹ᵁ L.U j → sval σ x j = r * τ j ^ m

def IsFrm (L : LB Z) (x : Sp R ⟶ Z) (τ : L.ι → R) : Prop :=
  (∀ j, ⊤ ≤ x ⁻¹ᵁ L.U j → IsUnit (τ j)) ∧
    ∀ j j', ⊤ ≤ x ⁻¹ᵁ (L.U j ⊓ L.U j') → τ j = valR x (L.U j ⊓ L.U j') (L.g j j').val * τ j'

def fib {S : Scheme.{0}} {G : Over S} {y : Sp R ⟶ S} (x : Over.mk y ⟶ G) : Sp R ⟶ pullback G.hom y :=
  pullback.lift x.left (𝟙 _) (by simp [Over.w x])

end Val

structure Germs where
  R : ℂ → Subalgebra ℂ ℂ⸨X⸩
  ev : ∀ w, R w →ₐ[ℂ] ℂ
  unit : ∀ w (s : R w), ev w s ≠ 0 → IsUnit s
  le : ∀ (T : ℝ) (w : ℂ), T < w.im → Conv.halfRing T ≤ R w
  ev_eq : ∀ (T : ℝ) (w : ℂ) (hw : T < w.im) (s : Conv.halfRing T),
    ev w (Subalgebra.inclusion (le T w hw) s) = Conv.ev T w hw s
  frac : ∀ w (f : R w), ∃ (T : ℝ) (hw : T < w.im) (a s : Conv.halfRing T),
    Conv.ev T w hw s ≠ 0 ∧ (s : ℂ⸨X⸩) * f = a

section An
variable {O₁ : Type} [CommRing O₁] [StarRing O₁] (A : AnArc O₁)

def IsFShift (k : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (la : A.La) (z : A.V) (S : ℂ⸨X⸩) : Prop :=
  (k ≠ 0 ∧ (k : ℤ) ∣ A.be la.y α) ∧
  ∀ n : ℤ, S.coeff n = ∑ᶠ (m : A.X) (_ : A.exponent k (α + la.y) m + A.be la.y α / k = n),
    A.term k α th m (z + (k : ℂ)⁻¹ • A.P0 la)

def IsDFSum (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (z₀ : A.V) (S : ℂ⸨X⸩) : Prop :=
  ∀ n : ℤ, S.coeff n = fderiv ℂ (fun v => (A.FSum j α th v).coeff n) 0 z₀

def IsComb (j : ℕ) [NeZero j] (B : Set ℂ⸨X⸩) (f : A.V → ℂ⸨X⸩) : Prop :=
  ∃ (n : ℕ) (r : Fin n → ℂ⸨X⸩) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ),
    (∀ i, r i ∈ B ∧ th i ∈ A.Theta j (α i)) ∧ ∀ v, f v = ∑ i, r i * A.FSum j (α i) (th i) v

def IsFactor (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ) : Prop :=
  ∀ (w : ℂ) (la : A.La) (v : A.V) (j : ℕ) (α : A.X), ∀ th ∈ A.Theta j α, ∀ m : A.X,
    A.term j α th m (v + A.Pw w la) * eTwoPi (w * A.exponent j α m) = Complex.exp (lin w la v + cst w la) ^ j *
      (A.term j α th (m + la.y) v * eTwoPi (w * A.exponent j α (m + la.y)))

variable {A} in

theorem IsFactor.hasSum {lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ} {cst : ℂ → A.La → ℂ} (h : IsFactor A lin cst) (w : ℂ)
    (la : A.La) (v : A.V) (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (hth : th ∈ A.Theta j α) {s : ℂ}
    (hs : HasSum (fun m => A.term j α th m v * eTwoPi (w * A.exponent j α m)) s) :
    HasSum (fun m => A.term j α th m (v + A.Pw w la) * eTwoPi (w * A.exponent j α m))
      (Complex.exp (lin w la v + cst w la) ^ j * s) := by
  simp only [h w la v j α th hth]
  exact ((Equiv.addRight la.y).hasSum_iff.2 hs).mul_left _

variable {A} in

theorem IsFactor.sum {lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ} {cst : ℂ → A.La → ℂ} (h : IsFactor A lin cst) (w : ℂ)
    (la : A.La) (v : A.V) (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (hth : th ∈ A.Theta j α) :
    A.Sum j α th w (v + A.Pw w la) = Complex.exp (lin w la v + cst w la) ^ j * A.Sum j α th w v := by
  rw [AnArc.Sum, AnArc.Sum, ← tsum_mul_left]
  refine Eq.trans ?_ ((Equiv.addRight la.y).tsum_eq _)
  exact tsum_congr fun m => h w la v j α th hth m

theorem not_isFShift_zero (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (la : A.La) (z : A.V) (S : ℂ⸨X⸩) :
    ¬ IsFShift A 0 α th la z S := fun h => h.1.1 rfl

theorem isFShift_zero_iff (k : ℕ) [NeZero k] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (z : A.V) (S : ℂ⸨X⸩) :
    IsFShift A k α th 0 z S ↔ S = A.FSum k α th z := by
  have hy : (0 : A.La).y = 0 := rfl
  have key : ∀ n : ℤ, (∑ᶠ (m : A.X) (_ : A.exponent k α m = n), A.term k α th m z) = (A.FSum k α th z).coeff n :=
    fun n => by
      rw [AnArc.coeff_FSum]
      exact finsum_cond_eq_sum_of_cond_iff _ fun {m} _ => by rw [AnArc.mem_level]
  simp only [IsFShift, hy, map_zero, LinearMap.zero_apply, add_zero, smul_zero, Int.zero_ediv, dvd_zero, and_true,
    key, ne_eq, NeZero.ne k, not_false_eq_true, true_and]
  exact ⟨fun h => HahnSeries.ext (funext h), fun h n => by rw [h]⟩

def AnFin : Prop :=
  (∀ (j : ℕ) (α : A.X), 1 ≤ j → Module.Finite ℂ (A.Theta j α)) ∧ ∃ th ∈ A.Theta 1 0, th ≠ 0

end An

section Gen
variable {S : Scheme.{0}}

structure GenPts (A : AnArc (𝓞 E)) (t : SAB H S) (y : Sp ℂ⸨X⸩ ⟶ S) where
  x : A.V → (Over.mk y ⟶ t.G)
  add : ∀ v v', x (v + v') = x v * x v'
  lin : ∀ (e : 𝓞 E) v, x (A.actV e v) = x v ≫ t.act.act e
  τ : A.V → t.PP.L.ι → ℂ⸨X⸩
  frm : ∀ v, IsFrm t.PP.L (x v).left (τ v)
  rig : ∀ j, ⊤ ≤ (x 0).left ⁻¹ᵁ t.PP.L.U j →
    τ 0 j = valR y ((t.PP.L.pull (eSec t.G)).U (fun _ => j)) (t.PP.rig.s (fun _ => j)).val
  sig : ∀ (j : ℕ) (α : A.X), ((Fin A.gB → ℂ) → ℂ) → SecP t.PP.L (pullback.fst t.G.hom y) j
  val : ∀ (j : ℕ) [NeZero j] (α : A.X), ∀ th ∈ A.Theta j α, ∀ v,
    HasVal (sig j α th) (fib (x v)) (τ v) (A.FSum j α th v)
  span : ∀ (j : ℕ) [NeZero j] (s : SecP t.PP.L (pullback.fst t.G.hom y) j), ∃ f : A.V → ℂ⸨X⸩,
    IsComb A j Set.univ f ∧ ∀ v, HasVal s (fib (x v)) (τ v) (f v)
  sep : ∀ (j : ℕ) [NeZero j] (s : SecP t.PP.L (pullback.fst t.G.hom y) j),
    (∀ v, HasVal s (fib (x v)) (τ v) 0) → ∀ i, s.f i = 0

variable {A : AnArc (𝓞 E)} {t : SAB H S} {y : Sp ℂ⸨X⸩ ⟶ S}

def GenPts.LevelPt (Φ : GenPts A t y) (k : ℕ) (p : Over.mk y ⟶ t.G) (la : A.La) : Prop :=
  p ^ k = 1 ∧ (k ≠ 0 ∧ ∀ α, (k : ℤ) ∣ A.be la.y α) ∧
  ∀ (α α' : A.X), ∀ th ∈ A.Theta k α, ∀ th' ∈ A.Theta k α', ∀ (z : A.V) (F F' : ℂ⸨X⸩) (j : t.PP.L.ι),
    IsFShift A k α th la z F → IsFShift A k α' th' la z F' → ⊤ ≤ (Φ.x z * p).left ⁻¹ᵁ t.PP.L.U j →
    sval (Φ.sig k α th) (fib (Φ.x z * p)) j * F' = sval (Φ.sig k α' th') (fib (Φ.x z * p)) j * F

theorem GenPts.LevelPt.ne_zero {Φ : GenPts A t y} {k : ℕ} {p : Over.mk y ⟶ t.G} {la : A.La} (h : Φ.LevelPt k p la) :
    k ≠ 0 := h.2.1.1

theorem GenPts.LevelPt.dvd {Φ : GenPts A t y} {k : ℕ} {p : Over.mk y ⟶ t.G} {la : A.La} (h : Φ.LevelPt k p la)
    (α : A.X) : (k : ℤ) ∣ A.be la.y α := h.2.1.2 α

theorem GenPts.levelPt_one (Φ : GenPts A t y) (k : ℕ) [NeZero k] : Φ.LevelPt k 1 0 := by
  refine ⟨one_pow _, ⟨NeZero.ne k, fun α => ?_⟩, fun α α' th h th' h' z F F' j hF hF' hj => ?_⟩
  · rw [show (0 : A.La).y = 0 from rfl, map_zero]; exact dvd_zero _
  · rw [isFShift_zero_iff] at hF hF'
    rw [_root_.mul_one] at hj ⊢
    have hj' : ⊤ ≤ (fib (Φ.x z) ≫ pullback.fst t.G.hom y) ⁻¹ᵁ t.PP.L.U j := by
      rw [fib, pullback.lift_fst]; exact hj
    rw [Φ.val k α th h z j hj', Φ.val k α' th' h' z j hj', hF, hF']
    ring

def GenPts.IsTan (Φ : GenPts A t y) (z₀ : A.V) (ν : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t.G.hom y) : Prop :=
  ν ≫ pullback.snd _ _ = spMap (algebraMap ℂ⸨X⸩ (DualNumber ℂ⸨X⸩)) ∧
  spMap (TrivSqZeroExt.fstHom ℂ⸨X⸩ ℂ⸨X⸩ ℂ⸨X⸩).toRingHom ≫ ν = fib (Φ.x 0) ∧
  ∃ τ : t.PP.L.ι → DualNumber ℂ⸨X⸩, IsFrm t.PP.L (ν ≫ pullback.fst _ _) τ ∧
    ∀ (j : ℕ) [NeZero j] (α : A.X), ∀ th ∈ A.Theta j α, ∀ F, IsDFSum A j α th z₀ F →
      HasVal (Φ.sig j α th) ν τ (TrivSqZeroExt.inl (A.FSum j α th 0) + TrivSqZeroExt.inr F)

def GenPts.Rational (Φ : GenPts A t y) : Prop :=
  (∀ v, ∃ x' : Sp Conv.convLaurent ⟶ t.G.left, spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫ x' = (Φ.x v).left) ∧
    ∀ v j, ⊤ ≤ (Φ.x v).left ⁻¹ᵁ t.PP.L.U j → Φ.τ v j ∈ Conv.convLaurent

structure Coords (Φ : GenPts A t y) (N : ℕ) [NeZero N] where
  T : ℝ
  U : S.Opens
  aff : IsAffineOpen U
  mem : ⊤ ≤ y ⁻¹ᵁ U
  n : ℕ
  b : Fin n → LB.Sec (Out.powOver t.G t.PP.L U N)
  emb : AmpleSpan.EmbedsBy (t.G.hom ∣_ U) b
  cf : Fin n → A.V → Conv.halfRing T
  comb : ∀ i, IsComb A N (Conv.halfRing T) (fun v => cf i v)
  val : ∀ i v (x' : Sp ℂ⸨X⸩ ⟶ (t.G.hom ⁻¹ᵁ U).toScheme) (j : t.PP.L.ι), x' ≫ (t.G.hom ⁻¹ᵁ U).ι = (Φ.x v).left →
    ⊤ ≤ (Φ.x v).left ⁻¹ᵁ t.PP.L.U j →
    valR x' ((Out.powOver t.G t.PP.L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = cf i v * Φ.τ v j ^ N
  bpf : ∀ (w : ℂ) (hw : T < w.im) v, ∃ i, Conv.ev T w hw (cf i v) ≠ 0

structure SpecPts (Φ : GenPts A t y) (Γ : Germs) where
  T : ℝ
  yT : Sp (Conv.halfRing T) ⟶ S
  yT_gen : spMap (Conv.halfRing T).val.toRingHom ≫ yT = y
  xt : ∀ (w : ℂ) (hw : T < w.im), A.V →
    (Over.mk (spMap (Subalgebra.inclusion (Γ.le T w hw)).toRingHom ≫ yT) ⟶ t.G)
  xt_gen : ∀ w hw v, spMap (Γ.R w).val.toRingHom ≫ (xt w hw v).left = (Φ.x v).left
  τt : ∀ (w : ℂ), A.V → t.PP.L.ι → Γ.R w
  τt_frm : ∀ w hw v, IsFrm t.PP.L (xt w hw v).left (τt w v)
  τt_gen : ∀ w hw v j, ⊤ ≤ (xt w hw v).left ⁻¹ᵁ t.PP.L.U j → (τt w v j : ℂ⸨X⸩) = Φ.τ v j
  yw : ℂ → (Sp ℂ ⟶ S)
  yw_eq : ∀ w (hw : T < w.im), yw w = spMap (Conv.ev T w hw).toRingHom ≫ yT
  pi : ∀ w, A.V → (Over.mk (yw w) ⟶ t.G)
  pi_eq : ∀ w hw v, (pi w v).left = spMap (Γ.ev w).toRingHom ≫ (xt w hw v).left

def SpecPts.fr {Φ : GenPts A t y} {Γ : Germs} (Ψ : SpecPts Φ Γ) (w : ℂ) (j : t.PP.L.ι) (v : A.V) : ℂ :=
  Γ.ev w (Ψ.τt w v j)

def GenPts.Rel {S' : Scheme.{0}} {t' : SAB H S'} {y' : Sp ℂ⸨X⸩ ⟶ S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (Φ' : GenPts A t' y') (Φ : GenPts A t y) : Prop :=
  y' ≫ f = y ∧ ∀ v, (Φ'.x v).left ≫ m.φ = (Φ.x v).left ∧ ∀ (j : t.PP.L.ι) (j' : t'.PP.L.ι),
    ⊤ ≤ (Φ'.x v).left ⁻¹ᵁ (LB.div (t.PP.L.pull m.φ) t'.PP.L).U (fun _ => j, j') →
    Φ.τ v j = valR (Φ'.x v).left _ (w.s (fun _ => j, j')).val * Φ'.τ v j'

structure IsFibAt (A : AnArc (𝓞 E)) (t : SAB H S) (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ) (w : ℂ)
    (y₀ : Sp ℂ ⟶ S) (π : A.V → (Over.mk y₀ ⟶ t.G)) (fr : t.PP.L.ι → A.V → ℂ) : Prop where
  add : ∀ v v', π (v + v') = π v * π v'
  act : ∀ (e : 𝓞 E) v, π (A.actV e v) = π v ≫ t.act.act e
  hol : IsHolTo Set.univ (fun v => (π v).left)
  per : ∀ la, π (A.Pw w la) = 1
  fr_hol : ∀ j, DifferentiableOn ℂ (fr j) {v | ⊤ ≤ (π v).left ⁻¹ᵁ t.PP.L.U j}
  frm : ∀ v, IsFrm t.PP.L (π v).left (fun j => fr j v)
  rig : ∀ j, ⊤ ≤ (π 0).left ⁻¹ᵁ t.PP.L.U j →
    fr j 0 = valAt' y₀ ((t.PP.L.pull (eSec t.G)).U (fun _ => j)) (t.PP.rig.s (fun _ => j)).val
  fac : ∀ la v j, ⊤ ≤ (π v).left ⁻¹ᵁ t.PP.L.U j → fr j v = Complex.exp (lin w la v + cst w la) * fr j (v + A.Pw w la)
  sec : ∀ th ∈ A.Theta 1 0, ∃ s : SecP t.PP.L (pullback.fst t.G.hom y₀) 1,
    ∀ v, HasVal s (fib (π v)) (fun j => fr j v) (A.Sum 1 0 th w v)

  conv : ∀ th ∈ A.Theta 1 0, ∀ v, Summable (fun m => A.term 1 0 th m v * eTwoPi (w * A.exponent 1 0 m)) := by
    exact fun _ _ _ => Summable.of_finite

structure FPts {V : Type} [AddCommGroup V] (act : 𝓞 E → V → V) {I : ℕ → Type} (t : SAB H S) {F : Type} [Field F]
    (y₁ : Sp F ⟶ S) (φ : ∀ j, I j → V → F) where
  x : V → (Over.mk y₁ ⟶ t.G)
  add : ∀ v v', x (v + v') = x v * x v'
  lin : ∀ (e : 𝓞 E) v, x (act e v) = x v ≫ t.act.act e
  τ : V → t.PP.L.ι → F
  frm : ∀ v, IsFrm t.PP.L (x v).left (τ v)
  rig : ∀ j, ⊤ ≤ (x 0).left ⁻¹ᵁ t.PP.L.U j →
    τ 0 j = valR y₁ ((t.PP.L.pull (eSec t.G)).U (fun _ => j)) (t.PP.rig.s (fun _ => j)).val
  sig : ∀ j, I j → SecP t.PP.L (pullback.fst t.G.hom y₁) j
  val : ∀ j, 1 ≤ j → ∀ i v, HasVal (sig j i) (fib (x v)) (τ v) (φ j i v)
  span : ∀ j, 1 ≤ j → ∀ s : SecP t.PP.L (pullback.fst t.G.hom y₁) j, ∃ (n : ℕ) (r : Fin n → F) (i : Fin n → I j),
    ∀ v, HasVal s (fib (x v)) (τ v) (∑ a, r a * φ j (i a) v)
  sep : ∀ j, 1 ≤ j → ∀ s : SecP t.PP.L (pullback.fst t.G.hom y₁) j,
    (∀ v, HasVal s (fib (x v)) (τ v) 0) → ∀ i, s.f i = 0

def FPts.Lev {V : Type} [AddCommGroup V] {act : 𝓞 E → V → V} {I : ℕ → Type} {F : Type} [Field F]
    {y₁ : Sp F ⟶ S} {φ : ∀ j, I j → V → F} (Θ : FPts act t y₁ φ) (k : ℕ) (p : Over.mk y₁ ⟶ t.G)
    (ψ : I k → V → F) : Prop :=
  p ^ k = 1 ∧ (k ≠ 0 ∧ ∃ i₀ i₁, (∀ z, φ k i₁ z ≠ 0 → ψ i₀ z ≠ 0) ∧ ∃ z, φ k i₁ z ≠ 0) ∧
  ∀ i i' z j, ⊤ ≤ (Θ.x z * p).left ⁻¹ᵁ t.PP.L.U j →
    sval (Θ.sig k i) (fib (Θ.x z * p)) j * ψ i' z = sval (Θ.sig k i') (fib (Θ.x z * p)) j * ψ i z

omit [StarRing (𝓞 E)] in

theorem FPts.lev_one {V : Type} [AddCommGroup V] {act : 𝓞 E → V → V} {I : ℕ → Type} {F : Type} [Field F]
    {y₁ : Sp F ⟶ S} {φ : ∀ j, I j → V → F} (Θ : FPts act t y₁ φ) (k : ℕ) (hk : 1 ≤ k) (i₀ : I k) (z₀ : V)
    (h : φ k i₀ z₀ ≠ 0) : Θ.Lev k 1 (φ k) := by
  refine ⟨one_pow _, ⟨by omega, i₀, i₀, fun _ hz => hz, z₀, h⟩, fun i i' z j hj => ?_⟩
  rw [_root_.mul_one] at hj ⊢
  have hj' : ⊤ ≤ (fib (Θ.x z) ≫ pullback.fst t.G.hom y₁) ⁻¹ᵁ t.PP.L.U j := by
    rw [fib, pullback.lift_fst]; exact hj
  rw [Θ.val k hk i z j hj', Θ.val k hk i' z j hj']
  ring

end Gen

end GlobalTheory.ArcPts

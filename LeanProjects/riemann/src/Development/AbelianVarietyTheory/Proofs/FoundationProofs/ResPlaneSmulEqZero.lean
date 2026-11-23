import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLevFacts
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

abbrev ResL (c : Coef l) : Type := c.O ⧸ Ideal.span {((l : ℕ) : c.O)}

open Classical in

def redL (c : Coef l) (x : Qbar l) : ResL c :=
  if h : x ∈ c.O then Ideal.Quotient.mk _ ⟨x, h⟩ else 0

theorem redL_of_mem (c : Coef l) {x : Qbar l} (h : x ∈ c.O) :
    redL c x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : c.O)}) ⟨x, h⟩ := by
  simp [redL, h]

theorem redL_add (c : Coef l) {x y : Qbar l} (hx : x ∈ c.O) (hy : y ∈ c.O) :
    redL c (x + y) = redL c x + redL c y := by
  rw [redL_of_mem c hx, redL_of_mem c hy, redL_of_mem c (c.O.add_mem hx hy), ← map_add]; rfl

theorem redL_sub (c : Coef l) {x y : Qbar l} (hx : x ∈ c.O) (hy : y ∈ c.O) :
    redL c (x - y) = redL c x - redL c y := by
  rw [redL_of_mem c hx, redL_of_mem c hy, redL_of_mem c (c.O.sub_mem hx hy), ← map_sub]; rfl

theorem redL_mul (c : Coef l) {x y : Qbar l} (hx : x ∈ c.O) (hy : y ∈ c.O) :
    redL c (x * y) = redL c x * redL c y := by
  rw [redL_of_mem c hx, redL_of_mem c hy, redL_of_mem c (c.O.mul_mem hx hy), ← map_mul]; rfl

theorem redL_zero (c : Coef l) : redL c 0 = 0 := by
  rw [redL_of_mem c c.O.zero_mem]; exact map_zero _

theorem redL_one (c : Coef l) : redL c 1 = 1 := by
  rw [redL_of_mem c c.O.one_mem]; exact map_one _

theorem redL_eq_zero_iff (c : Coef l) {x : Qbar l} (h : x ∈ c.O) :
    redL c x = 0 ↔ ∃ o ∈ c.O, x = (l : Qbar l) * o := by
  rw [redL_of_mem c h, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨o, ho⟩
    refine ⟨o, o.2, ?_⟩
    have : ((o * ((l : ℕ) : c.O) : c.O) : Qbar l) = x := congrArg Subtype.val ho
    rw [← this]; push_cast; ring
  · rintro ⟨o, ho, rfl⟩
    refine ⟨⟨o, ho⟩, Subtype.ext ?_⟩
    push_cast; ring

def ResPlane (c : Coef l) : Type := Fin 2 → ResL c

instance (c : Coef l) : AddCommGroup (ResPlane c) := inferInstanceAs (AddCommGroup (Fin 2 → ResL c))
instance (c : Coef l) : TopologicalSpace (ResPlane c) := ⊥
instance (c : Coef l) : DiscreteTopology (ResPlane c) := ⟨rfl⟩

theorem resL_natCast_l (c : Coef l) : ((l : ℕ) : ResL c) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : c.O)})), Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

theorem resPlane_smul_eq_zero (c : Coef l) (m : ResPlane c) : (l ^ 1) • m = 0 := by
  funext i
  show (l ^ 1) • (m i : ResL c) = 0
  rw [nsmul_eq_mul, pow_one, resL_natCast_l, zero_mul]

instance (c : Coef l) : Module (ZMod (l ^ 1)) (ResPlane c) := AddCommGroup.zmodModule (resPlane_smul_eq_zero c)

instance (c : Coef l) : Finite (ResPlane c) := by
  have : CharZero c.O := charZero_of_injective_algebraMap (UpperTheory.V.Base.dvrFacts l c.O).1
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have := (UpperTheory.V.X.So.levFacts l c.O ((l : ℕ) : c.O) hl0 (ResL c) ⟨LinearEquiv.refl _ _⟩).1
  exact inferInstanceAs (Finite (Fin 2 → ResL c))

def wRed (c : Coef l) (W : R2 Ω l) (s : G ℚ Ω) : Matrix (Fin 2) (Fin 2) (ResL c) := fun i j => redL c (mat W s i j)

def resMV (c : Coef l) (B : Matrix (Fin 2) (Fin 2) (ResL c)) : ResPlane c →+ ResPlane c where
  toFun m := B *ᵥ (m : Fin 2 → ResL c)
  map_zero' := Matrix.mulVec_zero B
  map_add' m m' := Matrix.mulVec_add B m m'

theorem wRed_one (c : Coef l) (W : R2 Ω l) : wRed c W 1 = 1 := by
  ext i j
  simp only [wRed, mat, map_one, Units.val_one, Matrix.one_apply]
  split_ifs
  · exact redL_one c
  · exact redL_zero c

theorem wRed_mul (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) (s t : G ℚ Ω) :
    wRed c W (s * t) = wRed c W s * wRed c W t := by
  ext i j
  have e : mat W (s * t) i j = mat W s i 0 * mat W t 0 j + mat W s i 1 * mat W t 1 j := by
    simp only [mat, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [wRed, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e, redL_add c (c.O.mul_mem (hO _ _ _) (hO _ _ _)) (c.O.mul_mem (hO _ _ _) (hO _ _ _)),
    redL_mul c (hO _ _ _) (hO _ _ _), redL_mul c (hO _ _ _) (hO _ _ _)]

def resAct (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) :
    G ℚ Ω →* (ResPlane c →ₗ[ZMod (l ^ 1)] ResPlane c) where
  toFun s := AddMonoidHom.toZModLinearMap (l ^ 1) (resMV c (wRed c W s))
  map_one' := by
    refine LinearMap.ext fun m => ?_
    show wRed c W 1 *ᵥ (m : Fin 2 → ResL c) = m
    rw [wRed_one]; exact Matrix.one_mulVec _
  map_mul' s t := by
    refine LinearMap.ext fun m => ?_
    show wRed c W (s * t) *ᵥ (m : Fin 2 → ResL c) = wRed c W s *ᵥ (wRed c W t *ᵥ (m : Fin 2 → ResL c))
    rw [wRed_mul c W hO]; exact (Matrix.mulVec_mulVec _ _ _).symm

theorem resAct_apply (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) (s : G ℚ Ω) (m : ResPlane c) :
    resAct c W hO s m = (wRed c W s *ᵥ (m : Fin 2 → ResL c) : Fin 2 → ResL c) := rfl

theorem resAct_eq_one (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) {a : G ℚ Ω} (ha : W a = 1) :
    resAct c W hO a = 1 := by
  refine LinearMap.ext fun m => ?_
  show wRed c W a *ᵥ (m : Fin 2 → ResL c) = m
  have : wRed c W a = wRed c W 1 := by unfold wRed mat; rw [ha, map_one]
  rw [this, wRed_one]; exact Matrix.one_mulVec _

def resRep (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1) :
    Representation (ZMod (l ^ 1)) (GS Ω (S : Set Pl)) (ResPlane c) :=
  QuotientGroup.lift (NS Ω (S : Set Pl)) (resAct c W hO) fun a ha =>
    resAct_eq_one c W hO (hN a ((QuotientGroup.eq_one_iff a).2 ha))

theorem resRep_toGS (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1) (s : G ℚ Ω) :
    resRep c W hO S hN (toGS Ω (S : Set Pl) s) = resAct c W hO s := rfl

def descS (S : Finset Pl) {X : Type} (f : G ℚ Ω → X) : GS Ω (S : Set Pl) → X := fun g => f g.out

def resCoc (c : Coef l) (W : R2 Ω l) (z : G ℚ Ω → Fin 2 → Qbar l) (y : Fin 2 → Qbar l) : G ℚ Ω → ResPlane c :=
  fun s i => redL c ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i)

theorem resCoc_mul_ker (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) (y : Fin 2 → Qbar l)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) (s a : G ℚ Ω)
    (ha : a ∈ (toGS Ω (S : Set Pl)).ker) : resCoc c W z y (s * a) = resCoc c W z y s := by
  obtain ⟨-, h2, -, h4, -, -⟩ := hz
  funext i
  have hWa : mat W (s * a) = mat W s := by simp only [mat, map_mul, hN a ha, mul_one]
  have hza : (mat W s *ᵥ z a) i ∈ c.O := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.add_mem (c.O.mul_mem (hO _ _ _) (h4 a ha 0)) (c.O.mul_mem (hO _ _ _) (h4 a ha 1))
  have hd : z (s * a) i - z s i ∈ c.O := by
    have := c.O.add_mem (h2 s a i) hza
    simpa using this
  have e : (l : Qbar l) * z (s * a) i - (mat W (s * a) *ᵥ y - y) i =
      ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) + (l : Qbar l) * (z (s * a) i - z s i) := by
    rw [hWa]; ring
  show redL c _ = redL c _
  rw [e, redL_add c (hzy s i) (c.O.mul_mem (c.O.natCast_mem l) hd), (redL_eq_zero_iff c (c.O.mul_mem (c.O.natCast_mem l) hd)).2 ⟨_, hd, rfl⟩, add_zero]

theorem descS_resCoc_toGS (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) (y : Fin 2 → Qbar l)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) (s : G ℚ Ω) :
    descS S (resCoc c W z y) (toGS Ω (S : Set Pl) s) = resCoc c W z y s := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (NS Ω (S : Set Pl)) s
  show resCoc c W z y ((toGS Ω (S : Set Pl) s).out) = _
  have e : (toGS Ω (S : Set Pl) s).out = s * h := hh
  rw [e]
  exact resCoc_mul_ker c W S A hO hN hz y hzy s h ((QuotientGroup.eq_one_iff (h : G ℚ Ω)).2 h.2)

end GlobalTheory.Ord2

end

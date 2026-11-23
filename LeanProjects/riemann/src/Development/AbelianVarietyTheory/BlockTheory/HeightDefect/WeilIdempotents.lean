import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def cj (D : D7) : AE D →+* AE D := sigR (AF D.host.F) D.sp.cm.sig

def cjU (D : D7) : (AE D)ˣ →* (AE D)ˣ := Units.map (cj D).toMonoidHom

def trA (D : D7) : AE D →ₗ[AF D.host.F] AF D.host.F := Algebra.trace (AF D.host.F) (AE D)

def half (D : D7) : AF D.host.F := algebraMap D.host.F (AF D.host.F) (1 / 2)

abbrev WA (A B : HSp D) : Type := Matrix (Fin A.rank) (Fin B.rank) (AE D)

def colMat {A B : HSp D} (x : WA A B) : Matrix (Fin B.rank) (Fin A.rank) (AE D) := xᵀ

def ofLin (A B : HSp D) (x : A.V →ₗ[D.host.E] B.V) : WA A B :=
  ((LinearMap.toMatrix A.frame B.frame x).map (incA D))ᵀ

def WQ (A B : HSp D) : AddSubgroup (WA A B) :=
  (AddMonoidHom.mapMatrix (incA D).toAddMonoidHom :
    Matrix (Fin A.rank) (Fin B.rank) D.host.E →+ WA A B).range

def gramA (V : HSp D) : Matrix (Fin V.rank) (Fin V.rank) (AE D) := V.gram.map (incA D)

def gramInvA (V : HSp D) : Matrix (Fin V.rank) (Fin V.rank) (AE D) := (V.gram⁻¹).map (incA D)

def adj {A B : HSp D} (x : WA A B) : WA B A :=
  (HMul.hMul (HMul.hMul (gramInvA A) (Formalism.UG.cT (cj D) (colMat x))) (gramA B))ᵀ

def herm {A B : HSp D} (x x' : WA A B) : AE D := Matrix.trace (HMul.hMul (colMat (adj x')) (colMat x))

def symp {A B : HSp D} (x x' : WA A B) : AF D.host.F := trA D (incA D D.host.xi0 * herm x x')

def riem {A B : HSp D} (x x' : WA A B) : AF D.host.F := -symp x x'

theorem herm_add_left {A B : HSp D} (x y z : WA A B) : herm (x + y) z = herm x z + herm y z := by
  simp [herm, colMat, Matrix.transpose_add, Matrix.mul_add, Matrix.trace_add]

theorem adj_add {A B : HSp D} (x y : WA A B) : adj (x + y) = adj x + adj y := by
  have : Formalism.UG.cT (cj D) (colMat (x + y)) = Formalism.UG.cT (cj D) (colMat x) + Formalism.UG.cT (cj D) (colMat y) := by
    ext i j; simp [Formalism.UG.cT, colMat]
  simp only [adj, this, Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add]

theorem herm_add_right {A B : HSp D} (x y z : WA A B) : herm x (y + z) = herm x y + herm x z := by
  simp [herm, colMat, adj_add, Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add]

theorem herm_smul_left {A B : HSp D} (c : AE D) (x y : WA A B) : herm (c • x) y = c * herm x y := by
  simp [herm, colMat, Matrix.transpose_smul, Matrix.mul_smul, Matrix.trace_smul]

theorem symp_add_left {A B : HSp D} (x y z : WA A B) : symp (x + y) z = symp x z + symp y z := by
  simp only [symp, herm_add_left, mul_add, map_add]

theorem symp_add_right {A B : HSp D} (x y z : WA A B) : symp x (y + z) = symp x y + symp x z := by
  simp only [symp, herm_add_right, mul_add, map_add]

theorem symp_zero_left {A B : HSp D} (x : WA A B) : symp 0 x = 0 := by
  have := symp_add_left (0 : WA A B) 0 x
  rw [add_zero] at this
  exact left_eq_add.mp this

theorem symp_zero_right {A B : HSp D} (x : WA A B) : symp x 0 = 0 := by
  have := symp_add_right x (0 : WA A B) 0
  rw [add_zero] at this
  exact left_eq_add.mp this

theorem symp_neg_left {A B : HSp D} (x y : WA A B) : symp (-x) y = -symp x y := by
  have := symp_add_left (-x) x y
  rw [neg_add_cancel, symp_zero_left] at this
  exact eq_neg_of_add_eq_zero_left this.symm

def gMat {V : HSp D} (g : GA D V) : Matrix (Fin V.rank) (Fin V.rank) (AE D) := (matHom V g).1

theorem gMat_one {V : HSp D} : gMat (1 : GA D V) = 1 := by simp [gMat]

theorem gMat_mul {V : HSp D} (g g' : GA D V) : gMat (g * g') = gMat g * gMat g' := by simp [gMat]

def act {A B : HSp D} (p : GA D A × GA D B) (x : WA A B) : WA A B :=
  (HMul.hMul (HMul.hMul (gMat p.2) (colMat x)) (gMat p.1⁻¹))ᵀ

theorem act_one {A B : HSp D} (x : WA A B) : act 1 x = x := by
  simp [act, colMat, gMat_one]

theorem act_mul {A B : HSp D} (p q : GA D A × GA D B) (x : WA A B) : act (p * q) x = act p (act q x) := by
  simp only [act, colMat, Prod.fst_mul, Prod.snd_mul, _root_.mul_inv_rev, gMat_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]

def detA (V : HSp D) : GA D V →* (AE D)ˣ := Matrix.GeneralLinearGroup.det.comp (matHom V)

@[ext] structure Heis (A B : HSp D) where

  w : WA A B

  t : AF D.host.F

instance (A B : HSp D) : Group (Heis A B) where
  mul a b := ⟨a.w + b.w, a.t + b.t + half D * symp a.w b.w⟩
  one := ⟨0, 0⟩
  inv a := ⟨-a.w, -a.t + half D * symp a.w a.w⟩
  mul_assoc a b c := by
    refine Heis.ext (add_assoc _ _ _) ?_
    change a.t + b.t + half D * symp a.w b.w + c.t + half D * symp (a.w + b.w) c.w =
      a.t + (b.t + c.t + half D * symp b.w c.w) + half D * symp a.w (b.w + c.w)
    rw [symp_add_left, symp_add_right]; ring
  one_mul a := by
    refine Heis.ext (zero_add _) ?_
    change 0 + a.t + half D * symp 0 a.w = a.t
    rw [symp_zero_left]; ring
  mul_one a := by
    refine Heis.ext (add_zero _) ?_
    change a.t + 0 + half D * symp a.w 0 = a.t
    rw [symp_zero_right]; ring
  inv_mul_cancel a := by
    refine Heis.ext (neg_add_cancel _) ?_
    change -a.t + half D * symp a.w a.w + a.t + half D * symp (-a.w) a.w = 0
    rw [symp_neg_left]; ring

def trInf (D : D7) (x : Ainf D.host.F) : ℝ :=
  ∑ v : InfinitePlace D.host.F, (v.mult : ℝ) * (InfinitePlace.Completion.extensionEmbedding v (x v)).re

def IsStdChar (D : D7) (s : ℤˣ) (ψ : AddChar (AF D.host.F) ℂ) : Prop :=
  IsCharAF D.host.F ψ ∧
    ∀ x : Ainf D.host.F, psiInf D.host.F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((s : ℤ) : ℂ) * (trInf D x : ℂ))

def hsymp {A B : HSp D} (x x' : WA A B) : AF D.host.F := half D * symp x x'

def rho {A B : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (u : WA A B) : Module.End ℂ (WA A B → ℂ) where
  toFun := fun (f : WA A B → ℂ) (w : WA A B) => (ψ (hsymp w u) : ℂ) * f (w + u)
  map_add' f g := funext fun w => mul_add (ψ (hsymp w u) : ℂ) (f (w + u)) (g (w + u))
  map_smul' c f := funext fun w => mul_left_comm (ψ (hsymp w u) : ℂ) c (f (w + u))

theorem rho_apply {A B : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (u : WA A B) (f : WA A B → ℂ) (w : WA A B) :
    rho ψ u f w = (ψ (hsymp w u) : ℂ) * f (w + u) := rfl

theorem rho_mul {A B : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (u u' : WA A B) :
    rho ψ u * rho ψ u' = (ψ (hsymp u u') : ℂ) • rho ψ (u + u') := by
  refine LinearMap.ext fun f => funext fun w => ?_
  change (ψ (hsymp w u) : ℂ) * ((ψ (hsymp (w + u) u') : ℂ) * f (w + u + u')) =
    (ψ (hsymp u u') : ℂ) * ((ψ (hsymp w (u + u')) : ℂ) * f (w + (u + u')))
  rw [hsymp, hsymp, hsymp, hsymp, symp_add_left, symp_add_right, mul_add, mul_add, AddChar.map_add_eq_mul,
    AddChar.map_add_eq_mul, add_assoc]
  ring

def rhoHeis {A B : HSp D} (ψ : AddChar (AF D.host.F) ℂ) : Heis A B →* Module.End ℂ (WA A B → ℂ) where
  toFun a := (ψ a.t : ℂ) • rho ψ a.w
  map_one' := by
    refine LinearMap.ext fun f => funext fun w => ?_
    change (ψ 0 : ℂ) * ((ψ (hsymp w 0) : ℂ) * f (w + 0)) = f w
    rw [hsymp, symp_zero_right, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul, one_mul]
  map_mul' a b := by
    change (ψ (a.t + b.t + hsymp a.w b.w) : ℂ) • rho ψ (a.w + b.w) = _
    rw [smul_mul_smul_comm, rho_mul, smul_smul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]

def thetaFun (A B : HSp D) : (WA A B → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj 0

def realAd (D : D7) (s : InfinitePlace D.host.F → ℝ) : AF D.host.F :=
  pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (fun v => s v.1, 0)) 0

def realPt (D : D7) (p : (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ)) : AE D :=
  realAd D p.1 ⊗ₜ[D.host.F] (1 : D.host.E) + realAd D p.2 ⊗ₜ[D.host.F] D.host.xi0

structure IsTheta {A B : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (f : WA A B → ℂ) : Prop where
  law : ∀ γ ∈ WQ A B, ∀ w, f (γ + w) = (ψ (hsymp w γ) : ℂ) * f w
  smooth : ∀ w : WA A B, ContDiff ℝ ∞
    fun p : Fin A.rank → Fin B.rank → (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ) =>
      f (w + Matrix.of fun i j => realPt D (p i j))
  level : ∃ U : AddSubgroup (WA A B), IsOpen (U : Set (WA A B)) ∧
    ∀ u ∈ U, u.map (infPart D) = 0 → rho ψ u f = f

def Theta (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) : Submodule ℂ (WA A B → ℂ) where
  carrier := {f | IsTheta ψ f}
  zero_mem' := ⟨fun _ _ _ => by simp, fun _ => contDiff_const, ⊤, isOpen_univ, fun _ _ _ => map_zero _⟩
  add_mem' := by
    rintro f g ⟨f1, f2, U, hU, f3⟩ ⟨g1, g2, U', hU', g3⟩
    refine ⟨fun γ hγ w => ?_, fun w => (f2 w).add (g2 w), U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
    · simp only [Pi.add_apply, f1 γ hγ w, g1 γ hγ w, mul_add]
    · rw [map_add, f3 u hu.1 h0, g3 u hu.2 h0]
  smul_mem' := by
    rintro c f ⟨f1, f2, U, hU, f3⟩
    refine ⟨fun γ hγ w => ?_, fun w => (f2 w).const_smul c, U, hU, fun u hu h0 => ?_⟩
    · simp only [Pi.smul_apply, f1 γ hγ w, smul_eq_mul, mul_left_comm]
    · rw [map_smul, f3 u hu h0]

@[reducible] def measWA (A B : HSp D) : MeasurableSpace (WA A B) := borel _

def IsProbPair (A B : HSp D) (μ : @Measure (WA A B) (measWA A B)) (𝓕 : Set (WA A B)) : Prop :=
  letI := measWA A B
  μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (WQ A B) 𝓕 μ ∧ μ 𝓕 = 1

def IsNormSq {A B : HSp D} (f : WA A B → ℂ) (N : ENNReal) : Prop :=
  AllSome (fun m : @Measure (WA A B) (measWA A B) × Set (WA A B) => IsProbPair A B m.1 m.2) fun m =>
    letI := measWA A B
    ∫⁻ w in m.2, ‖f w‖ₑ ^ 2 ∂m.1 = N

def Implements {A B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (M : Module.End ℂ (Theta ψ A B))
    (p : GA D A × GA D B) : Prop :=
  ∀ (w : WA A B) (f f' : Theta ψ A B), (f' : WA A B → ℂ) = rho ψ w f →
    ((M f' : Theta ψ A B) : WA A B → ℂ) = rho ψ (act p w) (M f : Theta ψ A B)

def IsRoot (D : D7) (x u : (AE D)ˣ) : Prop := x * (cjU D x)⁻¹ = u

def IsDetRoot {V : HSp D} (x : (AE D)ˣ) (g : GA D V) : Prop := IsRoot D x (detA V g)

def IsTildeVal (D : D7) (χ : (AE D)ˣ →* Circle) (u : (AE D)ˣ) (c : Circle) : Prop :=
  AllSome (fun x => IsRoot D x u) fun x => χ x = c

def idemFin (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : AE D :=
  algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1))

open Classical in

def idemInf (D : D7) (v : InfinitePlace D.host.F) : AE D :=
  algebraMap (AF D.host.F) (AE D) (pairA D.host.F (Pi.single v 1) 0)

structure IsSplitIdem (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) : Prop where
  idem : IsIdempotentElem e
  orth : e * cj D e = 0
  sum : e + cj D e = idemFin D v

def wComp (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (e z : AE D) : Fv D.host.F v :=
  evalV D.host.F v (sndA D.host.F (trA D (e * z)))

def absV (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (y : Fv D.host.F v) : ℝ :=
  (WithZeroMulInt.toNNReal (e := (Ideal.absNorm v.asIdeal : NNReal))
    (by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)) (Valued.v y) : NNReal)

def IsIdemOf (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D) : Prop :=
  IsSplitIdem D v e ∧ ∀ x : 𝓞 D.host.E, x ∈ w.asIdeal ↔ absV D v (wComp D v e (incA D (x : D.host.E))) < 1

def IsAt {V : HSp D} (e : AE D) (g : GA D V) : Prop := (1 - e) • gMat g = (1 - e) • (1 : Matrix _ _ (AE D))

def atIdem {R : Type} [CommRing R] {e : R} (he : IsIdempotentElem e) : Rˣ →* Rˣ where
  toFun u := ⟨e * u + (1 - e), e * ↑u⁻¹ + (1 - e),
    by have h1 := u.mul_inv; have h2 := he.eq
       linear_combination (e * e) * h1 + (2 - (u : R) - ↑u⁻¹) * h2,
    by have h1 := u.mul_inv; have h2 := he.eq
       linear_combination (e * e) * h1 + (2 - (u : R) - ↑u⁻¹) * h2⟩
  map_one' := by ext; simp
  map_mul' u u' := by
    ext
    have h2 := he.eq
    simp only [Units.val_mul]
    linear_combination (-((u : R) * u') + u + u' - 1) * h2

def lagr (A B : HSp D) (e : AE D) : Set (WA A B) := {x | e • x = x}

def splitChar (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) {e : AE D} (he : IsIdempotentElem e) :
    GA D A × GA D B →* Circle :=
  ((χB.comp ((atIdem he).comp (detA A))).comp (MonoidHom.fst _ _))⁻¹ *
    (χA.comp ((atIdem he).comp (detA B))).comp (MonoidHom.snd _ _)

def splitMod (A B : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) (p : GA D A × GA D B) : ℝ :=
  absV D v (wComp D v e (detA A p.1 : (AE D)ˣ)) ^ ((B.rank : ℝ) / 2) *
    absV D v (wComp D v e (detA B p.2 : (AE D)ˣ)) ^ (-(A.rank : ℝ) / 2)

def splitScalar (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}
    (he : IsSplitIdem D v e) (p : GA D A × GA D B) : ℂ :=
  ((splitChar A B χA χB he.idem p : Circle) : ℂ) * (splitMod A B v e p : ℂ)

def splitOp (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}
    (he : IsSplitIdem D v e) (p : GA D A × GA D B) (Φ : WA A B → ℂ) : WA A B → ℂ :=
  fun x => splitScalar A B χA χB he p * Φ (act p⁻¹ x)

def ActsBy {A B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (e : AE D) (M : Module.End ℂ (Theta ψ A B)) (c : ℂ) : Prop :=
  ∀ l : Theta ψ A B →ₗ[ℂ] ℂ,
    (∀ y ∈ lagr A B (cj D e), ∀ f f' : Theta ψ A B, (f' : WA A B → ℂ) = rho ψ y f → l f' = l f) →
    ∀ f, l (M f) = c * l f

structure IsWeil {A B : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (χA χB : (AE D)ˣ →* Circle)
    (om : GA D A × GA D B →* Module.End ℂ (Theta ψ A B)) : Prop where
  impl : ∀ p, Implements (om p) p
  unitary : ∀ p (f : Theta ψ A B), ∃ N, N ≠ ⊤ ∧ IsNormSq (f : WA A B → ℂ) N ∧
    IsNormSq ((om p f : Theta ψ A B) : WA A B → ℂ) N
  cont : ∀ (f : Theta ψ A B) (w : WA A B), Continuous fun p => ((om p f : Theta ψ A B) : WA A B → ℂ) w
  rat : ∀ g ∈ GQ A, ∀ h ∈ GQ B, ∀ f : Theta ψ A B,
    thetaFun A B ((om (g, h) f : Theta ψ A B) : WA A B → ℂ) = thetaFun A B (f : WA A B → ℂ)
  split : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) (he : IsSplitIdem D v e) (p : GA D A × GA D B),
    IsAt (idemFin D v) p.1 → IsAt (idemFin D v) p.2 → ActsBy e (om p) (splitScalar A B χA χB he p)

def ClaimCoord (D : D7) : Prop := ∀ A B : HSp D,
  (WQ A B : Set (WA A B)) = Set.range (ofLin A B) ∧
  ∀ (x : A.V →ₗ[D.host.E] B.V) (y : B.V →ₗ[D.host.E] A.V), (∀ a b, B.hD (x a) b = A.hD a (y b)) →
    adj (ofLin A B x) = ofLin B A y

def ClaimForms (D : D7) : Prop := ∀ A B : HSp D,
  (∀ x x' : WA A B, herm x' x = cj D (herm x x')) ∧ (∀ x : WA A B, symp x x = 0) ∧
  (∀ x : WA A B, (∀ x', symp x x' = 0) → x = 0) ∧
  ∀ x ∈ WQ A B, ∀ x' ∈ WQ A B, symp x x' ∈ Set.range (algebraMap D.host.F (AF D.host.F))

def ClaimInvariant (D : D7) : Prop := ∀ A B : HSp D,
  (∀ (p : GA D A × GA D B) (x x' : WA A B), herm (act p x) (act p x') = herm x x') ∧
  ∀ g ∈ GQ A, ∀ h ∈ GQ B, ∀ x ∈ WQ A B, act (g, h) x ∈ WQ A B

def ClaimAdjoint (D : D7) : Prop := ∀ A B : HSp D,
  (∀ x : WA A B, adj (adj x) = x) ∧ (∀ x x' : WA A B, symp (adj x) (adj x') = -symp x x') ∧
  ∀ (g : GA D A) (h : GA D B) (x : WA A B), adj (act (g, h) x) = act (h, g) (adj x)

def ClaimStdChar (D : D7) : Prop :=
  (∀ s, ∃! ψ, IsStdChar D s ψ) ∧ ∀ s ψ, IsStdChar D s ψ → IsStdChar D (-s) ψ⁻¹

def ClaimTheta (D : D7) : Prop := ∀ (A B : HSp D) (s : ℤˣ) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D s ψ →
  Theta ψ A B ≠ ⊥ ∧ ∀ f ∈ Theta ψ A B, Continuous f ∧
    ∃ N, N ≠ ⊤ ∧ IsNormSq f N ∧ (N = 0 → f = 0) ∧ ∀ u, rho ψ u f ∈ Theta ψ A B ∧ IsNormSq (rho ψ u f) N

def ClaimRoots (D : D7) : Prop :=
  (∀ (V : HSp D) (g : GA D V), detA V g * cjU D (detA V g) = 1) ∧
  (∀ u : (AE D)ˣ, u * cjU D u = 1 → ∃ x, IsRoot D x u) ∧
  ∀ u x x' : (AE D)ˣ, IsRoot D x u → IsRoot D x' u → ∃ a, x' = idF D a * x

def ClaimIdem (D : D7) : Prop := ∀ v : HeightOneSpectrum (𝓞 D.host.F),
  (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.asIdeal.LiesOver v.asIdeal →
    ((∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.asIdeal.LiesOver v.asIdeal ∧ w' ≠ w) ↔ ∃! e, IsIdemOf D v w e)) ∧
  ∀ e, IsSplitIdem D v e → ∃! w : HeightOneSpectrum (𝓞 D.host.E), w.asIdeal.LiesOver v.asIdeal ∧ IsIdemOf D v w e

def ClaimSplit (D : D7) : Prop := ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) (he : IsSplitIdem D v e),
  (∀ (V : HSp D) (g : GA D V), IsAt (idemFin D v) g →
    IsDetRoot (atIdem he.idem (detA V g)) g ∧
    wComp D v e (detA V g : (AE D)ˣ) * wComp D v (cj D e) (detA V g : (AE D)ˣ) = 1 ∧
    ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∀ x, IsDetRoot x g →
      (1 - idemFin D v) * (x : AE D) = 1 - idemFin D v → χ x = χ (atIdem he.idem (detA V g))) ∧
  ∀ A B : HSp D,
    (∀ x ∈ lagr A B e, ∀ x' ∈ lagr A B e, symp x x' = 0) ∧
    (∀ p : GA D A × GA D B, ∀ x ∈ lagr A B e, act p x ∈ lagr A B e) ∧
    ∀ x ∈ lagr A B (idemFin D v), ∃ y ∈ lagr A B e, ∃ z ∈ lagr A B (cj D e), x = y + z

def ClaimWeil (D : D7) : Prop := ∀ (A B : HSp D) (s : ℤˣ) (ψ : AddChar (AF D.host.F) ℂ) (χA χB : (AE D)ˣ →* Circle),
  IsStdChar D s ψ → IsHeckeChar D χA → IsHeckeChar D χB → ResEta D χA A.rank → ResEta D χB B.rank →
    ∃! om : GA D A × GA D B →* Module.End ℂ (Theta ψ A B), IsWeil ψ χA χB om

example {A B : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (x x' : WA A B) : ψ⁻¹ (riem x x') = ψ (symp x x') := by
  simp [riem, AddChar.inv_apply]

example {A B : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (f : WA A B → ℂ) (w : WA A B) :
    thetaFun A B (rho ψ w f) = f w := by
  change (ψ (hsymp 0 w) : ℂ) * f (0 + w) = f w
  rw [hsymp, symp_zero_left, mul_zero, zero_add, AddChar.map_zero_eq_one, one_mul]

example : ((atIdem (R := ℚ × ℚ) (e := (1, 0)) (by simp [IsIdempotentElem])
    ⟨(2, 1 / 2), (1 / 2, 2), by simp [Prod.ext_iff], by simp [Prod.ext_iff]⟩ : (ℚ × ℚ)ˣ) : ℚ × ℚ) = (2, 1) := by
  simp [atIdem, Prod.ext_iff]

end GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices

end

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasSubstEv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.BetaInt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HStable
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.CoeffSyGauge

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

def lin (φ : Pt R 1 d) (m : ℕ) : Matrix (Fin d) (Fin d) R :=
  fun i j => coeff (Finsupp.single ((0 : Fin 1), j) m) (φ i)

def bil (f : PS R 2 d) (m n : ℕ) : Matrix (Fin d) (Fin d) R :=
  fun i j => coeff (Finsupp.single ((0 : Fin 2), i) m + Finsupp.single ((1 : Fin 2), j) n) f

def AxOne (f : PS R 2 d) : Prop := ev (n := 1) ![0, pt R d 0] f = 1 ∧ ev (n := 1) ![pt R d 0, 0] f = 1

def ptPow (R : Type) [CommRing R] {n : ℕ} (d p : ℕ) (j : Fin n) : Pt R n d := fun i => X (j, i) ^ p

def rho (B : FB R d O) (a : O) : Matrix (Fin d) (Fin d) R := lin (B.A.act a) 1

def pow1 (B : FB R d O) (m : ℕ) : PS R 2 d :=
  ∏ n ∈ Finset.range m, ev (n := 2) ![comp1 (B.A.act (n : O)) (pt R d 0), pt R d 0, pt R d 1] B.ph1

def pow2 (B : FB R d O) (m : ℕ) : PS R 2 d :=
  ∏ n ∈ Finset.range m, ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1), pt R d 1] B.ph2

def hw (B : FB R d O) (p : ℕ) : Matrix (Fin d) (Fin d) R := lin (B.A.act (p : O)) p

def am (B : FB R d O) (p : ℕ) : Matrix (Fin d) (Fin d) R := bil (pow1 B p) p 1

def rhoH (B : FB R d O) (a : O) : Module.End R ((Fin d → R) × (Fin d → R)) :=
  LinearMap.prod (Matrix.toLin' (rho B a) ∘ₗ LinearMap.fst R _ _)
    (Matrix.toLin' (rho B (star a)).transpose ∘ₗ LinearMap.snd R _ _ -
      Matrix.toLin' (bil (B.ad a) 1 1).transpose ∘ₗ LinearMap.fst R _ _)

def pairH (B : FB R d O) (y y' : (Fin d → R) × (Fin d → R)) : R :=
  y'.2 ⬝ᵥ y.1 - y.2 ⬝ᵥ y'.1 + y.1 ⬝ᵥ (bil B.sy 1 1).mulVec y'.1

def alpha (B : FB R d O) (p : ℕ) : (Fin d → R) →ₗ[R] (Fin d → R) × (Fin d → R) :=
  LinearMap.prod (Matrix.toLin' (hw B p)) (Matrix.toLin' (am B p).transpose)

def beta (B : FB R d O) (p : ℕ) : ((Fin d → R) × (Fin d → R)) →ₗ[R] (Fin d → R) :=
  Matrix.toLin' (hw B p).transpose ∘ₗ LinearMap.snd R _ _ -
    Matrix.toLin' (am B p - (hw B p).transpose * bil B.sy 1 1) ∘ₗ LinearMap.fst R _ _

structure IsMapOf {R₂ : Type} [CommRing R₂] (f : R →+* R₂) (B : FB R d O) (B₂ : FB R₂ d O) : Prop where

  F : ∀ i, B₂.G.F i = MvPowerSeries.map f (B.G.F i)

  act : ∀ a i, B₂.A.act a i = MvPowerSeries.map f (B.A.act a i)

  ph1 : B₂.ph1 = MvPowerSeries.map f B.ph1

  ph2 : B₂.ph2 = MvPowerSeries.map f B.ph2

  sy : B₂.sy = MvPowerSeries.map f B.sy

  ad : ∀ a, B₂.ad a = MvPowerSeries.map f (B.ad a)

structure IsIso (B B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d) : Prop where

  c₁ : ∀ i, constantCoeff (φ i) = 0

  c₂ : ∀ i, constantCoeff (ψ i) = 0

  inv₁ : comp1 φ ψ = pt R (n := 1) d 0

  inv₂ : comp1 ψ φ = pt R (n := 1) d 0

  ax : AxOne lam

  law : comp1 φ (B₂.G.add (pt R (n := 2) d 0) (pt R d 1)) = B.G.add (comp1 φ (pt R d 0)) (comp1 φ (pt R d 1))

  act : ∀ a, comp1 φ (B₂.A.act a) = comp1 (B.A.act a) φ

  ph1 : B₂.ph1 * ev (n := 3) ![B₂.G.add (pt R d 0) (pt R d 1), pt R d 2] lam =
    ev (n := 3) ![pt R d 0, pt R d 2] lam * ev (n := 3) ![pt R d 1, pt R d 2] lam *
      ev (n := 3) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1), comp1 φ (pt R d 2)] B.ph1

  ph2 : B₂.ph2 * ev (n := 3) ![pt R d 0, B₂.G.add (pt R d 1) (pt R d 2)] lam =
    ev (n := 3) ![pt R d 0, pt R d 1] lam * ev (n := 3) ![pt R d 0, pt R d 2] lam *
      ev (n := 3) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1), comp1 φ (pt R d 2)] B.ph2

  sy : B₂.sy * lam = ev (n := 2) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1)] B.sy *
    ev (n := 2) ![pt R d 1, pt R d 0] lam

  ad : ∀ a, B₂.ad a * ev (n := 2) ![pt R d 0, comp1 (B₂.A.act (star a)) (pt R d 1)] lam =
    ev (n := 2) ![comp1 (B₂.A.act a) (pt R d 0), pt R d 1] lam *
      ev (n := 2) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1)] (B.ad a)

def transH (φ ψ : Pt R 1 d) (lam : PS R 2 d) : ((Fin d → R) × (Fin d → R)) →ₗ[R] (Fin d → R) × (Fin d → R) :=
  LinearMap.prod (Matrix.toLin' (lin φ 1) ∘ₗ LinearMap.fst R _ _)
    (Matrix.toLin' (lin ψ 1).transpose ∘ₗ
      (LinearMap.snd R _ _ + Matrix.toLin' (bil lam 1 1).transpose ∘ₗ LinearMap.fst R _ _))

def ConjInj (B : FB R d O) (p : ℕ) : Prop := Function.Injective (alpha B p)

structure Family {K : Type} [Field K] (C : ACurve K) (p d : ℕ) (O : Type) [CommRing O] [StarRing O] where

  B : FB K d O

  Bi : ∀ i : C.I, FB (C.v i).valuationSubring d O

  BK : C.I → FB K d O

  Bk : ∀ i : C.I, FB (IsLocalRing.ResidueField (C.v i).valuationSubring) d O

  mapK : ∀ i, IsMapOf (C.v i).valuationSubring.subtype (Bi i) (BK i)

  mapk : ∀ i, IsMapOf (IsLocalRing.residue _) (Bi i) (Bk i)

  inj : ∀ i, ConjInj (Bk i) p

  φ : C.I → Pt K 1 d

  ψ : C.I → Pt K 1 d

  lam : C.I → PS K 2 d

  iso : ∀ i, IsIso B (BK i) (φ i) (ψ i) (lam i)

  ae : {i | ¬ ∀ a b, C.v i (lin (φ i) 1 a b) ≤ 1 ∧ C.v i (lin (ψ i) 1 a b) ≤ 1 ∧
    C.v i (bil (lam i) 1 1 a b) ≤ 1}.Finite

theorem rhoH_apply (B : FB R d O) (a : O) (y : (Fin d → R) × (Fin d → R)) :
    rhoH B a y = ((rho B a).mulVec y.1,
      (rho B (star a)).transpose.mulVec y.2 - (bil (B.ad a) 1 1).transpose.mulVec y.1) := by
  simp [rhoH]

theorem alpha_apply (B : FB R d O) (p : ℕ) (u : Fin d → R) :
    alpha B p u = ((hw B p).mulVec u, (am B p).transpose.mulVec u) := by
  simp [alpha]

theorem beta_apply (B : FB R d O) (p : ℕ) (y : (Fin d → R) × (Fin d → R)) :
    beta B p y = (hw B p).transpose.mulVec y.2 -
      (am B p - (hw B p).transpose * bil B.sy 1 1).mulVec y.1 := by
  simp [beta, Matrix.toLin'_apply, Matrix.sub_mulVec]

theorem transH_apply (φ ψ : Pt R 1 d) (lam : PS R 2 d) (y : (Fin d → R) × (Fin d → R)) :
    transH φ ψ lam y = ((lin φ 1).mulVec y.1,
      (lin ψ 1).transpose.mulVec (y.2 + (bil lam 1 1).transpose.mulVec y.1)) := by
  simp only [transH, LinearMap.prod_apply, Function.prod_apply, Pi.prod, LinearMap.add_apply, LinearMap.comp_apply,
    Matrix.toLin'_apply, LinearMap.fst_apply, LinearMap.snd_apply]

theorem rhoH_inr (B : FB R d O) (a : O) (φ : Fin d → R) :
    rhoH B a (0, φ) = (0, (rho B (star a)).transpose.mulVec φ) := by
  simp [rhoH_apply]

theorem rhoH_fst (B : FB R d O) (a : O) (y : (Fin d → R) × (Fin d → R)) :
    (rhoH B a y).1 = (rho B a).mulVec y.1 := by
  rw [rhoH_apply]

theorem beta_inr (B : FB R d O) (p : ℕ) (φ : Fin d → R) :
    beta B p (0, φ) = (hw B p).transpose.mulVec φ := by
  simp [beta_apply]

theorem dotProduct_beta (B : FB R d O) (p : ℕ) (u : Fin d → R) (y : (Fin d → R) × (Fin d → R)) :
    u ⬝ᵥ beta B p y = pairH B (alpha B p u) y := by
  rw [beta_apply, alpha_apply]
  simp only [pairH, Matrix.sub_mulVec, dotProduct_sub, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose]
  have key : u ⬝ᵥ Matrix.vecMul ((bil B.sy 1 1).mulVec y.1) (hw B p) =
      Matrix.vecMul ((hw B p).mulVec u) (bil B.sy 1 1) ⬝ᵥ y.1 := by
    rw [dotProduct_comm, ← Matrix.dotProduct_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec]
  rw [key, dotProduct_comm u]
  ring

theorem beta_alpha_apply (B : FB R d O) (p : ℕ) (u : Fin d → R) :
    beta B p (alpha B p u) = ((hw B p).transpose * (am B p).transpose - am B p * hw B p +
      (hw B p).transpose * bil B.sy 1 1 * hw B p).mulVec u := by
  rw [alpha_apply, beta_apply]
  simp only [Matrix.sub_mul, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  abel

def pairHL (B : FB R d O) : ((Fin d → R) × (Fin d → R)) →ₗ[R] ((Fin d → R) × (Fin d → R)) →ₗ[R] R :=
  LinearMap.mk₂ R (pairH B)
    (fun a b c => by simp only [pairH, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
    (fun r a b => by
      simp only [pairH, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
    (fun a b c => by
      simp only [pairH, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add, Matrix.mulVec_add]; ring)
    (fun r a b => by
      simp only [pairH, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        Matrix.mulVec_smul]; ring)

theorem pairHL_apply (B : FB R d O) (y y' : (Fin d → R) × (Fin d → R)) : pairHL B y y' = pairH B y y' := rfl

theorem pairH_inr (B : FB R d O) (y : (Fin d → R) × (Fin d → R)) (φ' : Fin d → R) :
    pairH B y (0, φ') = φ' ⬝ᵥ y.1 := by
  simp [pairH]

theorem pairHL_bijective (B : FB R d O) : Function.Bijective (pairHL B) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    have h : ∀ y', pairH B y y' = 0 := fun y' => by rw [← pairHL_apply, hy]; rfl
    have h1 : y.1 = 0 := by
      funext i
      simpa [pairH_inr] using h (0, Pi.single i 1)
    have h2 : y.2 = 0 := by
      funext i
      simpa [pairH, h1] using h (Pi.single i 1, 0)
    exact Prod.ext h1 h2
  · intro f
    let u : Fin d → R := fun i => f (0, Pi.single i 1)
    let φ : Fin d → R := fun i => u ⬝ᵥ (bil B.sy 1 1).mulVec (Pi.single i 1) - f (Pi.single i 1, 0)
    refine ⟨(u, φ), LinearMap.prod_ext ?_ ?_⟩
    · refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
      simp [pairHL_apply, pairH, φ]
    · refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
      simp [pairHL_apply, pairH, u]

theorem bil_one_eq_zero {m : ℕ} (hm : m ≠ 0) (n : ℕ) : bil (1 : PS R 2 d) m n = 0 := by
  ext i j
  simp only [bil, MvPowerSeries.coeff_one, Matrix.zero_apply]
  rw [if_neg]
  intro h
  have h0 := congrArg (fun f => f ((0 : Fin 2), i)) h
  simp at h0
  exact hm h0

theorem lin_pt_eq_one : lin (pt R (n := 1) d 0) 1 = 1 := by
  ext i j
  simp [lin, pt, MvPowerSeries.coeff_X, Matrix.one_apply, Finsupp.single_eq_single_iff]
  exact if_congr eq_comm rfl rfl

theorem rho_one_eq (B : FB R d O) : rho B 1 = 1 := by
  show lin (B.A.act 1) 1 = 1
  rw [B.A.one_act, lin_pt_eq_one]

theorem rhoH_one_eq (B : FB R d O) : rhoH B 1 = 1 := by
  refine LinearMap.ext fun y => ?_
  rw [rhoH_apply, star_one, rho_one_eq, B.ad_one, bil_one_eq_zero one_ne_zero]
  simp

theorem transH_refl : transH (pt R (n := 1) d 0) (pt R d 0) 1 = LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  simp [transH_apply, lin_pt_eq_one, bil_one_eq_zero]

theorem IsMapOf.refl (B : FB R d O) : IsMapOf (RingHom.id R) B B where
  F := fun _ => by simp
  act := fun _ _ => by simp
  ph1 := by simp
  ph2 := by simp
  sy := by simp
  ad := fun _ => by simp

theorem IsMapOf.trans {R₂ R₃ : Type} [CommRing R₂] [CommRing R₃] {f : R →+* R₂} {g : R₂ →+* R₃} {B : FB R d O}
    {B₂ : FB R₂ d O} {B₃ : FB R₃ d O} (h : IsMapOf f B B₂) (h' : IsMapOf g B₂ B₃) : IsMapOf (g.comp f) B B₃ where
  F := fun i => by rw [h'.F, h.F, MvPowerSeries.map_comp]; rfl
  act := fun a i => by rw [h'.act, h.act, MvPowerSeries.map_comp]; rfl
  ph1 := by rw [h'.ph1, h.ph1, MvPowerSeries.map_comp]; rfl
  ph2 := by rw [h'.ph2, h.ph2, MvPowerSeries.map_comp]; rfl
  sy := by rw [h'.sy, h.sy, MvPowerSeries.map_comp]; rfl
  ad := fun a => by rw [h'.ad, h.ad, MvPowerSeries.map_comp]; rfl

theorem ev_pt_self {n : ℕ} (a : Fin n → Pt R n d) (ha : ∀ j, a j = pt R d j) (f : PS R n d) : ev a f = f := by
  have hx : (fun q : Fin n × Fin d => a q.1 q.2) = MvPowerSeries.X := by
    funext q
    rw [ha]
    rfl
  show MvPowerSeries.subst (fun q : Fin n × Fin d => a q.1 q.2) f = f
  rw [hx, MvPowerSeries.subst_self]
  rfl

theorem germ_comp1_zero_point_left {n : ℕ} (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) : comp1 (pt R d 0) a = a := by
  funext i
  have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d => (![a] : Fin 1 → Pt R n d) q.1 q.2) :=
    ⟨fun q => by
      rcases q with ⟨j, k⟩
      fin_cases j
      simp [ha], fun _ => Set.toFinite _⟩
  show MvPowerSeries.subst (fun q : Fin 1 × Fin d => (![a] : Fin 1 → Pt R n d) q.1 q.2) (MvPowerSeries.X ((0 : Fin 1), i)) = a i
  rw [MvPowerSeries.subst_X hs]
  rfl

theorem IsIso.refl (B : FB R d O) : IsIso B B (pt R d 0) (pt R d 0) 1 := by
  have hc : ∀ {n : ℕ} (j : Fin n) (i : Fin d), constantCoeff (pt R d j i) = 0 := fun j i => by simp [pt]
  have e2 : ∀ f : PS R 2 d, ev (n := 2) ![pt R d 0, pt R d 1] f = f :=
    ev_pt_self _ fun j => by fin_cases j <;> rfl
  have e3 : ∀ f : PS R 3 d, ev (n := 3) ![pt R d 0, pt R d 1, pt R d 2] f = f :=
    ev_pt_self _ fun j => by fin_cases j <;> rfl
  refine ⟨hc _, hc _, germ_comp1_zero_point_left _ (hc _), germ_comp1_zero_point_left _ (hc _), ⟨ev_one _, ev_one _⟩, ?_, fun a => ?_,
    ?_, ?_, ?_, fun a => ?_⟩
  · rw [germ_comp1_zero_point_left _ (hc _), germ_comp1_zero_point_left _ (hc _), germ_comp1_zero_point_left]
    intro i
    change constantCoeff (ev _ _) = 0
    rw [e2, B.G.const]
  · rw [germ_comp1_zero_point_left _ (B.A.const a)]
    funext i
    exact (ev_pt_self _ (fun j => by fin_cases j; rfl) _).symm
  all_goals simp [germ_comp1_zero_point_left _ (hc _), e2, e3]

section Gauge

open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

theorem pairH_eq_betaH (B : FB R d O) (h : bil B.sy 1 1 = 0) (y y' : (Fin d → R) × (Fin d → R)) :
    pairH B y y' = betaH R y y' := by
  simp [pairH, h, betaH, dotProduct, Finset.sum_sub_distrib]

variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

def toHk (h : PS k 2 d) (y : (Fin d → R) × (Fin d → R)) : (Fin d → k) × (Fin d → k) :=
  (fun i => algebraMap R k (y.1 i),
    fun i => algebraMap R k (y.2 i) - (sg1 k h).mulVec (fun j => algebraMap R k (y.1 j)) i)

theorem range_toHk (h : PS k 2 d) : Set.range (toHk (R := R) k h) = Hset (R := R) k h := by
  ext ξ
  exact ⟨fun ⟨y, e⟩ => ⟨y.1, y.2, e.symm⟩, fun ⟨u, φ, e⟩ => ⟨(u, φ), e.symm⟩⟩

theorem bil_sy_gauge (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (i j : Fin d) :
    algebraMap R k (bil B.sy 1 1 i j) = sg1 k h j i - sg1 k h i j :=
  coeff_sy_gauge k B h hc i j

theorem pairH_gauge (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (y y' : (Fin d → R) × (Fin d → R)) :
    algebraMap R k (pairH B y y') = betaH k (toHk k h y) (toHk k h y') := by
  rw [toHk, toHk, betaH_expand]
  simp only [← bil_sy_gauge k B h hc, pairH, dotProduct, Matrix.mulVec, map_add, map_sub, map_sum, map_mul,
    Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem bil_ad_gauge (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (a : O) (i j : Fin d) :
    algebraMap R k (bil (B.ad a) 1 1 j i) =
      ((dAct k B (star a)).transpose * sg1 k h - sg1 k h * dAct k B a) i j :=
  coeff_ad_gauge k B h hc a i j

theorem rhoH_gauge (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (a : O)
    (y : (Fin d → R) × (Fin d → R)) : toHk k h (rhoH B a y) = OactH k B a (toHk k h y) := by
  have hA : ∀ b : O, (rho B b).map (algebraMap R k) = dAct k B b := fun b => by
    ext i j
    simp only [Matrix.map_apply, rho, lin, dAct, FB.actK, coeff_map]
  have hM : (bil (B.ad a) 1 1).transpose.map (algebraMap R k) =
      (dAct k B (star a)).transpose * sg1 k h - sg1 k h * dAct k B a := by
    ext i j
    exact bil_ad_gauge k B h hc a i j
  have hv : ∀ (M : Matrix (Fin d) (Fin d) R) (v : Fin d → R),
      (fun i => algebraMap R k (M.mulVec v i)) =
        (M.map (algebraMap R k)).mulVec fun j => algebraMap R k (v j) := fun M v =>
    funext fun i => RingHom.map_mulVec _ _ _ _
  have h1 := hv (rho B a) y.1
  have h2 := hv (rho B (star a)).transpose y.2
  have h3 := hv (bil (B.ad a) 1 1).transpose y.1
  rw [hA] at h1
  rw [Matrix.transpose_map, hA] at h2
  rw [hM] at h3
  rw [rhoH_apply, toHk, toHk, OactH]
  refine Prod.ext h1 ?_
  funext i
  have e : (fun i => algebraMap R k (y.2 i) - (sg1 k h).mulVec (fun j => algebraMap R k (y.1 j)) i) =
      (fun i => algebraMap R k (y.2 i)) - (sg1 k h).mulVec (fun j => algebraMap R k (y.1 j)) := rfl
  simp only [h1, e, Pi.sub_apply, map_sub, congrFun h2 i, congrFun h3 i, Matrix.mulVec_sub, Matrix.sub_mulVec,
    Matrix.mulVec_mulVec]
  ring

end Gauge

example (G : FGLaw R 1) (A : OAct O G) : pairH (FB.triv G A) (![1], 0) (0, ![1]) = 1 := by
  simp [pairH]

example (G : FGLaw R 1) (A : OAct O G) : pairH (FB.triv G A) (0, ![1]) (![1], 0) = -1 := by
  simp [pairH]

example (G : FGLaw R d) (A : OAct O G) (p : ℕ) (hp : p ≠ 0) (y : (Fin d → R) × (Fin d → R)) :
    beta (FB.triv G A) p y = (hw (FB.triv G A) p).transpose.mulVec y.2 ∧
      alpha (FB.triv G A) p y.1 = ((hw (FB.triv G A) p).mulVec y.1, 0) := by
  have h1 : am (FB.triv G A) p = 0 := by
    have : pow1 (FB.triv G A) p = 1 := by simp [pow1, FB.triv]
    rw [am, this, bil_one_eq_zero hp]
  have h2 : bil (FB.triv G A).sy 1 1 = 0 := bil_one_eq_zero one_ne_zero 1
  simp [beta_apply, alpha_apply, h1, h2]

example (c : R) : bil (1 + C c * X ((0 : Fin 2), (0 : Fin 1)) * X ((1 : Fin 2), (0 : Fin 1)) : PS R 2 1) 1 1 0 0 = c := by
  have := congrFun (congrFun (bil_one_eq_zero (R := R) (d := 1) one_ne_zero 1) 0) 0
  rw [bil] at this ⊢
  rw [map_add, this, mul_assoc, coeff_C_mul, X_def, X_def, monomial_mul_monomial, coeff_monomial_same]
  simp

end GlobalTheory.CompanionTheory.Ar.Conj

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.Vanishing.H0 GlobalTheory.HermTools GlobalTheory.HilbertSamuel
open GlobalTheory.AllWt (Psi secZ exOf wtOf cuspOn latOn normOn petOn GoodOn suppOn LiesOn LiesOff)
open GlobalTheory.FlagMod (FlagCover FlagModel Frames frX ev)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.CompHt (hodgeWt uPrime)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Data

variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

def tanOrd (Dw : Datum H) : Fin (dimFlag Dw) ≃ TIx Dw (psiSet H) := by
  classical exact (Fintype.equivFinOfCardEq (FlagTan.card_TIx (FlagTan.isHalf_psiSet H))).symm

variable {X Z} (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

abbrev toFlag : M.X ⟶ X.YY := M.σ ≫ inc₀ X Z

abbrev flagIdx (la : AllWt.Weight Dw) (k : X.F.J) : ((L₀ X Z la).pull M.σ).ι := ((common₀ X Z).pull M.σ).idx la k

open Classical in

def IsKS (ω : H0 M.str (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) M.off) : Prop :=
  ∀ (K : Type) [Field K] [Algebra c.F K] (P Q : FrPt Xo c K) (t : Ix Dw → Kˣ)
    (v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)) (z : Sp K ⟶ M.X)
    (zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)) (i : M.K.bundle.ι) (k : X.F.J) (O : M.X.Opens)
    (hO : O ≤ M.K.bundle.U i) (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hz : ⊤ ≤ z ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    (hi : ⊤ ≤ z ⁻¹ᵁ (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k)),
    X.F.ChartFr k (z ≫ toFlag M) hk Q → FrBor t Q P → IsTanFrame (psiSet H) P v →
    (∀ b, zv b ≫ toFlag M = X.ptY (v b)) →
    H0.val (B := LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi ω *
        (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det =
      (∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix).val * evalPt z O hz (M.K.jacobian i hO g)

theorem IsKS.val_eq {ω ω' : H0 M.str (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) M.off} (h : IsKS M ω)
    (h' : IsKS M ω') {K : Type} [Field K] [Algebra c.F K] {P Q : FrPt Xo c K} {t : Ix Dw → Kˣ}
    {v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)} {z : Sp K ⟶ M.X}
    {zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)} {i : M.K.bundle.ι} {k : X.F.J} {O : M.X.Opens}
    (hO : O ≤ M.K.bundle.U i) {g : Fin (dimFlag Dw) → Γ(M.X, O)} (hz : ⊤ ≤ z ⁻¹ᵁ O) {hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O}
    {hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k} (ho : ⊤ ≤ z ⁻¹ᵁ M.off) (hi) (hQ : X.F.ChartFr k (z ≫ toFlag M) hk Q)
    (ht : FrBor t Q P) (hv : IsTanFrame (psiSet H) P v) (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b))
    (hd : (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det ≠ 0) :
    H0.val (B := LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi ω =
      H0.val (B := LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi ω' :=
  mul_right_cancel₀ hd ((h K P Q t v z zv i k O hO g hz hzv hk ho hi hQ ht hv hl).trans
    (h' K P Q t v z zv i k O hO g hz hzv hk ho hi hQ ht hv hl).symm)

structure CanId where

  ω : H0 M.str (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) M.off

  unit : NowhereZero ω

  isKS : IsKS M ω

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw)

variable (Z) in

instance (priority := high) cuspAddCommGroup (la : AllWt.Weight Dw) : AddCommGroup (Cusp Z U la) :=
  Submodule.addCommGroup _

variable (Z) in

instance (priority := high) cuspModule (la : AllWt.Weight Dw) : Module c.F (Cusp Z U la) := Submodule.module _

variable (X Z) in

abbrev Choice : Type 1 :=
  Resol (common₀ X Z) (U₀ X Z) (dimFlag Dw) (space X Z U P.u₁) (space X Z U P.u₂)

variable {U P} (R : Choice X Z U P) (ω : CanId R.toModif)

def adjSec (h₁ : FreeOnOpen X Z U P.u₁) (j : ℕ) : Cusp Z U (P.wt j) →ₗ[c.F] H0 R.str (R.adj j) R.off :=
  (R.adjEquiv ω.ω ω.unit h₁ j (P.kap_add j)).toLinearMap ∘ₗ R.pullOff ∘ₗ cuspSec X Z U (P.wt j)

theorem adjSec_injective (h₁ : FreeOnOpen X Z U P.u₁) (j : ℕ) : Function.Injective (adjSec R ω h₁ j) :=
  (R.adjEquiv ω.ω ω.unit h₁ j (P.kap_add j)).injective.comp
    ((R.bijective_pullOff (isLB_L₀ X Z _)).1.comp (cuspSec_injective X Z U _))

theorem mulPole_adjSec (h₁ : FreeOnOpen X Z U P.u₁) (j : ℕ) (f : Cusp Z U (P.wt j)) :
    R.mulPole j R.off (adjSec R ω h₁ j f) = R.mulCan ω.ω (P.kap_add j) (R.pullOff (cuspSec X Z U _ f)) :=
  R.mulPole_adjEquiv _ ω.unit h₁ _ _ _

def adjGlobal (j : ℕ) : Submodule c.F (H0 R.str (R.adj j) R.off) := LinearMap.range (restr le_top)

variable (x : ℝ) {D : Formalism.BasicNotions.D7} (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D)
  (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r)

variable (Z U) in

abbrev CuspFrame (la : AllWt.Weight Dw) : Type :=
  LatFrame (normOn U x V dict Z (wtOf Dw la 0)) (latOn U Z (wtOf Dw la 0))

variable {x V dict} in

theorem nonempty_cuspFrame {la : AllWt.Weight Dw} (h : GoodOn U x V dict Z (wtOf Dw la 0)) :
    Nonempty (CuspFrame Z U x V dict la) :=
  let ⟨N, n, b, w, A, hf⟩ := CompHt.exists_isFrame CompHt.conj_comp_ne
    (fun σ f => CompHt.petOn_conj U x V dict Z _ σ f.1) h.1 h.2.1 h.2.2
  ⟨⟨N, n, b, w, A, hf⟩⟩

structure Ready : Prop where

  conn : GeometricallyConnected R.str

  one_le : 1 ≤ dimFlag Dw

  le_T : dimFlag Dw + 1 ≤ P.T

  ext₁ : Extends X Z U P.u₁

  ext₂ : Extends X Z U P.u₂

  free₁ : FreeOnOpen X Z U P.u₁

  free₂ : FreeOnOpen X Z U P.u₂

  good : ∀ j ≤ P.T, GoodOn U x V dict Z (wtOf Dw (P.wt j) 0)

  global_le : ∀ j ≤ P.T, adjGlobal R j ≤ LinearMap.range (adjSec R ω free₁ j)

  le_global : LinearMap.range (adjSec R ω free₁ 0) ≤ adjGlobal R 0

variable {R ω x V dict} (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂)
  (th : R.L.Sec) (k : Consts)

def Ready.geo : Geo c.F :=
  R.geo (dense_U₀ X Z) h.conn h.one_le h.free₁ h.free₂ h.ext₁.equiv h.ext₂.equiv f₁ f₂ th k.abelian₂

def Ready.data : Data c.F :=
  dataOf (S := fun j => Cusp Z U (P.wt j)) (Nm := fun j => normOn U x V dict Z (wtOf Dw (P.wt j) 0))
    (M := fun j => latOn U Z (wtOf Dw (P.wt j) 0)) (h.geo f₁ f₂ th k) P.T h.le_T (adjSec R ω h.free₁) (adjSec_injective R ω h.free₁)
    (fun j hj => nonempty_cuspFrame (h.good j hj)) h.global_le h.le_global k

namespace Ready

theorem data_numbers : (h.data f₁ f₂ th k).D = dimFlag Dw ∧ (h.data f₁ f₂ th k).T = P.T ∧ (h.data f₁ f₂ th k).j₀ = 1 ∧
    (h.data f₁ f₂ th k).n = f₁.n ∧ (h.data f₁ f₂ th k).abelian₂ = k.abelian₂ ∧ (h.data f₁ f₂ th k).beta = k.beta ∧
    (h.data f₁ f₂ th k).LamD = k.LamD ∧ (h.data f₁ f₂ th k).LamT = k.LamT ∧ (h.data f₁ f₂ th k).J = k.J :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

example : (h.data f₁ f₂ th k).U = R.off ∧ (h.data f₁ f₂ th k).L = LB.div ((L₀ X Z P.u₁).pull R.σ) R.Δ₁.P ∧
    (h.data f₁ f₂ th k).L₂ = LB.div ((L₀ X Z P.u₂).pull R.σ) R.Δ₂.P ∧
    (h.data f₁ f₂ th k).LA = (L₀ X Z (P.u₂ + dimFlag Dw • P.u₁)).pull R.σ ∧ (h.data f₁ f₂ th k).e = R.e :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def equivV {j : ℕ} (hj : j ≤ P.T) : Cusp Z U (P.wt j) ≃ₗ[c.F] (h.data f₁ f₂ th k).V j :=
  dataEquiv (S := fun j => Cusp Z U (P.wt j)) (Nm := fun j => normOn U x V dict Z (wtOf Dw (P.wt j) 0))
    (M := fun j => latOn U Z (wtOf Dw (P.wt j) 0)) (h.geo f₁ f₂ th k) P.T h.le_T (adjSec R ω h.free₁) (adjSec_injective R ω h.free₁)
    (fun j hj => nonempty_cuspFrame (h.good j hj)) h.global_le h.le_global k hj

theorem coe_equivV {j : ℕ} (hj : j ≤ P.T) (f : Cusp Z U (P.wt j)) :
    (h.equivV f₁ f₂ th k hj f).1 = adjSec R ω h.free₁ j f :=
  coe_dataEquiv (S := fun j => Cusp Z U (P.wt j)) (Nm := fun j => normOn U x V dict Z (wtOf Dw (P.wt j) 0))
    (M := fun j => latOn U Z (wtOf Dw (P.wt j) 0)) (h.geo f₁ f₂ th k) P.T h.le_T (adjSec R ω h.free₁)
    (adjSec_injective R ω h.free₁) (fun j hj => nonempty_cuspFrame (h.good j hj)) h.global_le h.le_global k hj f

theorem equivV_mem {j : ℕ} (hj : j ≤ P.T) (f : Cusp Z U (P.wt j)) :
    h.equivV f₁ f₂ th k hj f ∈ (h.data f₁ f₂ th k).M j ↔ f ∈ latOn U Z (wtOf Dw (P.wt j) 0) :=
  dataEquiv_mem (S := fun j => Cusp Z U (P.wt j)) (Nm := fun j => normOn U x V dict Z (wtOf Dw (P.wt j) 0))
    (M := fun j => latOn U Z (wtOf Dw (P.wt j) 0)) (h.geo f₁ f₂ th k) P.T h.le_T (adjSec R ω h.free₁)
    (adjSec_injective R ω h.free₁) (fun j hj => nonempty_cuspFrame (h.good j hj)) h.global_le h.le_global k hj f

theorem nrm_equivV {j : ℕ} (hj : j ≤ P.T) (σ : c.F →+* ℂ) (f : Cusp Z U (P.wt j)) :
    ((h.data f₁ f₂ th k).nm j).nrm σ (h.equivV f₁ f₂ th k hj f) = petOn U x V dict Z (wtOf Dw (P.wt j) 0) σ f :=
  nrm_dataEquiv (S := fun j => Cusp Z U (P.wt j)) (Nm := fun j => normOn U x V dict Z (wtOf Dw (P.wt j) 0))
    (M := fun j => latOn U Z (wtOf Dw (P.wt j) 0)) (h.geo f₁ f₂ th k) P.T h.le_T (adjSec R ω h.free₁)
    (adjSec_injective R ω h.free₁) (fun j hj => nonempty_cuspFrame (h.good j hj)) h.global_le h.le_global k hj σ f

theorem ofSec_comb (w : Cusp Z U P.u₁) : H0.ofSec R.str ⊤ ((h.data f₁ f₂ th k).comb (f₁.b.equivFun w)) =
    R.Δ₁.lift (h.ext₁.equiv w) :=
  (R.ofSec_comb R.Δ₁ h.ext₁.equiv f₁ k.abelian₂ _).trans (by rw [LinearEquiv.symm_apply_apply])

theorem mem_lattice (w : Cusp Z U P.u₁) :
    f₁.b.equivFun w ∈ (h.data f₁ f₂ th k).lattice ↔ w ∈ latOn U Z (wtOf Dw P.u₁ 0) := f₁.mem_span_iff w

theorem normAt_eq (σ : c.F →+* ℂ) (w : Cusp Z U P.u₁) :
    (h.data f₁ f₂ th k).normAt σ (f₁.b.equivFun w) = petOn U x V dict Z (wtOf Dw P.u₁ 0) σ w := f₁.isFrame.norm σ w

theorem ofSec_comb₂ (w : Cusp Z U P.u₂) : H0.ofSec R.str ⊤ ((h.data f₁ f₂ th k).second.comb (f₂.b.equivFun w)) =
    R.Δ₂.lift (h.ext₂.equiv w) :=
  (R.ofSec_comb R.Δ₂ h.ext₂.equiv f₂ k.abelian₂ _).trans (by rw [LinearEquiv.symm_apply_apply])

theorem mem_lattice₂ (w : Cusp Z U P.u₂) :
    f₂.b.equivFun w ∈ (h.data f₁ f₂ th k).second.lattice ↔ w ∈ latOn U Z (wtOf Dw P.u₂ 0) := f₂.mem_span_iff w

theorem normAt_eq₂ (σ : c.F →+* ℂ) (w : Cusp Z U P.u₂) :
    (h.data f₁ f₂ th k).second.normAt σ (f₂.b.equivFun w) = petOn U x V dict Z (wtOf Dw P.u₂ 0) σ w :=
  f₂.isFrame.norm σ w

theorem d_eq : (h.data f₁ f₂ th k).d = Module.finrank c.F (Cusp Z U (P.wt P.T)) :=
  (h.data f₁ f₂ th k).d_eq_finrank.trans (h.equivV f₁ f₂ th k le_rfl).finrank_eq.symm

theorem mulW_adjSec (j : ℕ) (w : Cusp Z U P.u₁) (f : Cusp Z U (P.wt j)) (g : Cusp Z U (P.wt (j + 1)))
    (hg : g.1 = w.1 * f.1) :
    (h.data f₁ f₂ th k).mulW j (f₁.b.equivFun w) (adjSec R ω h.free₁ j f) = adjSec R ω h.free₁ (j + 1) g := by
  have e₀ : cuspSec X Z U _ g = ((common₀ X Z).addChart (P.u₁_add_wt j)).mul (cuspSec X Z U _ w) (cuspSec X Z U _ f) :=
    sec₀_mul X Z ((exOf_add_zero _ _).symm.trans (congrArg (exOf Dw · 0) (P.u₁_add_wt j))) _ _ _ hg
  have e₁ : R.pullOff (cuspSec X Z U _ w) = restr le_top (H0.pull R.σ le_top (h.ext₁.equiv w).1) :=
    (congrArg R.pullOff (h.ext₁.restr_equiv w).symm).trans
      ((pull_restr _ _ _ _).trans (restr_pull (isLB_L₀ X Z _) _ _ _ _).symm)
  have e₂ : R.pullOff (cuspSec X Z U _ g) = (R.com.addChart (P.u₁_add_wt j)).mul (R.pullOff (cuspSec X Z U _ w))
      (R.pullOff (cuspSec X Z U _ f)) :=
    (congrArg R.pullOff e₀).trans (((common₀ X Z).addChart (P.u₁_add_wt j)).pull_mul R.σ R.off_eq.le _ _)
  have e₃ := R.adjEquiv_mul ω.ω ω.unit h.free₁ j (P.kap_add j) (P.kap_add (j + 1)) (P.u₁_add_wt j) (h.ext₁.equiv w)
    (R.pullOff (cuspSec X Z U _ f))
  have e₄ : restr le_top (R.Δ₁.lift (h.ext₁.equiv w)) =
      H0.ofSec R.str R.off ((h.data f₁ f₂ th k).comb (f₁.b.equivFun w)) :=
    (congrArg (restr le_top) (h.ofSec_comb f₁ f₂ th k w).symm).trans (restr_ofSec _ _)
  rw [← e₁, ← e₂, e₄] at e₃
  exact (LinearMap.congr_fun ((h.geo f₁ f₂ th k).mulW_apply j _) _).trans e₃.symm

end Ready

end Data

def be (N : OT.Num) : ℝ := Real.exp N.lbe

theorem log_be (N : OT.Num) : Real.log (be N) = N.P7 + 2 * (N.D : ℝ) * Real.log ((N.D : ℝ) * N.ka) + N.V :=
  Real.log_exp _

def Consts.ofTable (N : OT.Num) (h : 0 ≤ N.lbe) (lam lamD lamT J : ℝ) (hD : 0 ≤ lamD) (hT : 0 ≤ lamT) : Consts :=
  ⟨Real.exp lam, be N, Real.exp lamD, Real.exp lamT, J, Real.one_le_exp h, Real.one_le_exp hD, Real.one_le_exp hT⟩

example (N : OT.Num) (h : 0 ≤ N.lbe) : (Consts.ofTable N h 0 0 0 0 le_rfl le_rfl).beta = be N ∧ 1 ≤ be N :=
  ⟨rfl, Real.one_le_exp h⟩

end GlobalTheory.CompHS

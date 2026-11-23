import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj
open GlobalTheory.CoefModel (realGL)
open GlobalTheory.AutMult (toFin toInf)
open scoped Matrix ComplexOrder

namespace GlobalTheory.RealType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type}

section Frame

variable (θ : InfFam D) (V : HSp D) (lam : D.what₂.Tau → DomWeight V.rank) (B : D.what₂.Tau → GL (Fin V.rank) ℂ)

def realFr : GA D V →* (D.what₂.Tau → GL (Fin V.rank) ℂ) := (MulAut.conj B⁻¹).toMonoidHom.comp (realGL θ V)

def rhoFr : GA D V →* Module.End ℂ (VV ℂ lam) := (rhoK lam).comp (invTrK.comp (realFr θ V B))

theorem realFr_apply (g : GA D V) : realFr θ V B g = B⁻¹ * realGL θ V g * B := by
  simp [realFr]

theorem realFr_coe (g : GA D V) (τ : D.what₂.Tau) : (realFr θ V B g τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) =
    ((B τ)⁻¹ : GL (Fin V.rank) ℂ).1 * Formalism.L2.Pj.archM V (θ τ) g * (B τ).1 := by
  rw [realFr_apply]; rfl

theorem realFr_one : realFr θ V 1 = realGL θ V := MonoidHom.ext fun g => by simp [realFr_apply]

theorem rhoFr_apply (g : GA D V) : rhoFr θ V lam B g = rhoK lam (invTrK (realFr θ V B g)) := rfl

theorem rhoFr_one (g : GA D V) : rhoFr θ V lam 1 g = rhoK lam (invTrK (realGL θ V g)) := by
  rw [rhoFr_apply, realFr_one]

theorem rhoK_rhoFr (g : GA D V) (v : VV ℂ lam) :
    rhoK lam (invTrK B) (rhoFr θ V lam B g v) = rhoFr θ V lam 1 g (rhoK lam (invTrK B) v) := by
  rw [rhoFr_apply, rhoFr_one, realFr_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← map_mul,
    ← map_mul, ← mul_assoc, mul_inv_cancel_left]

variable {V}

theorem realFr_fin {g : GA D V} (hg : g ∈ GfC V) : realFr θ V B g = 1 := by
  have : realGL θ V g = 1 := funext fun τ => by
    show Formalism.UG.bc (θ τ) (infHom V g) = 1
    rw [show infHom V g = 1 from hg, map_one]
  rw [realFr_apply, this, mul_one, inv_mul_cancel]

theorem rhoFr_fin {g : GA D V} (hg : g ∈ GfC V) : rhoFr θ V lam B g = 1 := by
  rw [rhoFr_apply, realFr_fin θ B hg, map_one, map_one]

theorem realFr_toInf (g : GA D V) : realFr θ V B (toInf V g) = realFr θ V B g := by
  conv_rhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g, map_mul, realFr_fin θ B (toFin V g).2, mul_one]

variable {θ} (hθ : IsInfFam θ)
include hθ

variable {B}

theorem exists_realFr_eq (hB : ∀ τ, (B τ).1ᴴ * V.gram.map (tauE D τ) * (B τ).1 = 1) (u : D.what₂.Tau → GL (Fin V.rank) ℂ)
    (hu : ∀ τ, (u τ).1 ∈ Matrix.unitaryGroup (Fin V.rank) ℂ) : ∃ k : GinfC V, realFr θ V B k = u := by
  obtain ⟨h, e⟩ := (GlobalTheory.CoefModel.realGL_laws hθ V).2 (B * u * B⁻¹) fun τ => GlobalTheory.CoefModel.conj_unitary (hB τ) (hu τ)
  exact ⟨toInf V h, by rw [realFr_toInf, realFr_apply, e]; group⟩

variable (B)

theorem continuous_realFr (τ : D.what₂.Tau) : Continuous fun g => (realFr θ V B g τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) := by
  simp only [realFr_coe]
  exact (continuous_const.matrix_mul ((GlobalTheory.CoefModel.realGL_laws hθ V).1 τ)).matrix_mul continuous_const

theorem continuous_rhoFr (Λ : Module.Dual ℂ (VV ℂ lam)) (v : VV ℂ lam) : Continuous fun g => Λ (rhoFr θ V lam B g v) := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have h1 : ∀ τ : D.what₂.Tau, ((fun _ => 1 : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) τ).PosDef := fun _ => Matrix.PosDef.one
  have h := GlobalTheory.CoefModel.continuous_rhoH lam h1 (fun g => invTrK (realFr θ V B g)) (fun τ => by
    refine ((continuous_realFr B hθ τ).comp continuous_inv).matrix_transpose.congr fun g => ?_
    show (realFr θ V B g⁻¹ τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ = _
    rw [map_inv]
    rfl) (GlobalTheory.CoefModel.toHilb lam h1 v)
  exact (Λ ∘ₗ (GlobalTheory.CoefModel.toHilb lam h1).symm.toLinearMap).continuous_of_finiteDimensional.comp h

end Frame

section Vertex

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T} (θ : InfFam D) (N : Std G U) (X : Node)

def realAt : GA D (G.V X) →* (D.what₂.Tau → GL (Fin (G.V X).rank) ℂ) := realFr θ _ (embGL (tauE D) (N.fr X))

def rhoAt : GA D (G.V X) →* Module.End ℂ (VV ℂ (wt G X)) := rhoFr θ _ (wt G X) (embGL (tauE D) (N.fr X))

def realFn (Λ : Module.Dual ℂ (VV ℂ (wt G X))) (V : FinPt G X → VV ℂ (wt G X)) : Fn G X :=
  fun g => Λ (rhoAt θ N X g⁻¹ (V (toFin _ g)))

theorem rhoAt_apply (g : GA D (G.V X)) : rhoAt θ N X g = rhoK (wt G X) (invTrK (realAt θ N X g)) := rfl

theorem rhoVr_rhoAt (g : GA D (G.V X)) (v : VV ℂ (wt G X)) : rhoVr (tauE D) (wt G X) (N.fr X) (rhoAt θ N X g v) =
    rhoFr θ _ (wt G X) 1 g (rhoVr (tauE D) (wt G X) (N.fr X) v) := rhoK_rhoFr θ _ _ _ g v

variable {X}

@[simp] theorem rhoAt_fin (y : FinPt G X) : rhoAt θ N X y = 1 := rhoFr_fin θ _ _ y.2

theorem frC_on (hX : DefNode D.R.m X) (τ : D.what₂.Tau) :
    (N.frC X τ)ᴴ * (G.V X).gram.map (tauE D τ) * N.frC X τ = 1 := by
  have h := congrArg (·.map (tauE D τ)) (N.fr_on X hX)
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
  rw [← h, Std.frC]
  congr 2
  ext a b
  exact (D.sp.cm.cmUnram.2.1 (tauE D τ) _).symm

variable (Λ : Module.Dual ℂ (VV ℂ (wt G X))) (V : FinPt G X → VV ℂ (wt G X))

theorem realFn_apply (g : GA D (G.V X)) : realFn θ N X Λ V g = Λ (rhoAt θ N X g⁻¹ (V (toFin _ g))) := rfl

@[simp] theorem realFn_fin (y : FinPt G X) : realFn θ N X Λ V y = Λ (V y) := by
  rw [realFn_apply, ← Subgroup.coe_inv, rhoAt_fin, GlobalTheory.AutMult.toFin_coe]; rfl

theorem realFn_one : realFn θ N X Λ V 1 = Λ (V 1) := realFn_fin θ N Λ V 1

theorem realFn_mul (g h : GA D (G.V X)) :
    realFn θ N X Λ V (g * h) = realFn θ N X (Λ ∘ₗ rhoAt θ N X h⁻¹) (fun y => V (y * toFin _ h)) g := by
  rw [realFn_apply, mul_inv_rev, map_mul, map_mul]; rfl

theorem realFn_mul_fin (g : GA D (G.V X)) (k : FinPt G X) :
    realFn θ N X Λ V (g * k) = realFn θ N X Λ (fun y => V (y * k)) g := by
  rw [realFn_mul, ← Subgroup.coe_inv, rhoAt_fin, GlobalTheory.AutMult.toFin_coe]; rfl

variable (X) in

theorem exists_realFn_ne_zero : ∃ (Λ : Module.Dual ℂ (VV ℂ (wt G X))) (v : VV ℂ (wt G X)),
    realFn θ N X Λ (fun _ => v) 1 ≠ 0 := by
  haveI : Nontrivial (VV ℂ (wt G X)) :=
    GlobalTheory.CoefModel.nontrivial_Hilb (wt G X) (G := fun _ => 1) fun _ => Matrix.PosDef.one
  obtain ⟨v, hv⟩ := exists_ne (0 : VV ℂ (wt G X))
  obtain ⟨Λ, h⟩ := not_forall.1 (mt (Module.forall_dual_apply_eq_zero_iff ℂ v).1 hv)
  exact ⟨Λ, v, by rwa [realFn_one]⟩

variable {θ} (hθ : IsInfFam θ)
include hθ

theorem exists_realAt_eq (hX : DefNode D.R.m X) (u : D.what₂.Tau → GL (Fin (G.V X).rank) ℂ)
    (hu : ∀ τ, (u τ).1 ∈ Matrix.unitaryGroup (Fin (G.V X).rank) ℂ) : ∃ k : GinfC (G.V X), realAt θ N X k = u :=
  exists_realFr_eq (B := embGL (tauE D) (N.fr X)) hθ (frC_on N hX) u hu

theorem continuous_rhoAt (v : VV ℂ (wt G X)) : Continuous fun g => Λ (rhoAt θ N X g v) := continuous_rhoFr _ _ hθ Λ v

end Vertex

section SlopeTestRemainingChoices

variable {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)

theorem unitaryEmbedding_mul (h h' : GA D A) : stabilizerEmbedding d (h * h') = stabilizerEmbedding d h * stabilizerEmbedding d h' := by
  obtain ⟨a1, a2⟩ := (embRel_iff d h _).2 rfl
  obtain ⟨b1, b2⟩ := (embRel_iff d h' _).2 rfl
  refine ((embRel_iff d _ _).1 ⟨?_, fun x hx => ?_⟩).symm
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, b1, ← Matrix.mul_assoc, a1, Matrix.mul_assoc]
  · rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, b2 x hx, a2 x hx]

theorem Emb_map_eq_one {R : Type} [CommRing R] (π : AE D →+* R) {h : GA D A} (hy : (matHom A h).1.map π = 1) :
    (matHom B (stabilizerEmbedding d h)).1.map π = 1 := by
  have hg := (embRel_iff d h _).2 rfl
  generalize stabilizerEmbedding d h = g at hg
  set P := frameMat B A d.ι
  set C := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * B.gram
  have hG : C * P = A.gram := GlobalTheory.AutFunCounterexample.gram_pull B A d.ι d.isom
  set N : Matrix (Fin B.rank) (Fin B.rank) D.host.E := 1 - P * (A.gram⁻¹ * C) with hN
  have hC : C * N = 0 := by
    rw [hN, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hG, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit, Matrix.one_mul, sub_self]
  have h1 : (matHom B g).1 * N.map (incA D) = N.map (incA D) := by
    ext i j
    exact congr_fun (hg.2 (fun k => N k j) (by funext k; exact congr_fun (congr_fun hC k) j)) i
  refine GlobalTheory.AutFunCounterexample.split_gen (π.comp (incA D)) P (A.gram⁻¹ * C) ((matHom B g).1.map π) 1 ?_ ?_
  · have := congrArg (·.map π) h1
    simp only [Matrix.map_mul] at this
    exact this.trans (Matrix.one_mul _).symm
  · have := congrArg (·.map π) hg.1
    simp only [Matrix.map_mul, hy, Matrix.mul_one] at this
    exact this.trans (Matrix.one_mul _).symm

theorem Emb_mem_inf {k : GA D A} (hk : k ∈ GinfC A) : stabilizerEmbedding d k ∈ GinfC B :=
  Units.ext (Emb_map_eq_one d
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom (congrArg Units.val hk))

theorem Emb_fin (y : GfC A) : stabilizerEmbedding d y = finEmb d y := ((embRel_iff d _ _).1 (finEmb_rel d y)).symm

variable {θ : InfFam D} (hθ : IsInfFam θ)
include hθ

theorem archM_Emb (h : GA D A) (τ : D.what₂.Tau) :
    Formalism.L2.Pj.archM B (θ τ) (stabilizerEmbedding d h) * (frameMat B A d.ι).map (tauE D τ) =
      (frameMat B A d.ι).map (tauE D τ) * Formalism.L2.Pj.archM A (θ τ) h ∧
    Formalism.L2.Pj.archM B (θ τ) (stabilizerEmbedding d h) * d.a.map (tauE D τ) = d.a.map (tauE D τ) := by
  obtain ⟨a1, a2⟩ := (embRel_iff d h _).2 rfl
  let π : AE D →+* ℂ := (θ τ).comp (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have e : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E), (M.map (incA D)).map π = M.map (tauE D τ) := fun M => by
    ext i j
    exact (hθ τ).1 _
  have a3 : HMul.hMul (matHom B (stabilizerEmbedding d h)).1 (d.a.map (incA D)) = d.a.map (incA D) := by
    ext i j
    exact congr_fun (a2 (fun k => d.a k j) (by funext k; exact congr_fun (congr_fun d.perp k) j)) i
  have b1 := congrArg (·.map π) a1
  have b3 := congrArg (·.map π) a3
  simp only [Matrix.map_mul, e] at b1 b3
  exact ⟨b1, b3⟩

end SlopeTestRemainingChoices

theorem isBlock_conj {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1) (b' : GL (Fin N) K) (b : GL (Fin n) K)
    {g' : Matrix (Fin N) (Fin N) K} {g : Matrix (Fin n) (Fin n) K} {P : Matrix (Fin N) (Fin n) K} {z : Matrix (Fin N) (Fin 1) K}
    (h1 : ∀ i k, b'.1 i (Formalism.L2.Col.Br.iC hN k) = (P * b.1) i k) (h2 : ∀ i, b'.1 i (Formalism.L2.Col.Br.iL hN) = z i 0)
    (hP : g' * P = P * g) (hz : g' * z = z) :
    GlobalTheory.BranchFormula.IsBlock hN ((b'⁻¹).1 * g' * b'.1) ((b⁻¹).1 * g * b.1) 1 := by
  have col : ∀ {r : Type} (f : r → Fin N) (M : Matrix (Fin N) (Fin N) K),
      M * (1 : Matrix (Fin N) (Fin N) K).submatrix id f = M.submatrix id f := fun f M => by
    ext i k
    simp [Matrix.mul_apply, Matrix.one_apply]
  have e1 : b'.1 * (1 : Matrix (Fin N) (Fin N) K).submatrix id (Formalism.L2.Col.Br.iC hN) = P * b.1 := by
    rw [col]; ext i k; exact h1 i k
  have e2 : b'.1 * (1 : Matrix (Fin N) (Fin N) K).submatrix id (fun _ : Fin 1 => Formalism.L2.Col.Br.iL hN) = z := by
    rw [col]; ext i k; rw [Subsingleton.elim k 0]; exact h2 i
  have c1 : ((b'⁻¹).1 * g' * b'.1).submatrix id (Formalism.L2.Col.Br.iC hN) =
      (1 : Matrix (Fin N) (Fin N) K).submatrix id (Formalism.L2.Col.Br.iC hN) * ((b⁻¹).1 * g * b.1) := by
    have e : P * g * b.1 = P * b.1 * ((b⁻¹).1 * g * b.1) := by
      rw [Matrix.mul_assoc P b.1, ← Matrix.mul_assoc b.1, ← Matrix.mul_assoc b.1, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc]
    rw [← col, Matrix.mul_assoc, e1, Matrix.mul_assoc, ← Matrix.mul_assoc g', hP, e, ← e1, ← Matrix.mul_assoc (b'⁻¹).1,
      ← Matrix.mul_assoc (b'⁻¹).1, Units.inv_mul, Matrix.one_mul]
  have c2 : ((b'⁻¹).1 * g' * b'.1).submatrix id (fun _ : Fin 1 => Formalism.L2.Col.Br.iL hN) =
      (1 : Matrix (Fin N) (Fin N) K).submatrix id (fun _ : Fin 1 => Formalism.L2.Col.Br.iL hN) := by
    rw [← col, Matrix.mul_assoc, e2, Matrix.mul_assoc, hz, ← e2, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have hne : ∀ a : Fin n, Formalism.L2.Col.Br.iC hN a ≠ Formalism.L2.Col.Br.iL hN := fun a h => absurd (congrArg Fin.val h) a.2.ne
  have hinj : Function.Injective (Formalism.L2.Col.Br.iC hN) := fun a b h => Fin.ext (congrArg Fin.val h :)
  generalize (b'⁻¹).1 * g' * b'.1 = M at c1 c2
  generalize (b⁻¹).1 * g * b.1 = m at c1
  refine ⟨fun a k => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · simpa [Matrix.mul_apply, Matrix.one_apply, hinj.eq_iff] using congr_fun (congr_fun c1 (Formalism.L2.Col.Br.iC hN a)) k
  · simpa [Matrix.one_apply, hne] using congr_fun (congr_fun c2 (Formalism.L2.Col.Br.iC hN a)) 0
  · simpa [Matrix.mul_apply, Matrix.one_apply, (hne _).symm] using congr_fun (congr_fun c1 (Formalism.L2.Col.Br.iL hN)) a
  · exact (congr_fun (congr_fun c2 (Formalism.L2.Col.Br.iL hN)) 0).trans (Matrix.one_apply_eq _)

section Top

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T} {θ : InfFam D} (hθ : IsInfFam θ) (N : Std G U)
include hθ

theorem isBlock_realAt (h : GA D (G.V (.grid D.R.m D.R.m))) (τ : D.what₂.Tau) :
    GlobalTheory.BranchFormula.IsBlock G.sp.topDec.rank.symm (realAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec h) τ).1
      (realAt θ N (.grid D.R.m D.R.m) h τ).1 1 := by
  obtain ⟨a1, a2⟩ := archM_Emb G.sp.topDec hθ h τ
  rw [realAt, realAt, realFr_coe, realFr_coe]
  refine isBlock_conj _ _ _ (fun i k => ?_) (fun i => ?_) a1 a2
  swap
  · exact congrArg (tauE D τ) (N.fr_last i)
  refine (congrArg (tauE D τ) (N.fr_top i k)).trans ?_
  exact congr_fun (congr_fun (Matrix.map_mul (f := tauE D τ)) i) k

theorem isBlock_invTrK_realAt (h : GA D (G.V (.grid D.R.m D.R.m))) (τ : D.what₂.Tau) :
    GlobalTheory.BranchFormula.IsBlock G.sp.topDec.rank.symm (invTrK (realAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec h)) τ).1
      (invTrK (realAt θ N (.grid D.R.m D.R.m) h) τ).1 1 := by
  have e : stabilizerEmbedding G.sp.topDec h⁻¹ = (stabilizerEmbedding G.sp.topDec h)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← unitaryEmbedding_mul, inv_mul_cancel]
    exact mul_left_cancel (a := stabilizerEmbedding G.sp.topDec 1) (by rw [← unitaryEmbedding_mul, mul_one, mul_one])
  have := (isBlock_realAt hθ N h⁻¹ τ).transpose
  rw [e, map_inv, map_inv] at this
  exact this

end Top

section Examples

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T} (θ : InfFam D) (N : Std G U) (X : Node)

example : ∃ Λ V, realFn θ N X Λ V ≠ 0 :=
  let ⟨Λ, v, h⟩ := exists_realFn_ne_zero θ N X
  ⟨Λ, fun _ => v, fun e => h (congrFun e 1)⟩

example (Λ) (V : FinPt G X → VV ℂ (wt G X)) (k : FinPt G X) (h : ∀ y, V (y * k) = V y) (g : GA D (G.V X)) :
    realFn θ N X Λ V (g * k) = realFn θ N X Λ V g := by
  simp only [realFn_mul_fin, h]

example (k : GA D (G.V X)) (c : D.what₂.Tau → ℂˣ) (h : ∀ τ, realAt θ N X k τ = Matrix.GeneralLinearGroup.scalar _ (c τ))
    (v : D.what₂.Tau × Fin (G.V X).rank × Fin (G.V X).rank) :
    trAct (invTrK (realAt θ N X k)) (MvPolynomial.X v) = MvPolynomial.C ((c v.1 : ℂ)⁻¹) * MvPolynomial.X v := by
  simp [trAct, Formalism.GradedWeylDivisibility.blockAct, invTrK_coe, h, ← map_inv, Matrix.diagonal_apply, apply_ite]

end Examples

end GlobalTheory.RealType

end

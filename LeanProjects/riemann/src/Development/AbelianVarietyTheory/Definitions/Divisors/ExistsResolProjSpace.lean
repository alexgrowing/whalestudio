import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.Vanishing.H0 GlobalTheory.HermTools GlobalTheory.ChowHt
open GlobalTheory.Adelic GlobalTheory.HilbertSamuel
open scoped Matrix ComplexOrder

variable {F : Type} [Field F] [NumberField F]

section Frame

variable {V : Type} [AddCommGroup V] [Module F V] [Module (𝓞 F) V]

structure LatFrame (Nm : (F →+* ℂ) → V → ℝ) (M : Submodule (𝓞 F) V) where

  N : ℕ

  n : ℕ

  b : Module.Basis (Fin N) F V

  w : Matrix (Fin N) (Fin n) F

  A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ

  isFrame : CompHt.IsFrame Nm M b w A

namespace LatFrame

variable {Nm : (F →+* ℂ) → V → ℝ} {M : Submodule (𝓞 F) V} (f : LatFrame Nm M)

def gram (σ : F →+* ℂ) : Matrix (Fin f.N) (Fin f.N) ℂ := (f.A σ)⁻¹ᴴ * (f.A σ)⁻¹

theorem posDef_gram (σ : F →+* ℂ) : (f.gram σ).PosDef :=
  Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2
    (Matrix.isUnit_nonsing_inv_iff.2 ((Matrix.isUnit_iff_isUnit_det _).2 (f.isFrame.herm σ).isUnit)))

theorem form_gram (σ : F →+* ℂ) (x : Fin f.N → ℂ) :
    star x ⬝ᵥ f.gram σ *ᵥ x = ((frameNorm (f.A σ) x ^ 2 : ℝ) : ℂ) := by
  rw [frameNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), gram, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  simp [dotProduct, Complex.conj_mul']

def fam : HermFam F V := ofGram f.b f.gram f.posDef_gram

theorem nrm_fam (σ : F →+* ℂ) (x : V) : f.fam.nrm σ x = Nm σ x := by
  rw [← f.isFrame.norm σ x]
  exact (congrArg (fun z : ℂ => Real.sqrt z.re) (f.form_gram σ _)).trans
    (by rw [Complex.ofReal_re]; exact Real.sqrt_sq (Real.sqrt_nonneg _))

theorem isConjInv_fam : f.fam.IsConjInv := isConjInv_ofGram _ _ fun σ i j => by
  let P := f.gram (ComplexEmbedding.conjugate σ) - (f.gram σ).map (starRingEnd ℂ)
  have h₀ : ∀ y, star y ⬝ᵥ P *ᵥ y = 0 := fun y => by
    have e : star y ⬝ᵥ (f.gram σ).map (starRingEnd ℂ) *ᵥ y =
        starRingEnd ℂ (star (star y) ⬝ᵥ f.gram σ *ᵥ star y) := by
      simp [dotProduct, Matrix.mulVec]
    have c := f.isFrame.conj σ (star y)
    simp only [Pi.star_apply, RCLike.star_def, Complex.conj_conj] at c
    rw [Matrix.sub_mulVec, dotProduct_sub, e, f.form_gram, f.form_gram, Complex.conj_ofReal, ← c]
    exact sub_self _
  have h₁ : P.PosSemidef := Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((f.posDef_gram _).1.sub ((f.posDef_gram σ).1.map _ fun _ => rfl)) fun y => (h₀ y).ge
  have := congrFun ((h₁.dotProduct_mulVec_zero_iff (Pi.single j 1)).1 (h₀ _)) i
  simpa [P, sub_eq_zero] using this

include f in

theorem isFull [IsScalarTower (𝓞 F) F V] : IsFull M := by
  refine ⟨f.isFrame.span ▸ Submodule.fg_span (Set.finite_range _), top_le_iff.1 fun x _ => ?_⟩
  have h : f.b.equivFun x ∈ Submodule.span F (Set.range f.w.col) := f.isFrame.full ▸ trivial
  rw [← f.b.equivFun.symm_apply_apply x]
  refine Submodule.span_le.2 ?_ (Submodule.apply_mem_span_image_of_mem_span f.b.equivFun.symm.toLinearMap h)
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  exact Submodule.subset_span (f.isFrame.span.le (Submodule.subset_span ⟨k, (f.b.equivFun_symm_apply _).symm⟩))

end LatFrame

end Frame

section Moving

variable {Y : Scheme.{0}} {p : Y ⟶ Sp F} {U : Y.Opens} {D : ℕ} {B : LB Y}

omit [NumberField F] in

theorem restr_pull (hB : B.IsLB) {T : Scheme.{0}} (r : T ⟶ Y) {O O' : T.Opens} (h : O ≤ r ⁻¹ᵁ U) (h' : O' ≤ O)
    (f : H0 p B U) : restr h' (H0.pull r h f) = H0.pull r (h'.trans h) f :=
  ext_germ fun z hz => (exists_chart (LB.isLB_pull hB r) z).imp fun i hi => ⟨hi,
    by
    rw [germ_restr, germ_pull, germ_pull]⟩

def NoBase (hB : B.IsLB) (W : Submodule F (H0 p B ⊤)) (U : Y.Opens) : Prop := ∀ y ∈ U, y ∉ (baseIdeal hB W).support

namespace Modif

variable (M : Modif p U D)

def bd : Closeds M.X := M.opn.compl

def off : M.X.Opens := M.bd.compl

theorem off_eq : M.off = M.σ ⁻¹ᵁ U := Opens.compl_compl _

def pullOff : H0 p B U →ₗ[F] H0 M.str (B.pull M.σ) M.off := H0.pull M.σ M.off_eq.le

theorem bijective_pullOff (hB : B.IsLB) : Function.Bijective (M.pullOff (B := B)) :=
  have := M.iso
  (isoOver_of_isIso M.σ).bijective_pull hB _ M.off_eq.ge

def K : CanonLB M.str D := CanonLB.all _ _

variable {hB : B.IsLB} {W : Submodule F (H0 p B ⊤)} (Δ : Cartier ((baseIdeal hB W).comap M.σ))

theorem notMem_support (h : NoBase hB W U) : ∀ z ∈ M.off, z ∉ ((baseIdeal hB W).comap M.σ).support := fun z hz => by
  rw [Scheme.IdealSheafData.support_comap]
  exact h _ (M.off_eq.le hz)

theorem lift_injective [IsReduced Y] (hU : Dense (U : Set Y)) : Function.Injective Δ.lift := fun w w' e => by
  refine Subtype.ext (restr_injective_of_dense le_top hU ((M.bijective_pull hB).1 ?_))
  have := congrArg (fun s => restr (le_top : M.opn ≤ ⊤) (Δ.incl ⊤ s)) e
  simp only [Δ.incl_lift] at this
  exact (pull_restr _ _ _ _).trans ((restr_pull hB _ _ _ _).symm.trans
    (this.trans ((restr_pull hB _ _ _ _).trans (pull_restr _ _ _ _).symm)))

variable {V : Type} [AddCommGroup V] [Module F V] [Module (𝓞 F) V] {Nm : (F →+* ℂ) → V → ℝ} {Lt : Submodule (𝓞 F) V}
  (φ : V ≃ₗ[F] W) (f : LatFrame Nm Lt)

def basisSec (j : Fin f.N) : Δ.moving.Sec := toSec (Δ.lift (φ (f.b j)))

abbrev sys (abelian₂ : ℝ) : HermSys F where
  Y := M.X
  str := M.str
  D := D
  L := Δ.moving
  isLB := Δ.isLB_moving
  N := f.N
  b := M.basisSec Δ φ f
  n := f.n
  w := f.w
  A := f.A
  abelian₂ := abelian₂

theorem ofSec_comb (abelian₂ : ℝ) (u : Fin f.N → F) :
    H0.ofSec M.str ⊤ ((M.sys Δ φ f abelian₂).comb u) = Δ.lift (φ (f.b.equivFun.symm u)) := by
  refine (LinSys.ofSec_comb (M.sys Δ φ f abelian₂).toLinSys ⊤ u).trans ?_
  rw [f.b.equivFun_symm_apply, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, map_smul]; exact congrArg _ (ofSec_toSec _)

theorem isAlgebraicData [IsReduced Y] (hU : Dense (U : Set Y)) (hc : GeometricallyConnected M.str) (hD : 1 ≤ D)
    (abelian₂ : ℝ) : (M.sys Δ φ f abelian₂).IsAlgebraicData := by
  refine ⟨⟨M.smooth, M.proj, hc, hD⟩, fun u hu => ?_, f.isFrame.full, Δ.iSup_nonzeroLocus ?_⟩
  · have := M.ofSec_comb Δ φ f abelian₂ u
    rw [hu, map_zero] at this
    exact f.b.equivFun.symm.map_eq_zero_iff.1 (φ.map_eq_zero_iff.1
      (M.lift_injective Δ hU (this.symm.trans (map_zero _).symm)))
  · exact (f.b.map φ).span_eq

theorem bd_ne_top (hc : GeometricallyConnected M.str) : M.bd ≠ ⊤ := fun e => by
  have : ConnectedSpace M.X := GeometricallyConnected.connectedSpace_of_subsingleton M.str
  obtain ⟨z, hz⟩ := M.dense.nonempty
  exact (e.ge (Set.mem_univ z)) hz

end Modif

end Moving

section Resol

variable {Y : Scheme.{0}} {p : Y ⟶ Sp F} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y}

structure Resol (C : Common B) (U : Y.Opens) (D : ℕ) {a₁ a₂ : Λ} (W₁ : Submodule F (H0 p (B a₁) ⊤))
    (W₂ : Submodule F (H0 p (B a₂) ⊤)) extends Modif p U D where

  Δ₁ : Cartier ((baseIdeal (C.isLB a₁) W₁).comap σ)

  Δ₂ : Cartier ((baseIdeal (C.isLB a₂) W₂).comap σ)

namespace Resol

variable {C : Common B} {U : Y.Opens} {D : ℕ} {a₁ a₂ : Λ} {W₁ : Submodule F (H0 p (B a₁) ⊤)}
  {W₂ : Submodule F (H0 p (B a₂) ⊤)} (R : Resol C U D W₁ W₂)

abbrev pb (a : Λ) : LB R.X := (B a).pull R.σ

abbrev com : Common R.pb := C.pull R.σ

abbrev L : LB R.X := R.Δ₁.moving

abbrev L₂ : LB R.X := R.Δ₂.moving

abbrev A : LB R.X := R.pb (a₂ + D • a₁)

def e : (LB.div R.A (tw R.L₂ R.L D)).Sec :=
  toSec ((R.com.effChart R.Δ₁.isLB R.Δ₂.isLB rfl).mul (H0.ofSec R.str ⊤ R.Δ₂.t) (H0.ofSec R.str ⊤ (R.Δ₁.pow D)))

theorem ger_e (t : R.Δ₂.P.ι × C.J × R.Δ₁.P.ι) (z : R.X) (h₂ : z ∈ R.Δ₂.P.U t.1) (h₁ : z ∈ R.Δ₁.P.U t.2.2) (h) :
    ger z h (R.e.f ((R.com.effChart R.Δ₁.isLB R.Δ₂.isLB rfl).c t)) =
      ger z h₂ (R.Δ₂.t.f t.1) * ger z h₁ (R.Δ₁.t.f t.2.2) ^ D :=
  (ger_toSec _ _ _ _).trans <| ((R.com.effChart R.Δ₁.isLB R.Δ₂.isLB rfl).germ_mul _ _ t z _ h₂ (mem_zpow_U.2 h₁) h).trans
    (congrArg₂ (· * ·) (germ_ofSec _ _ _ _ _) (R.Δ₁.germ_pow _ D _ z _ h₁ _))

theorem off_le_nonzeroLocus_e (h₁ : NoBase (C.isLB a₁) W₁ U) (h₂ : NoBase (C.isLB a₂) W₂ U) :
    R.off ≤ nonzeroLocus R.e := fun z hz => by
  obtain ⟨t, ha, hb, hc⟩ := (R.com.effChart (n := D) R.Δ₁.isLB R.Δ₂.isLB (rfl : a₂ + D • a₁ = _)).cover z
  refine (isUnit_ger_iff _ hc).1 ?_
  rw [R.ger_e t z ha (mem_zpow_U.1 hb)]
  exact ((isUnit_ger_iff _ _).2 ((R.Δ₂.mem_nonzeroLocus z).2 (R.notMem_support h₂ z hz))).mul
    (((isUnit_ger_iff _ _).2 ((R.Δ₁.mem_nonzeroLocus z).2 (R.notMem_support h₁ z hz))).pow D)

abbrev adj (j : ℕ) : LB R.X := tw (tens R.K.bundle R.A) R.L j

def mulPole (j : ℕ) (O : R.X.Opens) :
    H0 R.str (R.adj j) O →ₗ[F] H0 R.str (tens R.K.bundle (R.pb (a₂ + D • a₁ + j • a₁))) O :=
  (R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).mul (H0.ofSec R.str O (R.Δ₁.pow j))

variable {κ : Λ} (ω : H0 R.str (LB.div R.K.bundle (R.pb κ)) R.off)

def mulCan {b s : Λ} (h : κ + b = s) : H0 R.str (R.pb s) R.off →ₗ[F] H0 R.str (tens R.K.bundle (R.pb b)) R.off :=
  (R.com.canChart R.K.isLB h).mul ω

def adjEquiv (hω : NowhereZero ω) (h₁ : NoBase (C.isLB a₁) W₁ U) (j : ℕ) {s : Λ} (h : κ + (a₂ + D • a₁ + j • a₁) = s) :
    H0 R.str (R.pb s) R.off ≃ₗ[F] H0 R.str (R.adj j) R.off :=
  ((R.com.canChart R.K.isLB h).mulEquiv hω).trans ((R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).mulEquiv
    (R.Δ₁.nowhereZero_pow R.str (R.notMem_support h₁) j)).symm

theorem mulPole_adjEquiv (hω : NowhereZero ω) (h₁ : NoBase (C.isLB a₁) W₁ U) (j : ℕ) {s : Λ}
    (h : κ + (a₂ + D • a₁ + j • a₁) = s) (m : H0 R.str (R.pb s) R.off) :
    R.mulPole j R.off (R.adjEquiv ω hω h₁ j h m) = R.mulCan ω h m :=
  ((R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).mulEquiv
    (R.Δ₁.nowhereZero_pow R.str (R.notMem_support h₁) j)).apply_symm_apply _

abbrev adjIdx (j : ℕ) (t : R.K.bundle.ι × C.J × R.Δ₁.P.ι) : (R.adj j).ι :=
  twIdx (M := tens R.K.bundle R.A) (L := R.L) j (t.1, R.com.idx _ t.2.1) (R.com.idx a₁ t.2.1, t.2.2)

theorem germ_adjEquiv (hω : NowhereZero ω) (h₁ : NoBase (C.isLB a₁) W₁ U) (j : ℕ) {s : Λ}
    (h : κ + (a₂ + D • a₁ + j • a₁) = s) (m : H0 R.str (R.pb s) R.off) (t : R.K.bundle.ι × C.J × R.Δ₁.P.ι) (z : R.X)
    (hz : z ∈ R.off) (hP : z ∈ R.Δ₁.P.U t.2.2) (ha : z ∈ (R.adj j).U (R.adjIdx j t))
    (hω' : z ∈ (LB.div R.K.bundle (R.pb κ)).U (t.1, R.com.idx κ t.2.1)) (hs : z ∈ (R.pb s).U (R.com.idx s t.2.1)) :
    ger z hP (R.Δ₁.t.f t.2.2) ^ j * germ (R.adjIdx j t) z hz ha (R.adjEquiv ω hω h₁ j h m) =
      germ (B := LB.div R.K.bundle (R.pb κ)) (t.1, R.com.idx κ t.2.1) z hz hω' ω * germ (R.com.idx s t.2.1) z hz hs m := by
  have hc : z ∈ (tens R.K.bundle (R.pb (a₂ + D • a₁ + j • a₁))).U (t.1, R.com.idx _ t.2.1) :=
    ⟨hω'.1, (R.com.mem _ _ _).2 ((R.com.mem _ _ _).1 hs)⟩
  rw [← R.Δ₁.germ_pow R.str j _ z hz hP (mem_zpow_U.2 hP)]
  exact ((R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).germ_mul _ _ t z hz _ ha hc).symm.trans
    ((congrArg _ (R.mulPole_adjEquiv ω hω h₁ j h m)).trans
      ((R.com.canChart R.K.isLB h).germ_mul _ _ (t.1, t.2.1) z hz hω' hs hc))

theorem adjEquiv_mul (hω : NowhereZero ω) (h₁ : NoBase (C.isLB a₁) W₁ U) (j : ℕ) {s s' : Λ}
    (h : κ + (a₂ + D • a₁ + j • a₁) = s) (h' : κ + (a₂ + D • a₁ + (j + 1) • a₁) = s') (hs : a₁ + s = s') (w : W₁)
    (m : H0 R.str (R.pb s) R.off) :
    R.adjEquiv ω hω h₁ (j + 1) h' ((R.com.addChart hs).mul (restr le_top (H0.pull R.σ le_top w.1)) m) =
      (oneChart (isLB_tens R.K.isLB (R.com.isLB _)) R.Δ₁.isLB_moving (Nat.cast_succ j).symm).mul
        (restr le_top (R.Δ₁.lift w)) (R.adjEquiv ω hω h₁ j h m) := ext_germ fun z hz => by
  obtain ⟨i, hi⟩ := exists_chart R.K.isLB z
  obtain ⟨k, hk⟩ := R.com.cover z
  obtain ⟨n, hn⟩ := exists_chart R.Δ₁.isLB z
  have hk' (a : Λ) : z ∈ (R.pb a).U (R.com.idx a k) := (R.com.mem a k z).2 hk
  have ha (j : ℕ) : z ∈ (R.adj j).U (R.adjIdx j (i, k, n)) := mem_tw_U.2 ⟨⟨hi, hk' _⟩, hk' _, hn⟩
  refine ⟨R.adjIdx (j + 1) (i, k, n), ha _,
    (mul_cancel_left_mem_nonZeroDivisors (pow_mem (R.Δ₁.reg n z hn) (j + 1))).1 ?_⟩
  have e₁ := R.germ_adjEquiv ω hω h₁ (j + 1) h' ((R.com.addChart hs).mul (restr le_top (H0.pull R.σ le_top w.1)) m)
    (i, k, n) z hz hn (ha _) ⟨hi, hk' _⟩ (hk' _)
  have e₂ := R.germ_adjEquiv ω hω h₁ j h m (i, k, n) z hz hn (ha _) ⟨hi, hk' _⟩ (hk' _)
  have e₃ := (R.com.addChart hs).germ_mul (restr le_top (H0.pull R.σ le_top w.1)) m k z hz (hk' _) (hk' _) (hk' _)
  have e₄ := (oneChart (isLB_tens R.K.isLB (R.com.isLB (a₂ + D • a₁))) R.Δ₁.isLB_moving (Nat.cast_succ j).symm).germ_mul
    (restr le_top (R.Δ₁.lift w)) (R.adjEquiv ω hω h₁ j h m) ((i, R.com.idx _ k), (R.com.idx a₁ k, n)) z hz
    ⟨hk' _, hn⟩ (ha j) (ha (j + 1))
  have e₅ := R.Δ₁.germ_lift w (R.com.idx a₁ k, n) z ⟨hk' _, hn⟩
  replace e₃ := e₃.trans (congrArg (· * _) (germ_restr _ _ _ _ _ _))
  replace e₄ := e₄.trans (congrArg (· * _) (germ_restr _ _ _ _ _ _))
  refine e₁.trans (Eq.trans ?_ (congrArg (_ * ·) e₄).symm)
  refine (congrArg (_ * ·) (e₃.trans (congrArg (· * _) e₅.symm))).trans ?_
  refine (mul_left_comm _ _ _).trans ((congrArg (_ * ·) e₂.symm).trans ?_)
  rw [pow_succ']
  exact mul_mul_mul_comm _ _ _ _

variable {V₁ V₂ : Type} [AddCommGroup V₁] [Module F V₁] [Module (𝓞 F) V₁] [AddCommGroup V₂] [Module F V₂]
  [Module (𝓞 F) V₂] {N₁ : (F →+* ℂ) → V₁ → ℝ} {M₁ : Submodule (𝓞 F) V₁} {N₂ : (F →+* ℂ) → V₂ → ℝ}
  {M₂ : Submodule (𝓞 F) V₂}

def geo [IsReduced Y] (hU : Dense (U : Set Y)) (hc : GeometricallyConnected R.str) (hD : 1 ≤ D)
    (h₁ : NoBase (C.isLB a₁) W₁ U) (h₂ : NoBase (C.isLB a₂) W₂ U) (φ₁ : V₁ ≃ₗ[F] W₁) (φ₂ : V₂ ≃ₗ[F] W₂)
    (f₁ : LatFrame N₁ M₁) (f₂ : LatFrame N₂ M₂) (th : R.L.Sec) (abelian₂ : ℝ) : Geo F where
  toHermSys := R.sys R.Δ₁ φ₁ f₁ abelian₂
  bd := R.bd
  j₀ := 1
  th := secToPow th 1
  geom := ⟨R.isAlgebraicData _ _ _ hU hc hD _, R.bd_ne_top hc⟩
  herm := f₁.isFrame.herm
  conj := f₁.isFrame.conj
  K := R.K
  L₂ := R.L₂
  isLB₂ := R.Δ₂.isLB_moving
  N₂ := f₂.N
  b₂ := R.basisSec R.Δ₂ φ₂ f₂
  n₂ := f₂.n
  w₂ := f₂.w
  A₂ := f₂.A
  alg₂ := R.isAlgebraicData _ _ _ hU hc hD abelian₂
  herm₂ := f₂.isFrame.herm
  conj₂ := f₂.isFrame.conj
  LA := R.A
  isLBA := R.com.isLB _
  e := R.e
  U_le := R.off_le_nonzeroLocus_e h₁ h₂

end Resol

end Resol

section Lattices

structure Consts where

  abelian₂ : ℝ

  beta : ℝ

  LamD : ℝ

  LamT : ℝ

  J : ℝ

  one_le_beta : 1 ≤ beta

  one_le_LamD : 1 ≤ LamD

  one_le_LamT : 1 ≤ LamT

variable {S X : Type} [AddCommGroup S] [Module F S] [Module (𝓞 F) S] [IsScalarTower (𝓞 F) F S] [AddCommGroup X]
  [Module F X] [Module (𝓞 F) X] [IsScalarTower (𝓞 F) F X] (ψ : S →ₗ[F] X) (hψ : Function.Injective ψ) (q : Prop)

open Classical in

def rangeIf : Submodule F X := if q then LinearMap.range ψ else ⊥

omit [NumberField F] [Module (𝓞 F) S] [IsScalarTower (𝓞 F) F S] [Module (𝓞 F) X] [IsScalarTower (𝓞 F) F X] in

theorem rangeIf_le : rangeIf ψ q ≤ LinearMap.range ψ := by
  unfold rangeIf
  split_ifs
  exacts [le_rfl, bot_le]

def invIf : rangeIf ψ q →ₗ[F] S :=
  (LinearEquiv.ofInjective ψ hψ).symm.toLinearMap ∘ₗ Submodule.inclusion (rangeIf_le ψ q)

omit [NumberField F] [Module (𝓞 F) S] [IsScalarTower (𝓞 F) F S] [Module (𝓞 F) X] [IsScalarTower (𝓞 F) F X] in

theorem apply_invIf (x : rangeIf ψ q) : ψ (invIf ψ hψ q x) = x :=
  congrArg Subtype.val ((LinearEquiv.ofInjective ψ hψ).apply_symm_apply ⟨x, rangeIf_le ψ q x.2⟩)

omit [NumberField F] [Module (𝓞 F) S] [IsScalarTower (𝓞 F) F S] [Module (𝓞 F) X] [IsScalarTower (𝓞 F) F X] in

theorem invIf_injective : Function.Injective (invIf ψ hψ q) := fun x y e =>
  Subtype.ext (by rw [← apply_invIf ψ hψ, e, apply_invIf])

def equivIf (hq : q) : rangeIf ψ q ≃ₗ[F] S :=
  LinearEquiv.ofBijective (invIf ψ hψ q) ⟨invIf_injective ψ hψ q, fun s =>
    ⟨⟨ψ s, by rw [rangeIf, if_pos hq]; exact ⟨s, rfl⟩⟩, hψ (apply_invIf _ _ _ _)⟩⟩

variable {Nm : (F →+* ℂ) → S → ℝ} (M : Submodule (𝓞 F) S)

def latIf : Submodule (𝓞 F) (rangeIf ψ q) := M.comap ((invIf ψ hψ q).restrictScalars (𝓞 F))

variable {q M} (h : q → Nonempty (LatFrame Nm M))
include h

theorem isFull_latIf : IsFull (latIf ψ hψ q M) := by
  by_cases hq : q
  · obtain ⟨f⟩ := h hq
    let e := equivIf ψ hψ q hq
    have : latIf ψ hψ q M = M.map (e.symm.toLinearMap.restrictScalars (𝓞 F)) := Submodule.ext fun x =>
      ⟨fun hx => ⟨e x, hx, e.symm_apply_apply x⟩, fun ⟨s, hs, ex⟩ => ex ▸ ((e.apply_symm_apply s).symm ▸ hs : e (e.symm s) ∈ M)⟩
    rw [this]
    refine ⟨f.isFull.fg.map _, ?_⟩
    refine (Submodule.span_image e.symm.toLinearMap).trans ?_
    rw [f.isFull.span, Submodule.map_top, LinearEquiv.range]
  · have : Subsingleton (rangeIf ψ q) := by rw [rangeIf, if_neg hq]; infer_instance
    exact ⟨by rw [Subsingleton.elim (latIf ψ hψ q M) ⊥]; exact Submodule.fg_bot, Subsingleton.elim _ _⟩

theorem exists_famIf : ∃ g : HermFam F (rangeIf ψ q), g.IsConjInv ∧ (q → ∀ σ x, g.nrm σ x = Nm σ (invIf ψ hψ q x)) := by
  by_cases hq : q
  · obtain ⟨f⟩ := h hq
    exact ⟨HermTools.comap f.fam _ (invIf_injective ψ hψ q), isConjInv_comap f.isConjInv_fam _ _,
      fun _ σ x => f.nrm_fam σ _⟩
  · have := (isFull_latIf ψ hψ h).finiteDimensional
    exact ⟨ofBasis (Module.finBasis F _), isConjInv_ofBasis _, fun h => absurd h hq⟩

end Lattices

section Data

variable (G : Geo F) (T : ℕ) (hT : G.D + 1 ≤ T) {S : ℕ → Type} [∀ j, AddCommGroup (S j)] [∀ j, Module F (S j)]
  [∀ j, Module (𝓞 F) (S j)] [∀ j, IsScalarTower (𝓞 F) F (S j)] (ψ : ∀ j, S j →ₗ[F] G.Sec j)
  (hψ : ∀ j, Function.Injective (ψ j)) {Nm : ∀ j, (F →+* ℂ) → S j → ℝ} {M : ∀ j, Submodule (𝓞 F) (S j)}
  (hM : ∀ j, j ≤ T → Nonempty (LatFrame (Nm j) (M j))) (hle : ∀ j ≤ T, G.global j ≤ LinearMap.range (ψ j))
  (h0 : LinearMap.range (ψ 0) ≤ G.global 0) (k : Consts)

def dataOf : Data F where
  toGeo := G
  T := T
  le_T := hT
  V j := rangeIf (ψ j) (j ≤ T)
  global_le j hj := by rw [rangeIf, if_pos hj]; exact hle j hj
  V_zero := by rw [rangeIf, if_pos T.zero_le]; exact le_antisymm h0 (hle 0 T.zero_le)
  M j := latIf (ψ j) (hψ j) _ (M j)
  full j := isFull_latIf _ _ (hM j)
  nm j := (exists_famIf _ (hψ j) (hM j)).choose
  conjInv j := (exists_famIf _ (hψ j) (hM j)).choose_spec.1
  beta := k.beta
  LamD := k.LamD
  LamT := k.LamT
  J := k.J
  one_le_beta := k.one_le_beta
  one_le_LamD := k.one_le_LamD
  one_le_LamT := k.one_le_LamT

def dataEquiv {j : ℕ} (hj : j ≤ T) : S j ≃ₗ[F] (dataOf G T hT ψ hψ hM hle h0 k).V j := (equivIf (ψ j) (hψ j) _ hj).symm

theorem coe_dataEquiv {j : ℕ} (hj : j ≤ T) (s : S j) : (dataEquiv G T hT ψ hψ hM hle h0 k hj s).1 = ψ j s :=
  (apply_invIf _ (hψ j) _ _).symm.trans (congrArg _ ((equivIf (ψ j) (hψ j) _ hj).apply_symm_apply s))

theorem dataEquiv_mem {j : ℕ} (hj : j ≤ T) (s : S j) :
    dataEquiv G T hT ψ hψ hM hle h0 k hj s ∈ (dataOf G T hT ψ hψ hM hle h0 k).M j ↔ s ∈ M j :=
  Iff.of_eq (congrArg (· ∈ M j) ((equivIf (ψ j) (hψ j) _ hj).apply_symm_apply s))

theorem nrm_dataEquiv {j : ℕ} (hj : j ≤ T) (σ : F →+* ℂ) (s : S j) :
    ((dataOf G T hT ψ hψ hM hle h0 k).nm j).nrm σ (dataEquiv G T hT ψ hψ hM hle h0 k hj s) = Nm j σ s :=
  ((exists_famIf _ (hψ j) (hM j)).choose_spec.2 hj σ _).trans
    (congrArg _ ((equivIf (ψ j) (hψ j) _ hj).apply_symm_apply s))

end Data

theorem exists_resol_projSpace (F : Type) [Field F] [NumberField F] {M : ℕ} (hM : 1 ≤ M) :
    ∃ (W₁ : Submodule F (H0 (PSpace.str F M) (lbZPow (ProjSpace.O1 F M) 1) ⊤))
      (W₂ : Submodule F (H0 (PSpace.str F M) (lbZPow (ProjSpace.O1 F M) 2) ⊤))
      (R : Resol (Common.powers (ProjSpace.O1_isLB F M)) (ProjSpace.chart F M (Fin.last M)) M W₁ W₂),
      nonzeroLocus R.Δ₁.t = R.opn ∧ nonzeroLocus R.Δ₂.t = R.opn ∧ R.opn ≠ ⊥ := by
  have hv := projSys.isVariety F M hM
  have : IsIntegral (PSpace F M) := hv.isIntegral
  have hg := projSys.gen_mem F M (Fin.last M)
  have e (n : ℕ) (hn : 1 ≤ n) := (nonzeroLocus_secToPow (ProjSpace.coord F M (Fin.last M)) hn).trans
    (ProjSpace.nonzeroLocus_coord F M (Fin.last M))
  let Δ (n : ℕ) (hn : 1 ≤ n) := Cartier.ofSec (Twist.isLB_lbZPow (ProjSpace.O1_isLB F M) n)
    (secToPow (ProjSpace.coord F M (Fin.last M)) n) ((e n hn).ge hg)
  exact ⟨_, _, ⟨Modif.refl hv.smooth hv.proj ((ProjSpace.chart F M _).isOpen.dense ⟨_, hg⟩),
    { Δ 1 le_rfl with cut := (baseIdeal_span _ _).symm.trans (Scheme.IdealSheafData.comap_id _).symm },
    { Δ 2 one_le_two with cut := (baseIdeal_span _ _).symm.trans (Scheme.IdealSheafData.comap_id _).symm }⟩,
    e 1 le_rfl, e 2 one_le_two, fun h => h.le hg⟩

example : ∃ f : LatFrame (fun (σ : F →+* ℂ) (x : Fin 2 → F) => frameNorm 1 fun j => σ (x j))
    (Submodule.span (𝓞 F) (Set.range (Pi.basisFun F (Fin 2)))), f.N = 2 :=
  ⟨⟨2, 2, Pi.basisFun F _, 1, fun _ => 1, congrArg (fun v => Submodule.span _ (Set.range v))
    (funext fun k => by simp [Matrix.one_apply]), (Proj.isAlgebraicData F 1 le_rfl).spans,
    by simp, fun σ x => by simp [frameNorm], fun _ _ => rfl⟩, rfl⟩

end GlobalTheory.CompHS

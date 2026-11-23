import Mathlib
import Formalism.LocalRingCardinality.DataForms
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.PolyFn
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

noncomputable section

namespace GlobalTheory.GO

open NumberField Formalism.L2.Col Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms

@[reducible] def cplGSD {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (Y : Cpl S) : GSD K where
  G := S.G
  D := Y.Pts
  V := S.V
  ιV := S.ιV
  bV := S.bV
  pair := S.pair
  ρ := S.ρ
  Nab d := S.Nab d.1.1
  Del d := S.Del d.1.1

section Jet

open MvPolynomial Formalism.L2.Ker

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

omit [Fintype ι] in

theorem jetLin_monomial (J : (DVar ι a b →₀ ℕ) → K) (μ : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (c : K) :
    jetLin J (monomial μ c) = monomial (μ.comapDomain Sum.inl Sum.inl_injective.injOn)
      (c * J (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have h : (monomial μ c : MvPolynomial _ K) = c • basisMonomials _ K μ := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, jetLin, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

theorem jetMap_sum {α : Type} (s : Finset α) (r : α → K) (J : α → (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) :
    jetMap (∑ x ∈ s, r x • J x) n = ∑ x ∈ s, r x • jetMap (J x) n := by
  have h : jetLin (∑ x ∈ s, r x • J x) = ∑ x ∈ s, r x • jetLin (J x) := by
    refine (basisMonomials _ K).ext fun μ => ?_
    simp only [coe_basisMonomials, LinearMap.sum_apply, LinearMap.smul_apply, jetLin_monomial, one_mul, Finset.sum_apply, Pi.smul_apply,
      map_sum, smul_monomial]
  refine LinearMap.ext fun P => ?_
  simp only [jetMap, h, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply]

omit [Fintype ι] in

theorem map_subD {L : Type} [Field L] (s : K →+* L) (P : Formalism.L2.DIV.Pol K ι a) :
    MvPolynomial.map s (subD K ι a b P) = subD L ι a b (MvPolynomial.map s P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [subD]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [subD, aeval_X]
    split_ifs <;> simp

theorem map_jetMap {L : Type} [Field L] (s : K →+* L) (J : (DVar ι a b →₀ ℕ) → K) (J' : (DVar ι a b →₀ ℕ) → L) (r : L) (n : ι → ℕ)
    (P : Formalism.L2.DIV.Pol K ι a)
    (h : ∀ μ ∈ (subD K ι a b (P * ∏ τ, frDet K a τ ^ n τ)).support,
      s (J (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) = r * J' (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) :
    MvPolynomial.map s (jetMap J n P) = r • jetMap J' 0 (MvPolynomial.map s (P * ∏ τ, frDet K a τ ^ n τ)) := by
  have e0 : ∀ Q : Formalism.L2.DIV.Pol L ι a, jetMap J' 0 Q = jetLin J' (subD L ι a b Q) := fun Q => by simp [jetMap]
  have e1 : jetMap J n P = jetLin J (subD K ι a b (P * ∏ τ, frDet K a τ ^ n τ)) := rfl
  rw [e0, e1, ← map_subD]
  generalize subD K ι a b (P * ∏ τ, frDet K a τ ^ n τ) = Q at h
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  simp only [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [jetLin_monomial, map_monomial, map_monomial, jetLin_monomial, smul_monomial, map_mul, h μ hμ, smul_eq_mul, mul_left_comm]

def derPol (cD : ι → K) (Q : Formalism.L2.DIV.Pol K ι a) (y' : ι → Matrix (Fin b) (Fin b) K) : MvPolynomial (DVar ι a b) K :=
  aeval (fun k : ι × Fin a × Fin a => ∑ β : Fin b,
    C (cD k.1 * (if h : (k.2.2 : ℕ) < b then y' k.1 β ⟨k.2.2, h⟩ else 0)) * X ((k.1, β, k.2.1) : DVar ι a b)) Q

theorem eval_jetMap (cD : ι → K) (T : (DVar ι a b →₀ ℕ) → K) (Q : Formalism.L2.DIV.Pol K ι a) (y' : ι → Matrix (Fin b) (Fin b) K) :
    eval (fun v : ι × Fin b × Fin b => y' v.1 v.2.1 v.2.2) (jetMap (fun q => (q.prod fun k n => cD k.1 ^ n) * T q) 0 Q) =
      ∑ q ∈ (derPol cD Q y').support, coeff q (derPol cD Q y') * T q := by
  let φ : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K →ₐ[K] MvPolynomial (DVar ι a b) K :=
    aeval (Sum.elim (fun v => C (y' v.1 v.2.1 v.2.2)) fun k => C (cD k.1) * X k)
  let l : MvPolynomial (DVar ι a b) K →ₗ[K] K := (basisMonomials _ K).constr K T
  have hl : ∀ q c, l (monomial q c) = c * T q := fun q c => by
    have h : (monomial q c : MvPolynomial _ K) = c • basisMonomials _ K q := by
      rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
    rw [h, map_smul, Module.Basis.constr_basis, smul_eq_mul]
  have h1 : φ (subD K ι a b Q) = derPol cD Q y' := by
    rw [← AlgHom.comp_apply]
    refine AlgHom.congr_fun (MvPolynomial.algHom_ext fun v => ?_) Q
    simp only [subD, φ, AlgHom.comp_apply, aeval_X]
    split_ifs
    · simp only [map_sum, map_mul, aeval_X, Sum.elim_inl, Sum.elim_inr]
      exact Finset.sum_congr rfl fun β _ => by ring
    · simp
  have h2 : ∀ S, eval (fun v : ι × Fin b × Fin b => y' v.1 v.2.1 v.2.2) (jetLin (fun q => (q.prod fun k n => cD k.1 ^ n) * T q) S) =
      l (φ S) := fun S => by
    induction S using MvPolynomial.induction_on' with
    | add p q hp hq => simp only [map_add, hp, hq]
    | monomial μ c =>
      have e : φ (monomial μ c) = monomial (μ.comapDomain Sum.inr Sum.inr_injective.injOn)
          (c * ((μ.comapDomain Sum.inl Sum.inl_injective.injOn).prod fun v n => y' v.1 v.2.1 v.2.2 ^ n) *
            (μ.comapDomain Sum.inr Sum.inr_injective.injOn).prod fun k n => cD k.1 ^ n) := by
        rw [aeval_monomial, monomial_eq, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp),
          Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, Finsupp.comapDomain_apply, map_mul, map_prod, map_pow, mul_pow,
          Finset.prod_mul_distrib, algebraMap_eq]
        ring
      rw [e, hl, jetLin_monomial, eval_monomial]
      ring
  have e0 : jetMap (fun q => (q.prod fun k n => cD k.1 ^ n) * T q) 0 Q =
      jetLin (fun q => (q.prod fun k n => cD k.1 ^ n) * T q) (subD K ι a b Q) := by simp [jetMap]
  rw [e0, h2, h1]
  conv_lhs => rw [(derPol cD Q y').as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun q _ => hl _ _

theorem eval_jetMap_jetC (D : D7) {a b : ℕ} (cD : D.what₂.Tau → ℂ) (G : Formalism.MainNotions.TaylorLogMetric.VC D a b → ℂ)
    (Q : MvPolynomial (Formalism.MainNotions.GL3Theta.FrV D a) ℂ) (y' : D.what₂.Tau → Matrix (Fin b) (Fin b) ℂ) :
    eval (fun v : D.what₂.Tau × Fin b × Fin b => y' v.1 v.2.1 v.2.2) (jetMap (jetC cD G) 0 Q) =
      Formalism.MainNotions.GL3Theta.applyAt0 D (Formalism.MainNotions.GL3Theta.polD D cD Q y') G := by
  refine (eval_jetMap cD (derivAt0 G) Q y').trans (Finset.sum_congr rfl fun q _ => ?_)
  have h0 : (q.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h1 : (Formalism.MainNotions.TaylorLogMetric.coordV D : _ → Formalism.MainNotions.TaylorLogMetric.VC D a b) = coordX := by
    funext k τ i j
    unfold Formalism.MainNotions.TaylorLogMetric.coordV coordX
    congr
  rw [Formalism.MainNotions.TaylorLogMetric.taylor, mul_assoc, mul_div_cancel₀ _ h0, h1]
  rfl

end Jet

structure ChSrc (X : Fields) (R : Ranks) where

  F : ℕ → GFam X.K

  ok : ∀ i, (F i).Ok

  lam : ∀ i, X.Tau → DomWeight (R.N i)

  eV : ∀ i, (F i).V ≃ₗ[X.K] Formalism.L2.DIV.VV X.K (lam i)

  kk : KerFam F

  rho : ∀ i, (F i).Cl → ℂ

  rho' : ∀ i, (F (i + 1)).Cl → ℂ
  rho_norm : ∀ i, i < R.m → ∀ c, ‖rho i c‖ = 1
  rho'_norm : ∀ i, i < R.m → ∀ c, ‖rho' i c‖ = 1

  DG : ℕ
  DG_pos : 0 < DG
  dvd : ∀ i, i ≤ R.m → ∀ c : (F i).Cl,
    Nat.card (MulAction.stabilizer ((F i).G c.1) (((F i).mem c.1).outSec.rep c.2)) ∣ DG

namespace ChSrc

variable {X : Fields} {R : Ranks} (A : ChSrc X R) (σ : X.K →+* ℂ)

abbrev Fr (X : Fields) (σ : X.K →+* ℂ) (n : ℕ) : Type := Frames (gramC (1 : Matrix (Fin n) (Fin n) X.E) (embAt σ X.emb))

def ev (i : ℕ) (x : (A.F i).V) : Fr X σ (R.N i) → ℂ := evV X.emb 1 (A.lam i) σ (A.eV i x)

def ker (i : ℕ) (c : (A.F i).Cl) (c' : (A.F (i + 1)).Cl) : (A.F i).V →ₗ[X.K] (A.F (i + 1)).V :=
  GFam.Mat.atReps (A.kk i) (fun b => ((A.F i).mem b).outSec) (fun b => ((A.F (i + 1)).mem b).outSec) c c'

def kerC (i : ℕ) (c : (A.F i).Cl) (c' : (A.F (i + 1)).Cl) : (Fr X σ (R.N i) → ℂ) →ₗ[ℂ] (Fr X σ (R.N (i + 1)) → ℂ) :=
  Classical.epsilon fun U : (Fr X σ (R.N i) → ℂ) →ₗ[ℂ] (Fr X σ (R.N (i + 1)) → ℂ) =>
    ∀ x, U (A.ev σ i x) = A.ev σ (i + 1) (A.ker i c c' x)

theorem half (R : Ranks) (j : ℕ) : ∃ z : ℤ, (z : ℚ) = (R.N j : ℚ) / 2 := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.t_odd
  refine ⟨(a : ℤ) + j * (b + 1), ?_⟩
  simp only [Ranks.N, ha, hb]
  push_cast
  ring

def zOf (x : ℚ) : ℤ := ⌊x⌋

theorem zOf_spec (R : Ranks) (e : ℚ) (he : ∃ z : ℤ, e = z) (j : ℕ) : ((zOf (e - (R.N j : ℚ) / 2) : ℤ) : ℚ) = e - (R.N j : ℚ) / 2 := by
  obtain ⟨z, rfl⟩ := he
  obtain ⟨y, hy⟩ := half R j
  rw [← hy, ← Int.cast_sub, zOf, Int.floor_intCast]

def sS (hc : X.Tau → HCParam R) (i : ℕ) (τ : X.Tau) : ℤ :=
  if h : i < R.m then zOf (sExp' R ((hc τ).e ⟨i, h⟩) (i + 1)) else 0

def sD (hc : X.Tau → HCParam R) (i : ℕ) (τ : X.Tau) : ℤ :=
  if h : i < R.m then zOf (sExp R ((hc τ).e ⟨i, h⟩) (i + 1)) else 0

def chain (hc : X.Tau → HCParam R) : ColumnChain R X.Tau hc where
  cls i := (A.F i).Cl
  clsFin i := (A.ok i).fintypeCl
  stab i c := MulAction.stabilizer ((A.F i).G c.1) (((A.F i).mem c.1).outSec.rep c.2)
  stabGrp _ _ := inferInstance
  stabFin i c := (A.ok i c.1).fin_stab _
  DGam := A.DG
  DGam_pos := A.DG_pos
  dvd_DGam := A.dvd
  Y i := Fr X σ (R.N i)
  de _ y τ := deFr y τ
  de_ne _ y τ := (isUnit_det_fr y τ).ne_zero
  rhoDet := A.rho
  rhoDet' := A.rho'
  rho_norm := A.rho_norm
  rho'_norm := A.rho'_norm
  unf i c c' := (A.rho i c * A.rho' i c')⁻¹ •
    ((mulFun fun y => ∏ τ, deFr y τ ^ sD hc i τ).comp ((A.kerC σ i c c').comp (mulFun fun y => (∏ τ, deFr y τ ^ sS hc i τ)⁻¹)))
  sSharp := sS hc
  sSharp_eq i h τ := by
    rw [sS, dif_pos h]; exact zOf_spec R _ ((hc τ).e_int _) _
  sDiv := sD hc
  sDiv_eq i h τ := by
    rw [sD, dif_pos h]; exact zOf_spec R _ ((hc τ).e_int _) _

def emb (i : ℕ) (φ : (A.F i).Forms) : (A.F i).Cl → Fr X σ (R.N i) → ℂ :=
  fun c => A.ev σ i ((φ c.1).1 (((A.F i).mem c.1).outSec.rep c.2))

def evS (i : ℕ) : (A.F i).V →ₛₗ[σ] (Fr X σ (R.N i) → ℂ) :=
  (evV X.emb 1 (A.lam i) σ).comp (A.eV i).toLinearMap

theorem evS_apply (i : ℕ) (x : (A.F i).V) : A.evS σ i x = A.ev σ i x := rfl

theorem ev_injective (i : ℕ) : Function.Injective (A.ev σ i) :=
  (evV_injective X.emb 1 (A.lam i) σ (stdFrC _)).comp (A.eV i).injective

theorem ev_sum (i : ℕ) {J : Type} [Fintype J] (a : J → X.K) (v : J → (A.F i).V) :
    A.ev σ i (∑ j, a j • v j) = ∑ j, σ (a j) • A.ev σ i (v j) := by
  simp only [← evS_apply, map_sum, map_smulₛₗ]

theorem emb_injective (i : ℕ) : Function.Injective (A.emb σ i) := fun φ ψ h =>
  ((A.F i).resOf (A.ok i) fun b => ((A.F i).mem b).outSec).injective
    (Subtype.ext (funext fun c => A.ev_injective σ i (congrFun h c)))

theorem exists_ext (i : ℕ) (c : (A.F i).Cl) (c' : (A.F (i + 1)).Cl) :
    ∃ U : (Fr X σ (R.N i) → ℂ) →ₗ[ℂ] (Fr X σ (R.N (i + 1)) → ℂ), ∀ x, U (A.ev σ i x) = A.ev σ (i + 1) (A.ker i c c' x) := by
  have hl : LinearIndependent ℂ fun j => A.ev σ i ((A.F i).bV j) :=
    evV_linearIndependent X.emb 1 (A.lam i) σ (stdFrC _) (fun j => A.eV i ((A.F i).bV j))
      ((A.F i).bV.linearIndependent.map' (A.eV i).toLinearMap (A.eV i).ker)
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective
    (Finsupp.linearCombination ℂ fun j => A.ev σ i ((A.F i).bV j)) (LinearMap.ker_eq_bot.mpr hl)
  refine ⟨(Finsupp.linearCombination ℂ fun j => A.ev σ (i + 1) (A.ker i c c' ((A.F i).bV j))) ∘ₗ L, fun x => ?_⟩
  have hj : ∀ j, L (A.ev σ i ((A.F i).bV j)) = Finsupp.single j 1 := fun j => by
    have := LinearMap.congr_fun hL (Finsupp.single j 1)
    simpa using this
  rw [← (A.F i).bV.sum_repr x, ev_sum]
  simp only [map_sum, map_smul]
  rw [ev_sum]
  simp [hj]

theorem kerC_ev (i : ℕ) (c : (A.F i).Cl) (c' : (A.F (i + 1)).Cl) (x : (A.F i).V) :
    A.kerC σ i c c' (A.ev σ i x) = A.ev σ (i + 1) (A.ker i c c' x) :=
  Classical.epsilon_spec (A.exists_ext σ i c c') x

theorem prod_de_ne_zero {n : ℕ} (y : Fr X σ n) (e : X.Tau → ℤ) : (∏ τ, deFr y τ ^ e τ) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (isUnit_det_fr y τ).ne_zero

theorem Kmap_eq (hc : X.Tau → HCParam R) (i : ℕ) (hi : i < R.m) (c : (A.F i).Cl) (c' : (A.F (i + 1)).Cl) :
    (A.chain σ hc).Kmap i c c' = A.kerC σ i c c' := by
  have h1 : A.rho i c ≠ 0 := fun h => by simpa [h] using A.rho_norm i hi c
  have h2 : A.rho' i c' ≠ 0 := fun h => by simpa [h] using A.rho'_norm i hi c'
  refine LinearMap.ext fun φ => funext fun (y : Fr X σ (R.N (i + 1))) => ?_
  have e : (fun y : Fr X σ (R.N i) => (∏ τ, deFr y τ ^ sS hc i τ)⁻¹ * ((∏ τ, deFr y τ ^ sS hc i τ) * φ y)) = φ :=
    funext fun y => inv_mul_cancel_left₀ (prod_de_ne_zero σ y _) _
  show (A.rho i c * A.rho' i c') * ((∏ τ, deFr y τ ^ sD hc i τ)⁻¹ * ((A.rho i c * A.rho' i c')⁻¹ *
    ((∏ τ, deFr y τ ^ sD hc i τ) * A.kerC σ i c c'
      (fun y : Fr X σ (R.N i) => (∏ τ, deFr y τ ^ sS hc i τ)⁻¹ * ((∏ τ, deFr y τ ^ sS hc i τ) * φ y)) y))) = _
  rw [e]
  have := prod_de_ne_zero σ y (sD hc i)
  field_simp
  rfl

theorem Kmap_ev (hc : X.Tau → HCParam R) (i : ℕ) (hi : i < R.m) (c : (A.F i).Cl) (c' : (A.F (i + 1)).Cl) (x : (A.F i).V) :
    (A.chain σ hc).Kmap i c c' (A.ev σ i x) = A.ev σ (i + 1) (A.ker i c c' x) :=
  (LinearMap.congr_fun (A.Kmap_eq σ hc i hi c c') _).trans (A.kerC_ev σ i c c' x)

theorem unf_sharp_ev (hc : X.Tau → HCParam R) (i : ℕ) (c : (A.F i).Cl) (c' : (A.F (i + 1)).Cl) (x : (A.F i).V)
    (y : Fr X σ (R.N (i + 1))) :
    (A.chain σ hc).unf i c c' ((A.chain σ hc).sharp i (A.ev σ i x)) y =
      (A.rho i c * A.rho' i c')⁻¹ * ((∏ τ, deFr y τ ^ sD hc i τ) * A.ev σ (i + 1) (A.ker i c c' x) y) := by
  have e : (fun y : Fr X σ (R.N i) => (∏ τ, deFr y τ ^ sS hc i τ)⁻¹ * ((∏ τ, deFr y τ ^ sS hc i τ) * A.ev σ i x y)) = A.ev σ i x :=
    funext fun y => inv_mul_cancel_left₀ (prod_de_ne_zero σ y _) _
  show (A.rho i c * A.rho' i c')⁻¹ * ((∏ τ, deFr y τ ^ sD hc i τ) * A.kerC σ i c c'
      (fun y : Fr X σ (R.N i) => (∏ τ, deFr y τ ^ sS hc i τ)⁻¹ * ((∏ τ, deFr y τ ^ sS hc i τ) * A.ev σ i x y)) y) = _
  rw [e, kerC_ev]

theorem K_emb (hc : X.Tau → HCParam R) (i : ℕ) (hi : i < R.m) (φ : (A.F i).Forms) :
    (A.chain σ hc).K i (A.emb σ i φ) = A.emb σ (i + 1) (A.kk.step A.ok i φ) := by
  funext c'
  have hR : A.emb σ (i + 1) (A.kk.step A.ok i φ) c' = A.evS σ (i + 1) (∑ b, @Finset.sum _ _ _ (@Finset.univ _ (A.ok i b).fintypeCl)
      fun c : ((A.F i).mem b).Cl => (((((A.F i).mem b).toCSDOf (A.ok i b) ((A.F i).mem b).outSec).wt c : X.K))⁻¹ •
        A.ker i ⟨b, c⟩ c' ((φ b).1 (((A.F i).mem b).outSec.rep c))) := by
    unfold ChSrc.emb
    rw [evS_apply]
    congr 1
    simp only [KerFam.step, GFam.Mat.opOf, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hL : (A.chain σ hc).K i (A.emb σ i φ) c' =
      @Finset.sum _ _ _ (@Finset.univ _ (A.ok i).fintypeCl) fun c : (A.F i).Cl =>
        (A.chain σ hc).wt i c • (A.chain σ hc).Kmap i c c' (A.emb σ i φ c) := rfl
  letI : ∀ b, Fintype ((A.F i).mem b).Cl := fun b => (A.ok i b).fintypeCl
  rw [hL, hR, map_sum]
  refine (Fintype.sum_sigma _).trans (Finset.sum_congr rfl fun b _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LinearMap.map_smulₛₗ, map_inv₀, map_natCast]
  refine congrArg₂ (fun (a : ℂ) (f : Fr X σ (R.N (i + 1)) → ℂ) => a • f) ?_ (A.Kmap_ev σ hc i hi ⟨b, c⟩ c' _)
  unfold ColumnChain.wt CSD.wt
  exact congrArg (fun n : ℕ => (n : ℂ)⁻¹) (@Nat.card_eq_fintype_card _ ((A.ok i b).fintypeStab _))

theorem chain_emb (hc : X.Tau → HCParam R) (φ : (A.F 0).Forms) (j : ℕ) (hj : j ≤ R.m) :
    Formalism.ThetaLiftIndependence.chainOpM (A.chain σ hc).wt (A.chain σ hc).Kmap j (A.emb σ 0 φ) = A.emb σ j (A.kk.colTo A.ok j φ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have := A.K_emb σ hc j (by omega) (A.kk.colTo A.ok j φ)
    rw [← ih (by omega)] at this
    exact this

theorem col_emb (hc : X.Tau → HCParam R) (φ : (A.F 0).Forms) :
    (A.chain σ hc).col (A.emb σ 0 φ) = A.emb σ R.m (A.kk.colTo A.ok R.m φ) := A.chain_emb σ hc φ R.m le_rfl

def trueWt (hc : X.Tau → HCParam R) (i : ℕ) (τ : X.Tau) : DomWeight (R.N i) :=
  shiftW (Examples₂.lamOf (hc τ) i) (-((i : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ)))

theorem trueWt_eq {Word : Type} (W : Wts X Word R) (u : Word) (i : ℕ) : trueWt (W.hc u) i = W.lamTrue u i := rfl

theorem trueWt_old (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) (τ : X.Tau) (a : Fin (R.N (i + 1))) (h : a.1 < R.N i) :
    (trueWt hc (i + 1) τ).w a = (trueWt hc i τ).w ⟨a.1, h⟩ + sS hc i τ - sD hc i τ := by
  have h0 := Wts.lamTrue_old (⟨fun τ => RowPar.of (hc τ), fun _ => hc, ∅⟩ : Wts X Unit R) () hi τ a h
  have h1 : ((sS hc i τ : ℤ) : ℚ) = sExp' R ((hc τ).e ⟨i, hi⟩) (i + 1) := by
    rw [sS, dif_pos hi]; exact zOf_spec R _ ((hc τ).e_int _) _
  have h2 : ((sD hc i τ : ℤ) : ℚ) = sExp R ((hc τ).e ⟨i, hi⟩) (i + 1) := by
    rw [sD, dif_pos hi]; exact zOf_spec R _ ((hc τ).e_int _) _
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [h1, h2]
  exact h0

theorem trueWt_new (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) (τ : X.Tau) (a : Fin (R.N (i + 1))) (h : ¬ a.1 < R.N i) :
    (trueWt hc (i + 1) τ).w a = -sD hc i τ := by
  have h0 := Wts.lamTrue_new (⟨fun τ => RowPar.of (hc τ), fun _ => hc, ∅⟩ : Wts X Unit R) () hi τ a h
  have h2 : ((sD hc i τ : ℤ) : ℚ) = sExp R ((hc τ).e ⟨i, hi⟩) (i + 1) := by
    rw [sD, dif_pos hi]; exact zOf_spec R _ ((hc τ).e_int _) _
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [h2]
  exact h0

theorem trueWt_add_sS_nonneg (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) (τ : X.Tau) (a : Fin (R.N i)) :
    0 ≤ (trueWt hc i τ).w a + sS hc i τ := by
  have hN : R.N i < R.N (i + 1) := by unfold Ranks.N; rw [add_mul]; omega
  have h1 := trueWt_old hc hi τ ⟨a.1, a.2.trans hN⟩ a.2
  have h2 := trueWt_new hc hi τ ⟨R.N i, hN⟩ (lt_irrefl _)
  have h3 := (trueWt hc (i + 1) τ).anti (show (⟨a.1, a.2.trans hN⟩ : Fin (R.N (i + 1))) ≤ ⟨R.N i, hN⟩ from a.2.le)
  rw [h1, h2] at h3
  simp only [Fin.eta] at h3
  omega

structure Tied (hc : X.Tau → HCParam R) : Prop where

  lam_eq : ∀ i, i ≤ R.m → A.lam i = trueWt hc i

  act : ∀ i, i ≤ R.m → ∀ b : (A.F i).β, ∃ (u : (A.F i).G b →* UF X.E (R.N i)) (χ : (A.F i).G b →* X.Kˣ), ∀ g x,
    A.eV i ((A.F i).ρ b g x) = ((χ g : X.Kˣ) : X.K) • rhoVr X.emb (A.lam i) (ufGL X.E (R.N i) (u g)) (A.eV i x)

variable {A} in

theorem Tied.sharp_ev_poly {hc : X.Tau → HCParam R} (h : A.Tied hc) (i : ℕ) (hi : i < R.m) (x : (A.F i).V) :
    ∃ P : MvPolynomial (X.Tau × Fin (R.N i) × Fin (R.N i)) ℂ, ∀ y : Fr X σ (R.N i),
      (A.chain σ hc).sharp i (A.ev σ i x) y = MvPolynomial.eval (fun v => y.1 v.1 v.2.1 v.2.2) P := by
  have hn : ∀ τ, 0 ≤ sS hc i τ + (A.lam i τ).detShift := fun τ => by
    have := trueWt_add_sS_nonneg hc hi τ ⟨R.N i - 1, by have := R.N_pos i; omega⟩
    rw [h.lam_eq i hi.le, DomWeight.detShift, dif_pos (R.N_pos i)]
    omega
  refine ⟨(∏ τ, (Matrix.of fun a b => (MvPolynomial.X (τ, a, b) : MvPolynomial (X.Tau × Fin (R.N i) × Fin (R.N i)) ℂ)).det ^
    (sS hc i τ + (A.lam i τ).detShift).toNat) * MvPolynomial.map σ (A.eV i x).1, fun y => ?_⟩
  have hd : ∀ τ, MvPolynomial.eval (fun v : X.Tau × Fin (R.N i) × Fin (R.N i) => y.1 v.1 v.2.1 v.2.2)
      (Matrix.of fun a b => (MvPolynomial.X (τ, a, b) : MvPolynomial (X.Tau × Fin (R.N i) × Fin (R.N i)) ℂ)).det = (y.1 τ).det := fun τ => by
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp
  show (∏ τ, (y.1 τ).det ^ sS hc i τ) * evFr _ (shiftOf (A.lam i)) σ (A.eV i x).1 y = _
  rw [evFr_apply, map_mul, map_prod, MvPolynomial.eval_map, ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, hd, ← zpow_natCast, Int.toNat_of_nonneg (hn τ), zpow_add₀ (isUnit_det_fr y τ).ne_zero]
  rfl

variable {A} in

theorem Tied.ev_rho {hc : X.Tau → HCParam R} (h : A.Tied hc) (i : ℕ) (hi : i ≤ R.m) (b : (A.F i).β) :
    ∃ (u : (A.F i).G b →* UF X.E (R.N i)) (χ : (A.F i).G b →* X.Kˣ), ∀ g x (y y' : Fr X σ (R.N i)),
      IsTr (atInf (embAt σ X.emb) (ufGL X.E (R.N i) (u g) : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E)) y' y →
        A.ev σ i ((A.F i).ρ b g x) y = σ (χ g : X.Kˣ) * A.ev σ i x y' := by
  obtain ⟨u, χ, e⟩ := h.act i hi b
  refine ⟨u, χ, fun g x y y' hy => ?_⟩
  unfold ev
  rw [e, map_smulₛₗ, Pi.smul_apply, evV_rhoVr_tr _ _ _ _ _ _ y y' hy, smul_eq_mul]

@[reducible] def exampleGSD (X : Fields) {n : ℕ} (lam : X.Tau → DomWeight n) : GSD X.K where
  G := ℤˣ
  D := Unit
  V := VV X.K lam
  ιV := VVIdx lam
  decιV := Classical.decEq _
  bV := bVV X.K lam
  pair := pairVr X.emb lam 1
  ρ := 1
  Nab _ := nabAtr X.emb lam (stdLat X.E n)
  Del _ := delAtr X.emb lam (stdLat X.E n)

theorem exampleDatum_isAdmissible (X : Fields) {n : ℕ} (lam : X.Tau → DomWeight n) : (exampleGSD X lam).Ok where
  fin_orb := Quotient.finite _
  fin_stab _ := inferInstance
  nab_smul _ _ := (Submodule.map_id _).symm
  del_smul _ _ := (Submodule.map_id _).symm
  inv _ _ _ := rfl

theorem card_stabilizer_units_int (d : Unit) : Nat.card (MulAction.stabilizer ℤˣ d) = 2 := by
  have : MulAction.stabilizer ℤˣ d = ⊤ := by
    ext g; simp only [Subgroup.mem_top, iff_true]; rfl
  rw [this, Subgroup.card_top, Nat.card_eq_fintype_card]
  simp

theorem exists_linearForm_apply_eq_one (X : Fields) {n : ℕ} (lam : X.Tau → DomWeight n) : ∃ f : VV X.K lam →ₗ[X.K] X.K, f (extV X.K lam) = 1 := by
  obtain ⟨f, hf⟩ := not_forall.mp (mt (Module.forall_dual_apply_eq_zero_iff X.K (extV X.K lam)).mp (extV_ne_zero lam))
  exact ⟨(f (extV X.K lam))⁻¹ • f, by simp [inv_mul_cancel₀ hf]⟩

def toyExample (hc : X.Tau → HCParam R) : ChSrc X R where
  F i := (exampleGSD X (trueWt hc i)).toFam
  ok i _ := exampleDatum_isAdmissible X (trueWt hc i)
  lam := trueWt hc
  eV _ := LinearEquiv.refl _ _
  kk i _ _ :=
    { k := fun _ _ => (exists_linearForm_apply_eq_one X (trueWt hc i)).choose.smulRight (extV X.K (trueWt hc (i + 1)))
      equiv := fun _ _ _ _ => rfl }
  rho _ _ := Complex.I
  rho' _ _ := -1
  rho_norm _ _ _ := by simp
  rho'_norm _ _ _ := by simp
  DG := 2
  DG_pos := two_pos
  dvd _ _ _ := (card_stabilizer_units_int _).dvd

theorem exampleChain_compatible (hc : X.Tau → HCParam R) : (toyExample hc).Tied hc where
  lam_eq _ _ := rfl
  act i _ _ := ⟨1, 1, fun g x => by
    rw [MonoidHom.one_apply, MonoidHom.one_apply, map_one, map_one, Units.val_one, one_smul]
    rfl⟩

def exampleExt (hc : X.Tau → HCParam R) (i : ℕ) : ((toyExample hc).F i).Forms := fun _ => ⟨fun _ => extV X.K (trueWt hc i), fun _ _ => rfl⟩

theorem exampleExt_emb_ne_zero (hc : X.Tau → HCParam R) (i : ℕ) : (toyExample hc).emb σ i (exampleExt hc i) ≠ 0 := fun h =>
  evV_extV_ne_zero X.emb 1 (trueWt hc i) σ (stdFrC _) (congrFun h ⟨(), Quotient.mk _ ()⟩)

theorem exampleChain_K_apply (hc : X.Tau → HCParam R) (i : ℕ) (hi : i < R.m) (a : ℂ) :
    ((toyExample hc).chain σ hc).K i (a • (toyExample hc).emb σ i (exampleExt hc i)) = (a / 2) • (toyExample hc).emb σ (i + 1) (exampleExt hc (i + 1)) := by
  funext c'
  have hs : Subsingleton (((toyExample hc).chain σ hc).cls i) := ⟨by
    rintro ⟨⟨⟩, p⟩ ⟨⟨⟩, q⟩
    induction p using Quotient.inductionOn
    induction q using Quotient.inductionOn
    rfl⟩
  let c₀ : ((toyExample hc).F i).Cl := ⟨(), Quotient.mk _ ()⟩
  have hk : (toyExample hc).ker i c₀ c' (extV X.K (trueWt hc i)) = extV X.K (trueWt hc (i + 1)) := by
    show (exists_linearForm_apply_eq_one X (trueWt hc i)).choose (extV X.K (trueWt hc i)) • extV X.K (trueWt hc (i + 1)) = _
    rw [(exists_linearForm_apply_eq_one X (trueWt hc i)).choose_spec, one_smul]
  have hw : ((toyExample hc).chain σ hc).wt i c₀ = 2⁻¹ :=
    (congrArg (fun n : ℕ => (n : ℂ)⁻¹) (card_stabilizer_units_int _)).trans (by norm_num)
  have hK := (toyExample hc).Kmap_ev σ hc i hi c₀ c' (extV X.K (trueWt hc i))
  rw [hk] at hK
  refine (Fintype.sum_subsingleton (fun c : ((toyExample hc).chain σ hc).cls i => ((toyExample hc).chain σ hc).wt i c •
    ((toyExample hc).chain σ hc).Kmap i c c' (a • (toyExample hc).emb σ i (exampleExt hc i) c)) c₀).trans ?_
  have hm := (((toyExample hc).chain σ hc).Kmap i c₀ c').map_smul a ((toyExample hc).ev σ i (extV X.K (trueWt hc i)))
  rw [hK] at hm
  rw [hw]
  refine (congrArg (fun f : Fr X σ (R.N (i + 1)) → ℂ => (2⁻¹ : ℂ) • f) hm).trans ?_
  exact (smul_smul _ _ _).trans (congrArg (fun z : ℂ => z • (toyExample hc).ev σ (i + 1) (extV X.K (trueWt hc (i + 1)))) (by ring))

theorem exampleChain_col_apply (hc : X.Tau → HCParam R) :
    ((toyExample hc).chain σ hc).col ((toyExample hc).emb σ 0 (exampleExt hc 0)) = ((1 / 2 : ℂ) ^ R.m) • (toyExample hc).emb σ R.m (exampleExt hc R.m) := by
  have h : ∀ j, j ≤ R.m → Formalism.ThetaLiftIndependence.chainOpM ((toyExample hc).chain σ hc).wt ((toyExample hc).chain σ hc).Kmap j ((toyExample hc).emb σ 0 (exampleExt hc 0)) =
      ((1 / 2 : ℂ) ^ j) • (toyExample hc).emb σ j (exampleExt hc j) := by
    intro j hj
    induction j with
    | zero => rw [pow_zero, one_smul]; rfl
    | succ j ih =>
      have := exampleChain_K_apply σ hc j (by omega) ((1 / 2 : ℂ) ^ j)
      rw [← ih (by omega), div_eq_mul_one_div, ← pow_succ] at this
      exact this
  exact h R.m le_rfl

theorem exampleChain_col_ne_zero (hc : X.Tau → HCParam R) : ((toyExample hc).chain σ hc).col ((toyExample hc).emb σ 0 (exampleExt hc 0)) ≠ 0 := by
  rw [exampleChain_col_apply]
  exact smul_ne_zero (pow_ne_zero _ (by norm_num)) (exampleExt_emb_ne_zero σ hc R.m)

def exampleCpl (X : Fields) {n : ℕ} (lam : X.Tau → DomWeight n) : Cpl (exampleGSD X lam) where
  Yb := ℤˣ
  ys _ := Set.univ
  fin _ := Set.finite_univ
  equiv _ _ _ := Iff.rfl

example (X : Fields) {n : ℕ} (lam : X.Tau → DomWeight n) (p : (cplGSD (exampleGSD X lam) (exampleCpl X lam)).D) :
    @MulAction.stabilizer _ _ _ (cplGSD (exampleGSD X lam) (exampleCpl X lam)).actD p = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
  exact (mul_eq_right (M := ℤˣ) (a := g) (b := p.1.2)).mp (congrArg (fun q : (exampleCpl X lam).Pts => q.1.2) hg)

example {n : ℕ} {ST SG Q : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 X.E))} (lam : X.Tau → DomWeight n)
    (L : DecoF X.E n ST SG Q → Submodule (𝓞 X.E) (Sp X.E n)) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (g : FrmG Λ Θ)
    (x : VV X.K lam) :
    (frmGSD (roundPk X lam L) Λ Θ).ρ g x =
      ((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) • rhoVr X.emb lam (ufGL X.E n g.1) x := rfl

abbrev UnfFam : Type :=
  ∀ i, (A.F i).Cl → (A.F (i + 1)).Cl → ((Fr X σ (R.N i) → ℂ) →ₗ[ℂ] (Fr X σ (R.N (i + 1)) → ℂ))

def chainWith (hc : X.Tau → HCParam R) (U : A.UnfFam σ) : ColumnChain R X.Tau hc := { A.chain σ hc with unf := U }

def Unfolds (hc : X.Tau → HCParam R) (U : A.UnfFam σ) : Prop :=
  ∀ i, i < R.m → ∀ c c' x (y : Fr X σ (R.N (i + 1))), U i c c' ((A.chain σ hc).sharp i (A.ev σ i x)) y =
    (A.rho i c * A.rho' i c')⁻¹ * ((∏ τ, deFr y τ ^ sD hc i τ) * A.ev σ (i + 1) (A.ker i c c' x) y)

theorem unfolds_chain (hc : X.Tau → HCParam R) : A.Unfolds σ hc (A.chain σ hc).unf := fun i _ c c' x y => A.unf_sharp_ev σ hc i c c' x y

theorem chainWith_self (hc : X.Tau → HCParam R) : A.chainWith σ hc (A.chain σ hc).unf = A.chain σ hc := rfl

theorem chainWith_unf (hc : X.Tau → HCParam R) (U : A.UnfFam σ) : (A.chainWith σ hc U).unf = U := rfl

variable {A σ} in

theorem Unfolds.Kmap_ev {hc : X.Tau → HCParam R} {U : A.UnfFam σ} (h : A.Unfolds σ hc U) (i : ℕ) (hi : i < R.m) (c : (A.F i).Cl)
    (c' : (A.F (i + 1)).Cl) (x : (A.F i).V) :
    (A.chainWith σ hc U).Kmap i c c' (A.ev σ i x) = A.ev σ (i + 1) (A.ker i c c' x) := by
  rw [← A.Kmap_ev σ hc i hi c c' x]
  have e : U i c c' ((A.chain σ hc).sharp i (A.ev σ i x)) = (A.chain σ hc).unf i c c' ((A.chain σ hc).sharp i (A.ev σ i x)) :=
    funext fun y => (h i hi c c' x y).trans (A.unf_sharp_ev σ hc i c c' x y).symm
  exact congrArg (fun f => (A.rho i c * A.rho' i c') • (A.chain σ hc).divDe i f) e

theorem unfolds_iff_Kmap (hc : X.Tau → HCParam R) (U : A.UnfFam σ) : A.Unfolds σ hc U ↔
    ∀ i, i < R.m → ∀ c c' x, (A.chainWith σ hc U).Kmap i c c' (A.ev σ i x) = A.ev σ (i + 1) (A.ker i c c' x) := by
  refine ⟨fun h i hi c c' x => h.Kmap_ev i hi c c' x, fun h i hi c c' x y => ?_⟩
  have h1 : A.rho i c ≠ 0 := fun h => by simpa [h] using A.rho_norm i hi c
  have h2 : A.rho' i c' ≠ 0 := fun h => by simpa [h] using A.rho'_norm i hi c'
  have h3 := prod_de_ne_zero σ y (sD hc i)
  have e : (A.rho i c * A.rho' i c') * ((∏ τ, deFr y τ ^ sD hc i τ)⁻¹ * U i c c' ((A.chain σ hc).sharp i (A.ev σ i x)) y) =
    A.ev σ (i + 1) (A.ker i c c' x) y := congrFun (h i hi c c' x) y
  rw [← e]
  field_simp

variable {A σ} in

theorem Unfolds.K_emb {hc : X.Tau → HCParam R} {U : A.UnfFam σ} (h : A.Unfolds σ hc U) (i : ℕ) (hi : i < R.m) (φ : (A.F i).Forms) :
    (A.chainWith σ hc U).K i (A.emb σ i φ) = A.emb σ (i + 1) (A.kk.step A.ok i φ) := by
  rw [← A.K_emb σ hc i hi φ]
  funext c'
  refine Finset.sum_congr rfl fun c _ => ?_
  exact congrArg (fun f => (A.chain σ hc).wt i c • f) ((h.Kmap_ev i hi c c' _).trans (A.Kmap_ev σ hc i hi c c' _).symm)

variable {A σ} in

theorem Unfolds.chain_emb {hc : X.Tau → HCParam R} {U : A.UnfFam σ} (h : A.Unfolds σ hc U) (φ : (A.F 0).Forms) (j : ℕ) (hj : j ≤ R.m) :
    Formalism.ThetaLiftIndependence.chainOpM (A.chainWith σ hc U).wt (A.chainWith σ hc U).Kmap j (A.emb σ 0 φ) = A.emb σ j (A.kk.colTo A.ok j φ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have := h.K_emb j (by omega) (A.kk.colTo A.ok j φ)
    rw [← ih (by omega)] at this
    exact this

variable {A σ} in

theorem Unfolds.col_emb {hc : X.Tau → HCParam R} {U : A.UnfFam σ} (h : A.Unfolds σ hc U) (φ : (A.F 0).Forms) :
    (A.chainWith σ hc U).col (A.emb σ 0 φ) = A.emb σ R.m (A.kk.colTo A.ok R.m φ) := h.chain_emb φ R.m le_rfl

def polFn (X : Fields) (σ : X.K →+* ℂ) (n : ℕ) : Formalism.L2.DIV.Pol ℂ X.Tau n →ₗ[ℂ] (Fr X σ n → ℂ) := fnOf _ 0 1

theorem polFn_apply {n : ℕ} (Q : Formalism.L2.DIV.Pol ℂ X.Tau n) (y : Fr X σ n) :
    polFn X σ n Q y = MvPolynomial.eval (fun v => y.1 v.1 v.2.1 v.2.2) Q := by
  simp [polFn, fnOf]

theorem polFn_injective (n : ℕ) : Function.Injective (polFn X σ n) := fnOf_injective _ 0 1 (fun _ => by simp) (stdFrC _)

def fnPol (X : Fields) (σ : X.K →+* ℂ) (n : ℕ) : (Fr X σ n → ℂ) →ₗ[ℂ] Formalism.L2.DIV.Pol ℂ X.Tau n := polOf _ 0 (stdFrC _)

theorem fnPol_polFn {n : ℕ} (Q : Formalism.L2.DIV.Pol ℂ X.Tau n) : fnPol X σ n (polFn X σ n Q) = Q := by
  have h := polOf_fnOf (gramC (1 : Matrix (Fin n) (Fin n) X.E) (embAt σ X.emb)) 0 (stdFrC _) Q
  have e : (fun τ => ((stdFrC (n := n) (embAt σ X.emb)).1 τ)⁻¹) = 1 := funext fun τ => by simp [stdFrC]
  rw [e] at h
  exact h

abbrev JetFam : Type :=
  ∀ i, (A.F i).Cl → (A.F (i + 1)).Cl → (Formalism.L2.DIV.Pol ℂ X.Tau (R.N i) →ₗ[ℂ] Formalism.L2.DIV.Pol ℂ X.Tau (R.N (i + 1)))

def unfJet (J : A.JetFam) : A.UnfFam σ := fun i c c' => polFn X σ (R.N (i + 1)) ∘ₗ J i c c' ∘ₗ fnPol X σ (R.N i)

def chainJet (hc : X.Tau → HCParam R) (J : A.JetFam) : ColumnChain R X.Tau hc := A.chainWith σ hc (A.unfJet σ J)

theorem chainJet_unf (hc : X.Tau → HCParam R) (J : A.JetFam) (i : ℕ) (c : (A.F i).Cl) (c' : (A.F (i + 1)).Cl)
    (Q : Formalism.L2.DIV.Pol ℂ X.Tau (R.N i)) (y' : Fr X σ (R.N (i + 1))) :
    (A.chainJet σ hc J).unf i c c' (fun y : Fr X σ (R.N i) => MvPolynomial.eval (fun v => y.1 v.1 v.2.1 v.2.2) Q) y' =
      MvPolynomial.eval (fun v => y'.1 v.1 v.2.1 v.2.2) (J i c c' Q) := by
  have e : (fun y : Fr X σ (R.N i) => MvPolynomial.eval (fun v => y.1 v.1 v.2.1 v.2.2) Q) = polFn X σ _ Q :=
    funext fun y => (polFn_apply σ Q y).symm
  rw [e, ← polFn_apply]
  show polFn X σ _ (J i c c' (fnPol X σ _ (polFn X σ _ Q))) y' = _
  rw [fnPol_polFn]

def nuEnd (hc : X.Tau → HCParam R) (i : ℕ) (τ : X.Tau) : ℕ := ((trueWt hc i τ).detShift + sS hc i τ).toNat

theorem nuEnd_cast (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    (nuEnd hc i τ : ℤ) = (trueWt hc i τ).detShift + sS hc i τ := by
  have := trueWt_add_sS_nonneg hc hi τ ⟨R.N i - 1, by have := R.N_pos i; omega⟩
  rw [nuEnd, Int.toNat_of_nonneg]
  rwa [DomWeight.detShift, dif_pos (R.N_pos i)]

theorem nuEnd_eq {Pr : Primes X} (W : Wts X Pr.Word R) (u : Pr.Word) {i : ℕ} (hi : i < R.m) :
    nuEnd (W.hc u) i = Formalism.L2.Ker.nuLast W u i := by
  funext τ
  have h1 : ((sS (W.hc u) i τ : ℤ) : ℚ) = sExp' R ((W.hc u τ).e ⟨i, hi⟩) (i + 1) := (by
    rw [sS, dif_pos hi]; exact zOf_spec R _ ((W.hc u τ).e_int _) _)
  have h0 := W.nuW_eq_true u hi τ ⟨R.N i - 1, by have := R.N_pos i; omega⟩
  rw [← h1] at h0
  have h2 : (W.nuW u (i + 1) τ).detShift = (W.nuW u (i + 1) τ).w ⟨R.N i - 1, Nat.sub_lt (R.N_pos i) one_pos⟩ := dif_pos (R.N_pos i)
  rw [nuEnd, Formalism.L2.Ker.nuLast, h2, DomWeight.detShift, dif_pos (R.N_pos i), trueWt_eq]
  congr 1
  exact_mod_cast h0.symm

theorem trueWt_detShift_succ (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    (trueWt hc (i + 1) τ).detShift = -sD hc i τ := by
  have hN : R.N i < R.N (i + 1) := by unfold Ranks.N; rw [add_mul]; omega
  rw [DomWeight.detShift, dif_pos (R.N_pos _)]
  exact trueWt_new hc hi τ _ (by simp only; omega)

def sharpPol (hc : X.Tau → HCParam R) (i : ℕ) (x : (A.F i).V) : Formalism.L2.DIV.Pol ℂ X.Tau (R.N i) :=
  MvPolynomial.map σ ((A.eV i x).1 * ∏ τ, Formalism.L2.Ker.frDet X.K (R.N i) τ ^ nuEnd hc i τ)

variable {A} in

theorem Tied.sharp_ev {hc : X.Tau → HCParam R} (h : A.Tied hc) (i : ℕ) (hi : i < R.m) (x : (A.F i).V) :
    (A.chain σ hc).sharp i (A.ev σ i x) = polFn X σ _ (A.sharpPol σ hc i x) := by
  funext (y : Fr X σ (R.N i))
  have hd : ∀ τ, MvPolynomial.eval₂ σ (fun v : X.Tau × Fin (R.N i) × Fin (R.N i) => y.1 v.1 v.2.1 v.2.2)
      (Formalism.L2.Ker.frDet X.K (R.N i) τ) = (y.1 τ).det := fun τ => by
    rw [← MvPolynomial.coe_eval₂Hom, Formalism.L2.Ker.frDet, RingHom.map_det]
    congr 1
    ext a b
    simp
  show (∏ τ, (y.1 τ).det ^ sS hc i τ) * evFr _ (shiftOf (A.lam i)) σ (A.eV i x).1 y = _
  rw [polFn_apply, sharpPol, MvPolynomial.eval_map, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_prod, evFr_apply, ← mul_assoc,
    ← Finset.prod_mul_distrib, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [MvPolynomial.eval₂_pow, hd, ← zpow_natCast, nuEnd_cast hc hi, zpow_add₀ (isUnit_det_fr y τ).ne_zero, ← h.lam_eq i hi.le, mul_comm]
  rfl

variable {A} in

theorem Tied.de_mul_ev {hc : X.Tau → HCParam R} (h : A.Tied hc) (i : ℕ) (hi : i < R.m) (x : (A.F (i + 1)).V) (y : Fr X σ (R.N (i + 1))) :
    (∏ τ, deFr y τ ^ sD hc i τ) * A.ev σ (i + 1) x y = polFn X σ _ (MvPolynomial.map σ (A.eV (i + 1) x).1) y := by
  show (∏ τ, (y.1 τ).det ^ sD hc i τ) * evFr _ (shiftOf (A.lam (i + 1))) σ (A.eV (i + 1) x).1 y = _
  rw [polFn_apply, MvPolynomial.eval_map, evFr_apply, ← mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one, one_mul]
  intro τ _
  have : shiftOf (A.lam (i + 1)) τ = -sD hc i τ := by rw [← trueWt_detShift_succ hc hi, ← h.lam_eq _ hi]; rfl
  rw [this, zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ (isUnit_det_fr y τ).ne_zero)]

def JetTie (hc : X.Tau → HCParam R) (J : A.JetFam) : Prop :=
  ∀ i, i < R.m → ∀ c c' x, MvPolynomial.map σ (A.eV (i + 1) (A.ker i c c' x)).1 =
    (A.rho i c * A.rho' i c') • J i c c' (A.sharpPol σ hc i x)

variable {A} in

theorem Tied.unfolds_iff {hc : X.Tau → HCParam R} (h : A.Tied hc) (J : A.JetFam) :
    A.Unfolds σ hc (A.unfJet σ J) ↔ A.JetTie σ hc J := by
  refine forall_congr' fun i => forall_congr' fun hi => forall_congr' fun c => forall_congr' fun c' => forall_congr' fun x => ?_
  have h1 : A.rho i c ≠ 0 := fun h => by simpa [h] using A.rho_norm i hi c
  have h2 : A.rho' i c' ≠ 0 := fun h => by simpa [h] using A.rho'_norm i hi c'
  have e : A.unfJet σ J i c c' ((A.chain σ hc).sharp i (A.ev σ i x)) = polFn X σ _ (J i c c' (A.sharpPol σ hc i x)) := by
    rw [h.sharp_ev σ i hi]
    show polFn X σ _ (J i c c' (fnPol X σ _ (polFn X σ _ _))) = _
    rw [fnPol_polFn]
  rw [e, ← (polFn_injective σ _).eq_iff, map_smul, funext_iff]
  refine forall_congr' fun y => ?_
  rw [h.de_mul_ev σ i hi, eq_inv_mul_iff_mul_eq₀ (mul_ne_zero h1 h2), eq_comm]
  rfl

variable {A} in

theorem Tied.exists_jetTie {hc : X.Tau → HCParam R} (h : A.Tied hc) : ∃ J : A.JetFam, A.JetTie σ hc J := by
  refine ⟨fun i c c' => fnPol X σ _ ∘ₗ (A.chain σ hc).unf i c c' ∘ₗ polFn X σ _, fun i hi c c' x => ?_⟩
  have h1 : A.rho i c ≠ 0 := fun h => by simpa [h] using A.rho_norm i hi c
  have h2 : A.rho' i c' ≠ 0 := fun h => by simpa [h] using A.rho'_norm i hi c'
  have e : (A.chain σ hc).unf i c c' (polFn X σ _ (A.sharpPol σ hc i x)) =
      (A.rho i c * A.rho' i c')⁻¹ • polFn X σ _ (MvPolynomial.map σ (A.eV (i + 1) (A.ker i c c' x)).1) := by
    rw [← h.sharp_ev σ i hi]
    funext y
    exact (A.unf_sharp_ev σ hc i c c' x y).trans (congrArg _ (h.de_mul_ev σ i hi _ y))
  show _ = _ • fnPol X σ _ ((A.chain σ hc).unf i c c' (polFn X σ _ (A.sharpPol σ hc i x)))
  rw [e, map_smul, fnPol_polFn, smul_inv_smul₀ (mul_ne_zero h1 h2)]

abbrev ThFam : Type := ∀ i, (A.F i).Cl → (A.F (i + 1)).Cl → Formalism.L2.Ker.VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ

def jetTh (cD : X.Tau → ℂ) (Th : A.ThFam) : A.JetFam := fun i c c' => Formalism.L2.Ker.jetMap (Formalism.L2.Ker.jetC cD (Th i c c')) 0

def chainTh (hc : X.Tau → HCParam R) (cD : X.Tau → ℂ) (Th : A.ThFam) : ColumnChain R X.Tau hc := A.chainJet σ hc (A.jetTh cD Th)

theorem chainTh_unf (hc : X.Tau → HCParam R) (cD : X.Tau → ℂ) (Th : A.ThFam) (i : ℕ) (c : (A.F i).Cl) (c' : (A.F (i + 1)).Cl)
    (Q : Formalism.L2.DIV.Pol ℂ X.Tau (R.N i)) (y' : Fr X σ (R.N (i + 1))) :
    (A.chainTh σ hc cD Th).unf i c c' (fun y : Fr X σ (R.N i) => MvPolynomial.eval (fun v => y.1 v.1 v.2.1 v.2.2) Q) y' =
      ∑ q ∈ (derPol cD Q y'.1).support, MvPolynomial.coeff q (derPol cD Q y'.1) * Formalism.L2.Ker.derivAt0 (Th i c c') q :=
  (A.chainJet_unf σ hc _ i c c' Q y').trans (eval_jetMap cD _ Q y'.1)

theorem jetTie_of_tables (hc : X.Tau → HCParam R) (cD : X.Tau → ℂ) (Th : A.ThFam)
    (h : ∀ i, i < R.m → ∀ c c', ∃ T : (Formalism.L2.Ker.DVar X.Tau (R.N i) (R.N (i + 1)) →₀ ℕ) → X.K, ∀ x,
      (A.eV (i + 1) (A.ker i c c' x)).1 = Formalism.L2.Ker.jetMap T (nuEnd hc i) (A.eV i x).1 ∧
      ∀ μ ∈ (Formalism.L2.Ker.subD X.K X.Tau (R.N i) (R.N (i + 1))
          ((A.eV i x).1 * ∏ τ, Formalism.L2.Ker.frDet X.K (R.N i) τ ^ nuEnd hc i τ)).support,
        σ (T (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) =
          A.rho i c * A.rho' i c' * Formalism.L2.Ker.jetC cD (Th i c c') (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) :
    A.JetTie σ hc (A.jetTh cD Th) := by
  intro i hi c c' x
  obtain ⟨T, hT⟩ := h i hi c c'
  rw [(hT x).1]
  exact map_jetMap σ T _ _ _ _ (hT x).2

section Laws

variable {A} {hc : X.Tau → HCParam R} (h : A.Tied hc) {cD : X.Tau → ℂ} {Th : A.ThFam} (hJ : A.JetTie σ hc (A.jetTh cD Th))
include h hJ

theorem Tied.chainTh_Kmap_ev (i : ℕ) (hi : i < R.m) (c : (A.F i).Cl) (c' : (A.F (i + 1)).Cl) (x : (A.F i).V) :
    (A.chainTh σ hc cD Th).Kmap i c c' (A.ev σ i x) = A.ev σ (i + 1) (A.ker i c c' x) :=
  ((h.unfolds_iff σ _).mpr hJ).Kmap_ev i hi c c' x

theorem Tied.chainTh_K_emb (i : ℕ) (hi : i < R.m) (φ : (A.F i).Forms) :
    (A.chainTh σ hc cD Th).K i (A.emb σ i φ) = A.emb σ (i + 1) (A.kk.step A.ok i φ) :=
  ((h.unfolds_iff σ _).mpr hJ).K_emb i hi φ

theorem Tied.chainTh_col_emb (φ : (A.F 0).Forms) :
    (A.chainTh σ hc cD Th).col (A.emb σ 0 φ) = A.emb σ R.m (A.kk.colTo A.ok R.m φ) :=
  ((h.unfolds_iff σ _).mpr hJ).col_emb φ

end Laws

example (hc : X.Tau → HCParam R) (cD : X.Tau → ℂ) (Th : A.ThFam) (i : ℕ) (c : (A.F i).Cl) (c' : (A.F (i + 1)).Cl)
    (y' : Fr X σ (R.N (i + 1))) : (A.chainTh σ hc cD Th).unf i c c' (fun _ => 1) y' = Th i c c' 0 := by
  have h := A.chainTh_unf σ hc cD Th i c c' 1 y'
  simp only [map_one, derPol] at h
  refine h.trans ?_
  rw [MvPolynomial.support_one, Finset.sum_singleton, MvPolynomial.coeff_zero_one, one_mul, Formalism.L2.Ker.derivAt0]
  have h0 : ∀ n, n = 0 → ∀ v, iteratedFDeriv ℂ n (Th i c c') 0 v = Th i c c' 0 := by
    rintro _ rfl v
    exact iteratedFDeriv_zero_apply v
  exact h0 _ (by simp) _

example (hc : X.Tau → HCParam R) : ∃ J : (toyExample hc).JetFam, ((toyExample hc).chainJet σ hc J).col ((toyExample hc).emb σ 0 (exampleExt hc 0)) =
    ((1 / 2 : ℂ) ^ R.m) • (toyExample hc).emb σ R.m (exampleExt hc R.m) := by
  obtain ⟨J, hJ⟩ := (exampleChain_compatible hc).exists_jetTie σ
  exact ⟨J, ((((exampleChain_compatible hc).unfolds_iff σ J).mpr hJ).col_emb _).trans (((toyExample hc).col_emb σ hc _).symm.trans (exampleChain_col_apply σ hc))⟩

end ChSrc

@[reducible] def fieldsOn (D : D7) (X : Fields) (emb : D.what₂.Tau → (X.E →+* X.K)) : Fields :=
  { X with Tau := D.what₂.Tau, ftTau := inferInstance, deTau := Classical.decEq _, emb := emb }

theorem ChSrc.liftTie_chainTh (D : D7) (T : Formalism.MainNotions.TaylorLogMetric.Tor D) (e : Formalism.MainNotions.TaylorLogMetric.FamE D) (X : Fields) (emb : D.what₂.Tau → (X.E →+* X.K))
    (A : ChSrc (fieldsOn D X emb) D.R) (σ : X.K →+* ℂ) (u : D.what₂.Word) (cD : D.what₂.Tau → ℂ) (Th : A.ThFam)
    (O : Formalism.MainNotions.GL3Theta.LiftObj D (A.chainTh σ (D.hcW u) cD Th)) (i : ℕ)
    (hf : ∀ y, O.frm i y = y.1) (hf' : ∀ y, O.frm (i + 1) y = y.1) (hd : O.dgen = cD) (hT : ∀ c c', O.Th i c c' = Th i c c')
    (hK : ∀ c c', Formalism.MainNotions.GL3Theta.IsKer D T e O.S (O.lat i c).1 (O.lat (i + 1) c').1 (O.Th i c c')) :
    Formalism.MainNotions.GL3Theta.liftTie D T e O i := by
  refine ⟨hK, fun c c' Q y' => ?_⟩
  simp only [hf, hf', hd, hT]
  exact (A.chainJet_unf σ (D.hcW u) _ i c c' Q y').trans (eval_jetMap_jetC D cD _ Q y'.1)

end GlobalTheory.GO

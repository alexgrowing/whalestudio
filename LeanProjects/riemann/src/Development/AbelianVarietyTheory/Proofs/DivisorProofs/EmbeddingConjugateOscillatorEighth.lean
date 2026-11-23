import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrAtEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFockVacuumProperties

noncomputable section

namespace GlobalTheory.GalOne.PhaseAt

section General

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

theorem inner_of_int {K : Type} [Field K] [StarRing K] {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n) {W : Type}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (c₁ : VV K lam →ₛₗ[σ] W)
    (pr : VV K lam →ₗ⋆[K] VV K lam →ₗ[K] K)
    (hp : ∀ a a', inner ℂ (c₁ (bVV K lam a)) (c₁ (bVV K lam a')) = σ (pr (bVV K lam a) (bVV K lam a')))
    (u v : VV K lam) (P : MvPolynomial (I × Fin n × Fin n) ℤ) (hP : (u : Pol K I n) = map (Int.castRingHom K) P) :
    inner ℂ (c₁ u) (c₁ v) = σ (pr u v) := by
  have hu : ∀ a, (bVV K lam).repr u a ∈ Formalism.DivisionValues.cmMax K := by
    refine fk_descent _ (bVVfun K lam) (bVVfun_spec K lam).1 (fun k => ?_) _ ?_
    · obtain ⟨Pk, hPk⟩ := bVVfun_int K lam k
      rw [hPk]
      exact fk_int_mem _ _
    · have h := congrArg (fun x : VV K lam => (x : Pol K I n)) ((bVV K lam).sum_repr u)
      simp only [bVV_coe, Submodule.coe_sum, Submodule.coe_smul] at h
      rw [h, hP]
      exact fk_int_mem _ _
  generalize bVV K lam = b at hp hu
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  conv_rhs => rw [← b.sum_repr u, ← b.sum_repr v]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_mul,
    RingHom.id_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [starRingEnd_apply (b.repr u a'), hu a' σ]

theorem up_add {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n)
    (x y : VV K lam) : GlobalTheory.AdTh.CoefExt.up φ lam (x + y) = GlobalTheory.AdTh.CoefExt.up φ lam x + GlobalTheory.AdTh.CoefExt.up φ lam y :=
  Subtype.ext (map_add (MvPolynomial.map φ) _ _)

theorem up_smul {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n)
    (a : K) (x : VV K lam) : GlobalTheory.AdTh.CoefExt.up φ lam (a • x) = φ a • GlobalTheory.AdTh.CoefExt.up φ lam x := by
  apply Subtype.ext
  simp only [GlobalTheory.AdTh.CoefExt.up, Submodule.coe_smul, smul_eq_C_mul, map_mul, map_C]

theorem up_id {K : Type} [Field K] {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n)
    (x : VV K lam) : GlobalTheory.AdTh.CoefExt.up (RingHom.id K) lam x = x :=
  Subtype.ext (MvPolynomial.map_id _)

end General

section Letters

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
open GlobalTheory.AdTh.PhaseMap
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {m n : ℕ} {l : Geo.Tor.Level H} (c : Coeff l)
  (φ : c.F →+* ℂ) {e : D.what₂.Tau → D.what₂.Tau}

abbrev mv (e : D.what₂.Tau → D.what₂.Tau) (lt : LtN Dw n → FVar D m n) : LtN Dw n → FVar D m n :=
  fun ℓ => (e (lt ℓ).1, (lt ℓ).2)

def toG (lt : LtN Dw n → FVar D m n) : MvPolynomial (LtN Dw n) c.F →+* MvPolynomial (FVar D m n) ℂ :=
  (MvPolynomial.rename lt).toRingHom.comp (MvPolynomial.map φ)

variable {lt : LtN Dw n → FVar D m n}

theorem toG_apply (P : MvPolynomial (LtN Dw n) c.F) :
    toG c φ lt P = MvPolynomial.rename lt (MvPolynomial.map φ P) := rfl

theorem toG_X (ℓ : LtN Dw n) : toG c φ lt (MvPolynomial.X ℓ) = MvPolynomial.X (lt ℓ) := by
  simp [toG_apply]

theorem toG_C (a : c.F) : toG c φ lt (MvPolynomial.C a) = MvPolynomial.C (φ a) := by
  simp [toG_apply]

theorem toG_injective (hl : IsLt (mv e lt)) (h : IsTyp D H) : Function.Injective (toG c φ lt) :=
  (MvPolynomial.rename_injective _ fun _ _ hh => hl.injective h (congrArg (fun k : FVar D m n => (e k.1, k.2)) hh)).comp
    (MvPolynomial.map_injective _ φ.injective)

theorem toG_minorP (σ : D.host.E →+* ℂ) (i : ℕ) (hi : i < Dw.mult σ) (col : Fin (i + 1) → Fin n) :
    toG c φ lt (minorPolynomial c σ i hi col) =
      (Matrix.of fun b s : Fin (i + 1) =>
        (MvPolynomial.X (lt ⟨σ, ⟨s.val, by omega⟩, col b⟩) : MvPolynomial (FVar D m n) ℂ)).det := by
  rw [minorPolynomial, RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext1 b s
  exact toG_X c φ _

theorem toG_pG (he : Function.Bijective e) (hl : IsLt (mv e lt)) (h : IsTyp D H) (hn : Dw.p + Dw.q ≤ n)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (hp : ∀ t, p t = Dw.p) (hq : ∀ t, q t = Dw.q)
    (hap : ∀ t k, k < Dw.p → a (tauE D (e t), k) = ap t k)
    (ham : ∀ t k, k < Dw.q → a (conjEmb (tauE D (e t)), k) = am t k) :
    toG c φ lt (pG (Dw := Dw) c a n) = Formalism.IndefR.Datum.delta p q ap am := by
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => conjEmb (tauE D t)) := by
    refine ⟨?_, fun σ => ?_⟩
    · rintro (s | s) (t | t) e
      · exact congrArg _ (GlobalTheory.SmoothForms.RealPts.tauE_injective D e)
      · exact absurd e (h.ne _ _)
      · exact absurd (Eq.symm e) (h.ne _ _)
      · exact congrArg _ (GlobalTheory.SmoothForms.RealPts.tauE_injective D (conjEmb_inj e))
    · by_cases hσ : InPsi H σ
      · obtain ⟨t, ht⟩ := (h.1 σ).1 hσ
        exact ⟨Sum.inl t, ht.symm⟩
      · obtain ⟨t, ht⟩ := (h.2 σ).1 hσ
        exact ⟨Sum.inr t, ht.symm⟩
  have hprod : ∀ f : (D.host.E →+* ℂ) → MvPolynomial (FVar D m n) ℂ,
      ∏ σ, f σ = ∏ t, f (tauE D (e t)) * f (conjEmb (tauE D (e t))) := fun f => by
    rw [← hb.prod_comp, Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← he.prod_comp]
    rfl
  rw [pG, map_prod, hprod, Formalism.IndefR.Datum.delta]
  refine Finset.prod_congr rfl fun t _ => ?_
  have m1 := h.mult_pos Dw (e t)
  have m2 := h.mult_neg Dw (e t)
  rw [deltaAt, hp, hq]
  congr 1
  · rw [map_prod]
    conv_rhs => rw [← m1, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (i : ℕ) < Dw.p := lt_of_lt_of_eq i.2 m1
    rw [map_pow, dif_pos (by omega), if_pos ((h.1 _).2 ⟨e t, rfl⟩), toG_minorP]
    congr 1
    · rw [minorPlus]
      congr 1
      ext1 b s
      have h1 := hl.pos h (ℓ := ⟨tauE D (e t), ⟨s.val, by have := s.2; omega⟩, Fin.castLE (by omega) b⟩) rfl
      exact X_eq_varF _ (he.1 h1.1) h1.2.1 (congrArg Fin.val (hl _).1)
    · show aStep Dw a (tauE D (e t)) i = _
      rw [aStep, hap t i hi]
      congr 1
      split_ifs with h1
      · exact hap t _ (by omega)
      · rfl
  · rw [map_prod]
    conv_rhs => rw [← m2, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (i : ℕ) < Dw.q := lt_of_lt_of_eq i.2 m2
    rw [map_pow, dif_pos (by omega), if_neg ((h.2 _).2 ⟨e t, rfl⟩), toG_minorP]
    congr 1
    · rw [minorMinus]
      congr 1
      ext1 b s
      have h1 := hl.neg h (ℓ := ⟨conjEmb (tauE D (e t)), ⟨s.val, by have := s.2; omega⟩,
        Fin.cast (by omega) (Fin.natAdd (n - (i.val + 1)) b)⟩) rfl
      exact X_eq_varF _ (he.1 h1.1) h1.2 (congrArg Fin.val (hl _).1)
    · show aStep Dw a (conjEmb (tauE D (e t))) i = _
      rw [aStep, ham t i hi]
      congr 1
      split_ifs with h1
      · exact ham t _ (by omega)
      · rfl

theorem toG_gaStar (he : Function.Injective e) (hl : IsLt (mv e lt)) (h : IsTyp D H)
    (r1 : ∀ t, relab c φ (tauE D (e t)) = tauE D t) (r2 : ∀ t, relab c φ (conjEmb (tauE D (e t))) = conjEmb (tauE D t))
    (pW : D.what₂.Tau → ℕ) (hp : ∀ t, pW t = Dw.p)
    (ga : Matrix (Fin n) (Fin n) D.host.E) (U : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ t a b, (U t)⁻¹ a b = conj (tauE D t (ga b a))) (P : MvPolynomial (LtN Dw n) c.F) :
    toG c φ lt (gaStar c (ga.map (IsCMField.complexConj D.host.E)) P) = PhaseMap.sub pW U (toG c φ lt P) := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, toG_C, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P ℓ hP =>
    simp only [map_mul, hP]
    congr 1
    rw [toG_X, gaStar, MvPolynomial.aeval_X, MvPolynomial.aeval_X, letB, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hc : lt ⟨ℓ.1, ℓ.2.1, j⟩ = ((lt ℓ).1, (lt ℓ).2.1, j) :=
      Prod.ext (he (congrArg Prod.fst (hl.col h ℓ j))) (congrArg Prod.snd (hl.col h ℓ j) :)
    have h0 : (lt ℓ).2.2 = ℓ.2.2 := (hl ℓ).1
    rw [map_mul, toG_C, toG_X, hc, hU, hp, h0]
    congr 2
    show relab c φ ℓ.1 (IsCMField.complexConj D.host.E (ga j ℓ.2.2)) = _
    rw [IsCMField.complexEmbedding_complexConj]
    rcases (hl ℓ).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · replace h2 : ((lt ℓ).2.1 : ℕ) = ℓ.2.1 := h2
      rw [if_pos (h2 ▸ (hl.pos h h1).2.2)]
      exact congrArg (fun σ : D.host.E →+* ℂ => conj (σ _)) ((congrArg (relab c φ) h1).trans (r1 _))
    · replace h2 : ((lt ℓ).2.1 : ℕ) = Dw.p + ℓ.2.1 := h2
      rw [if_neg (by omega)]
      exact congrArg (fun σ : D.host.E →+* ℂ => conj (σ _)) ((congrArg (relab c φ) h1).trans (r2 _))

end Letters

end GlobalTheory.GalOne.PhaseAt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.PhaseAt

open GlobalTheory.AdTh GlobalTheory.AdTh.PhaseMap

end GlobalTheory.GalOne.PhaseAt

end

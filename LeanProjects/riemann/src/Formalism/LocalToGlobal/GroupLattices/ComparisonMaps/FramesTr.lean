import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ValUniqOf
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.YvRatOfValRat

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}

theorem frames_tr' (emb : Tau → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (γ : GL (Fin n) E)
    (hγ : γ ∈ UJ (σ : E →+* E) J) (z' : Frames (gramC J emb)) : ∃ z : Frames (gramC J emb), IsTr (atInf emb γ) z' z := by
  refine ⟨Subtype.mk (fun τ => atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * z'.1 τ) (fun τ => ?_), fun τ => rfl⟩
  rw [Matrix.det_mul]
  refine IsUnit.mul ?_ (z'.2 τ)
  have hdet : (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ).det = emb τ (γ : Matrix (Fin n) (Fin n) E).det := by
    rw [RingHom.map_det]; rfl
  rw [hdet]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit).map (emb τ)

variable (S : StepLevel F E σ J T f bad) (emb : Tau → E →+* ℂ) (embLL : LL →+* ℂ)
  (G : GAtP p) (e : LL →+* G.Kf) (A : LocAt F E n G) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
  {V cls : Type} [AddCommGroup V] [Module LL V] (embV : V →ₛₗ[embLL] (cls → Frames (gramC J emb) → ℂ))
  (yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))

def PtAll : Prop :=
  ∀ c : cls, ∃ (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (γ : GL (Fin n) E) (κ : S.U),
    γ ∈ UJ (σ : E →+* E) J ∧ A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (yc c).1 * κ.1)

variable {S emb embLL G e A pos embV yc}

theorem cmpC_rat (x : V) : RatFn G e (cmpC S emb embLL G e A pos embV yc x) := by
  delta RatFn RatFnP
  intro i L
  by_cases h : G.P.IsLatTup L
  · exact ⟨valC S emb embLL G A pos embV yc x i L, by simp [cmpC, h]⟩
  · exact ⟨0, by simp [cmpC, h]⟩

private theorem isLatTup_colSpan_GL (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
    G.P.IsLatTup (fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) := by
  intro v
  exact Exists.intro (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))
    ⟨(Matrix.isUnit_iff_isUnit_det _).mp (g v).isUnit, rfl⟩

theorem cmpC_inj (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hex : ValEx S emb embLL G A pos embV yc)
    (hall : PtAll S G A yc) (hinj : Function.Injective embV) (x : V)
    (hx : cmpC S emb embLL G e A pos embV yc x = 0) : x = 0 := by
  apply hinj
  rw [map_zero]
  funext c z'
  obtain ⟨i, g, γ, κ, hγ, hpt⟩ := hall c
  obtain ⟨z, hz⟩ := frames_tr' emb hc γ hγ z'
  have hL := isLatTup_colSpan_GL (G := G) g
  obtain ⟨Q, hQ⟩ := hex x i (fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) hL
  have hv : IsVal S emb embLL G A pos embV yc x i (fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
      (valC S emb embLL G A pos embV yc x i
      (fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))) := by
    have h' : ∃ Q, IsVal S emb embLL G A pos embV yc x i
        (fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) Q := ⟨Q, hQ⟩
    unfold valC
    rw [dif_pos h']
    exact Classical.choose_spec h'
  have h0 : valC S emb embLL G A pos embV yc x i
      (fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) = 0 := by
    have h1 : cmpC S emb embLL G e A pos embV yc x i
        (fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) = 0 := by
      rw [hx]; rfl
    simp only [cmpC, if_pos hL] at h1
    exact MvPolynomial.map_injective e e.injective (by rw [h1, map_zero])
  rw [h0] at hv
  unfold IsVal at hv
  have h2 := hv.2 g (fun v => rfl) c γ hγ κ hpt z z' hz
  simp only [map_zero, Pi.zero_apply] at h2
  simp only [Pi.zero_apply]
  exact (mul_eq_zero.mp h2.symm).resolve_left (by simp)

private theorem isVal_add {x y : V} {i : G.comp} {L : G.P.Tup} {Q Q' : XR G.P LL}
    (h : IsVal S emb embLL G A pos embV yc x i L Q) (h' : IsVal S emb embLL G A pos embV yc y i L Q') :
    IsVal S emb embLL G A pos embV yc (x + y) i L (Q + Q') := by
  unfold IsVal at *
  refine ⟨Submodule.add_mem _ h.1 h'.1, fun g hg c γ hγ κ hpt z z' hz => ?_⟩
  simp only [map_add, Pi.add_apply, mul_add]
  rw [h.2 g hg c γ hγ κ hpt z z' hz, h'.2 g hg c γ hγ κ hpt z z' hz]

private theorem isVal_smul {x : V} {i : G.comp} {L : G.P.Tup} {Q : XR G.P LL} (a : LL)
    (h : IsVal S emb embLL G A pos embV yc x i L Q) :
    IsVal S emb embLL G A pos embV yc (a • x) i L (a • Q) := by
  unfold IsVal at *
  refine ⟨Submodule.smul_mem _ a h.1, fun g hg c γ hγ κ hpt z z' hz => ?_⟩
  have hm : MvPolynomial.map embLL (a • Q) = (embLL a) • MvPolynomial.map embLL Q := by
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.smul_eq_C_mul]
  rw [hm, map_smul, Pi.smul_apply, h.2 g hg c γ hγ κ hpt z z' hz, map_smulₛₗ]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem isVal_valC_of_isLatTup (hex : ValEx S emb embLL G A pos embV yc) (x : V) (i : G.comp) {L : G.P.Tup}
    (hL : G.P.IsLatTup L) : IsVal S emb embLL G A pos embV yc x i L (valC S emb embLL G A pos embV yc x i L) := by
  have h' := hex x i L hL
  unfold valC
  rw [dif_pos h']
  exact Classical.choose_spec h'

theorem cmpC_li (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hex : ValEx S emb embLL G A pos embV yc)
    (hu : ValUniq S emb embLL G A pos embV yc) (hall : PtAll S G A yc) (hinj : Function.Injective embV)
    {ι : Type} (b : ι → V) (hb : LinearIndependent LL b) :
    LinearIndependent G.Kf fun a => cmpC S emb embLL G e A pos embV yc (b a) := by
  let Φ : V →ₗ[LL] (G.comp → {L : G.P.Tup // G.P.IsLatTup L} → XR G.P LL) :=
    { toFun := fun x i L => valC S emb embLL G A pos embV yc x i L.1
      map_add' := fun x y => by
        funext i L
        exact hu (x + y) i L.1 _ _ L.2 (isVal_valC_of_isLatTup hex (x + y) i L.2)
          (isVal_add (isVal_valC_of_isLatTup hex x i L.2) (isVal_valC_of_isLatTup hex y i L.2))
      map_smul' := fun a x => by
        funext i L
        exact hu (a • x) i L.1 _ _ L.2 (isVal_valC_of_isLatTup hex (a • x) i L.2)
          (isVal_smul a (isVal_valC_of_isLatTup hex x i L.2)) }
  have hΦ : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    refine cmpC_inj (e := e) hc hex hall hinj x ?_
    funext i L
    by_cases hL : G.P.IsLatTup L
    · have h3 := congrFun (congrFun hx i) ⟨L, hL⟩
      simp only [cmpC, if_pos hL, Pi.zero_apply]
      rw [show valC S emb embLL G A pos embV yc x i L = 0 from h3, map_zero]
    · simp only [cmpC, if_neg hL, Pi.zero_apply]
  have hw := hb.map' Φ hΦ
  letI : Algebra LL G.Kf := e.toAlgebra
  have hsm : ∀ (q : LL) (y : G.Kf), y * e q = q • y := fun q y => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
  let β := Module.Basis.ofVectorSpace LL G.Kf
  rw [linearIndependent_iff']
  rw [linearIndependent_iff'] at hw
  intro s g hg a ha
  have key : ∀ k, ∀ a ∈ s, β.repr (g a) k = 0 := by
    intro k
    apply hw s (fun a => β.repr (g a) k)
    ext i L m
    have h1 := congrArg (MvPolynomial.coeff m) (congrFun (congrFun hg i) L.1)
    simp only [Finset.sum_apply, Pi.smul_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
      smul_eq_mul, Pi.zero_apply, MvPolynomial.coeff_zero, cmpC, if_pos L.2, MvPolynomial.coeff_map] at h1
    have h2 := congrArg (fun y => β.repr y k) h1
    simp only [map_sum, map_zero, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_zero, Pi.zero_apply,
      hsm, map_smul, Finsupp.smul_apply, smul_eq_mul] at h2
    simp only [Finset.sum_apply, Pi.smul_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
      smul_eq_mul, Pi.zero_apply, MvPolynomial.coeff_zero]
    rw [← h2]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have h4 : β.repr (g a) = 0 := Finsupp.ext fun k => key k a ha
  exact β.repr.map_eq_zero_iff.mp h4

end Formalism.L2.G.Cmp

end

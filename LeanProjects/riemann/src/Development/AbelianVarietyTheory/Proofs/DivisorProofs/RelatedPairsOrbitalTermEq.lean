import Mathlib
import GroundTheory.Brauer.TensorSimple
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivializationsDifferByGroupPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjOfTwistedNormConjHermitianTripleRegulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCentralizerRegularTwistedCentraliser
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumConjData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumCompMulEquiv
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SigmaSplitSymmInl
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKDef.DRel

variable {p : ℕ} [Fact p.Prime]

section Generic

variable {S A : Type*} [Ring S] [CommRing A] [Algebra A S]

theorem triv_move (σ : S →+* Sᵐᵒᵖ) (b : S) (x Y : Sˣ) (t s : A)
    (hx : (x : S) * b * (σ x).unop = algebraMap A S t) :
    ((x * Y⁻¹ : Sˣ) : S) * (algebraMap A S s * ((Y : S) * b * (σ Y).unop)) * (σ ((x * Y⁻¹ : Sˣ) : S)).unop =
      algebraMap A S (s * t) := by
  have h1 : (σ Y).unop * (σ ((Y⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  calc ((x * Y⁻¹ : Sˣ) : S) * (algebraMap A S s * ((Y : S) * b * (σ Y).unop)) * (σ ((x * Y⁻¹ : Sˣ) : S)).unop
      = s • ((x : S) * ((((Y⁻¹ : Sˣ) : S) * Y) * b * ((σ Y).unop * (σ ((Y⁻¹ : Sˣ) : S)).unop)) * (σ x).unop) := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, ← Algebra.smul_def, mul_smul_comm,
          smul_mul_assoc, mul_assoc]
    _ = algebraMap A S (s * t) := by
        rw [Units.inv_mul, h1, one_mul, mul_one, hx, map_mul, Algebra.smul_def]

end Generic

variable {G : HTGroup p}

theorem sh_mul (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_units (y : G.Cˣ) : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
  rw [← sh_mul, Units.inv_mul]; simp [sh]

theorem key (y v : G.Cˣ) (β : G.C) (s : ℚ) :
    ((y * v * y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C s * (y * β * sh G y)) * sh G ((y * v * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C s * (y * ((v : G.C) * β * sh G v) * sh G y) := by
  calc ((y * v * y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C s * (y * β * sh G y)) * sh G ((y * v * y⁻¹ : G.Cˣ) : G.C)
      = s • ((y : G.C) * v * (((y⁻¹ : G.Cˣ) : G.C) * y) * β * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) *
          sh G v * sh G y) := by
        simp only [Units.val_mul, sh_mul, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = _ := by
        rw [Units.inv_mul, sh_units, mul_one, mul_one, Algebra.smul_def]; simp only [mul_assoc]

theorem scal (y : G.Cˣ) (β : G.C) (s u : ℚ) :
    algebraMap ℚ G.C u * (algebraMap ℚ G.C s * (y * β * sh G y)) =
      algebraMap ℚ G.C s * (y * (algebraMap ℚ G.C u * β) * sh G y) := by
  simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm u s]

theorem cancel (y : G.Cˣ) (X Z : G.C) (s : ℚ) (hs : s ≠ 0)
    (h : algebraMap ℚ G.C s * (y * X * sh G y) = algebraMap ℚ G.C s * (y * Z * sh G y)) : X = Z := by
  have h' : (y : G.C) * X * sh G y = y * Z * sh G y := by
    have := congrArg (fun w => algebraMap ℚ G.C s⁻¹ * w) h
    simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hs, map_one, one_mul] using this
  have e : ∀ W : G.C, W = ((y⁻¹ : G.Cˣ) : G.C) * (y * W * sh G y) * sh G ((y⁻¹ : G.Cˣ) : G.C) := by
    intro W
    rw [mul_assoc, mul_assoc, sh_units, mul_one, ← mul_assoc, Units.inv_mul, one_mul]
  rw [e X, e Z, h']

def cj (y : G.Cˣ) : G.Cˣ × ℚˣ ≃* G.Cˣ × ℚˣ := (MulAut.conj y).prodCongr (MulEquiv.refl ℚˣ)

theorem cj_apply (y : G.Cˣ) (v : G.Cˣ × ℚˣ) : cj y v = (y * v.1 * y⁻¹, v.2) := rfl

def innerAlgEquiv (R : Type) {A : Type} [CommRing R] [Ring A] [Algebra R A] (y : Aˣ) : A ≃ₐ[R] A :=
  GlobalTheory.InnerAutomorphism.innerAut R y

theorem rel_pol_c (P Q : DPair G) (h : P.Rel Q) : Q.pol = P.pol ∧ Q.c = P.c := by
  obtain ⟨y, s, _, hβ, hγ⟩ := h
  refine ⟨?_, ?_⟩
  · have h := minpoly.algEquiv_eq (innerAlgEquiv G.F y) (P.γ : G.C)
    simp only [DPair.pol, hγ, Units.val_mul]
    exact h
  · have hy : ∀ X : G.C, sh G (y : G.C) * (sh G ((y⁻¹ : G.Cˣ) : G.C) * X) = X := by
      intro X
      rw [← mul_assoc, sh_units, one_mul]
    have core : (y : G.C) * P.γ * ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * P.β * sh G y) *
        (sh G ((y⁻¹ : G.Cˣ) : G.C) * (sh G P.γ * sh G y)) = (P.c : ℚ) • ((y : G.C) * P.β * sh G y) := by
      calc (y : G.C) * P.γ * ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * P.β * sh G y) *
            (sh G ((y⁻¹ : G.Cˣ) : G.C) * (sh G P.γ * sh G y))
          = y * (P.γ * P.β * sh G P.γ) * sh G y := by
            simp only [mul_assoc, Units.inv_mul_cancel_left, hy]
        _ = _ := by
            rw [P.sim, ← Algebra.smul_def]
            simp only [mul_smul_comm, smul_mul_assoc]
    have key : algebraMap ℚ G.C (Q.c : ℚ) * Q.β = algebraMap ℚ G.C (P.c : ℚ) * Q.β := by
      rw [← Q.sim, hγ, hβ]
      simp only [Units.val_mul, sh_mul, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
      rw [core, smul_comm]
    have hinj : Function.Injective (algebraMap ℚ G.C) := (algebraMap ℚ G.C).injective
    exact Units.ext (hinj ((Units.mul_left_inj Q.β).mp key))

theorem mem_of (P Q : DPair G) (y : G.Cˣ) (s : ℚ) (hβ : (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y))
    (hγ : Q.γ = y * P.γ * y⁻¹) (v : G.Cˣ × ℚˣ) (hv : v ∈ P.cent) : cj y v ∈ Q.cent := by
  obtain ⟨h1, h2⟩ := hv
  change v.1 * P.γ = P.γ * v.1 at h1
  change (v.1 : G.C) * P.β * sh G v.1 = algebraMap ℚ G.C v.2 * P.β at h2
  refine ⟨?_, ?_⟩
  · change y * v.1 * y⁻¹ * Q.γ = Q.γ * (y * v.1 * y⁻¹)
    rw [hγ]
    calc y * v.1 * y⁻¹ * (y * P.γ * y⁻¹) = y * (v.1 * P.γ) * y⁻¹ := by group
      _ = y * (P.γ * v.1) * y⁻¹ := by rw [h1]
      _ = _ := by group
  · change ((y * v.1 * y⁻¹ : G.Cˣ) : G.C) * Q.β * sh G ((y * v.1 * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C v.2 * Q.β
    rw [hβ, key, h2, scal]

theorem mem_back (P Q : DPair G) (y : G.Cˣ) (s : ℚ) (hs : s ≠ 0)
    (hβ : (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y))
    (hγ : Q.γ = y * P.γ * y⁻¹) (w : G.Cˣ × ℚˣ) (hw : w ∈ Q.cent) : (cj y).symm w ∈ P.cent := by
  obtain ⟨h1, h2⟩ := hw
  set v := (cj y).symm w with hv
  have hw' : w = cj y v := by rw [hv, MulEquiv.apply_symm_apply]
  rw [hw', cj_apply] at h1 h2
  change y * v.1 * y⁻¹ * Q.γ = Q.γ * (y * v.1 * y⁻¹) at h1
  change ((y * v.1 * y⁻¹ : G.Cˣ) : G.C) * Q.β * sh G ((y * v.1 * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C v.2 * Q.β at h2
  refine ⟨?_, ?_⟩
  · change v.1 * P.γ = P.γ * v.1
    rw [hγ] at h1
    have : y * (v.1 * P.γ) * y⁻¹ = y * (P.γ * v.1) * y⁻¹ := by
      calc y * (v.1 * P.γ) * y⁻¹ = y * v.1 * y⁻¹ * (y * P.γ * y⁻¹) := by group
        _ = (y * P.γ * y⁻¹) * (y * v.1 * y⁻¹) := h1
        _ = _ := by group
    simpa using this
  · change (v.1 : G.C) * P.β * sh G v.1 = algebraMap ℚ G.C v.2 * P.β
    rw [hβ, key, scal] at h2
    exact cancel y _ _ s hs h2

theorem cent_map (P Q : DPair G) (y : G.Cˣ) (s : ℚ) (hs : s ≠ 0)
    (hβ : (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y))
    (hγ : Q.γ = y * P.γ * y⁻¹) : P.cent.map (cj y).toMonoidHom = Q.cent := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact mem_of P Q y s hβ hγ v hv
  · intro hw
    exact ⟨(cj y).symm w, mem_back P Q y s hs hβ hγ w hw, by simp⟩

theorem toAf_val (P : DPair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (v : P.cent) :
    ((P.toAf x t hx v : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) =
      (x * Units.map (inC G (AfP p)).toMonoidHom v.1.1 * x⁻¹, Units.map (algebraMap ℚ (AfP p)).toMonoidHom v.1.2) :=
  rfl

theorem toQr_val (P : DPair G) (r : ℕ) (z : Gr G r) (v : P.cent) :
    P.toQr r z v = z⁻¹ * inclG G r (locC G v.1) * z := by
  simp [DPair.toQr, carry, MulAut.conj_apply]

theorem locC_conj (y : G.Cˣ) (v : G.Cˣ × ℚˣ) :
    locC G (y * v.1 * y⁻¹, v.2) = locC G (y, 1) * locC G v * (locC G (y, 1))⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  ext <;> simp

theorem triv_rel (P Q : DPair G) (y : G.Cˣ) (s : ℚ) (hs : s ≠ 0)
    (hβ : (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y))
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) :
    Triv G (AfP p) Q.β (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹)
      (Units.map (algebraMap ℚ (AfP p)).toMonoidHom (Units.mk0 s hs) * t) := by
  have e1 : inC G (AfP p) (sh G y) = (starT G.star (AfP p) (inC G (AfP p) y)).unop :=
    (starT_tmul G.star (AfP p) 1 _).symm
  have e2 : inC G (AfP p) (algebraMap ℚ G.C s) =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (algebraMap ℚ (AfP p) s) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C).commutes _
  unfold Triv
  rw [hβ, map_mul, map_mul, map_mul, e1, e2]
  have := triv_move (starT G.star (AfP p)) (inC G (AfP p) P.β) x (Units.map (inC G (AfP p)).toMonoidHom y)
    (t : AfP p) (algebraMap ℚ (AfP p) s) hx
  simpa [mul_assoc] using this

end GlobalTheory.LKDef.DRel

namespace GlobalTheory.LKDef.DRel

open Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem charpoly_rho_eq_map_pol (G : HTGroup p) (P : DPair G) (w : Fin G.m) :
    (G.rho w (P.γ : G.C)).charpoly = P.pol.map (G.embW w) := by
  letI : Algebra G.F (G.Fw w) := (G.embW w).toAlgebra
  have hg : ∀ a, G.rho w (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) a :=
    fun a => by rw [G.rho_F, Matrix.algebraMap_eq_diagonal]; rfl
  let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) (G.Fw w) := { G.rho w with commutes' := hg }
  let L : G.Fw w ⊗[G.F] G.C →ₐ[G.Fw w] Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    Algebra.TensorProduct.lift (Algebra.ofId (G.Fw w) _) g (fun r _ => Algebra.commute_algebraMap_left r _)
  haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)
  have hL : ∀ x : G.C, L ((1 : G.Fw w) ⊗ₜ x) = G.rho w x := fun x => by
    show (Algebra.TensorProduct.lift _ g _) ((1 : G.Fw w) ⊗ₜ x) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  set γ : G.C := (P.γ : G.C) with hγ
  have hdeg : (minpoly G.F γ).natDegree = G.n := P.reg.1
  have hli : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hdeg] at this
    exact this
  have hT : LinearIndependent (G.Fw w) (fun i : Fin G.n => (1 : G.Fw w) ⊗ₜ[G.F] (γ ^ (i : ℕ))) :=
    Module.Flat.linearIndependent_one_tmul hli
  have hM : LinearIndependent (G.Fw w) (fun i : Fin G.n => (G.rho w γ) ^ (i : ℕ)) := by
    have := hT.map' L.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
    have e : (fun i : Fin G.n => (G.rho w γ) ^ (i : ℕ)) =
        L.toLinearMap ∘ (fun i : Fin G.n => (1 : G.Fw w) ⊗ₜ[G.F] (γ ^ (i : ℕ))) := by
      funext i
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply]
      rw [hL, map_pow]
    rw [e]
    exact this
  have hint : IsIntegral (G.Fw w) (G.rho w γ) := Algebra.IsIntegral.isIntegral _
  set q := minpoly (G.Fw w) (G.rho w γ) with hq
  have hqm : q.Monic := minpoly.monic hint
  have hqdeg : G.n ≤ q.natDegree := by
    by_contra hlt
    push_neg at hlt
    have h0 : aeval (G.rho w γ) q = 0 := minpoly.aeval _ _
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at h0
    have h1 := Fintype.linearIndependent_iff.1 hM (fun i => q.coeff i) h0 ⟨q.natDegree, hlt⟩
    have h2 : q.coeff q.natDegree = 1 := hqm.coeff_natDegree
    rw [h2] at h1
    exact one_ne_zero h1
  have hpol : aeval (G.rho w γ) (P.pol.map (G.embW w)) = 0 := by
    have h : aeval (g γ) (minpoly G.F γ) = 0 := by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    change aeval (G.rho w γ) ((minpoly G.F γ).map (algebraMap G.F (G.Fw w))) = 0
    rw [Polynomial.aeval_map_algebraMap]
    exact h
  have hFint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hm1 : (P.pol.map (G.embW w)).Monic := (minpoly.monic hFint).map _
  have hn1 : (P.pol.map (G.embW w)).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact hdeg
  have e1 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hm1 (minpoly.dvd _ _ hpol)
    (by rw [hn1]; exact hqdeg)
  have e2 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm (Matrix.charpoly_monic _)
    (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hqdeg)
  rw [e2, e1]

theorem atP_regular (G : HTGroup p) (P : DPair G) :
    regular₂ G P.atP ∧ ∀ y : P.cent, locC G y.1 ∈ Subgroup.centralizer {P.atP} := by
  refine ⟨fun w => ?_, fun y => ?_⟩
  · show (P.atP.2 w).val.charpoly.Separable
    rw [show (P.atP.2 w).val.charpoly = P.pol.map (G.embW w) from charpoly_rho_eq_map_pol G P w]
    exact P.reg.2.map
  · rw [Subgroup.mem_centralizer_singleton_iff]
    show locC G y.1 * locC G (P.γ, P.c) = locC G (P.γ, P.c) * locC G y.1
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext y.2.1 (mul_comm _ _)

theorem term_eq_termAt (G : HTGroup p) (P : DPair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ)
    (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (hr : 0 < r) (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g)
    (hφ : ∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) P.β x t) (δ z : Gr G r) (hn : IsNrm G r P.atP δ z) :
    P.term Kf f r K φ = P.termAt Kf f r K φ x t hx δ z := by
  have hex : ∃ dz : Gr G r × Gr G r, IsNrm G r P.atP dz.1 dz.2 := ⟨(δ, z), hn⟩
  unfold DPair.term
  rw [dif_pos hex]
  set x₀ := P.trivAf.choose
  set t₀ := P.trivAf.choose_spec.choose
  have h₀ : Triv G (AfP p) P.β x₀ t₀ := P.trivAf.choose_spec.choose_spec
  set δ₀ := hex.choose.1
  set z₀ := hex.choose.2
  have hn₀ : IsNrm G r P.atP δ₀ z₀ := hex.choose_spec
  obtain ⟨hreg, hcent⟩ := atP_regular G P
  obtain ⟨g, hgx⟩ := GlobalTheory.LKMid.triv_quot p G (AfP p) (P.β : G.C) x x₀ t t₀ hx h₀
  obtain ⟨g₂, hδ, hcz⟩ := GlobalTheory.T.twistedConj_of_twistedNormConj_hermitianTriple_regular p G r P.atP δ z δ₀ z₀ hr hreg hn hn₀
  have htw := GlobalTheory.CarryCent.map_centralizer_carry p G r P.atP δ z hr hreg hn
  have hAf : P.toAf x₀ t₀ h₀ = (MulAut.conj g⁻¹⁻¹).toMonoidHom.comp (P.toAf x t hx) := by
    ext y : 1
    apply Subtype.ext
    apply Prod.ext
    · have e : x₀ = (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x := by rw [hgx, inv_mul_cancel_right]
      simp only [DPair.toAf, MonoidHom.comp_apply, MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, MonoidHom.prodMap, MonoidHom.prod_apply, Subgroup.coe_subtype]
      rw [e]; group
    · simp only [DPair.toAf, MonoidHom.comp_apply, MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul, Prod.snd_inv, MonoidHom.prodMap, MonoidHom.prod_apply, Subgroup.coe_subtype]
      rw [mul_comm, inv_mul_cancel_left]
  have hQr : P.toQr r z₀ = (MulAut.conj g₂⁻¹).toMonoidHom.comp (P.toQr r z) := by
    ext y : 1
    have := hcz (locC G y.1) (hcent y)
    simp only [DPair.toQr, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [this]
  have hself : P.toAf x₀ t₀ h₀ P.self = g⁻¹⁻¹ * P.toAf x t hx P.self * g⁻¹ := by
    rw [hAf]; simp [MulAut.conj_apply]
  unfold DPair.termAt
  rw [hself, hAf, hQr, hδ]
  refine GlobalTheory.PointSumConj.pointSum_conj_data _ _ _ _ _ _ _ _ _ _ _ hf hφ ?_ ?_
  · intro y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · exact y.2.1
    · exact mul_comm _ _
  · intro y
    have hm : P.toQr r z y ∈ GlobalTheory.BCT.twCent (sigG G r) δ := by
      rw [← htw]; exact ⟨locC G y.1, hcent y, rfl⟩
    exact hm

theorem term_eq_of_rel (G : HTGroup p) (P Q : DPair G) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (hr : 0 < r)
    (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) (hφ : ∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g)
    (hPQ : P.Rel Q) : Q.term Kf f r K φ = P.term Kf f r K φ := by
  obtain ⟨y, s, hs, hβ, hγ⟩ := hPQ
  have hc : Q.c = P.c := (rel_pol_c P Q ⟨y, s, hs, hβ, hγ⟩).2
  have hat : Q.atP = locC G (y, 1) * P.atP * (locC G (y, 1))⁻¹ := by
    have := locC_conj y (P.γ, P.c)
    simp only [DPair.atP, hγ, hc]
    exact this
  have hnrm : ∀ δ z, IsNrm G r P.atP δ z → IsNrm G r Q.atP δ (inclG G r (locC G (y, 1)) * z) := by
    intro δ z h
    unfold IsNrm at h ⊢
    rw [h, hat, map_mul, map_mul, map_inv]
    group
  by_cases hP : ∃ dz : Gr G r × Gr G r, IsNrm G r P.atP dz.1 dz.2
  · obtain ⟨⟨δ, z⟩, hδ⟩ := hP
    obtain ⟨x, t, hx⟩ := P.trivAf
    have hx' := triv_rel P Q y s hs.ne' hβ x t hx
    rw [term_eq_termAt G P Kf f r K φ hr hf hφ x t hx δ z hδ,
      term_eq_termAt G Q Kf f r K φ hr hf hφ _ _ hx' δ _ (hnrm δ z hδ)]
    let e : P.cent ≃* Q.cent := ((cj y).subgroupMap P.cent).trans
      (MulEquiv.subgroupCongr (cent_map P Q y s hs.ne' hβ hγ))
    have he : ∀ v : P.cent, ((e v : Q.cent) : G.Cˣ × ℚˣ) = cj y v := fun v => rfl
    have hA : (Q.toAf _ _ hx').comp e.toMonoidHom = P.toAf x t hx := by
      ext v : 1
      apply Subtype.ext
      rw [MonoidHom.comp_apply, toAf_val, toAf_val]
      simp only [MulEquiv.coe_toMonoidHom, he, cj_apply]
      refine Prod.ext ?_ rfl
      simp only [map_mul, map_inv]
      group
    have hQr : (Q.toQr r (inclG G r (locC G (y, 1)) * z)).comp e.toMonoidHom = P.toQr r z := by
      ext v : 1
      rw [MonoidHom.comp_apply, toQr_val, toQr_val]
      simp only [MulEquiv.coe_toMonoidHom, he, cj_apply]
      rw [locC_conj, map_mul, map_mul, map_inv]
      group
    have hS : Q.self = e P.self := by
      apply Subtype.ext
      rw [he, cj_apply]
      exact Prod.ext hγ hc
    unfold DPair.termAt
    have hS' : Q.toAf _ _ hx' (e P.self) = P.toAf x t hx P.self := by rw [← hA]; rfl
    rw [hS, ← GlobalTheory.pointSum_comp_mulEquiv e, hS', hA, hQr]
  · have hQ : ¬ ∃ dz : Gr G r × Gr G r, IsNrm G r Q.atP dz.1 dz.2 := by
      rintro ⟨⟨δ, z⟩, h⟩
      apply hP
      refine ⟨(δ, (inclG G r (locC G (y, 1)))⁻¹ * z), ?_⟩
      unfold IsNrm at h ⊢
      rw [h, hat, map_mul, map_mul, map_inv]
      group
    unfold DPair.term
    rw [dif_neg hP, dif_neg hQ]

end GlobalTheory.LKDef.DRel

namespace GlobalTheory.LKDef.DPair

theorem rel_pol_c_term : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Q Q' : DPair G), Q.Rel Q' → Q.pol = Q'.pol ∧ Q.c = Q'.c ∧ ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → Q.term Kf f r K φ = Q'.term Kf f r K φ := by
  intro p _ G Q Q' h
  obtain ⟨h1, h2⟩ := GlobalTheory.LKDef.DRel.rel_pol_c Q Q' h
  refine ⟨h1.symm, h2.symm, fun Kf f r K φ hr hf hφ => ?_⟩
  exact (GlobalTheory.LKDef.DRel.term_eq_of_rel G Q Q' Kf f r K φ hr hf hφ h).symm

end GlobalTheory.LKDef.DPair

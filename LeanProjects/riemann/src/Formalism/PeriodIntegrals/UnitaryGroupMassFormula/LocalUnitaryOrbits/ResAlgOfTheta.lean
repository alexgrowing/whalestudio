import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.QSplitHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CrossMSmulRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensCntRes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUnifOIff

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def redR : v.adicCompletionIntegers F →+* 𝓞 F ⧸ v.asIdeal where
  toFun x := red v (x : Fv F v)
  map_one' := red_one v
  map_mul' x y := red_mul v x.2 y.2
  map_zero' := red_zero v
  map_add' x y := red_add v x.2 y.2

theorem redR_surj : Function.Surjective (redR v) := fun t => by
  obtain ⟨x, hx, h⟩ := red_surj v t
  exact ⟨⟨x, hx⟩, h⟩

theorem sc_eq' (c : Fv F v) : sc (E := E) v c = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := rfl

theorem inclR_alg' (a : F) :
    inclR (F := F) (Fv F v) (algebraMap F E a) = sc (E := E) v (algebraMap F (Fv F v) a) := by
  rw [sc_eq', ← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E).commutes a

theorem sigR_sc (c : Fv F v) : sigR (Fv F v) σ (sc (E := E) v c) = sc (E := E) v c := by
  show Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ (c ⊗ₜ (1 : E)) = c ⊗ₜ (1 : E)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem sigR_incl (e : E) : sigR (Fv F v) σ (inclR (F := F) (Fv F v) e) = inclR (F := F) (Fv F v) (σ e) := by
  show Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ ((1 : Fv F v) ⊗ₜ e) = (1 : Fv F v) ⊗ₜ σ e
  rw [Algebra.TensorProduct.map_tmul]
  rfl

def ThetaBas : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∃ θ : 𝓞 E,
    (∀ x ∈ OEv (E := E) v, ∃ a0 a1 : v.adicCompletionIntegers F,
      x = sc (E := E) v (a0 : Fv F v) + sc (E := E) v (a1 : Fv F v) * inclR (F := F) (Fv F v) (θ : E)) ∧
    (∀ a0 a1 : Fv F v, sc (E := E) v a0 + sc (E := E) v a1 * inclR (F := F) (Fv F v) (θ : E) = 0 →
      a0 = 0 ∧ a1 = 0) ∧
    (∀ a0 a1 : 𝓞 F ⧸ v.asIdeal, algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 *
      Ideal.Quotient.mk (IE (E := E) v) θ = 0 → a0 = 0 ∧ a1 = 0) ∧
    (∀ q : QE (E := E) v, ∃ a0 a1 : 𝓞 F ⧸ v.asIdeal,
      q = algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 * Ideal.Quotient.mk (IE (E := E) v) θ)

theorem resQ_of (hT : ThetaBas σ J ψ v) : ResQ σ J ψ v := by
  intro hstd hun ϖ hϖ
  obtain ⟨θ, h1, h2, h3, h4⟩ := hT hstd hun
  set iθ : Fv F v ⊗[F] E := inclR (F := F) (Fv F v) (θ : E) with hiθ
  have hss : sigO σ (sigO σ θ) = θ := RingOfIntegers.ext (by simp only [sigO_coe]; exact sig_sig σ hstd.1 _)
  obtain ⟨t, ht⟩ := fix_int σ hstd.1 (θ + sigO σ θ) (by rw [map_add, hss, add_comm])
  obtain ⟨m, hm⟩ := fix_int σ hstd.1 (θ * sigO σ θ) (by rw [map_mul, hss, mul_comm])
  have hθ2 : θ * θ = algebraMap (𝓞 F) (𝓞 E) t * θ - algebraMap (𝓞 F) (𝓞 E) m := by
    rw [ht, hm]; ring
  have hσθ : sigO σ θ = algebraMap (𝓞 F) (𝓞 E) t - θ := by rw [ht]; ring
  have hinc : ∀ a : 𝓞 F, inclR (F := F) (Fv F v) ((algebraMap (𝓞 F) (𝓞 E) a : 𝓞 E) : E) =
      sc (E := E) v (iO v a) := fun a => inclR_alg' v (a : F)
  have hiθ2 : iθ * iθ = sc (E := E) v (iO v t) * iθ - sc (E := E) v (iO v m) := by
    have e1 := congrArg (fun y : 𝓞 E => inclR (F := F) (Fv F v) (y : E)) hθ2
    simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, map_mul, map_sub, hinc] at e1
    exact e1
  have hsiθ : sigR (Fv F v) σ iθ = sc (E := E) v (iO v t) - iθ := by
    have e1 := congrArg (fun y : 𝓞 E => inclR (F := F) (Fv F v) (y : E)) hσθ
    simp only [AddSubgroupClass.coe_sub, map_sub, hinc, sigO_coe] at e1
    rw [hiθ, sigR_incl]
    exact e1
  let T0 : v.adicCompletionIntegers F := ⟨iO v t, mem_O_iO v t⟩
  let M0 : v.adicCompletionIntegers F := ⟨iO v m, mem_O_iO v m⟩
  have huniq : ∀ a0 a1 b0 b1 : Fv F v, sc (E := E) v a0 + sc (E := E) v a1 * iθ =
      sc (E := E) v b0 + sc (E := E) v b1 * iθ → a0 = b0 ∧ a1 = b1 := by
    intro a0 a1 b0 b1 h
    have := h2 (a0 - b0) (a1 - b1) (by simp only [sc_eq', map_sub] at h ⊢; linear_combination h)
    exact ⟨sub_eq_zero.1 this.1, sub_eq_zero.1 this.2⟩
  choose c0 c1 hc using fun x : OR (E := E) v => h1 (x : Fv F v ⊗[F] E) x.2
  have hco : ∀ (x : OR (E := E) v) (a0 a1 : v.adicCompletionIntegers F),
      (x : Fv F v ⊗[F] E) = sc (E := E) v (a0 : Fv F v) + sc (E := E) v (a1 : Fv F v) * iθ →
      c0 x = a0 ∧ c1 x = a1 := by
    intro x a0 a1 h
    have := huniq _ _ _ _ ((hc x).symm.trans h)
    exact ⟨Subtype.ext this.1, Subtype.ext this.2⟩
  let g : 𝓞 F ⧸ v.asIdeal →+* QE (E := E) v := algebraMap _ _
  let θb : QE (E := E) v := Ideal.Quotient.mk (IE (E := E) v) θ
  let ρf : OR (E := E) v → QE (E := E) v := fun x => g (redR v (c0 x)) + g (redR v (c1 x)) * θb
  have hρ : ∀ (x : OR (E := E) v) (a0 a1 : v.adicCompletionIntegers F),
      (x : Fv F v ⊗[F] E) = sc (E := E) v (a0 : Fv F v) + sc (E := E) v (a1 : Fv F v) * iθ →
      ρf x = g (redR v a0) + g (redR v a1) * θb := by
    intro x a0 a1 h
    obtain ⟨e0, e1⟩ := hco x a0 a1 h
    simp only [ρf, e0, e1]
  have hgt : ∀ a : 𝓞 F, g (redR v ⟨iO v a, mem_O_iO v a⟩) =
      Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) a) := by
    intro a
    show algebraMap _ _ (red v (iO v a)) = _
    rw [red_iO, Ideal.Quotient.algebraMap_quotient_map_quotient]
  have hQθ : θb * θb = Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) t) * θb -
      Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) m) := by
    simp only [θb]
    rw [← map_mul, ← map_mul, ← map_sub, hθ2]
  let ρ : OR (E := E) v →+* QE (E := E) v :=
    { toFun := ρf
      map_one' := by
        rw [hρ 1 1 0 (by simp only [sc_eq', OneMemClass.coe_one, ZeroMemClass.coe_zero, map_one, map_zero,
          zero_mul, add_zero])]
        simp
      map_mul' := fun x y => by
        rw [hρ (x * y) (c0 x * c0 y - c1 x * c1 y * M0) (c0 x * c1 y + c1 x * c0 y + c1 x * c1 y * T0) ?_]
        · show _ = ρf x * ρf y
          simp only [ρf, map_add, map_sub, map_mul, T0, M0, hgt]
          linear_combination (-(g (redR v (c1 x)) * g (redR v (c1 y)))) * hQθ
        · show (x : Fv F v ⊗[F] E) * (y : Fv F v ⊗[F] E) = _
          rw [hc x, hc y]
          simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, AddMemClass.coe_add, sc_eq', map_mul, map_sub,
            map_add, T0, M0] at hiθ2 ⊢
          linear_combination (algebraMap (Fv F v) (Fv F v ⊗[F] E) (c1 x) *
            algebraMap (Fv F v) (Fv F v ⊗[F] E) (c1 y)) * hiθ2
      map_zero' := by
        rw [hρ 0 0 0 (by simp only [sc_eq', ZeroMemClass.coe_zero, map_zero, zero_mul, add_zero])]
        simp
      map_add' := fun x y => by
        rw [hρ (x + y) (c0 x + c0 y) (c1 x + c1 y) ?_]
        · show _ = ρf x + ρf y
          simp only [ρf, map_add]
          ring
        · show (x : Fv F v ⊗[F] E) + (y : Fv F v ⊗[F] E) = _
          rw [hc x, hc y]
          simp only [AddMemClass.coe_add, sc_eq', map_add]
          ring }
  refine ⟨ρ, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨a0, a1, rfl⟩ := h4 q
    obtain ⟨b0, rfl⟩ := redR_surj v a0
    obtain ⟨b1, rfl⟩ := redR_surj v a1
    have m0 : sc (E := E) v (b0 : Fv F v) ∈ OEv (E := E) v := by
      simpa using sc_mul_mem_oEv v b0.2 (Orb.oSub (E := E) v).1
    have m1 : sc (E := E) v (b1 : Fv F v) * iθ ∈ OEv (E := E) v := sc_mul_mem_oEv v b1.2 (Orb.gen_mem v θ)
    exact ⟨⟨_, Orb.oev_add v m0 m1⟩, hρ _ b0 b1 rfl⟩
  · intro x
    have hρx : ρ x = g (redR v (c0 x)) + g (redR v (c1 x)) * θb := rfl
    have hz : ∀ c : v.adicCompletionIntegers F, redR v c = 0 ↔ ∃ d : v.adicCompletionIntegers F,
        (c : Fv F v) = ϖ * d := by
      intro c
      show red v (c : Fv F v) = 0 ↔ _
      rw [red_eq_zero_iff v c.2, ← mem_unifO_iff v hϖ c]
      rfl
    have hϖO : ϖ ∈ v.adicCompletionIntegers F := by
      show Valued.v ϖ ≤ 1
      rw [show Valued.v ϖ = _ from hϖ]
      exact le_of_lt (by decide)
    rw [hρx]
    constructor
    · intro h0
      obtain ⟨z0, z1⟩ := h3 _ _ h0
      obtain ⟨d0, hd0⟩ := (hz _).1 z0
      obtain ⟨d1, hd1⟩ := (hz _).1 z1
      refine ⟨sc (E := E) v (d0 : Fv F v) + sc (E := E) v (d1 : Fv F v) * iθ,
        Orb.oev_add v (by simpa using sc_mul_mem_oEv v d0.2 (Orb.oSub (E := E) v).1)
          (sc_mul_mem_oEv v d1.2 (Orb.gen_mem v θ)), ?_⟩
      rw [hc x, hd0, hd1]
      simp only [sc_eq', map_mul]
      ring
    · rintro ⟨o, ho, hxo⟩
      obtain ⟨d0, d1, hd⟩ := h1 o ho
      have hx' : (x : Fv F v ⊗[F] E) = sc (E := E) v (ϖ * d0) + sc (E := E) v (ϖ * d1) * iθ := by
        rw [hxo, hd]; simp only [sc_eq', map_mul]; ring
      obtain ⟨e0, e1⟩ := huniq _ _ _ _ ((hc x).symm.trans hx')
      rw [(hz _).2 ⟨d0, e0⟩, (hz _).2 ⟨d1, e1⟩]
      simp
  · intro x y hxy
    have hy : (y : Fv F v ⊗[F] E) = sc (E := E) v ((c0 x + c1 x * T0 : v.adicCompletionIntegers F) : Fv F v) +
        sc (E := E) v ((-c1 x : v.adicCompletionIntegers F) : Fv F v) * iθ := by
      rw [hxy, hc x, map_add, map_mul, sigR_sc, sigR_sc, hsiθ]
      simp only [AddMemClass.coe_add, MulMemClass.coe_mul, NegMemClass.coe_neg, sc_eq', map_add, map_mul, map_neg, T0]
      ring
    show ρf y = sigQ σ v (ρf x)
    rw [hρ y _ _ hy]
    simp only [ρf, map_add, map_mul, map_neg, hgt, sigQ_alg]
    have hsq : sigQ σ v θb = Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) t) - θb := by
      simp only [θb]
      rw [sigQ_mk, hσθ, map_sub]
    rw [hsq]
    have hsg : ∀ c, sigQ σ v (g c) = g c := fun c => sigQ_alg σ v c
    simp only [hsg]
    rw [show g (redR v T0) = Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) t) from hgt t]
    ring

theorem resAlg_of_theta (hT : ThetaBas σ J ψ v) (hE : EtaLink σ J ψ v) : ResAlg σ J ψ v :=
  resAlg_of' σ J ψ v (resQ_of σ J ψ v hT) hE

end PI.OmLocU.Red

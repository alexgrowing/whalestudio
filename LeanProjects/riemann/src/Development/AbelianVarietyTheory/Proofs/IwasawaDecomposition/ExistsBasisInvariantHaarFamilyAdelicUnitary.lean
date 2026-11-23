import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupPointsEquivOfChangeOfBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open Formalism.UG (cT cT_mul cT_one bc UJ)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.GaugeRef

section Cong

variable {A : Type} [CommRing A] {M : ℕ} (s : A →+* A)

def act (J : Matrix (Fin M) (Fin M) A) (P : GL (Fin M) A) : Matrix (Fin M) (Fin M) A :=
  cT s (P : Matrix (Fin M) (Fin M) A) * J * (P : Matrix (Fin M) (Fin M) A)

theorem act_one (J : Matrix (Fin M) (Fin M) A) : act s J 1 = J := by
  simp [act, cT_one]

theorem act_mul (J : Matrix (Fin M) (Fin M) A) (P Q : GL (Fin M) A) :
    act s J (P * Q) = act s (act s J P) Q := by
  simp only [act, Units.val_mul, cT_mul, Matrix.mul_assoc]

def cong (M : ℕ) : Setoid (Matrix (Fin M) (Fin M) A) where
  r J J' := ∃ P : GL (Fin M) A, J' = act s J P
  iseqv := ⟨fun J => ⟨1, (act_one s J).symm⟩,
    fun ⟨P, h⟩ => ⟨P⁻¹, by rw [h, ← act_mul, mul_inv_cancel, act_one]⟩,
    fun ⟨P, h⟩ ⟨Q, h'⟩ => ⟨P * Q, by rw [h', h, act_mul]⟩⟩

end Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ}

omit [NumberField E] in
theorem frameRel_iff (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E) (g : HA (AF F) σ J)
    (g' : HA (AF F) σ J') : FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g g' ↔
      HA.mat (AF F) σ J' g' = (bc (inclR (AF F)) P)⁻¹ * HA.mat (AF F) σ J g * bc (inclR (AF F)) P := by
  rw [mul_assoc, eq_inv_mul_iff_mul_eq, eq_comm, ← Units.val_inj]
  rfl

omit [NumberField E] in
theorem bc_mem {J : Matrix (Fin M) (Fin M) E} {u : GL (Fin M) E} (hu : act (σ : E →+* E) J u = J) :
    bc (inclR (AF F)) u ∈ HR (AF F) σ J := by
  show cT (sigR (AF F) σ) ((u : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) * J.map (inclR (AF F)) *
    (u : Matrix (Fin M) (Fin M) E).map (inclR (AF F)) = J.map (inclR (AF F))
  have h : cT (sigR (AF F) σ) ((u : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) =
      (cT (σ : E →+* E) (u : Matrix (Fin M) (Fin M) E)).map (inclR (AF F)) := by
    ext i j
    simp [cT, sigR, inclR]
  rw [h, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congrArg (fun X : Matrix (Fin M) (Fin M) E => X.map (inclR (F := F) (AF F))) hu

def IsTransport (σ : E →ₐ[F] E) (J₀ J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J)) : Prop :=
  ∃ (P : GL (Fin M) E) (e : HA (AF F) σ J₀ ≃* HA (AF F) σ J), J = act (σ : E →+* E) J₀ P ∧
    (∀ g, FrameRel J₀ J (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧ μ = Measure.haar.map e

theorem frame (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E) (h : J' = act (σ : E →+* E) J P) :
    (∃ e : HA (AF F) σ J ≃* HA (AF F) σ J', ∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧
    ∀ e : HA (AF F) σ J ≃* HA (AF F) σ J', (∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) →
      Continuous e ∧ Continuous e.symm :=
  ⟨(GlobalTheory.T.unitary_group_points_equiv_of_change_of_basis F E σ (AF F) M J J' P h).1.exists, (GlobalTheory.T.unitary_group_points_equiv_of_change_of_basis F E σ (AF F) M J J' P h).2⟩

theorem IsTransport.isHaar {J₀ J : Matrix (Fin M) (Fin M) E} {μ : Measure (HA (AF F) σ J)}
    (h : IsTransport σ J₀ J μ) : μ.IsHaarMeasure := by
  obtain ⟨P, e, hJ, he, rfl⟩ := h
  obtain ⟨h1, h2⟩ := (frame J₀ J P hJ).2 e he
  exact e.isHaarMeasure_map _ h1 h2

theorem IsTransport.map_eq (hσ : IsCMExt F E σ) {J₀ J J' : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    {μ : Measure (HA (AF F) σ J)} {μ' : Measure (HA (AF F) σ J')}
    (h : IsTransport σ J₀ J μ) (h' : IsTransport σ J₀ J' μ') {P : GL (Fin M) E} (hP : J' = act (σ : E →+* E) J P)
    (e : HA (AF F) σ J ≃* HA (AF F) σ J') (he : ∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) :
    μ.map e = μ' := by
  haveI := h.isHaar
  obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hσ
  haveI : μ.IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic σ (GlobalTheory.HermLineZeros.conj_invol hσ) (δ := σ d - d)
      (sub_ne_zero.2 hd) (by rw [map_sub, GlobalTheory.HermLineZeros.conj_invol hσ, neg_sub]) hJ μ
  obtain ⟨P₁, e₁, hJ₁, he₁, hμ⟩ := h
  obtain ⟨P₂, e₂, hJ₂, he₂, rfl⟩ := h'
  have hu : act (σ : E →+* E) J (P₁⁻¹ * P₂ * P⁻¹) = J := by
    conv_lhs => rw [hJ₁, ← act_mul, ← mul_assoc, mul_inv_cancel_left, act_mul, ← hJ₂, hP, ← act_mul,
      mul_inv_cancel, act_one]
  let u : HA (AF F) σ J := (⟨_, bc_mem hu⟩ : HR (AF F) σ J)
  have hc := ((frame J J' P hP).2 e he).1.measurable
  have hc₁ := ((frame J₀ J P₁ hJ₁).2 e₁ he₁).1.measurable
  have key : (e₂ : _ → _) = e ∘ ((fun x => x * u) ∘ (fun x => u⁻¹ * x)) ∘ e₁ := by
    funext g
    apply Subtype.ext
    have a := (frameRel_iff _ _ _ _ _).1 (he₂ g)
    have b := (frameRel_iff _ _ _ _ _).1 (he (u⁻¹ * e₁ g * u))
    have c := (frameRel_iff _ _ _ _ _).1 (he₁ g)
    refine a.trans (Eq.trans ?_ b.symm)
    show _ = _ * ((bc (inclR (AF F)) (P₁⁻¹ * P₂ * P⁻¹))⁻¹ * HA.mat (AF F) σ J (e₁ g) *
      bc (inclR (AF F)) (P₁⁻¹ * P₂ * P⁻¹)) * _
    rw [c]
    simp only [map_mul, map_inv]
    group
  have hl := measurable_const_mul u⁻¹
  have hr := measurable_mul_const u
  rw [key, ← Measure.map_map hc ((hr.comp hl).comp hc₁), ← Measure.map_map (hr.comp hl) hc₁, ← hμ,
    ← Measure.map_map hr hl, map_mul_left_eq_self, map_mul_right_eq_self]

theorem exists_isTransport (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    ∃ μ, IsTransport σ (Quotient.mk (cong (σ : E →+* E) M) J).out J μ := by
  obtain ⟨P, hP⟩ := Quotient.mk_out (s := cong (σ : E →+* E) M) J
  obtain ⟨e, he⟩ := (frame (σ := σ) _ J P hP).1
  exact ⟨_, P, e, hP, he, rfl⟩

theorem exists_isHaar_basisInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ G : GaugeFam F E σ, G.IsHaar ∧ G.BasisInv := by
  intro F E _ _ _ _ _ σ hσ
  choose μ hμ using fun (M : ℕ) (J : Matrix (Fin M) (Fin M) E) => exists_isTransport σ J
  refine ⟨⟨μ⟩, fun M J _ => (hμ M J).isHaar, fun M J J' P hJ hP => ⟨(frame J J' P hP).1, fun e he => ?_⟩⟩
  have h' := hμ M J'
  rw [← Quotient.sound (s := cong (σ : E →+* E) M) (a := J) (b := J') ⟨P, hP⟩] at h'
  exact (hμ M J).map_eq hσ hJ h' hP e he

end GlobalTheory.GaugeRef

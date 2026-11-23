import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelePowerIntegrableCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeBump

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem disp_add_x {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : Pl F) (x₀ : Fin n → E)
    (k : UA σ J) (l : (AE F E)ˣ) (i : Fin n) :
    disp v x₀ k l i + compFin F E v (incV F x₀ i) =
      compFin F E v (l : AE F E) * compFin F E v ((mat k⁻¹ *ᵥ incV F x₀) i) := by
  simp only [disp, sub_add_cancel, map_mul]

theorem lam_mul_x_eq_sum {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : Pl F) (x₀ : Fin n → E)
    (k : UA σ J) (l : (AE F E)ˣ) (i₀ : Fin n) :
    compFin F E v (l : AE F E) * compFin F E v (incV F x₀ i₀) =
      ∑ j, compFin F E v (mat k i₀ j) * (compFin F E v (incV F x₀ j) + disp v x₀ k l j) := by
  have h1 : mat k *ᵥ (mat k⁻¹ *ᵥ incV F x₀) = incV F x₀ := by
    rw [Matrix.mulVec_mulVec, show mat k * mat k⁻¹ = 1 from Units.mul_inv k.1, Matrix.one_mulVec]
  have hx : incV F x₀ i₀ = ∑ j, mat k i₀ j * (mat k⁻¹ *ᵥ incV F x₀) j := by
    conv_lhs => rw [← h1]
    rfl
  rw [hx, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, add_comm (compFin F E v (incV F x₀ j)), disp_add_x]
  ring

theorem mulVec_eq_of_disp {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} (v : Pl F) (x₀ : Fin n → E)
    {k : UA σ X.J} (hk : k ∈ UAt σ X (evFin F v)) {l : (AE F E)ˣ} (hl : l ∈ idelesAt E (evFin F v))
    (h : disp v x₀ k l = 0) : mat k *ᵥ incV F x₀ = (l : AE F E) • incV F x₀ := by
  have hk' : k⁻¹ ∈ UAtSub σ X (evFin F v) := inv_mem (show k ∈ UAtSub σ X (evFin F v) from hk)
  have hz : ∀ i, (l : AE F E) * (mat k⁻¹ *ᵥ incV F x₀) i = incV F x₀ i := by
    intro i
    have hat : At (evFin F v) ((l : AE F E) * (mat k⁻¹ *ᵥ incV F x₀) i - incV F x₀ i) := by
      intro u hu
      have e : (l : AE F E) * (mat k⁻¹ *ᵥ incV F x₀) i - incV F x₀ i =
          ((l : AE F E) - 1) * (mat k⁻¹ *ᵥ incV F x₀) i + ((mat k⁻¹ - 1) *ᵥ incV F x₀) i := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
        ring
      have h2 : u • ((mat k⁻¹ - 1) *ᵥ incV F x₀) = 0 := by
        rw [← Matrix.smul_mulVec, hk' u hu, Matrix.zero_mulVec]
      rw [e, smul_add, ← smul_mul_assoc, hl u hu, zero_mul, zero_add, ← Pi.smul_apply, h2, Pi.zero_apply]
    obtain ⟨h1, h2⟩ := at_evFin_iff.1 hat
    refine sub_eq_zero.1 (GlobalTheory.Doubling.adele_ext (fun w => by rw [h1 w, map_zero]) fun w => ?_)
    by_cases hw : w = v
    · subst hw
      rw [map_zero, map_sub, map_mul]
      have := congrFun h i
      simpa [disp, map_mul] using this
    · rw [h2 w hw, map_zero]
  calc mat k *ᵥ incV F x₀ = mat k *ᵥ ((l : AE F E) • (mat k⁻¹ *ᵥ incV F x₀)) := by
        congr 1; funext i; exact (hz i).symm
    _ = (l : AE F E) • (mat k *ᵥ (mat k⁻¹ *ᵥ incV F x₀)) := Matrix.mulVec_smul _ _ _
    _ = _ := by rw [Matrix.mulVec_mulVec, show mat k * mat k⁻¹ = 1 from Units.mul_inv k.1, Matrix.one_mulVec]

theorem disp_proper_near : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (r s : ℕ) (H : Plane E n n₁) (j₀ j₁ : ℕ) (K : Subgroup (UA σ X.J)),
    B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ j₀ j₁ → IsCompact (K : Set (UA σ X.J)) →
    ∀ (v : Pl F) (Ω : Set (KAt K (evFin F v) × idelesAt E (evFin F v))), IsOpen Ω →
      (∀ p : KAt K (evFin F v) × idelesAt E (evFin F v), mat p.1.1 *ᵥ incV F H.x = (p.2.1 : AE F E) • incV F H.x → p ∈ Ω) →
      ∃ U ∈ 𝓝 (0 : Fin n → Fv F v ⊗[F] E), ∃ C : Set (idelesAt E (evFin F v)), IsCompact C ∧
        ∀ p : KAt K (evFin F v) × idelesAt E (evFin F v), GlobalTheory.ConeBump.disp v H.x p.1.1 p.2.1 ∈ U → p ∈ Ω ∧ p.2 ∈ C := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ r s H j₀ j₁ K _hB _hX hH hK v Ω hΩ hfib
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : T2Space (Fv F v ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  haveI : CompactSpace (KAt K (evFin F v)) := isCompact_iff_compactSpace.1 (isCompact_KAt hK _)
  obtain ⟨i₀, hi₀⟩ : ∃ i, H.x i ≠ 0 := by
    by_contra h
    push_neg at h
    have h1 := hH.xy
    rw [show H.x = 0 from funext h] at h1
    simp [form] at h1
  have hcf : Continuous (compFin F E v) :=
    GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v))
      ((RestrictedProduct.continuous_eval v).comp continuous_snd)
  obtain ⟨sv, hsx⟩ : ∃ sv : Fv F v ⊗[F] E, sv * compFin F E v (incV F H.x i₀) = 1 :=
    ⟨compFin F E v (inclR (F := F) (AF F) (H.x i₀)⁻¹), by
      rw [incV, ← map_mul, ← map_mul, inv_mul_cancel₀ hi₀, map_one, map_one]⟩
  have hmat : Continuous fun q : KAt K (evFin F v) => mat q.1 :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hmatinv : Continuous fun q : KAt K (evFin F v) => mat q.1⁻¹ :=
    Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hOc : IsCompact (intLoc F E v : Set (Fv F v ⊗[F] E)) := (isCompact_isOpen_intLoc v).1
  have hOo : IsOpen (intLoc F E v : Set (Fv F v ⊗[F] E)) := (isCompact_isOpen_intLoc v).2
  let D : Set (Fin n → Fv F v ⊗[F] E) := Set.univ.pi fun _ => (intLoc F E v : Set (Fv F v ⊗[F] E))
  have hDc : IsCompact D := isCompact_univ_pi fun _ => hOc
  have hDo : IsOpen D := isOpen_set_pi Set.finite_univ fun _ _ => hOo
  let Φ₁ : KAt K (evFin F v) × (Fin n → Fv F v ⊗[F] E) → Fv F v ⊗[F] E :=
    fun q => sv * ∑ j, compFin F E v (mat q.1.1 i₀ j) * (compFin F E v (incV F H.x j) + q.2 j)
  have hΦ₁ : Continuous Φ₁ := continuous_const.mul (continuous_finset_sum _ fun j _ =>
    (hcf.comp ((continuous_apply j).comp ((continuous_apply i₀).comp (hmat.comp continuous_fst)))).mul
      (continuous_const.add (show Continuous fun q : KAt K (evFin F v) × (Fin n → Fv F v ⊗[F] E) => q.2 j from
        (continuous_apply j).comp continuous_snd)))
  let A₁ := Φ₁ '' (Set.univ ×ˢ D)
  have hA₁ : IsCompact A₁ := (isCompact_univ.prod hDc).image hΦ₁
  let Φ₂ : KAt K (evFin F v) × (Fv F v ⊗[F] E) → Fv F v ⊗[F] E :=
    fun q => sv * compFin F E v ((mat q.1.1⁻¹ *ᵥ incV F H.x) i₀) * q.2
  have hΦ₂ : Continuous Φ₂ := (continuous_const.mul (hcf.comp ((continuous_apply i₀).comp
    ((hmatinv.comp continuous_fst).matrix_mulVec continuous_const)))).mul continuous_snd
  let A₂ := Φ₂ '' (Set.univ ×ˢ (intLoc F E v : Set (Fv F v ⊗[F] E)))
  have hA₂ : IsCompact A₂ := (isCompact_univ.prod hOc).image hΦ₂
  let W : Set (Fv F v ⊗[F] E)ˣ :=
    {w | (w : Fv F v ⊗[F] E) ∈ A₁ ∧ ((w⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ A₂}
  have hW : IsCompact W := by
    have e : W = Units.embedProduct (Fv F v ⊗[F] E) ⁻¹' (A₁ ×ˢ (MulOpposite.op '' A₂)) := by
      ext w
      simp [W, Units.embedProduct_apply]
    rw [e]
    exact Units.isClosedEmbedding_embedProduct.isCompact_preimage (hA₁.prod (hA₂.image MulOpposite.continuous_op))
  let C : Set (idelesAt E (evFin F v)) := (idelesAtEquiv E v) ⁻¹' W
  have hC : IsCompact C := (Homeomorph.isCompact_preimage (idelesAtEquiv E v).toHomeomorph).2 hW
  let V₀ : Set (Fv F v ⊗[F] E) := Units.val '' ((intLoc F E v).toSubmonoid.units : Set (Fv F v ⊗[F] E)ˣ)
  have hV₀ : IsOpen V₀ :=
    (GlobalTheory.LocTateConv.isOpenEmbedding_val_tens v).isOpenMap _ (Submonoid.isOpen_units hOo)
  let U₀ : Set (Fin n → Fv F v ⊗[F] E) := D ∩ {d | 1 + sv * d i₀ ∈ V₀}
  have hU₀ : IsOpen U₀ :=
    hDo.inter (hV₀.preimage (show Continuous fun d : Fin n → Fv F v ⊗[F] E => 1 + sv * d i₀ by fun_prop))
  have h0U₀ : (0 : Fin n → Fv F v ⊗[F] E) ∈ U₀ :=
    ⟨fun _ _ => zero_mem (intLoc F E v), ⟨1, one_mem _, by simp⟩⟩
  have hbound : ∀ p : KAt K (evFin F v) × idelesAt E (evFin F v), disp v H.x p.1.1 p.2.1 ∈ U₀ → p.2 ∈ C := by
    rintro ⟨k, l⟩ ⟨hd, w, hw, hwv⟩
    have hlv : ((idelesAtEquiv E v l : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) = compFin F E v (l.1 : AE F E) := rfl
    refine ⟨⟨(k, disp v H.x k.1 l.1), ⟨trivial, hd⟩, ?_⟩,
      ⟨(k, ((w⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)), ⟨trivial, ((Submonoid.mem_units_iff _ _).1 hw).2⟩, ?_⟩⟩
    · show sv * ∑ j, compFin F E v (mat k.1 i₀ j) * (compFin F E v (incV F H.x j) + disp v H.x k.1 l.1 j) = _
      rw [← lam_mul_x_eq_sum, mul_left_comm, hsx, mul_one, hlv]
    · symm
      apply Units.inv_eq_of_mul_eq_one_right
      rw [hlv]
      show compFin F E v (l.1 : AE F E) * (sv * compFin F E v ((mat k.1⁻¹ *ᵥ incV F H.x) i₀) *
        ((w⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)) = 1
      have e1 : compFin F E v (l.1 : AE F E) * (sv * compFin F E v ((mat k.1⁻¹ *ᵥ incV F H.x) i₀)) =
          (w : Fv F v ⊗[F] E) := by
        rw [mul_left_comm, ← disp_add_x, mul_add, hsx, add_comm, hwv]
      rw [← mul_assoc, e1, Units.mul_inv]
  let dsp : KAt K (evFin F v) × idelesAt E (evFin F v) → (Fin n → Fv F v ⊗[F] E) :=
    fun p => disp v H.x p.1.1 p.2.1
  have hdsp : Continuous dsp := continuous_pi fun i =>
    (hcf.comp ((Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).mul
      ((continuous_apply i).comp ((hmatinv.comp continuous_fst).matrix_mulVec continuous_const)))).sub continuous_const
  let A : Set (KAt K (evFin F v) × idelesAt E (evFin F v)) := ({p | p.2 ∈ C} ∩ dsp ⁻¹' D) ∩ Ωᶜ
  have hA : IsCompact A := (isCompact_univ.prod hC).of_isClosed_subset
    (((hC.isClosed.preimage continuous_snd).inter (hDc.isClosed.preimage hdsp)).inter hΩ.isClosed_compl)
    (fun p hp => ⟨trivial, hp.1.1⟩)
  have hK₁ : IsClosed (dsp '' A) := (hA.image hdsp).isClosed
  have h0 : (0 : Fin n → Fv F v ⊗[F] E) ∉ dsp '' A := by
    rintro ⟨p, hp, hp0⟩
    exact hp.2 (hfib p (mulVec_eq_of_disp v H.x p.1.2.2 p.2.2 hp0))
  refine ⟨U₀ ∩ (dsp '' A)ᶜ, (hU₀.inter hK₁.isOpen_compl).mem_nhds ⟨h0U₀, h0⟩, C, hC, fun p hp => ?_⟩
  have hpC := hbound p hp.1
  refine ⟨?_, hpC⟩
  by_contra hpΩ
  exact hp.2 ⟨p, ⟨⟨hpC, hp.1.1⟩, hpΩ⟩, rfl⟩
end GlobalTheory.ConeBump

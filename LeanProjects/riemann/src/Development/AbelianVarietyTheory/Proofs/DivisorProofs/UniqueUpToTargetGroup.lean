import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransp
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

open scoped Matrix

section Unitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_sub_left' (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G (x - y) z = herm G x z - herm G y z := by
  simp only [herm, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem herm_sub_right' (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G x (y - z) = herm G x y - herm G x z := by
  simp only [herm, Pi.sub_apply, cc, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem herm_add_right' (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G x (y + z) = herm G x y + herm G x z := by
  simp only [herm, Pi.add_apply, cc, map_add, mul_add, Finset.sum_add_distrib]

theorem herm_smul_left' (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem herm_smul_right' (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G x (c • y) = cc c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, cc, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

def intOf (x : E) (hx : IsIntegral ℤ x) : 𝓞 E := ⟨x, hx⟩

@[simp] theorem coe_intOf (x : E) (hx : IsIntegral ℤ x) : ((intOf x hx : 𝓞 E) : E) = x := rfl

theorem sub_mem_natSMul_of_unitary (G : Matrix (Fin r) (Fin r) E) (L' : Submodule (𝓞 E) (Fin r → E))
    (hint : ∀ x ∈ L', ∀ y ∈ L', IsIntegral ℤ (herm G x y))
    (hdual : ∀ x, (∀ y ∈ L', IsIntegral ℤ (herm G x y)) → x ∈ L')
    (bar : 𝓞 E ≃+* 𝓞 E) (hbar : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E))
    (I : Ideal (𝓞 E)) (M : ℕ) (hM : M ≠ 0)
    (hprod : I * I.map (bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(M : 𝓞 E)})
    (hcop : I ⊔ I.map (bar : 𝓞 E →+* 𝓞 E) = ⊤) (ε : GL (Fin r) E)
    (hiso : ∀ u v, herm G ((ε : Matrix (Fin r) (Fin r) E) *ᵥ u) ((ε : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v)
    (hlat : ∀ v, v ∈ L' ↔ (ε : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ L')
    (hc : ∀ w ∈ L', (ε : Matrix (Fin r) (Fin r) E) *ᵥ w - w ∈ I • L') :
    ∀ w ∈ L', ∃ y ∈ L', (ε : Matrix (Fin r) (Fin r) E) *ᵥ w - w = (M : E) • y := by
  set J := I.map (bar : 𝓞 E →+* 𝓞 E) with hJ

  have hA : ∀ z ∈ L', ∀ u ∈ I • L', ∃ c ∈ J, herm G z u = ((c : 𝓞 E) : E) := by
    intro z hz u hu
    refine Submodule.smul_induction_on hu (fun m hm n hn => ?_) (fun u₁ u₂ h₁ h₂ => ?_)
    · refine ⟨bar m * intOf (herm G z n) (hint z hz n hn), J.mul_mem_right _ (Ideal.mem_map_of_mem _ hm), ?_⟩
      rw [← algebraMap_smul E m n, herm_smul_right']
      show _ = ((bar m : 𝓞 E) : E) * ((intOf (herm G z n) (hint z hz n hn) : 𝓞 E) : E)
      rw [hbar, coe_intOf]
      rfl
    · obtain ⟨c₁, hc₁, e₁⟩ := h₁
      obtain ⟨c₂, hc₂, e₂⟩ := h₂
      refine ⟨c₁ + c₂, J.add_mem hc₁ hc₂, ?_⟩
      rw [herm_add_right', e₁, e₂]
      push_cast
      rfl
  set ε' : Matrix (Fin r) (Fin r) E := (ε : Matrix (Fin r) (Fin r) E) with hε'
  have hεi : ε' * ((ε⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = 1 := by
    rw [hε', ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  intro w hw
  set v := ε' *ᵥ w - w with hv
  have hvI : v ∈ I • L' := hc w hw
  have hvL : v ∈ L' := L'.sub_mem ((hlat w).1 hw) hw

  have hB : ∀ z ∈ L', ∃ c ∈ J, herm G v z = ((c : 𝓞 E) : E) := by
    intro z hz
    set z' := ((ε⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ z with hz'
    have ez : ε' *ᵥ z' = z := by rw [hz', Matrix.mulVec_mulVec, hεi, Matrix.one_mulVec]
    have hz'L : z' ∈ L' := (hlat z').2 (ez ▸ hz)
    obtain ⟨c, hcJ, ec⟩ := hA w hw _ (hc z' hz'L)
    refine ⟨-c, J.neg_mem hcJ, ?_⟩
    rw [herm_sub_right'] at ec
    rw [← ez, hv, herm_sub_left', hiso]
    push_cast
    linear_combination -ec
  have hMO' : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM

  have hC : ∀ m ∈ I, ∃ y ∈ L', m • v = (M : 𝓞 E) • y := by
    intro m hm
    refine ⟨((M : E)⁻¹ * (m : E)) • v, hdual _ fun z hz => ?_, ?_⟩
    · obtain ⟨c, hcJ, ec⟩ := hB z hz
      have hmc : m * c ∈ Ideal.span {(M : 𝓞 E)} := hprod ▸ Ideal.mul_mem_mul hm hcJ
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hmc
      rw [herm_smul_left', ec]
      have : (M : E)⁻¹ * (m : E) * (c : E) = (d : E) := by
        have e2 : ((d * (M : 𝓞 E) : 𝓞 E) : E) = ((m * c : 𝓞 E) : E) := by rw [hd]
        push_cast at e2
        rw [mul_assoc, ← e2, mul_comm (d : E), ← mul_assoc, inv_mul_cancel₀ hMO', one_mul]
      rw [this]
      exact RingOfIntegers.isIntegral_coe d
    · rw [← algebraMap_smul E (M : 𝓞 E), smul_smul, ← algebraMap_smul E m v]
      congr 1
      rw [map_natCast, ← mul_assoc, mul_inv_cancel₀ hMO', one_mul]

  have hD : ∀ m ∈ J, ∃ y ∈ L', m • v = (M : 𝓞 E) • y := by
    intro m hm
    have h1 : m • v ∈ J • (I • L') := Submodule.smul_mem_smul hm hvI
    rw [← Submodule.smul_assoc, Ideal.smul_eq_mul, mul_comm, hprod, Submodule.ideal_span_singleton_smul] at h1
    obtain ⟨y, hy, ey⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1
    exact ⟨y, hy, ey.symm⟩
  have h1 : (1 : 𝓞 E) ∈ I ⊔ J := hcop ▸ Submodule.mem_top
  obtain ⟨m, hm, m', hm', hmm⟩ := Submodule.mem_sup.1 h1
  obtain ⟨y₁, hy₁, e₁⟩ := hC m hm
  obtain ⟨y₂, hy₂, e₂⟩ := hD m' hm'
  refine ⟨y₁ + y₂, L'.add_mem hy₁ hy₂, ?_⟩
  have : v = (M : 𝓞 E) • (y₁ + y₂) := by
    rw [smul_add, ← e₁, ← e₂, ← add_smul, hmm, one_smul]
  rw [this, ← algebraMap_smul E]
  simp

end Unitary

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

open scoped Matrix

section Transfer

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem sub_mem_natSMul_span (A : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (L' Λ : Submodule (𝓞 E) (Fin r → E))
    (hΛ : Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ A, ∃ u ∈ L', v = a • u}) (ε : Matrix (Fin r) (Fin r) E) (M : ℕ)
    (h : ∀ w ∈ L', ∃ y ∈ L', ε *ᵥ w - w = (M : E) • y) :
    ∀ x ∈ Λ, ∃ y ∈ Λ, ε *ᵥ x - x = (M : E) • y := by
  subst hΛ
  intro x hx
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, ha, u, hu, rfl⟩ := hv
    obtain ⟨y, hy, e⟩ := h u hu
    refine ⟨a • y, Submodule.subset_span ⟨a, ha, y, hy, rfl⟩, ?_⟩
    rw [Matrix.mulVec_smul, ← smul_sub, e, smul_comm]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x₁ x₂ _ _ h₁ h₂ =>
    obtain ⟨y₁, hy₁, e₁⟩ := h₁
    obtain ⟨y₂, hy₂, e₂⟩ := h₂
    refine ⟨y₁ + y₂, Submodule.add_mem _ hy₁ hy₂, ?_⟩
    rw [Matrix.mulVec_add, smul_add, ← e₁, ← e₂]
    abel
  | smul c x _ hx =>
    obtain ⟨y, hy, e⟩ := hx
    refine ⟨c • y, Submodule.smul_mem _ c hy, ?_⟩
    rw [← algebraMap_smul E c x, Matrix.mulVec_smul, ← smul_sub, e, ← algebraMap_smul E c y, smul_comm]

end Transfer

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem IsTransp.uniq {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
    (_hp : More p) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (_ho : OwnPin r) (i : Fin D.R.m)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k)
    (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
    (k k₁ k₂ : (uAt r v i).Comp) (a₁ a₂ : GL (Fin D.R.r) D.host.E)
    (h₁ : IsTransp p r i v ψ γ k k₁ a₁) (h₂ : IsTransp p r i v ψ γ k k₂ a₂) :
    k₁ = k₂ ∧ a₁ * a₂⁻¹ ∈ ((uAt r v i).X k₁).Γ := by
  obtain ⟨hm₁, hp₁, hq₁⟩ := h₁
  obtain ⟨hm₂, hp₂, hq₂⟩ := h₂
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hU : IsUnf (uAt r v i) := (h.laws v).p.toLawsCore.unf _ hj _ (r.used v).full.toCore.good_σ₀
  obtain ⟨x, hx⟩ := (GlobalTheory.frames_isConnected _ _ ((uAt r v i).X k)).nonempty
  obtain ⟨hy₁, t₁, f₁⟩ := hp₁ x hx
  obtain ⟨hy₂, t₂, f₂⟩ := hp₂ x hx
  obtain ⟨-, htr, hsy, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid D.host.E _ _ _
    ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (CAt (r.used v).full.σ₀)
  have hb := htr _ _ _ _ _ f₂ (hsy _ _ _ f₁)
  obtain ⟨γ', -, b, -, hσ⟩ := (hU.2.2.2.1 k₂ k₁ _ _).1 ⟨_, hb⟩
  have hk : k₁ = k₂ := (Sigma.mk.inj_iff.1 hσ).1
  subst hk
  refine ⟨rfl, ?_⟩
  obtain ⟨Xx, ⟨e1, e2, e3⟩, -⟩ := GlobalTheory.ModelLatticeCheck.holds_by_value D (r.used v).full.toCore
    (h.laws v).p.toLawsCore ((i : ℕ) + 1) hj (r.used v).full.σ₀ (r.used v).full.toCore.good_σ₀ k₁
  have eL : Xx.L' = lattice₂ D ((uAt r v i).X k₁).Λ := by
    rw [GlobalTheory.ModelLatExamples.eq_latP D Xx.Λ Xx.L' e3]
    show lattice₂ D Xx.toData.Λ = _
    rw [e1]
  have hGm : Xx.Gm = ((uAt r v i).X k₁).Gm := congrArg Data.Gm e1
  have hΛ : Xx.Λ = ((uAt r v i).X k₁).Λ := congrArg Data.Λ e1
  have hΓ : Xx.Γ = ((uAt r v i).X k₁).Γ := congrArg Data.Γ e1
  have hεm : ((a₁ * a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) =
      (a₁ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * ((a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix _ _ _) :=
    Matrix.GeneralLinearGroup.coe_mul _ _
  have ha₂ : (a₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * ((a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix _ _ _) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hiso : ∀ u w, herm ((uAt r v i).X k₁).Gm
      (((a₁ * a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ u)
      (((a₁ * a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ w) =
      herm ((uAt r v i).X k₁).Gm u w := by
    intro u w
    rw [hεm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hm₁.iso, ← hm₂.iso, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ha₂, Matrix.one_mulVec, Matrix.one_mulVec]
  have hlatΛ : ∀ w, w ∈ ((uAt r v i).X k₁).Λ ↔
      ((a₁ * a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ w ∈
        ((uAt r v i).X k₁).Λ := by
    intro w
    rw [hεm, ← Matrix.mulVec_mulVec, ← hm₁.lat]
    have := hm₂.lat (((a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix _ _ _) *ᵥ w)
    rw [Matrix.mulVec_mulVec, ha₂, Matrix.one_mulVec] at this
    exact this.symm
  have hlatL := mem_localLattice_iff_mulVec D _ hlatΛ
  have hcong : ∀ w ∈ lattice₂ D ((uAt r v i).X k₁).Λ,
      ((a₁ * a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ w - w ∈
        p.T.Q.l.Mb • lattice₂ D ((uAt r v i).X k₁).Λ := by
    intro w hw
    have ew : (a₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ
        (((a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix _ _ _) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ha₂, Matrix.one_mulVec]
    have hu : ((a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix _ _ _) *ᵥ w ∈ lattice₂ D ((uAt r v i).X k).Λ :=
      (mem_localLattice_iff_mulVec D _ hm₂.lat _).2 (ew.symm ▸ hw)
    obtain ⟨hw₁, q₁⟩ := hq₁ ⟨_, hu⟩
    obtain ⟨hw₂, q₂⟩ := hq₂ ⟨_, hu⟩
    have hq := q₁.trans q₂.symm
    rw [Submodule.Quotient.eq] at hq
    have hmem := Submodule.mem_map_of_mem (f := (lattice₂ D ((uAt r v i).X k₁).Λ).subtype) hq
    rw [Submodule.map_smul'', Submodule.map_subtype_top] at hmem
    have e : ((a₁ * a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ w - w =
        (a₁ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ (((a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix _ _ _) *ᵥ w) -
          (a₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ (((a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix _ _ _) *ᵥ w) := by
      rw [ew, hεm, Matrix.mulVec_mulVec]
    rw [e]
    simpa using hmem
  have hM := sub_mem_natSMul_of_unitary Xx.Gm Xx.L' Xx.L'_int Xx.L'_dual p.T.Q.H.bar (fun a => p.T.Q.H.bar_eq a)
    p.T.Q.l.Mb p.T.Q.l.M (by have := p.T.Q.l.three_le; omega) p.T.Q.l.prod p.T.Q.l.coprime (a₁ * a₂⁻¹)
    (by rw [hGm]; exact hiso) (by rw [eL]; exact hlatL) (by rw [eL]; exact hcong)
  have hMΛ := sub_mem_natSMul_span D.host.AA Xx.L' Xx.Λ e3 _ p.T.Q.l.M hM
  have hin := Xx.cong (a₁ * a₂⁻¹) ⟨by rw [hGm]; exact hiso, by rw [hΛ]; exact hlatΛ⟩ (by rw [e2]; exact hMΛ)
  rw [← hΓ]
  exact hin

end GlobalTheory.ShareOn

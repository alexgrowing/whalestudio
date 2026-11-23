import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.ConeLawAB

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem units_sum {K : Type} [Field K] {a : K → ℂ} (ha : Summable a) : ∑' ξ : Kˣ, a ξ = ∑' x, a x - a 0 := by
  have h1 := ha.tsum_subtype_add_tsum_subtype_compl {0}
  rw [tsum_singleton] at h1
  rw [← h1, add_sub_cancel_left]
  exact (unitsEquivNeZero (G₀ := K)).tsum_eq fun x => a x.1

theorem orbit_sum {Γ I : Type} [Group Γ] [MulAction Γ I] (hfree : ∀ (ξ η : Γ) (x : I), ξ • x = η • x → ξ = η) {f : I → ℂ}
    (hf : Summable f) : ∑' x, f x = ∑' q : MulAction.orbitRel.Quotient Γ I, ∑' ξ : Γ, f (ξ • q.out) := by
  have hb : Function.Bijective fun y : MulAction.orbitRel.Quotient Γ I × Γ => y.2 • y.1.out := by
    constructor
    · rintro ⟨q, ξ⟩ ⟨q', η⟩ h
      dsimp only at h
      have : q = q' := by
        rw [← q.out_eq, ← q'.out_eq]
        exact Quotient.sound ⟨ξ⁻¹ * η, by dsimp only; rw [mul_smul, ← h, inv_smul_smul]⟩
      subst this
      rw [hfree _ _ _ h]
    · intro x
      obtain ⟨ξ, hξ⟩ : (Quotient.mk (MulAction.orbitRel Γ I) x).out ∈ MulAction.orbit Γ x := Quotient.mk_out (s := MulAction.orbitRel Γ I) x
      exact ⟨(Quotient.mk _ x, ξ⁻¹), by dsimp only at hξ ⊢; rw [← hξ, inv_smul_smul]⟩
  rw [← (Equiv.ofBijective _ hb).tsum_eq]
  exact ((Equiv.ofBijective _ hb).summable_iff.2 hf).tsum_prod

section

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

theorem form_smul (J : Matrix (Fin n) (Fin n) E) (c : E) (x : Fin n → E) : form σ J (c • x) (c • x) = c * σ c * form σ J x x := by
  simp only [form, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

instance isoAct : MulAction Eˣ (IsoV σ X) where
  smul ξ x := ⟨(ξ : E) • x.1, smul_ne_zero ξ.ne_zero x.2.1, by rw [form_smul, x.2.2, mul_zero]⟩
  one_smul x := Subtype.ext (one_smul E x.1)
  mul_smul a b x := Subtype.ext (mul_smul (a : E) (b : E) x.1)

theorem isoAct_val (ξ : Eˣ) (x : IsoV σ X) : (ξ • x).1 = (ξ : E) • x.1 := rfl

theorem isoAct_free (ξ η : Eˣ) (x : IsoV σ X) (h : ξ • x = η • x) : ξ = η :=
  Units.ext (smul_left_injective E x.2.1 (congrArg Subtype.val h))

def conjE (hσ : IsCMExt F E σ) : Eˣ ≃ Eˣ where
  toFun := Units.map (σ : E →* E)
  invFun := Units.map (σ : E →* E)
  left_inv x := Units.ext (cm_conj_conj hσ x.1)
  right_inv x := Units.ext (cm_conj_conj hσ x.1)

abbrev idl (ξ : Eˣ) : (AE F E)ˣ := Units.map (inclR (F := F) (AF F)).toMonoidHom ξ

theorem incV_smul (c : E) (x : Fin n → E) : incV F (c • x) = inclR (F := F) (AF F) c • incV F x := by
  funext i
  simp [incV]

theorem incM_smul (c : E) (x : Matrix (Fin n) (Fin d) E) : incM F (c • x) = inclR (F := F) (AF F) c • incM F x := by
  ext i j
  simp [incM]

variable {B : Base F E} {M : Model σ X W} {om : Rep σ X W} {M₀ : Model σ X₁ W₁} {om₀ : Rep σ X₁ W₁} {H : Plane E n n₁}
  {H' : Plane E d d₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {u : (AE F E)ˣ → Ten F E n d} {ν χ : Chr F E} {z : ℕ}
  {ι : (AE F E)ˣ → (AE F E)ˣ} {w : (AE F E)ˣ → ℂ} {χX χW : Chr F E} {r s r' s' r₀ s₀ r₀' s₀' : ℕ}

theorem LawsT.mult (h : LawsT B M om om₀ H H' e u w ι) (hD : StabDec) (hU : UnipEx) (hTB : ThetaBasic)
    (hp : IsPair B M χX χW om r s r' s') (hp₀ : IsPair B M₀ χX χW om₀ r₀ s₀ r₀' s₀') {j₀ j₁} (hH : H.IsAdapted σ B X X₁ j₀ j₁)
    (hs : ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (u 1) Ψ) ∈ schA F (Fin n₁ × Fin d₁)) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    {γ} (hγ : Moves (σ := σ) (X := X) H γ) (y g) (x : IsoV σ X) (ξ η : Eˣ) (hη : ι (idl η) = idl ξ⁻¹) (hν : w (idl η) = 1) :
    thv B M om e (u 1) Φ y (γ (ξ • x) * g) = thetaSum F (e (M.co.rho B.ψ (u (idl η)) (om (γ x * g, y) Φ))) := by
  obtain ⟨-, -, -, -, ⟨lev, -, hlev, -⟩, -⟩ := hU F E σ B n n₁ X X₁ H j₀ j₁ r s hp.base (Or.inl hp.herm) hH
  have hl := hlev (idl ξ⁻¹) 1
  have hr := (hD F E σ B n n₁ X X₁ H j₀ j₁ r s hp.base (Or.inl hp.herm) hH).2.1 ξ⁻¹ 1 (one_mem _) _ hl
  set p := lev (idl ξ⁻¹, 1)
  have h1 : mat (p * γ x) *ᵥ incV F (ξ • x).1 = incV F H.x := by
    rw [mat_mul', ← Matrix.mulVec_mulVec, isoAct_val, incV_smul, Matrix.mulVec_smul, (hγ x).2, Matrix.mulVec_smul, hl.1, smul_smul]
    simp [← map_mul]
  have h2 := h.rat hD hTB hp hp₀ hH hs hΦ y (δ := γ (ξ • x) * (p * γ x)⁻¹)
    (mul_mem (hγ _).1 (inv_mem (mul_mem hr (hγ x).1)))
    (by rw [mat_mul', ← Matrix.mulVec_mulVec, mat_inv_mulVec _ h1, (hγ _).2]) (p * γ x * g)
  rw [show γ (ξ • x) * (p * γ x)⁻¹ * (p * γ x * g) = γ (ξ • x) * g by group] at h2
  have h3 := h.theta (l := idl η) (by rwa [hη]) (levi_one (W₁ := W₁) H') (pair_pres hp (γ x * g, y) hΦ)
  rw [hη, hν, GlobalTheory.Doubling.absE_inclR] at h3
  rw [h2]
  simpa [thv, om_mul, mul_assoc, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, ← Prod.one_eq_mk] using h3

end

end PositivityTheory.ThKCT

end

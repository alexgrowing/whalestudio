import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.NormalOfCenter
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.GlobNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.EmbAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.GqS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IotaEx

namespace UpperTheory.V.Z.Sym.Glob

open NumberField Loc

private theorem aux_statement_10 {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (hD : D.Ok) (t : Dat.Par F)
    (ht : D.Cone t) (τ : F) (h : D.admitted t τ) : τ ^ 2 - 4 ≠ 0 := by
  intro h0
  obtain ⟨v, hv⟩ := hD.ne
  refine ((hD.sig v hv).reg (t v) (ht v hv) _ (h v hv)).2 ?_
  have h2 : IsIntegral (Ov v) (2 : Kv v) := by
    have := isIntegral_algebraMap (R := Ov v) (A := Kv v) (x := 2)
    rwa [map_ofNat] at this
  have h1 : (τ - 2) * (τ + 2) = 0 := by rw [← h0]; ring
  rcases mul_eq_zero.mp h1 with h1 | h1
  · rw [sub_eq_zero.mp h1, map_ofNat]; exact h2
  · rw [eq_neg_of_add_eq_zero_left h1, map_neg, map_ofNat]; exact h2.neg

private theorem sum_sub {α : Type} (p : α → Prop) (f : α → ℂ) (c : ℂ) :
    ∑ᶠ i : {a // p a}, c * f i.1 = c * ∑ᶠ a, one (p a) * f a := by
  classical
  have h1 : ∑ᶠ i : {a // p a}, c * f i.1 = ∑ᶠ (a) (_ : p a), c * f a :=
    finsum_subtype_eq_finsum_cond (f := fun a => c * f a) p
  rw [h1]
  have h2 : ∀ a, ∑ᶠ (_ : p a), c * f a = c • (one (p a) * f a) := by
    intro a
    rw [finsum_eq_if, smul_eq_mul]
    unfold one
    split_ifs <;> simp
  simp_rw [h2]
  rw [← smul_finsum, smul_eq_mul]

set_option maxHeartbeats 1600000 in
theorem split_side_identity_unitary : QuaternionStableSideTraceIdentity := by
  intro F _ _ Δ D hD x₀ hx₀
  obtain ⟨-, ⟨ι, hι⟩, -⟩ := iotaEx F Δ
  obtain ⟨n, x, c, hx0, hoff, hc, hsum⟩ := fibre F Δ D hD ι hι x₀ hx₀
  have hΔ : Δ ≠ 0 := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    obtain ⟨σ⟩ : Nonempty (F →+* ℝ) := ⟨InfinitePlace.embedding_of_isReal (hD.real.isReal w)⟩
    have hneg : σ Δ < 0 := hD.neg σ
    intro h0
    rw [h0, map_zero] at hneg
    exact lt_irrefl _ hneg
  refine ⟨n, x, c * ∏ v ∈ D.Sg, (D.S v).cS, hx0, hoff, ?_, ?_⟩
  · exact mul_pos hc (Finset.prod_pos fun v hv => (hD.sig v hv).cS)
  · intro V _ _ _ ch B hB t ht
    classical
    have hG : ∀ a, D.Good t a ↔ IsCM a ∧ D.admitted t a := fun a => Iff.rfl
    have hex : ∀ s : {a // D.Good t a}, ∃ g : DX Δ, HasTr g s.1 :=
      fun s => (embEx F Δ D hD s.1).1 ((hG _).1 s.2).1
    choose γ hγ using hex
    have hreg : ∀ s : {a // D.Good t a}, s.1 ^ 2 - 4 ≠ 0 :=
      fun s => aux_statement_10 D hD t ht s.1 ((hG _).1 s.2).2
    have hj : ∀ s : {a // D.Good t a}, ∃ j : (Etau F s.1)ˣ →* DX Δ, IsEmb s.1 (γ s) j :=
      fun s => (embAlg F Δ s.1 hΔ (hreg s) (γ s) (hγ s)).1
    choose j hjj using hj
    rw [hsum V ch B hB t ht {a // D.Good t a} (fun s => s.1) γ j Subtype.val_injective
      (fun s => ⟨hreg s, hγ s, hjj s⟩) ?_]
    · have hterm : ∀ s : {a // D.Good t a},
          ch s.1 * gqOn (ι.comp (j s)) (scalE s.1) D.UZ
            (fun y => D.FS t ((Quotient.out y)⁻¹ * ι (γ s) * Quotient.out y)) =
            (∏ v ∈ D.Sg, ((D.S v).cS : ℂ)) * (ch s.1 * ms s.1 * D.nS s.1) := by
        intro s
        rw [gqS F Δ D hD ι hι t ht s.1 ((hG _).1 s.2).1 (γ s) (j s) (hγ s) (hjj s)]
        have h1 : one (D.admitted t s.1) = 1 := if_pos ((hG _).1 s.2).2
        rw [h1]
        ring
      rw [finsum_congr hterm, sum_sub (fun a => D.Good t a) (fun a => ch a * ms a * D.nS a)]
      unfold Dat.sumS
      push_cast
      ring
    · intro g s hg hs
      exact ⟨⟨s, (hG s).2 ⟨(embEx F Δ D hD s).2 g hg (aux_statement_10 D hD t ht s hs), hs⟩⟩, rfl⟩

end UpperTheory.V.Z.Sym.Glob

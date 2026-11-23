import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryHyperbolicOrbitCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts

noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig

namespace UpperTheory.V.Z.Sym.Sig

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem dc_mul (V : Lev k) {d : Fin 3 → kˣ} {u v g : GL (Fin 3) k} (hu : u ∈ V.J 3) (hv : v ∈ V.J 3)
    (h : g ∈ V.DC d) : u * g * v ∈ V.DC d := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact ⟨u * a, (V.J 3).mul_mem hu ha, b * v, (V.J 3).mul_mem hb hv, by group⟩

private theorem dc_iff (V : Lev k) {d : Fin 3 → kˣ} {u v : GL (Fin 3) k} (hu : u ∈ V.J 3) (hv : v ∈ V.J 3)
    (g : GL (Fin 3) k) : u * g * v ∈ V.DC d ↔ g ∈ V.DC d := by
  constructor
  · intro h
    have h2 := dc_mul V ((V.J 3).inv_mem hu) ((V.J 3).inv_mem hv) h
    simpa [mul_assoc] using h2
  · exact dc_mul V hu hv

private theorem gl3_spherical_bi_invariant (V : Lev k) (d : Fin 3 → kˣ) {u u' : GL (Fin 3) k} (hu : u ∈ V.J 3) (hu' : u' ∈ V.J 3)
    (g : GL (Fin 3) k) : V.unitaryDoubleCosetIndicator d (u * g * th k 3 u') = V.unitaryDoubleCosetIndicator d g := by
  have hF := thFacts k V
  have key : u * g * th k 3 u' * (Phi k)⁻¹ = u * (g * (Phi k)⁻¹) * th' k u' := by
    have h7 := hF.2.2.2.2.2.2 u'
    have : th k 3 u' = (Phi k)⁻¹ * th' k u' * Phi k := by
      rw [mul_assoc, h7]
      group
    rw [this]
    group
  simp only [Lev.unitaryDoubleCosetIndicator]
  rw [key, dc_iff V hu (hF.2.1 u' hu')]

private theorem gl3_spherical_finite_support (V : Lev k) (d : Fin 3 → kˣ) :
    {y : GL (Fin 3) k ⧸ (V.J 3).map (th k 3) | V.unitaryDoubleCosetIndicator d y.out ≠ 0}.Finite := by
  have hF := thFacts k V
  have hJ := (finFacts k V).2.2.2.2.2 3
  have horb : (MulAction.orbit (V.J 3) ((dg d : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3)).Finite := hJ.1 (dg d)
  let F : GL (Fin 3) k ⧸ (V.J 3).map (th k 3) → GL (Fin 3) k ⧸ V.J 3 :=
    fun y => ((Quotient.out y * (Phi k)⁻¹ : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3)
  refine Set.Finite.of_finite_image (f := F) (horb.subset ?_) ?_
  · rintro _ ⟨y, hy, rfl⟩
    simp only [Set.mem_setOf_eq, Lev.unitaryDoubleCosetIndicator] at hy
    have hy' : Quotient.out y * (Phi k)⁻¹ ∈ V.DC d := by
      by_contra hc
      rw [if_neg hc] at hy
      exact hy rfl
    obtain ⟨a, ha, b, hb, hab⟩ := hy'
    refine ⟨⟨a, ha⟩, ?_⟩
    show ((a * dg d : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) = F y
    simp only [F]
    rw [hab, QuotientGroup.eq]
    simpa [mul_assoc] using hb
  · intro y1 _ y2 _ h
    simp only [F] at h
    rw [QuotientGroup.eq] at h
    rw [← QuotientGroup.out_eq' y1, ← QuotientGroup.out_eq' y2, QuotientGroup.eq]
    set w := Phi k * ((Quotient.out y1)⁻¹ * Quotient.out y2) * (Phi k)⁻¹ with hw
    refine ⟨th' k w, hF.2.1 w ?_, ?_⟩
    · convert h using 1
      rw [hw]
      group
    · have h7 := hF.2.2.2.2.2.2 (th' k w)
      rw [Pres.invol hF.1 w] at h7
      have : th k 3 (th' k w) = (Phi k)⁻¹ * (w * Phi k) := by
        rw [h7]
        group
      rw [this, hw]
      group

end UpperTheory.V.Z.Sym.Sig

theorem UpperTheory.V.Z.Sym.Sig.eqG :
    UpperTheory.V.Z.Sym.Sig.EqG := by
  intro k _ _ _ _ V ω Rs Ry x z d
  refine ⟨fun u hu u' hu' g => ⟨gl3_spherical_bi_invariant V d hu hu' g, ?_⟩, gl3_spherical_finite_support V d, ?_⟩
  · simp only [Lev.fG, gl3_spherical_bi_invariant V _ hu hu' g]
  · refine (Set.Finite.biUnion Rs.finite_toSet fun e _ =>
      Set.Finite.biUnion Ry.finite_toSet fun y _ => gl3_spherical_finite_support V ![x * e, y, z]).subset ?_
    intro q hq
    have hq' : ∑ e ∈ Rs, ∑ y ∈ Ry, (ω e : ℂ) * V.unitaryDoubleCosetIndicator ![x * e, y, z] q.out ≠ 0 := hq
    obtain ⟨e, he, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq'
    obtain ⟨y, hy, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact Set.mem_biUnion he (Set.mem_biUnion hy (right_ne_zero_of_mul h))

end

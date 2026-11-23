import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.UnitaryHyperbolicOrbitCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.UnitaryDoubleCosetIndicator
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

section
open MulAction

variable {T G : Type} [Group T] [Group G]

private def OrbSupp (ι : T →* G) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ : G) : Prop :=
  letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι
  {o : orbitRel.Quotient T (G ⧸ U) | f (o.out.out⁻¹ * δ * θ o.out.out) ≠ 0}.Finite

private theorem orb_sum {I : Type} (ι : T →* G) (C : Subgroup T) (θ : G →* G) (U : Subgroup G) (δ : G)
    (S : Finset I) (f : I → G → ℂ) (h : ∀ i ∈ S, OrbSupp ι θ U (f i) δ) :
    orb ι C θ U (fun g => ∑ i ∈ S, f i g) δ = ∑ i ∈ S, orb ι C θ U (f i) δ := by
  letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι
  unfold orb wcount
  simp only [Finset.mul_sum]
  rw [finsum_sum_comm]
  intro i hi
  refine (h i hi).subset ?_
  intro o ho
  simp only [Function.mem_support] at ho
  exact right_ne_zero_of_mul ho

private theorem finOrb_of (ι : T →* G) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ : G)
    (hf : ∀ u ∈ U, ∀ x, f (u⁻¹ * x * θ u) = f x) (hδ : ∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ)
    (h : OrbSupp ι θ U f δ) : FinOrb ι θ U f δ := by
  letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι
  classical
  have h' : {o : orbitRel.Quotient T (G ⧸ U) | f (o.out.out⁻¹ * δ * θ o.out.out) ≠ 0}.Finite := h
  refine ⟨h'.toFinset.image (fun o => o.out.out), ?_⟩
  intro y hy
  let o : orbitRel.Quotient T (G ⧸ U) := Quotient.mk _ (QuotientGroup.mk y : G ⧸ U)
  obtain ⟨t, ht⟩ : ∃ t : T, t • (QuotientGroup.mk y : G ⧸ U) = o.out :=
    Quotient.exact (Quotient.out_eq o)
  have hs : (QuotientGroup.mk (o.out.out) : G ⧸ U) = QuotientGroup.mk (ι t * y) := by
    rw [QuotientGroup.out_eq', ← ht]
    rfl
  have hu := QuotientGroup.eq.mp hs.symm
  set s := o.out.out with hsdef
  set u := (ι t * y)⁻¹ * s with hudef
  have hs' : s = ι t * y * u := by rw [hudef]; group
  refine ⟨t⁻¹, s, ?_, u⁻¹, U.inv_mem hu, ?_⟩
  · refine Finset.mem_image.mpr ⟨o, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    show f (s⁻¹ * δ * θ s) ≠ 0
    have e : s⁻¹ * δ * θ s = u⁻¹ * (y⁻¹ * δ * θ y) * θ u := by
      rw [hs', map_mul, map_mul]
      calc (ι t * y * u)⁻¹ * δ * (θ (ι t) * θ y * θ u)
          = u⁻¹ * (y⁻¹ * ((ι t)⁻¹ * δ * θ (ι t)) * θ y) * θ u := by group
        _ = _ := by rw [hδ]
    rw [e, hf u hu]
    exact hy
  · rw [hs', map_inv]
    group

private theorem finOrb_sum {I : Type} (ι : T →* G) (θ : G →* G) (U : Subgroup G) (δ : G)
    (S : Finset I) (f : I → G → ℂ) (hf : ∀ i ∈ S, ∀ u ∈ U, ∀ x, f i (u⁻¹ * x * θ u) = f i x)
    (hδ : ∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ) (h : ∀ i ∈ S, OrbSupp ι θ U (f i) δ) :
    FinOrb ι θ U (fun g => ∑ i ∈ S, f i g) δ := by
  refine finOrb_of ι θ U _ δ ?_ hδ ?_
  · intro u hu x
    exact Finset.sum_congr rfl fun i hi => hf i hi u hu x
  · letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι
    change {o : orbitRel.Quotient T (G ⧸ U) | (∑ i ∈ S, f i (o.out.out⁻¹ * δ * θ o.out.out)) ≠ 0}.Finite
    have hU : (⋃ i ∈ (S : Set I),
        {o : orbitRel.Quotient T (G ⧸ U) | f i (o.out.out⁻¹ * δ * θ o.out.out) ≠ 0}).Finite :=
      Set.Finite.biUnion S.finite_toSet fun i hi => h i hi
    refine hU.subset ?_
    intro o ho
    simp only [Set.mem_setOf_eq] at ho
    obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero ho
    exact Set.mem_biUnion (Finset.mem_coe.mpr hi) hne

end

theorem UpperTheory.V.Z.Sym.Sig.orbital_integral_over_extended_group :
    UpperTheory.V.Z.Sym.Sig.TwistedOrbitalIntegralGL3Formula := by
  intro k _ _ _ _ V Ry hR t ht T _ r hr g₀ ι hι x y z hxz
  set θ := th k 3 with hθ
  set δ := g₀ * dg ![x, y, z] * Phi k * (θ g₀)⁻¹ with hδdef
  obtain ⟨_, _, hth'dg, _, _, _, hth'Φ⟩ := thFacts k V
  have hδ : ∀ s, (ι s)⁻¹ * δ * θ (ι s) = δ := by
    intro s
    have hΦ : Phi k * θ (dg ![r s, 1, (r s)⁻¹]) = dg ![r s, 1, (r s)⁻¹] * Phi k := by
      rw [← hth'Φ, hth'dg, inv_inv, inv_one]
    have hc : dg ![x, y, z] * dg ![r s, 1, (r s)⁻¹] = dg ![r s, 1, (r s)⁻¹] * dg ![x, y, z] := by
      simp only [dg]
      rw [← map_mul, ← map_mul, mul_comm]
    rw [hι s, map_mul, map_mul, map_inv]
    calc (g₀ * dg ![r s, 1, (r s)⁻¹] * g₀⁻¹)⁻¹ * δ * (θ g₀ * θ (dg ![r s, 1, (r s)⁻¹]) * (θ g₀)⁻¹)
        = g₀ * (dg ![r s, 1, (r s)⁻¹])⁻¹ * dg ![x, y, z] * (Phi k * θ (dg ![r s, 1, (r s)⁻¹])) *
            (θ g₀)⁻¹ := by
          rw [hδdef]; group
      _ = g₀ * (dg ![r s, 1, (r s)⁻¹])⁻¹ * (dg ![x, y, z] * dg ![r s, 1, (r s)⁻¹]) * Phi k *
            (θ g₀)⁻¹ := by
          rw [hΦ]; group
      _ = δ := by rw [hc, hδdef]; group
  set ϖ := unif k with hϖ
  let d : kˣ → Fin 3 → kˣ := fun a => ![t * ϖ⁻¹, a, ϖ⁻¹]
  have hw1 : valuation k (ϖ : k) < 1 := by
    rw [hϖ, GlAx.unif_spec]
    exact uniformizer_lt_one
  have hw0 : 0 < valuation k (ϖ : k) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr ϖ.ne_zero
  have hSD : ∀ a ∈ Ry, SDom (d a) := by
    intro a ha i j hij
    obtain ⟨hal, hau⟩ := hR.1 a ha
    have htw : valuation k (t : k) * (valuation k (ϖ : k))⁻¹ < valuation k (ϖ : k) := by
      rw [mul_inv_lt_iff₀ hw0]
      simpa [pow_two, hϖ] using ht
    have ht1 : valuation k (t : k) * (valuation k (ϖ : k))⁻¹ < 1 := htw.trans hw1
    have hinv : 1 < (valuation k (ϖ : k))⁻¹ := (one_lt_inv₀ hw0).mpr hw1
    fin_cases i <;> fin_cases j <;> simp at hij <;>
      simp [d, map_mul, map_inv₀, Units.val_inv_eq_inv_val]
    · exact htw.trans_le hal
    · exact ht1.trans hinv
    · exact hau.trans_lt hinv
  have hinvar : ∀ a ∈ Ry, ∀ u ∈ V.J 3, ∀ g, V.unitaryDoubleCosetIndicator (d a) (u⁻¹ * g * θ u) = V.unitaryDoubleCosetIndicator (d a) g := by
    intro a _ u hu g
    exact ((eqG k V 1 Ry Ry x z (d a)).1 u⁻¹ ((V.J 3).inv_mem hu) u hu g).1
  have h0 := fun a (ha : a ∈ Ry) => orbital_integral_over_base_group k V T r hr g₀ ι hι (d a) (hSD a ha) x y z hxz
  have hfun : V.unitaryHeckeTestSum Ry t = fun g => ∑ a ∈ Ry, V.unitaryDoubleCosetIndicator (d a) g := rfl
  rw [hfun]
  refine ⟨finOrb_sum ι θ (V.J 3) δ Ry (fun a => V.unitaryDoubleCosetIndicator (d a)) hinvar hδ (fun a ha => (h0 a ha).1), ?_⟩
  rw [orb_sum ι _ θ (V.J 3) δ Ry (fun a => V.unitaryDoubleCosetIndicator (d a)) (fun a ha => (h0 a ha).1)]
  rw [Finset.sum_congr rfl fun a ha => (h0 a ha).2]
  obtain ⟨a₀, ⟨ha₀, hq₀⟩, huniq⟩ := hR.2 y
  rw [Finset.sum_eq_single a₀]
  · have e : (d a₀) 0 / (d a₀) 2 = t := by simp [d]
    rw [e]
    unfold Glob.one
    by_cases hP : x / z / t ∈ V.H
    · rw [if_pos ⟨hP, hq₀⟩, if_pos hP, mul_one]
    · rw [if_neg (fun hh => hP hh.1), if_neg hP, mul_zero]
  · intro b hb hne
    rw [if_neg]
    rintro ⟨_, hq⟩
    exact hne (huniq b ⟨hb, hq⟩)
  · intro hn
    exact absurd ha₀ hn

end

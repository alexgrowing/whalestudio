import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryHyperbolicOrbitCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FixG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.BdMul

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig

namespace UpperTheory.V.Z.Sym.Sig

open MulAction

private theorem wcount_of {T Y A : Type} [Group T] [MulAction T Y] [Finite A] (C : Subgroup T) (f : Y → ℂ) (n : ℕ)
    (Ψ : A → orbitRel.Quotient T Y) (inj : Function.Injective Ψ)
    (hr : ∀ o : orbitRel.Quotient T Y, f o.out ≠ 0 ↔ o ∈ Set.range Ψ)
    (h1 : ∀ o : orbitRel.Quotient T Y, f o.out ≠ 0 → f o.out = 1 ∧ (stabilizer T o.out).relIndex C = n) :
    {o : orbitRel.Quotient T Y | f o.out ≠ 0}.Finite ∧ wcount C f = (n : ℂ) * (Nat.card A : ℂ) := by
  classical
  have hs : {o : orbitRel.Quotient T Y | f o.out ≠ 0} = Set.range Ψ := Set.ext fun o => hr o
  have : Fintype A := Fintype.ofFinite A
  refine ⟨hs ▸ Set.finite_range Ψ, ?_⟩
  unfold wcount
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.image Ψ)]
  · rw [Finset.sum_image (fun a _ b _ h => inj h)]
    have key : ∀ a, ((stabilizer T (Ψ a).out).relIndex C : ℂ) * f (Ψ a).out = n := by
      intro a
      have ha : f (Ψ a).out ≠ 0 := (hr _).2 ⟨a, rfl⟩
      obtain ⟨h1a, h2a⟩ := h1 _ ha
      rw [h1a, h2a, mul_one]
    simp only [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    ring
  · intro o ho
    have hne : f o.out ≠ 0 := fun h => ho (by simp [h])
    obtain ⟨a, rfl⟩ := (hr o).1 hne
    simp

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem dg_mem (V : Lev k) (w : Fin 3 → kˣ) : dg w ∈ V.J 3 ↔ ∀ i, w i ∈ V.H := by
  refine ⟨fun h i => ?_, V.dg_mem⟩
  obtain ⟨u, hu, he⟩ := ((memJ k V 3 (dg w)).1 h).2.2 i
  have hu' : u = w i := Units.ext (by rw [he]; simp [dg, val_diagT])
  exact hu' ▸ hu

private theorem mk_eq (V : Lev k) (g₀ : GL (Fin 3) k) (u u' : Fin 3 → kˣ) :
    ((g₀ * dg u : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) = ((g₀ * dg u' : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) ↔
      ∀ i, (u i)⁻¹ * u' i ∈ V.H := by
  rw [QuotientGroup.eq, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left, ← map_inv, ← map_mul]
  exact (dg_mem V _).trans (by simp [Pi.mul_apply, Pi.inv_apply])

private def Cd (V : Lev k) (d : Fin 3 → kˣ) (x y z : kˣ) (u : Fin 3 → kˣ) : Prop :=
  x / (u 0 * u 2) / d 0 ∈ V.H ∧ y / u 1 ^ 2 / d 1 ∈ V.H ∧ z / (u 0 * u 2) / d 2 ∈ V.H

private theorem supp_iff (V : Lev k) (d : Fin 3 → kˣ) (hd : SDom d) (x y z : kˣ) (hv : valuation k ((x / z : kˣ) : k) < 1)
    (g₀ w : GL (Fin 3) k) :
    V.unitaryDoubleCosetIndicator d (w⁻¹ * (g₀ * dg ![x, y, z] * Phi k * (th k 3 g₀)⁻¹) * th k 3 w) ≠ 0 ↔
      ∃ u, (w : GL (Fin 3) k ⧸ V.J 3) = ((g₀ * dg u : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) ∧ Cd V d x y z u := by
  have hf : ∀ g, V.unitaryDoubleCosetIndicator d g ≠ 0 ↔ g * (Phi k)⁻¹ ∈ V.DC d := by
    intro g
    unfold Lev.unitaryDoubleCosetIndicator
    split_ifs <;> simp_all
  have hM : w⁻¹ * (g₀ * dg ![x, y, z] * Phi k * (th k 3 g₀)⁻¹) * th k 3 w =
      (g₀⁻¹ * w)⁻¹ * (dg ![x, y, z] * Phi k) * th k 3 (g₀⁻¹ * w) := by
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]
  rw [hf, hM, fixG k V d hd x y z hv]
  constructor
  · rintro ⟨u, j, hj, he, h1, h2, h3⟩
    refine ⟨u, ?_, h1, h2, h3⟩
    have hj' : (g₀ * dg u)⁻¹ * w = j := by
      rw [_root_.mul_inv_rev, mul_assoc, he, inv_mul_cancel_left]
    rw [QuotientGroup.eq]
    rw [← hj'] at hj
    have := inv_mem hj
    rw [_root_.mul_inv_rev, inv_inv] at this
    exact this
  · rintro ⟨u, hq, h1, h2, h3⟩
    rw [QuotientGroup.eq] at hq
    refine ⟨u, (g₀ * dg u)⁻¹ * w, ?_, ?_, h1, h2, h3⟩
    · have := inv_mem hq
      rw [_root_.mul_inv_rev, inv_inv] at this
      exact this
    · rw [_root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left]

end

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem gl3_spherical_value_one (V : Lev k) (d : Fin 3 → kˣ) (g : GL (Fin 3) k) (h : V.unitaryDoubleCosetIndicator d g ≠ 0) : V.unitaryDoubleCosetIndicator d g = 1 := by
  classical
  unfold Lev.unitaryDoubleCosetIndicator at h ⊢
  split_ifs at h ⊢ with h'
  · rfl
  · exact absurd rfl h

private theorem cd_act (V : Lev k) (d : Fin 3 → kˣ) (x y z a : kˣ) (u : Fin 3 → kˣ) (h : Cd V d x y z u) :
    Cd V d x y z (![a, 1, a⁻¹] * u) := by
  have e0 : (![a, 1, a⁻¹] * u) 0 * (![a, 1, a⁻¹] * u) 2 = u 0 * u 2 := by
    simp [Pi.mul_apply, mul_mul_mul_comm]
  have e1 : (![a, 1, a⁻¹] * u) 1 = u 1 := by simp [Pi.mul_apply]
  unfold Cd
  rw [e0, e1]
  exact h

end

theorem orbital_integral_over_base_group : UnitaryHyperbolicOrbitCount := by
  intro k _ _ _ _ V T _ r hr g₀ ι hι d hd x₁ y₁ z₁ hv
  letI : MulAction T (GL (Fin 3) k ⧸ V.J 3) := MulAction.compHom _ ι
  set δ := g₀ * dg ![x₁, y₁, z₁] * Phi k * (th k 3 g₀)⁻¹ with hδ
  have hF : ∀ q : GL (Fin 3) k ⧸ V.J 3, V.unitaryDoubleCosetIndicator d (q.out⁻¹ * δ * th k 3 q.out) ≠ 0 ↔
      ∃ u, q = ((g₀ * dg u : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) ∧ Cd V d x₁ y₁ z₁ u := by
    intro q
    have h := supp_iff V d hd x₁ y₁ z₁ hv g₀ q.out
    rw [QuotientGroup.out_eq'] at h
    exact h
  have hact : ∀ (s : T) (u : Fin 3 → kˣ), s • ((g₀ * dg u : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) =
      ((g₀ * dg (![r s, 1, (r s)⁻¹] * u) : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) := by
    intro s u
    show ((ι s * (g₀ * dg u) : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) = _
    rw [hι, show dg (![r s, 1, (r s)⁻¹] * u) = dg ![r s, 1, (r s)⁻¹] * dg u from map_mul _ _ _]
    simp only [mul_assoc, inv_mul_cancel_left]
  have hstab : ∀ u : Fin 3 → kˣ, stabilizer T ((g₀ * dg u : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) =
      Subgroup.comap r V.H := by
    intro u
    ext s
    rw [mem_stabilizer_iff, hact, mk_eq, Subgroup.mem_comap]
    have e : ∀ i, ((![r s, 1, (r s)⁻¹] * u) i)⁻¹ * u i = (![r s, 1, (r s)⁻¹] i)⁻¹ := by
      intro i
      simp only [Pi.mul_apply, mul_inv, inv_mul_cancel_right]
    constructor
    · intro h
      have h2 := h 2
      rw [e] at h2
      simpa using h2
    · intro h i
      rw [e]
      rcases (by decide : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2) i with rfl | rfl | rfl <;> simp [h]
  have FF := finFacts k V
  have hne : V.H.relIndex V.H2 ≠ 0 := by
    intro h0
    apply FF.1
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ FF.2.2.1 FF.2.1, h0, zero_mul]
  unfold orb
  by_cases hc : x₁ / z₁ / (d 0 / d 2) ∈ V.H ∧ ∃ s, y₁ / (d 1 * s ^ 2) ∈ V.H
  · rw [if_pos hc]
    obtain ⟨hxz, s0, hs0⟩ := hc
    haveI : (V.H.subgroupOf V.H2).FiniteIndex := ⟨hne⟩
    let U : ↥V.H2 → Fin 3 → kˣ := fun v => ![x₁ / d 0, s0 * (v : kˣ), 1]
    let q : ↥V.H2 → GL (Fin 3) k ⧸ V.J 3 := fun v => ((g₀ * dg (U v) : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3)
    let Ψ : ↥V.H2 ⧸ V.H.subgroupOf V.H2 → orbitRel.Quotient T (GL (Fin 3) k ⧸ V.J 3) :=
      Quotient.lift (s := QuotientGroup.leftRel (V.H.subgroupOf V.H2))
        (fun v => (Quotient.mk'' (q v) : orbitRel.Quotient T (GL (Fin 3) k ⧸ V.J 3))) (by
        intro a b hab
        have hab' : a⁻¹ * b ∈ V.H.subgroupOf V.H2 := QuotientGroup.leftRel_apply.mp hab
        rw [Subgroup.mem_subgroupOf] at hab'
        apply congrArg
        simp only [q]
        rw [mk_eq]
        intro i
        rcases (by decide : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2) i with rfl | rfl | rfl
        · convert one_mem V.H using 1
          ext
          simp [U] <;> field_simp
        · convert hab' using 1
          ext
          simp [U] <;> field_simp
        · convert one_mem V.H using 1
          ext
          simp [U])
    have hΨ : ∀ v : ↥V.H2, Ψ (v : ↥V.H2 ⧸ V.H.subgroupOf V.H2) =
        (Quotient.mk'' (q v) : orbitRel.Quotient T (GL (Fin 3) k ⧸ V.J 3)) := fun v => rfl
    have hinj : Function.Injective Ψ := by
      intro a b hab
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective b
      rw [hΨ, hΨ] at hab
      have hab' := Quotient.exact' hab
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab'
      obtain ⟨s, hs⟩ := hab'
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [q] at hs
      rw [hact, mk_eq] at hs
      have h1 := inv_mem (hs 1)
      convert h1 using 1
      ext
      simp [U, Pi.mul_apply] <;> field_simp
    have hrng : ∀ o : orbitRel.Quotient T (GL (Fin 3) k ⧸ V.J 3),
        V.unitaryDoubleCosetIndicator d (o.out.out⁻¹ * δ * th k 3 o.out.out) ≠ 0 ↔ o ∈ Set.range Ψ := by
      intro o
      rw [hF]
      constructor
      · rintro ⟨u, hu, h1, h2, h3⟩
        have hv2 : u 1 * s0⁻¹ ∈ V.H2 := by
          show (u 1 * s0⁻¹) ^ 2 ∈ V.H
          have e : (u 1 * s0⁻¹) ^ 2 = y₁ / (d 1 * s0 ^ 2) / (y₁ / u 1 ^ 2 / d 1) := by
            ext
            simp <;> field_simp
          rw [e]
          exact div_mem hs0 h2
        obtain ⟨s, hs⟩ := hr (u 2)
        refine ⟨((⟨u 1 * s0⁻¹, hv2⟩ : ↥V.H2) : ↥V.H2 ⧸ V.H.subgroupOf V.H2), ?_⟩
        rw [hΨ]
        refine (Quotient.sound' ?_).trans (Quotient.out_eq' o)
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
        refine ⟨s, ?_⟩
        rw [hu, hact, hs]
        simp only [q]
        rw [mk_eq]
        intro i
        rcases (by decide : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2) i with rfl | rfl | rfl
        · convert h1 using 1
          ext
          simp [U, Pi.mul_apply] <;> field_simp
        · convert one_mem V.H using 1
          ext
          simp [U, Pi.mul_apply] <;> field_simp
        · convert one_mem V.H using 1
          ext
          simp [U, Pi.mul_apply]
      · rintro ⟨a, rfl⟩
        obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective a
        rw [hΨ]
        have hm := Quotient.mk_out' (s₁ := orbitRel T (GL (Fin 3) k ⧸ V.J 3)) (q v)
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hm
        obtain ⟨s, hs⟩ := hm
        refine ⟨![r s, 1, (r s)⁻¹] * U v, hs.symm.trans (hact s (U v)), cd_act V d x₁ y₁ z₁ (r s) (U v) ?_⟩
        have hv2 : (v : kˣ) ^ 2 ∈ V.H := v.2
        refine ⟨?_, ?_, ?_⟩
        · convert one_mem V.H using 1
          ext
          simp [U] <;> field_simp
        · convert mul_mem hs0 (inv_mem hv2) using 1
          ext
          simp [U] <;> field_simp
        · convert inv_mem hxz using 1
          ext
          simp [U] <;> field_simp
    have hone : ∀ o : orbitRel.Quotient T (GL (Fin 3) k ⧸ V.J 3),
        V.unitaryDoubleCosetIndicator d (o.out.out⁻¹ * δ * th k 3 o.out.out) ≠ 0 →
          V.unitaryDoubleCosetIndicator d (o.out.out⁻¹ * δ * th k 3 o.out.out) = 1 ∧
            (stabilizer T o.out).relIndex (Subgroup.comap r (Uo k)) = V.H.relIndex (Uo k) := by
      intro o h
      refine ⟨gl3_spherical_value_one V d _ h, ?_⟩
      obtain ⟨u, hu, -⟩ := (hF _).1 h
      rw [hu, hstab, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hr]
    obtain ⟨hfin, hsum⟩ := wcount_of (C := Subgroup.comap r (Uo k))
      (f := fun q : GL (Fin 3) k ⧸ V.J 3 => V.unitaryDoubleCosetIndicator d (q.out⁻¹ * δ * th k 3 q.out))
      (n := V.H.relIndex (Uo k)) Ψ hinj hrng hone
    exact ⟨hfin, hsum.trans rfl⟩
  · rw [if_neg hc]
    have hzero : ∀ q : GL (Fin 3) k ⧸ V.J 3, V.unitaryDoubleCosetIndicator d (q.out⁻¹ * δ * th k 3 q.out) = 0 := by
      intro q
      by_contra h
      obtain ⟨u, -, h1, h2, h3⟩ := (hF q).1 h
      refine hc ⟨?_, u 1, ?_⟩
      · convert div_mem h1 h3 using 1
        ext
        simp <;> field_simp
      · convert h2 using 1
        ext
        simp <;> field_simp
    obtain ⟨hfin, hsum⟩ := wcount_of (A := Empty) (C := Subgroup.comap r (Uo k))
      (f := fun q : GL (Fin 3) k ⧸ V.J 3 => V.unitaryDoubleCosetIndicator d (q.out⁻¹ * δ * th k 3 q.out))
      (n := 0) (fun e => e.elim) (fun e => e.elim) (fun o => by simp [hzero])
      (fun o h => absurd (hzero _) h)
    exact ⟨hfin, hsum.trans (by simp)⟩

end UpperTheory.V.Z.Sym.Sig

end

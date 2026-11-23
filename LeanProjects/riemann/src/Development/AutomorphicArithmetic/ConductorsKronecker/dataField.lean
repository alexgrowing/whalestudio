import Development.AutomorphicArithmetic.PrimitiveCosets.RecH
import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij

open UpperTheory.Comparison₂ Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost NumberField Ideal

private theorem UpperTheory.GL.df_modEq_iff {N M : ℕ} [NeZero N] (x : ZMod N) (a : ℕ) :
    x.val ≡ a [MOD M] ↔ (x.cast : ZMod M) = (a : ZMod M) := by
  rw [← ZMod.natCast_val, ZMod.natCast_eq_natCast_iff]

private theorem UpperTheory.GL.df_mem_local {N : ℕ} [NeZero N] (p : ℕ) (u : (ZMod N)ˣ) :
    u ∈ Formalism.LFunctionChainParameters.LHost.localUnits N p ↔ (u : ZMod N).val ≡ 1 [MOD ordCompl[p] N] := by
  rw [UpperTheory.GL.df_modEq_iff, Nat.cast_one, Formalism.LFunctionChainParameters.LHost.localUnits, MonoidHom.mem_ker, Units.ext_iff,
    ZMod.unitsMap_val, Units.val_one]

private theorem UpperTheory.GL.df_mem_frob {N : ℕ} [NeZero N] (p : ℕ) (hp : p.Prime) (u : (ZMod N)ˣ) :
    u * (frobUnit N p)⁻¹ ∈ Formalism.LFunctionChainParameters.LHost.localUnits N p ↔ (u : ZMod N).val ≡ p [MOD ordCompl[p] N] := by
  have hw := (frobenius_unit_spec N p (NeZero.ne N) hp).1.1
  rw [UpperTheory.GL.df_modEq_iff, Formalism.LFunctionChainParameters.LHost.localUnits, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one,
    Units.ext_iff, ZMod.unitsMap_val, ZMod.unitsMap_val, hw]

private theorem UpperTheory.GL.df_inertia {φ : Frame} (H : HostRaw φ) (p : ℕ) (g : φ.GG) :
    (toE φ g).toAdd ∈ (arith H).inertia p ↔ ∃ u ∈ Formalism.LFunctionChainParameters.LHost.localUnits H.condN p, g = H.art u := by
  show Multiplicative.ofAdd (toE φ g).toAdd ∈ Subgroup.map (recH H) (Formalism.LFunctionChainParameters.LHost.localUnits H.condN p) ↔ _
  rw [Subgroup.mem_map]
  have hinj := ((UpperTheory.Comparison₂.toE_bij φ).1).1
  constructor
  · rintro ⟨u, hu, h⟩
    refine ⟨u, hu, hinj ?_⟩
    exact h.symm
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

theorem UpperTheory.GL.dataField :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
      ((∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ (toE φ (H.gal σ)).toAdd ∈ (arith H.toHostRaw).inertia p) ∧
      (IsArithFrobAt ℤ σ P ↔ (toE φ (H.gal σ)).toAdd - (arith H.toHostRaw).frob p ∈ (arith H.toHostRaw).inertia p) := by
  intro φ H p _ P _ _ σ
  have hp : p.Prime := Fact.out
  haveI : NeZero H.condN := ⟨(Nat.mul_pos (Nat.mul_pos H.QS_pos H.hyp.1.pos) H.hyp.2.1.pos).ne'⟩
  constructor
  · rw [H.der.inertia p P σ, UpperTheory.GL.df_inertia]
    simp only [UpperTheory.GL.df_mem_local]
  · have hfr : (arith H.toHostRaw).frob p =
        (toE φ (H.art (Formalism.LFunctionChainParameters.LHost.frobUnit H.condN p))).toAdd := rfl
    rw [hfr, ← toAdd_div, ← map_div, UpperTheory.GL.df_inertia, H.der.frob_any p P σ]
    constructor
    · rintro ⟨u, hu, he⟩
      refine ⟨u * (Formalism.LFunctionChainParameters.LHost.frobUnit H.condN p)⁻¹, (UpperTheory.GL.df_mem_frob p hp u).2 hu, ?_⟩
      rw [he, map_mul, map_inv, div_eq_mul_inv]
    · rintro ⟨v, hv, he⟩
      refine ⟨v * Formalism.LFunctionChainParameters.LHost.frobUnit H.condN p, (UpperTheory.GL.df_mem_frob p hp _).1 (by rwa [mul_inv_cancel_right]), ?_⟩
      rw [map_mul, ← he, div_mul_cancel]

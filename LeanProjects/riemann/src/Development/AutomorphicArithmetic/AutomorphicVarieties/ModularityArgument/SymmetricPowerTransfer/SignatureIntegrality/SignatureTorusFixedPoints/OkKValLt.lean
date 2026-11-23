import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ScMemIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.SuppZ

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem okK_val_lt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ)
    (ht : valuation k (t : k) < valuation k (unif k : k) ^ 2) : valuation k (t : k) < 1 := by
  have hw : valuation k (unif k : k) < 1 := by
    rw [GlAx.unif_spec]
    exact uniformizer_lt_one
  exact ht.trans (pow_lt_one₀ zero_le' hw two_ne_zero)

private theorem okK_conj {k : Type} [Field k] (g₀ : GL (Fin 2) k) (a b : kˣ) :
    ((g₀ * diagT k (Fin 2) ![a, b] * g₀⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).trace = (a : k) + b ∧
    ((g₀ * diagT k (Fin 2) ![a, b] * g₀⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = (a : k) * b := by
  have hinv : ((g₀⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (g₀ : Matrix (Fin 2) (Fin 2) k) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  simp only [Matrix.GeneralLinearGroup.coe_mul, val_diagT]
  constructor
  · rw [Matrix.trace_mul_cycle, hinv, one_mul]
    simp [Matrix.trace_diagonal, Fin.sum_univ_two]
  · rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, hinv,
      Matrix.det_one, one_mul]
    simp [Matrix.det_diagonal, Fin.prod_univ_two]

theorem UpperTheory.V.Z.Sym.Sig.okK :
    UpperTheory.V.Z.Sym.Sig.OkK := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry hR χ hχ t ht S
  have htv : valuation k (t : k) < 1 := okK_val_lt k t ht
  have hSD : SDom (![t, 1] : Fin 2 → kˣ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    simpa using htv
  have hχH : ∀ u ∈ V.H, χ u = 1 := fun u hu => hχ u (V.H_le hu)
  obtain ⟨_, hZJ, hZd⟩ := eqZ k V χ hχH 2 two_pos
  obtain ⟨_, hmul, hJJ, hfin⟩ := hZd ![t, 1] hSD
  obtain ⟨_, _, _, hIsScal, hmt, hcomap⟩ := eD_facts k O hO h2 Δ s hs hs0
  have hfK : ∀ g, S.fK t g = (((χ t)⁻¹ : ℂˣ) : ℂ) * V.fZ χ ![t, 1] (eD hs g) := fun g => rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro u hu y
    have hu' : eD hs u ∈ V.J 2 := hu
    constructor
    · rw [hfK, hfK, map_mul]
      have e := hJJ (eD hs u) hu' 1 (Subgroup.one_mem _) (eD hs y)
      rw [mul_one] at e
      rw [e]
    · rw [hfK, hfK, map_mul]
      have e := hJJ 1 (Subgroup.one_mem _) (eD hs u) hu' (eD hs y)
      rw [one_mul] at e
      rw [e]
  · intro z s' hz y
    rw [hfK, hfK, map_mul, (hIsScal z s').mp hz, hmul]
    ring
  · have hcj : Subgroup.comap (eD hs) (V.ZJ 2) = ZD Δ ⊔ S.J2 := hcomap V
    have hright : ∀ (g w : GL (Fin 2) k), w ∈ V.ZJ 2 →
        (V.fZ χ ![t, 1] (g * w) ≠ 0 ↔ V.fZ χ ![t, 1] g ≠ 0) := by
      intro g w hw
      obtain ⟨z, j, hj, rfl⟩ := (hZJ w).mp hw
      have hc : g * GeneralLinearGroup.scalar (Fin 2) z = GeneralLinearGroup.scalar (Fin 2) z * g := by
        apply Units.ext
        simp only [Units.val_mul, GeneralLinearGroup.coe_scalar]
        exact (scalar_commute (z : k) (fun r => Commute.all _ r) (g : Matrix (Fin 2) (Fin 2) k)).eq.symm
      have e := hJJ 1 (Subgroup.one_mem _) j hj g
      rw [one_mul] at e
      rw [← mul_assoc, hc, mul_assoc, hmul, e]
      exact ⟨fun h => right_ne_zero_of_mul h, fun h => mul_ne_zero (Units.ne_zero _) h⟩
    let φ : (DX Δ ⧸ (ZD Δ ⊔ S.J2)) → (GL (Fin 2) k ⧸ V.ZJ 2) :=
      fun x => (QuotientGroup.mk (eD hs x.out))
    have hφ : ∀ x x', φ x = φ x' → x = x' := by
      intro x x' he
      have hm := QuotientGroup.eq.mp he
      rw [← map_inv, ← map_mul, ← Subgroup.mem_comap, hcj] at hm
      rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x']
      exact QuotientGroup.eq.mpr hm
    refine (Set.Finite.preimage (f := φ) (fun x _ x' _ he => hφ x x' he) hfin).subset ?_
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hx ⊢
    rw [hfK] at hx
    have hx' := right_ne_zero_of_mul hx
    show V.fZ χ ![t, 1] (Quotient.out (QuotientGroup.mk (eD hs x.out) : GL (Fin 2) k ⧸ V.ZJ 2)) ≠ 0
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (V.ZJ 2) (eD hs x.out)
    rw [hw, hright _ _ w.2]
    exact hx'
  · intro g hg
    rw [hfK] at hg
    have hg' : V.fZ χ ![t, 1] (eD hs g) ≠ 0 := right_ne_zero_of_mul hg
    obtain ⟨g₀, a, b, hgeq, hab⟩ := suppZ k V χ ![t, 1] hSD (eD hs g) hg'
    have ha := a.ne_zero
    have hb := b.ne_zero
    refine ⟨((a / b : kˣ) : k) + ((a / b : kˣ)⁻¹ : kˣ), ⟨a / b / t, ?_, ?_⟩, ?_⟩
    · exact (by simpa using hab : a / b / t ∈ V.H)
    · have e : t * (a / b / t) = a / b := by rw [mul_comm, div_mul_cancel]
      rw [e]
    · obtain ⟨hdet, htr⟩ := hmt g
      rw [show dg ![a, b] = diagT k (Fin 2) ![a, b] from rfl] at hgeq
      obtain ⟨htr', hdet'⟩ := okK_conj g₀ a b
      rw [hdet, htr, hgeq, htr', hdet', ← map_pow, ← map_mul]
      congr 1
      simp only [Units.val_div_eq_div_val, Units.val_inv_eq_inv_val, inv_div]
      field_simp
      ring

end

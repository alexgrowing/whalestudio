import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.UMFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.FlagVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.ResEntry

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

namespace UpperTheory.V.Ws.Bl

end UpperTheory.V.Ws.Bl

private theorem mem_ideal_smul_module_of_entries_mem {A : Type} [CommRing A] (I : Ideal A) (Y : uM A)
    (hY : ∀ i j, (Y : M4 A) i j ∈ I) : Y ∈ I • (⊤ : Submodule A (uM A)) := by
  have h1 : (!![0,0,0,0; 1,0,0,0; 0,0,0,0; 0,0,-1,0] : M4 A) ∈ uM A := by
    refine ⟨fun i j h => ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [adj, sgn]
  have h2 : (!![0,0,0,0; 0,0,1,0; 0,0,0,0; 0,0,0,0] : M4 A) ∈ uM A := by
    refine ⟨fun i j h => ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [adj, sgn]
  have h3 : (!![0,0,0,0; 0,0,0,0; 0,0,0,0; 1,0,0,0] : M4 A) ∈ uM A := by
    refine ⟨fun i j h => ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [adj, sgn]
  obtain ⟨hz, ha⟩ := Y.2
  have h32 : (Y : M4 A) 3 2 = -(Y : M4 A) 1 0 := by
    have h := congrFun (congrFun ha 3) 2
    simp [adj, sgn] at h
    rw [h, neg_neg]
  have hd : Y = (Y : M4 A) 1 0 • (⟨_, h1⟩ : uM A) + (Y : M4 A) 1 2 • (⟨_, h2⟩ : uM A)
      + (Y : M4 A) 3 0 • (⟨_, h3⟩ : uM A) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h32] <;> exact hz _ _ (by decide)
  rw [hd]
  exact add_mem (add_mem (Submodule.smul_mem_smul (hY 1 0) trivial)
    (Submodule.smul_mem_smul (hY 1 2) trivial)) (Submodule.smul_mem_smul (hY 3 0) trivial)

private theorem isLocallyConstant_mkQ_adU_of_adicCont {A : Type} [CommRing A] [IsLocalRing A] {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] [ContinuousInv Γ] (r : Γ →* M4 A) (hb : BG r)
    (hc : ∀ i j, AdicCont (maximalIdeal A) fun g => r g i j) (n : ℕ) (x : uM A) :
    IsLocallyConstant fun g => (lev A (uM A) n).mkQ ((adU hb g) x) := by
  let φ := (Ideal.Quotient.mk (maximalIdeal A ^ n)).mapMatrix (m := Fin 4)
  have hq : ∀ (f : Γ → M4 A), (∀ i j, AdicCont (maximalIdeal A) fun g => f g i j) →
      IsLocallyConstant fun g => φ (f g) := by
    intro f hf
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro M
    have hM : (fun g => φ (f g)) ⁻¹' {M} =
        ⋂ i, ⋂ j, (fun g => Ideal.Quotient.mk (maximalIdeal A ^ n) (f g i j)) ⁻¹' {M i j} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
      constructor
      · intro h i j
        rw [← h]
        rfl
      · intro h
        ext i j
        exact h i j
    rw [hM]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hf i j n).isOpen_fiber _
  have hP : IsLocallyConstant fun g => (φ (r g), φ (r g⁻¹)) :=
    (hq _ hc).prodMk (hq (fun g => r g⁻¹) fun i j N => (hc i j N).comp_continuous continuous_inv)
  have key : ∀ g' g : Γ, (φ (r g'), φ (r g'⁻¹)) = (φ (r g), φ (r g⁻¹)) →
      (lev A (uM A) n).mkQ ((adU hb g') x) = (lev A (uM A) n).mkQ ((adU hb g) x) := by
    intro g' g hgg
    obtain ⟨e1, e2⟩ := Prod.mk.inj hgg
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    apply mem_ideal_smul_module_of_entries_mem
    intro i j
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h0 : φ ((↑((adU hb g') x - (adU hb g) x) : M4 A)) = 0 := by
      rw [Submodule.coe_sub]
      change φ (r g' * (x : M4 A) * r g'⁻¹ - r g * (x : M4 A) * r g⁻¹) = 0
      simp only [map_sub, map_mul, e1, e2, sub_self]
    simpa [φ] using congrFun (congrFun h0 i) j
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  have hy : (fun g => (lev A (uM A) n).mkQ ((adU hb g) x)) ⁻¹' {y} =
      ⋃ g ∈ (fun g => (lev A (uM A) n).mkQ ((adU hb g) x)) ⁻¹' {y},
        (fun g => (φ (r g), φ (r g⁻¹))) ⁻¹' {(φ (r g), φ (r g⁻¹))} := by
    ext g'
    constructor
    · intro h
      exact Set.mem_biUnion h rfl
    · intro h
      obtain ⟨g, hg, hgg⟩ := Set.mem_iUnion₂.1 h
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg hgg ⊢
      rw [← hg]
      exact key g' g hgg
  rw [hy]
  exact isOpen_biUnion fun g _ => hP.isOpen_fiber _

private theorem isSUp_mul_mul_of_isUp_isSUp_isUp {A : Type} [CommRing A] (P N Q : M4 A) (hP : IsUp P) (hN : IsSUp N)
    (hQ : IsUp Q) : IsSUp (P * N * Q) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hli : l < i
  · rw [hP i l hli, zero_mul, zero_mul]
  by_cases hkl : k ≤ l
  · rw [hN l k hkl, mul_zero, zero_mul]
  rw [hQ k j (by omega), mul_zero]

theorem UpperTheory.V.Ws.Bl.latU :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (r : G ℚ Ω →* M4 A) (u : M4 A) (h : BlockDiagonalOrdinaryGSpRep S c s B r u),
          Lat (adU h.bg) (Dec (F := ℚ) B) (uPlus u) ∧ (∀ Y, adU h.bg c Y = -Y) ∧ r.ker ≤ (adU h.bg).ker := by
  intro Ω _ _ _ l _ S c s B hp A _ _ _ r u h
  have hinv : ∀ g, r g = 1 → r g⁻¹ = 1 := by
    intro g hg
    calc r g⁻¹ = r g⁻¹ * r g := by rw [hg, mul_one]
      _ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have huu : u * adj u = 1 := by
    have h1 : adj u * u = 1 := by
      have := h.sp
      simpa [IsGSp] using this
    exact mul_eq_one_comm.1 h1
  refine ⟨⟨fun n x => isLocallyConstant_mkQ_adU_of_adicCont r h.bg h.cont n x, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg Y hY
    have hg' : g⁻¹ ∈ Dec (F := ℚ) B := (Dec (F := ℚ) B).inv_mem hg
    change IsSUp (adj u * (r g * (Y : M4 A) * r g⁻¹) * u)
    have he : adj u * (r g * (Y : M4 A) * r g⁻¹) * u
        = (adj u * r g * u) * (adj u * (Y : M4 A) * u) * (adj u * r g⁻¹ * u) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc u (adj u), huu, Matrix.one_mul, ← Matrix.mul_assoc u (adj u), huu,
        Matrix.one_mul]
    rw [he]
    exact isSUp_mul_mul_of_isUp_isSUp_isUp _ _ _ (h.flag g hg) hY (h.flag _ hg')
  · intro a Y ha hY
    change IsSUp (adj u * ((a • Y : uM A) : M4 A) * u) at hY
    change IsSUp (adj u * (Y : M4 A) * u)
    intro i j hij
    have h0 := hY i j hij
    rw [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.1 h0).resolve_left ha
  · exact flagVec A (r s) u (h.bg.blk s) h.sep h.sp (h.flag s hp.dec) h.char
  · exact ⟨s, hp.dec, adBij A (G ℚ Ω) r h.bg s h.sep⟩
  · intro Y
    have hc2 : r c * r c = 1 := by
      rw [h.cc]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [eAB]
    have hci : r c⁻¹ = r c := by
      calc r c⁻¹ = r c⁻¹ * (r c * r c) := by rw [hc2, Matrix.mul_one]
        _ = r (c⁻¹ * c) * r c := by rw [map_mul, Matrix.mul_assoc]
        _ = r c := by rw [inv_mul_cancel, map_one, Matrix.one_mul]
    obtain ⟨hz, _⟩ := Y.2
    apply Subtype.ext
    change r c * (Y : M4 A) * r c⁻¹ = -(Y : M4 A)
    rw [hci, h.cc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eAB, hz 0 0 (by decide), hz 0 1 (by decide), hz 0 2 (by decide), hz 0 3 (by decide),
        hz 1 1 (by decide), hz 1 3 (by decide), hz 2 0 (by decide), hz 2 1 (by decide),
        hz 2 2 (by decide), hz 2 3 (by decide), hz 3 1 (by decide), hz 3 3 (by decide)]
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply LinearMap.ext
    intro Y
    apply Subtype.ext
    change r g * (Y : M4 A) * r g⁻¹ = (Y : M4 A)
    rw [hg, hinv g hg, Matrix.one_mul, Matrix.mul_one]

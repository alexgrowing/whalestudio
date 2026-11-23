import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqActStdLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLatticeStdLatAndAct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLatticeChainLatAndComap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenAndRelIndexNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsRepsOfFg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StabiliserFiniteCosetsMod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnipotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralPeriodicEqMeasureMulSumCosets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolFreePerLatStdLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexPerLat

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise

noncomputable section
namespace GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms

@[to_additive relIndex_mul_addVol
]
theorem relIndex_mul_mulVol {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H L : Subgroup G) (hHL : H ≤ L) [(H.subgroupOf L).FiniteIndex]
    (hH : MeasurableSet (H : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] :
    (H.relIndex L : ENNReal) * μ H = μ L := by
  obtain ⟨s, hs, -⟩ := (H.subgroupOf L).exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  have hU : (⋃ a : s, (a.val : L) • (H : Set G)) = (L : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_smul_set, SetLike.mem_coe]
    constructor
    · rintro ⟨a, h, hh, rfl⟩
      exact L.mul_mem a.val.2 (hHL hh)
    · intro hx
      obtain ⟨⟨b, h⟩, hbh, -⟩ := hs.existsUnique ⟨x, hx⟩
      refine ⟨b, (h.val : G), Subgroup.mem_subgroupOf.mp h.2, ?_⟩
      have := congrArg Subtype.val hbh
      exact this
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => (a.val : L) • (H : Set G)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨h1, hh1, rfl⟩ ⟨h2, hh2, he⟩
    apply hab
    have hh1' : (⟨h1, hHL hh1⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh1
    have hh2' : (⟨h2, hHL hh2⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh2
    have e : (a.val : L) * ⟨h1, hHL hh1⟩ = (b.val : L) * ⟨h2, hHL hh2⟩ := Subtype.ext he.symm
    have := (hs.existsUnique ((a.val : L) * ⟨h1, hHL hh1⟩)).unique
      (y₁ := (a, ⟨_, hh1'⟩)) (y₂ := (b, ⟨_, hh2'⟩)) rfl e.symm
    exact congrArg Prod.fst this
  calc (H.relIndex L : ENNReal) * μ H = ∑' a : s, μ ((a.val : L) • (H : Set G)) := by
        simp [measure_smul, hs.encard_left, Subgroup.relIndex]
    _ = μ (⋃ a : s, (a.val : L) • (H : Set G)) :=
        (measure_iUnion hdisj fun a => hH.const_smul _).symm
    _ = μ L := by rw [hU]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

set_option linter.unusedSectionVars false

theorem coe_ne_zero {ϖ : 𝒪[k]} (h : Irreducible ϖ) : (ϖ : k) ≠ 0 := fun h0 => h.ne_zero (Subtype.ext h0)

theorem psi_int {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {s : k} (hs : s ∈ 𝒪[k]) : ψ s = 1 :=
  hψ.eq_one (by simpa [cball, Valuation.mem_integer_iff] using hs)

theorem mem_int_of_psi {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {s : k}
    (hs : ∀ a : 𝒪[k], ψ (-(a * s)) = 1) : s ∈ 𝒪[k] := by
  rcases eq_or_ne s 0 with rfl | h0
  · exact zero_mem _
  have := (hψ s).1 fun y hy => by
    have ha : -(y / s) ∈ 𝒪[k] := by
      refine neg_mem ?_
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ hy zero_le
    have := hs ⟨_, ha⟩
    simpa [h0] using this
  simpa [Valuation.mem_integer_iff] using this

theorem smul_mem_Yle {i : ℕ} (a : k) {v : n ⊕ Fin c → k} (hv : v ∈ Yle k n c i) : a • v ∈ Yle k n c i :=
  fun l hl => by simp [hv l hl]

theorem smul_inX (a : k) (v : n → k) : a • inX k n c v = inX k n c (a • v) := by
  ext (r | r) <;> simp [inX_apply]

theorem colMat_eq_zero {y : Fin c → (n ⊕ Fin c → k)} (hy : ∀ i, y i ∈ Yle k n c (i.val + 1))
    (l : Fin c) (j : Fin (c + 1)) (h : j.val ≤ l.val) : colMat n' y (Sum.inr l) (Sum.inr j) = 0 := by
  revert h
  refine Fin.cases (fun _ => ?_) (fun i h => ?_) j
  · simp [colMat]
  · simp only [Fin.val_succ] at h
    simpa [colMat] using hy i l (by omega)

theorem mulVec_auxiliaryBasisVectorSumFin_apply (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (j : Fin (c + 1)) (r) :
    (x *ᵥ aux k n' j) r = x r (Sum.inr j) := by
  simp [aux]

theorem act_embX (ϖ : 𝒪[k]) (g : GL n k) (L : Submodule 𝒪[k] (n → k)) :
    act (embX c g) (chainLat ϖ c L) = chainLat ϖ c (act g L) := by
  ext v
  rw [mem_act_iff_inv, ← map_inv, Radical.embX_val, fromBlocks_mulVec, mem_chainLat, mem_chainLat,
    mem_act_iff_inv]
  simp only [Sum.elim_inl, Sum.elim_inr, zero_mulVec, add_zero, zero_add, one_mulVec, Function.comp]
  rfl

variable [MeasurableSpace k] [BorelSpace k]

theorem oneClass (hc : 1 ≤ c) {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {ν : Measure k} (hν : IsUnitVol ν) (L' : Submodule 𝒪[k] (n' → k)) : OneClass ϖ ψ ν n hc L' := by
  intro Λ hΛ Ψ _ hS hP hE
  have := hν.1
  have h0 := coe_ne_zero hϖ
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, opE ψ ν 1 Ψ x₀ ≠ 0 := Function.ne_iff.1 hE
  obtain ⟨y, hy, hΨ⟩ := exists_pt_ne_zero hx₀
  have hmap := hS _ hΨ
  have h1 : ∀ i : Fin c, (Λ ⊓ Yle k n c (i.val + 1)).map (LinearMap.proj (Sum.inr i)) =
      Submodule.span 𝒪[k] {(ϖ : k) ^ (i.val + 1)} := by
    intro i
    apply le_antisymm
    · have key : ∀ v ∈ Λ ⊓ Yle k n c (i.val + 1), ψ (-(v (Sum.inr i) / (ϖ : k) ^ (i.val + 1))) = 1 := by
        intro v hv
        let z : Fin c → (n ⊕ Fin c → k) := Pi.single i (((ϖ : k) ^ (i.val + 2))⁻¹ • v)
        have hz : ∀ j, (ϖ : k) ^ (j.val + 2) • z j ∈ Λ := by
          intro j
          rcases eq_or_ne j i with rfl | hj
          · simp only [z, Pi.single_eq_same]
            rw [smul_inv_smul₀ (pow_ne_zero _ h0)]
            exact hv.1
          · simp [z, hj]
        have hz' : ∀ j, ((ϖ : k) • z) j ∈ Yle k n c (j.val + 1) := by
          intro j
          rcases eq_or_ne j i with rfl | hj
          · simp only [z, Pi.smul_apply, Pi.single_eq_same]
            exact smul_mem_Yle _ (smul_mem_Yle _ hv.2)
          · simp [z, hj]
        have := opE_translate ψ ν hz' (fun x => by
          rw [colMat_smul]; exact hP x _ (mapsInto_colMat hz)) x₀
        have h2 : (ψ (-∑ j, ((ϖ : k) • z) j (Sum.inr j)) : ℂ) = 1 :=
          mul_right_cancel₀ hx₀ (by rw [one_mul]; exact this.symm)
        rw [Finset.sum_eq_single i (fun j _ hj => by simp [z, hj]) (by simp)] at h2
        rw [← Circle.coe_eq_one, ← h2]
        congr 3
        simp only [z, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
        field_simp
        ring
      rintro _ ⟨v, hv, rfl⟩
      have := mem_int_of_psi hψ (s := v (Sum.inr i) / (ϖ : k) ^ (i.val + 1)) fun a => by
        have := key _ (Submodule.smul_mem _ a hv)
        rw [← this]
        congr 2
        simp [Subring.smul_def, mul_div_assoc]
      refine Submodule.mem_span_singleton.2 ⟨⟨_, this⟩, ?_⟩
      simp [Subring.smul_def, h0]
    · rw [Submodule.span_singleton_le_iff_mem]
      refine ⟨_, ⟨hmap _ (scaled_basis_mem_chainLattice ϖ L' i.castSucc), fun l hl => ?_⟩, ?_⟩
      · rw [Matrix.mulVec_smul, Pi.smul_apply, mulVec_auxiliaryBasisVectorSumFin_apply, pt_eq, Matrix.add_apply,
          colMat_eq_zero hy _ _ (by simp; omega)]
        have : l.val ≠ i.val := by omega
        simp [basePt, this]
      · rw [LinearMap.proj_apply, Matrix.mulVec_smul, Pi.smul_apply, mulVec_auxiliaryBasisVectorSumFin_apply, pt_eq, Matrix.add_apply,
          colMat_eq_zero hy _ _ (by simp)]
        simp [basePt]
  have h2 : (ϖ : k) • aux k n (⟨0, hc⟩ : Fin c) ∈ Λ := by
    have := hmap _ (scaled_basis_mem_chainLattice ϖ L' 0)
    convert this using 1
    ext r
    rw [Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, mulVec_auxiliaryBasisVectorSumFin_apply]
    rcases r with r | r
    · simp [pt_eq, basePt, colMat, aux]
    · simp only [pt_eq, basePt, colMat, aux, Pi.single_apply, Fin.ext_iff]
      by_cases hr : r.val = 0 <;> simp [hr, Fin.ext_iff]
  obtain ⟨u, hu, huΛ⟩ := GlobalTheory.RootEx.UnfoldFlag.exists_unipotent k n c hc ϖ h0 Λ h1 h2
  refine ⟨h1, h2, ⟨u, hu, huΛ⟩, ?_⟩
  obtain ⟨g, hg⟩ := GlobalTheory.RootEx.UnfoldShape.exists_eq_act_stdLat k n _ ((GlobalTheory.RootEx.ChainLattice.isLattice_chainLat_and_comap k n c).2 Λ hΛ)
  refine ⟨u⁻¹ * embX c g, mul_mem (inv_mem (Subgroup.mem_sup_right hu)) (Subgroup.mem_sup_left ⟨g, rfl⟩), ?_⟩
  rw [act_mul, act_embX, ← hg, ← huΛ, ← act_mul, inv_mul_cancel, act_one]

theorem oneCoset (hc : 1 ≤ c) {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {ν : Measure k} (hν : IsUnitVol ν) (L' : Submodule 𝒪[k] (n' → k)) : OneCoset ϖ ψ ν n c L' := by
  have h0 := coe_ne_zero hϖ
  have hlat : Submodule.IsLattice k (chainLat ϖ c (stdLat k n)) :=
    (GlobalTheory.RootEx.ChainLattice.isLattice_chainLat_and_comap k n c).1 ϖ h0 _ (GlobalTheory.RootEx.UnfoldShape.isLattice_stdLat_and_act k n).1
  constructor
  · intro μ Φ hΦ hS hP h' h hh' hE
    have key := oneClass hc hϖ hψ hν L' _ ((GlobalTheory.RootEx.UnfoldShape.isLattice_stdLat_and_act k _).2 h _ hlat) _
      (om_mem_SB μ h' h hΦ) ?_ ?_ hE
    · obtain ⟨r, hr, e⟩ := key.2.2.2
      refine ⟨r, hr, r⁻¹ * h, ?_, by group⟩
      rw [act_mul, e, ← act_mul, inv_mul_cancel, act_one]
    · intro x hx v hv
      rw [← hh'] at hv
      obtain ⟨w, hw, rfl⟩ := mem_act.1 hv
      have := hS _ (right_ne_zero_of_mul hx) w hw
      rw [mem_act_iff_inv]
      simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using this
    · intro x y hy
      have : MapsInto ((h⁻¹).val * y * h'.val) (chainLat ϖ (c + 1) L') (chainLat ϖ c (stdLat k n)) := by
        intro w hw
        have h1 : h'.val *ᵥ w ∈ chainLat ϖ (c + 1) L' := by
          rw [← hh']; exact mem_act.2 ⟨w, hw, rfl⟩
        have := mem_act_iff_inv.1 (hy _ h1)
        simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using this
      simp only [om]
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hP _ _ this]
  · intro J hJ hJ'
    obtain ⟨S, hS⟩ := GlobalTheory.RootEx.UnfoldShape.exists_isReps_of_fg k _ ϖ hϖ _ hlat.fg
    obtain ⟨T, hT, hT'⟩ := GlobalTheory.RootEx.UnfoldShape.stabiliser_finite_cosets_mod k _ ϖ _ S hlat.fg hS
    refine ⟨T, hT, fun h => ⟨?_, ?_⟩⟩
    · rintro ⟨r, hr, t, ht, rfl⟩
      obtain ⟨t₀, ht₀, j, hj, hj', rfl⟩ := hT' t ht
      exact ⟨r, hr, t₀, ht₀, j, hJ' j hj hj', (mul_assoc _ _ _).symm⟩
    · rintro ⟨r, hr, t, ht, j, hj, rfl⟩
      exact ⟨r, hr, t * j, by rw [act_mul, hJ j hj, hT t ht], mul_assoc _ _ _⟩

theorem suppIn_opE {ϖ : 𝒪[k]} (ψ : AddChar k Circle) (ν : Measure k) {L' : Submodule 𝒪[k] (n' → k)}
    {L : Submodule 𝒪[k] (n → k)} {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hS : SuppIn Ψ (chainLat ϖ (c + 1) L') (chainLat ϖ c L)) : SuppIn (opE ψ ν 1 Ψ) L' L := by
  intro x₀ hx v hv
  obtain ⟨y, -, hy⟩ := exists_pt_ne_zero hx
  have := hS _ hy _ (inX_mem_chainLat.2 hv)
  rwa [pt_mulVec_inX, inX_mem_chainLat] at this

theorem periodicMod_opE {ϖ : 𝒪[k]} (ψ : AddChar k Circle) (ν : Measure k) {L' : Submodule 𝒪[k] (n' → k)}
    {L : Submodule 𝒪[k] (n → k)} {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hP : PeriodicMod ϖ Ψ (chainLat ϖ (c + 1) L') (chainLat ϖ c L)) : PeriodicMod ϖ (opE ψ ν 1 Ψ) L' L := by
  intro x₀ x₁ hx
  have h1 : MapsInto (fromBlocks x₁ 0 0 0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
      (chainLat ϖ (c + 1) L') (chainLat ϖ c L) := by
    intro v hv
    rw [fromBlocks_mulVec, mem_chainLat]
    refine ⟨?_, fun i => ⟨0, by simp⟩⟩
    simpa [Function.comp_def] using hx _ (mem_chainLat.1 hv).1
  have h2 : (fromBlocks ((ϖ : k) • x₁) 0 0 0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) =
      (ϖ : k) • fromBlocks x₁ 0 0 0 := by simp [fromBlocks_smul]
  simp only [opE_one_eq_volFree, pt_add_base, h2, hP _ _ h1]

theorem injSupp {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) (ψ : AddChar k Circle) (ν : Measure k)
    (L' : Submodule 𝒪[k] (n' → k)) : InjSupp ϖ ψ ν n c L' := by
  intro L _ Ψ _ hS _ hI x₀ hx
  have h0 := coe_ne_zero hϖ
  refine ⟨suppIn_opE ψ ν hS x₀ hx, fun v hv hxv => ?_⟩
  obtain ⟨y, -, hy⟩ := exists_pt_ne_zero hx
  have := (hI _ hy).2 _ (inX_mem_chainLat.2 hv) (by
    rw [pt_mulVec_inX, mem_smul_iff_inv h0, smul_inX, inX_mem_chainLat]
    exact (mem_smul_iff_inv h0).1 hxv)
  rw [mem_smul_iff_inv h0, smul_inX, inX_mem_chainLat] at this
  exact (mem_smul_iff_inv h0).2 this

theorem continuous_col (i : Fin c) :
    Continuous fun e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k => col e i := by
  refine continuous_pi fun r => ?_
  simp only [col]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem measurableSet_perLat {ϖ : 𝒪[k]} (h0 : (ϖ : k) ≠ 0) {L : Submodule 𝒪[k] (n → k)}
    (hL : Submodule.IsLattice k L) :
    MeasurableSet (perLat ϖ n' c L : Set ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k)) := by
  have := secondCountable k
  have ho := (GlobalTheory.RootEx.LatOpen.isOpen_and_relIndex_ne_zero k _ _ ((GlobalTheory.RootEx.ChainLattice.isLattice_chainLat_and_comap k n c).1 ϖ h0 L hL)).1
  have : (perLat ϖ n' c L : Set ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k)) = ⋂ i : Fin c,
      (fun e => (ϖ : k) ^ (i.val + 1) • col (n' := n') e i) ⁻¹' (chainLat ϖ c L : Set (n ⊕ Fin c → k)) := by
    ext e
    simp only [SetLike.mem_coe, mem_perLat, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact (isOpen_iInter_of_finite fun i => ho.preimage ((continuous_col (n := n) (n' := n') i).const_smul ((ϖ : k) ^ (i.val + 1)))).measurableSet

theorem volFree_invariant (ν : Measure k) [ν.IsAddHaarMeasure] : (volFree ν n n' c).IsAddLeftInvariant := by
  have := secondCountable k
  unfold volFree
  infer_instance

theorem vol_perLat {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {ν : Measure k} (hν : IsUnitVol ν)
    {L : Submodule 𝒪[k] (n → k)} (hL : Submodule.IsLattice k L) (hle : L ≤ stdLat k n) :
    volFree ν n n' c (perLat ϖ n' c L) ≠ ⊤ ∧ (((volFree ν n n' c).real (perLat ϖ n' c L) : ℝ) : ℂ) =
      (resCard k : ℂ) ^ expo c (Fintype.card n) /
        (L.toAddSubgroup.relIndex (stdLat k n).toAddSubgroup : ℂ) ^ c := by
  have := hν.1
  have := secondCountable k
  have := volFree_invariant (n := n) (n' := n') (c := c) ν
  have h0 := coe_ne_zero hϖ
  have hi := (GlobalTheory.RootEx.LatOpen.isOpen_and_relIndex_ne_zero k n L hL).2
  have hidx := GlobalTheory.RootEx.PerIndex.relIndex_perLat k n n' c ϖ h0 L
  have hbox := GlobalTheory.RootEx.UnfoldShape.volFree_perLat_stdLat k n n' c ϖ hϖ ν hν
  have hHL : perLat ϖ n' c L ≤ perLat ϖ n' c (stdLat k n) := fun e he i =>
    mem_chainLat.2 ⟨hle (mem_chainLat.1 (he i)).1, (mem_chainLat.1 (he i)).2⟩
  have : ((perLat ϖ n' c L).addSubgroupOf (perLat ϖ n' c (stdLat k n))).FiniteIndex :=
    ⟨by rw [← AddSubgroup.relIndex, hidx]; exact pow_ne_zero _ hi⟩
  have h := relIndex_mul_addVol _ _ hHL (measurableSet_perLat h0 hL) (volFree ν n n' c)
  refine ⟨ne_top_of_le_ne_top (by rw [hbox]; simp) (measure_mono hHL), ?_⟩
  rw [hbox, hidx] at h
  have h2 := congrArg (fun x : ENNReal => (x.toReal : ℂ)) h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast, Nat.cast_pow] at h2
  push_cast at h2
  rw [eq_div_iff (pow_ne_zero _ (Nat.cast_ne_zero.2 hi)), ← h2, mul_comm]
  rfl

theorem col_sub (e e' : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) :
    col (e - e') = col e - col e' := by
  rw [eq_sub_iff_add_eq, ← col_add, sub_add_cancel]

theorem formula {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {ν : Measure k} (hν : IsUnitVol ν) {L' : Submodule 𝒪[k] (n' → k)}
    {L : Submodule 𝒪[k] (n → k)} (hL : Submodule.IsLattice k L) (hle : L ≤ stdLat k n)
    {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hS : SuppIn Ψ (chainLat ϖ (c + 1) L') (chainLat ϖ c L))
    (hP : PeriodicMod ϖ Ψ (chainLat ϖ (c + 1) L') (chainLat ϖ c L))
    (T : Fin c → Finset (n ⊕ Fin c → k))
    (hT : ∀ i, IsReps ϖ (chainLat ϖ c L ⊓ Yle k n c (i.val + 1)) (T i))
    (x₀ : Matrix n n' k) (hx : MapsInto x₀ L' L) :
    opE ψ ν 1 Ψ x₀ = (resCard k : ℂ) ^ expo c (Fintype.card n) /
        (L.toAddSubgroup.relIndex (stdLat k n).toAddSubgroup : ℂ) ^ c *
      ∑ w ∈ Fintype.piFinset T, term ϖ ψ Ψ x₀ w := by
  have := hν.1
  have := secondCountable k
  have := volFree_invariant (n := n) (n' := n') (c := c) ν
  have h0 := coe_ne_zero hϖ
  obtain ⟨hfin, hvol⟩ := vol_perLat (n' := n') (c := c) hϖ hν hL hle
  have hcol : ∀ w ∈ Fintype.piFinset T, col (uncol n' fun i => ((ϖ : k) ^ (i.val + 2))⁻¹ • w i) =
      fun i => ((ϖ : k) ^ (i.val + 2))⁻¹ • w i := fun w hw =>
    col_uncol fun i => smul_mem_Yle _ ((hT i).1 _ (Fintype.mem_piFinset.1 hw i)).2
  have hsc : ∀ (i : Fin c) (v : n ⊕ Fin c → k),
      (ϖ : k) ^ (i.val + 1) • ((ϖ : k) ^ (i.val + 2))⁻¹ • v = (ϖ : k)⁻¹ • v := by
    intro i v
    rw [smul_smul]
    congr 1
    field_simp
    ring
  rw [opE_one_eq_volFree, GlobalTheory.RootEx.UnfoldShape.integral_periodic_eq_measure_mul_sum_cosets _ (volFree ν n n' c) (perLat ϖ n' c L) (measurableSet_perLat h0 hL) hfin _ _
    (Fintype.piFinset T) (fun w => uncol n' fun i => ((ϖ : k) ^ (i.val + 2))⁻¹ • w i), hvol]
  · congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hcol w hw, term, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, Finset.sum_div]
    congr 4
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · intro e h hh
    have h1 : colMat n' (col h) = (ϖ : k) • colMat n' ((ϖ : k)⁻¹ • col h) := by
      rw [← colMat_smul, smul_inv_smul₀ h0]
    have h2 : MapsInto (colMat n' ((ϖ : k)⁻¹ • col h)) (chainLat ϖ (c + 1) L') (chainLat ϖ c L) := by
      refine mapsInto_colMat fun i => ?_
      rw [Pi.smul_apply, smul_smul, pow_succ, mul_inv_cancel_right₀ h0]
      exact hh i
    have h3 : ψ (-∑ i, col h i (Sum.inr i)) = 1 := by
      refine psi_int hψ (neg_mem (sum_mem fun i _ => ?_))
      obtain ⟨a, ha⟩ := (mem_chainLat.1 (hh i)).2 i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm] at ha
      rw [mul_right_cancel₀ (pow_ne_zero _ h0) ha]
      exact a.2
    simp only [col_add, pt_add, Pi.add_apply, Finset.sum_add_distrib, neg_add, AddChar.map_add_eq_mul, h3,
      mul_one]
    rw [h1, hP _ _ h2]
  · intro e he
    have hm := hS _ (left_ne_zero_of_mul he)
    have h1 : ∀ i : Fin c, (ϖ : k) ^ (i.val + 2) • col e i ∈ chainLat ϖ c L ⊓ Yle k n c (i.val + 1) := by
      intro i
      refine ⟨?_, smul_mem_Yle _ (col_mem_Yle e i)⟩
      have ha := scaled_basis_mem_chainLattice ϖ L' i.succ
      have := sub_mem (hm _ ha) (mapsInto_basePt hx _ ha)
      rw [pt_eq, Matrix.add_mulVec, add_sub_cancel_left] at this
      have e1 : colMat n' (col e) *ᵥ ((ϖ : k) ^ (i.succ.val + 1) • aux k n' i.succ) =
          (ϖ : k) ^ (i.val + 2) • col e i := by
        ext r
        rw [Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, mulVec_auxiliaryBasisVectorSumFin_apply]
        simp [colMat]
      rwa [e1] at this
    choose w hw using fun i => ((hT i).2 _ (h1 i)).exists
    have hw' : w ∈ Fintype.piFinset T := Fintype.mem_piFinset.2 fun i => (hw i).1
    refine ⟨w, hw', fun i => ?_⟩
    have := ((mem_smul_iff_inv h0).1 (hw i).2).1
    rw [← hsc i, smul_sub ((ϖ : k) ^ (i.val + 2))⁻¹, inv_smul_smul₀ (pow_ne_zero _ h0)] at this
    rw [col_sub, hcol w hw']
    exact this
  · intro w hw w' hw' h
    funext i
    have hi := (hT i).1 _ (Fintype.mem_piFinset.1 hw i)
    have hi' := (hT i).1 _ (Fintype.mem_piFinset.1 hw' i)
    have h1 := h i
    rw [col_sub, hcol w hw, hcol w' hw', Pi.sub_apply, ← smul_sub, hsc] at h1
    refine ((hT i).2 _ hi).unique ⟨Fintype.mem_piFinset.1 hw i, by rw [sub_self]; exact zero_mem _⟩
      ⟨Fintype.mem_piFinset.1 hw' i, (mem_smul_iff_inv h0).2 ⟨h1, smul_mem_Yle _ (sub_mem hi.2 hi'.2)⟩⟩

theorem psi_pow_ringChar {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {s : k} (hs : s ∈ 𝒪[k]) : ψ (s / ϖ) ^ ringChar 𝓀[k] = 1 := by
  have h0 := coe_ne_zero hϖ
  have h1 : ((ringChar 𝓀[k] : ℕ) : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact (ringChar.spec _ _).2 dvd_rfl
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at h1
  obtain ⟨a, ha⟩ := h1
  have h2 : (a : k) * ϖ = (ringChar 𝓀[k] : ℕ) := by exact_mod_cast congrArg Subtype.val ha
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ← h2]
  refine psi_int hψ ?_
  rw [mul_assoc, mul_div_cancel₀ _ h0]
  exact mul_mem a.2 hs

theorem funMod {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {ν : Measure k} (hν : IsUnitVol ν) (L' : Submodule 𝒪[k] (n' → k)) : FunMod ϖ ψ ν n c L' := by
  classical
  intro L hL Ψ _ hS hP
  have h0 := coe_ne_zero hϖ
  have hT : ∃ T : Fin c → Finset (n ⊕ Fin c → k),
      ∀ i, IsReps ϖ (chainLat ϖ c L ⊓ Yle k n c (i.val + 1)) (T i) := by
    have := fun i : Fin c => GlobalTheory.RootEx.UnfoldShape.exists_isReps_of_fg k _ ϖ hϖ (chainLat ϖ c L ⊓ Yle k n c (i.val + 1))
      (Submodule.FG.of_le ((GlobalTheory.RootEx.ChainLattice.isLattice_chainLat_and_comap k n c).1 ϖ h0 L hL).fg inf_le_left)
    choose T hT using this
    exact ⟨T, hT⟩
  refine ⟨suppIn_opE ψ ν hS, periodicMod_opE ψ ν hP, hT, fun hle =>
    ⟨fun T hT x₀ hx => formula hϖ hψ hν hL hle hS hP T hT x₀ hx, fun x₀ => ?_⟩⟩
  by_cases hx : MapsInto x₀ L' L
  · obtain ⟨T, hT⟩ := hT
    refine ⟨_, sum_mem fun w hw => ?_, formula hϖ hψ hν hL hle hS hP T hT x₀ hx⟩
    refine mul_mem (Subring.subset_closure (Or.inr ⟨_, rfl⟩)) (Subring.subset_closure (Or.inl ?_))
    rw [Set.mem_setOf_eq, ← map_pow, ← Circle.coe_pow, psi_pow_ringChar hϖ hψ, Circle.coe_one, map_one]
    refine sum_mem fun i _ => ?_
    obtain ⟨a, ha⟩ := (mem_chainLat.1 ((hT i).1 _ (Fintype.mem_piFinset.1 hw i)).1).2 i
    rw [ha, mul_div_cancel_right₀ _ (pow_ne_zero _ h0)]
    exact a.2
  · refine ⟨0, zero_mem _, ?_⟩
    rw [mul_zero]
    by_contra h
    exact hx (suppIn_opE ψ ν hS x₀ h)

theorem shape : GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.Shape :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc _ hϖ ψ hψ ν hν L' _ =>
    ⟨oneClass hc hϖ hψ hν L', oneCoset hc hϖ hψ hν L', funMod hϖ hψ hν L', injSupp hϖ ψ ν L'⟩

end GlobalTheory.RootEx.UnfoldShape

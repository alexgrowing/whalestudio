import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
open Classical

noncomputable section

namespace GlobalTheory.LowerHeckeCount

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {D : Type} [Fintype D] [DecidableEq D]

theorem ko_mulVec_mem (κ : GL D k) (hκ : κ ∈ KO k D) (v : D → k) (hv : v ∈ mLat k D) :
    κ.1 *ᵥ v ∈ mLat k D := by
  rw [mem_mLat] at hv ⊢
  intro i
  have hent : ∀ j, valuation k (κ.1 i j) ≤ 1 := fun j =>
    (Valuation.mem_integer_iff _ _).1 (((GlobalTheory.SplitFlip.mem_KO_iff κ).1 hκ).1 i j)
  rw [Matrix.mulVec, dotProduct]
  exact Valuation.map_sum_lt _ one_ne_zero fun j _ => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hent j)) (hv j)

theorem dc_mulVec_mem {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {s : Finset D} {g : GL D k}
    (hg : ∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') (v : D → k) (hv : v ∈ mLat k D) :
    g.1 *ᵥ v ∈ mLat k D := by
  obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hg
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have h1 := ko_mulVec_mem κ' hκ' v hv
  have h2 : (torusElt k D ϖ (indic s)).1 *ᵥ (κ'.1 *ᵥ v) ∈ mLat k D := by
    rw [mem_mLat] at h1 ⊢
    intro i
    rw [val_torusElt, mulVec_diagonal, map_mul]
    have hle : valuation k ((ϖ : k) ^ indic s i) ≤ 1 := by
      rw [map_zpow₀]
      exact zpow_le_one₀ (zero_lt_iff.2 (by simp)) hlt.le (by unfold indic; split_ifs <;> norm_num)
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hle) (h1 i)
  have h3 := ko_mulVec_mem κ hκ _ h2
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
  exact h3

theorem preLat_inv_le {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {s : Finset D} {g : GL D k}
    (hg : ∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') :
    preLat (g⁻¹).1 ≤ mLat k D := by
  intro v hv
  have e : g.1 *ᵥ ((g⁻¹).1 *ᵥ v) = v := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  rw [← e]
  exact dc_mulVec_mem hϖ hg _ (mem_preLat.1 hv)

theorem smul_mem_preLat_inv {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {s : Finset D} {g : GL D k}
    (hg : ∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') (u : D → k) (hu : u ∈ mLat k D) :
    (ϖ : k) • u ∈ preLat (g⁻¹).1 := by
  obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hg
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have ht : (torusElt k D ϖ (indic s))⁻¹ = torusElt k D ϖ (-indic s) := by
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    rw [Units.val_mul, val_torusElt, val_torusElt, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
    congr 1; funext i
    rw [← zpow_add₀ (Units.ne_zero ϖ)]; simp
  have e : (κ * torusElt k D ϖ (indic s) * κ')⁻¹ = κ'⁻¹ * torusElt k D ϖ (-indic s) * κ⁻¹ := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, ht, mul_assoc]
  rw [mem_preLat, e, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_smul]
  refine ko_mulVec_mem κ'⁻¹ (inv_mem hκ') _ ?_
  have hw := mem_mLat.1 (ko_mulVec_mem κ⁻¹ (inv_mem hκ) u hu)
  rw [mem_mLat]
  intro i
  rw [val_torusElt, mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  by_cases hi : i ∈ s
  · have : indic s i = 1 := by unfold indic; simp [hi]
    rw [this, _root_.zpow_neg_one, inv_mul_cancel_left₀ (Units.ne_zero ϖ)]
    exact hw i
  · have : indic s i = 0 := by unfold indic; simp [hi]
    rw [this, neg_zero, zpow_zero, one_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hlt.le) (hw i)

theorem relIndex_preLat_inv_ne_zero {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {s : Finset D}
    {g : GL D k} (hg : ∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') :
    (preLat (g⁻¹).1).relIndex (mLat k D) ≠ 0 := by
  have hdiv : ∀ x : k, valuation k x < 1 → (ϖ : k)⁻¹ * x ∈ 𝒪[k] := by
    intro x hx
    rw [Valuation.mem_integer_iff, map_mul, map_inv₀]
    have hle : valuation k x ≤ valuation k (ϖ : k) := by rw [hϖ]; exact le_uniformizer_iff.2 hx
    have hpos : valuation k (ϖ : k) ≠ 0 := by simp
    calc (valuation k (ϖ : k))⁻¹ * valuation k x ≤ (valuation k (ϖ : k))⁻¹ * valuation k (ϖ : k) :=
          by gcongr
      _ = 1 := inv_mul_cancel₀ hpos
  have hkey : ∀ x : 𝒪[k], x ∈ IsLocalRing.maximalIdeal 𝒪[k] ↔ valuation k (x : k) < 1 := fun x => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
    exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩
  let r : mLat k D →+ (D → 𝓀[k]) :=
    { toFun := fun v i => IsLocalRing.residue 𝒪[k] ⟨(ϖ : k)⁻¹ * v.1 i, hdiv _ (mem_mLat.1 v.2 i)⟩
      map_zero' := by
        funext i
        have h0 : (⟨(ϖ : k)⁻¹ * ((0 : mLat k D) : D → k) i, hdiv _ (mem_mLat.1 (0 : mLat k D).2 i)⟩ : 𝒪[k]) = 0 :=
          Subtype.ext (by simp)
        simp only [h0, map_zero, Pi.zero_apply]
      map_add' := by
        intro v w
        funext i
        simp only [Pi.add_apply]
        rw [← map_add]
        congr 1
        exact Subtype.ext (by simp [mul_add]) }
  have hle : r.ker ≤ (preLat (g⁻¹).1).addSubgroupOf (mLat k D) := by
    intro v hv
    rw [AddMonoidHom.mem_ker] at hv
    rw [AddSubgroup.mem_addSubgroupOf]
    have hu : (fun i => (ϖ : k)⁻¹ * v.1 i) ∈ mLat k D := by
      rw [mem_mLat]
      intro i
      have h0 := congrFun hv i
      have h1 := (IsLocalRing.residue_eq_zero_iff _).1 h0
      exact (hkey _).1 h1
    have e : (ϖ : k) • (fun i => (ϖ : k)⁻¹ * v.1 i) = v.1 := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ (Units.ne_zero ϖ)]
    rw [← e]
    exact smul_mem_preLat_inv hϖ hg _ hu
  have : ((preLat (g⁻¹).1).addSubgroupOf (mLat k D)).FiniteIndex := AddSubgroup.finiteIndex_of_le hle
  exact this.index_ne_zero

theorem card_eq_relIndex_of_reps {G : Type} [AddCommGroup G] (H K : AddSubgroup G) (F : Finset G)
    (hF : ∀ x ∈ F, x ∈ K) (hu : ∀ x ∈ K, ∃! y, y ∈ F ∧ x - y ∈ H) : F.card = H.relIndex K := by
  let f : F → K ⧸ H.addSubgroupOf K := fun y => QuotientAddGroup.mk ⟨y.1, hF y.1 y.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨y, hy⟩ ⟨y', hy'⟩ h
      have h' := QuotientAddGroup.eq.1 h
      rw [AddSubgroup.mem_addSubgroupOf] at h'
      have hyy : y' - y ∈ H := by
        have e : y' - y = -y + y' := by abel
        rw [e]; simpa using h'
      obtain ⟨z, -, hz⟩ := hu y' (hF y' hy')
      have e1 := hz y ⟨hy, hyy⟩
      have e2 := hz y' ⟨hy', by simp⟩
      exact Subtype.ext (e1.trans e2.symm)
    · intro q
      induction q using QuotientAddGroup.induction_on with
      | H x =>
        obtain ⟨y, ⟨hy, hxy⟩, -⟩ := hu x.1 x.2
        refine ⟨⟨y, hy⟩, ?_⟩
        apply QuotientAddGroup.eq.2
        rw [AddSubgroup.mem_addSubgroupOf]
        have e : -y + x.1 = x.1 - y := by abel
        simpa [e] using hxy
  rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card,
    Fintype.card_coe]

theorem relIndex_pi_univ {ι G : Type} [Fintype ι] [AddCommGroup G] (A B : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ A).relIndex (AddSubgroup.pi Set.univ B) = ∏ i, (A i).relIndex (B i) := by
  let g : (∀ i, B i) →+ (AddSubgroup.pi Set.univ B) :=
    { toFun := fun v => ⟨fun i => (v i : G), fun i _ => (v i).2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hg : Function.Surjective g := fun x => ⟨fun i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩, rfl⟩
  have hc : ((AddSubgroup.pi Set.univ A).addSubgroupOf (AddSubgroup.pi Set.univ B)).comap g =
      AddSubgroup.pi Set.univ fun i => (A i).addSubgroupOf (B i) := by
    ext v
    simp [g, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hg, hc]
  simp_rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_pi]

theorem mem_sup_iff_of_mem {V : Type} [AddCommGroup V] {S L large₂ : AddSubgroup V} (h : large₂ ≤ L) {x : V}
    (hx : x ∈ L) : x ∈ S ⊔ large₂ ↔ x ∈ (S ⊓ L) ⊔ large₂ := by
  constructor
  · intro hs
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hs
    have haL : a ∈ L := by
      have e : a = (a + b) - b := by abel
      rw [e]; exact sub_mem hx (h hb)
    exact AddSubgroup.mem_sup.2 ⟨a, ⟨ha, haL⟩, b, hb, rfl⟩
  · exact fun hs => (sup_le_sup_right inf_le_left large₂) hs

variable {A : Type} [Fintype A] [DecidableEq A]

theorem sub_mem_iff (g : GL D k) (ν ν' : Matrix D A k) :
    (∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ) ↔
      ∀ a, (fun i => (ν - ν') i a) ∈ preLat (g⁻¹).1 := by
  constructor
  · rintro ⟨μ, hμ, he⟩ a
    rw [mem_preLat, he]
    have e : (fun i => (g.1 * μ) i a) = g.1 *ᵥ (fun i => μ i a) := rfl
    rw [e, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, mem_mLat]
    exact fun i => hμ i a
  · intro h
    refine ⟨(g⁻¹).1 * (ν - ν'), fun i a => mem_mLat.1 (mem_preLat.1 (h a)) i, ?_⟩
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem cond_iff (m g y κ'' : GL D k) (hκ'' : κ'' ∈ KO k D) (hy : y = m * g * κ'') (ν : Matrix D A k) :
    (∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧ (∀ i a, valuation k (ν₂ i a) < 1) ∧
      m.1 * ν = ν₁ + y.1 * ν₂) ↔ ∀ a, (fun i => ν i a) ∈ preLat m.1 ⊔ preLat (g⁻¹).1 := by
  constructor
  · rintro ⟨ν₁, ν₂, h1, h2, he⟩ a
    have e1 : m.1 *ᵥ (fun i => ν i a) = (fun i => ν₁ i a) + y.1 *ᵥ (fun i => ν₂ i a) := by
      funext i; exact congrArg (fun M : Matrix D A k => M i a) he
    have hmy : (m⁻¹).1 * y.1 = g.1 * κ''.1 := by
      rw [← Units.val_mul, ← Units.val_mul, hy]; congr 1; group
    refine AddSubgroup.mem_sup.2 ⟨(m⁻¹).1 *ᵥ (fun i => ν₁ i a), ?_, (g.1 * κ''.1) *ᵥ (fun i => ν₂ i a), ?_, ?_⟩
    · rw [mem_preLat, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, mem_mLat]
      exact fun i => h1 i a
    · rw [mem_preLat, mulVec_mulVec, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul]
      exact ko_mulVec_mem κ'' hκ'' _ (mem_mLat.2 fun i => h2 i a)
    · calc (m⁻¹).1 *ᵥ (fun i => ν₁ i a) + (g.1 * κ''.1) *ᵥ (fun i => ν₂ i a)
          = (m⁻¹).1 *ᵥ (m.1 *ᵥ (fun i => ν i a)) := by
            rw [e1, mulVec_add, mulVec_mulVec, hmy]
        _ = fun i => ν i a := by
            rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  · intro h
    choose t ht u hu htu using fun a => AddSubgroup.mem_sup.1 (h a)
    let ν₁ : Matrix D A k := fun i a => (m.1 *ᵥ t a) i
    let ν₂ : Matrix D A k := fun i a => ((κ''⁻¹).1 *ᵥ ((g⁻¹).1 *ᵥ u a)) i
    refine ⟨ν₁, ν₂, fun i a => mem_mLat.1 (mem_preLat.1 (ht a)) i,
      fun i a => mem_mLat.1 (ko_mulVec_mem κ''⁻¹ (inv_mem hκ'') _ (mem_preLat.1 (hu a))) i, ?_⟩
    have key : ∀ a, y.1 *ᵥ ((κ''⁻¹).1 *ᵥ ((g⁻¹).1 *ᵥ u a)) = m.1 *ᵥ u a := by
      intro a
      rw [mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
      congr 2
      rw [hy]; group
    ext i a
    have hc : (fun j => ν j a) = t a + u a := (htu a).symm
    show (m.1 *ᵥ (fun j => ν j a)) i = (m.1 *ᵥ t a) i + (y.1 *ᵥ ((κ''⁻¹).1 *ᵥ ((g⁻¹).1 *ᵥ u a))) i
    rw [key, hc, mulVec_add]
    rfl

theorem card_filter_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (m g y : GL D k), (∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') → (∃ κ'' ∈ KO k D, y = m * g * κ'') → ∀ N : Finset (Matrix D A k), ((∀ ν ∈ N, ∀ i a, valuation k (ν i a) < 1) ∧ ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) → ∃! ν', ν' ∈ N ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ) → (N.filter fun ν => ∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧ (∀ i a, valuation k (ν₂ i a) < 1) ∧ m.1 * ν = ν₁ + y.1 * ν₂).card = ((preLat m.1 ⊓ preLat (g⁻¹).1).relIndex (preLat m.1 ⊓ mLat k D)) ^ Fintype.card A ∧ 0 < (preLat m.1 ⊓ preLat (g⁻¹).1).relIndex (preLat m.1 ⊓ mLat k D) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ s m g y hg hy N hN
  obtain ⟨κ'', hκ'', hyeq⟩ := hy
  have hLgL : preLat (g⁻¹).1 ≤ mLat k D := preLat_inv_le hϖ hg
  let W : AddSubgroup (D → k) := (preLat m.1 ⊓ mLat k D) ⊔ preLat (g⁻¹).1
  have hLgW : preLat (g⁻¹).1 ≤ W := le_sup_right
  have hWL : W ≤ mLat k D := sup_le inf_le_right hLgL
  have hidx : (preLat m.1 ⊓ preLat (g⁻¹).1).relIndex (preLat m.1 ⊓ mLat k D) = (preLat (g⁻¹).1).relIndex W := by
    rw [← AddSubgroup.inf_relIndex_right (preLat m.1 ⊓ preLat (g⁻¹).1), AddSubgroup.relIndex_sup_right,
      ← AddSubgroup.inf_relIndex_right (preLat (g⁻¹).1)]
    congr 1
    ext v
    simp only [AddSubgroup.mem_inf]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h2, h3, h4⟩
    · rintro ⟨h2, h3, h4⟩; exact ⟨⟨h3, h2⟩, h3, h4⟩
  have hpos : 0 < (preLat (g⁻¹).1).relIndex W := by
    have h := AddSubgroup.relIndex_mul_relIndex (preLat (g⁻¹).1) W (mLat k D) hLgW hWL
    have h0 := relIndex_preLat_inv_ne_zero hϖ hg
    rw [← h] at h0
    exact Nat.pos_of_ne_zero (left_ne_zero_of_mul h0)
  have hcond : ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) →
      ((∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧ (∀ i a, valuation k (ν₂ i a) < 1) ∧
        m.1 * ν = ν₁ + y.1 * ν₂) ↔ ∀ a, (fun i => ν i a) ∈ W) := by
    intro ν hν
    rw [cond_iff m g y κ'' hκ'' hyeq ν]
    exact forall_congr' fun a => mem_sup_iff_of_mem hLgL (mem_mLat.2 fun i => hν i a)
  let col : Matrix D A k → (A → D → k) := fun ν a i => ν i a
  have hcol : Function.Injective col := fun ν ν' h => by
    funext i a; exact congrFun (congrFun h a) i
  refine ⟨?_, hidx ▸ hpos⟩
  rw [hidx, ← Finset.card_image_of_injective _ hcol]
  refine (card_eq_relIndex_of_reps (AddSubgroup.pi Set.univ fun _ : A => preLat (g⁻¹).1)
    (AddSubgroup.pi Set.univ fun _ : A => W) _ ?_ ?_).trans ?_
  · intro x hx
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.mem_filter] at hν
    rw [AddSubgroup.mem_pi]
    intro a _
    exact (hcond ν (hN.1 ν hν.1)).1 hν.2 a
  · intro x hx
    rw [AddSubgroup.mem_pi] at hx
    let ν : Matrix D A k := fun i a => x a i
    have hνL : ∀ i a, valuation k (ν i a) < 1 := fun i a => mem_mLat.1 (hWL (hx a (Set.mem_univ a))) i
    obtain ⟨ν', ⟨hν'N, μ, hμ, hνμ⟩, huniq⟩ := hN.2 ν hνL
    have hdiff := (sub_mem_iff g ν ν').1 ⟨μ, hμ, hνμ⟩
    refine ⟨col ν', ⟨?_, ?_⟩, ?_⟩
    · refine Finset.mem_image.2 ⟨ν', Finset.mem_filter.2 ⟨hν'N, (hcond ν' (hN.1 ν' hν'N)).2 fun a => ?_⟩, rfl⟩
      have e : (fun i => ν' i a) = x a - (fun i => (ν - ν') i a) := by
        funext i
        show ν' i a = x a i - (x a i - ν' i a)
        ring
      rw [e]
      exact sub_mem (hx a (Set.mem_univ a)) (hLgW (hdiff a))
    · rw [AddSubgroup.mem_pi]
      intro a _
      exact hdiff a
    · rintro z ⟨hz, hxz⟩
      obtain ⟨ν'', hν'', rfl⟩ := Finset.mem_image.1 hz
      rw [Finset.mem_filter] at hν''
      rw [AddSubgroup.mem_pi] at hxz
      exact congrArg col (huniq ν'' ⟨hν''.1, (sub_mem_iff g ν ν'').2 fun a => hxz a (Set.mem_univ a)⟩)
  · rw [relIndex_pi_univ, Finset.prod_const, Finset.card_univ]

end GlobalTheory.LowerHeckeCount

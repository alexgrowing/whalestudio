import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ParHecke.CosetSubL

theorem exists_equiv_map_eq {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (W W' : Submodule F V)
    (h : Module.finrank F W = Module.finrank F W') :
    ∃ e : V ≃ₗ[F] V, W.map e.toLinearMap = W' := by
  obtain ⟨U, hU⟩ := W.exists_isCompl
  obtain ⟨U', hU'⟩ := W'.exists_isCompl
  have h1 := Submodule.finrank_add_eq_of_isCompl hU
  have h2 := Submodule.finrank_add_eq_of_isCompl hU'
  have h3 : Module.finrank F U = Module.finrank F U' := by omega
  let a : W ≃ₗ[F] W' := LinearEquiv.ofFinrankEq _ _ h
  let b : U ≃ₗ[F] U' := LinearEquiv.ofFinrankEq _ _ h3
  let e : V ≃ₗ[F] V := (Submodule.prodEquivOfIsCompl W U hU).symm ≪≫ₗ (a.prodCongr b) ≪≫ₗ
    Submodule.prodEquivOfIsCompl W' U' hU'
  have he : ∀ w : W, e w = a w := by
    intro w
    simp [e]
  refine ⟨e, ?_⟩
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have := he ⟨w, hw⟩
    change e w ∈ W'
    simp only at this
    rw [this]
    exact (a ⟨w, hw⟩).2
  · intro w hw
    refine ⟨a.symm ⟨w, hw⟩, (a.symm ⟨w, hw⟩).2, ?_⟩
    change e _ = w
    rw [he]
    simp

theorem exists_gl_map_eq (O : Type) [CommRing O] [IsLocalRing O] (n : Type) [Fintype n] [DecidableEq n]
    (W W' : Submodule (IsLocalRing.ResidueField O) (n → IsLocalRing.ResidueField O))
    (h : Module.finrank (IsLocalRing.ResidueField O) W =
      Module.finrank (IsLocalRing.ResidueField O) W') :
    ∃ g : GL n O, W.map (g.1.map (IsLocalRing.residue O)).mulVecLin = W' := by
  obtain ⟨e, he⟩ := exists_equiv_map_eq W W' h
  let M : Matrix n n (IsLocalRing.ResidueField O) := LinearMap.toMatrix' e.toLinearMap
  choose A hA using fun i j => IsLocalRing.residue_surjective (R := O) (M i j)
  have hAM : (Matrix.of A).map (IsLocalRing.residue O) = M := by
    ext i j
    exact hA i j
  have hM : M.det ≠ 0 := by
    have : M.det = LinearMap.det e.toLinearMap := LinearMap.det_toMatrix' _
    rw [this]
    exact (LinearEquiv.isUnit_det' e).ne_zero
  have hu : IsUnit (Matrix.of A).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    change ((Matrix.of A).map (IsLocalRing.residue O)).det ≠ 0
    rw [hAM]
    exact hM
  obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  refine ⟨g, ?_⟩
  rw [hg, hAM, ← he]
  congr 1
  exact Matrix.toLin'_toMatrix' e.toLinearMap

theorem exists_range_eq (F : Type) [Field F] (n : Type) [Fintype n] [DecidableEq n] (U : Submodule F (n → F)) :
    ∃ M : Matrix n n F, LinearMap.range M.mulVecLin = U := by
  obtain ⟨U', hU⟩ := U.exists_isCompl
  refine ⟨LinearMap.toMatrix' (U.subtype ∘ₗ Submodule.projectionOnto U U' hU), ?_⟩
  rw [← toLin'_apply', toLin'_toMatrix', LinearMap.range_comp, Submodule.range_projectionOnto, Submodule.map_subtype_top]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n m : Type} [Fintype n] [DecidableEq n]

def projE (F : Type) [Field F] (s : Finset n) : Matrix n n F := diagonal fun i => if i ∈ s then 1 else 0

theorem rank_projE (F : Type) [Field F] (s : Finset n) : (projE F s).rank = s.card := by
  classical
  rw [projE, rank_diagonal]
  rw [Fintype.card_subtype]
  congr 1
  ext i
  by_cases h : i ∈ s <;> simp [h]

abbrev red {a b : Type} (M : Matrix a b 𝒪[k]) : Matrix a b 𝓀[k] := M.map (IsLocalRing.residue 𝒪[k])

abbrev inc {a b : Type} (M : Matrix a b 𝒪[k]) : Matrix a b k := M.map (algebraMap 𝒪[k] k)

abbrev incG (κ : GL n 𝒪[k]) : GL n k := GeneralLinearGroup.map (algebraMap 𝒪[k] k) κ

theorem isUnit_red (κ : GL n 𝒪[k]) : IsUnit (red (k := k) κ.1).det := by
  have : (red (k := k) κ.1).det = IsLocalRing.residue 𝒪[k] κ.1.det := (RingHom.map_det _ _).symm
  rw [this]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 κ.isUnit).map _

def rowKer (s : Finset n) (κ : GL n 𝒪[k]) : Submodule 𝓀[k] (n → 𝓀[k]) :=
  LinearMap.ker (projE 𝓀[k] s * red (κ⁻¹).1).mulVecLin

theorem finrank_rowKer (s : Finset n) (κ : GL n 𝒪[k]) :
    Module.finrank 𝓀[k] (rowKer s κ) + s.card = Fintype.card n := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (projE 𝓀[k] s * red (k := k) (κ⁻¹).1).mulVecLin
  have h2 : (projE 𝓀[k] s * red (k := k) (κ⁻¹).1).rank = s.card := by
    rw [← rank_projE 𝓀[k] s]
    exact rank_mul_eq_left_of_isUnit_det _ _ (isUnit_red κ⁻¹)
  rw [Matrix.rank] at h2
  rw [Module.finrank_fintype_fun_eq_card] at h1
  unfold rowKer
  omega

end GlobalTheory.ParHecke.CosetSubL

namespace GlobalTheory.ParHecke.CosetSubL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n m : Type} [Fintype n] [DecidableEq n]

theorem inv_mul_mem_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (x : 𝒪[k]) :
    (ϖ : k)⁻¹ * (x : k) ∈ 𝒪[k] ↔ IsLocalRing.residue 𝒪[k] x = 0 := by
  rw [mul_comm, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one, Valuation.mem_integer_iff, ← le_uniformizer_iff, ← hϖ,
    map_mul, map_inv₀, mul_inv_le_iff₀ (by rw [hϖ]; exact uniformizer_pos), one_mul]

theorem torus_inv (ϖ : kˣ) (s : Finset n) : (torusElt k n ϖ (indic s))⁻¹ = torusElt k n ϖ (-indic s) := by
  rw [inv_eq_iff_mul_eq_one]
  apply Units.ext
  rw [Units.val_mul, val_torusElt, val_torusElt, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
  congr 1
  ext i
  rw [← zpow_add₀ ϖ.ne_zero]
  simp

theorem torus_inv_mul_int_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset n) (M : Matrix n m 𝒪[k]) :
    (∀ i j, (((torusElt k n ϖ (indic s))⁻¹).1 * inc M) i j ∈ 𝒪[k]) ↔ projE 𝓀[k] s * red M = 0 := by
  rw [torus_inv, val_torusElt, projE, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [diagonal_mul, diagonal_mul]
  by_cases h : i ∈ s
  · have := inv_mul_mem_iff hϖ (M i j)
    simp only [indic, h, Pi.neg_apply, if_true, _root_.zpow_neg, zpow_one, one_mul, map_apply, Matrix.zero_apply]
    exact this
  · simp only [indic, h, Pi.neg_apply, if_false, neg_zero, zpow_zero, one_mul, zero_mul, map_apply, Matrix.zero_apply, iff_true]
    exact (M i j).2

omit [DecidableEq n] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem int_mul {a b : Type} {A : Matrix a n k} {B : Matrix n b k} (hA : ∀ i j, A i j ∈ 𝒪[k]) (hB : ∀ i j, B i j ∈ 𝒪[k]) :
    ∀ i j, (A * B) i j ∈ 𝒪[k] := fun i j => by
  rw [mul_apply]
  exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

theorem int_of_KO {g : GL n k} (hg : g ∈ KO k n) : ∀ i j, g.1 i j ∈ 𝒪[k] := by
  obtain ⟨κ, rfl⟩ := hg
  intro i j
  exact (κ.1 i j).2

theorem KO_of_int {g : GL n k} (hg : ∀ i j, g.1 i j ∈ 𝒪[k]) (hg' : ∀ i j, (g⁻¹).1 i j ∈ 𝒪[k]) : g ∈ KO k n := by
  let A : Matrix n n 𝒪[k] := fun i j => ⟨_, hg i j⟩
  let B : Matrix n n 𝒪[k] := fun i j => ⟨_, hg' i j⟩
  have hA : inc A = g.1 := rfl
  have hB : inc B = (g⁻¹).1 := rfl
  have inj : Function.Injective (inc : Matrix n n 𝒪[k] → Matrix n n k) := map_injective Subtype.val_injective
  have h1 : inc (1 : Matrix n n 𝒪[k]) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext hA⟩
  · rw [h1, inc, Matrix.map_mul]
    change g.1 * (g⁻¹).1 = 1
    simp
  · rw [h1, inc, Matrix.map_mul]
    change (g⁻¹).1 * g.1 = 1
    simp

theorem KO_mul_int_iff {A : Matrix n m k} {g : GL n k} (hg : g ∈ KO k n) :
    (∀ i j, (g.1 * A) i j ∈ 𝒪[k]) ↔ ∀ i j, A i j ∈ 𝒪[k] := by
  refine ⟨fun h => ?_, fun h => int_mul (int_of_KO hg) h⟩
  have := int_mul (int_of_KO (inv_mem hg)) h
  rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this

theorem int_torus {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset n) :
    ∀ i j, (torusElt k n ϖ (indic s)).1 i j ∈ 𝒪[k] := by
  intro i j
  rw [val_torusElt, diagonal_apply]
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  split_ifs with h
  · by_cases h' : i ∈ s
    · simpa [indic, h', Valuation.mem_integer_iff] using hlt.le
    · simp [indic, h']
  · exact zero_mem _

theorem int_coset {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset n) (κ : GL n 𝒪[k]) :
    ∀ i j, (incG κ * torusElt k n ϖ (indic s)).1 i j ∈ 𝒪[k] := by
  rw [Units.val_mul]
  exact int_mul (int_of_KO ⟨κ, rfl⟩) (int_torus hϖ s)

theorem int_iff_rowKer [Fintype m] [DecidableEq m] {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset n) (y₀ : Matrix n m 𝒪[k])
    (κ : GL n 𝒪[k]) :
    (∀ i j, (((incG κ * torusElt k n ϖ (indic s))⁻¹).1 * inc y₀) i j ∈ 𝒪[k]) ↔
      LinearMap.range (red y₀).mulVecLin ≤ rowKer s κ := by
  have e1 : (incG κ * torusElt k n ϖ (indic s))⁻¹ = (torusElt k n ϖ (indic s))⁻¹ * incG κ⁻¹ := by
    rw [_root_.mul_inv_rev]
    congr 1
  have e2 : (incG κ⁻¹).1 * inc y₀ = inc ((κ⁻¹).1 * y₀) := Matrix.map_mul.symm
  have e3 : red ((κ⁻¹).1 * y₀) = red (k := k) (κ⁻¹).1 * red y₀ := Matrix.map_mul
  rw [e1, Units.val_mul, Matrix.mul_assoc, e2, torus_inv_mul_int_iff hϖ, rowKer, LinearMap.range_le_ker_iff,
    ← mulVecLin_mul, e3, ← Matrix.mul_assoc, ← toLin'_apply', map_eq_zero_iff _ toLin'.injective]

theorem int_quot_of_le {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset n) (κ₁ κ₂ : GL n 𝒪[k])
    (h : rowKer s κ₂ ≤ rowKer s κ₁) :
    ∀ i j, ((incG κ₁ * torusElt k n ϖ (indic s))⁻¹ * (incG κ₂ * torusElt k n ϖ (indic s))).1 i j ∈ 𝒪[k] := by
  let y : Matrix n n 𝒪[k] := fun i j => ⟨_, int_coset hϖ s κ₂ i j⟩
  have hy : inc y = (incG κ₂ * torusElt k n ϖ (indic s)).1 := rfl
  rw [Units.val_mul, ← hy, int_iff_rowKer hϖ]
  refine le_trans ?_ h
  rw [← int_iff_rowKer hϖ, hy, ← Units.val_mul, inv_mul_cancel]
  exact int_of_KO (one_mem _)

theorem rowKer_eq_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset n) (κ₁ κ₂ : GL n 𝒪[k]) :
    rowKer s κ₁ = rowKer s κ₂ ↔
      (incG κ₁ * torusElt k n ϖ (indic s))⁻¹ * (incG κ₂ * torusElt k n ϖ (indic s)) ∈ KO k n := by
  constructor
  · intro h
    refine KO_of_int (int_quot_of_le hϖ s κ₁ κ₂ h.ge) ?_
    rw [_root_.mul_inv_rev, inv_inv]
    exact int_quot_of_le hϖ s κ₂ κ₁ h.le
  · intro h
    set t := torusElt k n ϖ (indic s)
    have key : ∀ y : Matrix n n 𝒪[k], LinearMap.range (red y).mulVecLin ≤ rowKer s κ₁ ↔
        LinearMap.range (red y).mulVecLin ≤ rowKer s κ₂ := by
      intro y
      have e : (incG κ₂ * t)⁻¹ = ((incG κ₁ * t)⁻¹ * (incG κ₂ * t))⁻¹ * (incG κ₁ * t)⁻¹ := by group
      rw [← int_iff_rowKer hϖ, ← int_iff_rowKer hϖ, e, Units.val_mul, Matrix.mul_assoc, KO_mul_int_iff (inv_mem h)]
    have key2 : ∀ U : Submodule 𝓀[k] (n → 𝓀[k]), ∃ y : Matrix n n 𝒪[k], LinearMap.range (red y).mulVecLin = U := by
      intro U
      obtain ⟨M, hM⟩ := exists_range_eq 𝓀[k] n U
      choose A hA using fun i j => IsLocalRing.residue_surjective (R := 𝒪[k]) (M i j)
      have hAM : red (k := k) (Matrix.of A) = M := by
        ext i j
        exact hA i j
      exact ⟨Matrix.of A, by rw [hAM, hM]⟩
    apply le_antisymm
    · obtain ⟨y, hy⟩ := key2 (rowKer s κ₁)
      rw [← hy, ← key, hy]
    · obtain ⟨y, hy⟩ := key2 (rowKer s κ₂)
      rw [← hy, key, hy]

theorem exists_rowKer (s : Finset n) (U : Submodule 𝓀[k] (n → 𝓀[k]))
    (hU : Module.finrank 𝓀[k] U + s.card = Fintype.card n) : ∃ κ : GL n 𝒪[k], rowKer s κ = U := by
  have h0 : Module.finrank 𝓀[k] (LinearMap.ker (projE 𝓀[k] s).mulVecLin) + s.card = Fintype.card n := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (projE 𝓀[k] s).mulVecLin
    have h2 := rank_projE 𝓀[k] s
    rw [Matrix.rank] at h2
    rw [Module.finrank_fintype_fun_eq_card] at h1
    omega
  obtain ⟨g, hg⟩ := exists_gl_map_eq 𝒪[k] n U (LinearMap.ker (projE 𝓀[k] s).mulVecLin) (by omega)
  refine ⟨g⁻¹, ?_⟩
  have hinj : Function.Injective (red (k := k) g.1).mulVecLin :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_red g))
  rw [rowKer, inv_inv, mulVecLin_mul, LinearMap.ker_comp, ← hg, Submodule.comap_map_eq_of_injective hinj]

end GlobalTheory.ParHecke.CosetSubL

open GlobalTheory.ParHecke.CosetSubL in

theorem GlobalTheory.ParHecke.CosetSubL.sum_intInd_cosets_up : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D D' : Type) [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D') RK, IsRepsK (torusElt k D' ϖ (indic s)) RK → ∀ y : Matrix D' D k, ((¬ ∀ i j, y i j ∈ 𝒪[k]) → ∑ g ∈ RK, intInd ((g⁻¹).1 * y) = 0) ∧ ∀ y₀ : Matrix D' D 𝒪[k], y = y₀.map (algebraMap 𝒪[k] k) → ∑ g ∈ RK, intInd ((g⁻¹).1 * y) = (Nat.card {U : Submodule 𝓀[k] (D' → 𝓀[k]) // LinearMap.range (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ≤ U ∧ Module.finrank 𝓀[k] U + s.card = Fintype.card D'} : ℂ) := by
  intro k _ _ _ _ D D' _ _ _ _ ϖ hϖ s RK hR y
  classical
  set g₀ := torusElt k D' ϖ (indic s) with hg₀
  have hex : ∀ g : RK, ∃ κ : GL D' 𝒪[k], ∃ κ' ∈ KO k D', g.1 = incG κ * g₀ * κ' := by
    intro g
    obtain ⟨_, ⟨κ, rfl⟩, κ', hκ', e⟩ := hR.1 g.1 g.2
    exact ⟨κ, κ', hκ', e⟩
  choose κ κ' hκ' hg using hex
  constructor
  · intro hy
    refine Finset.sum_eq_zero fun g hgR => ?_
    rw [ParHecke.intInd, if_neg]
    intro h
    apply hy
    have hgi : ∀ i j, g.1 i j ∈ 𝒪[k] := by
      have e : g = incG (κ ⟨g, hgR⟩) * g₀ * κ' ⟨g, hgR⟩ := hg ⟨g, hgR⟩
      rw [e, Units.val_mul]
      exact int_mul (int_coset hϖ s _) (int_of_KO (hκ' _))
    have := int_mul hgi h
    rwa [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul] at this
  · rintro y₀ rfl
    have hint : ∀ g : RK, (∀ i j, ((g.1⁻¹).1 * inc y₀) i j ∈ 𝒪[k]) ↔
        LinearMap.range (red y₀).mulVecLin ≤ rowKer s (κ g) := by
      intro g
      rw [← int_iff_rowKer hϖ, hg g, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc,
        KO_mul_int_iff (inv_mem (hκ' g))]
    have hco : ∀ (g : RK) (c : GL D' 𝒪[k]), g.1⁻¹ * (incG c * g₀) ∈ KO k D' ↔ rowKer s (κ g) = rowKer s c := by
      intro g c
      rw [rowKer_eq_iff hϖ, hg g, _root_.mul_inv_rev, mul_assoc, (KO k D').mul_mem_cancel_left (inv_mem (hκ' g))]
    let f : {g : RK // ∀ i j, ((g.1⁻¹).1 * inc y₀) i j ∈ 𝒪[k]} → {U : Submodule 𝓀[k] (D' → 𝓀[k]) // LinearMap.range (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ≤ U ∧ Module.finrank 𝓀[k] U + s.card = Fintype.card D'} :=
      fun g => ⟨rowKer s (κ g.1), (hint g.1).1 g.2, finrank_rowKer s _⟩
    have hf : Function.Bijective f := by
      constructor
      · intro g₁ g₂ h
        have h' : rowKer s (κ g₁.1) = rowKer s (κ g₂.1) := congrArg Subtype.val h
        have := (hR.2 (incG (κ g₂.1)) ⟨_, rfl⟩).unique ⟨g₁.1.2, (hco _ _).2 h'⟩ ⟨g₂.1.2, (hco _ _).2 rfl⟩
        exact Subtype.ext (Subtype.ext this)
      · rintro ⟨U, hU, hd⟩
        obtain ⟨c, rfl⟩ := exists_rowKer s U hd
        obtain ⟨g, ⟨hgR, hgc⟩, -⟩ := hR.2 (incG c) ⟨_, rfl⟩
        have e := (hco ⟨g, hgR⟩ c).1 hgc
        exact ⟨⟨⟨g, hgR⟩, (hint _).2 (e ▸ hU)⟩, Subtype.ext e⟩
    rw [← Nat.card_eq_of_bijective f hf, ← Finset.sum_coe_sort, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [ParHecke.intInd]
    rw [Finset.sum_boole]

end

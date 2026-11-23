import Mathlib
import GroundTheory.AutomorphicForms.GLnLocal

noncomputable section

namespace GroundTheory.Automorphic

open ValuativeRel Topology Filter Set
open scoped Pointwise Matrix

namespace GLnLocal

variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)

section Algebraic

def glLin (g : GL (Fin n) F) : (Fin n → F) →ₗ[𝒪[F]] (Fin n → F) :=
  (Matrix.toLin' (g : Matrix (Fin n) (Fin n) F)).restrictScalars 𝒪[F]

@[simp]
theorem glLin_apply (g : GL (Fin n) F) (v : Fin n → F) :
    glLin F n g v = (g : Matrix (Fin n) (Fin n) F) *ᵥ v :=
  rfl

def mapSubmodule (g : GL (Fin n) F) (L : Submodule 𝒪[F] (Fin n → F)) :
    Submodule 𝒪[F] (Fin n → F) :=
  L.map (glLin F n g)

theorem mapSubmodule_one (L : Submodule 𝒪[F] (Fin n → F)) : mapSubmodule F n 1 L = L := by
  have : glLin F n 1 = LinearMap.id := LinearMap.ext fun v => by simp
  rw [mapSubmodule, this, Submodule.map_id]

theorem mapSubmodule_mul (g h : GL (Fin n) F) (L : Submodule 𝒪[F] (Fin n → F)) :
    mapSubmodule F n (g * h) L = mapSubmodule F n g (mapSubmodule F n h L) := by
  have : glLin F n (g * h) = glLin F n g ∘ₗ glLin F n h := LinearMap.ext fun v => by
    simp [Matrix.mulVec_mulVec]
  rw [mapSubmodule, mapSubmodule, mapSubmodule, this, Submodule.map_comp]

theorem mapSubmodule_inv_mapSubmodule (g : GL (Fin n) F) (L : Submodule 𝒪[F] (Fin n → F)) :
    mapSubmodule F n g⁻¹ (mapSubmodule F n g L) = L := by
  rw [← mapSubmodule_mul, inv_mul_cancel, mapSubmodule_one]

theorem mapSubmodule_mapSubmodule_inv (g : GL (Fin n) F) (L : Submodule 𝒪[F] (Fin n → F)) :
    mapSubmodule F n g (mapSubmodule F n g⁻¹ L) = L := by
  rw [← mapSubmodule_mul, mul_inv_cancel, mapSubmodule_one]

theorem isLattice_mapSubmodule (g : GL (Fin n) F) (L : Submodule 𝒪[F] (Fin n → F))
    [L.IsLattice F] : (mapSubmodule F n g L).IsLattice F where
  fg := (Submodule.IsLattice.fg (A := F) (M := L)).map _
  span_eq_top := by
    have : ((mapSubmodule F n g L : Submodule 𝒪[F] (Fin n → F)) : Set (Fin n → F)) =
        Matrix.toLin' (g : Matrix (Fin n) (Fin n) F) '' (L : Set (Fin n → F)) := by
      rw [mapSubmodule, Submodule.map_coe]
      rfl
    rw [this, Submodule.span_image, Submodule.IsLattice.span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top]
    intro v
    refine ⟨((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

def standardLattice : Submodule 𝒪[F] (Fin n → F) where
  carrier := {v | ∀ i, v i ∈ 𝒪[F]}
  add_mem' ha hb i := Subring.add_mem _ (ha i) (hb i)
  zero_mem' _ := Subring.zero_mem _
  smul_mem' c _ hv i := Subring.mul_mem _ c.2 (hv i)

theorem mem_standardLattice {v : Fin n → F} : v ∈ standardLattice F n ↔ ∀ i, v i ∈ 𝒪[F] :=
  Iff.rfl

theorem single_mem_standardLattice (j : Fin n) : Pi.single j (1 : F) ∈ standardLattice F n := by
  intro i
  rw [Pi.single_apply]
  split_ifs <;> simp

theorem standardLattice_eq_span :
    standardLattice F n = Submodule.span 𝒪[F] (Set.range fun j => Pi.single j (1 : F)) := by
  refine le_antisymm (fun v hv => ?_) (Submodule.span_le.mpr ?_)
  · have : v = ∑ j, (⟨v j, hv j⟩ : 𝒪[F]) • (Pi.single j (1 : F) : Fin n → F) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rintro _ ⟨j, rfl⟩
    exact single_mem_standardLattice F n j

instance isLattice_standardLattice : (standardLattice F n).IsLattice F where
  fg := by
    rw [standardLattice_eq_span]
    exact Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    refine eq_top_iff.mpr ((Pi.basisFun F (Fin n)).span_eq.symm.le.trans (Submodule.span_mono ?_))
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply]
    exact single_mem_standardLattice F n j

theorem mulVec_mem_standardLattice {A : Matrix (Fin n) (Fin n) F} (hA : ∀ i j, A i j ∈ 𝒪[F])
    {v : Fin n → F} (hv : v ∈ standardLattice F n) : A *ᵥ v ∈ standardLattice F n := fun i => by
  rw [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hv j)

theorem mapSubmodule_le_standardLattice_iff {g : GL (Fin n) F} :
    mapSubmodule F n g (standardLattice F n) ≤ standardLattice F n ↔ ∀ i j, g i j ∈ 𝒪[F] := by
  constructor
  · intro h i j
    have := h (Submodule.mem_map_of_mem (f := glLin F n g) (single_mem_standardLattice F n j)) i
    rwa [glLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] at this
  · rintro h _ ⟨v, hv, rfl⟩
    exact mulVec_mem_standardLattice F n h hv

theorem mapSubmodule_standardLattice_eq_iff {g : GL (Fin n) F} :
    mapSubmodule F n g (standardLattice F n) = standardLattice F n ↔ g ∈ integralGL F n := by
  rw [mem_integralGL_iff]
  constructor
  · intro h
    refine ⟨(mapSubmodule_le_standardLattice_iff F n).mp h.le,
      (mapSubmodule_le_standardLattice_iff F n).mp ?_⟩
    conv_lhs => rw [← h]
    rw [mapSubmodule_inv_mapSubmodule]
  · rintro ⟨h1, h2⟩
    refine le_antisymm ((mapSubmodule_le_standardLattice_iff F n).mpr h1) ?_
    conv_lhs => rw [← mapSubmodule_mapSubmodule_inv F n g (standardLattice F n)]
    exact Submodule.map_mono ((mapSubmodule_le_standardLattice_iff F n).mpr h2)

def Lattice : Type _ := {L : Submodule 𝒪[F] (Fin n → F) // L.IsLattice F}

instance (L : Lattice F n) : L.1.IsLattice F := L.2

instance : MulAction (GL (Fin n) F) (Lattice F n) where
  smul g L := ⟨mapSubmodule F n g L.1, isLattice_mapSubmodule F n g L.1⟩
  one_smul L := Subtype.ext (mapSubmodule_one F n L.1)
  mul_smul g h L := Subtype.ext (mapSubmodule_mul F n g h L.1)

@[simp]
theorem coe_smul (g : GL (Fin n) F) (L : Lattice F n) :
    (g • L).1 = mapSubmodule F n g L.1 :=
  rfl

def standard : Lattice F n := ⟨standardLattice F n, inferInstance⟩

theorem smul_standard_eq_iff {g : GL (Fin n) F} :
    g • standard F n = standard F n ↔ g ∈ integralGL F n := by
  rw [← mapSubmodule_standardLattice_eq_iff]
  exact Subtype.ext_iff

theorem stabilizer_standard :
    MulAction.stabilizer (GL (Fin n) F) (standard F n) = integralGL F n := by
  ext g
  rw [MulAction.mem_stabilizer_iff, smul_standard_eq_iff]

theorem smul_standard_eq_smul_standard_iff {g h : GL (Fin n) F} :
    g • standard F n = h • standard F n ↔ g⁻¹ * h ∈ integralGL F n := by
  rw [eq_comm, ← inv_smul_eq_iff, smul_smul, smul_standard_eq_iff]

section MaximalCompact

theorem transvection_mem_integer {i j : Fin n} {c : F} (hc : c ∈ 𝒪[F]) (a b : Fin n) :
    Matrix.transvection i j c a b ∈ 𝒪[F] := by
  rw [Matrix.transvection, Matrix.add_apply]
  refine Subring.add_mem _ ?_ ?_
  · rw [Matrix.one_apply]
    split_ifs <;> simp
  · rw [Matrix.single_apply]
    split_ifs
    · exact hc
    · exact Subring.zero_mem _

def transvectionGL {i j : Fin n} (hij : i ≠ j) : GL (Fin n) F :=
  ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
    by rw [Matrix.transvection_mul_transvection_same _ _ hij, add_neg_cancel,
      Matrix.transvection_zero],
    by rw [Matrix.transvection_mul_transvection_same _ _ hij, neg_add_cancel,
      Matrix.transvection_zero]⟩

theorem transvectionGL_mem {i j : Fin n} (hij : i ≠ j) : transvectionGL F n hij ∈ integralGL F n :=
  (mem_integralGL_iff F n).mpr ⟨transvection_mem_integer F n (Subring.one_mem _),
    transvection_mem_integer F n (Subring.neg_mem _ (Subring.one_mem _))⟩

theorem conj_mem_integralGL_of_conj_inv_mem {g : GL (Fin n) F}
    (hg : ∀ k ∈ integralGL F n, g⁻¹ * k * g ∈ integralGL F n) {k : GL (Fin n) F}
    (hk : k ∈ integralGL F n) : g * k * g⁻¹ ∈ integralGL F n := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · exact (mem_integralGL_iff F n).mpr ⟨fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  set A : Matrix (Fin n) (Fin n) F := (g : Matrix (Fin n) (Fin n) F) with hAdef
  set B : Matrix (Fin n) (Fin n) F := ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    with hBdef
  have hAB : A * B = 1 := Units.mul_inv g
  have hBA : B * A = 1 := Units.inv_mul g
  obtain ⟨⟨j₀, k₀⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun p : Fin n × Fin n => valuation F (A p.1 p.2)) Finset.univ_nonempty
  set a := A j₀ k₀ with ha_def
  have hmax' : ∀ i j, valuation F (A i j) ≤ valuation F a := fun i j =>
    hmax (i, j) (Finset.mem_univ _)
  have ha : a ≠ 0 := by
    intro h0
    have hA0 : A = 0 := Matrix.ext fun i j => by
      have := hmax' i j
      rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
      exact this
    have := congrFun (congrFun hAB j₀) j₀
    rw [hA0, zero_mul, Matrix.zero_apply, Matrix.one_apply_eq] at this
    exact zero_ne_one this
  have hva : 0 < valuation F a := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr ha)

  have hconj : ∀ k ∈ integralGL F n, B * (k : Matrix (Fin n) (Fin n) F) * A ∈ integralMatrices F n :=
    fun k hk => (mem_integralMatrices F n).mpr ((mem_integralGL_iff F n).mp (hg k hk)).1
  have hsingle_ne : ∀ i t : Fin n, i ≠ t →
      B * Matrix.single i t (1 : F) * A ∈ integralMatrices F n := by
    intro i t hit
    have h := hconj _ (transvectionGL_mem F n hit)
    have : B * Matrix.single i t (1 : F) * A =
        B * ((transvectionGL F n hit : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A - 1 := by
      change _ = B * Matrix.transvection i t 1 * A - 1
      rw [Matrix.transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hBA,
        add_sub_cancel_left]
    rw [this]
    exact Subring.sub_mem _ h (Subring.one_mem _)
  have hsingle : ∀ i, B * Matrix.single i j₀ (1 : F) * A ∈ integralMatrices F n := by
    intro i
    by_cases hi : i = j₀
    · subst hi
      by_cases ht : ∃ t, t ≠ i
      · obtain ⟨t, ht⟩ := ht
        have : B * Matrix.single i i (1 : F) * A =
            (B * Matrix.single i t (1 : F) * A) * (B * Matrix.single t i (1 : F) * A) := by
          have hs : Matrix.single i i (1 : F) = Matrix.single i t 1 * Matrix.single t i 1 := by
            rw [Matrix.single_mul_single_same, mul_one]
          rw [hs]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc A B, hAB, Matrix.one_mul]
        rw [this]
        exact Subring.mul_mem _ (hsingle_ne i t (Ne.symm ht)) (hsingle_ne t i ht)
      · push Not at ht
        have h1 : Matrix.single i i (1 : F) = 1 := Matrix.ext fun x y => by
          rw [ht x, ht y, Matrix.single_apply, Matrix.one_apply_eq]
          simp
        rw [h1, Matrix.mul_one, hBA]
        exact Subring.one_mem _
    · exact hsingle_ne i j₀ hi

  have hB' : a • B ∈ integralMatrices F n := by
    refine (mem_integralMatrices F n).mpr fun l i => ?_
    have h := (mem_integralMatrices F n).mp (hsingle i) l k₀
    have : (B * Matrix.single i j₀ (1 : F) * A) l k₀ = B l i * a := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j₀]
      · rw [Matrix.mul_single_apply_same, mul_one]
      · intro x _ hx
        rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hx, zero_mul]
      · simp
    rw [this] at h
    rw [Matrix.smul_apply, smul_eq_mul, mul_comm]
    exact h
  have hA' : a⁻¹ • A ∈ integralMatrices F n := by
    refine (mem_integralMatrices F n).mpr fun i j => ?_
    rw [Matrix.smul_apply, smul_eq_mul, Valuation.mem_integer_iff, map_mul, map_inv₀,
      inv_mul_le_iff₀ hva, mul_one]
    exact hmax' i j

  have hmain : ∀ k' ∈ integralGL F n,
      ((g * k' * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ∈ integralMatrices F n := by
    intro k' hk'
    have hk'' : (k' : Matrix (Fin n) (Fin n) F) ∈ integralMatrices F n :=
      (mem_integralMatrices F n).mpr ((mem_integralGL_iff F n).mp hk').1
    have : ((g * k' * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        a⁻¹ • A * (k' : Matrix (Fin n) (Fin n) F) * (a • B) := by
      rw [Units.val_mul, Units.val_mul]
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ ha, one_smul]
      rfl
    rw [this]
    exact Subring.mul_mem _ (Subring.mul_mem _ hA' hk'') hB'
  refine (mem_integralGL_iff F n).mpr ⟨(mem_integralMatrices F n).mp (hmain k hk), ?_⟩
  have : (g * k * g⁻¹)⁻¹ = g * k⁻¹ * g⁻¹ := by group
  rw [this]
  exact (mem_integralMatrices F n).mp (hmain _ (inv_mem hk))

end MaximalCompact

end Algebraic

section Topological

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_smul_standard (L : Lattice F n) : ∃ g : GL (Fin n) F, g • standard F n = L := by
  obtain ⟨L, hL⟩ := L
  let b := Module.Free.chooseBasis 𝒪[F] L
  let B := b.extendOfIsLattice F
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex 𝒪[F] L) = n := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  let M : Matrix (Fin n) (Fin n) F := (Pi.basisFun F (Fin n)).toMatrix (B.reindex e)
  let : Invertible M := (Pi.basisFun F (Fin n)).invertibleToMatrix (B.reindex e)
  refine ⟨unitOfInvertible M, Subtype.ext ?_⟩
  have hspan : Submodule.span 𝒪[F] (Set.range fun k => (b k : Fin n → F)) = L := by
    have := congrArg (Submodule.map L.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at this
    exact this
  have hcol : ∀ j, glLin F n (unitOfInvertible M) (Pi.single j 1) = (b (e.symm j) : Fin n → F) := by
    intro j
    ext i
    rw [glLin_apply, show ((unitOfInvertible M : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = M
      from rfl, Matrix.mulVec_single_one, Matrix.col_apply]
    simp [M, Module.Basis.toMatrix_apply, B]
  have hfun : (glLin F n (unitOfInvertible M) ∘ fun j => Pi.single j (1 : F)) =
      (fun k => (b k : Fin n → F)) ∘ e.symm := funext hcol
  change mapSubmodule F n _ (standardLattice F n) = L
  rw [standardLattice_eq_span, mapSubmodule, Submodule.map_span, ← Set.range_comp, hfun,
    e.symm.surjective.range_comp, hspan]

def quotientEquivLattice : GL (Fin n) F ⧸ integralGL F n ≃ Lattice F n :=
  Equiv.ofBijective
    (Quotient.lift (fun g : GL (Fin n) F => g • standard F n) fun a b h => by
      have h' : (a : GL (Fin n) F ⧸ integralGL F n) = b := Quotient.sound h
      rw [QuotientGroup.eq] at h'
      exact (smul_standard_eq_smul_standard_iff F n).mpr h')
    ⟨fun x y => Quotient.inductionOn₂ x y fun a b h =>
      (QuotientGroup.eq (s := integralGL F n)).mpr ((smul_standard_eq_smul_standard_iff F n).mp h),
    fun L => (exists_smul_standard F n L).elim fun g hg =>
      ⟨(g : GL (Fin n) F ⧸ integralGL F n), hg⟩⟩

@[simp]
theorem quotientEquivLattice_mk (g : GL (Fin n) F) :
    quotientEquivLattice F n (g : GL (Fin n) F ⧸ integralGL F n) = g • standard F n :=
  rfl

theorem quotientEquivLattice_smul (g : GL (Fin n) F) (x : GL (Fin n) F ⧸ integralGL F n) :
    quotientEquivLattice F n (g • x) = g • quotientEquivLattice F n x := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [MulAction.Quotient.smul_mk, quotientEquivLattice_mk, quotientEquivLattice_mk, smul_eq_mul,
      mul_smul]

end Topological

section Compact

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem eventually_pow_mul_mem (x : F) :
    ∀ᶠ m in atTop, (uniformizer F : F) ^ m * x ∈ 𝒪[F] := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx' : valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨m, hm⟩ := exists_pow_lt₀ (valuation_uniformizer_lt_one F) (Units.mk0 _ hx')⁻¹
  have hm' : valuation F (uniformizer F : F) ^ m ≤ (valuation F x)⁻¹ := by simpa using hm.le
  refine eventually_atTop.mpr ⟨m, fun m' hmm' => ?_⟩
  rw [Valuation.mem_integer_iff, map_mul, map_pow]
  calc valuation F (uniformizer F : F) ^ m' * valuation F x
      ≤ (valuation F x)⁻¹ * valuation F x :=
        mul_le_mul' ((pow_le_pow_right_of_le_one' (valuation_uniformizer_lt_one F).le hmm').trans
          hm') le_rfl
    _ = 1 := inv_mul_cancel₀ hx'

theorem exists_pow_mul_mem_of_isCompact {S : Set (GL (Fin n) F)} (hS : IsCompact S) :
    ∃ m : ℕ, ∀ g ∈ S, ∀ i j, (uniformizer F : F) ^ m * g i j ∈ 𝒪[F] := by
  let U : ℕ → Set (GL (Fin n) F) := fun m => {g | ∀ i j, (uniformizer F : F) ^ m * g i j ∈ 𝒪[F]}
  have hU : ∀ m, IsOpen (U m) := fun m => by
    have : U m = ⋂ i, ⋂ j,
        (fun g : GL (Fin n) F => (uniformizer F : F) ^ m * g i j) ⁻¹' (𝒪[F] : Set F) := by
      ext g
      simp [U]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      Valuation.isOpen_integer.preimage (continuous_const.mul (continuous_entry F n i j))
  have hcover : S ⊆ ⋃ m, U m := fun g _ => by
    have : ∀ᶠ m in atTop, ∀ i j, (uniformizer F : F) ^ m * g i j ∈ 𝒪[F] :=
      eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_pow_mul_mem F (g i j)
    obtain ⟨m, hm⟩ := this.exists
    exact Set.mem_iUnion.mpr ⟨m, hm⟩
  have hmono : Monotone U := fun m m' h g hg i j => by
    have : (uniformizer F : F) ^ m' * g i j =
        (uniformizer F : F) ^ (m' - m) * ((uniformizer F : F) ^ m * g i j) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel h]
    rw [this]
    exact Subring.mul_mem _ (Subring.pow_mem _ (uniformizer F).2 _) (hg i j)
  obtain ⟨m, hm⟩ := hS.elim_directed_cover U hU hcover hmono.directed_le
  exact ⟨m, fun g hg => hm hg⟩

theorem exists_conj_le_integralGL {H : Subgroup (GL (Fin n) F)}
    (hH : IsCompact (H : Set (GL (Fin n) F))) :
    ∃ g : GL (Fin n) F, ∀ h ∈ H, g⁻¹ * h * g ∈ integralGL F n := by
  obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_isCompact F n hH
  have hϖ : (uniformizer F : F) ^ m ≠ 0 :=
    pow_ne_zero _ fun h => valuation_uniformizer_ne_zero F (by rw [h, map_zero])
  let a : Fˣ := Units.mk0 _ hϖ
  let S : Set (Fin n → F) :=
    ⋃ h ∈ H, (mapSubmodule F n h (standardLattice F n) : Set (Fin n → F))
  let L : Submodule 𝒪[F] (Fin n → F) := Submodule.span 𝒪[F] S

  have hLa : L ≤ a⁻¹ • standardLattice F n := by
    rw [Submodule.span_le]
    intro v hv
    obtain ⟨h, hh, hv⟩ := Set.mem_iUnion₂.mp hv
    rw [SetLike.mem_coe, mapSubmodule, Submodule.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [SetLike.mem_coe, ← inv_smul_smul a (glLin F n h w)]
    refine Submodule.smul_mem_pointwise_smul _ _ _ ((mem_standardLattice F n).mpr fun i => ?_)
    change (uniformizer F : F) ^ m * ∑ j, h i j * w j ∈ 𝒪[F]
    rw [Finset.mul_sum]
    refine Subring.sum_mem _ fun j _ => ?_
    rw [← mul_assoc]
    exact Subring.mul_mem _ (hm h hh i j) (hw j)
  have hfg : L.FG :=
    Submodule.FG.of_le (Submodule.IsLattice.fg (A := F) (M := a⁻¹ • standardLattice F n)) hLa
  have hstd : standardLattice F n ≤ L := fun v hv => Submodule.subset_span
    (Set.mem_iUnion₂.mpr ⟨1, H.one_mem, by rw [mapSubmodule_one]; exact hv⟩)
  have hLlat : L.IsLattice F := Submodule.IsLattice.of_le_of_isLattice_of_fg F hstd hfg

  have hstab_le : ∀ h ∈ H, mapSubmodule F n h L ≤ L := by
    intro h hh
    rw [mapSubmodule, Submodule.map_span_le]
    intro v hv
    obtain ⟨h', hh', hv⟩ := Set.mem_iUnion₂.mp hv
    refine Submodule.subset_span (Set.mem_iUnion₂.mpr ⟨h * h', H.mul_mem hh hh', ?_⟩)
    rw [SetLike.mem_coe, mapSubmodule_mul]
    exact Submodule.mem_map_of_mem hv
  have hstab : ∀ h ∈ H, mapSubmodule F n h L = L := fun h hh =>
    le_antisymm (hstab_le h hh) (by
      have := Submodule.map_mono (f := glLin F n h) (hstab_le h⁻¹ (H.inv_mem hh))
      change mapSubmodule F n h (mapSubmodule F n h⁻¹ L) ≤ mapSubmodule F n h L at this
      rwa [mapSubmodule_mapSubmodule_inv] at this)
  obtain ⟨g, hg⟩ := exists_smul_standard F n ⟨L, hLlat⟩
  have hgL : mapSubmodule F n g (standardLattice F n) = L := congrArg Subtype.val hg
  refine ⟨g, fun h hh => (mapSubmodule_standardLattice_eq_iff F n).mp ?_⟩
  rw [mapSubmodule_mul, mapSubmodule_mul, hgL, hstab h hh, ← hgL, mapSubmodule_inv_mapSubmodule]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem mem_map_conj {g x : GL (Fin n) F} {H : Subgroup (GL (Fin n) F)} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g⁻¹ * (MulAut.conj g).toMonoidHom y * g = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [this]
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem isCompact_map_conj (g : GL (Fin n) F) {H : Subgroup (GL (Fin n) F)}
    (hH : IsCompact (H : Set (GL (Fin n) F))) :
    IsCompact (H.map (MulAut.conj g).toMonoidHom : Set (GL (Fin n) F)) := by
  rw [Subgroup.coe_map]
  refine hH.image ?_
  have : ⇑(MulAut.conj g).toMonoidHom = fun x => g * x * g⁻¹ := rfl
  rw [this]
  fun_prop

theorem eq_integralGL_of_isCompact_of_le {H : Subgroup (GL (Fin n) F)}
    (hH : IsCompact (H : Set (GL (Fin n) F))) (hle : integralGL F n ≤ H) :
    H = integralGL F n := by
  obtain ⟨g, hg⟩ := exists_conj_le_integralGL F n hH
  refine le_antisymm (fun h hh => ?_) hle
  have h1 := conj_mem_integralGL_of_conj_inv_mem F n (fun k hk => hg k (hle hk)) (hg h hh)
  have : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
  rwa [this] at h1

def IsMaximalCompact {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G) : Prop :=
  IsCompact (H : Set G) ∧ ∀ H' : Subgroup G, IsCompact (H' : Set G) → H ≤ H' → H' = H

theorem isMaximalCompact_integralGL : IsMaximalCompact (integralGL F n) :=
  ⟨isCompact_integralGL F n, fun _ hH' hle => eq_integralGL_of_isCompact_of_le F n hH' hle⟩

theorem isMaximalCompact_iff {H : Subgroup (GL (Fin n) F)} :
    IsMaximalCompact H ↔ ∃ g : GL (Fin n) F, H = (integralGL F n).map (MulAut.conj g).toMonoidHom := by
  constructor
  · rintro ⟨hc, hmax⟩
    obtain ⟨g, hg⟩ := exists_conj_le_integralGL F n hc
    refine ⟨g, (hmax _ (isCompact_map_conj F n g (isCompact_integralGL F n))
      fun h hh => (mem_map_conj F n).mpr (hg h hh)).symm⟩
  · rintro ⟨g, rfl⟩
    refine ⟨isCompact_map_conj F n g (isCompact_integralGL F n), fun H' hH' hle => ?_⟩

    have hK : integralGL F n ≤ H'.map (MulAut.conj g⁻¹).toMonoidHom := fun k hk => by
      rw [mem_map_conj, inv_inv]
      have : g * k * g⁻¹ ∈ (integralGL F n).map (MulAut.conj g).toMonoidHom := by
        rw [mem_map_conj]
        have : g⁻¹ * (g * k * g⁻¹) * g = k := by group
        rwa [this]
      exact hle this
    have heq := eq_integralGL_of_isCompact_of_le F n (isCompact_map_conj F n g⁻¹ hH') hK
    refine le_antisymm (fun h hh => ?_) hle
    rw [mem_map_conj]
    have : g⁻¹ * h * g ∈ H'.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [mem_map_conj, inv_inv]
      have : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
      rwa [this]
    rwa [heq] at this

end Compact

end GLnLocal

end GroundTheory.Automorphic

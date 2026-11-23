import Development.WeilBound.ThetaLifts.SphericalLattices.IndexComapOfCover

noncomputable section

namespace PositivityTheory.Sph.M2.ZC

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {c : L →+* L} {q : ℕ} {m : ℕ}

def IntM {α β : Type} (X : Matrix α β L) : Prop := ∀ i j, X i j ∈ intL L

theorem IntM.mul {α β γ : Type} [Fintype β] {X : Matrix α β L} {Y : Matrix β γ L} (hX : IntM X) (hY : IntM Y) :
    IntM (X * Y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)

theorem IntM.conjT (h : IsUnramInv ϖ c q) {α β : Type} {X : Matrix α β L} (hX : IntM X) : IntM (X.map c)ᵀ := by
  intro i j
  exact c_int h (hX j i)

theorem intM_one {α : Type} [DecidableEq α] : IntM (1 : Matrix α α L) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem intM_zero {α β : Type} : IntM (0 : Matrix α β L) := by
  intro i j
  exact zero_mem _

theorem intM_fromBlocks {α : Type} {a b c' d : Matrix α α L} :
    IntM (fromBlocks a b c' d) ↔ IntM a ∧ IntM b ∧ IntM c' ∧ IntM d := by
  constructor
  · intro hM
    exact ⟨fun i j => hM (Sum.inl i) (Sum.inl j), fun i j => hM (Sum.inl i) (Sum.inr j),
      fun i j => hM (Sum.inr i) (Sum.inl j), fun i j => hM (Sum.inr i) (Sum.inr j)⟩
  · rintro ⟨ha, hb, hc, hd⟩ i j
    rcases i with i | i <;> rcases j with j | j
    exacts [ha i j, hb i j, hc i j, hd i j]

theorem mem_IntGL {g : GL (Fin m ⊕ Fin m) L} : g ∈ IntGL L m ↔ IntM g.val ∧ IntM (g⁻¹).val := by
  constructor
  · intro hg
    obtain ⟨g', rfl⟩ := MonoidHom.mem_range.mp hg
    exact ⟨fun i j => (g'.val i j).2, fun i j => ((g'⁻¹).val i j).2⟩
  · rintro ⟨h1, h2⟩
    refine MonoidHom.mem_range.mpr
      ⟨⟨Matrix.of fun i j => ⟨g.val i j, h1 i j⟩, Matrix.of fun i j => ⟨(g⁻¹).val i j, h2 i j⟩, ?_, ?_⟩, ?_⟩
    · ext i j
      have e := congrFun (congrFun (Units.mul_inv g) i) j
      rw [Matrix.mul_apply] at e
      rw [Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum]
      simp only [MulMemClass.coe_mul, Matrix.of_apply]
      rw [e, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    · ext i j
      have e := congrFun (congrFun (Units.inv_mul g) i) j
      rw [Matrix.mul_apply] at e
      rw [Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum]
      simp only [MulMemClass.coe_mul, Matrix.of_apply]
      rw [e, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    · ext i j
      rfl

theorem inv_of_iso (h : IsUnramInv ϖ c q) {g : GL (Fin m ⊕ Fin m) L} (hg : Iso c (Wm L (Fin m)) (Wm L (Fin m)) g.val) :
    (g⁻¹).val = Wm L (Fin m) * (g.val.map c)ᵀ * Wm L (Fin m) := by
  have hcc : ∀ y, c (c y) = y := h.1
  have hW : (Wm L (Fin m)).map c = Wm L (Fin m) := by
    show (fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).map c = fromBlocks 0 1 1 0
    rw [Matrix.fromBlocks_map]
    simp
  have hgg : (g.val.map c).map c = g.val := by
    rw [Matrix.map_map]
    ext i j
    exact hcc _
  have hg' : g.valᵀ * Wm L (Fin m) * g.val.map c = Wm L (Fin m) := hg
  have h2 : (g.val.map c)ᵀ * Wm L (Fin m) * g.val = Wm L (Fin m) := by
    have e := congrArg (fun M => M.map c) hg'
    rw [Matrix.map_mul, Matrix.map_mul, hW, hgg, Matrix.transpose_map] at e
    exact e
  apply Units.inv_eq_of_mul_eq_one_left
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (g.val.map c)ᵀ, h2, Wm_mul_self]

theorem mem_KPW (h : IsUnramInv ϖ c q) {g : GL (Fin m ⊕ Fin m) L} :
    g ∈ KPW L c m ↔ g ∈ GW L c m ∧ g.val.toBlocks₂₁ = 0 ∧ IntM g.val := by
  have hB : g ∈ GlobalTheory.LGrp.blockQ L (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m)) ↔ g.val.toBlocks₂₁ = 0 := by
    show (g.val).BlockTriangular (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m)) ↔ _
    constructor
    · intro hb
      ext i j
      exact @hb (Sum.inr i) (Sum.inl j) (show (0:ℕ) < 1 from Nat.one_pos)
    · intro h0 i j hij
      rcases i with i | i <;> rcases j with j | j
      · exact absurd hij (lt_irrefl _)
      · exact absurd hij (Nat.not_lt_zero _)
      · exact congrFun (congrFun h0 i) j
      · exact absurd hij (lt_irrefl _)
  have hWint : IntM (Wm L (Fin m)) := by
    show IntM (fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)
    exact intM_fromBlocks.mpr ⟨intM_zero, intM_one, intM_one, intM_zero⟩
  show g ∈ (GW L c m ⊓ GlobalTheory.LGrp.blockQ L (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m))) ⊓ (GW L c m ⊓ IntGL L m) ↔ _
  simp only [Subgroup.mem_inf, hB, mem_IntGL]
  constructor
  · rintro ⟨⟨hG, hC⟩, -, hI, -⟩
    exact ⟨hG, hC, hI⟩
  · rintro ⟨hG, hC, hI⟩
    refine ⟨⟨hG, hC⟩, hG, hI, ?_⟩
    rw [inv_of_iso h hG]
    exact IntM.mul (IntM.mul hWint (IntM.conjT h hI)) hWint

theorem zW_mem (h : IsUnramInv ϖ c q) {x : Lˣ} (hx : (x : L) = ϖ) : zW L m x ∈ GW L c m := by
  have hcx : c (x : L) = x := by rw [hx]; exact h.2.2.1
  have hx0 : (x : L) ≠ 0 := x.ne_zero
  have hcx' : c (x : L)⁻¹ = (x : L)⁻¹ := by rw [map_inv₀, hcx]
  show (fromBlocks ((x : L) • (1 : Matrix (Fin m) (Fin m) L)) 0 0 (((x⁻¹ : Lˣ) : L) • 1))ᵀ * fromBlocks 0 1 1 0 *
      (fromBlocks ((x : L) • (1 : Matrix (Fin m) (Fin m) L)) 0 0 (((x⁻¹ : Lˣ) : L) • 1)).map c = fromBlocks 0 1 1 0
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Units.val_inv_eq_inv_val, Matrix.smul_one_eq_diagonal, Matrix.diagonal_map, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, hcx, hcx', hx0]

theorem conj_val (x : Lˣ) (g : GL (Fin m ⊕ Fin m) L) :
    ((zW L m x)⁻¹ * g * zW L m x).val = fromBlocks g.val.toBlocks₁₁ (((x : L)⁻¹ * (x : L)⁻¹) • g.val.toBlocks₁₂)
      (((x : L) * x) • g.val.toBlocks₂₁) g.val.toBlocks₂₂ := by
  have hx0 : (x : L) ≠ 0 := x.ne_zero
  have hg : g.val = fromBlocks g.val.toBlocks₁₁ g.val.toBlocks₁₂ g.val.toBlocks₂₁ g.val.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks _).symm
  show fromBlocks (((x⁻¹ : Lˣ) : L) • (1 : Matrix (Fin m) (Fin m) L)) 0 0 ((x : L) • 1) * g.val *
      fromBlocks ((x : L) • (1 : Matrix (Fin m) (Fin m) L)) 0 0 (((x⁻¹ : Lˣ) : L) • 1) = _
  conv_lhs => rw [hg]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Units.val_inv_eq_inv_val, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hx0]

theorem mem_conj (h : IsUnramInv ϖ c q) {x : Lˣ} (hx : (x : L) = ϖ) {g : GL (Fin m ⊕ Fin m) L} :
    g ∈ (KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom ↔ g ∈ GW L c m ∧ g.val.toBlocks₂₁ = 0 ∧
      IntM g.val.toBlocks₁₁ ∧ IntM g.val.toBlocks₂₂ ∧ g.val.toBlocks₁₂ ∈ MA m (ϖ⁻¹ * ϖ⁻¹) := by
  have hz := zW_mem (m := m) h hx
  have key : g ∈ (KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom ↔
      (zW L m x)⁻¹ * g * zW L m x ∈ KPW L c m := by
    constructor
    · intro hg
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
      simpa [mul_assoc] using hk
    · intro hk
      exact Subgroup.mem_map.mpr ⟨_, hk, by simp [mul_assoc]⟩
  have hGW : (zW L m x)⁻¹ * g * zW L m x ∈ GW L c m ↔ g ∈ GW L c m := by
    constructor
    · intro h1
      have := (GW L c m).mul_mem ((GW L c m).mul_mem hz h1) ((GW L c m).inv_mem hz)
      simpa [mul_assoc] using this
    · intro h1
      exact (GW L c m).mul_mem ((GW L c m).mul_mem ((GW L c m).inv_mem hz) h1) hz
  have hp : ϖ ≠ 0 := pi_ne h
  rw [key, mem_KPW h, hGW, conj_val, Matrix.toBlocks_fromBlocks₂₁, intM_fromBlocks, hx]
  constructor
  · rintro ⟨hG, hC, hA, hB, -, hD⟩
    have hC' : g.val.toBlocks₂₁ = 0 := by
      rw [smul_eq_zero] at hC
      exact hC.resolve_left (mul_ne_zero hp hp)
    refine ⟨hG, hC', hA, hD, ?_⟩
    rw [mem_MA]
    intro i j
    exact hB i j
  · rintro ⟨hG, hC, hA, hD, hB⟩
    rw [mem_MA] at hB
    refine ⟨hG, by rw [hC, smul_zero], hA, fun i j => hB i j, by rw [hC, smul_zero]; exact intM_zero, hD⟩

theorem conj_le (h : IsUnramInv ϖ c q) {x : Lˣ} (hx : (x : L) = ϖ) :
    (KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom ≤ KPW L c m := by
  intro g hg
  rw [mem_conj h hx] at hg
  obtain ⟨hG, hC, hA, hD, hB⟩ := hg
  rw [mem_KPW h]
  refine ⟨hG, hC, ?_⟩
  rw [← Matrix.fromBlocks_toBlocks g.val, intM_fromBlocks]
  refine ⟨hA, ?_, by rw [hC]; exact intM_zero, hD⟩
  intro i j
  rw [mem_MA] at hB
  have hp : ϖ ≠ 0 := pi_ne h
  have e : g.val.toBlocks₁₂ i j = (ϖ * ϖ) * ((ϖ⁻¹ * ϖ⁻¹) * g.val.toBlocks₁₂ i j) := by
    field_simp
  rw [e]
  exact mul_mem (mul_mem (pi_int h) (pi_int h)) (hB i j)

def nU (X : Matrix (Fin m) (Fin m) L) : GL (Fin m ⊕ Fin m) L :=
  ⟨fromBlocks 1 X 0 1, fromBlocks 1 (-X) 0 1, by simp [fromBlocks_multiply, fromBlocks_one],
    by simp [fromBlocks_multiply, fromBlocks_one]⟩

theorem nU_mem (h : IsUnramInv ϖ c q) {X : Matrix (Fin m) (Fin m) L} (hX : X ∈ NA c m) : nU X ∈ KPW L c m := by
  obtain ⟨hXi, hXs⟩ := hX
  rw [mem_KPW h]
  refine ⟨?_, ?_, ?_⟩
  · show Iso c (Wm L (Fin m)) (Wm L (Fin m)) (fromBlocks 1 X 0 1)
    apply iso_n
    ext i j
    exact hXs i j
  · exact Matrix.toBlocks_fromBlocks₂₁ _ _ _ _
  · show IntM (fromBlocks 1 X 0 1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)
    exact intM_fromBlocks.mpr ⟨intM_one, hXi, intM_zero, intM_one⟩

def nHom (h : IsUnramInv ϖ c q) (m : ℕ) : Multiplicative (NA c m) →* KPW L c m where
  toFun X := ⟨nU (X.toAdd : NA c m).1, nU_mem h (X.toAdd : NA c m).2⟩
  map_one' := Subtype.ext (Units.ext (by simp [nU, fromBlocks_one]))
  map_mul' X Y := Subtype.ext (Units.ext (by simp [nU, fromBlocks_multiply, add_comm]))

theorem skew_of_iso (h : IsUnramInv ϖ c q) {a b d : Matrix (Fin m) (Fin m) L}
    (hg : Iso c (Wm L (Fin m)) (Wm L (Fin m)) (fromBlocks a b 0 d)) :
    (a.map c)ᵀ * d = 1 ∧ (b * (a.map c)ᵀ).map c = -(b * (a.map c)ᵀ)ᵀ := by
  have hcc : ∀ y, c (c y) = y := h.1
  have hmm : ∀ M : Matrix (Fin m) (Fin m) L, (M.map c).map c = M := by
    intro M
    rw [Matrix.map_map]
    ext i j
    exact hcc _
  have hg' : (fromBlocks a b 0 d)ᵀ * fromBlocks 0 1 1 0 * (fromBlocks a b 0 d).map c =
      (fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) := hg
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at hg'
  simp only [Matrix.transpose_zero, Matrix.map_zero, map_zero, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add] at hg'
  obtain ⟨-, h12, h21, h22⟩ := Matrix.fromBlocks_inj.mp hg'
  have e1 : (a.map c)ᵀ * d = 1 := by
    have e := congrArg (fun M => M.map c) h12
    simp only [Matrix.map_mul, hmm, Matrix.map_one (⇑c) (map_zero c) (map_one c)] at e
    rw [← Matrix.transpose_map]
    exact e
  have hA : a.map c * dᵀ = 1 := mul_eq_one_comm.mp h21
  have hD : d.map c * aᵀ = 1 := mul_eq_one_comm.mp h12
  have h22' : dᵀ * b.map c = -(bᵀ * d.map c) := eq_neg_of_add_eq_zero_left h22
  refine ⟨e1, ?_⟩
  rw [Matrix.map_mul, Matrix.transpose_map, hmm, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc b.map c * aᵀ = a.map c * dᵀ * b.map c * aᵀ := by rw [hA, Matrix.one_mul]
    _ = a.map c * (dᵀ * b.map c) * aᵀ := by rw [Matrix.mul_assoc (a.map c)]
    _ = -(a.map c * bᵀ * (d.map c * aᵀ)) := by
      rw [h22']
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -(a.map c * bᵀ) := by rw [hD, Matrix.mul_one]

theorem cover (h : IsUnramInv ϖ c q) {x : Lˣ} (hx : (x : L) = ϖ) (k : KPW L c m) :
    ∃ X, (nHom h m X)⁻¹ * k ∈ ((KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom).subgroupOf (KPW L c m) := by
  have hk := (mem_KPW h).mp k.2
  obtain ⟨hG, hC, hI⟩ := hk
  obtain ⟨A, hA'⟩ : ∃ A, A = (k : GL (Fin m ⊕ Fin m) L).val.toBlocks₁₁ := ⟨_, rfl⟩
  obtain ⟨B, hB'⟩ : ∃ B, B = (k : GL (Fin m ⊕ Fin m) L).val.toBlocks₁₂ := ⟨_, rfl⟩
  obtain ⟨D, hD'⟩ : ∃ D, D = (k : GL (Fin m ⊕ Fin m) L).val.toBlocks₂₂ := ⟨_, rfl⟩
  have hv : (k : GL (Fin m ⊕ Fin m) L).val = fromBlocks A B 0 D := by
    rw [hA', hB', hD', ← hC, Matrix.fromBlocks_toBlocks]
  have hiso : Iso c (Wm L (Fin m)) (Wm L (Fin m)) (fromBlocks A B 0 D) := by
    rw [← hv]
    exact hG
  obtain ⟨e1, e2⟩ := skew_of_iso h hiso
  have hIfb : IntM (fromBlocks A B 0 D) := by
    rw [← hv]
    exact hI
  obtain ⟨hA, hB, -, hD⟩ := intM_fromBlocks.mp hIfb
  obtain ⟨X, hXdef⟩ : ∃ X : Matrix (Fin m) (Fin m) L, X = B * (A.map c)ᵀ := ⟨_, rfl⟩
  have hXNA : X ∈ NA c m := by
    refine ⟨?_, ?_⟩
    · rw [hXdef]
      exact IntM.mul hB (IntM.conjT h hA)
    · intro i j
      rw [hXdef]
      exact congrFun (congrFun e2 i) j
  have hXD : X * D = B := by
    rw [hXdef, Matrix.mul_assoc, e1, Matrix.mul_one]
  refine ⟨Multiplicative.ofAdd ⟨X, hXNA⟩, ?_⟩
  have hprod : (((nHom h m (Multiplicative.ofAdd ⟨X, hXNA⟩))⁻¹ * k : KPW L c m) :
      GL (Fin m ⊕ Fin m) L).val = fromBlocks A 0 0 D := by
    show fromBlocks 1 (-X) 0 1 * (k : GL (Fin m ⊕ Fin m) L).val = _
    rw [hv, Matrix.fromBlocks_multiply]
    simp [hXD]
  rw [Subgroup.mem_subgroupOf, mem_conj h hx, hprod, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₁₁,
    Matrix.toBlocks_fromBlocks₂₂, Matrix.toBlocks_fromBlocks₁₂]
  exact ⟨((nHom h m (Multiplicative.ofAdd ⟨X, hXNA⟩))⁻¹ * k).2.1.1, rfl, hA, hD, zero_mem _⟩

theorem comap_eq (h : IsUnramInv ϖ c q) {x : Lˣ} (hx : (x : L) = ϖ) :
    (((KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom).subgroupOf (KPW L c m)).comap (nHom h m) =
      ((MA m (ϖ⁻¹ * ϖ⁻¹)).addSubgroupOf (NA c m)).toSubgroup := by
  ext X
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, mem_conj h hx]
  show _ ↔ ((Multiplicative.toAdd X : NA c m) : Matrix (Fin m) (Fin m) L) ∈ MA m (ϖ⁻¹ * ϖ⁻¹)
  have hv : ((nHom h m X : KPW L c m) : GL (Fin m ⊕ Fin m) L).val =
      fromBlocks 1 ((Multiplicative.toAdd X : NA c m) : Matrix (Fin m) (Fin m) L) 0 1 := rfl
  rw [hv, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₂,
    Matrix.toBlocks_fromBlocks₁₂]
  constructor
  · rintro ⟨-, -, -, -, hM⟩
    exact hM
  · intro hM
    exact ⟨(nHom h m X).2.1.1, rfl, intM_one, intM_one, hM⟩

end PositivityTheory.Sph.M2.ZC

namespace PositivityTheory.Sph.M2

theorem zCount : ZCountSt := by
  intro L _ _ ϖ c q h m x hx
  refine ⟨ZC.conj_le h hx, ?_⟩
  show (((KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom).subgroupOf (KPW L c m)).index = q ^ (2 * m * m)
  rw [← ZC.index_comap_of_cover (ZC.nHom h m) _ (ZC.cover h hx), ZC.comap_eq h hx, AddSubgroup.index_toSubgroup]
  exact ZC.relIndex_NA h m

end PositivityTheory.Sph.M2

end

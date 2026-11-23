import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace P_TzE

variable {n : ℕ} (G : Grp k n)

theorem isClosed_unipRad : IsClosed (unipRad k G.e : Set (GL (Fin n) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have e : (unipRad k G.e : Set (GL (Fin n) k)) =
      (⋂ i : Fin n, ⋂ j : Fin n, {g : GL (Fin n) k | blk G.e j < blk G.e i → (g : Matrix (Fin n) (Fin n) k) i j = 0}) ∩
      (⋂ a : Fin G.s, ⋂ i : Fin (G.d a), ⋂ j : Fin (G.d a),
        {g : GL (Fin n) k | (g : Matrix (Fin n) (Fin n) k) (G.e ⟨a, i⟩) (G.e ⟨a, j⟩) = (1 : Matrix (Fin (G.d a)) (Fin (G.d a)) k) i j}) := by
    ext g
    simp only [SetLike.mem_coe, mem_unipRad, mem_parab, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
    (isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun j => ?_)
  · by_cases h : blk G.e j < blk G.e i
    · simp only [h, true_implies]
      exact isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
    · simp only [h, false_implies, Set.ofPred_true]
      exact isClosed_univ
  · exact isClosed_eq (Units.continuous_val.matrix_elem _ _) continuous_const

theorem isCompact_NO : IsCompact (G.NO : Set (GL (Fin n) k)) := by
  have h := (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)).inter_left (isClosed_unipRad G)
  simpa [Grp.NO, Subgroup.coe_inf] using h

theorem zpow_eq (ϖ : kˣ) (m : ℕ) : ∃ y : Levi k (fun a : Fin G.s => Fin (G.d a)), G.zEl ϖ ^ m = leviEmb k G.e y :=
  ⟨_, (map_pow (leviEmb k G.e) _ m).symm⟩

theorem mem_zN_iff (ϖ : kˣ) (m : ℕ) (u : ↥G.NO) :
    u ∈ G.zN ϖ m ↔ (G.zEl ϖ ^ m)⁻¹ * (u : GL (Fin n) k) * G.zEl ϖ ^ m ∈ KO k (Fin n) := by
  obtain ⟨y, hy⟩ := zpow_eq G ϖ m
  rw [Grp.zN, Subgroup.mem_subgroupOf, Subgroup.mem_map, hy]
  constructor
  · rintro ⟨w, hw, hwu⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwu
    rw [← hwu]
    have : (leviEmb k G.e y)⁻¹ * (leviEmb k G.e y * w * (leviEmb k G.e y)⁻¹) * leviEmb k G.e y = w := by group
    rw [this]
    exact (Subgroup.mem_inf.1 hw).2
  · intro h
    have hN : (leviEmb k G.e y)⁻¹ ∈ Subgroup.normalizer (unipRad k G.e : Set (GL (Fin n) k)) := by
      rw [← map_inv]
      exact leviEmb_mem_normalizer k G.e y⁻¹
    have hu := (Subgroup.mem_inf.1 u.2).1
    have h2 := (Subgroup.mem_normalizer_iff.1 hN (u : GL (Fin n) k)).1 hu
    rw [inv_inv] at h2
    refine ⟨(leviEmb k G.e y)⁻¹ * (u : GL (Fin n) k) * leviEmb k G.e y, Subgroup.mem_inf.2 ⟨h2, h⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem isOpen_zN (ϖ : kˣ) (m : ℕ) : IsOpen ((G.zN ϖ m : Subgroup ↥G.NO) : Set ↥G.NO) := by
  have e : ((G.zN ϖ m : Subgroup ↥G.NO) : Set ↥G.NO) =
      (fun u : ↥G.NO => (G.zEl ϖ ^ m)⁻¹ * (u : GL (Fin n) k) * G.zEl ϖ ^ m) ⁻¹' (KO k (Fin n) : Set (GL (Fin n) k)) := by
    ext u
    exact mem_zN_iff G ϖ m u
  rw [e]
  exact GlobalTheory.SplitFlip.isOpen_KO.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)

theorem finite_quot (ϖ : kˣ) (m : ℕ) : Finite (↥G.NO ⧸ G.zN ϖ m) := by
  have : CompactSpace ↥G.NO := isCompact_iff_compactSpace.mp (isCompact_NO G)
  exact Subgroup.quotient_finite_of_isOpen (G.zN ϖ m) (isOpen_zN G ϖ m)

theorem mem_Nbar {g : GL (Fin n) k} : g ∈ G.Nbar ↔ ∀ i j, (G.bl i < G.bl j → (g : Matrix (Fin n) (Fin n) k) i j = 0) ∧
    (G.bl i = G.bl j → (g : Matrix (Fin n) (Fin n) k) i j = if i = j then 1 else 0) := Iff.rfl

theorem mem_JSet {g : GL (Fin n) k} : g ∈ G.JSet ↔ g ∈ KO k (Fin n) ∧
    ∀ i j, G.bl j < G.bl i → InPow (cc G.μ (G.bl j) (G.bl i)) ((g : Matrix (Fin n) (Fin n) k) i j) := Iff.rfl

@[simp] theorem block_e (a : Fin G.s) (i : Fin (G.d a)) : G.bl (G.e ⟨a, i⟩) = a := by
  show (G.e.symm (G.e ⟨a, i⟩)).1 = a
  rw [Equiv.symm_apply_apply]

theorem nbar_iff (g : GL (Fin n) k) : g ∈ G.Nbar ↔ g ∈ unipRadLower k G.e := by
  rw [mem_unipRadLower, mem_parabLower_iff, mem_Nbar]
  constructor
  · intro hg
    refine ⟨fun a b i j hab => (hg _ _).1 (by simpa [block_e] using hab), fun a i j => ?_⟩
    rw [(hg _ _).2 (by simp [block_e]), Matrix.one_apply]
    simp
  · rintro ⟨h1, h2⟩ i j
    obtain ⟨⟨a, i'⟩, rfl⟩ := G.e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := G.e.surjective j
    refine ⟨fun hab => h1 a b i' j' (by simpa [block_e] using hab), fun hab => ?_⟩
    have hab' : a = b := by simpa [block_e] using hab
    subst hab'
    rw [h2, Matrix.one_apply]
    simp

def dz (ϖ : kˣ) (m : ℕ) (i : Fin n) : k := ((ϖ : k) ^ (G.s - 1 - (G.bl i : ℕ))) ^ m

theorem dz_ne (ϖ : kˣ) (m : ℕ) (i : Fin n) : dz G ϖ m i ≠ 0 :=
  pow_ne_zero _ (pow_ne_zero _ ϖ.ne_zero)

theorem zmat (ϖ : kˣ) (m : ℕ) :
    ((G.zEl ϖ ^ m : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = diagonal (dz G ϖ m) := by
  ext i j
  obtain ⟨⟨a, i'⟩, rfl⟩ := G.e.surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := G.e.surjective j
  rw [Grp.zEl, ← map_pow]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    simp [dz, block_e, Matrix.diagonal_apply, Matrix.scalar_apply, Units.coe_map, Matrix.diagonal_pow]
  · rw [leviEmb_apply_ne k G.e _ hab, Matrix.diagonal_apply_ne]
    intro h
    exact hab (congrArg Sigma.fst (G.e.injective h))

theorem zinv_mat (ϖ : kˣ) (m : ℕ) :
    (((G.zEl ϖ ^ m)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = diagonal fun i => (dz G ϖ m i)⁻¹ := by
  have h : ((G.zEl ϖ ^ m : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * diagonal (fun i => (dz G ϖ m i)⁻¹) = 1 := by
    rw [zmat, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (dz_ne G ϖ m i)
  calc (((G.zEl ϖ ^ m)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = (((G.zEl ϖ ^ m)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *
          (((G.zEl ϖ ^ m : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * diagonal (fun i => (dz G ϖ m i)⁻¹)) := by
        rw [h, mul_one]
    _ = diagonal fun i => (dz G ϖ m i)⁻¹ := by rw [← mul_assoc, Units.inv_mul, one_mul]

theorem conj_apply (ϖ : kˣ) (m : ℕ) (g : GL (Fin n) k) (i j : Fin n) :
    (((G.zEl ϖ ^ m)⁻¹ * g * G.zEl ϖ ^ m : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (dz G ϖ m i)⁻¹ * (g : Matrix (Fin n) (Fin n) k) i j * dz G ϖ m j := by
  rw [Units.val_mul, Units.val_mul, zinv_mat, zmat, mul_diagonal, diagonal_mul]

theorem inPow_mul_int {c : ℕ} {x : k} (hx : InPow c x) (w : 𝒪[k]) : InPow c (algebraMap 𝒪[k] k w * x) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨w * y, Ideal.mul_mem_left _ w hy, by rw [map_mul]⟩

theorem int_of_inPow {c : ℕ} {x : k} (hx : InPow c x) : x ∈ 𝒪[k] := by
  obtain ⟨y, -, rfl⟩ := hx
  exact y.2

theorem conj_lower (ϖ : kˣ) (hϖ : IsUnif ϖ) (m : ℕ) (g : GL (Fin n) k) (i j : Fin n) (hij : G.bl j < G.bl i)
    {c : ℕ} (hg : InPow c ((g : Matrix (Fin n) (Fin n) k) i j)) :
    InPow c ((((G.zEl ϖ ^ m)⁻¹ * g * G.zEl ϖ ^ m : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) := by
  obtain ⟨w, -, hw⟩ := hϖ
  rw [conj_apply]
  have hlt : (G.bl j : ℕ) < G.bl i := hij
  have hle : G.s - 1 - (G.bl i : ℕ) ≤ G.s - 1 - (G.bl j : ℕ) := by omega
  have key : (dz G ϖ m i)⁻¹ * (g : Matrix (Fin n) (Fin n) k) i j * dz G ϖ m j =
      algebraMap 𝒪[k] k ((w ^ (G.s - 1 - (G.bl j : ℕ) - (G.s - 1 - (G.bl i : ℕ)))) ^ m) *
        (g : Matrix (Fin n) (Fin n) k) i j := by
    rw [map_pow, map_pow, hw]
    have hd : dz G ϖ m j = dz G ϖ m i * ((ϖ : k) ^ (G.s - 1 - (G.bl j : ℕ) - (G.s - 1 - (G.bl i : ℕ)))) ^ m := by
      simp only [dz]
      rw [← mul_pow, ← pow_add, Nat.add_sub_of_le hle]
    rw [hd]
    have ha := dz_ne G ϖ m i
    set A := dz G ϖ m i
    set X := (g : Matrix (Fin n) (Fin n) k) i j
    set Y := ((ϖ : k) ^ (G.s - 1 - (G.bl j : ℕ) - (G.s - 1 - (G.bl i : ℕ)))) ^ m
    calc A⁻¹ * X * (A * Y) = (A⁻¹ * A) * (Y * X) := by ring
      _ = Y * X := by rw [inv_mul_cancel₀ ha, one_mul]
  rw [key]
  exact inPow_mul_int hg _

theorem conj_int (ϖ : kˣ) (hϖ : IsUnif ϖ) (m : ℕ) (g : GL (Fin n) k) (hg : g ∈ G.Nbar) (hgJ : g ∈ G.JSet)
    (i j : Fin n) :
    (((G.zEl ϖ ^ m)⁻¹ * g * G.zEl ϖ ^ m : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
  rw [mem_Nbar] at hg
  rw [mem_JSet] at hgJ
  rcases lt_trichotomy (G.bl j) (G.bl i) with h | h | h
  · exact int_of_inPow (conj_lower G ϖ hϖ m g i j h (hgJ.2 i j h))
  · rw [conj_apply]
    have hd : dz G ϖ m j = dz G ϖ m i := by simp only [dz, h]
    rw [hd, (hg i j).2 h.symm]
    have ha := dz_ne G ϖ m i
    split_ifs
    · rw [mul_one, inv_mul_cancel₀ ha]; exact one_mem _
    · rw [mul_zero, zero_mul]; exact zero_mem _
  · rw [conj_apply, (hg i j).1 h, mul_zero, zero_mul]
    exact zero_mem _

theorem conj_nbar (ϖ : kˣ) (hϖ : IsUnif ϖ) (m : ℕ) (hJi : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet) (v : GL (Fin n) k)
    (hv : v ∈ G.Nbar) (hvJ : v ∈ G.JSet) :
    (G.zEl ϖ ^ m)⁻¹ * v * G.zEl ϖ ^ m ∈ G.Nbar ∧ (G.zEl ϖ ^ m)⁻¹ * v * G.zEl ϖ ^ m ∈ G.JSet := by
  have hN : ∀ w ∈ G.Nbar, (G.zEl ϖ ^ m)⁻¹ * w * G.zEl ϖ ^ m ∈ G.Nbar := by
    intro w hw
    rw [nbar_iff] at hw ⊢
    have hz : (G.zEl ϖ ^ m)⁻¹ ∈
        Subgroup.normalizer ((unipRadLower k G.e : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) := by
      rw [Grp.zEl, ← map_pow]
      exact inv_mem (leviEmb_mem_normalizer_lower k G.e _)
    have := (Subgroup.mem_normalizer_iff.1 hz w).1 hw
    simpa using this
  have hvi : v⁻¹ ∈ G.Nbar := by
    rw [nbar_iff] at hv ⊢
    exact inv_mem hv
  refine ⟨hN v hv, ?_⟩
  rw [mem_JSet]
  refine ⟨(GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => conj_int G ϖ hϖ m v hv hvJ i j, fun i j => ?_⟩,
    fun i j hij => conj_lower G ϖ hϖ m v i j hij (((mem_JSet G).1 hvJ).2 i j hij)⟩
  have he : ((G.zEl ϖ ^ m)⁻¹ * v * G.zEl ϖ ^ m)⁻¹ = (G.zEl ϖ ^ m)⁻¹ * v⁻¹ * G.zEl ϖ ^ m := by group
  rw [he]
  exact conj_int G ϖ hϖ m v⁻¹ hvi (hJi v hvJ) i j

def zL (ϖ : kˣ) : Levi k (fun a : Fin G.s => Fin (G.d a)) :=
  fun a => Units.map (Matrix.scalar (Fin (G.d a)) : k →+* Matrix (Fin (G.d a)) (Fin (G.d a)) k).toMonoidHom
    (ϖ ^ (G.s - 1 - (a : ℕ)))

theorem zpow_eq' (ϖ : kˣ) (m : ℕ) : G.zEl ϖ ^ m = leviEmb k G.e (zL G ϖ ^ m) := by
  rw [map_pow]; rfl

theorem zL_comm (ϖ : kˣ) (l : Levi k (fun a : Fin G.s => Fin (G.d a))) : Commute (zL G ϖ) l := by
  show zL G ϖ * l = l * zL G ϖ
  funext a
  apply Units.ext
  show (Matrix.scalar (Fin (G.d a)) (((ϖ ^ (G.s - 1 - (a : ℕ)) : kˣ) : k))) * ((l a : GL _ k) : Matrix _ _ k) =
    ((l a : GL _ k) : Matrix _ _ k) * Matrix.scalar (Fin (G.d a)) (((ϖ ^ (G.s - 1 - (a : ℕ)) : kˣ) : k))
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

theorem z_comm_levi (ϖ : kˣ) (m : ℕ) (l : Levi k (fun a : Fin G.s => Fin (G.d a))) :
    G.zEl ϖ ^ m * leviEmb k G.e l = leviEmb k G.e l * G.zEl ϖ ^ m := by
  rw [zpow_eq', ← map_mul, ← map_mul, ((zL_comm G ϖ l).pow_left m).eq]

theorem conj_unip (ϖ : kˣ) (m : ℕ) {u : GL (Fin n) k} (hu : u ∈ unipRad k G.e) :
    (G.zEl ϖ ^ m)⁻¹ * u * G.zEl ϖ ^ m ∈ unipRad k G.e := by
  have hN : (G.zEl ϖ ^ m)⁻¹ ∈ Subgroup.normalizer (unipRad k G.e : Set (GL (Fin n) k)) := by
    rw [zpow_eq', ← map_inv]
    exact leviEmb_mem_normalizer k G.e _
  have h2 := (Subgroup.mem_normalizer_iff.1 hN u).1 hu
  rwa [inv_inv] at h2

structure Hyp (G : Grp k n) : Prop where
  one : (1 : GL (Fin n) k) ∈ G.JSet
  mul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet
  inv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet
  lmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, G.lam (g * h) = G.lam g * G.lam h
  unip : LambdaUnipotentProp G
  iw : ∀ g ∈ G.JSet, ∃ v ∈ G.Nbar, v ∈ G.JSet ∧
    ∃ l : Levi k (fun a : Fin G.s => Fin (G.d a)), l ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)) ∧
      ∃ u ∈ G.NO, g = v * leviEmb k G.e l * u

variable {G}

theorem lam_one (H : Hyp G) : G.lam 1 = 1 := (H.unip.1 1 (one_mem _)).2

theorem lam_ne (H : Hyp G) {g : GL (Fin n) k} (hg : g ∈ G.JSet) : G.lam g ≠ 0 := by
  intro h0
  have := H.lmul g hg g⁻¹ (H.inv g hg)
  rw [mul_inv_cancel, lam_one H, h0, zero_mul] at this
  exact one_ne_zero this

theorem NO_J (H : Hyp G) {u : GL (Fin n) k} (hu : u ∈ G.NO) : u ∈ G.JSet := (H.unip.1 u hu).1

theorem J_KO {g : GL (Fin n) k} (hg : g ∈ G.JSet) : g ∈ KO k (Fin n) := by
  unfold Grp.JSet at hg
  exact hg.1

def Jsub (H : Hyp G) : Subgroup (GL (Fin n) k) where
  carrier := G.JSet
  mul_mem' ha hb := H.mul _ ha _ hb
  one_mem' := H.one
  inv_mem' ha := H.inv _ ha

def Kz (H : Hyp G) (ϖ : kˣ) (m : ℕ) : Subgroup ↥(Jsub H) where
  carrier := {g | (G.zEl ϖ ^ m)⁻¹ * (g : GL (Fin n) k) * G.zEl ϖ ^ m ∈ G.JSet}
  mul_mem' {a b} ha hb := by
    have e : (G.zEl ϖ ^ m)⁻¹ * ((a * b : ↥(Jsub H)) : GL (Fin n) k) * G.zEl ϖ ^ m =
        ((G.zEl ϖ ^ m)⁻¹ * (a : GL (Fin n) k) * G.zEl ϖ ^ m) *
          ((G.zEl ϖ ^ m)⁻¹ * (b : GL (Fin n) k) * G.zEl ϖ ^ m) := by
      rw [Subgroup.coe_mul]; group
    rw [Set.mem_ofPred_eq, e]; exact H.mul _ ha _ hb
  one_mem' := by
    show (G.zEl ϖ ^ m)⁻¹ * ((1 : ↥(Jsub H)) : GL (Fin n) k) * G.zEl ϖ ^ m ∈ G.JSet
    rw [Subgroup.coe_one, mul_one, inv_mul_cancel]; exact H.one
  inv_mem' {a} ha := by
    have e : (G.zEl ϖ ^ m)⁻¹ * ((a⁻¹ : ↥(Jsub H)) : GL (Fin n) k) * G.zEl ϖ ^ m =
        ((G.zEl ϖ ^ m)⁻¹ * (a : GL (Fin n) k) * G.zEl ϖ ^ m)⁻¹ := by
      rw [Subgroup.coe_inv]; group
    rw [Set.mem_ofPred_eq, e]; exact H.inv _ ha

theorem lam_conj (H : Hyp G) (ϖ : kˣ) (hϖ : IsUnif ϖ) (m : ℕ) {g : GL (Fin n) k} (hg : g ∈ G.JSet)
    (hg' : (G.zEl ϖ ^ m)⁻¹ * g * G.zEl ϖ ^ m ∈ G.JSet) :
    G.lam ((G.zEl ϖ ^ m)⁻¹ * g * G.zEl ϖ ^ m) = G.lam g := by
  obtain ⟨v, hvN, hvJ, l, -, u, hu, rfl⟩ := H.iw g hg
  obtain ⟨hAN, hAJ⟩ := conj_nbar G ϖ hϖ m H.inv v hvN hvJ
  have hB0 := conj_unip G ϖ m (Subgroup.mem_inf.1 hu).1
  have hzL := z_comm_levi G ϖ m l
  set z := G.zEl ϖ ^ m with hzdef
  set L := leviEmb k G.e l with hLdef
  have huJ : u ∈ G.JSet := NO_J H hu
  have hLJ : L ∈ G.JSet := by
    have : L = v⁻¹ * (v * L * u) * u⁻¹ := by group
    rw [this]; exact H.mul _ (H.mul _ (H.inv _ hvJ) _ hg) _ (H.inv _ huJ)
  have e1 : z⁻¹ * (v * L * u) * z = (z⁻¹ * v * z) * L * (z⁻¹ * u * z) := by
    have : (z⁻¹ * v * z) * L * (z⁻¹ * u * z) = z⁻¹ * v * (z * L) * z⁻¹ * u * z := by group
    rw [this, hzL]; group
  have hB : z⁻¹ * u * z ∈ G.JSet := by
    have : z⁻¹ * u * z = ((z⁻¹ * v * z) * L)⁻¹ * (z⁻¹ * (v * L * u) * z) := by rw [e1]; group
    rw [this]; exact H.mul _ (H.inv _ (H.mul _ hAJ _ hLJ)) _ hg'
  have hBN : z⁻¹ * u * z ∈ G.NO := Subgroup.mem_inf.2 ⟨hB0, J_KO hB⟩
  rw [e1, H.lmul _ (H.mul _ hAJ _ hLJ) _ hB, H.lmul _ hAJ _ hLJ, H.lmul _ (H.mul _ hvJ _ hLJ) _ huJ,
    H.lmul _ hvJ _ hLJ, H.unip.2 _ hAN hAJ, H.unip.2 _ hvN hvJ, (H.unip.1 _ hBN).2, (H.unip.1 _ hu).2]

def fz (H : Hyp G) (ϖ : kˣ) (m : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (x : V) (y : ↥(Jsub H)) : V :=
  (G.lam y)⁻¹ • π y (π (G.zEl ϖ ^ m) x)

theorem fz_eq (H : Hyp G) (ϖ : kˣ) (hϖ : IsUnif ϖ) (m : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (x : V) (hx : x ∈ G.Eig π) (a b : ↥(Jsub H))
    (hab : a⁻¹ * b ∈ Kz H ϖ m) : fz H ϖ m π x a = fz H ϖ m π x b := by
  have hk : ((a⁻¹ * b : ↥(Jsub H)) : GL (Fin n) k) ∈ G.JSet := (a⁻¹ * b).2
  have hab' : (G.zEl ϖ ^ m)⁻¹ * ((a⁻¹ * b : ↥(Jsub H)) : GL (Fin n) k) * G.zEl ϖ ^ m ∈ G.JSet := hab
  have hlc := lam_conj H ϖ hϖ m hk hab'
  have hb : (b : GL (Fin n) k) = a * ((a⁻¹ * b : ↥(Jsub H)) : GL (Fin n) k) := by simp
  set c : GL (Fin n) k := ((a⁻¹ * b : ↥(Jsub H)) : GL (Fin n) k) with hc
  set z := G.zEl ϖ ^ m with hzdef
  have e2 : π c (π z x) = G.lam c • π z x := by
    have : c * z = z * (z⁻¹ * c * z) := by group
    rw [← Module.End.mul_apply, ← map_mul, this, map_mul, Module.End.mul_apply, hx _ hab', map_smul, hlc]
  unfold fz
  rw [hb, map_mul, Module.End.mul_apply, e2, map_smul, smul_smul, H.lmul _ a.2 _ hk, mul_inv, mul_assoc,
    inv_mul_cancel₀ (lam_ne H hk), mul_one]

def Fq (H : Hyp G) (ϖ : kˣ) (hϖ : IsUnif ϖ) (m : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (x : V) (hx : x ∈ G.Eig π) : ↥(Jsub H) ⧸ Kz H ϖ m → V :=
  Quotient.lift (fz H ϖ m π x) fun a b hab => fz_eq H ϖ hϖ m π x hx a b (QuotientGroup.leftRel_apply.mp hab)

theorem NO_le (H : Hyp G) : G.NO ≤ Jsub H := fun _ hu => NO_J H hu

def iota (H : Hyp G) (ϖ : kˣ) (m : ℕ) : ↥G.NO ⧸ G.zN ϖ m → ↥(Jsub H) ⧸ Kz H ϖ m :=
  Quotient.lift (fun u => (QuotientGroup.mk (Subgroup.inclusion (NO_le H) u) : ↥(Jsub H) ⧸ Kz H ϖ m))
    fun a b hab => by
      have hab' := (mem_zN_iff G ϖ m _).1 (QuotientGroup.leftRel_apply.mp hab)
      rw [QuotientGroup.eq]
      show (G.zEl ϖ ^ m)⁻¹ * (((Subgroup.inclusion (NO_le H) a)⁻¹ * Subgroup.inclusion (NO_le H) b :
        ↥(Jsub H)) : GL (Fin n) k) * G.zEl ϖ ^ m ∈ G.JSet
      have hu : ((a⁻¹ * b : ↥G.NO) : GL (Fin n) k) ∈ unipRad k G.e := (Subgroup.mem_inf.1 (a⁻¹ * b).2).1
      have := NO_J H (Subgroup.mem_inf.2 ⟨conj_unip G ϖ m hu, hab'⟩)
      simpa using this

theorem iota_mk (H : Hyp G) (ϖ : kˣ) (m : ℕ) (u : ↥G.NO) :
    iota H ϖ m (QuotientGroup.mk u) = QuotientGroup.mk (Subgroup.inclusion (NO_le H) u) := rfl

theorem iota_inj (H : Hyp G) (ϖ : kˣ) (m : ℕ) : Function.Injective (iota H ϖ m) := by
  intro c1 c2
  refine QuotientGroup.induction_on c1 (fun a => ?_)
  refine QuotientGroup.induction_on c2 (fun b => ?_)
  intro h
  rw [iota_mk, iota_mk, QuotientGroup.eq] at h
  have h' : (G.zEl ϖ ^ m)⁻¹ * (((Subgroup.inclusion (NO_le H) a)⁻¹ * Subgroup.inclusion (NO_le H) b :
      ↥(Jsub H)) : GL (Fin n) k) * G.zEl ϖ ^ m ∈ G.JSet := h
  rw [QuotientGroup.eq, mem_zN_iff]
  have := J_KO h'
  simpa using this

theorem iota_surj (H : Hyp G) (ϖ : kˣ) (hϖ : IsUnif ϖ) (m : ℕ) : Function.Surjective (iota H ϖ m) := by
  intro q
  refine QuotientGroup.induction_on q (fun y => ?_)
  obtain ⟨v, hvN, hvJ, l, -, u, hu, hy⟩ := H.iw _ (H.inv _ y.2)
  have hA := (conj_nbar G ϖ hϖ m H.inv v hvN hvJ).2
  have hzL := z_comm_levi G ϖ m l
  refine ⟨QuotientGroup.mk (⟨u⁻¹, inv_mem hu⟩ : ↥G.NO), ?_⟩
  rw [iota_mk, QuotientGroup.eq]
  show (G.zEl ϖ ^ m)⁻¹ * (((Subgroup.inclusion (NO_le H) ⟨u⁻¹, inv_mem hu⟩)⁻¹ * y : ↥(Jsub H)) :
    GL (Fin n) k) * G.zEl ϖ ^ m ∈ G.JSet
  have hyv : (y : GL (Fin n) k) = (v * leviEmb k G.e l * u)⁻¹ := by rw [← hy, inv_inv]
  have hLJ : leviEmb k G.e l ∈ G.JSet := by
    have : leviEmb k G.e l = v⁻¹ * (v * leviEmb k G.e l * u) * u⁻¹ := by group
    rw [this, ← hy]
    exact H.mul _ (H.mul _ (H.inv _ hvJ) _ (H.inv _ y.2)) _ (H.inv _ (NO_J H hu))
  have e : (G.zEl ϖ ^ m)⁻¹ * (((Subgroup.inclusion (NO_le H) ⟨u⁻¹, inv_mem hu⟩)⁻¹ * y : ↥(Jsub H)) :
      GL (Fin n) k) * G.zEl ϖ ^ m = (((G.zEl ϖ ^ m)⁻¹ * v * G.zEl ϖ ^ m) * leviEmb k G.e l)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    rw [hyv]
    set z := G.zEl ϖ ^ m
    set L := leviEmb k G.e l
    have h2 : (z⁻¹ * v * z) * L = z⁻¹ * v * (z * L) := by group
    rw [h2, hzL]
    group
  rw [e]
  exact H.inv _ (H.mul _ hA _ hLJ)

theorem eig_Tz (H : Hyp G) (ϖ : kˣ) (hϖ : IsUnif ϖ) (m : ℕ) [Finite (↥G.NO ⧸ G.zN ϖ m)]
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (x : V) (hx : x ∈ G.Eig π) : G.Tz π ϖ m x ∈ G.Eig π := by
  have : Fintype (↥G.NO ⧸ G.zN ϖ m) := Fintype.ofFinite _
  have : Finite (↥(Jsub H) ⧸ Kz H ϖ m) := Finite.of_surjective _ (iota_surj H ϖ hϖ m)
  have : Fintype (↥(Jsub H) ⧸ Kz H ϖ m) := Fintype.ofFinite _
  have hιF : ∀ c, Fq H ϖ hϖ m π x hx (iota H ϖ m c) =
      π ((Quotient.out c : ↥G.NO) : GL (Fin n) k) (π (G.zEl ϖ ^ m) x) := by
    intro c
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rw [iota_mk]
    show (G.lam ((Subgroup.inclusion (NO_le H) c.out : ↥(Jsub H)) : GL (Fin n) k))⁻¹ •
      π ((Subgroup.inclusion (NO_le H) c.out : ↥(Jsub H)) : GL (Fin n) k) (π (G.zEl ϖ ^ m) x) = _
    rw [Subgroup.coe_inclusion, (H.unip.1 _ c.out.2).2, inv_one, one_smul]
  have hT : G.Tz π ϖ m x = ∑ q, Fq H ϖ hϖ m π x hx q := by
    unfold Grp.Tz
    rw [finsum_eq_sum_of_fintype]
    exact Fintype.sum_bijective _ ⟨iota_inj H ϖ m, iota_surj H ϖ hϖ m⟩ _ _ fun c => (hιF c).symm
  intro g hg
  rw [hT, map_sum]
  let gJ : ↥(Jsub H) := ⟨g, hg⟩
  have key : ∀ q, π g (Fq H ϖ hϖ m π x hx q) = G.lam g • Fq H ϖ hϖ m π x hx (gJ • q) := by
    intro q
    refine QuotientGroup.induction_on q (fun y => ?_)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    show π g ((G.lam y)⁻¹ • π y (π (G.zEl ϖ ^ m) x)) =
      G.lam g • ((G.lam ((gJ * y : ↥(Jsub H)) : GL (Fin n) k))⁻¹ •
        π ((gJ * y : ↥(Jsub H)) : GL (Fin n) k) (π (G.zEl ϖ ^ m) x))
    rw [Subgroup.coe_mul, H.lmul _ hg _ y.2, map_mul, Module.End.mul_apply, map_smul, smul_smul, mul_inv,
      ← mul_assoc, mul_inv_cancel₀ (lam_ne H hg), one_mul]
  rw [Finset.sum_congr rfl fun q _ => key q, ← Finset.smul_sum]
  congr 1
  exact Fintype.sum_bijective _ (MulAction.bijective gJ) _ _ fun _ => rfl

variable (G) in
theorem step_TzE_of (H : Hyp G) : ∀ (ϖ : kˣ), IsUnif ϖ → ∀ m : ℕ, Finite (↥G.NO ⧸ G.zN ϖ m) ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
      ∀ x ∈ G.Eig π, G.Tz π ϖ m x ∈ G.Eig π := by
  intro ϖ hϖ m
  have := finite_quot G ϖ m
  exact ⟨inferInstance, fun V _ _ π x hx => eig_Tz H ϖ hϖ m V π x hx⟩

end P_TzE

theorem step_TzE {n : ℕ} (G : Grp k n) : TorusCentreEigenProp G := by
  intro hcc hccB hΔU hΔM hJm hJi hlm hlu hiw
  exact P_TzE.step_TzE_of G ⟨(hlu.1 1 (one_mem _)).1, hJm hcc hccB, hJi hcc hccB, hlm hcc hΔU hΔM hccB, hlu,
    hiw hcc hccB hΔU hJm hJi⟩

end UpperTheory.TNZ.Grp

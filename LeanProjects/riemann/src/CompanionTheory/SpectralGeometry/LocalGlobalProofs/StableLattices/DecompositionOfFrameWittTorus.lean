import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

noncomputable section
namespace GlobalTheory.CompanionTheory.FlDecomp
open CompanionTheory.Rg.FlB

section SlopeTestRemainingChoices
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]

def pull (k : V ≃ₗ[L] V) (Λ : AddSubgroup V) : AddSubgroup V := Λ.comap k.toLinearMap.toAddMonoidHom

theorem mem_pull {k : V ≃ₗ[L] V} {Λ : AddSubgroup V} {x : V} : x ∈ pull k Λ ↔ k x ∈ Λ := Iff.rfl

theorem isIso_mul {h : V → V → L} {a b : V ≃ₗ[L] V} (ha : IsIso h a) (hb : IsIso h b) : IsIso h (a * b) :=
  fun x y => by simpa [LinearEquiv.mul_apply] using (ha (b x) (b y)).trans (hb x y)

theorem isIso_inv {h : V → V → L} {a : V ≃ₗ[L] V} (ha : IsIso h a) : IsIso h a⁻¹ := fun x y => by
  have := ha (a⁻¹ x) (a⁻¹ y)
  have h1 : ∀ z, a (a⁻¹ z) = z := fun z => by
    change (a * a⁻¹) z = z
    simp
  rw [h1, h1] at this
  exact this.symm

theorem adapted_unique {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V} {u v : Fin l → L}
    {Λ₁ Λ₂ : AddSubgroup V} (hF : IsFrame h δ e f W) (h1 : IsAdapted h e f W u Λ₁) (h2 : IsAdapted h e f W v Λ₂)
    (huv : ∀ i, ‖u i‖ = ‖v i‖) (x : V) : x ∈ Λ₁ ↔ x ∈ Λ₂ := by
  obtain ⟨a, b, w, hw, rfl⟩ := hF.2.2.2.2.2 x
  rw [h1 a b w hw, h2 a b w hw]
  simp only [huv]

theorem adapted_pull {h : V → V → L} {l : ℕ} {e f e' f' : Fin l → V} {W W' : Submodule L V} {u : Fin l → L}
    {Λ : AddSubgroup V} {k : V ≃ₗ[L] V} (hk : IsIso h k) (he : ∀ i, k (e i) = e' i) (hf : ∀ i, k (f i) = f' i)
    (hW : ∀ w ∈ W, k w ∈ W') (hA : IsAdapted h e' f' W' u Λ) : IsAdapted h e f W u (pull k Λ) := by
  intro a b w hw
  rw [mem_pull]
  have : k (∑ i, a i • e i + ∑ i, b i • f i + w) = ∑ i, a i • e' i + ∑ i, b i • f' i + k w := by
    simp [map_add, map_sum, he, hf]
  rw [this, hA a b (k w) (hW w hw), hk]

theorem adapted_reindex {h : V → V → L} {l l' : ℕ} {e f : Fin l' → V} {W : Submodule L V} {u : Fin l' → L}
    {Λ : AddSubgroup V} (hA : IsAdapted h e f W u Λ) (τ : Fin l ≃ Fin l') :
    IsAdapted h (e ∘ τ) (f ∘ τ) W (u ∘ τ) Λ := by
  intro a b w hw
  have h1 : ∑ i, a i • (e ∘ τ) i = ∑ j, (a ∘ τ.symm) j • e j :=
    Fintype.sum_equiv τ _ _ (fun i => by simp)
  have h2 : ∑ i, b i • (f ∘ τ) i = ∑ j, (b ∘ τ.symm) j • f j :=
    Fintype.sum_equiv τ _ _ (fun i => by simp)
  rw [h1, h2, hA _ _ w hw]
  simp only [Function.comp]
  refine and_congr ?_ (and_congr ?_ Iff.rfl)
  · exact ⟨fun H i => by simpa using H (τ i), fun H j => by simpa using H (τ.symm j)⟩
  · exact ⟨fun H i => by simpa using H (τ i), fun H j => by simpa using H (τ.symm j)⟩

theorem adapted_tor {s : L →+* L} (hs : IsInv s) {h : V → V → L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
    {u : Fin l → L} {Λ : AddSubgroup V} {t : V ≃ₗ[L] V} (hu : ∀ i, u i ≠ 0) (ht : IsTor s e f W u t)
    (hA : IsAdapted h e f W u Λ) : IsAdapted h e f W (fun _ => 1) (pull t Λ) := by
  intro a b w hw
  rw [mem_pull]
  have : t (∑ i, a i • e i + ∑ i, b i • f i + w) =
      ∑ i, (a i * u i) • e i + ∑ i, (b i * (s (u i))⁻¹) • f i + w := by
    simp [map_add, map_sum, ht.1, ht.2.1, ht.2.2 w hw, smul_smul]
  rw [this, hA _ _ w hw]
  have hn : ∀ i, ‖s (u i)‖ = ‖u i‖ := fun i => hs.2.1 _
  have hp : ∀ i, 0 < ‖u i‖ := fun i => norm_pos_iff.2 (hu i)
  refine and_congr (forall_congr' fun i => ?_) (and_congr (forall_congr' fun i => ?_) Iff.rfl)
  · rw [norm_mul, norm_one]
    exact ⟨fun H => le_of_mul_le_mul_right (by simpa using H) (hp i), fun H => by simpa using mul_le_mul_of_nonneg_right H (hp i).le⟩
  · rw [norm_mul, norm_inv, hn, norm_one]
    have := inv_pos.2 (hp i)
    exact ⟨fun H => le_of_mul_le_mul_right (by simpa using H) this, fun H => by simpa using mul_le_mul_of_nonneg_right H this.le⟩

theorem norm_discrete {p : L} (hp0 : p ≠ 0) (hp1 : ‖p‖ < 1) (hpu : ∀ a : L, ‖a‖ < 1 → ‖a‖ ≤ ‖p‖) {x : L} (hx : x ≠ 0) :
    ∃ n : ℤ, ‖x‖ = ‖p‖ ^ n := by
  have hpp : 0 < ‖p‖ := norm_pos_iff.2 hp0
  have hc : 1 < ‖p‖⁻¹ := (one_lt_inv₀ hpp).2 hp1
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow (norm_pos_iff.2 hx) hc
  refine ⟨-n, ?_⟩
  have hcn : 0 < ‖p‖⁻¹ ^ n := zpow_pos (inv_pos.2 hpp) n
  set y : L := x * p ^ n with hy
  have hyn : ‖y‖ = ‖x‖ * ‖p‖ ^ n := by simp [hy, norm_zpow]
  have hinv : ‖p‖ ^ n * ‖p‖⁻¹ ^ n = 1 := by
    rw [inv_zpow, mul_inv_cancel₀ (zpow_ne_zero _ hpp.ne')]
  have hpn : 0 < ‖p‖ ^ n := zpow_pos hpp n
  have hy1 : 1 ≤ ‖y‖ := by
    rw [hyn, ← hinv, mul_comm ‖x‖]
    exact mul_le_mul_of_nonneg_left hn1 hpn.le
  have hy2 : ‖y‖ * ‖p‖ < 1 := by
    have : ‖x‖ * ‖p‖ ^ n < ‖p‖⁻¹ := by
      have h3 := mul_lt_mul_of_pos_right hn2 hpn
      rw [zpow_add₀ (inv_pos.2 hpp).ne', zpow_one] at h3
      calc ‖x‖ * ‖p‖ ^ n < ‖p‖⁻¹ ^ n * ‖p‖⁻¹ * ‖p‖ ^ n := h3
        _ = ‖p‖⁻¹ := by
          rw [mul_right_comm, mul_comm (‖p‖⁻¹ ^ n), hinv, one_mul]
    rw [hyn]
    calc ‖x‖ * ‖p‖ ^ n * ‖p‖ < ‖p‖⁻¹ * ‖p‖ := mul_lt_mul_of_pos_right this hpp
      _ = 1 := inv_mul_cancel₀ hpp.ne'
  have hy3 : ‖y‖ ≤ 1 := by
    have := hpu (y * p) (by simpa using hy2)
    rw [norm_mul] at this
    exact le_of_mul_le_mul_right (by simpa using this) hpp
  have hy4 : ‖y‖ = 1 := le_antisymm hy3 hy1
  rw [hyn] at hy4
  rw [zpow_neg]
  exact eq_inv_of_mul_eq_one_left hy4

theorem exists_antitone_perm {n : ℕ} (m : Fin n → ℕ) : ∃ σ : Equiv.Perm (Fin n), Antitone (m ∘ σ) := by
  refine ⟨Tuple.sort (fun i => OrderDual.toDual (m i)), ?_⟩
  have := Tuple.monotone_sort (fun i => OrderDual.toDual (m i))
  intro i j hij
  exact this hij

end SlopeTestRemainingChoices

section Lem
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]

theorem isLat_pull (k : V ≃ₗ[L] V) {Λ : AddSubgroup V} (hΛ : IsLat L Λ) : IsLat L (pull k Λ) := by
  obtain ⟨m, b, hb⟩ := hΛ
  refine ⟨m, b.map k.symm, fun x => ?_⟩
  rw [mem_pull, hb]
  simp [Module.Basis.map_repr]

theorem isMax_pull {h : V → V → L} {Λ : AddSubgroup V} (hM : IsMax h Λ)
    {g : V ≃ₗ[L] V} (hg : IsIso h g) : IsMax h (pull g⁻¹ Λ) := by
  have hgi := isIso_inv hg
  have h1 : ∀ z, g (g⁻¹ z) = z := fun z => by
    change (g * g⁻¹) z = z
    simp
  have h2 : ∀ z, g⁻¹ (g z) = z := fun z => by
    change (g⁻¹ * g) z = z
    simp
  refine ⟨isLat_pull _ hM.1, fun x hx => ?_, fun Λ' hl hi hle => ?_⟩
  · rw [← hgi x x]
    exact hM.2.1 _ hx
  · have key : pull g Λ' = Λ := hM.2.2 _ (isLat_pull _ hl) (fun x hx => by
      have : ‖h (g x) (g x)‖ ≤ 1 := hi _ hx
      rwa [hg] at this) (fun x hx => by
      apply hle
      show g⁻¹ (g x) ∈ Λ
      rw [h2]
      exact hx)
    ext x
    rw [mem_pull, ← key, mem_pull, h1]

variable {s : L →+* L} {δ : L} {h : V → V → L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}

def hl (hh : IsHerm s h) (x : V) : V →ₗ[L] L where
  toFun := h x
  map_add' := hh.1 x
  map_smul' a y := by simpa using hh.2.1 a x y

theorem hl_apply (hh : IsHerm s h) (x y : V) : hl hh x y = h x y := rfl

theorem h_fe (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i j : Fin l) :
    h (f i) (e j) = if i = j then s δ else 0 := by
  rw [hh.2.2.1 (e j) (f i), hF.2.2.1]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

theorem form_e (hh : IsHerm s h) (hF : IsFrame h δ e f W) (a b : Fin l → L) {w : V} (hw : w ∈ W) (i : Fin l) :
    h (e i) (∑ j, a j • e j + ∑ j, b j • f j + w) = b i * δ := by
  change hl hh (e i) _ = _
  simp only [map_add, map_sum, map_smul, smul_eq_mul, hl_apply, hF.1, hF.2.2.1, (hF.2.2.2.1 w hw i).1]
  simp

theorem form_f (hh : IsHerm s h) (hF : IsFrame h δ e f W) (a b : Fin l → L) {w : V} (hw : w ∈ W) (i : Fin l) :
    h (f i) (∑ j, a j • e j + ∑ j, b j • f j + w) = a i * s δ := by
  change hl hh (f i) _ = _
  simp only [map_add, map_sum, map_smul, smul_eq_mul, hl_apply, h_fe hh hF, hF.2.1, (hF.2.2.2.1 w hw i).2]
  simp

theorem form_w (hh : IsHerm s h) (hF : IsFrame h δ e f W) (a b : Fin l → L) {w v : V} (hw : w ∈ W) (hv : v ∈ W) :
    h v (∑ j, a j • e j + ∑ j, b j • f j + w) = h v w := by
  have h1 : ∀ j, h v (e j) = 0 := fun j => by
    rw [hh.2.2.1 (e j) v, (hF.2.2.2.1 v hv j).1, map_zero]
  have h2 : ∀ j, h v (f j) = 0 := fun j => by
    rw [hh.2.2.1 (f j) v, (hF.2.2.2.1 v hv j).2, map_zero]
  change hl hh v _ = _
  simp only [map_add, map_sum, map_smul, smul_eq_mul, hl_apply, h1, h2]
  simp

theorem frame_form (hh : IsHerm s h) (hF : IsFrame h δ e f W) (a b a' b' : Fin l → L) {w w' : V} (hw : w ∈ W)
    (hw' : w' ∈ W) :
    h (∑ j, a' j • e j + ∑ j, b' j • f j + w') (∑ j, a j • e j + ∑ j, b j • f j + w) =
      ∑ j, a j * s (b' j * δ) + ∑ j, b j * s (a' j * s δ) + s (h w w') := by
  set y := ∑ j, a' j • e j + ∑ j, b' j • f j + w' with hy
  have h1 : ∀ j, h y (e j) = s (b' j * δ) := fun j => by
    rw [hh.2.2.1 (e j) y, hy, form_e hh hF a' b' hw' j]
  have h2 : ∀ j, h y (f j) = s (a' j * s δ) := fun j => by
    rw [hh.2.2.1 (f j) y, hy, form_f hh hF a' b' hw' j]
  have h3 : h y w = s (h w w') := by
    rw [hh.2.2.1 w y, hy, form_w hh hF a' b' hw' hw]
  change hl hh y _ = _
  simp only [map_add, map_sum, map_smul, smul_eq_mul, hl_apply, h1, h2, h3]

def permMap (hh : IsHerm s h) (δ : L) (e f : Fin l → V) (τ : Equiv.Perm (Fin l)) : V →ₗ[L] V :=
  LinearMap.id + ∑ i, (((s δ)⁻¹ • hl hh (f i)).smulRight (e (τ i) - e i) +
    (δ⁻¹ • hl hh (e i)).smulRight (f (τ i) - f i))

theorem permMap_apply (hδ : δ ≠ 0) (hh : IsHerm s h) (hF : IsFrame h δ e f W) (τ : Equiv.Perm (Fin l))
    (a b : Fin l → L) {w : V} (hw : w ∈ W) :
    permMap hh δ e f τ (∑ j, a j • e j + ∑ j, b j • f j + w) =
      ∑ j, a (τ.symm j) • e j + ∑ j, b (τ.symm j) • f j + w := by
  have hsδ : s δ ≠ 0 := (map_ne_zero s).2 hδ
  have he : ∑ j, a (τ.symm j) • e j = ∑ i, a i • e (τ i) :=
    (Equiv.sum_comp τ (fun j => a (τ.symm j) • e j)).symm.trans (by simp)
  have hf : ∑ j, b (τ.symm j) • f j = ∑ i, b i • f (τ i) :=
    (Equiv.sum_comp τ (fun j => b (τ.symm j) • f j)).symm.trans (by simp)
  rw [he, hf]
  simp only [permMap, LinearMap.add_apply, LinearMap.id_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, hl_apply, form_e hh hF a b hw, form_f hh hF a b hw, smul_eq_mul]
  have c1 : ∀ i, (s δ)⁻¹ * (a i * s δ) = a i := fun i => by field_simp
  have c2 : ∀ i, δ⁻¹ * (b i * δ) = b i := fun i => by field_simp
  simp only [c1, c2, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

theorem frame_perm {δ : L} (hδ : δ ≠ 0) {h : V → V → L} (hh : IsHerm s h) {l : ℕ}
    {e f : Fin l → V} {W : Submodule L V} (hF : IsFrame h δ e f W) (σ : Equiv.Perm (Fin l)) :
    ∃ P : V ≃ₗ[L] V, IsIso h P ∧ (∀ i, P (e i) = e (σ i)) ∧ (∀ i, P (f i) = f (σ i)) ∧ ∀ w ∈ W, P w = w := by
  have hinv : ∀ τ : Equiv.Perm (Fin l), permMap hh δ e f τ ∘ₗ permMap hh δ e f τ.symm = LinearMap.id := by
    intro τ
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, b, w, hw, rfl⟩ := hF.2.2.2.2.2 x
    rw [LinearMap.comp_apply, permMap_apply hδ hh hF _ a b hw, permMap_apply hδ hh hF _ _ _ hw]
    simp
  let P : V ≃ₗ[L] V := LinearEquiv.ofLinear (permMap hh δ e f σ) (permMap hh δ e f σ.symm) (hinv σ)
    (by simpa using hinv σ.symm)
  have hP : ∀ x, P x = permMap hh δ e f σ x := fun _ => rfl
  have he : ∀ j, e j = ∑ i, (Pi.single j (1 : L) : Fin l → L) i • e i + ∑ i, (0 : Fin l → L) i • f i + 0 := fun j => by
    simp [Pi.single_apply, ite_smul]
  have hf : ∀ j, f j = ∑ i, (0 : Fin l → L) i • e i + ∑ i, (Pi.single j (1 : L) : Fin l → L) i • f i + 0 := fun j => by
    simp [Pi.single_apply, ite_smul]
  have hw0 : ∀ w, w = ∑ i, (0 : Fin l → L) i • e i + ∑ i, (0 : Fin l → L) i • f i + w := fun w => by simp
  refine ⟨P, fun x y => ?_, fun i => ?_, fun i => ?_, fun w hw => ?_⟩
  · obtain ⟨a, b, w, hw, rfl⟩ := hF.2.2.2.2.2 x
    obtain ⟨a', b', w', hw', rfl⟩ := hF.2.2.2.2.2 y
    rw [hP, hP, permMap_apply hδ hh hF _ _ _ hw, permMap_apply hδ hh hF _ _ _ hw', frame_form hh hF _ _ _ _ hw' hw,
      frame_form hh hF _ _ _ _ hw' hw,
      Equiv.sum_comp σ.symm (fun j => a' j * s (b j * δ)), Equiv.sum_comp σ.symm (fun j => b' j * s (a j * s δ))]
  · rw [hP, he i, permMap_apply hδ hh hF _ _ _ W.zero_mem]
    simp [Pi.single_apply, ite_smul, Equiv.symm_apply_eq]
  · rw [hP, hf i, permMap_apply hδ hh hF _ _ _ W.zero_mem]
    simp [Pi.single_apply, ite_smul, Equiv.symm_apply_eq]
  · rw [hP]
    conv_lhs => rw [hw0 w]
    rw [permMap_apply hδ hh hF _ _ _ hw]
    simp

theorem flip_sum (F : Fin l → Prop) [DecidablePred F] (c : L) (a b : Fin l → L) :
    ∑ i, a i • (if F i then f i else e i) + ∑ i, b i • (if F i then c • e i else f i) =
      ∑ i, (if F i then c * b i else a i) • e i + ∑ i, (if F i then a i else b i) • f i := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [smul_smul, add_comm, mul_comm (b i)]
  · rfl

theorem adapted_flip (F : Fin l → Prop) [DecidablePred F] {c : L} (hc : ‖c‖ = 1) {u v : Fin l → L}
    {Λ : AddSubgroup V} (hv : ∀ i, ‖v i‖ = if F i then ‖u i‖⁻¹ else ‖u i‖) (hA : IsAdapted h e f W u Λ) :
    IsAdapted h (fun i => if F i then f i else e i) (fun i => if F i then c • e i else f i) W v Λ := by
  intro a b w hw
  rw [flip_sum, hA _ _ w hw, ← and_assoc, ← and_assoc, ← forall_and, ← forall_and]
  refine and_congr (forall_congr' fun i => ?_) Iff.rfl
  rw [hv i]
  by_cases hF : F i
  · simp only [hF, if_true, norm_mul, hc, one_mul, inv_inv]
    exact and_comm
  · simp only [hF, if_false]

theorem hermitian_frame_partial_flip (hs : IsInv s) (hδ : δ ≠ 0) (hh : IsHerm s h) (hF : IsFrame h δ e f W)
    (F : Fin l → Prop) [DecidablePred F] :
    IsFrame h δ (fun i => if F i then f i else e i) (fun i => if F i then (δ / s δ) • e i else f i) W := by
  have hsδ : s δ ≠ 0 := (map_ne_zero s).2 hδ
  set c := δ / s δ with hc
  have hc0 : c ≠ 0 := div_ne_zero hδ hsδ
  have hl1 : ∀ (a : L) x y, h (a • x) y = s a * h x y := fun a x y => by
    rw [hh.2.2.1 y (a • x), hh.2.1, map_mul, ← hh.2.2.1 y x]
  have hr1 : ∀ (a : L) x y, h x (a • y) = a * h x y := hh.2.1
  have hne : ∀ {i j}, F i → ¬ F j → i ≠ j := fun hi hj hij => hj (hij ▸ hi)
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun w hw i => ?_, hF.2.2.2.2.1, fun x => ?_⟩
  · by_cases h1 : F i <;> by_cases h2 : F j <;> simp only [h1, h2, if_true, if_false]
    · exact hF.2.1 i j
    · rw [h_fe hh hF, if_neg (hne h1 h2)]
    · rw [hF.2.2.1, if_neg (fun hij : i = j => h1 (hij ▸ h2))]
    · exact hF.1 i j
  · by_cases h1 : F i <;> by_cases h2 : F j <;> simp only [h1, h2, if_true, if_false]
    · rw [hl1, hr1, hF.1]
      simp
    · rw [hl1, hF.2.2.1, if_neg (hne h1 h2)]
      simp
    · rw [hr1, h_fe hh hF, if_neg (fun hij : i = j => h1 (hij ▸ h2))]
      simp
    · exact hF.2.1 i j
  · by_cases h1 : F i <;> by_cases h2 : F j <;> simp only [h1, h2, if_true, if_false]
    · rw [hr1, h_fe hh hF]
      by_cases hij : i = j
      · simp [hij, hc, hsδ]
      · simp [hij]
    · rw [hF.2.1, if_neg (hne h1 h2)]
    · rw [hr1, hF.1, if_neg (fun hij : i = j => h1 (hij ▸ h2))]
      simp
    · exact hF.2.2.1 i j
  · have := hF.2.2.2.1 w hw i
    by_cases h1 : F i <;> simp only [h1, if_true, if_false]
    · rw [hl1, this.1, this.2]
      simp
    · exact this
  · obtain ⟨a, b, w, hw, rfl⟩ := hF.2.2.2.2.2 x
    refine ⟨fun i => if F i then b i else a i, fun i => if F i then c⁻¹ * a i else b i, w, hw, ?_⟩
    rw [flip_sum]
    congr 2
    · refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h1 : F i
      · simp [h1, hc0]
      · simp [h1]
    · refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h1 : F i <;> simp [h1]

theorem frame_flip (hs : IsInv s) (hδ : δ ≠ 0) (hh : IsHerm s h)
    {u : Fin l → L} {Λ Λ' : AddSubgroup V} (hF : IsFrame h δ e f W)
    (h1 : IsAdapted h e f W (fun _ => 1) Λ) (h2 : IsAdapted h e f W u Λ') (p : L) (n : Fin l → ℤ)
    (hn : ∀ i, ‖u i‖ = ‖p‖ ^ n i) (hp0 : p ≠ 0) :
    ∃ (e' f' : Fin l → V) (m : Fin l → ℕ), IsFrame h δ e' f' W ∧ IsAdapted h e' f' W (fun _ => 1) Λ ∧
      IsAdapted h e' f' W (fun i => p ^ m i) Λ' := by
  have hsδ : s δ ≠ 0 := (map_ne_zero s).2 hδ
  have hc : ‖δ / s δ‖ = 1 := by
    rw [norm_div, hs.2.1, div_self (norm_ne_zero_iff.2 hδ)]
  refine ⟨_, _, fun i => (n i).natAbs, hermitian_frame_partial_flip hs hδ hh hF (fun i => n i < 0),
    adapted_flip (fun i => n i < 0) hc (fun i => ?_) h1, adapted_flip (fun i => n i < 0) hc (fun i => ?_) h2⟩
  · simp
  · rw [hn i, norm_pow]
    have hpp : ‖p‖ ≠ 0 := norm_ne_zero_iff.2 hp0
    by_cases hi : n i < 0
    · rw [if_pos hi, ← zpow_neg, ← zpow_natCast]
      congr 1
      beta_reduce
      omega
    · rw [if_neg hi, ← zpow_natCast]
      congr 1
      beta_reduce
      omega
end Lem

theorem stDecomp_of_frame_witt_tor : StFrame → StWitt → StTor → StDecomp := by
  intro hFr hWi hT L _ _ _ _ s hs δ hδ V _ _ _ h hh l e f W Λ hF hM hA p hp0 hp1 hpu g hg
  have hδ0 : δ ≠ 0 := hδ.1
  have hM' := isMax_pull hM hg
  obtain ⟨l', e₁, f₁, W₁, u, hu, hF₁, hA₁, hA₂⟩ := hFr L s hs δ hδ V h hh Λ (pull g⁻¹ Λ) hM hM'
  choose n hn using fun i => norm_discrete hp0 hp1 hpu (hu i)
  obtain ⟨e₂, f₂, m, hF₂, hA₃, hA₄⟩ := frame_flip hs hδ0 hh hF₁ hA₁ hA₂ p n hn hp0
  obtain ⟨q, k₀, hk₀, hke, hkf, hkW⟩ := hWi L s hs δ hδ V h hh l l' e f W e₂ f₂ W₁ hF hF₂
  obtain ⟨σ, hσ⟩ := exists_antitone_perm (m ∘ q)
  obtain ⟨P, hP, hPe, hPf, hPW⟩ := frame_perm hδ0 hh hF σ
  have hk : IsIso h (k₀ * P) := isIso_mul hk₀ hP
  have he' : ∀ i, (k₀ * P) (e i) = (e₂ ∘ (σ.trans q)) i := fun i => by
    simp [LinearEquiv.mul_apply, hPe, hke]
  have hf' : ∀ i, (k₀ * P) (f i) = (f₂ ∘ (σ.trans q)) i := fun i => by
    simp [LinearEquiv.mul_apply, hPf, hkf]
  have hW' : ∀ w ∈ W, (k₀ * P) w ∈ W₁ := fun w hw => by
    simpa [LinearEquiv.mul_apply, hPW w hw] using (hkW w).1 hw
  have hu' : ∀ i, p ^ (m ∘ q ∘ σ) i ≠ 0 := fun i => pow_ne_zero _ hp0
  obtain ⟨t, ht, hTt, -⟩ := hT L s hs δ hδ V h hh l e f W hF (fun i => p ^ (m ∘ q ∘ σ) i) hu'
  have hKΛ := adapted_pull (W := W) hk he' hf' hW' (adapted_reindex hA₃ (σ.trans q))
  have hKΛ' := adapted_pull (W := W) hk he' hf' hW' (adapted_reindex hA₄ (σ.trans q))
  have hTΛ' := adapted_tor hs hu' hTt hKΛ'
  have hkeep : ∀ x, (k₀ * P) x ∈ Λ ↔ x ∈ Λ := fun x =>
    adapted_unique hF hKΛ hA (fun _ => rfl) x
  have hfin : ∀ x, g⁻¹ ((k₀ * P) (t x)) ∈ Λ ↔ x ∈ Λ := fun x =>
    adapted_unique hF hTΛ' hA (fun _ => rfl) x
  have hgg : ∀ x, g⁻¹ (g x) = x := fun x => by
    change (g⁻¹ * g) x = x
    simp
  refine ⟨k₀ * P, t, (k₀ * P * t)⁻¹ * g, m ∘ q ∘ σ, hσ, hk, isIso_mul (isIso_inv (isIso_mul hk ht)) hg, hkeep, ?_, hTt, by group⟩
  intro x
  have h3 : (k₀ * P) (t (((k₀ * P * t)⁻¹ * g) x)) = g x := by
    change ((k₀ * P * t) * ((k₀ * P * t)⁻¹ * g)) x = g x
    rw [mul_inv_cancel_left]
  rw [← hfin, h3, hgg]

end GlobalTheory.CompanionTheory.FlDecomp
end

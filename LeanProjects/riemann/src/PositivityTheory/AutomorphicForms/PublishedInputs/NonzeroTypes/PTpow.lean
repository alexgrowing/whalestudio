import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace Grp

namespace P_Tpow

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} (G : Grp k n)

section Rep

variable {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)

theorem rep_mul_apply (g h : GL (Fin n) k) (v : V) : π (g * h) v = π g (π h v) := by
  rw [map_mul]
  rfl

theorem rep_inv_apply (g : GL (Fin n) k) (v : V) : π g⁻¹ (π g v) = v := by
  rw [← rep_mul_apply, inv_mul_cancel, map_one]
  rfl

theorem rep_apply_ne_zero (g : GL (Fin n) k) {v : V} (hv : v ≠ 0) : π g v ≠ 0 := by
  intro h
  apply hv
  have := rep_inv_apply π g v
  rw [h, map_zero] at this
  exact this.symm

theorem finsum_rep_of_infinite {ι : Type} [Infinite ι] (g : ι → GL (Fin n) k) (v : V) :
    ∑ᶠ i, π (g i) v = 0 := by
  by_cases hv : v = 0
  · subst hv
    simp
  · apply finsum_of_infinite_support
    have : Function.support (fun i => π (g i) v) = Set.univ := by
      ext i
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact rep_apply_ne_zero π (g i) hv
    rw [this]
    exact Set.infinite_univ

end Rep

theorem zEl_val (ϖ : kˣ) : ((G.zEl ϖ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
    diagonal (fun i => (ϖ : k) ^ (G.s - 1 - (G.bl i : ℕ))) := by
  ext i j
  obtain ⟨⟨a, i'⟩, rfl⟩ := G.e.surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := G.e.surjective j
  by_cases hab : a = b
  · subst hab
    rw [zEl, leviEmb_apply_same]
    simp [Grp.bl, Matrix.diagonal_apply, Matrix.scalar_apply, Units.coe_map, Matrix.diagonal_pow, Pi.pow_apply]
  · rw [zEl, leviEmb_apply_ne k G.e _ hab, Matrix.diagonal_apply_ne]
    intro h
    exact hab (by simpa using congrArg (fun t => (G.e.symm t).1) h)

theorem zEl_inv_val (ϖ : kˣ) : (((G.zEl ϖ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
    diagonal (fun i => ((ϖ : k) ^ (G.s - 1 - (G.bl i : ℕ)))⁻¹) := by
  have h0 : ∀ i : Fin n, (ϖ : k) ^ (G.s - 1 - (G.bl i : ℕ)) ≠ 0 := fun i => pow_ne_zero _ ϖ.ne_zero
  have h1 : diagonal (fun i => ((ϖ : k) ^ (G.s - 1 - (G.bl i : ℕ)))⁻¹) *
      diagonal (fun i => (ϖ : k) ^ (G.s - 1 - (G.bl i : ℕ))) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (h0 i)
  calc (((G.zEl ϖ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = (diagonal (fun i => ((ϖ : k) ^ (G.s - 1 - (G.bl i : ℕ)))⁻¹) *
          diagonal (fun i => (ϖ : k) ^ (G.s - 1 - (G.bl i : ℕ)))) *
          (((G.zEl ϖ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by rw [h1, one_mul]
    _ = diagonal (fun i => ((ϖ : k) ^ (G.s - 1 - (G.bl i : ℕ)))⁻¹) *
          (((G.zEl ϖ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *
          (((G.zEl ϖ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) := by rw [zEl_val, mul_assoc]
    _ = _ := by rw [Units.mul_inv, mul_one]

theorem unif_mem {ϖ : kˣ} (hϖ : IsUnif ϖ) : (ϖ : k) ∈ 𝒪[k] := by
  obtain ⟨w, _, hw⟩ := hϖ
  rw [← hw]
  exact w.2

theorem conj_int {ϖ : kˣ} (hϖ : IsUnif ϖ) {b : GL (Fin n) k} (hb : b ∈ G.NO) (i j : Fin n) :
    ((G.zEl ϖ * b * (G.zEl ϖ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
  rw [NO, Subgroup.mem_inf] at hb
  obtain ⟨hU, hK⟩ := hb
  have hint := ((GlobalTheory.SplitFlip.mem_KO_iff b).1 hK).1 i j
  rw [Units.val_mul, Units.val_mul, zEl_inv_val, zEl_val, mul_diagonal, diagonal_mul]
  by_cases hji : G.bl j < G.bl i
  · have h0 : (b : Matrix (Fin n) (Fin n) k) i j = 0 := (mem_parab.1 (mem_unipRad.1 hU).1) i j hji
    rw [h0, mul_zero, zero_mul]
    exact zero_mem _
  · have hle : G.s - 1 - (G.bl j : ℕ) ≤ G.s - 1 - (G.bl i : ℕ) := by
      have := Fin.not_lt.1 hji
      rw [Fin.le_def] at this
      omega
    have hp : (ϖ : k) ^ (G.s - 1 - (G.bl i : ℕ)) * (b : Matrix (Fin n) (Fin n) k) i j *
        ((ϖ : k) ^ (G.s - 1 - (G.bl j : ℕ)))⁻¹ =
        (ϖ : k) ^ ((G.s - 1 - (G.bl i : ℕ)) - (G.s - 1 - (G.bl j : ℕ))) * (b : Matrix (Fin n) (Fin n) k) i j := by
      rw [pow_sub₀ _ ϖ.ne_zero hle]
      ring
    rw [hp]
    exact mul_mem (pow_mem (unif_mem hϖ) _) hint

theorem pos {ϖ : kˣ} (hϖ : IsUnif ϖ) {b : GL (Fin n) k} (hb : b ∈ G.NO) :
    G.zEl ϖ * b * (G.zEl ϖ)⁻¹ ∈ G.NO := by
  have hb' := hb
  rw [NO, Subgroup.mem_inf] at hb' ⊢
  obtain ⟨hU, _⟩ := hb'
  refine ⟨(Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k G.e _ : G.zEl ϖ ∈ _) b).1 hU, ?_⟩
  refine (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => conj_int G hϖ hb i j, fun i j => ?_⟩
  have : (G.zEl ϖ * b * (G.zEl ϖ)⁻¹)⁻¹ = G.zEl ϖ * b⁻¹ * (G.zEl ϖ)⁻¹ := by group
  rw [this]
  exact conj_int G hϖ (inv_mem hb) i j

theorem posm {ϖ : kˣ} (hϖ : IsUnif ϖ) (m : ℕ) {b : GL (Fin n) k} (hb : b ∈ G.NO) :
    G.zEl ϖ ^ m * b * (G.zEl ϖ ^ m)⁻¹ ∈ G.NO := by
  induction m with
  | zero => simpa using hb
  | succ m ih =>
    have : G.zEl ϖ ^ (m + 1) * b * (G.zEl ϖ ^ (m + 1))⁻¹ =
        G.zEl ϖ * (G.zEl ϖ ^ m * b * (G.zEl ϖ ^ m)⁻¹) * (G.zEl ϖ)⁻¹ := by
      rw [pow_succ']
      group
    rw [this]
    exact pos G hϖ ih

theorem mem_zN (ϖ : kˣ) (m : ℕ) (a : ↥G.NO) :
    a ∈ G.zN ϖ m ↔ ∃ b ∈ G.NO, G.zEl ϖ ^ m * b * (G.zEl ϖ ^ m)⁻¹ = (a : GL (Fin n) k) := by
  rw [zN, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  rfl

theorem out_mk_eq (ϖ : kˣ) (m : ℕ) (c : ↥G.NO ⧸ G.zN ϖ m) :
    (QuotientGroup.mk (Quotient.out c) : ↥G.NO ⧸ G.zN ϖ m) = c :=
  Quotient.out_eq c

def cz {ϖ : kˣ} (hϖ : IsUnif ϖ) (b : ↥G.NO) : ↥G.NO :=
  ⟨G.zEl ϖ * (b : GL (Fin n) k) * (G.zEl ϖ)⁻¹, pos G hϖ b.2⟩

theorem cz_coe {ϖ : kˣ} (hϖ : IsUnif ϖ) (b : ↥G.NO) :
    ((cz G hϖ b : ↥G.NO) : GL (Fin n) k) = G.zEl ϖ * (b : GL (Fin n) k) * (G.zEl ϖ)⁻¹ := rfl

def psi {ϖ : kˣ} (hϖ : IsUnif ϖ) (m : ℕ) (p : (↥G.NO ⧸ G.zN ϖ 1) × (↥G.NO ⧸ G.zN ϖ m)) :
    ↥G.NO ⧸ G.zN ϖ (m + 1) :=
  QuotientGroup.mk ((Quotient.out p.1 : ↥G.NO) * cz G hϖ (Quotient.out p.2))

theorem psi_injective {ϖ : kˣ} (hϖ : IsUnif ϖ) (m : ℕ) : Function.Injective (psi G hϖ m) := by
  rintro ⟨p1, p2⟩ ⟨q1, q2⟩ hpq
  unfold psi at hpq
  rw [QuotientGroup.eq, mem_zN] at hpq
  obtain ⟨w, hw, e⟩ := hpq
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, cz_coe] at e
  have h1 : p1 = q1 := by
    rw [← out_mk_eq G ϖ 1 p1, ← out_mk_eq G ϖ 1 q1, QuotientGroup.eq, mem_zN]
    refine ⟨(Quotient.out p2 : ↥G.NO) * (G.zEl ϖ ^ m * w * (G.zEl ϖ ^ m)⁻¹) * (Quotient.out q2 : ↥G.NO)⁻¹,
      mul_mem (mul_mem (Quotient.out p2).2 (posm G hϖ m hw)) (inv_mem (Quotient.out q2).2), ?_⟩
    have key : G.zEl ϖ ^ 1 * ((Quotient.out p2 : ↥G.NO) * (G.zEl ϖ ^ m * w * (G.zEl ϖ ^ m)⁻¹) *
        (Quotient.out q2 : ↥G.NO)⁻¹) * (G.zEl ϖ ^ 1)⁻¹ =
        (G.zEl ϖ * (Quotient.out p2 : ↥G.NO) * (G.zEl ϖ)⁻¹) *
        (G.zEl ϖ ^ (m + 1) * w * (G.zEl ϖ ^ (m + 1))⁻¹) *
        (G.zEl ϖ * (Quotient.out q2 : ↥G.NO) * (G.zEl ϖ)⁻¹)⁻¹ := by
      rw [pow_one, pow_succ']
      simp only [Subgroup.coe_inv]
      group
    rw [key, e, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  subst h1
  have h2 : p2 = q2 := by
    rw [← out_mk_eq G ϖ m p2, ← out_mk_eq G ϖ m q2, QuotientGroup.eq, mem_zN]
    refine ⟨w, hw, ?_⟩
    have key : G.zEl ϖ * (G.zEl ϖ ^ m * w * (G.zEl ϖ ^ m)⁻¹) * (G.zEl ϖ)⁻¹ =
        G.zEl ϖ ^ (m + 1) * w * (G.zEl ϖ ^ (m + 1))⁻¹ := by
      rw [pow_succ']
      group
    rw [e] at key
    have key2 : G.zEl ϖ ^ m * w * (G.zEl ϖ ^ m)⁻¹ =
        (G.zEl ϖ)⁻¹ * ((((Quotient.out p1 : ↥G.NO) : GL (Fin n) k) *
          (G.zEl ϖ * (Quotient.out p2 : ↥G.NO) * (G.zEl ϖ)⁻¹))⁻¹ *
          (((Quotient.out p1 : ↥G.NO) : GL (Fin n) k) *
          (G.zEl ϖ * (Quotient.out q2 : ↥G.NO) * (G.zEl ϖ)⁻¹))) * G.zEl ϖ := by
      rw [← key]
      group
    rw [key2, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [h2]

theorem psi_surjective {ϖ : kˣ} (hϖ : IsUnif ϖ) (m : ℕ) : Function.Surjective (psi G hϖ m) := by
  intro c
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective c
  have e1' := out_mk_eq G ϖ 1 (QuotientGroup.mk h)
  rw [QuotientGroup.eq, mem_zN] at e1'
  obtain ⟨b, hb, e1⟩ := e1'
  have e2' := out_mk_eq G ϖ m (QuotientGroup.mk (⟨b, hb⟩ : ↥G.NO))
  rw [QuotientGroup.eq, mem_zN] at e2'
  obtain ⟨w, hw, e2⟩ := e2'
  refine ⟨(QuotientGroup.mk h, QuotientGroup.mk ⟨b, hb⟩), ?_⟩
  unfold psi
  rw [QuotientGroup.eq, mem_zN]
  refine ⟨w, hw, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, cz_coe] at e1 e2 ⊢
  rw [pow_one] at e1
  calc G.zEl ϖ ^ (m + 1) * w * (G.zEl ϖ ^ (m + 1))⁻¹
      = G.zEl ϖ * (G.zEl ϖ ^ m * w * (G.zEl ϖ ^ m)⁻¹) * (G.zEl ϖ)⁻¹ := by
        rw [pow_succ']
        group
    _ = G.zEl ϖ * (((Quotient.out (QuotientGroup.mk (⟨b, hb⟩ : ↥G.NO) : ↥G.NO ⧸ G.zN ϖ m) : ↥G.NO) :
          GL (Fin n) k)⁻¹ * b) * (G.zEl ϖ)⁻¹ := by rw [e2]
    _ = (G.zEl ϖ * ((Quotient.out (QuotientGroup.mk (⟨b, hb⟩ : ↥G.NO) : ↥G.NO ⧸ G.zN ϖ m) : ↥G.NO) :
          GL (Fin n) k) * (G.zEl ϖ)⁻¹)⁻¹ * (G.zEl ϖ * b * (G.zEl ϖ)⁻¹) := by group
    _ = _ := by
        rw [e1]
        group

def psiEquiv {ϖ : kˣ} (hϖ : IsUnif ϖ) (m : ℕ) :
    (↥G.NO ⧸ G.zN ϖ 1) × (↥G.NO ⧸ G.zN ϖ m) ≃ ↥G.NO ⧸ G.zN ϖ (m + 1) :=
  Equiv.ofBijective (psi G hϖ m) ⟨psi_injective G hϖ m, psi_surjective G hϖ m⟩

theorem sub0 (ϖ : kˣ) : Subsingleton (↥G.NO ⧸ G.zN ϖ 0) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  rw [QuotientGroup.eq, mem_zN]
  exact ⟨_, (a⁻¹ * b).2, by simp⟩

theorem finite_all {ϖ : kˣ} (hϖ : IsUnif ϖ) (h1 : Finite (↥G.NO ⧸ G.zN ϖ 1)) (m : ℕ) :
    Finite (↥G.NO ⧸ G.zN ϖ m) := by
  induction m with
  | zero =>
    haveI := sub0 G ϖ
    exact Finite.of_subsingleton
  | succ m ih => exact Finite.of_equiv _ (psiEquiv G hϖ m)

theorem infinite_succ {ϖ : kˣ} (hϖ : IsUnif ϖ) (h1 : Infinite (↥G.NO ⧸ G.zN ϖ 1)) (m : ℕ) :
    Infinite (↥G.NO ⧸ G.zN ϖ (m + 1)) := by
  haveI : Nonempty (↥G.NO ⧸ G.zN ϖ m) := ⟨QuotientGroup.mk 1⟩
  exact Infinite.of_injective _ (psiEquiv G hϖ m).injective

section Op

variable {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)

theorem summand_out (ϖ : kˣ) (x : V) (hfix : ∀ h ∈ G.NO, π h x = x) (m : ℕ) (h : ↥G.NO) :
    π ((Quotient.out (QuotientGroup.mk h : ↥G.NO ⧸ G.zN ϖ m) : ↥G.NO) : GL (Fin n) k) (π (G.zEl ϖ ^ m) x) =
      π (h : GL (Fin n) k) (π (G.zEl ϖ ^ m) x) := by
  have e' := out_mk_eq G ϖ m (QuotientGroup.mk h)
  rw [QuotientGroup.eq, mem_zN] at e'
  obtain ⟨b, hb, e⟩ := e'
  have hh : (h : GL (Fin n) k) = ((Quotient.out (QuotientGroup.mk h : ↥G.NO ⧸ G.zN ϖ m) : ↥G.NO) :
      GL (Fin n) k) * (G.zEl ϖ ^ m * b * (G.zEl ϖ ^ m)⁻¹) := by
    rw [e, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [hh]
  simp only [rep_mul_apply, rep_inv_apply, hfix b hb]

theorem tz_zero (ϖ : kˣ) (x : V) (hfix : ∀ h ∈ G.NO, π h x = x) : G.Tz π ϖ 0 x = x := by
  haveI := sub0 G ϖ
  haveI : Unique (↥G.NO ⧸ G.zN ϖ 0) := uniqueOfSubsingleton (QuotientGroup.mk 1)
  unfold Tz
  rw [finsum_unique]
  rw [pow_zero, map_one]
  exact hfix _ (Subtype.prop _)

theorem tz_succ {ϖ : kˣ} (hϖ : IsUnif ϖ) (x : V) (hfix : ∀ h ∈ G.NO, π h x = x) (m : ℕ)
    (h1 : Finite (↥G.NO ⧸ G.zN ϖ 1)) : G.Tz π ϖ (m + 1) x = G.Tz π ϖ 1 (G.Tz π ϖ m x) := by
  haveI := h1
  haveI := finite_all G hϖ h1 m
  haveI := finite_all G hϖ h1 (m + 1)
  letI := Fintype.ofFinite (↥G.NO ⧸ G.zN ϖ 1)
  letI := Fintype.ofFinite (↥G.NO ⧸ G.zN ϖ m)
  letI := Fintype.ofFinite (↥G.NO ⧸ G.zN ϖ (m + 1))
  unfold Tz
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← Equiv.sum_comp (psiEquiv G hϖ m), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c1 _ => ?_
  rw [pow_one, map_sum, map_sum]
  refine Finset.sum_congr rfl fun c2 _ => ?_
  show π ((Quotient.out (psi G hϖ m (c1, c2)) : ↥G.NO) : GL (Fin n) k) (π (G.zEl ϖ ^ (m + 1)) x) = _
  unfold psi
  rw [summand_out G π ϖ x hfix (m + 1), Subgroup.coe_mul, cz_coe, pow_succ']
  simp only [rep_mul_apply, rep_inv_apply]

theorem tz_iter {ϖ : kˣ} (hϖ : IsUnif ϖ) (x : V) (hfix : ∀ h ∈ G.NO, π h x = x) (m : ℕ) :
    G.Tz π ϖ m x = (G.Tz π ϖ 1)^[m] x := by
  by_cases hfin : Finite (↥G.NO ⧸ G.zN ϖ 1)
  · induction m with
    | zero => rw [Function.iterate_zero_apply]; exact tz_zero G π ϖ x hfix
    | succ m ih => rw [Function.iterate_succ_apply', ← ih]; exact tz_succ G π hϖ x hfix m hfin
  · rw [not_finite_iff_infinite] at hfin
    cases m with
    | zero => rw [Function.iterate_zero_apply]; exact tz_zero G π ϖ x hfix
    | succ m =>
      haveI := hfin
      haveI := infinite_succ G hϖ hfin m
      rw [Function.iterate_succ_apply']
      unfold Tz
      rw [finsum_rep_of_infinite π _ _, finsum_rep_of_infinite π _ _]

end Op

end P_Tpow

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} (G : Grp k n)

theorem step_Tpow : TorusPowerProp G := by
  unfold TorusPowerProp
  intro _ _ _ _ _ _ _ hU _ _ ϖ hϖ V _ _ π x hx m
  refine P_Tpow.tz_iter G π hϖ x (fun h hh => ?_) m
  have hJ := hU.1 h hh
  have := (show ∀ g ∈ G.JSet, π g x = G.lam g • x from hx) h hJ.1
  rw [this, hJ.2, one_smul]

end Grp

end UpperTheory.TNZ

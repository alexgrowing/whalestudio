import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin

open MulAction

private theorem idx {H T : Type} [Group H] [CommGroup T] (φ : H →* T) (H₀ : Subgroup H) (C S : Subgroup T) (hS : S ≤ C)
    (h0 : H₀ ≤ S.comap φ) :
    (φ.range ⊔ S).index * H₀.relIndex (C.comap φ) = (φ.range ⊔ C).index * S.relIndex C * H₀.relIndex (S.comap φ) := by
  set R := φ.range
  have hA := Subgroup.relIndex_mul_relIndex H₀ (S.comap φ) (C.comap φ) h0 (Subgroup.comap_mono hS)
  have hB := Subgroup.relIndex_mul_index (H := R ⊔ S) (K := R ⊔ C) (sup_le_sup_left hS R)
  have hC : (S.comap φ).relIndex (C.comap φ) = S.relIndex (R ⊓ C) := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq]
  have hD : (R ⊔ S).relIndex (R ⊔ C) = (R ⊔ S).relIndex C := by
    have : R ⊔ C = (R ⊔ S) ⊔ C := by
      rw [sup_assoc, sup_eq_right.mpr hS]
    rw [this, Subgroup.relIndex_sup_left]
  have hE : S ⊔ (R ⊓ C) = (R ⊔ S) ⊓ C := by
    apply le_antisymm
    · exact sup_le (le_inf le_sup_right hS) (inf_le_inf_right C le_sup_left)
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨r, hr, s, hs, rfl⟩ := Subgroup.mem_sup.mp hx1
      have hrC : r ∈ C := by
        have := C.mul_mem hx2 (C.inv_mem (hS hs))
        simpa using this
      rw [mul_comm]
      exact Subgroup.mem_sup.mpr ⟨s, hs, r, Subgroup.mem_inf.mpr ⟨hr, hrC⟩, rfl⟩
  have hF : S.relIndex (R ⊓ C) = S.relIndex ((R ⊔ S) ⊓ C) := by
    rw [← hE, Subgroup.relIndex_sup_left]
  have hG := Subgroup.relIndex_inf_mul_relIndex S (R ⊔ S) C
  rw [show S ⊓ (R ⊔ S) = S from inf_eq_left.mpr le_sup_right] at hG
  rw [← hB, ← hA, hC, hD, ← hG, ← hF]
  ring

private theorem card_fib {H T Y : Type} [Group H] [CommGroup T] [MulAction T Y] [MulAction H Y] (φ : H →* T)
    (hφ : ∀ h (y : Y), h • y = φ h • y) (O : orbitRel.Quotient T Y) :
    Nat.card {o : orbitRel.Quotient H Y // (Quotient.mk'' o.out : orbitRel.Quotient T Y) = O} = (φ.range ⊔ stabilizer T O.out).index := by
  classical
  set y₀ : Y := O.out with hy₀
  set K : Subgroup T := φ.range ⊔ stabilizer T y₀
  have hO : (Quotient.mk'' y₀ : orbitRel.Quotient T Y) = O := Quotient.out_eq' O
  have fib : ∀ t : T, (Quotient.mk'' (Quotient.out (Quotient.mk'' (t • y₀) : orbitRel.Quotient H Y)) :
      orbitRel.Quotient T Y) = O := by
    intro t
    obtain ⟨h, hh⟩ := (Quotient.exact' (Quotient.out_eq' (Quotient.mk'' (t • y₀) : orbitRel.Quotient H Y)) :
      Quotient.out (Quotient.mk'' (t • y₀) : orbitRel.Quotient H Y) ∈ orbit H (t • y₀))
    rw [← hO]
    apply Quotient.sound'
    refine ⟨φ h * t, ?_⟩
    rw [← hh]
    show (φ h * t) • y₀ = h • t • y₀
    rw [hφ, mul_smul]
  let g : T → {o : orbitRel.Quotient H Y // (Quotient.mk'' o.out : orbitRel.Quotient T Y) = O} :=
    fun t => ⟨Quotient.mk'' (t • y₀), fib t⟩
  have resp : ∀ a b : T, a⁻¹ * b ∈ K → g a = g b := by
    intro a b hab
    obtain ⟨r, ⟨h, rfl⟩, s, hs, hrs⟩ := Subgroup.mem_sup.mp hab
    have hb : b = φ h * a * s := by
      rw [mul_comm (φ h) a, mul_assoc, hrs, mul_inv_cancel_left]
    have e : h • (a • y₀) = b • y₀ := by
      rw [hb, mul_smul, MulAction.mem_stabilizer_iff.mp hs, mul_smul, hφ]
    have e' : (Quotient.mk'' (b • y₀) : orbitRel.Quotient H Y) = Quotient.mk'' (a • y₀) :=
      Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨h, e⟩))
    exact Subtype.ext e'.symm
  let F : T ⧸ K → {o : orbitRel.Quotient H Y // (Quotient.mk'' o.out : orbitRel.Quotient T Y) = O} :=
    fun q => Quotient.liftOn' q g (fun a b hab => resp a b (QuotientGroup.leftRel_apply.mp hab))
  have hF : ∀ t : T, F (QuotientGroup.mk t) = g t := fun t => rfl
  have inj : Function.Injective F := by
    intro p q hpq
    induction p using QuotientGroup.induction_on with
    | H a =>
    induction q using QuotientGroup.induction_on with
    | H b =>
    rw [hF, hF] at hpq
    have e1 : (Quotient.mk'' (a • y₀) : orbitRel.Quotient H Y) = Quotient.mk'' (b • y₀) :=
      congrArg Subtype.val hpq
    obtain ⟨h, hh0⟩ := (Quotient.exact' e1.symm : b • y₀ ∈ orbit H (a • y₀))
    have hh : h • a • y₀ = b • y₀ := hh0
    rw [hφ, ← mul_smul] at hh
    apply QuotientGroup.eq.mpr
    refine Subgroup.mem_sup.mpr ⟨φ h, ⟨h, rfl⟩, (φ h)⁻¹ * a⁻¹ * b, ?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, ← hh, ← mul_smul, ← mul_smul]
      rw [← mul_inv_rev, mul_comm (φ h) a, inv_mul_cancel, one_smul]
    · rw [mul_assoc, mul_inv_cancel_left]
  have surj : Function.Surjective F := by
    rintro ⟨o, ho⟩
    have e2 : (Quotient.mk'' o.out : orbitRel.Quotient T Y) = Quotient.mk'' y₀ := ho.trans hO.symm
    obtain ⟨t, ht0⟩ := (Quotient.exact' e2 : o.out ∈ orbit T y₀)
    have ht : t • y₀ = o.out := ht0
    refine ⟨QuotientGroup.mk t, ?_⟩
    rw [hF]
    apply Subtype.ext
    change (Quotient.mk'' (t • y₀) : orbitRel.Quotient H Y) = o
    rw [ht]
    exact Quotient.out_eq' o
  rw [Subgroup.index]
  exact (Nat.card_congr (Equiv.ofBijective F ⟨inj, surj⟩)).symm

open UpperTheory.V.Z.Sym in
private theorem gq_mass {H T Y : Type} [Group H] [CommGroup T] [MulAction T Y] [MulAction H Y] (φ : H →* T)
    (hφ : ∀ h (y : Y), h • y = φ h • y) (H₀ : Subgroup H) (C : Subgroup T) (k : Y → ℂ) (hk : ∀ (t : T) y, k (t • y) = k y)
    (fin : {O : orbitRel.Quotient T Y | k O.out ≠ 0}.Finite) (h0 : ∀ z ∈ H₀, ∀ y : Y, φ z • y = y)
    (h1 : (φ.range ⊔ C).index ≠ 0) (h2 : H₀.relIndex (C.comap φ) ≠ 0)
    (h3 : ∀ y, k y ≠ 0 → stabilizer T y ≤ C ∧ (stabilizer T y).relIndex C ≠ 0) : gq H₀ k = mass φ H₀ C * wcount C k := by
  classical
  set R := φ.range with hR
  let π : orbitRel.Quotient H Y → orbitRel.Quotient T Y := fun o => Quotient.mk'' o.out
  have orbT : ∀ o : orbitRel.Quotient H Y, ∃ t : T, t • o.out = (π o).out := by
    intro o
    exact (Quotient.exact' (Quotient.out_eq' (π o)) : (π o).out ∈ orbit T o.out)
  have stabT : ∀ (t : T) (y : Y), stabilizer T (t • y) = stabilizer T y := by
    intro t y
    ext s
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, smul_smul, mul_comm, mul_smul]
    exact smul_left_cancel_iff t
  have stabH : ∀ y : Y, stabilizer H y = (stabilizer T y).comap φ := by
    intro y
    ext h
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, hφ]
  have kπ : ∀ o, k (π o).out = k o.out := by
    intro o
    obtain ⟨t, ht⟩ := orbT o
    rw [← ht, hk]
  have termeq : ∀ o, k o.out / (H₀.relIndex (stabilizer H o.out) : ℂ) =
      k (π o).out / (H₀.relIndex ((stabilizer T (π o).out).comap φ) : ℂ) := by
    intro o
    obtain ⟨t, ht⟩ := orbT o
    rw [← ht, hk, stabT, stabH]
  have h0S : ∀ y : Y, H₀ ≤ (stabilizer T y).comap φ :=
    fun y z hz => MulAction.mem_stabilizer_iff.mpr (h0 z hz y)
  have nzS : ∀ y : Y, k y ≠ 0 → H₀.relIndex ((stabilizer T y).comap φ) ≠ 0 := by
    intro y hy h
    apply h2
    rw [← Subgroup.relIndex_mul_relIndex H₀ _ _ (h0S y) (Subgroup.comap_mono (h3 y hy).1), h, zero_mul]
  have nzR : ∀ y : Y, k y ≠ 0 → (R ⊔ stabilizer T y).index ≠ 0 := by
    intro y hy h
    have e := idx φ H₀ C (stabilizer T y) (h3 y hy).1 (h0S y)
    rw [← hR, h, zero_mul] at e
    exact mul_ne_zero (mul_ne_zero h1 (h3 y hy).2) (nzS y hy) e.symm
  have key : ∀ y : Y, k y ≠ 0 → ((R ⊔ stabilizer T y).index : ℂ) *
      (k y / (H₀.relIndex ((stabilizer T y).comap φ) : ℂ)) =
      mass φ H₀ C * (((stabilizer T y).relIndex C : ℂ) * k y) := by
    intro y hy
    have e := congrArg (Nat.cast : ℕ → ℂ) (idx φ H₀ C (stabilizer T y) (h3 y hy).1 (h0S y))
    rw [← hR] at e
    push_cast at e
    have a1 : (H₀.relIndex ((stabilizer T y).comap φ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (nzS y hy)
    have a2 : (H₀.relIndex (C.comap φ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h2
    unfold mass
    rw [← hR, mul_div_assoc', div_mul_eq_mul_div, div_eq_div_iff a1 a2]
    linear_combination k y * e
  set sT := fin.toFinset with hsT
  have memT : ∀ O, O ∈ sT ↔ k O.out ≠ 0 := fun O => by simp [hsT]
  have finFib : ∀ O ∈ sT, {o : orbitRel.Quotient H Y | π o = O}.Finite := by
    intro O hO
    have nz := nzR O.out ((memT O).mp hO)
    rw [← card_fib φ hφ O] at nz
    exact Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero nz)
  have sHfin : {o : orbitRel.Quotient H Y | π o ∈ sT}.Finite := by
    have e : {o : orbitRel.Quotient H Y | π o ∈ sT} = ⋃ O ∈ (sT : Set _), {o | π o = O} := by
      ext o
      simp
    rw [e]
    exact Set.Finite.biUnion sT.finite_toSet (fun O hO => finFib O hO)
  set sH := sHfin.toFinset with hsH
  have memH : ∀ o, o ∈ sH ↔ π o ∈ sT := fun o => by simp [hsH]
  have lhs : gq H₀ k = ∑ o ∈ sH, k o.out / (H₀.relIndex (stabilizer H o.out) : ℂ) := by
    unfold gq
    apply finsum_eq_sum_of_support_subset
    intro o ho
    rw [Finset.mem_coe, memH, memT, kπ]
    intro h
    apply ho
    simp [h]
  have rhs : wcount C k = ∑ O ∈ sT, ((stabilizer T O.out).relIndex C : ℂ) * k O.out := by
    unfold wcount
    apply finsum_eq_sum_of_support_subset
    intro O hO
    rw [Finset.mem_coe, memT]
    intro h
    apply hO
    simp [h]
  rw [lhs, rhs, Finset.mul_sum, Finset.sum_congr rfl (fun o _ => termeq o)]
  rw [← Finset.sum_fiberwise_of_maps_to (s := sH) (t := sT) (g := π) (fun o ho => (memH o).mp ho)]
  refine Finset.sum_congr rfl (fun O hO => ?_)
  have fil : sH.filter (fun o => π o = O) = (finFib O hO).toFinset := by
    ext o
    have r : o ∈ (finFib O hO).toFinset ↔ π o = O := by
      rw [Set.Finite.mem_toFinset]
      rfl
    rw [Finset.mem_filter, memH, r]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hO, h⟩⟩
  have cnt : (sH.filter (fun o => π o = O)).card = (R ⊔ stabilizer T O.out).index := by
    rw [fil, ← Set.ncard_eq_toFinset_card _ (finFib O hO), ← Nat.card_coe_set_eq]
    exact card_fib φ hφ O
  rw [Finset.sum_congr rfl (g := fun _ => k O.out / (H₀.relIndex ((stabilizer T O.out).comap φ) : ℂ))
    (fun o ho => by rw [(Finset.mem_filter.mp ho).2]), Finset.sum_const, nsmul_eq_mul, cnt]
  exact key O.out ((memT O).mp hO)

open UpperTheory.V.Z.Sym in
theorem UpperTheory.V.Z.Sym.Tf.gqMass :
    UpperTheory.V.Z.Sym.Tf.GqMass := by
  intro H T G _ _ _ φ ι H₀ C θ U f δ hf hδ hfin h0 h1 h2 h3 hle
  letI iT : MulAction T (G ⧸ U) := MulAction.compHom _ ι
  letI iH : MulAction H (G ⧸ U) := MulAction.compHom _ (ι.comp φ)
  have hsmul : ∀ (t : T) (g : G), t • (QuotientGroup.mk g : G ⧸ U) = QuotientGroup.mk (ι t * g) :=
    fun t g => rfl
  let k : G ⧸ U → ℂ := fun y => f ((Quotient.out y)⁻¹ * δ * θ (Quotient.out y))
  have hk : ∀ (t : T) (y : G ⧸ U), k (t • y) = k y := by
    intro t y
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (ι t * y.out)
    have e : t • y = (QuotientGroup.mk (ι t * y.out) : G ⧸ U) := by
      rw [← hsmul]
      congr 1
      exact (QuotientGroup.out_eq' y).symm
    show f ((Quotient.out (t • y))⁻¹ * δ * θ (Quotient.out (t • y))) = f ((Quotient.out y)⁻¹ * δ * θ (Quotient.out y))
    rw [e, hu]
    set g := Quotient.out y
    calc f ((ι t * g * ↑u)⁻¹ * δ * θ (ι t * g * ↑u))
        = f ((↑u)⁻¹ * (g⁻¹ * ((ι t)⁻¹ * δ * θ (ι t)) * θ g) * θ ↑u) := by
          rw [map_mul, map_mul]
          congr 1
          group
      _ = f ((↑u)⁻¹ * (g⁻¹ * δ * θ g) * θ ↑u) := by rw [hδ t]
      _ = f (g⁻¹ * δ * θ g) := hf u u.2 _
  have fin : {O : orbitRel.Quotient T (G ⧸ U) | k O.out ≠ 0}.Finite := by
    obtain ⟨S, hS⟩ := hfin
    refine Set.Finite.subset (S.finite_toSet.image
      (fun s => (Quotient.mk'' (QuotientGroup.mk s : G ⧸ U) : orbitRel.Quotient T (G ⧸ U)))) ?_
    intro O hO
    obtain ⟨t, s, hs, u, hu, hg⟩ := hS _ hO
    refine ⟨s, hs, ?_⟩
    have e : O.out = t • (QuotientGroup.mk s : G ⧸ U) := by
      rw [hsmul, ← QuotientGroup.mk_mul_of_mem (ι t * s) hu, ← hg]
      exact (QuotientGroup.out_eq' _).symm
    conv_rhs => rw [← Quotient.out_eq' O]
    apply Quotient.sound'
    refine MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨t⁻¹, ?_⟩)
    rw [e, inv_smul_smul]
  have stab : ∀ y : G ⧸ U, stabilizer T y = (stabilizer G y).comap ι := fun y => rfl
  exact gq_mass φ (fun h y => rfl) H₀ C k hk fin (fun z hz y => h0 z hz y) h1 h2
    (fun y hy => by rw [stab]; exact h3 y hy)

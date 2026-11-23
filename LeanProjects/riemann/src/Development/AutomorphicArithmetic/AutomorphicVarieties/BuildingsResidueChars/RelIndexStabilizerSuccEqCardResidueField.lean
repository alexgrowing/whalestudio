import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

namespace UpperTheory.HilbertUnitGroup

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {τ : K}

private theorem mem_ord {y w : Etau K τ} :
    w ∈ Ord O y ↔ ∃ a b : O, w = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y := by
  change w ∈ Submodule.span O {1, y} ↔ _
  rw [Submodule.mem_span_pair]
  simp only [Algebra.smul_def, mul_one, eq_comm]

private theorem ord_mul {y v w : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c)
    (hv : v ∈ Ord O y) (hw : w ∈ Ord O y) : v * w ∈ Ord O y := by
  obtain ⟨a, b, rfl⟩ := mem_ord.1 hv
  obtain ⟨a', b', rfl⟩ := mem_ord.1 hw
  refine mem_ord.2 ⟨a * a' + b * b' * c, a * b' + a' * b, ?_⟩
  simp only [map_add, map_mul]
  linear_combination (algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) b') * hy

private theorem mem_Hu {y : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c) {u : (Etau K τ)ˣ} :
    u ∈ Hu O y ↔ (u : Etau K τ) ∈ Ord O y ∧ ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y := by
  have one : (1 : Etau K τ) ∈ Ord O y := mem_ord.2 ⟨1, 0, by simp⟩
  have key : ∀ v : (Etau K τ)ˣ, v ∈ Hu O y → ((v⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y := fun v hv => by
    have h1 : (1 : Etau K τ) ∈ PS.ml v (Ord O y) := by
      rw [show PS.ml v (Ord O y) = Ord O y from hv]; exact one
    simpa using PS.mem_ml.1 h1
  refine ⟨fun h => ⟨by simpa using key _ (inv_mem h), key _ h⟩, fun ⟨h1, h2⟩ => ?_⟩
  change PS.ml u (Ord O y) = Ord O y
  ext w
  rw [PS.mem_ml]
  refine ⟨fun hw => ?_, fun hw => ord_mul hy h2 hw⟩
  simpa using ord_mul hy h1 hw

private theorem uniq (hinj : Function.Injective (algebraMap O K)) {y : Etau K τ} (h0 : y.im ≠ 0) {a b a' b' : O}
    (h : algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y =
      algebraMap O (Etau K τ) a' + algebraMap O (Etau K τ) b' * y) : a = a' ∧ b = b' := by
  rw [algebraMap_etau a, algebraMap_etau b, algebraMap_etau a', algebraMap_etau b'] at h
  have im_algebraMap_add_mul : ∀ p q : K, (algebraMap K (Etau K τ) p + algebraMap K (Etau K τ) q * y).im = q * y.im := by
    intro p q; simp
  have kre : ∀ p q : K, (algebraMap K (Etau K τ) p + algebraMap K (Etau K τ) q * y).re = p + q * y.re := by
    intro p q; simp
  have him := congrArg QuadraticAlgebra.im h
  have hre := congrArg QuadraticAlgebra.re h
  rw [im_algebraMap_add_mul, im_algebraMap_add_mul] at him
  rw [kre, kre] at hre
  have hb := mul_right_cancel₀ h0 him
  rw [hb] at hre
  exact ⟨hinj (add_right_cancel hre), hinj hb⟩

private theorem isUnit_fst (hinj : Function.Injective (algebraMap O K)) {y : Etau K τ} (h0 : y.im ≠ 0) {c : O}
    (hy : y * y = algebraMap O (Etau K τ) c) (hc : ¬ IsUnit c) {u : (Etau K τ)ˣ} (hu : u ∈ Hu O y) {a b : O}
    (e : (u : Etau K τ) = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y) : IsUnit a := by
  obtain ⟨a', b', e'⟩ := mem_ord.1 ((mem_Hu hy).1 hu).2
  have h1 : algebraMap O (Etau K τ) (a * a' + b * b' * c) + algebraMap O (Etau K τ) (a * b' + a' * b) * y =
      algebraMap O (Etau K τ) 1 + algebraMap O (Etau K τ) 0 * y := by
    have := u.mul_inv
    rw [e, e'] at this
    simp only [map_add, map_mul, map_one, map_zero]
    linear_combination this - (algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) b') * hy
  have h2 := (uniq hinj h0 h1).1
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h2 with h3 | h3
  · exact isUnit_of_mul_isUnit_left h3
  · exact absurd (isUnit_of_mul_isUnit_right h3) hc

private theorem step (hinj : Function.Injective (algebraMap O K)) {y : Etau K τ} (h0 : y.im ≠ 0) {c π : O}
    (hπ : Irreducible π) (hy : y * y = algebraMap O (Etau K τ) c) (hc : π ∣ c) :
    (Hu O (algebraMap O (Etau K τ) π * y)).relIndex (Hu O y) = Nat.card (IsLocalRing.ResidueField O) := by
  classical
  have hcu : ¬ IsUnit c := fun h => hπ.not_isUnit (isUnit_of_dvd_unit hc h)
  have hy' : (algebraMap O (Etau K τ) π * y) * (algebraMap O (Etau K τ) π * y) =
      algebraMap O (Etau K τ) (π * π * c) := by
    simp only [map_mul]; linear_combination (algebraMap O (Etau K τ) π * algebraMap O (Etau K τ) π) * hy
  have hπ0 : IsLocalRing.residue O π = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]; exact hπ.not_isUnit
  have hc0 : IsLocalRing.residue O c = 0 := by
    obtain ⟨d, rfl⟩ := hc; rw [map_mul, hπ0, zero_mul]
  have ex : ∀ u : Hu O y, ∃ p : O × O, ((u : (Etau K τ)ˣ) : Etau K τ) =
      algebraMap O (Etau K τ) p.1 + algebraMap O (Etau K τ) p.2 * y := fun u => by
    obtain ⟨a, b, e⟩ := mem_ord.1 ((mem_Hu hy).1 u.2).1
    exact ⟨(a, b), e⟩
  choose P hP using ex
  let g : Hu O y → IsLocalRing.ResidueField O := fun u =>
    IsLocalRing.residue O (P u).2 / IsLocalRing.residue O (P u).1
  have gval : ∀ (u : Hu O y) (a b : O), ((u : (Etau K τ)ˣ) : Etau K τ) =
      algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y →
      g u = IsLocalRing.residue O b / IsLocalRing.residue O a := fun u a b e => by
    obtain ⟨h1, h2⟩ := uniq hinj h0 ((hP u).symm.trans e)
    simp only [g, h1, h2]
  have resne : ∀ (u : Hu O y) (a b : O), ((u : (Etau K τ)ˣ) : Etau K τ) =
      algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y → IsLocalRing.residue O a ≠ 0 := fun u a b e =>
    ((isUnit_fst hinj h0 hy hcu u.2 e).map (IsLocalRing.residue O)).ne_zero
  have gmul : ∀ u v : Hu O y, g (u * v) = g u + g v := fun u v => by
    have eu := hP u
    have ev := hP v
    have e : (((u * v : Hu O y) : (Etau K τ)ˣ) : Etau K τ) =
        algebraMap O (Etau K τ) ((P u).1 * (P v).1 + (P u).2 * (P v).2 * c) +
          algebraMap O (Etau K τ) ((P u).1 * (P v).2 + (P v).1 * (P u).2) * y := by
      rw [Subgroup.coe_mul, Units.val_mul, eu, ev]
      simp only [map_add, map_mul]
      linear_combination (algebraMap O (Etau K τ) (P u).2 * algebraMap O (Etau K τ) (P v).2) * hy
    have n1 := resne u _ _ eu
    have n2 := resne v _ _ ev
    rw [gval _ _ _ e, gval _ _ _ eu, gval _ _ _ ev]
    simp only [map_add, map_mul, hc0, mul_zero, add_zero]
    field_simp
    ring
  let f : Hu O y →* Multiplicative (IsLocalRing.ResidueField O) :=
    MonoidHom.mk' (fun u => Multiplicative.ofAdd (g u)) (fun u v => by rw [gmul, ofAdd_add])
  have fval : ∀ u, f u = Multiplicative.ofAdd (g u) := fun _ => rfl
  have down : ∀ u : Hu O y, f u = 1 → ((u : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O (algebraMap O (Etau K τ) π * y) := fun u hu => by
    have h1 : g u = 0 := by simpa [fval] using hu
    have e := hP u
    rw [gval _ _ _ e, div_eq_zero_iff, or_iff_left (resne u _ _ e), IsLocalRing.residue_eq_zero_iff,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton] at h1
    obtain ⟨d, hd⟩ := h1
    refine mem_ord.2 ⟨(P u).1, d, ?_⟩
    rw [e, hd, map_mul]
    ring
  have hker : f.ker = (Hu O (algebraMap O (Etau K τ) π * y)).subgroupOf (Hu O y) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_Hu hy']
    refine ⟨fun hu => ⟨down u hu, ?_⟩, fun ⟨h1, _⟩ => ?_⟩
    · have := down u⁻¹ (by rw [map_inv, hu, inv_one])
      simpa using this
    · obtain ⟨a, b, e⟩ := mem_ord.1 h1
      have e' : ((u : (Etau K τ)ˣ) : Etau K τ) =
          algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) (b * π) * y := by
        rw [e, map_mul]; ring
      rw [fval, gval _ _ _ e', map_mul, hπ0, mul_zero, zero_div, ofAdd_zero]
  have hsurj : Function.Surjective f := fun r => by
    obtain ⟨s, hs⟩ := IsLocalRing.residue_surjective (Multiplicative.toAdd r)
    have hn : IsUnit (1 - s * s * c) := by
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := 1 - s * s * c) (b := s * s * c) (by ring) with h | h
      · exact h
      · exact absurd (isUnit_of_mul_isUnit_right h) hcu
    obtain ⟨ν, hν⟩ := hn
    have hν' : algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * (1 - algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) c) = 1 := by
      rw [← map_mul, ← map_mul, ← map_one (algebraMap O (Etau K τ)), ← map_sub, ← hν, ← map_mul, Units.inv_mul]
    let w : (Etau K τ)ˣ :=
      { val := algebraMap O (Etau K τ) 1 + algebraMap O (Etau K τ) s * y
        inv := algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) + algebraMap O (Etau K τ) (-(((ν⁻¹ : Oˣ) : O) * s)) * y
        val_inv := by
          simp only [map_neg, map_mul, map_one]
          linear_combination hν' - (algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s) * hy
        inv_val := by
          simp only [map_neg, map_mul, map_one]
          linear_combination hν' - (algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s) * hy }
    have hw : w ∈ Hu O y := (mem_Hu hy).2 ⟨mem_ord.2 ⟨1, s, rfl⟩, mem_ord.2 ⟨_, _, rfl⟩⟩
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [fval, gval ⟨w, hw⟩ 1 s rfl, map_one, div_one, hs, ofAdd_toAdd]
  have hr : f.range = ⊤ := MonoidHom.range_eq_top.2 hsurj
  change ((Hu O (algebraMap O (Etau K τ) π * y)).subgroupOf (Hu O y)).index = _
  rw [← hker, Subgroup.index_ker, hr, Subgroup.card_top]
  exact Nat.card_congr Multiplicative.toAdd

end UpperTheory.HilbertUnitGroup

theorem UpperTheory.relIndex_stabilizer_succ_eq_card_residueField :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → ∀ m : ℕ, 1 ≤ m → (Hu O (yy π (m + 1) x)).relIndex (Hu O (yy π m x)) = Nat.card (IsLocalRing.ResidueField O) := by
  intro O K _ _ _ _ _ Δ τ L _ π n e h x hC m hm
  haveI := L.frac
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hπ := hC.irr
  have hp : algebraMap O K (π ^ m) ≠ 0 := fun h0 =>
    pow_ne_zero m hπ.ne_zero (hinj (by rw [h0, map_zero]))
  have h0 : (yy π m x).im ≠ 0 := by
    rw [yy, im_smul, smul_eq_mul]
    exact mul_ne_zero hp hC.gen.im_ne
  have hsm : ∀ k : ℕ, yy π k x = algebraMap O (Etau K τ) (π ^ k) * x := fun k => by
    rw [yy, Algebra.smul_def, ← algebraMap_etau]
  have hy : yy π m x * yy π m x = algebraMap O (Etau K τ) (π ^ m * π ^ m * (e : O)) := by
    rw [hsm, map_mul, map_mul, ← hC.sq]; ring
  have hc : π ∣ π ^ m * π ^ m * (e : O) :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self π (by omega)) _) _
  have e1 : yy π (m + 1) x = algebraMap O (Etau K τ) π * yy π m x := by
    rw [hsm, hsm, pow_succ, map_mul]; ring
  rw [e1]
  exact UpperTheory.HilbertUnitGroup.step hinj h0 hπ hy hc

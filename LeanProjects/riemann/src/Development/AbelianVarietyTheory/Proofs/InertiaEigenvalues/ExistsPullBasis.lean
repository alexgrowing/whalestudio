import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfAssembleMem

noncomputable section
namespace GlobalTheory.PsiShiftProof
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.PhiGam.Inh GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters GlobalTheory.PsiLemmaCompare

section Ring
variable {k : Type} [Field k] {l : ℕ} [hl : Fact l.Prime] [CharP k l]
  {R : RingPG k l} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} (hι : IsCyclotomic R ι)
include hι

theorem range_iff (y : k⸨X⸩) : (∃ x, ι x = y) ↔ ∀ t : ℤ_[l]ˣ, t ^ (l - 1) = 1 → delPi k t y = y := by
  have h := ((isCyclotomic_iff R ι).1 hι).1
  have : y ∈ Set.range ι ↔ FrobeniusBinomialReduction.DeltaInv k l y := by rw [h]; rfl
  simpa only [FrobeniusBinomialReduction.DeltaInv, delPi_eq, Set.mem_range] using this

theorem iota_gam (x : k⸨X⸩) : ι (R.γ x) = gamPi k l (ι x) := by
  rw [← gamPi_eq']; exact ((isCyclotomic_iff R ι).1 hι).2.2.2.2 x

theorem iota_mem {a : ℤ} {x : k⸨X⸩} (hx : x ∈ Dp k a) : ι x ∈ Dp k ((l - 1) * a) := by
  have := map_mem (σ := (ι : k⸨X⸩ →+* k⸨X⸩)) hι.2.1 hι.1 hx
  rwa [Nat.cast_sub hl.out.one_le, Nat.cast_one] at this

theorem mem_of_iota_mem {a s : ℤ} (hs : (l - 1) * (a - 1) < s) {x : k⸨X⸩} (hx : ι x ∈ Dp k s) : x ∈ Dp k a :=
  mem_of_map_mem (σ := (ι : k⸨X⸩ →+* k⸨X⸩)) hι.2.1 hι.1
    (by rwa [Nat.cast_sub hl.out.one_le, Nat.cast_one]) hx

theorem exists_psi : ∃ ψ : k⸨X⸩ →ₗ[k] k⸨X⸩, ∀ x, ι (ψ x) = psiPi k l (ι x) := by
  have : ∀ x, ∃ y, ι y = psiPi k l (ι x) := fun x => (range_iff hι _).2 fun t ht => by
    rw [← psi_del, (range_iff hι _).1 ⟨x, rfl⟩ t ht]
  choose ψ hψ using this
  refine ⟨⟨⟨ψ, fun x y => ι.injective ?_⟩, fun c x => ι.injective ?_⟩, hψ⟩
  · change ι _ = ι _
    simp only [map_add, hψ]
  · change lin ι (ψ (c • x)) = lin ι (c • ψ x)
    rw [map_smul, lin_apply, lin_apply, hψ, hψ, ← map_smul, ← lin_apply ι, map_smul, lin_apply]

variable {ψ : k⸨X⸩ →ₗ[k] k⸨X⸩} (hψ : ∀ x, ι (ψ x) = psiPi k l (ι x))
include hψ

theorem psiK_phi_mul (a x : k⸨X⸩) : ψ (R.φ a * x) = a * ψ x := by
  apply ι.injective
  change ι _ = ι _
  rw [hψ, map_mul ι, map_mul ι, hι.2.2.2.1, psi_phi_mul, hψ]

theorem psiK_mem {a : ℤ} (ha : 2 - (l : ℤ) ≤ a) {x : k⸨X⸩} (hx : x ∈ Dp k a) : ψ x ∈ Dp k 0 := by
  have h2 : (2 : ℤ) ≤ l := by exact_mod_cast hl.out.two_le
  refine mem_of_iota_mem hι (s := 2 - l) (by linarith) ?_
  rw [hψ]
  exact psi_mem k l (by nlinarith) (iota_mem hι hx)

theorem psiK_vv : ∃ d : k⟦X⟧, (d : k⸨X⸩) * ψ (vv k) = 1 := by
  have h2 : (2 : ℤ) ≤ l := by exact_mod_cast hl.out.two_le
  have hv : vv k ∈ Dp k 1 := by simpa using zpow_mem (k := k) 1
  obtain ⟨c, hc⟩ := mem_Dp_zero.1 (psiK_mem hι hψ (by omega) hv)
  have hu : IsUnit c := by
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    intro h0
    obtain ⟨e, he⟩ := PowerSeries.X_dvd_iff.2 h0
    have h3 : ψ (vv k) ∈ Dp k 1 := mem_Dp.2 ⟨e, by rw [hc, he, map_mul, zpow_one, vv_eq]⟩
    have h4 := mem_Dp_coeff.1 (iota_mem hι h3) 0 (by omega)
    have h5 : ι (vv k) ∈ Dp k (l - 1) := by simpa using iota_mem hι hv
    rw [hψ, psi_coeff_zero k l h5, zsmul_eq_mul, mul_eq_zero] at h4
    have h6 := h4.resolve_left (by simp)
    have h7 : ι (vv k) ∈ Dp k l := mem_Dp_coeff.2 fun m hm => by
      rcases eq_or_ne m (l - 1) with rfl | hne
      · exact h6
      · exact mem_Dp_coeff.1 h5 m (by omega)
    have h8 := Dp_mul (mem_of_iota_mem hι (a := 2) (by linarith) h7) (zpow_mem (-1)) (u := 1) (by norm_num)
    rw [zpow_neg_one, mul_inv_cancel₀ vv_ne] at h8
    exact one_not_mem h8
  obtain ⟨d, hd⟩ := hu.exists_left_inv
  exact ⟨d, by rw [hc, ← map_mul, hd, map_one]⟩

theorem psiRing : PsiRing R ψ := by
  refine ⟨psiK_phi_mul hι hψ, fun a => ι.injective ?_, fun x => ι.injective ?_, fun a h1 h2 => ?_⟩
  · change ι _ = ι _
    rw [hψ, hι.2.2.2.1]
    simpa using psi_pow_mul k l hl.out.pos (ι a)
  · change ι _ = ι _
    rw [hψ, iota_gam hι, iota_gam hι, psi_gam, hψ]
  · ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, ← mem_Dp, ← mem_Dp_zero]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact psiK_mem hι hψ h1 hx
    · intro hy
      obtain ⟨b, rfl⟩ := mem_Dp_zero.1 hy
      obtain ⟨d, hd⟩ := psiK_vv hι hψ
      obtain ⟨e, he⟩ := R.φ_int (b * d)
      refine ⟨R.φ (b * d : k⟦X⟧) * vv k, ?_, ?_⟩
      · rw [he]
        simpa using Dp_mul (coe_mem e) (zpow_mem 1) (u := a) (by omega)
      · rw [psiK_phi_mul hι hψ, map_mul, mul_assoc, hd, mul_one]

theorem ker_mem_iff {a : ℤ} (h1 : 2 - (l : ℤ) ≤ a) (h2 : a ≤ 1) {x : k⸨X⸩} (hx : ψ x = 0) :
    x ∈ Dp k a ↔ ι x ∈ Dp k (l * a) := by
  refine ⟨fun h => ?_, fun h => mem_of_iota_mem hι (by linarith) h⟩
  rcases h2.eq_or_lt with rfl | h3
  · rw [mul_one]
    exact mem_of_psi_eq_zero k l (by simpa using iota_mem hι h) (by rw [← hψ, hx, map_zero])
  · exact Dp_mono (by linarith) (iota_mem hι h)

omit hι in
theorem ker_iff {x : k⸨X⸩} : ψ x = 0 ↔ psiPi k l (ι x) = 0 := by
  rw [← hψ, map_eq_zero ι]

variable {n : ℕ} (h5 : 5 ≤ l) (G : Matrix (Fin n) (Fin n) k⸨X⸩) (hG : ∀ i m, (G - 1) i m ∈ Dp k 1)
include h5 hG

omit hψ in
theorem map_sub_one (i m : Fin n) : (G.map ι - 1) i m ∈ Dp k 2 := by
  have : (G.map ι - 1) i m = ι ((G - 1) i m) := by
    simp [Matrix.one_apply, apply_ite ι]
  rw [this]
  exact Dp_mono (by omega) (iota_mem hι (hG i m))

omit hψ h5 hG in
theorem iota_op (x : Fin n → k⸨X⸩) (i : Fin n) : ι (∑ m, R.φ (G i m) * R.γ (x m) - x i) =
    ∑ m, phiPi k l (G.map ι i m) * gamPi k l (ι (x m)) - ι (x i) := by
  simp only [map_sub, map_sum, map_mul, hι.2.2.2.1, iota_gam hι, Matrix.map_apply]

theorem coord_maps {a : ℤ} (h1 : 2 - (l : ℤ) ≤ a) (h2 : a ≤ 0) (x : Fin n → k⸨X⸩) (hx : ∀ i, ψ (x i) = 0)
    (hs : ∀ i, x i ∈ Dp k a) (i : Fin n) : ∑ m, R.φ (G i m) * R.γ (x m) - x i ∈ Dp k (a + 1) := by
  have := core_maps h5 _ (map_sub_one hι h5 G hG) (fun i => ι (x i)) (fun i => (ker_iff hψ).1 (hx i))
    (fun i => (ker_mem_iff hι hψ h1 (by omega) (hx i)).1 (hs i)) i
  rw [← iota_op hι, ← ker_iff hψ] at this
  exact (ker_mem_iff hι hψ (by omega) (by omega) this.1).2 this.2

theorem coord_surj {a : ℤ} (h1 : 2 - (l : ℤ) ≤ a) (h2 : a ≤ 0) (z : Fin n → k⸨X⸩) (hz : ∀ i, ψ (z i) = 0)
    (hs : ∀ i, z i ∈ Dp k (a + 1)) : ∃ x : Fin n → k⸨X⸩, (∀ i, ψ (x i) = 0) ∧ (∀ i, x i ∈ Dp k a) ∧
      ∀ i, ∑ m, R.φ (G i m) * R.γ (x m) - x i = z i := by
  obtain ⟨y, y1, y2, y3⟩ := core_surj h5 _ (map_sub_one hι h5 G hG) (fun i => ι (z i))
    (fun i => (ker_iff hψ).1 (hz i)) (fun i => (ker_mem_iff hι hψ (by omega) (by omega) (hz i)).1 (hs i))
  have : ∀ i, ∃ x, ι x = y i := by
    intro i
    refine (range_iff hι _).2 fun t ht => ?_
    have hd : ∀ x, delPi k t (ι x) = ι x := fun x => (range_iff hι _).1 ⟨x, rfl⟩ t ht
    have := core_inj h5 _ (map_sub_one hι h5 G hG) (fun i => delPi k t (y i) - y i)
      (fun i => by rw [map_sub, psi_del, y1, map_zero, sub_zero]) (fun i => by
        have h3 := congrArg (delPi k t) (y3 i)
        have h4 := y3 i
        simp only [map_sub, map_sum, map_mul, del_phi, del_gam, Matrix.map_apply, hd, mul_sub,
          Finset.sum_sub_distrib] at h3 h4 ⊢
        linear_combination h3 - h4)
    exact sub_eq_zero.1 (congrFun this i)
  choose x hx using this
  have hk : ∀ i, ψ (x i) = 0 := fun i => by rw [ker_iff hψ, hx, y1]
  refine ⟨x, hk, fun i => (ker_mem_iff hι hψ h1 (by omega) (hk i)).2 (hx i ▸ y2 i), fun i => ι.injective ?_⟩
  change ι _ = ι _
  rw [iota_op hι, ← y3]
  simp only [hx]

end Ring

section Mod
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V]

omit [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] in
theorem exists_pull_basis {σ : k⸨X⸩ →ₐ[k] k⸨X⸩} {f : V →ₗ[k] V} (hf : Semi σ f)
    (ht : Submodule.span k⸨X⸩ (Set.range f) = ⊤) {n : ℕ} (b : Module.Basis (Fin n) k⸨X⸩ V) :
    ∃ c : Module.Basis (Fin n) k⸨X⸩ V, ∀ i, c i = f (b i) := by
  have h : ⊤ ≤ Submodule.span k⸨X⸩ (Set.range fun j => f (b j)) := by
    rw [← ht]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hf]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank h
    (Module.finrank_eq_card_basis b).symm) h, fun i => Module.Basis.mk_apply _ _ i⟩

omit [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] in
theorem exists_Psi [FiniteDimensional k⸨X⸩ V] {σ : k⸨X⸩ →ₐ[k] k⸨X⸩} {f : V →ₗ[k] V} (hf : Semi σ f)
    (ht : Submodule.span k⸨X⸩ (Set.range f) = ⊤) (ψ : k⸨X⸩ →ₗ[k] k⸨X⸩) (hψ : ∀ a x, ψ (σ a * x) = a * ψ x) :
    ∃ Ψ : V →ₗ[k] V, ∀ (a : k⸨X⸩) (x : V), Ψ (a • f x) = ψ a • x := by
  let b := Module.finBasis k⸨X⸩ V
  obtain ⟨c, hc⟩ := exists_pull_basis hf ht b
  refine ⟨⟨⟨fun x => ∑ i, ψ (c.repr x i) • b i, fun x y => ?_⟩, fun r x => ?_⟩, fun a x => ?_⟩
  · simp only [map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
  · simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_one_smul k⸨X⸩ r x, map_smul, Finsupp.smul_apply, smul_assoc, one_smul, map_smul, smul_assoc]
  · change ∑ i, ψ (c.repr (a • f x) i) • b i = _
    have h1 : a • f x = ∑ i, (σ (b.repr x i) * a) • c i := by
      conv_lhs => rw [← b.sum_repr x, map_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hf, hc, smul_smul, mul_comm]
    conv_rhs => rw [← b.sum_repr x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1, c.repr_sum_self, hψ, smul_smul, mul_comm]

omit [Module k V] [IsScalarTower k k⸨X⸩ V] in
theorem mem_sh_span {n : ℕ} (b : Module.Basis (Fin n) k⸨X⸩ V) (s : ℤ) (x : V) :
    x ∈ sh s (Submodule.span k⟦X⟧ (Set.range b)) ↔ ∀ i, b.repr x i ∈ Dp k s := by
  rw [mem_sh_iff_smul_mem, b.mem_span_iff_repr_mem k⟦X⟧]
  refine forall_congr' fun i => ?_
  rw [Dp, mem_sh_iff_smul_mem, mem_stdLat, map_smul, Finsupp.smul_apply]
  rfl

omit [Module k V] [IsScalarTower k k⸨X⸩ V] in
theorem exists_lat_basis {M : Submodule k⟦X⟧ V} (hM : IsLat M) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k⸨X⸩ V), M = Submodule.span k⟦X⟧ (Set.range b) := by
  have : Submodule.IsLattice k⸨X⸩ M := ⟨hM.1, hM.2⟩
  let e := Module.finBasis k⟦X⟧ M
  refine ⟨_, e.extendOfIsLattice k⸨X⸩, ?_⟩
  have h := congrArg (Submodule.map M.subtype) e.span_eq
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h
  refine h.symm.trans ?_
  congr 2
  funext i
  simp

omit [IsScalarTower k k⸨X⸩ V] in
theorem pull_span {σ : k⸨X⸩ →ₐ[k] k⸨X⸩} (hσ : ∀ a : k⟦X⟧, ∃ b : k⟦X⟧, σ (a : k⸨X⸩) = (b : k⸨X⸩))
    {f : V →ₗ[k] V} (hf : Semi σ f) {n : ℕ} (b c : Fin n → V) (hc : ∀ i, c i = f (b i)) :
    pull f (Submodule.span k⟦X⟧ (Set.range b)) = Submodule.span k⟦X⟧ (Set.range c) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨j, rfl⟩ := hy; exact Submodule.subset_span ⟨j, hc j⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      obtain ⟨e, he⟩ := hσ a
      rw [← algebraMap_smul k⸨X⸩ a y, hf]
      exact (he ▸ TwistShift.coe_smul_mem e hy :)
  · refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨b j, Submodule.subset_span ⟨j, rfl⟩, (hc j).symm⟩

end Mod

theorem lemmaPsi : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi := by
  intro l hl k _ _ h5 R ι hι
  obtain ⟨ψ, hψ⟩ := exists_psi hι
  have hR := psiRing hι hψ
  refine ⟨assemble_bijective k l, ψ, fun x y h => by rw [hψ, h, psi_assemble], hR, ?_⟩
  intro V _ _ _ _ _ _ _ _ f g₀ g hf ht hg₀ hg hc
  obtain ⟨Ψ, hΨ⟩ := exists_Psi hf ht ψ hR.1
  have hcomm : ∀ x, Ψ (g x) = g₀ (Ψ x) := by
    intro x
    obtain ⟨c, hc'⟩ := exists_pull_basis hf ht (Module.finBasis k⸨X⸩ V)
    rw [← c.sum_repr x]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc', hg, ← hc, hΨ, hΨ, hg₀, hR.2.2.1]
  refine ⟨Ψ, (psiMod_iff R ψ ((psiRing_iff R ψ).1 hR) f g₀ g Ψ).2 ⟨hΨ, hcomm, ?_⟩⟩
  intro M hM hC a h1 h2
  obtain ⟨n, b, rfl⟩ := exists_lat_basis hM
  obtain ⟨c, hcb⟩ := exists_pull_basis hf ht b
  rw [pull_span R.φ_int hf b c hcb]
  let G : Matrix (Fin n) (Fin n) k⸨X⸩ := Matrix.of fun i m => b.repr (g₀ (b m)) i
  have hG : ∀ i m, (G - 1) i m ∈ Dp k 1 := by
    intro i m
    have := (mem_sh_span b 1 _).1 (hC (b m) (Submodule.subset_span ⟨m, rfl⟩)) i
    simpa [G, Matrix.one_apply, Finsupp.single_apply, eq_comm] using this
  have hker : ∀ x, Ψ x = 0 ↔ ∀ i, ψ (c.repr x i) = 0 := by
    intro x
    have : Ψ x = ∑ i, ψ (c.repr x i) • b i := by
      conv_lhs => rw [← c.sum_repr x, map_sum]
      simp only [hcb, hΨ]
    rw [this]
    exact ⟨Fintype.linearIndependent_iff.1 b.linearIndependent _, fun h => by simp [h]⟩
  have hop : ∀ x i, c.repr (g x - x) i = ∑ m, R.φ (G i m) * R.γ (c.repr x m) - c.repr x i := by
    intro x i
    have h3 : ∀ m, c.repr (g (c m)) i = R.φ (G i m) := by
      intro m
      rw [hcb, ← hc, ← b.sum_repr (g₀ (b m)), map_sum]
      simp only [hf _, ← hcb]
      rw [c.repr_sum_self]
      rfl
    rw [map_sub, Finsupp.sub_apply]
    congr 1
    conv_lhs => rw [← c.sum_repr x, map_sum, map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hg, map_smul, Finsupp.smul_apply, h3, smul_eq_mul, mul_comm]
  ext z
  simp only [FrobeniusBinomialReduction.kerPsi, Set.mem_image, Set.mem_setOf_eq, mem_sh_span]
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    refine ⟨fun i => ?_, by rw [map_sub, hcomm, hx2, map_zero, sub_zero]⟩
    rw [hop]
    exact coord_maps hι hψ h5 G hG h1 h2 _ ((hker x).1 hx2) hx1 i
  · rintro ⟨hz1, hz2⟩
    obtain ⟨x, x1, x2, x3⟩ := coord_surj hι hψ h5 G hG h1 h2 _ ((hker z).1 hz2) hz1
    refine ⟨∑ i, x i • c i, ⟨by simpa only [c.repr_sum_self] using x2,
      (hker _).2 (by simpa only [c.repr_sum_self] using x1)⟩, c.ext_elem fun i => ?_⟩
    rw [hop, c.repr_sum_self, x3]

end GlobalTheory.PsiShiftProof

import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.Bridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RqFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SChain

open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up

private theorem bock_abs {C2 C1 C0 D2 D1 H : Type} [AddCommGroup C2] [AddCommGroup C1] [AddCommGroup C0]
    [AddCommGroup D2] [AddCommGroup D1] [AddCommGroup H] {A : Type} [CommRing A] [Module A D2] [Module A D1]
    (q : ℕ) (hq : 0 < q) (d1 : C2 →ₗ[ℤ] C1) (d0 : C1 →ₗ[ℤ] C0) (e : D2 →ₗ[A] D1) (r2 : C2 →+ D2) (r1 : C1 →+ D1)
    (hdd : ∀ z, d0 (d1 z) = 0) (hc : ∀ z, e (r2 z) = r1 (d1 z)) (hs : Function.Surjective r2)
    (h2 : ∀ z, r2 z = 0 ↔ ∃ w, z = q • w) (h1 : ∀ z, r1 z = 0 ↔ ∃ w, z = q • w)
    (t1 : ∀ w : C1, q • w = 0 → w = 0) (t0 : ∀ w : C0, q • w = 0 → w = 0)
    (cls : LinearMap.ker d0 →+ H) (hz : ∀ z, cls z = 0 ↔ z.1 ∈ LinearMap.range d1) :
    ∃ β : LinearMap.ker e →+ AddCommGroup.torsion H, ∀ y, β y = 0 → ∃ z : C2, d1 z = 0 ∧ r2 z = y.1 := by
  classical
  have hlift : ∀ y : LinearMap.ker e, ∃ x : C2, ∃ w : C1, r2 x = y.1 ∧ d1 x = q • w := by
    intro y
    obtain ⟨x, hx⟩ := hs y.1
    have h0 : r1 (d1 x) = 0 := by
      rw [← hc, hx]
      exact y.2
    obtain ⟨w, hw⟩ := (h1 _).1 h0
    exact ⟨x, w, hx, hw⟩
  have hker : ∀ (x : C2) (w : C1), d1 x = q • w → d0 w = 0 := by
    intro x w h
    apply t0
    rw [← map_nsmul, ← h, hdd]
  have hwd : ∀ (x x' : C2) (w w' : C1) (hw0 : d0 w = 0) (hw0' : d0 w' = 0), r2 x = r2 x' →
      d1 x = q • w → d1 x' = q • w' →
      cls ⟨w, LinearMap.mem_ker.2 hw0⟩ = cls ⟨w', LinearMap.mem_ker.2 hw0'⟩ := by
    intro x x' w w' hw0 hw0' hr h h'
    obtain ⟨u, hu⟩ := (h2 (x' - x)).1 (by rw [map_sub, hr, sub_self])
    have hd : d1 u ∈ LinearMap.ker d0 := LinearMap.mem_ker.2 (hdd u)
    have heq : w' = w + d1 u := by
      apply sub_eq_zero.1
      apply t1
      rw [smul_sub, smul_add, ← h, ← h', ← map_nsmul, ← hu, map_sub]
      abel
    have hsum : (⟨w', LinearMap.mem_ker.2 hw0'⟩ : LinearMap.ker d0) = ⟨w, LinearMap.mem_ker.2 hw0⟩ + ⟨d1 u, hd⟩ :=
      Subtype.ext heq
    rw [hsum, map_add, (hz ⟨d1 u, hd⟩).2 ⟨u, rfl⟩, add_zero]
  choose X W hXr hXd using hlift
  have hW0 : ∀ y, d0 (W y) = 0 := fun y => hker _ _ (hXd y)
  let f : LinearMap.ker e → H := fun y => cls ⟨W y, LinearMap.mem_ker.2 (hW0 y)⟩
  have htor : ∀ y, f y ∈ AddCommGroup.torsion H := by
    intro y
    refine (AddCommGroup.mem_torsion _).2 (isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨q, hq, ?_⟩)
    have hm : q • (⟨W y, LinearMap.mem_ker.2 (hW0 y)⟩ : LinearMap.ker d0) = ⟨d1 (X y), by
        rw [LinearMap.mem_ker, hdd]⟩ := Subtype.ext (hXd y).symm
    show q • cls _ = 0
    rw [← map_nsmul, hm, (hz _).2 ⟨X y, rfl⟩]
  refine ⟨{ toFun := fun y => ⟨f y, htor y⟩, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · apply Subtype.ext
    show f 0 = 0
    have h00 := hwd (X 0) 0 (W 0) 0 (hW0 0) (map_zero _) (by simp [hXr]) (hXd 0) (by simp)
    exact h00.trans (map_zero cls)
  · intro a b
    apply Subtype.ext
    show f (a + b) = f a + f b
    have hab := hwd (X (a + b)) (X a + X b) (W (a + b)) (W a + W b) (hW0 _)
      (by rw [map_add, hW0, hW0, add_zero]) (by rw [map_add, hXr, hXr, hXr]; rfl)
      (hXd _) (by rw [map_add, hXd, hXd, smul_add])
    exact hab.trans (map_add cls ⟨W a, LinearMap.mem_ker.2 (hW0 a)⟩ ⟨W b, LinearMap.mem_ker.2 (hW0 b)⟩)
  · intro y hy
    have hy' : f y = 0 := congrArg Subtype.val hy
    obtain ⟨v, hv⟩ := (hz _).1 hy'
    refine ⟨X y - q • v, ?_, ?_⟩
    · rw [map_sub, map_nsmul, hv, hXd, sub_self]
    · rw [map_sub, hXr, (h2 _).2 ⟨v, rfl⟩, sub_zero]

private theorem ch_tf (q : ℕ) (hq : 0 < q) (G : Type) (m : ℕ) (w : Ch ℤ G m) (h : q • w = 0) : w = 0 := by
  refine Finsupp.ext fun a => ?_
  have h' := congrArg (fun v => v a) h
  simp only [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, nsmul_eq_mul] at h'
  rcases mul_eq_zero.1 h' with h0 | h0
  · have : q = 0 := by exact_mod_cast h0
    omega
  · rw [h0]
    rfl

private theorem bd_zero (G : Type) [Group G] (z : Ch ℤ G 1) : bd ℤ G 0 z = 0 := by
  have hv : (fun g : Fin (0 + 1) → G => (fun₀ | (fun i : Fin 0 => g i.succ) => (1 : ℤ)) +
      ∑ j : Fin (0 + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) •
        (fun₀ | j.contractNth (fun x1 x2 : G => x1 * x2) g => (1 : ℤ))) = 0 := by
    funext g
    rw [Fin.sum_univ_one, Subsingleton.elim (Fin.contractNth (0 : Fin (0 + 1)) (fun x1 x2 : G => x1 * x2) g)
      (fun i : Fin 0 => g i.succ)]
    simp
  simp only [bd, hv, Finsupp.linearCombination_zero, LinearMap.zero_apply]

theorem UpperTheory.V.ZK.Up.bock :
    UpperTheory.V.ZK.Up.Bock := by
  intro q hq G _ k
  obtain ⟨f1, -, f3, f4⟩ := rqFacts q
  cases k with
  | zero =>
    refine ⟨0, fun y _ => ?_⟩
    obtain ⟨z, hz⟩ := f3 G 1 y.1
    exact ⟨z, bd_zero G z, hz⟩
  | succ k =>
    obtain ⟨cls, hcls⟩ := bridge k
    exact bock_abs q hq (bd ℤ G (k + 1)) (bd ℤ G k) (bd (ZMod q) G (k + 1)) (rq q G (k + 2)) (rq q G (k + 1))
      ((sChain ℤ).1 G k) (f1 G (k + 1)) (f3 G _) (f4 G _) (f4 G _) (ch_tf q hq G _) (ch_tf q hq G _) (cls G)
      (hcls.zero G)

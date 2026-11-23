import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrAdd

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem dd_fin (X : Type) [CommRing X] (g : ℕ) : Module.Finite X (DD X g) := by
  let f : (X × (Fin g → X) × (Fin g → X) × X) →ₗ[X] DD X g :=
    { toFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
      map_add' := fun p q => DD.ext (by simp) (by ext j; simp) (by ext j; simp) (by simp)
      map_smul' := fun c p => by
        have hC : (DD.C c : DD X g) = ⟨c, 0, 0, 0⟩ := rfl
        simp only [RingHom.id_apply]
        change _ = DD.C c * _
        rw [hC]
        apply DD.ext <;> (try funext j) <;> simp }
  refine Module.Finite.of_surjective f ?_
  intro y
  exact ⟨(y.a, y.ep, y.ep', y.eta), rfl⟩

private theorem dd_nil (X : Type) [CommRing X] (g : ℕ) : RingHom.ker (DD.aug X g) ^ 3 = ⊥ := by
  set I := RingHom.ker (DD.aug X g) with hIdef
  have hI : ∀ y ∈ I, y.a = 0 := fun y hy => RingHom.mem_ker.mp hy
  have h2 : ∀ w ∈ I ^ 2, w.a = 0 ∧ w.ep = 0 ∧ w.ep' = 0 := by
    intro w hw
    rw [sq] at hw
    refine Submodule.mul_induction_on hw ?_ ?_
    · intro m hm n hn
      have e1 := hI m hm
      have e2 := hI n hn
      refine ⟨by simp [e1, e2], by ext j; simp [e1, e2], by ext j; simp [e1, e2]⟩
    · rintro x y ⟨h1, h2, h3⟩ ⟨h4, h5, h6⟩
      refine ⟨by simp [h1, h4], by ext j; simp [h2, h5], by ext j; simp [h3, h6]⟩
  rw [eq_bot_iff, pow_succ, Ideal.mul_le]
  intro r hr s hs
  obtain ⟨a1, a2, a3⟩ := h2 r hr
  have e := hI s hs
  rw [Ideal.mem_bot]
  apply DD.ext
  · simp [a1]
  · ext j
    simp [a1, a2, e]
  · ext j
    simp [a1, a3, e]
  · simp [a1, a2, a3, e]

theorem UpperTheory.V.Pa.testEx :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ (e : ℕ) (α : Fin e → S.Bh →+ S.F) (μ : Fin e → S.U.N →+ S.F) (Φ : S.U.N →+ S.F), (∀ k, α k ∈ S.Tp) → (∀ k, μ k ∈ S.La) → (∀ (b : S.Bh) y, Φ (b • y) = S.rF b * Φ y + ∑ k, α k b * μ k y) → ∃ θ : S.U.AA →+* DD S.F e, S.Test (DD S.F e) (DD.aug S.F e) θ ∧ ∀ a, θ a = ⟨S.rF (S.pr0 a), fun k => μ k (S.pr1 a), fun k => α k (S.pr0 a), Φ (S.pr1 a)⟩ := by
  intro l _ S e α μ Φ hα hμ hΦ
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := prAdd l S
  have hα' : ∀ k, (∀ b b', α k (b * b') = S.rF b * α k b' + S.rF b' * α k b) ∧
      (∀ o, α k (algebraMap S.OO S.Bh o) = 0) ∧ ∀ b ∈ ired S.U.N, α k b = 0 := fun k => hα k
  have hμ' : ∀ k (b : S.Bh) y, μ k (b • y) = S.rF b * μ k y := fun k => hμ k
  have q0 : ∀ b : S.Bh, S.pr0 (algebraMap S.Bh S.U.AA b) = b := fun b => by simpa using (p2 b 0).1
  have q1 : ∀ b : S.Bh, S.pr1 (algebraMap S.Bh S.U.AA b) = 0 := fun b => by simpa using (p2 b 0).2
  have o0 : S.pr0 1 = 1 := by simpa using q0 1
  have o1 : S.pr1 1 = 0 := by simpa using q1 1
  have z0 : S.pr0 0 = 0 := by simpa using q0 0
  have z1 : S.pr1 0 = 0 := by simpa using q1 0
  have hα1 : ∀ k, α k 1 = 0 := fun k => by simpa using (hα' k).2.1 1
  let T : S.U.AA → DD S.F e := fun a =>
    ⟨S.rF (S.pr0 a), fun k => μ k (S.pr1 a), fun k => α k (S.pr0 a), Φ (S.pr1 a)⟩
  have hmul : ∀ a a', T (a * a') = T a * T a' := by
    intro a a'
    have hd : S.rF (S.pr0 (a * a')) = S.rF (S.pr0 a) * S.rF (S.pr0 a') := by
      have h0 : S.pr0 (a * a') - S.pr0 a * S.pr0 a' ∈ RingHom.ker S.rF := by
        rw [S.rF_ker]
        exact p6 (p5 a a').1
      rw [RingHom.mem_ker, map_sub, map_mul, sub_eq_zero] at h0
      exact h0
    have hda : ∀ k, α k (S.pr0 (a * a')) =
        S.rF (S.pr0 a) * α k (S.pr0 a') + S.rF (S.pr0 a') * α k (S.pr0 a) := by
      intro k
      have h0 := (hα' k).2.2 _ (p5 a a').1
      rw [map_sub, sub_eq_zero] at h0
      rw [h0, (hα' k).1]
    have hp1 := (p5 a a').2
    apply DD.ext
    · simp only [T, DD.mul_a]
      exact hd
    · funext k
      simp only [T, DD.mul_ep]
      rw [hp1, map_add, hμ', hμ']
      ring
    · funext k
      simp only [T, DD.mul_ep']
      rw [hda k]
      ring
    · simp only [T, DD.mul_eta]
      rw [hp1, map_add, hΦ, hΦ, Finset.sum_add_distrib]
      have s1 : ∑ j, μ j (S.pr1 a) * α j (S.pr0 a') = ∑ j, α j (S.pr0 a') * μ j (S.pr1 a) :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      rw [s1]
      ring
  let θ : S.U.AA →+* DD S.F e :=
    { toFun := T
      map_one' := DD.ext (by simp [T, o0]) (by funext k; simp [T, o1]) (by funext k; simp [T, o0, hα1])
        (by simp [T, o1])
      map_mul' := hmul
      map_zero' := DD.ext (by simp [T, z0]) (by funext k; simp [T, z1]) (by funext k; simp [T, z0])
        (by simp [T, z1])
      map_add' := fun a a' => DD.ext (by simp [T, (p3 a a').1]) (by funext k; simp [T, (p3 a a').2])
        (by funext k; simp [T, (p3 a a').1]) (by simp [T, (p3 a a').2]) }
  have hAlg : ∀ c : S.F, algebraMap S.F (DD S.F e) c = ⟨c, 0, 0, 0⟩ := fun c => rfl
  refine ⟨θ, ⟨dd_fin _ _, ⟨3, dd_nil _ _⟩, fun a => rfl, fun o => ?_⟩, fun a => rfl⟩
  rw [hAlg]
  apply DD.ext
  · simp [θ, T, q0]
  · funext k
    simp [θ, T, q1]
  · funext k
    simp [θ, T, q0, (hα' k).2.1]
  · simp [θ, T, q1]

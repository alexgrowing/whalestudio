import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.LUnH
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.ProdEqNorm
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.EvalSmulCong
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.CauchyFar
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

private theorem exTr (H G : Subgroup SL(2, ℤ)) [G.FiniteIndex] :
    ∃ (κ : Type) (_ : Fintype κ) (δ : κ → SL(2, ℤ)), IsTr (H ⊓ G) H δ := by
  classical
  refine ⟨H ⧸ G.subgroupOf H, Fintype.ofFinite _, fun q => ((q.out⁻¹ : H) : SL(2, ℤ)), fun q => (q.out⁻¹).2, fun d hd => ?_⟩
  have key : ∀ q : H ⧸ G.subgroupOf H, d * (((q.out⁻¹ : H) : SL(2, ℤ)))⁻¹ ∈ H ⊓ G ↔
      (QuotientGroup.mk (⟨d, hd⟩⁻¹ : H) : H ⧸ G.subgroupOf H) = q := by
    intro q
    conv_rhs => rw [← QuotientGroup.out_eq' q, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.mem_inf, Subgroup.coe_inv, inv_inv, Subgroup.coe_mul]
    exact ⟨fun h => h.2, fun h => ⟨H.mul_mem hd q.out.2, h⟩⟩
  exact ⟨_, (key _).2 rfl, fun q hq => ((key q).1 hq).symm⟩

private theorem gamma_le {M M' : ℕ} (h : M ∣ M') : CongruenceSubgroup.Gamma M' ≤ CongruenceSubgroup.Gamma M := by
  intro g hg
  rw [CongruenceSubgroup.Gamma_mem] at hg ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hg
  have e : ∀ z : ℤ, ((z : ℤ) : ZMod M) = ZMod.castHom h (ZMod M) (z : ZMod M') := fun z => (map_intCast _ z).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e, h1, map_one]
  · rw [e, h2, map_zero]
  · rw [e, h3, map_zero]
  · rw [e, h4, map_one]

private theorem neg_one_not (l n : ℕ) [hl : Fact l.Prime] (h2 : l ≠ 2) (hn : 1 ≤ n) :
    (-1 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma (l ^ n) := by
  intro h
  have h' := gamma_le (dvd_pow_self l (by omega : n ≠ 0)) h
  rw [CongruenceSubgroup.Gamma_mem] at h'
  have h1 := h'.1
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply, Matrix.one_apply_eq,
    Int.cast_neg, Int.cast_one] at h1
  have h3 : ((2 : ℕ) : ZMod l) = 0 := by
    push_cast
    linear_combination -h1
  rw [ZMod.natCast_eq_zero_iff] at h3
  exact h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h3)

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem un_of (X : Tower Ω ε) {H : Subgroup SL(2, ℤ)} {m : ℕ} {a : X.Kˣ} (h : LUnH X H m (a : X.K)) : a ∈ X.Un m := by
  intro W hW
  obtain ⟨c, -, hc, hv⟩ := h.2.2 W hW
  exact ⟨Units.mk0 c hc, hv⟩

private theorem inv_of (X : Tower Ω ε) {H : Subgroup SL(2, ℤ)} {m : ℕ} {a : X.Kˣ} (h : LUnH X H m (a : X.K)) : InvH X H m a := by
  intro g hg
  exact ⟨1, by simpa using (mem_lev_iff X H _).1 h.2.1 g hg⟩

private def St (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ) (lam : Fin 2 → ℤ) (n : ℕ) (t : X.Fn l) : Prop :=
  ∃ (H : Subgroup SL(2, ℤ)) (M : ℕ) (ι : Type) (_ : Fintype ι) (γ : ι → SL(2, ℤ)) (a : X.Kˣ) (x : X.Khat l),
    0 < M ∧ CongruenceSubgroup.Gamma M ≤ H ∧ H ≤ Gam N l ⊓ CongruenceSubgroup.Gamma (l ^ n) ∧ IsTr H (Gam N l) γ ∧
      LUnH X H (l ^ n) (a : X.K) ∧ Rep X l n a x ∧ t = trH X l w γ lam x

private theorem St.next [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [hl : Fact l.Prime] (N w : ℕ) (lam : Fin 2 → ℤ) (h2 : l ≠ 2)
    (n : ℕ) (hn : 1 ≤ n) (t : X.Fn l) (ht : St X l N w lam n t) : ∃ t', St X l N w lam (n + 1) t' ∧ CgF X l n t' t := by
  obtain ⟨H, M, ι, _, γ, a, x, hM, hMH, hH, hγ, ha, hx, rfl⟩ := ht
  have hl0 : 0 < l := hl.out.pos
  haveI : NeZero (l ^ (n + 1)) := ⟨(pow_pos hl0 _).ne'⟩
  obtain ⟨κ, _, δ, hδ⟩ := exTr H (CongruenceSubgroup.Gamma (l ^ (n + 1)))
  have hM' : CongruenceSubgroup.Gamma (M * l ^ (n + 1)) ≤ H ⊓ CongruenceSubgroup.Gamma (l ^ (n + 1)) :=
    le_inf ((gamma_le (dvd_mul_right _ _)).trans hMH) (gamma_le (dvd_mul_left _ _))
  have hMp : 0 < M * l ^ (n + 1) := Nat.mul_pos hM (pow_pos hl0 _)
  obtain ⟨f', hf', h, hh, hprod⟩ := step ε X H (H ⊓ CongruenceSubgroup.Gamma (l ^ (n + 1))) (M * l ^ (n + 1)) (l ^ n) l hMp
    (pow_pos hl0 _) hl0 hM' inf_le_left (fun h => neg_one_not l n h2 hn (hH h).2)
    (fun g hg d hd => ⟨H.mul_mem (H.mul_mem hg hd.1) (H.inv_mem hg),
      (CongruenceSubgroup.Gamma_normal _).conj_mem d hd.2 g⟩) κ δ hδ a ha
  rw [← pow_succ] at hf'
  let a' : X.Kˣ := Units.mk0 f' hf'.1
  let x' : X.Khat l := AdicCompletion.of (idl l) (X.Kl l) ((1 : ℤ_[l]) ⊗ₜ Additive.ofMul a')
  have hx' : ∀ k, Rep X l k a' x' := fun k => rfl
  obtain ⟨htr, hc⟩ := (trc ε X l N w n H hH ι γ hγ lam a x hx).2.2.2 _ κ δ inf_le_left hδ
  refine ⟨_, ⟨_, M * l ^ (n + 1), κ × ι, inferInstance, _, a', x', hMp, hM', ?_, htr, hf', hx' _, rfl⟩,
    hc a' (Units.mk0 h hh) x' (hx' _) hprod⟩
  exact inf_le_inf_right _ (hH.trans inf_le_left)

end

theorem UpperTheory.Kd.K4.liftL :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l : ℕ) [Fact l.Prime] (N w : ℕ), l ≠ 2 → ∃ c : ℕ, ∀ (n : ℕ) (H : Subgroup SL(2, ℤ)) (M : ℕ), 1 ≤ n → 0 < M → CongruenceSubgroup.Gamma M ≤ H →
      H ≤ Gam N l ⊓ CongruenceSubgroup.Gamma (l ^ n) → ∀ (ι : Type) [Fintype ι] (γ : ι → SL(2, ℤ)), IsTr H (Gam N l) γ →
      ∀ (lam : Fin 2 → ℤ) (a : X.Kˣ) (x : X.Khat l), LUnH X H (l ^ n) (a : X.K) → Rep X l n a x → ∃ b, LiftB X l N w n c (trH X l w γ lam x) b := by
  intro Ω _ _ _ ε X l _ N w h2
  obtain ⟨c, hc⟩ := lim ε X l N w
  refine ⟨c, fun n H M hn hM hMH hH ι _ γ hγ lam a x ha hx => ?_⟩
  have hs : ∀ (k : ℕ) (t : {t // St X l N w lam (n + k) t}), ∃ t' : {t // St X l N w lam (n + (k + 1)) t},
      CgF X l (n + k) t'.1 t.1 := fun k t => by
    obtain ⟨t', h1, h3⟩ := St.next X l N w lam h2 (n + k) (by omega) t.1 t.2
    exact ⟨⟨t', h1⟩, h3⟩
  choose F hF using hs
  let s : ∀ k : ℕ, {t // St X l N w lam (n + k) t} := fun k =>
    Nat.rec (motive := fun k => {t // St X l N w lam (n + k) t})
      ⟨trH X l w γ lam x, H, M, ι, inferInstance, γ, a, x, hM, hMH, hH, hγ, ha, hx, rfl⟩ F k
  refine hc n (fun k => (s k).1) (fun k => ?_) (fun k => hF k (s k)) (fun k => ?_)
  · obtain ⟨H, M, ι, _, γ, a, x, hM, hMH, hH, hγ, ha, hx, e⟩ := (s k).2
    show PolMod X l w (n + k) (s k).1
    rw [e]
    exact (trc ε X l N w (n + k) H hH ι γ hγ lam a x hx).1 (un_of X ha)
  · obtain ⟨H, M, ι, _, γ, a, x, hM, hMH, hH, hγ, ha, hx, e⟩ := (s k).2
    intro g hg
    show CgF X l (n + k) (X.act l _ (s k).1) (s k).1
    rw [e]
    exact (trc ε X l N w (n + k) H hH ι γ hγ lam a x hx).2.1 (inv_of X ha) g hg

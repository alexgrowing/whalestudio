import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankLevelDatumIdempotentEqOfSameShapeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubgroupCharacterIdempotentPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumSubgroupCharacterPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RepresentationRootSubgroupExchangeStatement

open Polynomial Classical GlobalTheory.BadShare

noncomputable section
namespace GlobalTheory.BadShare.RxStep

def sgOf {G : Type} [Group G] [Finite G] (S : G → Prop) (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) :
    Subgroup G where
  carrier := {u | S u}
  one_mem' := h1
  mul_mem' := fun {a b} ha hb => hm a b ha hb
  inv_mem' := fun {a} ha => by
    have hp : ∀ n : ℕ, S (a ^ n) := by
      intro n
      induction n with
      | zero => simpa using h1
      | succ n ih => rw [pow_succ]; exact hm _ _ ih ha
    have ho : 0 < orderOf a := orderOf_pos a
    have : a⁻¹ = a ^ (orderOf a - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel ho, pow_orderOf_eq_one]
    show S a⁻¹
    rw [this]; exact hp _

theorem mem_sgOf {G : Type} [Group G] [Finite G] (S : G → Prop) (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v))
    (u : G) : u ∈ sgOf S h1 hm ↔ S u := Iff.rfl

theorem exists_perm {F : Type} [Field F] {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    ∃ Q : GL (Fin N) F, ∀ (u : GL (Fin N) F) a b, (Q * u * Q⁻¹).val a b = u.val (σ a) (σ b) := by
  refine ⟨⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, ?_, ?_⟩, ?_⟩
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp
  · intro u a b
    show (σ.toPEquiv.toMatrix * u.val * σ.symm.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) F) a b = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    simp

theorem exists_cycle {N : ℕ} (i k : ℕ) (h : i + k < N) :
    ∃ σ : Equiv.Perm (Fin N), ∀ a : Fin N, (σ a : ℕ) =
      if (a : ℕ) < i then (a : ℕ) else if (a : ℕ) < i + k then a + 1 else if (a : ℕ) = i + k then i else a := by
  refine ⟨⟨fun a => ⟨if (a : ℕ) < i then (a : ℕ) else if (a : ℕ) < i + k then a + 1 else if (a : ℕ) = i + k then i else a, ?_⟩,
    fun a => ⟨if (a : ℕ) < i then (a : ℕ) else if (a : ℕ) = i then i + k else if (a : ℕ) ≤ i + k then a - 1 else a, ?_⟩,
    ?_, ?_⟩, fun a => rfl⟩
  · have := a.2; split_ifs <;> omega
  · have := a.2; split_ifs <;> omega
  · intro a; apply Fin.ext; simp only; split_ifs <;> omega
  · intro a; apply Fin.ext; simp only; split_ifs <;> omega

def tv {F : Type} [Field F] {N : ℕ} (e f : Fin N → F) (h : f ⬝ᵥ e = 0) : GL (Fin N) F :=
  ⟨1 + Matrix.vecMulVec e f, 1 - Matrix.vecMulVec e f,
    by simp [add_mul, mul_sub, Matrix.vecMulVec_mul_vecMulVec, h],
    by simp [sub_mul, mul_add, Matrix.vecMulVec_mul_vecMulVec, h]⟩

theorem comm_val {F : Type} [Field F] {N : ℕ} (x y : GL (Fin N) F) (e f ξ η : Fin N → F)
    (hx : x.val = 1 + Matrix.vecMulVec e ξ) (hy : y.val = 1 + Matrix.vecMulVec η f)
    (h1 : ξ ⬝ᵥ e = 0) (h2 : f ⬝ᵥ e = 0) :
    (y⁻¹ * x⁻¹ * y * x).val = 1 + Matrix.vecMulVec e (-(ξ ⬝ᵥ η) • f) := by
  have h3 : (-(ξ ⬝ᵥ η) • f) ⬝ᵥ e = 0 := by rw [smul_dotProduct, h2, smul_zero]
  have : y⁻¹ * x⁻¹ * y * x = tv e _ h3 := by
    have : y * x = x * y * tv e _ h3 := by
      apply Units.ext
      show y.val * x.val = x.val * y.val * (1 + Matrix.vecMulVec e (-(ξ ⬝ᵥ η) • f))
      rw [hx, hy]
      simp only [add_mul, mul_add, one_mul, mul_one, Matrix.vecMulVec_mul_vecMulVec, smul_dotProduct, h1, h2,
        zero_smul, smul_zero, Matrix.vecMulVec_zero]
      simp only [neg_smul, Matrix.vecMulVec_neg]
      abel
    rw [mul_assoc, this]; group
  rw [this]; rfl

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

theorem edge_iff (L : Lev g N) (h : L.sharp = true) (a b : Fin N) : L.Edge a b ↔
    (((b : ℕ) = a + 1 ∧ (a : ℕ) + 1 ≠ L.s ∧ ¬ (0 < L.k ∧ (a : ℕ) + 1 = L.s + L.k)) ∨
      ((a : ℕ) + 1 = L.s ∧ (b : ℕ) = L.s + L.k)) := by
  unfold Lev.Edge; rw [if_pos h]

theorem chi_eq (L : Lev g N) (h : L.sharp = true) (u : GG g N) (D : Matrix (Fin N) (Fin N) (ZMod g))
    (hu : u.val = 1 + D) (i j : Fin N) (hij : L.Edge i j) (hD : ∀ a b, L.Edge a b → a ≠ i ∨ b ≠ j → D a b = 0) :
    L.chi u = L.ψ (L.co i * D i j) := by
  have hne : ∀ a b, L.Edge a b → a ≠ b := by
    intro a b hab e
    rw [edge_iff L h, e] at hab
    omega
  unfold Lev.chi
  congr 1
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · rw [if_pos hij, hu, Matrix.add_apply, Matrix.one_apply_ne (hne _ _ hij), zero_add]
  · intro b _ hb
    split_ifs with hE
    · rw [hu, Matrix.add_apply, Matrix.one_apply_ne (hne _ _ hE), hD _ _ hE (Or.inr hb)]; simp
    · rfl
  · simp
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    split_ifs with hE
    · rw [hu, Matrix.add_apply, Matrix.one_apply_ne (hne _ _ hE), hD _ _ hE (Or.inl ha)]; simp
    · rfl
  · simp

def rowGrp (i : Fin N) (W : Fin N → Prop) (hi : ¬ W i) : Subgroup (GG g N) :=
  sgOf (fun u => ∃ ξ : Fin N → ZMod g, (∀ a, ¬ W a → ξ a = 0) ∧ u.val = 1 + Matrix.vecMulVec (Pi.single i 1) ξ)
    ⟨0, fun _ _ => rfl, by simp⟩ (by
      rintro u v ⟨ξ, h, hu⟩ ⟨ξ', h', hv⟩
      refine ⟨ξ + ξ', fun a ha => by simp [h a ha, h' a ha], ?_⟩
      rw [Units.val_mul, hu, hv]
      simp [add_mul, mul_add, Matrix.vecMulVec_mul_vecMulVec, h i hi, Matrix.vecMulVec_add, add_assoc])

def colGrp (j : Fin N) (W : Fin N → Prop) (hj : ¬ W j) : Subgroup (GG g N) :=
  sgOf (fun u => ∃ η : Fin N → ZMod g, (∀ a, ¬ W a → η a = 0) ∧ u.val = 1 + Matrix.vecMulVec η (Pi.single j 1))
    ⟨0, fun _ _ => rfl, by simp⟩ (by
      rintro u v ⟨ξ, h, hu⟩ ⟨ξ', h', hv⟩
      refine ⟨ξ + ξ', fun a ha => by simp [h a ha, h' a ha], ?_⟩
      rw [Units.val_mul, hu, hv]
      simp [add_mul, mul_add, Matrix.vecMulVec_mul_vecMulVec, h' j hj, Matrix.add_vecMulVec, add_assoc])

theorem mem_of_val (L : Lev g N) (u : GG g N) (D : Matrix (Fin N) (Fin N) (ZMod g)) (hu : u.val = 1 + D)
    (h1 : ∀ a b, b ≤ a → D a b = 0)
    (h2 : ∀ a b : Fin N, L.s ≤ a → (a : ℕ) < L.s + L.k → (b : ℕ) = L.s + L.k → D a b = 0) : L.Mem u := by
  refine ⟨⟨fun a => ?_, fun a b hab => ?_⟩, fun _ a b ha hb hc => ?_⟩
  · rw [hu, Matrix.add_apply, h1 a a le_rfl]; simp
  · rw [hu, Matrix.add_apply, h1 a b hab.le, Matrix.one_apply_ne hab.ne']; simp
  · rw [hu, Matrix.add_apply, h2 a b ha hb hc, Matrix.one_apply_ne (by intro e; rw [e] at hb; omega)]; simp

theorem exchange (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M)
    (L : Lev g N) (hL : L.sharp = true) (i : Fin N) (hs : L.s = i + 1) (J' : Subgroup (GG g N))
    (hJ' : ∀ u, u ∈ J' ↔ IsUp g N u ∧ ∀ b : Fin N, L.s ≤ b → (b : ℕ) < L.s + L.k → u.val i b = 0)
    (n : ℕ) (v : Fin n → M) (hv : LinearIndependent ℂ v) (he : ∀ m, ∀ u ∈ J', ρ u (v m) = L.chi u • v m) :
    n ≤ rk ρ L.e := by
  obtain ⟨m1, mm, c1, cm, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L
  let j : Fin N := ⟨L.s + L.k, L.hk⟩
  have hj : (j : ℕ) = L.s + L.k := rfl
  let W : Fin N → Prop := fun a => L.s ≤ a ∧ (a : ℕ) < L.s + L.k
  have hiW : ¬ W i := by simp only [W]; omega
  have hjW : ¬ W j := by simp only [W]; omega
  have hij : L.Edge i j := by rw [edge_iff L hL]; omega
  have hji : j ≠ i := by intro e; rw [e] at hj; omega
  let J : Subgroup (GG g N) := sgOf L.Mem m1 mm
  let X : Subgroup (GG g N) := rowGrp i W hiW
  let Y : Subgroup (GG g N) := colGrp j W hjW
  have hXJ : ∀ x ∈ X, L.Mem x ∧ L.chi x = 1 := by
    rintro x ⟨ξ, h, hx⟩
    refine ⟨mem_of_val L x _ hx ?_ ?_, ?_⟩
    · intro a b hab
      rw [Matrix.vecMulVec_apply]
      by_cases ha : a = i
      · rw [h b (by simp only [W]; subst ha; have := Fin.le_def.1 hab; omega), mul_zero]
      · rw [Pi.single_eq_of_ne ha, zero_mul]
    · intro a b _ _ hb
      rw [Matrix.vecMulVec_apply, h b (by simp only [W]; omega), mul_zero]
    · rw [chi_eq L hL x _ hx i j hij, Matrix.vecMulVec_apply, h j hjW]
      · simp
      · intro a b hab _
        rw [edge_iff L hL] at hab
        rw [Matrix.vecMulVec_apply]
        by_cases ha : a = i
        · rw [h b (by simp only [W]; subst ha; omega), mul_zero]
        · rw [Pi.single_eq_of_ne ha, zero_mul]
  have hYJ : ∀ y ∈ Y, y ∈ J' ∧ L.chi y = 1 := by
    rintro y ⟨η, h, hy⟩
    have hD : ∀ a b : Fin N, b ≤ a → Matrix.vecMulVec η (Pi.single j (1 : ZMod g)) a b = 0 := by
      intro a b hab
      rw [Matrix.vecMulVec_apply]
      by_cases hb : b = j
      · rw [h a (by simp only [W]; subst hb; have := Fin.le_def.1 hab; omega), zero_mul]
      · rw [Pi.single_eq_of_ne hb, mul_zero]
    refine ⟨(hJ' y).2 ⟨⟨fun a => ?_, fun a b hab => ?_⟩, fun b hb hb' => ?_⟩, ?_⟩
    · rw [hy, Matrix.add_apply, hD a a le_rfl]; simp
    · rw [hy, Matrix.add_apply, hD a b hab.le, Matrix.one_apply_ne hab.ne']; simp
    · rw [hy, Matrix.add_apply, Matrix.vecMulVec_apply, h i hiW,
        Matrix.one_apply_ne (by intro e; rw [← e] at hb; omega)]; simp
    · rw [chi_eq L hL y _ hy i j hij, Matrix.vecMulVec_apply, h i hiW]
      · simp
      · intro a b hab _
        rw [edge_iff L hL] at hab
        rw [Matrix.vecMulVec_apply]
        by_cases hb : b = j
        · rw [h a (by simp only [W]; subst hb; omega), zero_mul]
        · rw [Pi.single_eq_of_ne hb, mul_zero]
  have hdec : ∀ u, L.Mem u → ∃ x ∈ X, u * x ∈ J ⊓ J' := by
    intro u hu
    let ξ : Fin N → ZMod g := fun a => if W a then - u.val i a else 0
    have h0 : ∀ a, ¬ W a → ξ a = 0 := fun a ha => if_neg ha
    have hd : ξ ⬝ᵥ Pi.single i 1 = 0 := by simp [h0 i hiW]
    have hx : tv (Pi.single i 1) ξ hd ∈ X := ⟨ξ, h0, rfl⟩
    have hm := mm _ _ hu (hXJ _ hx).1
    refine ⟨_, hx, hm, (hJ' _).2 ⟨hm.1, fun b hb hb' => ?_⟩⟩
    show (u.val * (1 + Matrix.vecMulVec (Pi.single i 1) ξ)) i b = 0
    have : ξ b = - u.val i b := if_pos ⟨hb, hb'⟩
    rw [mul_add, mul_one, Matrix.mul_vecMulVec, Matrix.add_apply, Matrix.vecMulVec_apply, this]
    simp [hu.1.1 i]
  have hcomm : ∀ (x y : GG g N) (ξ η : Fin N → ZMod g), (∀ a, ¬ W a → ξ a = 0) →
      x.val = 1 + Matrix.vecMulVec (Pi.single i 1) ξ → y.val = 1 + Matrix.vecMulVec η (Pi.single j 1) →
      y⁻¹ * x⁻¹ * y * x ∈ J ⊓ J' ∧ L.chi (y⁻¹ * x⁻¹ * y * x) = L.ψ (L.co i * -(ξ ⬝ᵥ η)) := by
    intro x y ξ η h hx hy
    have hc := comm_val x y _ _ ξ η hx hy (by simp [h i hiW]) (by simp [Pi.single_eq_of_ne hji.symm])
    have hD : ∀ a b : Fin N, a ≠ i ∨ b ≠ j →
        Matrix.vecMulVec (Pi.single i (1 : ZMod g)) (-(ξ ⬝ᵥ η) • Pi.single j (1 : ZMod g)) a b = 0 := by
      rintro a b (ha | hb)
      · rw [Matrix.vecMulVec_apply, Pi.single_eq_of_ne ha, zero_mul]
      · rw [Matrix.vecMulVec_apply, Pi.smul_apply, Pi.single_eq_of_ne hb, smul_zero, mul_zero]
    have hm : L.Mem (y⁻¹ * x⁻¹ * y * x) := by
      refine mem_of_val L _ _ hc (fun a b hab => hD a b ?_) (fun a b ha _ _ => hD a b (Or.inl ?_))
      · by_contra hcon
        push_neg at hcon
        rw [hcon.1, hcon.2, Fin.le_def] at hab
        omega
      · intro e; rw [e] at ha; omega
    refine ⟨⟨hm, (hJ' _).2 ⟨hm.1, fun b hb hb' => ?_⟩⟩, ?_⟩
    · rw [hc, Matrix.add_apply, hD i b (Or.inr (by intro e; rw [e] at hb'; omega)),
        Matrix.one_apply_ne (by intro e; rw [← e] at hb; omega)]; simp
    · rw [chi_eq L hL _ _ hc i j hij (fun a b _ h => hD a b h), Matrix.vecMulVec_apply]
      simp
  obtain ⟨w, hw, hw'⟩ := GlobalTheory.T.representation_root_subgroup_exchange (GG g N) M ρ (J ⊓ J') X Y L.chi
    (by
      rintro x ⟨ξ, h, hx⟩ hB
      have : ξ = 0 := by
        funext b
        by_cases hb : W b
        · have := ((hJ' x).1 hB.2).2 b hb.1 hb.2
          rw [hx, Matrix.add_apply, Matrix.one_apply_ne (by intro e; rw [← e] at hb; exact hiW hb),
            Matrix.vecMulVec_apply] at this
          simpa using this
        · exact h b hb
      apply Units.ext
      rw [hx, this]; simp)
    (by
      intro b hb x hx
      have hbx : b * x ∈ J := J.mul_mem hb.1 (hXJ x hx).1
      obtain ⟨x', hx', hb'⟩ := hdec _ (J.inv_mem hbx)
      refine ⟨x', hx', ((b * x)⁻¹ * x')⁻¹, Subgroup.inv_mem _ hb', by group, ?_⟩
      have e : x' * ((b * x)⁻¹ * x')⁻¹ = b * x := by group
      have h1 := cm _ _ (hXJ x' hx').1 (J.inv_mem hb'.1)
      rw [e, cm _ _ hb.1 (hXJ x hx).1, (hXJ x hx).2, (hXJ x' hx').2] at h1
      simpa using h1.symm)
    (by
      rintro x ⟨ξ, h, hx⟩ y ⟨η, _, hy⟩
      exact (hcomm x y ξ η h hx hy).1)
    (by
      rintro x ⟨ξ, h, hx⟩ x' ⟨ξ', h', hx'⟩ hne
      have hξ : ξ ≠ ξ' := by
        intro e; apply hne; apply Units.ext; rw [hx, hx', e]
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hξ
      have haW : W a := by
        by_contra hc; exact ha (by rw [h a hc, h' a hc])
      obtain ⟨t, ht⟩ := AddChar.ne_one_iff.1 L.hψ
      have hc : (L.co i : ZMod g) * (ξ' a - ξ a) ≠ 0 := mul_ne_zero (L.co i).ne_zero (sub_ne_zero.2 ha.symm)
      let η : Fin N → ZMod g := Pi.single a (t / ((L.co i : ZMod g) * (ξ' a - ξ a)))
      have h0 : ∀ b, ¬ W b → η b = 0 := fun b hb => Pi.single_eq_of_ne (by intro e; rw [e] at hb; exact hb haW) _
      have hd : (Pi.single j 1 : Fin N → ZMod g) ⬝ᵥ η = 0 := by simp [h0 j hjW]
      refine ⟨tv η (Pi.single j 1) hd, ⟨η, h0, rfl⟩, ?_⟩
      rw [(hcomm x _ ξ η h hx rfl).2, (hcomm x' _ ξ' η h' hx' rfl).2]
      intro e
      apply ht
      have e2 : (L.co i : ZMod g) * -(ξ ⬝ᵥ η) = t + L.co i * -(ξ' ⬝ᵥ η) := by
        simp only [η, dotProduct_single]
        have h3 := left_ne_zero_of_mul hc
        have h4 := right_ne_zero_of_mul hc
        field_simp
        ring
      rw [e2, AddChar.map_add_eq_mul] at e
      have hn : L.ψ (L.co i * -(ξ' ⬝ᵥ η)) ≠ 0 := by
        intro h5
        have := L.ψ.map_add_eq_mul (L.co i * -(ξ' ⬝ᵥ η)) (-(L.co i * -(ξ' ⬝ᵥ η)))
        rw [h5] at this
        simp at this
      exact mul_right_cancel₀ hn (by rw [e, one_mul]))
    n v hv
    (fun m => ⟨fun b hb => he m b hb.2, fun y hy => by rw [he m y (hYJ y hy).1, (hYJ y hy).2, one_smul]⟩)
  refine (GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) M ρ L.Mem L.chi m1 mm c1 cm).2.2.2 n w hw ?_
  intro m u hu
  obtain ⟨x, hx, hb⟩ := hdec u hu
  have e : u = (u * x) * x⁻¹ := by group
  have h1 := cm _ _ hu (hXJ x hx).1
  rw [(hXJ x hx).2, mul_one] at h1
  calc ρ u (w m) = ρ (u * x) (ρ x⁻¹ (w m)) := by rw [← Module.End.mul_apply, ← map_mul, ← e]
    _ = _ := by rw [(hw' m).2 _ (X.inv_mem hx), (hw' m).1 _ hb, h1]

theorem rk_le_step : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), ∀ L L' : Lev g N, L.sharp = true → L'.sharp = true → L.k = L'.k → L.s = L'.s + 1 → rk ρ L'.e ≤ rk ρ L.e := by
  intro g _ N M _ _ _ ρ L L' hL hL' hk hs
  have hN := L.hk
  obtain ⟨σ, hσ⟩ := exists_cycle (N := N) L'.s L'.k L'.hk
  obtain ⟨Q, hQ⟩ := exists_perm (F := ZMod g) σ
  let K : Lev g N := ⟨true, L'.s, L'.k, L'.hk, L.ψ, L.hψ, fun a => L.co (σ a)⟩
  rw [GlobalTheory.T.rank_levelDatum_idempotent_eq_of_same_shape g N M ρ L' K hL' rfl rfl]
  obtain ⟨m1, mm, c1, cm, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N K
  have hE : ∀ a b, K.Edge a b ↔ L.Edge (σ a) (σ b) := by
    intro a b
    rw [edge_iff K rfl, edge_iff L hL, hσ, hσ, hk, hs]
    show (((b : ℕ) = a + 1 ∧ (a : ℕ) + 1 ≠ L'.s ∧ ¬ (0 < L'.k ∧ (a : ℕ) + 1 = L'.s + L'.k)) ∨
      ((a : ℕ) + 1 = L'.s ∧ (b : ℕ) = L'.s + L'.k)) ↔ _
    split_ifs <;> omega
  have hchi : ∀ u, K.chi (Q * u * Q⁻¹) = L.chi u := by
    intro u
    unfold Lev.chi
    show L.ψ _ = L.ψ _
    congr 1
    refine Fintype.sum_equiv σ _ _ fun a => ?_
    refine Fintype.sum_equiv σ _ _ fun b => ?_
    rw [hQ]
    exact if_congr (hE a b) rfl rfl
  let i : Fin N := ⟨L'.s, by omega⟩
  have hi : (i : ℕ) = L'.s := rfl
  let J' : Subgroup (GG g N) := sgOf (fun u => K.Mem (Q * u * Q⁻¹)) (by simpa using m1) (by
    intro u v hu hv
    have : Q * (u * v) * Q⁻¹ = (Q * u * Q⁻¹) * (Q * v * Q⁻¹) := by group
    rw [this]; exact mm _ _ hu hv)
  have hJ' : ∀ u, u ∈ J' ↔ IsUp g N u ∧ ∀ b : Fin N, L.s ≤ b → (b : ℕ) < L.s + L.k → u.val i b = 0 := by
    intro u
    rw [mem_sgOf]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      simp only [hQ] at h1 h2 h3
      have h4 : ∀ a b : Fin N, L'.s ≤ a → (a : ℕ) < L'.s + L'.k → (b : ℕ) = L'.s + L'.k → u.val (σ a) (σ b) = 0 :=
        h3 rfl
      refine ⟨⟨fun a => by simpa using h1 (σ.symm a), fun a b hab => ?_⟩, fun b hb hb' => ?_⟩
      · obtain ⟨a, rfl⟩ := σ.surjective a
        obtain ⟨b, rfl⟩ := σ.surjective b
        by_cases hc : b < a
        · exact h2 a b hc
        · rw [Fin.lt_def, hσ, hσ] at hab
          rw [Fin.lt_def] at hc
          apply h4 <;> split_ifs at hab <;> omega
      · obtain ⟨a, ha⟩ := σ.surjective i
        obtain ⟨b, rfl⟩ := σ.surjective b
        rw [← ha]
        apply h2
        have h5 := congrArg Fin.val ha
        rw [hσ] at h5 hb hb'
        rw [Fin.lt_def]
        split_ifs at h5 hb hb' <;> omega
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨fun a => by rw [hQ]; exact h1 _, fun a b hab => ?_⟩, fun _ a b ha ha' hb => ?_⟩
      · rw [hQ]
        by_cases hc : σ b < σ a
        · exact h2 _ _ hc
        · rw [Fin.lt_def, hσ, hσ] at hc
          rw [Fin.lt_def] at hab
          have : σ a = i := by
            apply Fin.ext; rw [hσ, hi]; split_ifs at hc ⊢ <;> omega
          rw [this]
          apply h3 <;> rw [hσ] <;> split_ifs at hc ⊢ <;> omega
      · rw [hQ]
        apply h2
        change L'.s ≤ a at ha
        change (a : ℕ) < L'.s + L'.k at ha'
        change (b : ℕ) = L'.s + L'.k at hb
        rw [Fin.lt_def, hσ, hσ]
        split_ifs <;> omega
  have hr := (GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) M ρ K.Mem K.chi m1 mm c1 cm).2.2.1
  let bs := Module.finBasis ℂ (LinearMap.range (op ρ K.e))
  have hinj : LinearMap.ker (ρ Q⁻¹ ∘ₗ (LinearMap.range (op ρ K.e)).subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    have := congrArg (ρ Q) hxy
    apply Subtype.ext
    simpa [← Module.End.mul_apply, ← map_mul] using this
  refine exchange M ρ L hL i hs J' hJ' _ _ (bs.linearIndependent.map' _ hinj) ?_
  intro m u hu
  show ρ u (ρ Q⁻¹ (bs m).1) = L.chi u • ρ Q⁻¹ (bs m).1
  have h1 := (hr (bs m).1).1 (bs m).2 _ hu
  rw [← map_smul, ← hchi, ← h1, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

end GlobalTheory.BadShare.RxStep

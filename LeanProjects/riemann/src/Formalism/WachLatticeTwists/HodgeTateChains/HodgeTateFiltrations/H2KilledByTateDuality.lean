import Formalism.WachLatticeTwists.HodgeTateChains.H2KilledByTateDuality
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.TwistKill

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Polynomial

theorem tbcB : StatTBcB := by
  intro ℓ _ s m t e gK U A _ _ Hf y he h
  have hle : cTB ℓ s m e gK U ≤ cB ℓ s m t gK U :=
    Finset.le_sup (f := fun e => cTB ℓ s m e gK U) (Finset.mem_range.2 he)
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
  rw [hj, add_comm, pow_add, mul_smul]
  exact Hf.smul_mem _ h

theorem h2_killed_by_tate_duality : H2KilledByTateDuality := by
  intro ℓ _ u s hs h2 hu e H2 M0 P _ _ _ _ _ _ pair hinj hM0 x
  obtain ⟨hne, hval⟩ := Formalism.WindowSums.valuation_zpow_sub_one ℓ u s hs h2 hu ((e : ℤ) + 1) (by omega)
  have hv : padicValInt ℓ ((e : ℤ) + 1) = padicValNat ℓ (e + 1) := by
    unfold padicValInt
    congr 1
  rw [hv] at hval
  obtain ⟨c, hc⟩ : ∃ c : ℤ_[ℓ]ˣ, (((u ^ ((e : ℤ) + 1) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1)
      = (c : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ (s + padicValNat ℓ (e + 1)) := by
    have h := PadicInt.unitCoeff_spec hne
    rw [hval] at h
    exact ⟨_, h⟩
  have hk : ∀ y : M0, ((ℓ : ℤ_[ℓ]) ^ (s + padicValNat ℓ (e + 1))) • y = 0 := by
    intro y
    have h1 : (((u ^ ((e : ℤ) + 1) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) • y = 0 := by
      rw [sub_smul, one_smul, hM0, sub_self]
    rw [hc, mul_smul] at h1
    have h3 := congrArg (fun v => ((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • v) h1
    simpa [smul_smul] using h3
  apply hinj
  rw [map_smul, map_zero]
  ext y
  rw [LinearMap.smul_apply, ← map_smul, hk, map_zero, LinearMap.zero_apply]

theorem freeAlg : StatFreeAlg := by
  intro ℓ _ w U i V _ _ g hkill x
  constructor
  · have h0 : aeval g ((X - 1) * Rpoly ℓ w U i) x = 0 := by rw [hkill]; rfl
    rw [map_mul, Module.End.mul_apply] at h0
    have h1 : g (aeval g (Rpoly ℓ w U i) x) - aeval g (Rpoly ℓ w U i) x = 0 := by simpa using h0
    exact sub_eq_zero.1 h1
  · obtain ⟨R', hR'⟩ := poly_split (Rpoly ℓ w U i)
    refine ⟨aeval g R' x, ?_⟩
    rw [aeval_split g _ R' hR' x, add_sub_cancel_left]

lemma freeMono {ℓ : ℕ} [Fact ℓ.Prime] {H0 H1 : Type} [AddCommGroup H0] [Module ℤ_[ℓ] H0]
    [AddCommGroup H1] [Module ℤ_[ℓ] H1] (cup : H0 →ₗ[ℤ_[ℓ]] H1) (al al' : ℕ) (h : al ≤ al')
    (hF : FreeIn ℓ cup al) : FreeIn ℓ cup al' := by
  intro y
  obtain ⟨z, t, hz⟩ := hF y
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨((ℓ : ℤ_[ℓ]) ^ j) • z, t, ?_⟩
  rw [map_smul, add_comm, pow_add, mul_smul, ← smul_sub, smul_comm, hz, smul_zero]

theorem freePiece : StatFreePiece := by
  intro ℓ _ w m hm h2 hw U i A P H0A cup ⟨hS, ⟨hI1, hI2⟩, hT4, ⟨_, hT3⟩, htf, hHT⟩ hlog y
  have hkill : aeval P.gm ((X - 1) * Rpoly ℓ w U i) = 0 := by
    obtain ⟨q, hq⟩ := (htpoly ℓ w U i).1
    rw [hq, map_mul, hHT, zero_mul]
  obtain ⟨hne, hval⟩ := rVal ℓ w m hm h2 hw U i
  obtain ⟨c, hc⟩ : ∃ c : ℤ_[ℓ]ˣ, (Rpoly ℓ w U i).eval 1 = (c : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ (rI ℓ m U i) := by
    have h := PadicInt.unitCoeff_spec hne
    rw [hval] at h
    exact ⟨_, h⟩
  obtain ⟨a, x, hax⟩ := (hI1 ((ℓ : ℤ_[ℓ]) • P.lam y)).1 (by rw [map_smul]; exact hT4 _)
  obtain ⟨hfix, y', hy'⟩ := freeAlg ℓ w U i P.Wm P.gm hkill a
  generalize aeval P.gm (Rpoly ℓ w U i) a = a0 at hfix hy'
  have h1 : P.infm a0 = ((Rpoly ℓ w U i).eval 1) • P.infm a := by
    have h := (hI2 (a0 - ((Rpoly ℓ w U i).eval 1) • a) 0).2
      ⟨⟨y', hy'⟩, 0, by rw [map_zero, sub_zero]⟩
    rw [map_zero, add_zero, map_sub, map_smul] at h
    exact sub_eq_zero.1 h
  have hfix' : P.gm (((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • a0) = ((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • a0 := by
    rw [map_smul, hfix]
  obtain ⟨z, hz⟩ := hlog _ hfix'
  have h3 : ((ℓ : ℤ_[ℓ]) ^ (rI ℓ m U i)) • P.infm a = P.infm (((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • a0) := by
    rw [map_smul, h1, hc, smul_smul, ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨x'', hx''⟩ := hT3 x
  have h4 : (ℓ : ℤ_[ℓ]) • P.infX x = 0 := by
    have h := (hI2 0 ((ℓ : ℤ_[ℓ]) • x)).2 ⟨⟨0, by rw [map_zero, sub_zero]⟩, x'', hx''⟩
    rw [map_zero, zero_add, map_smul] at h
    exact h
  refine ⟨z, 1, ?_⟩
  have h5 : ((ℓ : ℤ_[ℓ]) ^ (rI ℓ m U i + m + 2)) • y
      = cup z + ((ℓ : ℤ_[ℓ]) ^ m) • (((ℓ : ℤ_[ℓ]) ^ (rI ℓ m U i)) • P.io (P.infX x)) := by
    calc ((ℓ : ℤ_[ℓ]) ^ (rI ℓ m U i + m + 2)) • y
        = ((ℓ : ℤ_[ℓ]) ^ m) • (((ℓ : ℤ_[ℓ]) ^ (rI ℓ m U i)) • P.io ((ℓ : ℤ_[ℓ]) • P.lam y)) := by
          rw [map_smul, hS, smul_smul, smul_smul, smul_smul]
          congr 1
          ring
      _ = ((ℓ : ℤ_[ℓ]) ^ m) • (P.io (((ℓ : ℤ_[ℓ]) ^ (rI ℓ m U i)) • P.infm a) + ((ℓ : ℤ_[ℓ]) ^ (rI ℓ m U i)) • P.io (P.infX x)) := by
          rw [hax, map_add, smul_add, map_smul]
      _ = _ := by rw [h3, smul_add, hz]
  rw [h5, add_sub_cancel_left, pow_one, smul_comm, smul_comm (ℓ : ℤ_[ℓ]), ← map_smul, h4, map_zero, smul_zero,
    smul_zero]

theorem freeExt : StatFreeExt := by
  intro ℓ _ H0' H0 H0'' H1' H1 H1'' _ _ _ _ _ _ _ _ _ _ _ _ i0 p0 dl i1 p1 cup' cup cup'' c' c'' al' al''
    hex0 hex1 hc1 hc2 hT5 hk' hk'' hF' hF'' y
  obtain ⟨z'', t, hz''⟩ := hF'' (p1 y)
  have h1 : ((ℓ : ℤ_[ℓ]) ^ c'') • (((ℓ : ℤ_[ℓ]) ^ al'') • p1 y - cup'' z'') = 0 := hk'' _ ⟨t, hz''⟩
  have h2 : dl (((ℓ : ℤ_[ℓ]) ^ c') • z'') = 0 := by rw [map_smul]; exact hk' _ (hT5 z'')
  obtain ⟨z1, hz1⟩ := (hex0 _).1 h2
  have h3 : p1 (((ℓ : ℤ_[ℓ]) ^ (c' + c'' + al'')) • y - cup (((ℓ : ℤ_[ℓ]) ^ c'') • z1)) = 0 := by
    rw [map_sub, ← hc2, map_smul p0, hz1, map_smul, map_smul, map_smul]
    have h4 : ((ℓ : ℤ_[ℓ]) ^ (c' + c'' + al'')) • p1 y - ((ℓ : ℤ_[ℓ]) ^ c'') • (((ℓ : ℤ_[ℓ]) ^ c') • cup'' z'')
        = ((ℓ : ℤ_[ℓ]) ^ c') • (((ℓ : ℤ_[ℓ]) ^ c'') • (((ℓ : ℤ_[ℓ]) ^ al'') • p1 y - cup'' z'')) := by
      simp only [smul_sub, smul_smul, ← pow_add]
      have e1 : c' + c'' + al'' = c' + (c'' + al'') := by ring
      have e2 : c'' + c' = c' + c'' := by ring
      rw [e1, e2]
    rw [h4, h1, smul_zero]
  obtain ⟨y', hy'⟩ := (hex1 _).1 h3
  obtain ⟨z', t', hz'⟩ := hF' y'
  refine ⟨((ℓ : ℤ_[ℓ]) ^ (al' + c'')) • z1 + i0 z', t', ?_⟩
  have h5 := congrArg i1 hz'
  rw [map_smul, map_sub, map_smul, hy', ← hc1, map_zero] at h5
  have h6 : ((ℓ : ℤ_[ℓ]) ^ (al' + al'' + c' + c'')) • y - cup (((ℓ : ℤ_[ℓ]) ^ (al' + c'')) • z1 + i0 z')
      = ((ℓ : ℤ_[ℓ]) ^ al') • (((ℓ : ℤ_[ℓ]) ^ (c' + c'' + al'')) • y - cup (((ℓ : ℤ_[ℓ]) ^ c'') • z1)) - cup (i0 z') := by
    rw [map_add, smul_sub, smul_smul, ← pow_add, map_smul, map_smul, smul_smul, ← pow_add]
    have e1 : al' + al'' + c' + c'' = al' + (c' + c'' + al'') := by ring
    rw [e1]; abel
  rw [h6]; exact h5

theorem halving : StatHalving := by
  intro α γ P hmono hone hext
  have main : ∀ n, ∀ i j, j - i = n → i < j →
      P i j (∑ x ∈ Finset.Ico i j, α x + (∑ x ∈ Finset.Ico i j, γ x) * Nat.clog 2 (j - i)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i j hn hij
      by_cases h1 : j = i + 1
      · subst h1
        have e1 : i + 1 - i = 1 := by omega
        rw [e1, Nat.clog_one_right, Nat.mul_zero, Nat.add_zero, Nat.Ico_succ_singleton,
          Finset.sum_singleton]
        exact hone i
      · have hik : i < i + (j - i) / 2 := by omega
        have hkj : i + (j - i) / 2 < j := by omega
        have A1 := ih (i + (j - i) / 2 - i) (by omega) i (i + (j - i) / 2) rfl hik
        have A2 := ih (j - (i + (j - i) / 2)) (by omega) (i + (j - i) / 2) j rfl hkj
        have A3 := hext i (i + (j - i) / 2) j _ _ hik hkj A1 A2
        refine hmono _ _ _ _ ?_ A3
        have hc : Nat.clog 2 (j - i) = Nat.clog 2 ((j - i + 2 - 1) / 2) + 1 :=
          Nat.clog_of_two_le (by norm_num) (by omega)
        have c1 : Nat.clog 2 (i + (j - i) / 2 - i) ≤ Nat.clog 2 ((j - i + 2 - 1) / 2) :=
          Nat.clog_mono_right 2 (by omega)
        have c2 : Nat.clog 2 (j - (i + (j - i) / 2)) ≤ Nat.clog 2 ((j - i + 2 - 1) / 2) :=
          Nat.clog_mono_right 2 (by omega)
        have sα := Finset.sum_Ico_consecutive α hik.le hkj.le
        have sγ := Finset.sum_Ico_consecutive γ hik.le hkj.le
        rw [hc, ← sα, ← sγ]
        generalize Nat.clog 2 ((j - i + 2 - 1) / 2) = L at c1 c2
        generalize Nat.clog 2 (i + (j - i) / 2 - i) = L1 at c1
        generalize Nat.clog 2 (j - (i + (j - i) / 2)) = L2 at c2
        generalize ∑ x ∈ Finset.Ico i (i + (j - i) / 2), γ x = g1
        generalize ∑ x ∈ Finset.Ico (i + (j - i) / 2) j, γ x = g2
        nlinarith [Nat.mul_le_mul_left g1 c1, Nat.mul_le_mul_left g2 c2]
  intro i j hij
  exact main _ i j rfl hij

theorem freeGm : StatFreeGm := by
  intro ℓ _ w m hm h2 hw U a D hD hP hlog hLL i j hij
  refine halving (fun x => rI ℓ m U (a + x) + m + 2) (fun x => 2 + max 1 (rI ℓ m U (a + x)))
    (fun i j al => FreeIn ℓ (D.cup i j) al) (fun i j al al' h hF => freeMono _ al al' h hF)
    (fun i => freePiece ℓ w m hm h2 hw U (a + i) _ (D.piece i) _ (D.cup i (i + 1)) (hP i) (hlog i))
    (fun i k j al' al'' hik hkj hF'' hF' => ?_) i j hij
  obtain ⟨e0, e1, c1, c2, t5⟩ := hD i k j hik hkj
  have h := freeExt ℓ (D.H0 k j) (D.H0 i j) (D.H0 i k) (D.H1 k j) (D.H1 i j) (D.H1 i k)
    (D.i0 i k j) (D.p0 i k j) (D.dl i k j) (D.i1 i k j) (D.p1 i k j) (D.cup k j) (D.cup i j) (D.cup i k)
    _ _ al' al'' e0 e1 c1 c2 t5 (hLL k j hkj) (hLL i k hik) hF' hF''
  have hs := Finset.sum_Ico_consecutive (fun x => 2 + max 1 (rI ℓ m U (a + x))) hik.le hkj.le
  refine freeMono _ _ _ (le_of_eq ?_) h
  rw [← hs]; ring

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

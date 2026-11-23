import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.LinAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.FirstOrderLiftConstantPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Claim2
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DualEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TpDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.ExistsSemilinearFunctionalNonzero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.LiftsSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.AlSel
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.pres :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ D0, SelmerRankBoundLaurent S.h S.k D0 → EvenCocyclesLiftLaurent S.h S.k → SelmerSpannedByKappaLaurent S.h S.k → S.Pres D0 := by
  intro l _ S D0 h1 h2 h3
  obtain ⟨hfin, hsep, hlift⟩ := tpDual l S
  obtain ⟨hsel, -, hlin, -⟩ := alSel l S
  obtain ⟨L0, Ladd, Lsmul⟩ := liftsSub l S.L S.G S.G0 S.h S.n S.x S.k
  have hz : S.alC 0 = 0 := by
    simpa using hlin (Fin 0) (fun _ => 0) (fun _ => 0)
  have hadd : ∀ a b : S.Bh →+ S.F, S.alC (a + b) = S.alC a + S.alC b := by
    intro a b
    simpa [Fin.sum_univ_two] using hlin (Fin 2) (fun _ => 1) ![a, b]
  have hsmul : ∀ (r : S.F) (a : S.Bh →+ S.F), S.alC (r • a) = r • S.alC a := by
    intro r a
    simpa using hlin (Fin 1) (fun _ => r) (fun _ => a)
  let U : Submodule S.F (Fin S.k.g → S.Tp) :=
    { carrier := {a | Lifts S.h S.k (fun j => S.alC (a j : S.Bh →+ S.F))}
      add_mem' := by
        intro a b ha hb
        show Lifts S.h S.k (fun j => S.alC ((a + b) j : S.Bh →+ S.F))
        convert Ladd _ _ ha hb using 1
        funext j
        simp [hadd]
      zero_mem' := by
        show Lifts S.h S.k (fun j => S.alC ((0 : Fin S.k.g → S.Tp) j : S.Bh →+ S.F))
        convert L0 using 1
        funext j
        simp [hz]
      smul_mem' := by
        intro r a ha
        show Lifts S.h S.k (fun j => S.alC ((r • a) j : S.Bh →+ S.F))
        convert Lsmul r _ ha using 1
        funext j
        simp [hsmul] }
  have hA : ∀ z : Fin (S.k.g + 1) → Fin S.k.g → S.Tp,
      ∃ c : Fin (S.k.g + 1) → S.F, c ≠ 0 ∧ ∑ i, c i • z i ∈ U := by
    intro z
    obtain ⟨c, hc, hL⟩ := h2 (fun i j => S.alC (z i j : S.Bh →+ S.F)) (fun i j => hsel _ (z i j).2)
    refine ⟨c, hc, ?_⟩
    show Lifts S.h S.k _
    convert hL using 1
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
    exact hlin _ _ _
  have hB : ∀ (e : ℕ) (α : Fin e → S.Tp), LinearIndependent S.F α →
      (∀ i j, Pi.single j (α i) ∈ U) → e + S.k.g * S.k.g ≤ D0 := by
    intro e α hα hs
    refine claim1 l S D0 h1 e α hα ?_
    intro i j
    have hij : Lifts S.h S.k (fun j' => S.alC ((Pi.single j (α i) : Fin S.k.g → S.Tp) j' : S.Bh →+ S.F)) := hs i j
    convert hij using 1
    funext j'
    by_cases hj : j' = j
    · subst hj
      simp
    · simp [Pi.single_apply, hj, hz]
  haveI := hfin
  obtain ⟨X, c, hXspan, hcind, hrel⟩ := linAlg S.F S.Tp S.k.g D0 U hA hB
  choose Xb hXm hXv using fun k => hlift (X k)
  choose cO hcO using fun (p : Fin S.k.g × Fin S.k.g) (a : Fin D0) => S.oo_surj (c p a)
  obtain ⟨m, hmD, hmspan⟩ := dualEx l S h3
  have hrF : ∀ b ∈ maximalIdeal S.Bh, S.rF b = 0 := by
    intro b hb
    rw [← RingHom.mem_ker, S.rF_ker]
    exact hb
  have hmulT : ∀ α : S.Bh →+ S.F, α ∈ S.Tp → ∀ (o : S.OO) (b : S.Bh), b ∈ maximalIdeal S.Bh →
      α (algebraMap S.OO S.Bh o * b) = S.rF (algebraMap S.OO S.Bh o) * α b := by
    intro α hα o b hb
    obtain ⟨hd, hO, -⟩ := hα
    rw [hd, hO, hrF b hb, zero_mul, add_zero]
  unfold Ctx.Pres
  refine ⟨Xb, m, cO, hXm, hmspan, ?_, ?_, ?_⟩
  · set ψ := S.rF.comp (algebraMap S.OO S.Bh) with hψ
    have hker : RingHom.ker ψ = maximalIdeal S.OO :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ψ S.oo_surj)
    rw [Fintype.linearIndependent_iff]
    intro r hr p
    obtain ⟨s, rfl⟩ : ∃ s : Fin S.k.g × Fin S.k.g → S.OO, (fun q => residue S.OO (s q)) = r :=
      ⟨fun q => (residue_surjective (r q)).choose,
        funext fun q => (residue_surjective (r q)).choose_spec⟩
    have h0 : ∀ q, ψ (s q) = 0 := by
      refine (Fintype.linearIndependent_iff.mp hcind) (fun q => ψ (s q)) ?_
      funext a
      have ha := congrFun hr a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ha ⊢
      have hm : (∑ q, s q * cO q a) ∈ maximalIdeal S.OO := by
        rw [← residue_eq_zero_iff, map_sum]
        simpa [map_mul] using ha
      rw [← hker, RingHom.mem_ker, map_sum] at hm
      simpa [map_mul, hcO] using hm
    show residue S.OO (s p) = 0
    rw [residue_eq_zero_iff, ← hker, RingHom.mem_ker]
    exact h0 p
  · intro b hb
    let ξ : Module.Dual S.F S.Tp :=
      { toFun := fun α => (α : S.Bh →+ S.F) b
        map_add' := fun α β => rfl
        map_smul' := fun r α => rfl }
    have hξ : ξ ∈ Submodule.span S.F (Set.range X) := by
      rw [hXspan]
      exact Submodule.mem_top
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun S.F).mp hξ
    choose o ho using fun k => S.oo_surj (r k)
    have hb'm : b - ∑ k, algebraMap S.OO S.Bh (o k) * Xb k ∈ maximalIdeal S.Bh :=
      Ideal.sub_mem _ hb (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hXm k))
    have hb'J : b - ∑ k, algebraMap S.OO S.Bh (o k) * Xb k ∈ S.J2 := by
      refine hsep _ hb'm fun α hα => ?_
      have e1 : α b = ∑ k, r k * X k ⟨α, hα⟩ := by
        have := congrArg (fun f : Module.Dual S.F S.Tp => f ⟨α, hα⟩) hr
        simpa [ξ] using this.symm
      have e2 : ∀ k, α (algebraMap S.OO S.Bh (o k) * Xb k) = r k * X k ⟨α, hα⟩ := by
        intro k
        rw [hmulT α hα _ _ (hXm k), ← hXv k ⟨α, hα⟩, ← ho k]
        rfl
      simp only [map_sub, map_sum, e2, e1, sub_self]
    rw [← sub_add_cancel b (∑ k, algebraMap S.OO S.Bh (o k) * Xb k)]
    refine Ideal.add_mem _ (Ideal.mem_sup_right hb'J) (Ideal.mem_sup_left ?_)
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
  · intro i
    refine phSep l S _ fun Φ hΦ => ?_
    obtain ⟨α, hαdef, hαL⟩ := claim2 l S m hmD Φ hΦ
    have hαU : α ∈ U := hαL
    have hrelα := hrel α hαU i
    have hb : ∀ j, (∑ a, algebraMap S.OO S.Bh (cO (i, j) a) * Xb a) ∈ maximalIdeal S.Bh :=
      fun j => Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hXm a)
    have e3 : ∀ j, Φ ((∑ a, algebraMap S.OO S.Bh (cO (i, j) a) * Xb a) • m j)
        = ∑ a, c (i, j) a * X a (α j) := by
      intro j
      have hj := hαdef j (∑ a, algebraMap S.OO S.Bh (cO (i, j) a) * Xb a)
      rw [hrF _ (hb j), zero_mul, sub_zero] at hj
      rw [← hj, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hmulT _ (α j).2 _ _ (hXm a), hXv a (α j), ← hcO (i, j) a]
      rfl
    rw [map_sum]
    simp only [e3]
    exact hrelα

import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BcOnFalse

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap.DividedPowerIdealFacts

variable {A B : Type} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B}

theorem dividedPowerFiltration_anti (γ : DividedPowers I) {r r' : ℕ} (h : r ≤ r') : pdP γ r' ≤ pdP γ r := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨L, hL, hr, rfl⟩
  exact Ideal.subset_span ⟨L, hL, h.trans hr, rfl⟩

theorem dividedPowerFiltration_zero (γ : DividedPowers I) : pdP γ 0 = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span ⟨[], by simp, by simp, by simp⟩

theorem dpow_mem_pdP (γ : DividedPowers I) (n : ℕ) {x : A} (hx : x ∈ I) : γ.dpow n x ∈ pdP γ n :=
  Ideal.subset_span ⟨[(n, x)], by simpa using hx, by simp, by simp⟩

theorem dividedPowerFiltration_mul (γ : DividedPowers I) (a b : ℕ) : pdP γ a * pdP γ b ≤ pdP γ (a + b) := by
  unfold pdP
  rw [Ideal.span_mul_span']
  refine Ideal.span_le.2 ?_
  rintro _ ⟨x, ⟨L1, h1, r1, rfl⟩, y, ⟨L2, h2, r2, rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨L1 ++ L2, ?_, ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact h1 q hq
    · exact h2 q hq
  · simp only [List.map_append, List.sum_append]; omega
  · simp [List.prod_append]

theorem dividedPowerFiltration_le_map (γ : DividedPowers I) (δ : DividedPowers J) (f : A →+* B) (hf : IsDPMorphism γ δ f)
    (hJ : J = I.map f) (r : ℕ) : pdP δ r ≤ (pdP γ r).map f := by

  have key : ∀ x ∈ J, ∀ n, δ.dpow n x ∈ (pdP γ n).map f := by
    intro x hx
    have hx' : x ∈ I.map f := hJ ▸ hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      intro n
      rw [hf.dpow_comp (n := n) a ha]
      exact Ideal.mem_map_of_mem _ (dpow_mem_pdP γ n ha)
    | zero =>
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [δ.dpow_zero J.zero_mem, dividedPowerFiltration_zero, Ideal.map_top]; exact Submodule.mem_top
      · rw [δ.dpow_eval_zero hn.ne']; exact Ideal.zero_mem _
    | add y z hy hz ihy ihz =>
      intro n
      have hyJ : y ∈ J := hJ ▸ hy
      have hzJ : z ∈ J := hJ ▸ hz
      rw [δ.dpow_add hyJ hzJ]
      refine Ideal.sum_mem _ fun k hk => ?_
      have hk' : k.1 + k.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hk
      have := Ideal.mul_mem_mul (ihy hyJ k.1) (ihz hzJ k.2)
      rw [← Ideal.map_mul] at this
      rw [← hk']
      exact Ideal.map_mono (dividedPowerFiltration_mul γ k.1 k.2) this
    | smul c y hy ihy =>
      intro n
      have hyJ : y ∈ J := hJ ▸ hy
      rw [smul_eq_mul, δ.dpow_mul hyJ]
      exact Ideal.mul_mem_left _ _ (ihy hyJ n)
  refine Ideal.span_le.2 ?_
  rintro _ ⟨L, hL, hr, rfl⟩
  refine Ideal.map_mono (dividedPowerFiltration_anti γ hr) ?_
  clear hr
  induction L with
  | nil => simp [dividedPowerFiltration_zero, Ideal.map_top]
  | cons q L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have h1 := key q.2 (hL q (by simp)) q.1
    have h2 := ih (fun q' hq' => hL q' (by simp [hq']))
    have := Ideal.mul_mem_mul h1 h2
    rw [← Ideal.map_mul] at this
    exact Ideal.map_mono (dividedPowerFiltration_mul γ _ _) this

end CrystallineSemistableComparison.Pb.Kap.DividedPowerIdealFacts

namespace CrystallineSemistableComparison.Pb.Kap

namespace CgEmpty

variable {O' : Type} [CommRing O'] {R' : Type} [CommRing R'] {I' : Ideal R'}

theorem thick_sub {γ : DividedPowers I'} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O')} {κ : O' →+* R' ⧸ I'}
    (hX : IsEmpty X) (T : Thick (nlFun γ 0 X q κ)) : Subsingleton T.B := by
  have h1 : Subsingleton (T.B ⧸ T.J) := by
    by_contra hn
    rw [not_subsingleton_iff_nontrivial] at hn
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (T.B ⧸ T.J)
    exact hX.elim ((pt T).base ⟨M, hM.isPrime⟩)
  have hJ : T.J = ⊤ := Ideal.Quotient.subsingleton_iff.1 h1
  obtain ⟨n, hn⟩ := T.adm.2 rfl
  rw [hJ, Ideal.top_pow] at hn
  have h2 : (1 : T.B) ∈ (⊤ : Ideal T.B) := Submodule.mem_top
  rw [hn] at h2
  exact subsingleton_of_zero_eq_one ((Submodule.mem_bot _).1 h2).symm

theorem HO_sub {γ : DividedPowers I'} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O')} {κ : O' →+* R' ⧸ I'}
    (hX : IsEmpty X) (Q : ObjectProperty (Thick (nlFun γ 0 X q κ))) (j : ℕ) : Subsingleton (HO Q j) := by
  have hc : Subsingleton (CH.Cn (CH.modF (sP Q).A) j) :=
    ⟨fun f g => funext fun s => @Subsingleton.elim _ (thick_sub hX (s.obj (Fin.last j)).obj) (f s) (g s)⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  congr 1
  exact Subtype.ext (hc.elim _ _)

theorem HdR_sub {K' : Type} [CommRing K'] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K')) (hX : IsEmpty X) (j : ℕ) :
    Subsingleton (HdR q j) := by
  have hc : Subsingleton (GlobalTheory.CatH.Cn (O (smFun X q)) j) :=
    ⟨fun f g => funext fun s => @Subsingleton.elim _ (thick_sub hX (s.obj (Fin.last j))) (f s) (g s)⟩
  refine ⟨fun x y => ?_⟩
  unfold HdR at x y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  congr 1
  exact Subtype.ext (hc.elim _ _)

end CgEmpty

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {m : ℕ}

theorem cg_basis_pdP {L : Lev R m} (hL : L.Good) : pdP L.γB m = ⊥ := by
  have h := DividedPowerIdealFacts.dividedPowerFiltration_le_map L.γ L.γB L.ι hL.ι_dp hL.IB_eq m
  rw [(hL.lat m le_rfl).tf.nil, Ideal.map_bot] at h
  exact le_bot_iff.1 h

theorem cg_basis_empty {L : Lev R m} (hL : L.Good) (M : Model l K) (hM : M.Sm) (s : ℕ) (U : Cov M.q)
    (hU0 : IsEmpty U.ι) (j : ℕ) {a : ℕ} (bs : Module.Basis (Fin a) K (HdR M.q j)) (w : HO (QB L M s) j) :
    ∃! g : Fin a → L.B, w = ∑ t, g t • muB L.γB M.q 1 s {⊤} j (bs t) := by
  have hX : IsEmpty M.gen := by
    have h := U.cover
    rw [iSup_of_empty] at h
    refine ⟨fun x => ?_⟩
    have hx : x ∈ (⊤ : M.gen.Opens) := trivial
    rw [← h] at hx
    simp at hx
  haveI := CgEmpty.HO_sub hX (QB L M s) j
  haveI := CgEmpty.HdR_sub M.q hX j
  have ha : a = 0 := by
    by_contra h
    exact bs.ne_zero ⟨0, Nat.pos_of_ne_zero h⟩ (Subsingleton.elim _ _)
  subst ha
  exact ⟨Fin.elim0, Subsingleton.elim _ _, fun g _ => funext fun t => t.elim0⟩

theorem cg_basis_pf {L : Lev R m} (hL : L.Good) (M : Model l K) (hM : M.Sm) (s : ℕ) (U : Cov M.q) (hU : ∀ α, U.d α + m ≤ s)
    (j : ℕ) {a : ℕ} (bs : Module.Basis (Fin a) K (HdR M.q j)) (w : HO (QB L M s) j) :
    ∃! g : Fin a → L.B, w = ∑ t, g t • muB L.γB M.q 1 s {⊤} j (bs t) := by
  rcases isEmpty_or_nonempty U.ι with h0 | h1
  · exact cg_basis_empty hL M hM s U h0 j bs w
  · obtain ⟨α⟩ := h1
    have hms : m ≤ s := le_trans (Nat.le_add_left _ _) (hU α)
    exact (basisB L.γB s m (cg_basis_pdP hL) hms M.q U hU {⊤} sSup_singleton j bs).1 w

end CrystallineSemistableComparison.Pb.Kap

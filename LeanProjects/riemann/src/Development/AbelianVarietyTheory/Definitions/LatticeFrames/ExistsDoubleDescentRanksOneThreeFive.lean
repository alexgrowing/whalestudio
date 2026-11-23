import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubleStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasis
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbXMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonarchimedeanLocalFieldSecondCountableT2Space
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharacters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCOPrXCgrp

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel
open GlobalTheory.PosOne (toOne Covers)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl.Model

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def sph (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n]
    [DecidableEq n] : Level (GL n k) := ⟨KO k n, 1⟩

omit [MeasurableSpace k] [BorelSpace k] in
theorem isCO_sph : IsCO (sph k n).J := ⟨SplitFlip.isOpen_KO, SplitFlip.isCompact_KO⟩

abbrev ind (k : Type) [Field k] [ValuativeRel k] (n n' : Type) : Matrix n n' k → ℂ :=
  Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1

omit [MeasurableSpace k] [BorelSpace k] in
theorem om_ind {μ : kˣ →* ℂˣ} (hμ : IsUnram μ) {g : GL n' k} {h : GL n k} (hg : g ∈ KO k n') (hh : h ∈ KO k n) :
    om μ g h (ind k n n') = ind k n n' := by
  funext x
  have a := valuation_det_of_mem_KO hg
  have b := valuation_det_of_mem_KO hh
  have e : IntM ((h⁻¹).val * x * g.val) ↔ IntM x := by
    refine ⟨fun H => ?_, fun H => ((mem_KO.1 hh).2.mul H).mul (mem_KO.1 hg).1⟩
    have := ((mem_KO.1 hh).1.mul H).mul (mem_KO.1 hg).2
    rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one] at this
  simp only [om, hμ _ a, hμ _ b, nabs_eq_one_of_valuation_eq_one a, nabs_eq_one_of_valuation_eq_one b, Real.one_rpow]
  simp only [Units.val_one, inv_one, Complex.ofReal_one, one_mul, ind]
  by_cases H : IntM x
  · rw [Set.indicator_of_mem (by exact e.2 H), Set.indicator_of_mem (by exact H)]
  · rw [Set.indicator_of_notMem (by exact fun H' => H (e.1 H')), Set.indicator_of_notMem (by exact H)]

omit [MeasurableSpace k] [BorelSpace k] in
theorem hasTypes_ind {μ : kˣ →* ℂˣ} (hμ : IsUnram μ) : HasTypes μ (sph k n') (sph k n) (ind k n n') :=
  ⟨fun g => (om_ind hμ g.2 (one_mem _)).trans (one_smul ℂ _).symm,
    fun h => (om_ind hμ (one_mem _) h.2).trans (by rw [show (sph k n).lam h = 1 from rfl, inv_one, Units.val_one, one_smul])⟩

theorem covers_ind {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) (μ : kˣ →* ℂˣ) :
    Covers 1 (KO k (n ⊕ Fin (c + 1))) {1} fun h => GlobalTheory.StepData.flat ψ ν μ (ind k (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1))) 1 h := by
  refine ⟨by simp, fun h h0 => ⟨1, by simp, ?_⟩⟩
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  obtain ⟨r, hr, w, hw, rfl⟩ := (Unram.opE_unramified k n n' (c + 1) 1 le_rfl (by omega) ψ hψ ν hν μ _ rfl).1 h x hx
  exact ((DoubleCoset.eq _ _ _ _).2 ⟨r, hr, w, hw, by simp⟩).symm

theorem xi_ind {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) (μ : kˣ →* ℂˣ) :
    xi ψ ν μ (ind k (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1))) (KO k _) 1 1 1 = ind k n n' := by
  haveI := hν.1
  have v : volNat ν (1 : GL (n ⊕ Fin (c + 1)) k) (Cgrp (KO k _) 1) = 1 := by
    rw [← volNat_stabLat ν (1 : GL (n ⊕ Fin (c + 1)) k)]
    unfold volNat
    congr 3
    ext u
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_Cgrp, stabLat]
    have hu : u.1 ∈ R k n (c + 1) 1 := Subgroup.mem_sup_right u.2
    simp [hu]
  funext x
  rw [xi, v, GlobalTheory.StepData.flat, om_one,
    (Unram.opE_unramified k n n' (c + 1) 1 le_rfl (by omega) ψ hψ ν hν μ (ind k _ _) rfl).2.1]
  simp only [inv_one, Complex.ofReal_one, one_mul]
  rfl

theorem isOneComb_one (ψ : AddChar k Circle) (ν : Measure k) (L : Level (GL (n ⊕ Fin c) k)) (β : GL (n ⊕ Fin c) k) :
    IsOneComb ψ ν 1 L β (Finsupp.single β 1) := fun A _ _ σ _ l _ v _ => by
  simp [GlobalTheory.PosOne.comb, GlobalTheory.PosOne.toOne_one]

theorem isOneComb_two {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) (hc : 1 < c) :
    IsOneComb ψ ν 2 (sph k (n ⊕ Fin c)) 1 (Finsupp.single 1 1) := fun A _ _ σ hσ l hl v hv => by
  haveI := hν.1
  obtain ⟨_, _⟩ := GlobalTheory.RootExchangeFixed.nonarchimedeanLocalField_secondCountable_t2Space (k := k)
  have hK : ∀ g ∈ KO k (n ⊕ Fin c), σ g v = v := fun g hg => (hv ⟨g, hg⟩).trans (one_smul ℂ v)
  have key := ((ExchangeSupport.exchange_support k n c 1 le_rfl hc ψ hψ.continuous hψ.ne_one ν A σ hσ l v).2 hl).2
  let S : Set (n → k) := Set.univ.pi fun _ => (𝒪[k] : Set k)
  have hS : MeasurableSet S := MeasurableSet.univ_pi fun _ => (Valuation.isOpen_integer).measurableSet
  have hf : (fun β : n → k => l (σ (colE c (1 + 1) β) v)) = S.indicator fun _ => l v := by
    funext β
    by_cases h : β ∈ S
    · rw [Set.indicator_of_mem h, hK]
      refine GlobalTheory.RootExchangeFixed.upU_mem_KO _ fun r i => ?_
      rw [Matrix.of_apply]
      split_ifs
      · exact h r trivial
      · simp
    · rw [Set.indicator_of_notMem h]
      simp only [S, Set.mem_pi, Set.mem_univ, true_imp_iff, not_forall] at h
      obtain ⟨r, hr⟩ := h
      have hx : ¬ valuation k (β r) ≤ valuation k ((1 : kˣ) : k) := by rw [Units.val_one, map_one]; exact hr
      have h0 : 0 < valuation k (β r) := lt_of_le_of_lt zero_le (not_le.1 hx)
      have hb : β r ≠ 0 := by rintro h; simp [h] at h0
      rw [← hψ] at hx
      push Not at hx
      obtain ⟨y, hy, hy1⟩ := hx
      have := key (Pi.single r (-(y / β r))) β
      rw [hK (rowE c 1 _) (GlobalTheory.RootExchangeFixed.lowU_mem_KO _ fun l s => ?_), single_dotProduct, neg_mul, neg_neg,
        div_mul_cancel₀ _ hb] at this
      · by_contra hne
        exact hy1 (Circle.ext (by simpa using (mul_right_cancel₀ hne (this.symm.trans (one_mul _).symm))))
      · rw [Matrix.of_apply]
        split_ifs
        · by_cases e : s = r
          · subst e
            rw [Pi.single_eq_same, Valuation.map_neg, map_div₀, div_le_iff₀ h0, one_mul]
            exact hy
          · simp [Pi.single_eq_of_ne e]
        · simp
  rw [GlobalTheory.PosOne.toOne_succ, GlobalTheory.PosOne.toOne_one, map_one, Module.End.one_apply, exDown, zero_add, hf,
    integral_indicator_const _ hS, Measure.real, Measure.pi_pi]
  simp [GlobalTheory.PosOne.comb, hν.2]

theorem exists_haar (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] :
    ∃ m : Measure (GL n k), m.IsHaarMeasure ∧ m (KO k n) = 1 := by
  obtain ⟨h0, _, _, h1, h2, -⟩ := volGL_haar k n ν
  haveI : BorelSpace (GL n k) := h0
  haveI := (GlobalTheory.RootExchangeFixed.nonarchimedeanLocalField_secondCountable_t2Space (k := k)).2
  let K : TopologicalSpace.PositiveCompacts (GL n k) := ⟨⟨KO k n, h1⟩, by rw [h2.interior_eq]; exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩

omit [MeasurableSpace k] [BorelSpace k] in
theorem isOpen_ker {μ : kˣ →* ℂˣ} (hμ : IsUnram μ) : IsOpen (μ.ker : Set kˣ) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (x := Units.val ⁻¹' ((· - 1) ⁻¹' {x : k | valuation k x < 1}))
    (IsOpen.mem_nhds (IsOpen.preimage Units.continuous_val (IsOpen.preimage (by fun_prop) ?_)) (by simp)) fun x hx => ?_)
  · simpa using (valuation k).isOpen_ball 1
  · exact DblInhab.isTame_of_isUnram hμ x hx

end Local

variable {D : D7}

theorem exists_doubleDescent_of_parity {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {σ : ℕ} (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1))
    (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (h₁ : B.A.rank % 2 = J.W₀.rank % 2) (h₂ : J.W₀.rank % 2 = B'.A.rank % 2) :
    ∃ S : Dbl2 ψ σ, S.B = B ∧ S.J = J ∧ S.B' = B' := by
  obtain ⟨χ, a1, a2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D J.W₀.rank
  obtain ⟨η, b1, b2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D 1
  have c1 : IsHeckeChar D (χ * η) := ⟨a1.1.mul b1.1, fun x => by rw [MonoidHom.mul_apply, a1.2, b1.2, mul_one]⟩
  have c2 := resEta_mul a2 b2
  have r1 := B.o.rank_add
  have r2 := B.line.1
  have r3 := B'.o.rank_add
  have r4 := B'.line.1
  have p1 := Inhab.even_im_hermitian_sub B.d
  have p2 := Inhab.even_im_hermitian_sub J.d
  have p3 := Inhab.even_im_hermitian_sub B'.d
  obtain ⟨o₁, w₁⟩ := Inhab.exists_weil hψ B.V J.W c1 a1 (resEta_parity c2 (by omega)) (resEta_parity a2 (by omega))
  obtain ⟨o₁', w₁'⟩ := Inhab.exists_weil hψ B.V₀ J.W₀ c1 a1 (resEta_parity c2 (by omega)) a2
  obtain ⟨o₂, w₂⟩ := Inhab.exists_weil hψ J.W B'.V a1 c1 (resEta_parity a2 (by omega)) (resEta_parity c2 (by omega))
  obtain ⟨o₂', w₂'⟩ := Inhab.exists_weil hψ J.W₀ B'.V₀ a1 c1 a2 (resEta_parity c2 (by omega))
  obtain ⟨oa, wa⟩ := Inhab.exists_weil hψ B.A J.W₀ a1 a1 (resEta_parity a2 (by omega)) a2
  obtain ⟨ob, wb⟩ := Inhab.exists_weil hψ J.W₀ B'.A a1 a1 a2 (resEta_parity a2 (by omega))
  exact ⟨⟨B, J, B', ⟨_, _, o₁, o₁', w₁, w₁', (Inhab.nonempty_vol _).some, (Inhab.nonempty_volM _ _ _).some,
      (Inhab.nonempty_volM _ _ _).some, (Inhab.nonempty_volU _ _).some⟩,
    ⟨_, _, o₂, o₂', w₂, w₂', (Inhab.nonempty_vol _).some, (Inhab.nonempty_volM _ _ _).some,
      (Inhab.nonempty_volM _ _ _).some, (Inhab.nonempty_volU _ _).some⟩, l, (Inhab.nonempty_volM _ _ _).some,
    χ, χ, η, oa, ob, rfl, rfl, rfl, rfl, wa, wb⟩, rfl, rfl, rfl⟩

theorem even_im_hermitian_sub {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} (S : Dbl2 ψ σ) :
    S.B.A.rank % 2 = S.J.W₀.rank % 2 ∧ S.J.W₀.rank % 2 = S.B'.A.rank % 2 := by
  have key : ∀ {χ : (AE D)ˣ →* Circle} {a b : ℕ}, ResEta D χ a → ResEta D χ b → a % 2 = b % 2 := fun {χ a b} ha hb => by
    by_contra h
    rcases Nat.mod_two_eq_zero_or_one a with e | e
    · exact resEta_not_both (resEta_parity ha (by omega)) (resEta_parity hb (by omega))
    · exact resEta_not_both (resEta_parity hb (by omega)) (resEta_parity ha (by omega))
  exact ⟨key S.weila.resS S.weila.resT, key S.weilb.resS S.weilb.resT⟩

theorem exists_doubleDescent_ranks_one_three_five (D : D7) : ∃ (ψ : AddChar (AF D.host.F) ℂ) (S : Dbl2 ψ 0), IsStdChar D ψ (-1) ∧
    S.B.A.rank = 1 ∧ S.J.W₀.rank = 3 ∧ S.B'.A.rank = 5 := by
  obtain ⟨ψ, hψ⟩ := (Inhab.exists_chain D).1
  obtain ⟨B, J, B', r₀, r₁, r₂, ⟨l⟩⟩ := DblInhab.exists_levels D
  obtain ⟨S, rfl, rfl, rfl⟩ := exists_doubleDescent_of_parity hψ B J B' l (by omega) (by omega)
  exact ⟨ψ, S, hψ, r₀.symm, r₁.symm, r₂.symm⟩

def IsSph {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) : Prop :=
  IsOne Q.Φ₁ ∧ IsOne Q.Φ₂ ∧ Q.A₁ = {1} ∧ Q.A₂ = {1} ∧ Q.volJ = 1 ∧ Q.e₀ = Finsupp.single 1 1 ∧
    (∃ f₁ f₂, Q.Vac f₁ f₂ ∧ f₁ ≠ 0 ∧ f₂ ≠ 0) ∧ Q.Typed fun _ => 1

theorem exists_gl {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) :
    ∃ gl : GL Y k →* GA D V, ∀ g, (ofSplit q).IsLoc F (gl g) g :=
  let ⟨gl, h1, h2⟩ := GlobalTheory.GlEmbed.exists_gl D k q V Y F.β F.γ F.βγ F.γβ
  ⟨gl, fun g => ⟨h1 g, h2 g⟩⟩

set_option maxHeartbeats 1000000 in

theorem exists_qstep_at {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S : Dbl2 ψ 0) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {ψk : AddChar k Circle}
    (hk : (ofSplit q).IsChar ψ ψk) (hc : HasConductor ψk 1) {μ₁ μ₂ : kˣ →* ℂˣ} (c₁ : (ofSplit q).IsComp S.χ₁⁻¹ μ₁)
    (c₂ : (ofSplit q).IsComp S.χ₂⁻¹ μ₂) (u₁ : IsUnram μ₁) (u₂ : IsUnram μ₂) : ∃ Q : QStep S, Q.q.v = q.v ∧ IsSph Q := by
  borelize k
  obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.exists_isUnitVol (k := k)
  haveI := hν.1
  obtain ⟨F, -⟩ := PinModel.exists_dbl (σ := 0) (ofSplit q) S.B S.J S.B' _ _ _ one_ne_zero (Frame.ofGL 1) (Frame.ofGL 1) (Frame.ofGL 1)
  obtain ⟨gl₀, l₀⟩ := exists_gl q _ F.G₀
  obtain ⟨gl₁, l₁⟩ := exists_gl q _ F.G₁
  obtain ⟨gl₂, l₂⟩ := exists_gl q _ F.G₂
  obtain ⟨Φ₁, h₁, z₁⟩ := PinModel.exists_isOne (k := k) (Y := Fin S.J.W₀.rank ⊕ Fin (0 + 1 + 1)) (Y' := Fin S.B.A.rank ⊕ Fin (0 + 1 + 1 + 1))
  obtain ⟨Φ₂, h₂, z₂⟩ := PinModel.exists_isOne (k := k) (Y := Fin S.B'.A.rank ⊕ Fin (0 + 1)) (Y' := Fin S.J.W₀.rank ⊕ Fin (0 + 1 + 1))
  have e₁ : Φ₁.1 = ind k _ _ := h₁
  have e₂ : Φ₂.1 = ind k _ _ := h₂
  obtain ⟨m₁, a₁, b₁⟩ := exists_haar ν (Fin S.J.W₀.rank)
  obtain ⟨m₂, a₂, b₂⟩ := exists_haar ν (Fin S.B'.A.rank)
  obtain ⟨T₁, t₁, i₁⟩ := Exist.exists_injective_model D k (ofSplit q) ψ hψ _ _ _ _ F.G₀ F.G₁
  obtain ⟨T₂, t₂, i₂⟩ := Exist.exists_injective_model D k (ofSplit q) ψ hψ _ _ _ _ F.G₁ F.G₂
  refine ⟨{ k := k, ν := ν, unitVol := hν, q := q, ψk := ψk, char := hk, cond := hc, c := 0, F := F
            n₀ := Fin S.B.A.rank, n₁ := Fin S.J.W₀.rank, n₂ := Fin S.B'.A.rank
            gl₀ := gl₀, gl₁ := gl₁, gl₂ := gl₂, loc₀ := l₀, loc₁ := l₁, loc₂ := l₂, μ₁ := μ₁, μ₂ := μ₂, comp₁ := c₁, comp₂ := c₂
            open₁ := isOpen_ker u₁, open₂ := isOpen_ker u₂, L₀ := sph k _, L₁ := sph k _, L₂ := sph k _
            co₁ := isCO_sph, co₂ := isCO_sph
            le₁ := le_rfl, le₂ := le_rfl, Φ₁ := Φ₁, Φ₂ := Φ₂
            ty₁ := e₁ ▸ hasTypes_ind u₁, ty₂ := e₂ ▸ hasTypes_ind u₂
            D₁ := Finsupp.single 0 1, D₂ := Finsupp.single 0 1
            dat₁ := e₁ ▸ PinModel.isCombAt_one _ ψ _ _, dat₂ := e₂ ▸ PinModel.isCombAt_one _ ψ _ _
            α := 1, A₁ := {1}, A₂ := {1}
            cov₁ := e₁ ▸ covers_ind hc hν μ₁
            cov₂ := fun γ hγ => by rw [Finset.mem_singleton.1 hγ, e₂]; exact covers_ind hc hν μ₂
            d₁ := fun _ => Finsupp.single 0 1, d₂ := fun _ _ => Finsupp.single 0 1
            ent₁ := fun γ => by
              rw [Finset.mem_singleton.1 γ.2, e₁]
              exact (congrArg _ (xi_ind (c := 1) hc hν μ₁)).mpr (PinModel.isCombAt_one _ ψ F.F₀ F.F₁)
            ent₂ := fun γ β => by
              rw [Finset.mem_singleton.1 γ.2, Finset.mem_singleton.1 β.2, e₂]
              exact (congrArg _ (xi_ind (c := 0) hc hν μ₂)).mpr (PinModel.isCombAt_one _ ψ F.F₁ F.F₂)
            e₀ := Finsupp.single 1 1, e₂ := fun β => Finsupp.single β.1 1
            one₀ := isOneComb_two hc hν (by omega), one₂ := fun β => isOneComb_one _ _ _ _
            m₁ := m₁, m₂ := m₂, haar₁ := a₁, haar₂ := a₂, vol₁ := b₁, vol₂ := b₂ }, rfl, h₁, h₂, rfl, rfl, ?_, rfl,
    ⟨T₁ Φ₁, T₂ Φ₂, ⟨⟨T₁, Φ₁, t₁, h₁, rfl⟩, T₂, Φ₂, t₂, h₂, rfl⟩, fun h => ?_, fun h => ?_⟩, fun j => ?_⟩
  · simp [QStep.volJ, sph]
  · rw [i₁ (h.trans (map_zero T₁).symm)] at z₁
    exact zero_ne_one z₁
  · rw [i₂ (h.trans (map_zero T₂).symm)] at z₂
    exact zero_ne_one z₂
  · exact (one_smul ℂ (fun _ => (1 : ℂ))).symm

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem infinite_qstep {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S : Dbl2 ψ 0) :
    {v | ∃ Q : QStep S, Q.q.v = v ∧ IsSph Q}.Infinite := by
  have hev := (GlobalTheory.T.standard_character_conductor_almost_all D ψ hψ).and ((GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0).and
    ((GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0⁻¹).and
      ((DblInhab.eventually_isUnram D S.χ₁⁻¹ S.weila.hecS.1.inv).and (DblInhab.eventually_isUnram D S.χ₂⁻¹ S.weilb.hecS.1.inv))))
  refine Filter.frequently_cofinite_iff_infinite.1
    (((Filter.frequently_cofinite_iff_infinite.2 (GlobalTheory.T.infinitely_many_split_places D)).and_eventually hev).mono ?_)
  rintro v ⟨⟨e, ε, he, hε, hs⟩, a1, a2, a3, a4, a5⟩
  obtain ⟨q, -, hq⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε he hε hs
  obtain ⟨⟨ψk, hk⟩, -, -, -, hc⟩ := GlobalTheory.LocChar.weil_char_split D _ (ofSplit q) ψ hψ
  obtain ⟨μ₁, c₁⟩ := hc S.χ₁⁻¹
  obtain ⟨μ₂, c₂⟩ := hc S.χ₂⁻¹
  rw [← hq]
  exact exists_qstep_at hψ S q hk (DblInhab.hasConductor q (by rw [hq]; exact a1) (by rw [hq]; exact a2) (by rw [hq]; exact a3) hk)
    c₁ c₂ (a4 _ q hq _ c₁) (a5 _ q hq _ c₂)

theorem exists_family (D : D7) (r : ℕ) : ∃ (ψ : AddChar (AF D.host.F) ℂ) (S : Dbl2 ψ 0) (Q : Fin r → QStep S), IsStdChar D ψ (-1) ∧
    S.B.A.rank = 1 ∧ S.J.W₀.rank = 3 ∧ S.B'.A.rank = 5 ∧ Function.Injective (fun i => (Q i).q.v) ∧ ∀ i, IsSph (Q i) := by
  obtain ⟨ψ, S, hψ, r₀, r₁, r₂⟩ := exists_doubleDescent_ranks_one_three_five D
  let e := (infinite_qstep hψ S).natEmbedding
  choose Q hQ hS using fun i : Fin r => (e i).2
  refine ⟨ψ, S, Q, hψ, r₀, r₁, r₂, fun i j h => ?_, hS⟩
  exact Fin.ext (e.injective (Subtype.ext ((hQ i).symm.trans (h.trans (hQ j)))))

theorem volJ_ne_zero {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) : Q.volJ ≠ 0 := by
  have key : ∀ {Y : Type} [Fintype Y] [DecidableEq Y] (J : Subgroup (GL Y Q.k)), IsOpen (J : Set (GL Y Q.k)) →
      J.relIndex (KO Q.k Y) ≠ 0 := fun {Y} _ _ J hJ => by
    haveI : CompactSpace (KO Q.k Y) := isCompact_iff_compactSpace.1 SplitFlip.isCompact_KO
    haveI := Subgroup.quotient_finite_of_isOpen (J.subgroupOf (KO Q.k Y)) (hJ.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite
  exact inv_ne_zero (mul_ne_zero (Nat.cast_ne_zero.2 (key _ Q.co₁.1)) (Nat.cast_ne_zero.2 (key _ Q.co₂.1)))

theorem w_ne_zero {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) (γ : Q.A₁) (β : Q.A₂) :
    Q.w₁ γ ≠ 0 ∧ Q.w₂ β ≠ 0 := by
  have key : ∀ {Y : Type} [Fintype Y] [DecidableEq Y] (m : Measure (GL Y Q.k)), m.IsHaarMeasure → ∀ C : Subgroup (GL Y Q.k),
      IsCO C → (((m C).toReal⁻¹ : ℝ) : ℂ) ≠ 0 := fun {Y} _ _ m hm C hC =>
    Complex.ofReal_ne_zero.2 (inv_ne_zero (ENNReal.toReal_ne_zero.2
      ⟨hC.1.measure_ne_zero m ⟨1, C.one_mem⟩, hC.2.measure_lt_top.ne⟩))
  exact ⟨key _ Q.haar₁ _ (GlobalTheory.PrCompactOpen.isCO_prX_Cgrp _ _ _ _ Q.co₁ _).1,
    key _ Q.haar₂ _ (GlobalTheory.PrCompactOpen.isCO_prX_Cgrp _ _ _ _ Q.co₂ _).1⟩

theorem c_eq {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) : Q.c = 2 * σ := by
  have := Q.F.bes.1
  omega

example {G : Type} [Monoid G] (e : G →₀ ℂ) (g h : G) (a b : ℂ) :
    conv [e] = e ∧ conv [Finsupp.single g a, Finsupp.single h b] = Finsupp.single (g * h) (a * b) := by
  simp [conv, -Finsupp.single_mul]

example {G : Type} [AddMonoid G] (e : G →₀ ℂ) (g h : G) (a b : ℂ) :
    aconv [e] = e ∧ aconv [Finsupp.single g a, Finsupp.single h b] = Finsupp.single (g + h) (a * b) := by
  simp [aconv, -Finsupp.single_mul]

end GlobalTheory.QPl.Model
end

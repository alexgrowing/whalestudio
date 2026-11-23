import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInjectiveModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InfinitelyManySplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardCharacterConductorAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOffStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSymmetricPositionLevel

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel
open GlobalTheory.LocMod Filter
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.DblInhab

theorem exists_dbl : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (n₀ n₁ n₂ : Type)
    [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]
    (F₀ : GlobalTheory.LocMod.Frame k B.A.rank n₀) (F₁ : GlobalTheory.LocMod.Frame k J.W₀.rank n₁) (F₂ : GlobalTheory.LocMod.Frame k B'.A.rank n₂) (s : k),
    s ≠ 0 → ∃ F : Dbl p B J B' n₀ n₁ n₂ (2 * σ), F.s = s ∧ F.F₀ = F₀ ∧ F.F₁ = F₁ ∧ F.F₂ = F₂ := by
  intro D k _ _ _ _ p σ B J B' n₀ n₁ n₂ _ _ _ _ _ _ F₀ F₁ F₂ s hs
  have hx := GlobalTheory.LocChar.xi_ne p
  obtain ⟨-, ⟨G₀, h₀⟩, hz⟩ := (Exist.exists_frames D k p n₀ (σ + 1) s hs).1 B F₀
  obtain ⟨G₁, h₁⟩ := (Exist.exists_frames D k p n₁ (σ + 1) s hs).2 J _ hz F₁
  obtain ⟨-, ⟨G₂, h₂⟩, -⟩ := (Exist.exists_frames D k p n₂ σ (s * p.xi) (mul_ne_zero hs hx)).1 B' F₂
  exact ⟨⟨s, hs, F₀, F₁, F₂, G₀, G₁, G₂, h₀, h₁, h₂⟩, rfl, rfl, rfl, rfl⟩

section Gram

variable (E : Type) [Field E] [CharZero E] [StarRing E]

theorem five_gram (e e' : Matrix (Fin 5) (Fin 1) E) (i : Matrix (Fin 5) (Fin 3) E) (he : e = !![0; 0; 0; 1; 1])
    (he' : e' = !![0; 0; 0; 1 / 2; -(1 / 2)]) (hi : i = !![1, 0, 0; 0, 1, 0; 0, 0, 1; 0, 0, 0; 0, 0, 0]) :
    eᴴ * sgnM E ![false, false, false, false, true] * e = 0 ∧ e'ᴴ * sgnM E ![false, false, false, false, true] * e' = 0 ∧
    e'ᴴ * sgnM E ![false, false, false, false, true] * e = 1 ∧
    iᴴ * sgnM E ![false, false, false, false, true] * i = sgnM E (fun _ => false) ∧
    iᴴ * sgnM E ![false, false, false, false, true] * e = 0 ∧ iᴴ * sgnM E ![false, false, false, false, true] * e' = 0 := by
  subst he he' hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext a b <;> rw [Matrix.mul_apply] <;>
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply] <;> fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_five, Examples₂.sgn] <;> norm_num

omit [CharZero E] in
theorem sub_gram {N a b : ℕ} (M : Matrix (Fin N) (Fin N) E) (f : Fin a → Fin N) (g : Fin b → Fin N) :
    ((1 : Matrix (Fin N) (Fin N) E).submatrix id f)ᴴ * M * (1 : Matrix (Fin N) (Fin N) E).submatrix id g = M.submatrix f g := by
  have h := Matrix.submatrix_mul (1 : Matrix (Fin N) (Fin N) E) M f id id Function.bijective_id
  rw [Matrix.submatrix_id_id] at h
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one, ← h, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
    Matrix.one_mul, Matrix.mul_one]

omit [CharZero E] in
theorem last_gram (N : ℕ) (a : Matrix (Fin (N + 1)) (Fin N) E) (b : Matrix (Fin (N + 1)) (Fin 1) E)
    (ha : a = (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) E).submatrix id Fin.castSucc)
    (hb : b = (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) E).submatrix id fun _ => Fin.last N) :
    aᴴ * sgnM E (fun i => decide (i = Fin.last N)) * a = sgnM E (fun _ => false) ∧
    bᴴ * sgnM E (fun i => decide (i = Fin.last N)) * b = sgnM E ![true] ∧
    bᴴ * sgnM E (fun i => decide (i = Fin.last N)) * a = 0 := by
  subst ha hb
  refine ⟨?_, ?_, ?_⟩ <;> rw [sub_gram] <;> ext i j
  · simp [Matrix.diagonal_apply, Fin.castSucc_ne_last]
  · rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp
  · simp [Matrix.diagonal_apply, (Fin.castSucc_ne_last j).symm]

end Gram

abbrev posSp (D : D7) (N : ℕ) : HSp D := diagSp D N (fun _ => false) N 0

theorem coCpt_posSp (D : D7) (N : ℕ) : CoCpt (posSp D N) := by
  refine GlobalTheory.Unf.Inhab.coCpt_of_posDef fun τ => ?_
  have h : gramAt D (posSp D N) τ = 1 := by
    rw [gramAt, diagSp_gram]
    exact Matrix.map_one _ (map_zero (tauE D τ)) (map_one (tauE D τ))
  rw [h]
  exact Matrix.PosDef.one

def hypFive (D : D7) : HypDec (diagSp D 5 ![false, false, false, false, true] 4 1) (posSp D 3) 1 where
  e := (!![0; 0; 0; 1; 1] : Matrix (Fin 5) (Fin 1) D.host.E)
  e' := (!![0; 0; 0; 1 / 2; -(1 / 2)] : Matrix (Fin 5) (Fin 1) D.host.E)
  i₀ := (!![1, 0, 0; 0, 1, 0; 0, 0, 1; 0, 0, 0; 0, 0, 0] : Matrix (Fin 5) (Fin 3) D.host.E)
  ee := gram_check _ _ _ (five_gram D.host.E _ _ _ rfl rfl rfl).1
  e'e' := gram_check _ _ _ (five_gram D.host.E _ _ _ rfl rfl rfl).2.1
  e'e := gram_check _ _ _ (five_gram D.host.E _ _ _ rfl rfl rfl).2.2.1
  iso := (gram_check _ _ _ (five_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.1).trans (diagSp_gram 3 _ 3 0).symm
  i₀e := gram_check _ _ _ (five_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.2.1
  i₀e' := gram_check _ _ _ (five_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.2.2
  rank_add := rfl

def orthLast (D : D7) (N : ℕ) :
    OrthDec (diagSp D (N + 1) (fun i => decide (i = Fin.last N)) N 1) (posSp D N) (GlobalTheory.Unf.Inhab.negLine D) where
  iA := ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) D.host.E).submatrix id Fin.castSucc : Matrix (Fin (N + 1)) (Fin N) D.host.E)
  iB := ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) D.host.E).submatrix id fun _ => Fin.last N :
    Matrix (Fin (N + 1)) (Fin 1) D.host.E)
  isoA := (gram_check _ _ _ (last_gram D.host.E N _ _ rfl rfl).1).trans (diagSp_gram N _ N 0).symm
  isoB := (gram_check _ _ _ (last_gram D.host.E N _ _ rfl rfl).2.1).trans (diagSp_gram 1 _ 0 1).symm
  orth := gram_check _ _ _ (last_gram D.host.E N _ _ rfl rfl).2.2
  rank_add := rfl

open GlobalTheory.Unf.Inhab in

theorem exists_levels (D : D7) : ∃ (B : BesLev D (0 + 1)) (J : JacLev D (0 + 1)) (B' : BesLev D 0),
    1 = B.A.rank ∧ 3 = J.W₀.rank ∧ 5 = B'.A.rank ∧ Nonempty (Link B B'.L B'.ζ) := by
  let B : BesLev D 1 := besPlane (GlobalTheory.RegSW.Model.hypFour D) (cmHost_imaginaryGenerator_ne_zero D)
  let J : JacLev D 1 := ⟨_, _, hypFive D, coCpt_posSp D 3, (nonempty_vol _).some, (nonempty_volN _).some⟩
  let B' : BesLev D 0 := ⟨_, _, _, _, hypRefl _, orthLast D 5, fun _ => 1, isLineVec_negLine one_ne_zero, coCpt_posSp D 5,
    (nonempty_vol _).some, (nonempty_volN _).some⟩
  have e : D.host.xi0⁻¹ • B.ζ = B'.ζ := funext fun _ => inv_mul_cancel₀ (cmHost_imaginaryGenerator_ne_zero D)
  have l : Link B B.L B'.ζ := e ▸ selfLink B
  exact ⟨B, J, B', rfl, rfl, rfl, ⟨l⟩⟩

section Place

open GlobalTheory.FinPl (SplitPt Pl idAt intAt)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem sec_one : q.sec 1 = q.e := GlobalTheory.LocChar.ι_one (ofSplit q)

theorem sec_mul_pr (a : k) (o : AE D) : q.sec (a * q.pr o) = q.sec a * o := by
  have h := q.sec_pr (q.sec a * o)
  rw [map_mul, q.pr_sec] at h
  rw [h, ← mul_assoc]
  exact congrArg (· * o) (GlobalTheory.LocChar.e_mul_ι (ofSplit q) a)

theorem sec_mem_idAt (a : k) : q.sec a ∈ idAt D (· = q.v) := by
  obtain ⟨ε, hε, hsum⟩ := q.above
  obtain ⟨hee, hec, -⟩ := q.split
  have he : q.e ∈ idAt D (· = q.v) := by
    refine ((GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D q.v ε hε).1 q.e).2 ?_
    rw [← hsum, add_mul, hee, mul_comm (cA D q.e), hec, add_zero]
  have h : q.e * q.sec a = q.sec a := GlobalTheory.LocChar.e_mul_ι (ofSplit q) a
  rw [← h]
  exact Ideal.mul_mem_right _ _ he

theorem sec_mem_intAt (a : k) : q.sec a ∈ intAt D (· = q.v) ↔ valuation k a ≤ 1 :=
  (and_iff_right (sec_mem_idAt q a)).trans (q.int_iff a).symm

theorem pr_le_one {o : AE D} (ho : o ∈ intAt D (· = q.v)) : valuation k (q.pr o) ≤ 1 := by
  refine (q.int_iff _).2 ?_
  rw [q.sec_pr, ← sec_one, map_mul]
  exact GlobalTheory.HostAdeleIso.intAE_mul_mem D ((q.int_iff 1).1 (one_mem _)) ho.2

theorem hasConductor {ψ : AddChar (AF D.host.F) ℂ}
    (hc : ∀ s ∈ idAt D (· = q.v), (∀ o ∈ intAt D (· = q.v), psiE ψ (s * o) = 1) ↔ s ∈ intAt D (· = q.v))
    (h1 : ∀ a ∈ intAt D (· = q.v), incA D D.host.xi0 * a ∈ intAt D (· = q.v))
    (h2 : ∀ a ∈ intAt D (· = q.v), incA D D.host.xi0⁻¹ * a ∈ intAt D (· = q.v))
    {ψk : AddChar k Circle} (hk : (ofSplit q).IsChar ψ ψk) : HasConductor ψk 1 := by
  have hk' : ∀ x, (ψk x : ℂ) = psiE ψ (incA D D.host.xi0 * q.sec x) := hk
  intro x
  rw [Units.val_one, map_one]
  refine ⟨fun h => ?_, fun h y hy => Circle.ext ?_⟩
  · have hs := (hc _ (Ideal.mul_mem_left _ (incA D D.host.xi0) (sec_mem_idAt q x))).1 fun o ho => by
      rw [mul_assoc, ← sec_mul_pr, ← hk', h _ (by rw [map_mul]; exact mul_le_of_le_one_right' (pr_le_one q ho)), Circle.coe_one]
    have := h2 _ hs
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D), map_one, one_mul] at this
    exact (sec_mem_intAt q x).1 this
  · have hs := h1 _ ((sec_mem_intAt q y).2 (hy.trans h))
    have := (hc _ hs.1).2 hs _ ((sec_mem_intAt q 1).2 (map_one _).le)
    rw [mul_assoc, ← sec_mul_pr, q.pr_sec, mul_one] at this
    rw [hk', this, Circle.coe_one]

end Place

theorem eventually_isUnram (D : D7) (χ : (AE D)ˣ →* Circle) (hχ : Continuous χ) : ∀ᶠ v : GlobalTheory.FinPl.Pl D in cofinite,
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k),
      q.v = v → ∀ μ, (ofSplit q).IsComp χ μ → IsUnram μ := by
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D χ hχ
  filter_upwards [GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (N : D.host.E)⁻¹] with v hv k _ _ _ _ q hq μ hμ x hx
  subst hq
  have key : ∀ y : k, valuation k y ≤ 1 → infPart D (q.sec y + (1 - q.e)) = 1 ∧ finPart D (q.sec y + (1 - q.e)) ∈ intAE D ∧
      ∃ z ∈ intAE D, finPart D (q.sec y + (1 - q.e)) - 1 = N • z := fun y hy => by
    have hy' := (sec_mem_intAt q (y - 1)).2 ((Valuation.map_sub _ _ _).trans (max_le hy (map_one _).le))
    have e : q.sec y + (1 - q.e) = q.sec (y - 1) + 1 := by rw [map_sub, sec_one]; ring
    have hi : infPart D (q.sec (y - 1)) = 0 := hy'.1.1
    rw [e, RingHom.map_add, RingHom.map_add, RingHom.map_one, RingHom.map_one, hi, zero_add, add_sub_cancel_right]
    refine ⟨rfl, add_mem hy'.2 (GlobalTheory.HeckeConj.one_mem_intAE D), _, (hv _ hy').2, ?_⟩
    have e' : q.sec (y - 1) = N • (incA D (N : D.host.E)⁻¹ * q.sec (y - 1)) := by
      rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (incA D), ← RingHom.map_mul,
        mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), RingHom.map_one, one_mul]
    exact (congrArg (finPart D) e').trans ((finPart D).toAddMonoidHom.map_nsmul _ _)
  have hx' : valuation k ((x⁻¹ : kˣ) : k) ≤ 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  have h1 : χ (GlobalTheory.LocChar.unitsHom (ofSplit q) x) = 1 :=
    hker _ ⟨(key _ hx.le).1, (key _ hx.le).2.1, (key _ hx').2.1⟩ (key _ hx.le).2.2
  have h2 := hμ x (GlobalTheory.LocChar.unitsHom (ofSplit q) x) rfl
  rw [h1, Circle.coe_one] at h2
  exact Units.ext h2

theorem isTame_of_isUnram {k : Type} [Field k] [ValuativeRel k] {μ : kˣ →* ℂˣ} (h : IsUnram μ) : IsTame μ := fun x hx =>
  h x (by simpa using Valuation.map_one_add_of_lt (valuation k) hx)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem exists_good_place (D : D7) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (χ₁ χ₂ : (AE D)ˣ →* Circle)
    (h₁ : Continuous χ₁) (h₂ : Continuous χ₂) : ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k)
      (_ : IsNonarchimedeanLocalField k) (p : Place D k) (ψk : AddChar k Circle) (μ₁ μ₂ : kˣ →* ℂˣ),
      p.IsChar ψ ψk ∧ HasConductor ψk 1 ∧ p.IsComp χ₁ μ₁ ∧ IsUnram μ₁ ∧ p.IsComp χ₂ μ₂ ∧ IsUnram μ₂ := by
  have hev := (GlobalTheory.T.standard_character_conductor_almost_all D ψ hψ).and ((GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0).and
    ((GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0⁻¹).and
      ((eventually_isUnram D χ₁ h₁).and (eventually_isUnram D χ₂ h₂))))
  obtain ⟨v, ⟨e, ε, he, hε, hs⟩, a1, a2, a3, a4, a5⟩ := ((Filter.frequently_cofinite_iff_infinite.2 (GlobalTheory.T.infinitely_many_split_places D)).and_eventually hev).exists
  obtain ⟨q, -, hq⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε he hε hs
  obtain ⟨⟨ψk, hk⟩, -, -, -, hc⟩ := GlobalTheory.LocChar.weil_char_split D _ (ofSplit q) ψ hψ
  obtain ⟨μ₁, c₁⟩ := hc χ₁
  obtain ⟨μ₂, c₂⟩ := hc χ₂
  exact ⟨_, _, _, _, _, ofSplit q, ψk, μ₁, μ₂, hk, hasConductor q (by rw [hq]; exact a1) (by rw [hq]; exact a2)
    (by rw [hq]; exact a3) hk, c₁, a4 _ q hq _ c₁, c₂,
    a5 _ q hq _ c₂⟩

end GlobalTheory.LocMod.DblInhab

end

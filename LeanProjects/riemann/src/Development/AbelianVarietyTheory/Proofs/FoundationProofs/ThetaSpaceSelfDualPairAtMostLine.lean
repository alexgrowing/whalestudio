import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrtStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferentStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianPairingRationalValuesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionSelfDualExistsEqSmulStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaLine

variable {D : D7} {N N' : ℕ}

def sq (z w : VC D N N') : ℂ := ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)

theorem Hf_eq (T : Tor D) (z w : VC D N N') : Hf D T z w = sq z w / (area T.abelian₂ : ℂ) := rfl

theorem im_Hf (T : Tor D) (z w : VC D N N') : (Hf D T z w).im = (sq z w).im / area T.abelian₂ := by
  rw [Hf_eq, Complex.div_ofReal_im]

theorem sq_smul_left (c : ℂ) (z w : VC D N N') : sq (c • z) w = c * sq z w := by
  simp [sq, Finset.mul_sum, mul_assoc]

theorem sq_smul_right (c : ℂ) (z w : VC D N N') : sq z (c • w) = sq z w * (starRingEnd ℂ) c := by
  simp only [sq, Finset.sum_mul, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem sq_add_left (z z' w : VC D N N') : sq (z + z') w = sq z w + sq z' w := by
  simp [sq, add_mul, Finset.sum_add_distrib]

theorem sq_add_right (z w w' : VC D N N') : sq z (w + w') = sq z w + sq z w' := by
  simp [sq, mul_add, Finset.sum_add_distrib]

theorem sq_neg_left (z w : VC D N N') : sq (-z) w = -sq z w := by simp [sq]

theorem sq_neg_right (z w : VC D N N') : sq z (-w) = -sq z w := by simp [sq]

theorem sq_zero_left (w : VC D N N') : sq 0 w = 0 := by simp [sq]

theorem sq_zero_right (w : VC D N N') : sq w 0 = 0 := by simp [sq]

theorem sq_self_im (z : VC D N N') : (sq z z).im = 0 := by
  simp [sq, Complex.im_sum, Complex.mul_conj]

theorem continuous_sq (w : VC D N N') : Continuous fun z : VC D N N' => sq z w := by
  unfold sq; fun_prop

variable (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)

theorem embV_apply (x : Matrix (Fin N') (Fin N) D.host.E) (τ i j) :
    embV D (tor0 D cc δ) x τ i j = embT D τ (x i j) := rfl

theorem sq_embV (hG : admG1 D) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    sq (embV D (tor0 D cc δ) x) (embV D (tor0 D cc δ) y) =
      D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) := by
  rw [hYY, ← hG.2]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [map_sum, map_mul, embV_apply]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  exact congrArg _ (D.host.conjE_apply (embT D τ) _).symm

theorem embV_smul (hG : admG1 D) (a : D.host.K) (x : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (a • x) = D.host.φ₀ (a : D.host.E) • embV D (tor0 D cc δ) x := by
  funext τ i j
  simp only [embV_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, ← hG.1 τ a, ← map_mul]
  rfl

theorem embV_sum {ι : Type} (s : Finset ι) (x : ι → Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (∑ i ∈ s, x i) = ∑ i ∈ s, embV D (tor0 D cc δ) (x i) := by
  funext τ i j
  simp [embV_apply, Matrix.sum_apply, Finset.sum_apply]

theorem span_embT (D : D7) :
    Submodule.span ℂ (Set.range fun (t : D.host.E) (τ : D.what₂.Tau) => embT D τ t) = ⊤ := by
  have hinj : Function.Injective fun τ : D.what₂.Tau => (embT D τ : D.host.E →* ℂ) := by
    intro τ τ' h
    have h1 : embT D τ = embT D τ' := RingHom.ext fun x => DFunLike.congr_fun h x
    exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h1))
  have hli := (linearIndependent_monoidHom D.host.E ℂ).comp _ hinj
  exact span_flip_eq_top_iff_linearIndependent.2 hli

theorem expand (hG : admG1 D) {r : ℕ} (y y' : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (h : ∀ x, x = ∑ i, hYY D x (y' i) • y i) (z : VC D N N') :
    z = ∑ i, sq z (embV D (tor0 D cc δ) (y' i)) • embV D (tor0 D cc δ) (y i) := by
  let P : Submodule ℂ (VC D N N') :=
    { carrier := {z | z = ∑ i, sq z (embV D (tor0 D cc δ) (y' i)) • embV D (tor0 D cc δ) (y i)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, sq_add_left, add_smul, Finset.sum_add_distrib] at *
        rw [← ha, ← hb]
      zero_mem' := by simp [sq_zero_left]
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, sq_smul_left, mul_smul, ← Finset.smul_sum] at *
        rw [← ha] }
  have hP : ∀ x, embV D (tor0 D cc δ) x ∈ P := fun x => by
    change _ = _
    conv_lhs => rw [h x]
    simp only [embV_sum, embV_smul cc δ hG, sq_embV cc δ hG]
  have hc : ∀ a b (c : D.what₂.Tau → ℂ),
      (fun τ i j => if a = i ∧ b = j then c τ else 0 : VC D N N') ∈ P := by
    intro a b c
    have hc : c ∈ Submodule.span ℂ
      (Set.range fun (t : D.host.E) (τ : D.what₂.Tau) => embT D τ t) := span_embT D ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      convert hP (Matrix.single a b t) using 1
      funext τ i j
      rw [embV_apply, Matrix.single_apply]
      split_ifs <;> simp
    | zero => convert P.zero_mem using 1; funext τ i j; simp
    | add x x' _ _ hx hx' =>
      convert P.add_mem hx hx' using 1; funext τ i j
      simp only [Pi.add_apply]; split_ifs <;> simp
    | smul t x _ hx =>
      convert P.smul_mem t hx using 1; funext τ i j
      simp only [Pi.smul_apply]; split_ifs <;> simp
  have hz : z = ∑ a, ∑ b, (fun τ i j => if a = i ∧ b = j then z τ a b else 0 : VC D N N') := by
    funext τ i j
    simp [Finset.sum_apply, ite_and]
  change z ∈ P
  rw [hz]
  exact P.sum_mem fun a _ => P.sum_mem fun b _ => hc a b _

theorem lam_mul (a : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ lamOf D cc δ) :
    D.host.φ₀ ((a : D.host.K) : D.host.E) * w ∈ lamOf D cc δ := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
    push_cast [map_mul]
    ring
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem of_dual_families (hG : admG1 D) (hC : Crv D cc δ)
    (S : Set (Matrix (Fin N') (Fin N) D.host.E))
    (hS : ∀ x ∈ S, ∀ y ∈ S, hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range)
    {r : ℕ} (y y' : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hy : ∀ i, y i ∈ S)
    (hy' : ∀ i, y' i ∈ S) (h : ∀ x, x = ∑ i, hYY D x (y' i) • y i) (A : AddSubgroup (VC D N N'))
    (hA : A = AddSubgroup.closure
      {z | ∃ w ∈ lamOf D cc δ, ∃ x ∈ S, z = w • embV D (tor0 D cc δ) x}) :
    (∀ F ∈ ThSp D (tor0 D cc δ) A, ∀ G ∈ ThSp D (tor0 D cc δ) A, G ≠ 0 → ∃ c : ℂ, F = c • G) ∧ (∀ x ∈ A, ∀ F, Wd D (tor0 D cc δ) x F = fun z => al D (tor0 D cc δ) x * U D (tor0 D cc δ) x F z) ∧ (∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m) ∧ (∀ x, (∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m) → x ∈ A) ∧ A.FG ∧ Submodule.span ℝ (A : Set (VC D N N')) = ⊤ ∧ ∀ x ∈ A, ∃ m : ℤ, qH D (tor0 D cc δ) x = m := by
  obtain ⟨L, hL⟩ := GlobalTheory.T.exists_periodPair_idealCurveLattice D cc δ hC
  obtain ⟨hpos, hdual⟩ := GlobalTheory.T.latticeCovolume_pos_and_selfDual L _ hL
  have hLam : (tor0 D cc δ).abelian₂ = lamOf D cc δ := rfl
  have hgen : ∀ w ∈ lamOf D cc δ, ∀ x ∈ S, w • embV D (tor0 D cc δ) x ∈ A := fun w hw x hx =>
    hA ▸ AddSubgroup.subset_closure ⟨w, hw, x, hx, rfl⟩
  have hsq : ∀ z ∈ A, ∀ x ∈ S, sq z (embV D (tor0 D cc δ) x) ∈ lamOf D cc δ := by
    intro z hz x hx
    rw [hA] at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨w, hw, x', hx', rfl⟩ := hz
      obtain ⟨a, ha⟩ := hS x' hx' x hx
      rw [sq_smul_left, sq_embV cc δ hG, ← ha, mul_comm]
      exact lam_mul cc δ a hw
    | zero => rw [sq_zero_left]; exact zero_mem _
    | add a b _ _ ha hb => rw [sq_add_left]; exact add_mem ha hb
    | neg a _ ha => rw [sq_neg_left]; exact neg_mem ha
  have hint : ∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m := by
    intro z hz u hu
    rw [hA] at hu
    simp only [im_Hf, hLam]
    induction hu using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨w, hw, x, hx, rfl⟩ := hu
      rw [sq_smul_right]
      exact (hdual _).1 (hsq z hz x hx) w hw
    | zero => exact ⟨0, by simp [sq_zero_right]⟩
    | add a b _ _ ha hb =>
      obtain ⟨m, hm⟩ := ha
      obtain ⟨n, hn⟩ := hb
      exact ⟨m + n, by rw [sq_add_right, Complex.add_im, add_div, hm, hn, Int.cast_add]⟩
    | neg a _ ha =>
      obtain ⟨m, hm⟩ := ha
      exact ⟨-m, by rw [sq_neg_right, Complex.neg_im, neg_div, hm, Int.cast_neg]⟩
  have hexp := expand cc δ hG y y' h
  have hmem : ∀ z, (∀ i, sq z (embV D (tor0 D cc δ) (y' i)) ∈ lamOf D cc δ) → z ∈ A :=
    fun z hz => by
      rw [hexp z]
      exact sum_mem fun i _ => hgen _ (hz i) _ (hy i)
  have hsd : ∀ x, (∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m) → x ∈ A := fun z hz =>
    hmem z fun i => (hdual _).2 fun w hw => by
      have := hz _ (hgen w hw _ (hy' i))
      rwa [im_Hf, hLam, sq_smul_right] at this
  have hq : ∀ x ∈ A, ∃ m : ℤ, qH D (tor0 D cc δ) x = m := by
    intro x hx
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_integer_map_eq_halfOneAddSqrt D
    have hx' : w0 D • x ∈ A := hmem _ fun i => by
      rw [sq_smul_left, ← ha]
      exact lam_mul cc δ a (hsq x hx _ (hy' i))
    obtain ⟨m, hm⟩ := hint _ hx' x hx
    refine ⟨m, ?_⟩
    rw [← hm, im_Hf, sq_smul_left, qH, Hf_eq, Complex.div_ofReal_re, Complex.mul_im, sq_self_im]
    simp [w0]
    ring
  have hdisc : DiscreteTopology A := by
    haveI : DiscreteTopology L.lattice := inferInstance
    let f : A → Fin r → L.lattice := fun z i =>
      ⟨sq z.1 (embV D (tor0 D cc δ) (y' i)), (hL _).1 (hsq z.1 z.2 _ (hy' i))⟩
    have hf : Continuous f := continuous_pi fun i =>
      Continuous.subtype_mk ((continuous_sq _).comp continuous_subtype_val) _
    refine DiscreteTopology.of_continuous_injective hf fun z u hzu => Subtype.ext ?_
    rw [hexp z.1, hexp u.1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show sq z.1 _ = sq u.1 _ from congrArg Subtype.val (congrFun hzu i)]
  have h1 : L.ω₁ ∈ lamOf D cc δ := (hL _).2 L.ω₁_mem_lattice
  have h2 : L.ω₂ ∈ lamOf D cc δ := (hL _).2 L.ω₂_mem_lattice
  refine ⟨GlobalTheory.T.thetaFunction_selfDual_exists_eq_smul D _ N N' A hpos hdisc fun x => ⟨hint x, hsd x⟩, fun x hx F => ?_, hint, hsd,
    ?_, ?_, hq⟩
  · obtain ⟨m, hm⟩ := hq x hx
    funext z
    have hm' : Real.sqrt D.host.d / 2 * (Hf D (tor0 D cc δ) x x).re = m := hm
    rw [Wd, wdPh, hm, al, hm', round_intCast, ee, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
    congr 2
    push_cast
    ring
  · rw [AddSubgroup.fg_iff]
    refine ⟨Set.range (fun i => L.ω₁ • embV D (tor0 D cc δ) (y i)) ∪
      Set.range (fun i => L.ω₂ • embV D (tor0 D cc δ) (y i)), le_antisymm ?_ fun z hz => ?_,
      (Set.finite_range _).union (Set.finite_range _)⟩
    · rw [AddSubgroup.closure_le]
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact hgen _ h1 _ (hy i)
      · exact hgen _ h2 _ (hy i)
    · rw [hexp z]
      refine sum_mem fun i _ => ?_
      obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 ((hL _).1 (hsq z hz _ (hy' i)))
      rw [← hmn, add_smul, mul_smul, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      refine add_mem (zsmul_mem (AddSubgroup.subset_closure ?_) m)
        (zsmul_mem (AddSubgroup.subset_closure ?_) n)
      exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨i, rfl⟩]
  · rw [eq_top_iff]
    intro z _
    rw [hexp z]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← L.basis.sum_repr (sq z _), Fin.sum_univ_two, add_smul, smul_assoc, smul_assoc,
      L.basis_zero, L.basis_one]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (hgen _ h1 _ (hy i))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (hgen _ h2 _ (hy i))))

theorem hYY_smul (a : D.host.K) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (a • x) y = a * hYY D x y := by
  rw [hYY, hYY, ← smul_eq_mul, ← map_smul]
  simp [Finset.smul_sum]

theorem hYY_add (x x' y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (x + x') y = hYY D x y + hYY D x' y := by
  simp [hYY, add_mul, Finset.sum_add_distrib]

theorem onB_expand {r : ℕ} {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : OnB D b)
    (x : Matrix (Fin N') (Fin N) D.host.E) : x = ∑ i, hYY D x (b i) • b i := by
  have hx : x ∈ Submodule.span D.host.K (Set.range b) := hb.2 ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    simp [hb.1 j, ite_smul]
  | zero => simp [hYY]
  | add x x' _ _ hx hx' =>
    simp only [hYY_add, add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hx']
  | smul a x _ hx =>
    simp only [hYY_smul, mul_smul, ← Finset.smul_sum]
    rw [← hx]

theorem theta_line : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → (∀ F ∈ ThSp D (tor0 D cc δ) A, ∀ G ∈ ThSp D (tor0 D cc δ) A, G ≠ 0 → ∃ c : ℂ, F = c • G) ∧ (∀ x ∈ A, ∀ F, Wd D (tor0 D cc δ) x F = fun z => al D (tor0 D cc δ) x * U D (tor0 D cc δ) x F z) ∧ (∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m) ∧ (∀ x, (∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m) → x ∈ A) ∧ A.FG ∧ Submodule.span ℝ (A : Set (VC D N N')) = ⊤ ∧ ∀ x ∈ A, ∃ m : ℤ, qH D (tor0 D cc δ) x = m := by
  intro D hG cc δ hC N N' A hA
  rcases hA with ⟨r, b, hb, rfl⟩ | ⟨L, L', hL, hL', rfl⟩
  · refine of_dual_families cc δ hG hC (Set.range b) ?_ b b (fun i => ⟨i, rfl⟩)
      (fun i => ⟨i, rfl⟩) (onB_expand hb) _ ?_
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      rw [hb.1 i j]
      split_ifs
      exacts [one_mem _, zero_mem _]
    · unfold LaB
      congr 1
      ext z
      simp [tor0]
  · obtain ⟨r, y, y', hy, hy', h⟩ := GlobalTheory.T.exists_traceDual_family_homLattice D (GlobalTheory.T.exists_traceDual_family_inverseHalfDifferent D) N N' L L' hL hL'
    have hint := GlobalTheory.T.hermitian_pairing_integral_values D N N' L L' hL hL'
    have hA : La D (tor0 D cc δ) L L' = AddSubgroup.closure
        {z | ∃ w ∈ lamOf D cc δ, ∃ x ∈ {x | x ∈ YYl D L L'}, z = w • embV D (tor0 D cc δ) x} := rfl
    exact of_dual_families cc δ hG hC {x | x ∈ YYl D L L'} (fun x hx y hy => hint x hx y hy) y y'
      hy hy' h _ hA

end GlobalTheory.ThetaLine

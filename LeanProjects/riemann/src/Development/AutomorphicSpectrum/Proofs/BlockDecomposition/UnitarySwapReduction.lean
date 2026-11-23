import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryBorelSplitting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdmissibleLinearFunctionalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnitaryRootMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleReflectionRootBorelDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleReflectionMemMaximalCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootMapMemCompactOfIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReflectionRootUnipotentShiftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReflectionRootDiagonalConjStatement

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct Matrix

namespace GlobalTheory.CompanionTheory.SwapRoot

section Lem
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {ϖ : L} {σ : L →+* L} {q : ℕ}

theorem step_exists_int [CompleteSpace L] (hU : IsUnramInv ϖ σ q) (w : ℂ) (hw0 : w ≠ 0) (hw : ‖w‖ * (q : ℝ) ^ 2 < 1) :
    ∃ I : (L → ℂ) → ℂ,
      (∀ F G : L → ℂ, IsAdm w F → IsAdm w G → I (F + G) = I F + I G) ∧
      (∀ (c : ℂ) (F : L → ℂ), IsAdm w F → I (c • F) = c * I F) ∧
      (∀ (F : L → ℂ) (y : L), IsAdm w F → IsAdm w (fun x => F (x + y)) ∧ I (fun x => F (x + y)) = I F) ∧
      (∀ (F : L → ℂ) (c : L), IsAdm w F → c ≠ 0 →
        IsAdm w (fun x => F (c * x)) ∧ I (fun x => F (c * x)) = (q : ℂ) ^ (2 * ordL c) * I F) ∧
      IsAdm w (sphFn (L := L) w) ∧ I (sphFn w) = (1 - w) / (1 - w * (q : ℂ) ^ 2) :=
  GlobalTheory.T.exists_admissible_linear_functional L ϖ σ q hU w hw0 hw

theorem step_uR_continuous (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) :
    Continuous (uR σ hU.1 a h : L → GU σ n) :=
  GlobalTheory.T.continuous_unitary_root_map L ϖ σ q n hU a h

theorem step_factor (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2))
    (hi : i.val = a) (hj : j.val = a + 1) (x : L) (hx : x ≠ 0) :
    ∃ b : GU σ n, IsBorelU b ∧
      chiDeltaU q (fun k => (χ k : ℂ)) b = (((χ i : ℂ) / (χ j : ℂ)) / (q : ℂ) ^ 2) ^ (-ordL x) ∧
      sR σ hU.1 a h * uR σ hU.1 a h x = b * (sR σ hU.1 a h * uR σ hU.1 a h x⁻¹ * sR σ hU.1 a h) :=
  GlobalTheory.T.simple_reflection_root_borel_decomp L ϖ σ q n hU a h χ i j hi hj x hx

theorem step_sR_mem_KU (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) : sR σ hU.1 a h ∈ KU σ n :=
  GlobalTheory.T.simple_reflection_mem_maximal_compact L ϖ σ q n hU a h

theorem step_uR_mem_KU (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : Valued.v x ≤ 1) :
    uR σ hU.1 a h x ∈ KU σ n :=
  GlobalTheory.T.root_map_mem_compact_of_integral L ϖ σ q n hU a h x hx

theorem step_unip_shift (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (v : GU σ n) (hv : IsUnipU v) :
    ∃ y : L, ∀ x : L, ∃ b : GU σ n, IsUnipU b ∧
      sR σ hσ a h * uR σ hσ a h x * v = b * (sR σ hσ a h * uR σ hσ a h (x + y)) :=
  GlobalTheory.T.reflection_root_unipotent_shift L σ n hσ a h v hv

theorem step_torus_shift (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2))
    (hi : i.val = a) (hj : j.val = a + 1) (t : GU σ n) (ht : IsDiagM (t : GL (Fin n) L)) :
    ∃ c : L, c ≠ 0 ∧ ∃ t' : GU σ n, IsBorelU t' ∧
      (∀ x : L, sR σ hU.1 a h * uR σ hU.1 a h x * t = t' * (sR σ hU.1 a h * uR σ hU.1 a h (c * x))) ∧
      chiDeltaU q (fun k => (χ k : ℂ)) t' * (q : ℂ) ^ (2 * ordL c) =
        chiDeltaU q (fun k => ((χ ∘ Equiv.swap i j) k : ℂ)) t :=
  GlobalTheory.T.reflection_root_diagonal_conj L ϖ σ q n hU a h χ i j hi hj t ht

end Lem

section Main
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {ϖ : L} {σ : L →+* L} {q : ℕ}

theorem step_borel_shift (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2))
    (hi : i.val = a) (hj : j.val = a + 1) (b : GU σ n) (hb : IsBorelU b) :
    ∃ (c y : L) (C : ℂ), c ≠ 0 ∧
      (∀ x : L, ∃ b' : GU σ n, IsBorelU b' ∧ chiDeltaU q (fun k => (χ k : ℂ)) b' = C ∧
        sR σ hU.1 a h * uR σ hU.1 a h x * b = b' * (sR σ hU.1 a h * uR σ hU.1 a h (c * x + y))) ∧
      C * (q : ℂ) ^ (2 * ordL c) = chiDeltaU q (fun k => ((χ ∘ Equiv.swap i j) k : ℂ)) b := by
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (show q ≠ 0 by omega)
  obtain ⟨t, v, ht, hv, rfl⟩ := GlobalTheory.CompanionTheory.BorelSplit.borelSplitU L σ n hU.1 b hb
  have hv' : IsUnipU v := ⟨fun p r hpr => hv.1 p r hpr, hv.2⟩
  obtain ⟨y, hy⟩ := step_unip_shift hU.1 a h v hv'
  obtain ⟨c, hc, t', ht', h1, h2⟩ := step_torus_shift hU a h χ i j hi hj t ht
  have ht2 : IsBorelU t := fun p r hpr => ht p r (ne_of_gt hpr)
  refine ⟨c, y, chiDeltaU q (fun k => (χ k : ℂ)) t', hc, fun x => ?_, ?_⟩
  · obtain ⟨b0, hb0, e⟩ := hy (c * x)
    refine ⟨t' * b0, borel_mul _ _ ht' hb0.1, ?_, ?_⟩
    · rw [chi_borel_mul hq χ _ _ ht' hb0.1, chi_unip _ _ hb0, mul_one]
    · rw [← mul_assoc, h1 x, mul_assoc, mul_assoc, ← mul_assoc _ _ v, e, mul_assoc]
  · rw [h2, chi_borel_mul hq (χ ∘ Equiv.swap i j) t v ht2 hv'.1, chi_unip _ v hv', mul_one]

theorem step_stab_adm (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2))
    (hi : i.val = a) (hj : j.val = a + 1) (φ : GU σ n → ℂ) (hφ : φ ∈ psSpaceU σ q χ) (S : Set (GU σ n)) (hS : IsOpen S)
    (h1 : (1 : GU σ n) ∈ S) (hinv : ∀ s ∈ S, ∀ g, φ (g * s) = φ g) (g : GU σ n) :
    IsAdm (((χ i : ℂ) / (χ j : ℂ)) / (q : ℂ) ^ 2) (fun x => φ (sR σ hU.1 a h * uR σ hU.1 a h x * g)) := by
  have hc := step_uR_continuous (L := L) (n := n) hU a h
  set s := sR σ hU.1 a h
  set u : L → GU σ n := uR σ hU.1 a h
  have hu0 : u 0 = 1 := by
    have := uR_add σ hU.1 a h (0 : L) 0
    simpa using this
  have hss : s * s = 1 := sR_mul_sR σ hU.1 a h
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hA : Continuous fun y : L => g⁻¹ * u (y - x) * g := by fun_prop
    have hA1 : (fun y : L => g⁻¹ * u (y - x) * g) x = 1 := by simp [hu0]
    have : ∀ᶠ y in nhds x, g⁻¹ * u (y - x) * g ∈ S :=
      hA.continuousAt.eventually_mem (hS.mem_nhds (by have h2 := h1; rw [← hA1] at h2; exact h2))
    filter_upwards [this] with y hy
    have e : s * u y * g = s * u x * g * (g⁻¹ * u (y - x) * g) := by
      have : u y = u x * u (y - x) := by
        rw [← uR_add]; congr 1; ring
      rw [this]; group
    rw [e, hinv _ hy]
  · have hB : Continuous fun y : L => g⁻¹ * (s * u y * s) * g := by fun_prop
    have hB1 : (fun y : L => g⁻¹ * (s * u y * s) * g) 0 = 1 := by
      simp [hu0, hss]
    have hB2 : (fun y : L => g⁻¹ * (s * u y * s) * g) ⁻¹' S ∈ nhds (0 : L) :=
      hB.continuousAt.preimage_mem_nhds (hS.mem_nhds (by have h2 := h1; rw [← hB1] at h2; exact h2))
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hB2
    have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
    set c := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc'
    refine ⟨WithZero.log c - 1, φ g, fun x hx hR => ?_⟩
    have hv : Valued.v x⁻¹ < c := by
      rw [v_eq_exp' (inv_ne_zero hx), ordL_inv' hx, neg_neg, ← WithZero.exp_log hne]
      exact WithZero.exp_lt_exp.2 (by omega)
    have hmem : g⁻¹ * (s * u x⁻¹ * s) * g ∈ S :=
      hγ (by simpa [Valuation.restrict_lt_iff_lt_embedding, sub_zero] using hv)
    obtain ⟨b, hb, hbc, e⟩ := step_factor hU a h χ i j hi hj x hx
    have e1 : s * u x * g = b * (g * (g⁻¹ * (s * u x⁻¹ * s) * g)) := by
      have : s * u x = b * (s * u x⁻¹ * s) := e
      rw [this]; group
    show φ (s * u x * g) = _
    rw [e1, hφ b _ hb, hinv _ hmem, hbc, mul_comm]

end Main

theorem swapStepU : PositivityTheory.SphericalProduct.SwapStepU := by
  intro L _ _ _ ϖ σ q n hU V _ _ ρ hadm hirr hsph χ i j hij hz f hinj hf
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hqr : (0 : ℝ) < (q : ℝ) ^ 2 := by
    have : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    positivity
  have hj2 := j.2
  have h : 2 * (i.val + 2) ≤ n := by omega
  set w : ℂ := ((χ i : ℂ) / (χ j : ℂ)) / (q : ℂ) ^ 2 with hwdef
  have hw0 : w ≠ 0 := div_ne_zero (div_ne_zero (χ i).ne_zero (χ j).ne_zero) (pow_ne_zero _ hq)
  have hw : ‖w‖ * (q : ℝ) ^ 2 < 1 := by
    rw [hwdef, norm_div, norm_pow, Complex.norm_natCast, div_mul_cancel₀ _ hqr.ne']
    exact hz
  obtain ⟨I, Iadd, Ismul, Itr, Isc, Isph, Ival⟩ := step_exists_int (L := L) hU w hw0 hw
  set s := sR σ hU.1 i.val h with hs
  set u : L → GU σ n := uR σ hU.1 i.val h with hu
  have hr : ∀ (k : GU σ n) (v : V) (g' : GU σ n), (f (ρ k v)).1 g' = (f v).1 (g' * k) := fun k v g' => by
    rw [hf]; rfl
  have hAdm : ∀ (v : V) (g : GU σ n), IsAdm w (fun x => (f v).1 (s * u x * g)) := fun v g =>
    step_stab_adm hU i.val h χ i j rfl hij.symm (f v).1 (f v).2 {k | ρ k v = v} (hadm.1 v) (by simp)
      (fun k hk g' => by rw [← hr, show ρ k v = v from hk]) g
  let T : V → (GU σ n → ℂ) := fun v g => I (fun x => (f v).1 (s * u x * g))
  have Tmem : ∀ v, T v ∈ psSpaceU σ q (χ ∘ Equiv.swap i j) := by
    intro v b g hb
    obtain ⟨c, y, C, hc, hrel, hC⟩ := step_borel_shift hU i.val h χ i j rfl hij.symm b hb
    have hF := hAdm v g
    have hG := (Itr _ y hF).1
    have hH := (Isc _ c hG hc).1
    have e : (fun x => (f v).1 (s * u x * (b * g))) =
        C • (fun x => (fun x' => (fun x'' => (f v).1 (s * u x'' * g)) (x' + y)) (c * x)) := by
      funext x
      obtain ⟨b', hb', hb'C, hx⟩ := hrel x
      have e2 := (f v).2 b' (s * u (c * x + y) * g) hb'
      show (f v).1 (s * u x * (b * g)) = C * (f v).1 (s * u (c * x + y) * g)
      have e3 : s * u x * b = b' * (s * u (c * x + y)) := hx
      rw [← mul_assoc, e3, mul_assoc, ← hb'C]
      exact e2
    show I (fun x => (f v).1 (s * u x * (b * g))) = _ * I (fun x => (f v).1 (s * u x * g))
    rw [e, Ismul C _ hH, (Isc _ c hG hc).2, (Itr _ y hF).2, ← hC]
    ring
  let f' : V →ₗ[ℂ] psSpaceU σ q (χ ∘ Equiv.swap i j) :=
    { toFun := fun v => ⟨T v, Tmem v⟩
      map_add' := fun v v' => by
        refine Subtype.ext (funext fun g => ?_)
        show I (fun x => (f (v + v')).1 (s * u x * g)) = I _ + I _
        rw [← Iadd _ _ (hAdm v g) (hAdm v' g)]
        congr 1
        funext x
        simp [map_add]
      map_smul' := fun c v => by
        refine Subtype.ext (funext fun g => ?_)
        show I (fun x => (f (c • v)).1 (s * u x * g)) = c * I _
        rw [← Ismul c _ (hAdm v g)]
        congr 1
        funext x
        simp [map_smul] }
  have hf' : ∀ (g : GU σ n) (v : V), f' (ρ g v) = psFunU σ q (χ ∘ Equiv.swap i j) g (f' v) := by
    intro g v
    refine Subtype.ext (funext fun g' => ?_)
    show I (fun x => (f (ρ g v)).1 (s * u x * g')) = I (fun x => (f v).1 (s * u x * (g' * g)))
    congr 1
    funext x
    rw [hr, mul_assoc]
  refine ⟨f', ?_, hf'⟩

  obtain ⟨v₀, hv₀, hv₀0⟩ := (Submodule.ne_bot_iff _).1 hsph
  have hfix : ∀ k ∈ KU σ n, ρ k v₀ = v₀ := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hv₀ k hk
  have hK : ∀ (g : GU σ n), ∀ k ∈ KU σ n, (f v₀).1 (g * k) = (f v₀).1 g := fun g k hk => by
    rw [← hr, hfix k hk]
  have hone : (f v₀).1 1 ≠ 0 := by
    intro h0
    refine hv₀0 (hinj (Subtype.ext (funext fun g => ?_)))
    obtain ⟨b, k, hb, hk, rfl⟩ := P.fIwasawa_iwasawa σ hU.1 hU.2.1 g
    have e := (f v₀).2 b k hb
    have e2 := hK 1 k hk
    rw [one_mul] at e2
    rw [map_zero]
    show (f v₀).1 (b * k) = 0
    rw [e, e2, h0, mul_zero]
  have hsph' : (fun x => (f v₀).1 (s * u x * 1)) = ((f v₀).1 1) • sphFn w := by
    funext x
    show _ = (f v₀).1 1 * sphFn w x
    rw [mul_one]
    by_cases hx : Valued.v x ≤ 1
    · have hk : s * u x ∈ KU σ n := mul_mem (step_sR_mem_KU hU _ h) (step_uR_mem_KU hU _ h x hx)
      have := hK 1 _ hk
      rw [one_mul] at this
      rw [this, sphFn, if_pos hx, mul_one]
    · have hx0 : x ≠ 0 := fun e => hx (by simp [e])
      obtain ⟨b, hb, hbc, e⟩ := step_factor hU i.val h χ i j rfl hij.symm x hx0
      have hx1 : Valued.v x⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hx))
      have hk : s * u x⁻¹ * s ∈ KU σ n :=
        mul_mem (mul_mem (step_sR_mem_KU hU _ h) (step_uR_mem_KU hU _ h _ hx1)) (step_sR_mem_KU hU _ h)
      have e1 : s * u x = b * (s * u x⁻¹ * s) := e
      have e2 := hK 1 _ hk
      rw [one_mul] at e2
      rw [e1, (f v₀).2 b _ hb, e2, hbc, sphFn, if_neg hx, mul_comm]
  have hne : f' v₀ ≠ 0 := by
    intro h0
    have e : T v₀ 1 = 0 := congrFun (congrArg Subtype.val h0) 1
    have e2 : T v₀ 1 = (f v₀).1 1 * ((1 - w) / (1 - w * (q : ℂ) ^ 2)) := by
      show I (fun x => (f v₀).1 (s * u x * 1)) = _
      rw [hsph', Ismul _ _ Isph, Ival]
    rw [e2] at e
    have hw1 : ‖w‖ < 1 := by
      have h1 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
        nlinarith
      nlinarith [norm_nonneg w]
    have n1 : (1 - w) ≠ 0 := fun e0 => by
      have : w = 1 := by linear_combination -e0
      rw [this] at hw1
      simp at hw1
    have n2 : (1 - w * (q : ℂ) ^ 2) ≠ 0 := fun e0 => by
      have e3 : w * (q : ℂ) ^ 2 = 1 := by linear_combination -e0
      have : ‖w * (q : ℂ) ^ 2‖ = 1 := by rw [e3]; simp
      rw [norm_mul, norm_pow, Complex.norm_natCast] at this
      linarith
    exact mul_ne_zero hone (div_ne_zero n1 n2) e
  let F := f'.intertwiningMap_of_isIntertwiningMap ρ (psFunU σ q (χ ∘ Equiv.swap i j)) hf'
  haveI := hirr
  rcases Representation.IsIrreducible.injective_or_eq_zero F with hi | hz
  · exact hi
  · exact absurd (DFunLike.congr_fun hz v₀) hne

end GlobalTheory.CompanionTheory.SwapRoot

end

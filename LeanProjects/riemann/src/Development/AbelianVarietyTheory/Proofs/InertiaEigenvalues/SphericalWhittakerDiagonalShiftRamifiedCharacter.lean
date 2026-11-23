import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CondExpEqZeroOfNotMem
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerEqZeroOfNotAntitoneStatement

noncomputable section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun

namespace GlobalTheory.JSW.ShiftWhit
open GlobalTheory.IwaCell
variable {k : Type} [Field k] {n : ℕ}

theorem val_tD' (ϖ : kˣ) (a : Fin n → ℤ) : (tD ϖ a).val = Matrix.diagonal fun i => ((ϖ ^ a i : kˣ) : k) :=
  GlobalTheory.SmGL.val_diagT k _

theorem conj_tD_apply (ϖ : kˣ) (c : Fin n → ℤ) (u : GL (Fin n) k) (i j : Fin n) :
    ((tD ϖ c * u * tD ϖ (-c) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      ((ϖ ^ c i : kˣ) : k) * (u : Matrix (Fin n) (Fin n) k) i j * ((ϖ ^ (-c) j : kˣ) : k) := by
  rw [Units.val_mul, Units.val_mul, val_tD', val_tD', Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem tD_eq_diagPow (ϖ : kˣ) (ν : Fin n → ℤ) (h : ∀ i, 0 ≤ ν i) :
    tD ϖ ν = GlobalTheory.JSW.diagPow ϖ (fun i => (ν i).toNat) := by
  have e : (fun i => ((ϖ ^ ν i : kˣ) : k)) = fun i => ((ϖ ^ (ν i).toNat : kˣ) : k) :=
    funext fun i => by rw [← zpow_natCast, Int.toNat_of_nonneg (h i)]
  ext i j
  rw [val_tD', e]
  rfl

theorem commute_tD_const (ϖ : kˣ) (c : ℤ) (x : GL (Fin n) k) : Commute (tD ϖ (fun _ : Fin n => c)) x := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, val_tD']
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

theorem conj_mem_unipB (ϖ : kˣ) (c : Fin n → ℤ) {u : GL (Fin n) k} (hu : u ∈ GlobalTheory.SmGL.unipB k (Fin n)) :
    tD ϖ c * u * tD ϖ (-c) ∈ GlobalTheory.SmGL.unipB k (Fin n) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB k).1 hu
  refine (GlobalTheory.SmGL.mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [conj_tD_apply, h1 i j hij, mul_zero, zero_mul]
  · rw [conj_tD_apply, h2 i, mul_one, ← Units.val_mul, Pi.neg_apply, ← _root_.zpow_add, add_neg_cancel, zpow_zero, Units.val_one]

theorem superDiag_conj (ϖ : kˣ) (e : ℤ) (m : ℕ) (u : GL (Fin (m + 1)) k) :
    GlobalTheory.Whittaker.superDiag (tD ϖ (fun i : Fin (m + 1) => e * ((m : ℤ) - ((i : ℕ) : ℤ))) * u *
      tD ϖ (-(fun i : Fin (m + 1) => e * ((m : ℤ) - ((i : ℕ) : ℤ))))) =
      ((ϖ ^ e : kˣ) : k) * GlobalTheory.Whittaker.superDiag u := by
  rw [GlobalTheory.Whittaker.superDiag, GlobalTheory.Whittaker.superDiag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : (j : ℕ) = (i : ℕ) + 1 := (Finset.mem_filter.1 hj).2
  rw [conj_tD_apply]
  have hz : (ϖ ^ (e * ((m : ℤ) - ((i : ℕ) : ℤ))) : kˣ) * ϖ ^ ((-(fun i : Fin (m + 1) => e * ((m : ℤ) - ((i : ℕ) : ℤ)))) j) = ϖ ^ e := by
    rw [← _root_.zpow_add]
    congr 1
    simp only [Pi.neg_apply, hj']
    push_cast
    ring
  rw [← hz, Units.val_mul]
  ring

end GlobalTheory.JSW.ShiftWhit

namespace GlobalTheory.JSW.ShiftWhit
open GlobalTheory.IwaCell GlobalTheory.JSW GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.MultiplicityOne GlobalTheory.PRep
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def psiScaled (w : HeightOneSpectrum (𝓞 E)) (c : w.adicCompletion E) : AddChar (w.adicCompletion E) ℂ :=
  (psiLocChar w).compAddMonoidHom (AddMonoidHom.mulLeft c)

theorem psiScaled_apply (w : HeightOneSpectrum (𝓞 E)) (c x : w.adicCompletion E) :
    psiScaled w c x = psiLoc w (c * x) := rfl

theorem main_of_fixed (m : ℕ) (π : CuspSub E (m + 1)) (w : HeightOneSpectrum (𝓞 E))
    (α : Fin (m + 1) → ℂˣ) (hα : HasSatGL w (π.locRep w) (Finset.univ.val.map α))
    (φ : π.V) (hφ : φ ∈ fixed (π.locRep w) (KGL w (m + 1)))
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (e : ℤ)
    (hc : GlobalTheory.RamShift.CondOne w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E))
    (g : GA E (m + 1)) (hg : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1)
    (ν : Fin (m + 1) → ℤ) (hν : 0 ≤ ν (Fin.last m)) :
    whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)) + ν i)))) =
      GlobalTheory.RSCell.sphZ (qV E w) (fun i => (α i : ℂ)) ν *
        whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)))))) := by
  classical
  set c : Fin (m + 1) → ℤ := fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)) with hcdef
  have hsplit : tD ϖ (fun i => c i + ν i) = tD ϖ c * tD ϖ ν := by rw [← tD_add]; rfl
  have hcont : ∀ ψ : π.V, Continuous ψ.1.1 := fun ψ => (π.cusp _ ψ.2).1.continuous
  have hleft : AutomorphicForm.IsLeftInvariant φ.1.1 := fun γ y => by
    rw [show AdelicGLn.diagonal E (m + 1) γ = ratGL E (m + 1) γ from Units.ext (Matrix.ext fun _ _ => rfl)]
    exact (π.cusp _ φ.2).1.left γ y
  let f : π.V →ₗ[ℂ] (GL (Fin (m + 1)) (w.adicCompletion E) → ℂ) :=
    { toFun := fun ψ h => whit ψ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))
      map_add' := fun ψ ψ' => funext fun h => whit_add (hcont ψ) (hcont ψ') _
      map_smul' := fun c ψ => funext fun h => whit_smul c ψ.1.1 _ }
  have hmul : ∀ h k : GL (Fin (m + 1)) (w.adicCompletion E),
      g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * (h * k))) =
        (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h))) * finGL E (m + 1) (locGL E (m + 1) w k) := by
    intro h k
    rw [← mul_assoc (tD ϖ c) h k, map_mul (locGL E (m + 1) w), map_mul (finGL E (m + 1)), mul_assoc]
  have hf : ∀ k (ψ : π.V), f (π.locRep w k ψ) = rightReg ℂ _ ℂ k (f ψ) := by
    intro k ψ
    funext h
    change whit (fun z => ψ.1.1 (z * finGL E (m + 1) (locGL E (m + 1) w k)))
        (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h))) =
      whit ψ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * (h * k))))
    rw [hmul, whit_mul_right ψ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))]

  have hN0 : ∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin (m + 1)), ∀ h : GL (Fin (m + 1)) (w.adicCompletion E),
      whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (u * h))) =
        psiLoc w (GlobalTheory.Whittaker.superDiag u) * whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w h)) := by
    intro u hu h
    rw [map_mul, map_mul, ← mul_assoc, commute_finGL_locGL w hg u, mul_assoc, finGL_locGL_eq_uGL w hu, whit,
      whittaker_uGL_mul (hcont φ) hleft, supSum_sLoc]
    rfl
  have hN : ∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin (m + 1)), ∀ h,
      f φ (u * h) = psiScaled w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E)
        (GlobalTheory.Whittaker.superDiag u) * f φ h := by
    intro u hu h
    change whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * (u * h)))) =
      _ * whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))
    have e1 : tD ϖ c * (u * h) = (tD ϖ c * u * tD ϖ (-c)) * (tD ϖ c * h) := by rw [tD_neg]; group
    rw [e1, hN0 _ (conj_mem_unipB ϖ c hu), psiScaled_apply, hcdef, superDiag_conj]
  have hK : ∀ h, ∀ k ∈ KGL w (m + 1), f φ (h * k) = f φ h := by
    intro h k hk
    change whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * (h * k)))) =
      whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))
    rw [hmul, whit_mul_right φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))]
    congr 1
    funext z
    exact congrArg (fun ψ : π.V => ψ.1.1 z) (GlobalTheory.LGrp.mem_fixed.1 hφ k hk)
  have hψ : ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w,
      psiScaled w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E) (x * y) = 1) ↔ x ∈ Ov E w := by
    intro x
    simp only [psiScaled_apply, ← mul_assoc]
    exact hc x
  have hgoal : f φ (tD ϖ ν) = GlobalTheory.RSCell.sphZ (qV E w) (fun i => (α i : ℂ)) ν * f φ 1 := by
    by_cases h0 : φ = 0
    · subst h0
      have hz : ∀ h, f 0 h = 0 := fun h => by rw [map_zero]; rfl
      rw [hz, hz, mul_zero]
    by_cases hanti : Antitone ν
    · have hpos : ∀ i, 0 ≤ ν i := fun i => hν.trans (hanti (Fin.le_last i))
      have hsat := hα.2 φ hφ h0
      have hmain := GlobalTheory.T.shintani_formula_alt E w (m + 1) _ hψ (f φ) α hN hK ?_ ϖ hϖ (fun i => (ν i).toNat)
      · rw [GlobalTheory.RSCell.sphZ, if_pos hanti, tD_eq_diagPow ϖ ν hpos]
        exact hmain
      · intro ϖ' hϖ' j hj
        rw [← map_heckeVec (Final.GLintComm E w (m + 1)) (Tj_mem_hecke hϖ' j) f hf, hsat.2.2.2 ϖ' hϖ' j hj, map_smul]
    · rw [GlobalTheory.RSCell.sphZ, if_neg hanti, zero_mul]
      set M : ℕ := ∑ i, (ν i).natAbs
      have hM : ∀ i, (ν i).natAbs ≤ M := fun i =>
        Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      set ν' : Fin (m + 1) → ℤ := fun i => ν i + M
      have hpos : ∀ i, 0 ≤ ν' i := fun i => by have := hM i; simp only [ν']; omega
      set z := tD ϖ (fun _ : Fin (m + 1) => -(M : ℤ))
      have hνz : tD ϖ ν = tD ϖ ν' * z := by
        rw [← tD_add]; congr 1; funext i; simp only [ν', Pi.add_apply]; ring
      have hanti' : ¬ Antitone (fun i => (ν' i).toNat) := by
        intro ha
        refine hanti fun i j hij => ?_
        have := ha hij
        have h1 := Int.toNat_of_nonneg (hpos i)
        have h2 := Int.toNat_of_nonneg (hpos j)
        simp only [ν'] at this h1 h2
        omega
      have hz := GlobalTheory.T.whittaker_diagonal_eq_zero_of_not_antitone E w (m + 1) _ hψ (fun h => f φ (h * z))
        (fun u hu h => by simp only [mul_assoc]; exact hN u hu (h * z))
        (fun h k hk => by
          show f φ (h * k * z) = f φ (h * z)
          rw [mul_assoc, ← (commute_tD_const ϖ _ k).eq, ← mul_assoc, hK _ k hk])
        ϖ hϖ (fun i => (ν' i).toNat) hanti'
      rw [hνz, tD_eq_diagPow ϖ ν' hpos]
      exact hz
  have e2 := hgoal
  change whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * tD ϖ ν))) = _ *
    whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * 1))) at e2
  rw [mul_one, ← hsplit] at e2
  exact e2

end GlobalTheory.JSW.ShiftWhit

namespace GlobalTheory.JSW

theorem whit_mul_locGL_tD_shift : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π : CuspSub E (m + 1)) (w : HeightOneSpectrum (𝓞 E)) (α : Fin (m + 1) → ℂˣ), HasSatGL w (π.locRep w) (Finset.univ.val.map α) → ∀ φ ∈ π.V, (∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ e : ℤ, GlobalTheory.RamShift.CondOne w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E) → ∀ g : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1 → ∀ ν : Fin (m + 1) → ℤ, 0 ≤ ν (Fin.last m) → GlobalTheory.JSW.whit φ.1 (g * finGL E (m + 1) (locGL E (m + 1) w (GlobalTheory.IwaCell.tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)) + ν i)))) = GlobalTheory.RSCell.sphZ (qV E w) (fun i => (α i : ℂ)) ν * GlobalTheory.JSW.whit φ.1 (g * finGL E (m + 1) (locGL E (m + 1) w (GlobalTheory.IwaCell.tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)))))) := by
  intro E _ _ _ m π w α hα φ hφV hφ ϖ hϖ e hc g hg ν hν
  exact GlobalTheory.JSW.ShiftWhit.main_of_fixed m π w α hα ⟨φ, hφV⟩
    (GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (hφ k hk)) ϖ hϖ e hc g hg ν hν

end GlobalTheory.JSW

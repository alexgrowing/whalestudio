import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UopSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.HkReps
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.HkComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.MemParahoricTimesPrincipalCongruenceIff
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.DeterminantRepresentatives

variable {F : Type} [Field F] [NumberField F]

theorem norm_one' {w : Pl F} {x : w.adicCompletion F} (h : Valued.v x = 1) : ‖x‖ = 1 := by
  have := (Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le
  have h2 := (Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge
  exact le_antisymm this h2

theorem fin_supp (y : (Af F)ˣ) : Function.HasFiniteMulSupport fun w : Pl F => ‖pLoc F w (y : Af F)‖ := by
  have h1 := Filter.eventually_cofinite.1 (y : Af F).2
  have h2 := Filter.eventually_cofinite.1 ((y⁻¹ : (Af F)ˣ) : Af F).2
  refine (h1.union h2).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
  have a1 : Valued.v (pLoc F w (y : Af F)) ≤ 1 := hc.1
  have a2 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := hc.2
  have a3 : Valued.v (pLoc F w (y : Af F)) * Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine hw (norm_one' (le_antisymm a1 ?_))
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc F w (y : Af F)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

theorem absF_mul (y z : (Af F)ˣ) : absF (y * z) = absF y * absF z := by
  unfold absF
  rw [← finprod_mul_distrib (fin_supp y) (fin_supp z)]
  simp

theorem aff_mul {R : Type} [CommRing R] (y z : Rˣ) (x t : R) : aff y x * aff z t = aff (y * z) (x + y * t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

@[simp] theorem aff_one {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

theorem det_aff {R : Type} [CommRing R] (y : Rˣ) (x : R) : Matrix.GeneralLinearGroup.det (aff y x) = y := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, aff, Matrix.det_fin_two_of]

theorem det_centralSection {R : Type} [CommRing R] (y : Rˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) y * (aff y 0)⁻¹) = y := by
  rw [map_mul, map_inv, det_aff]
  ext
  simp [pow_two]

theorem pLoc_det (v : Pl F) (g : GF F) : pLoc F v ((Matrix.GeneralLinearGroup.det g : (Af F)ˣ) : Af F) =
    ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (pLoc F v) g) : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
  simp [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]

theorem absF_loc (w : Pl F) (g : GL (Fin 2) (w.adicCompletion F))
    (hg : Matrix.GeneralLinearGroup.det g = atFin w (unif w)) :
    absF (Matrix.GeneralLinearGroup.det (locGL F 2 w g)) = (normV w : ℝ)⁻¹ := by
  rw [absF, finprod_eq_single _ w fun v hv => by rw [pLoc_det, pLoc_locGL_of_ne hv]; simp, pLoc_det, pLoc_locGL, hg,
    FinitePlace.norm_def, unif_spec, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]

  simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [show Multiplicative.toAdd (WithZero.unzero _) = (-1 : ℤ) from rfl, zpow_neg_one]

theorem step {c : Pl F → ℕ} {w : Pl F} {W : List (Pl F)} {ι κ : Type} [Fintype ι] [Fintype κ] {b : ι → GF F}
    (hb : IsReps c W b) (r : κ → GL (Fin 2) (w.adicCompletion F))
    (hr1 : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V),
      ∀ x ∈ Hi.fixd ρ (K1 w (c w)), Uop w ρ (c w) x = ∑ j, ρ (r j) x)
    (hr2 : ∀ j, Matrix.GeneralLinearGroup.det (r j) = atFin w (unif w))
    (hr3 : c w ≠ 0 → ∀ j, ∃ u : w.adicCompletionIntegers F, r j = aff (atFin w (unif w)) (u : w.adicCompletion F)) :
    IsReps c (w :: W) (fun p : κ × ι => locGL F 2 w (r p.1) * b p.2) where
  act V _ _ ρ x hx := by
    obtain ⟨hy, he⟩ := hb.act V ρ x hx
    have hy' : (∑ i, ρ (b i) x) ∈ Hi.fixd (ρ.comp (locGL F 2 w)) (K1 w (c w)) :=
      fun k hk => hy _ ((kcTop F).2.2.2.2.2 c w k hk)
    have hs : ∑ p : κ × ι, ρ (locGL F 2 w (r p.1) * b p.2) x =
        Uop w (ρ.comp (locGL F 2 w)) (c w) (∑ i, ρ (b i) x) := by
      rw [hr1 V (ρ.comp (locGL F 2 w)) _ hy', Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, Module.End.mul_apply]
      rfl
    rw [hs]
    refine ⟨(hkComm (hkReps uopSum) kcTop F V ρ c _ hy w).1, ?_⟩
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ← he]
  det p := by
    rw [map_mul, absF_mul, absF_loc w _ (hr2 p.1), hb.det, List.map_cons, List.prod_cons]
  loc p w' hw' := by
    classical
    obtain ⟨u', hu'⟩ := hb.loc p.2 w' hw'
    rw [map_mul]
    by_cases h : w' = w
    · subst h
      obtain ⟨u, hu⟩ := hr3 hw' p.1
      have hm : ((atFin w' (unif w') : (w'.adicCompletion F)ˣ) : w'.adicCompletion F) ∈ w'.adicCompletionIntegers F := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, unif_spec, ← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
      refine ⟨u + ⟨_, hm⟩ * u', ?_⟩
      rw [pLoc_locGL, hu, hu', aff_mul, List.count_cons_self, pow_succ']
      push_cast
      rfl
    · refine ⟨u', ?_⟩
      rw [pLoc_locGL_of_ne h, one_mul, hu']
      simp [List.count_cons, Ne.symm h]

theorem base (c : Pl F → ℕ) : IsReps c ([] : List (Pl F)) (fun _ : Unit => (1 : GF F)) where
  act V _ _ ρ x hx := by simpa using hx
  det _ := by simp [absF]
  loc _ w _ := ⟨0, by simp⟩

theorem reindex {c : Pl F → ℕ} {W : List (Pl F)} {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι) {a : ι → GF F}
    (h : IsReps c W a) : IsReps c W (a ∘ e) where
  act V _ _ ρ x hx := by
    rw [show ∑ i, ρ ((a ∘ e) i) x = ∑ i, ρ (a i) x from Equiv.sum_comp e (fun i => ρ (a i) x)]
    exact h.act V ρ x hx
  det i := h.det (e i)
  loc i := h.loc (e i)

theorem ex (c : Pl F → ℕ) (W : List (Pl F)) : ∃ (ι : Type) (_ : Fintype ι) (a : ι → GF F), IsReps c W a := by
  induction W with
  | nil => exact ⟨Unit, inferInstance, _, base c⟩
  | cons w W ih =>
    obtain ⟨ι, _, b, hb⟩ := ih
    classical
    haveI := Formalism.UG.P.glint_finite_residueField w
    letI := Fintype.ofFinite (IsLocalRing.ResidueField (w.adicCompletionIntegers F))
    choose s hs using (IsLocalRing.residue_surjective (R := w.adicCompletionIntegers F))
    have hS : Set.BijOn (IsLocalRing.residue (w.adicCompletionIntegers F))
        ((Finset.univ.image s : Finset (w.adicCompletionIntegers F)) : Set (w.adicCompletionIntegers F)) Set.univ := by
      refine ⟨fun _ _ => Set.mem_univ _, ?_, fun r _ => ⟨s r, by simp, hs r⟩⟩
      intro x hx y hy h
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      obtain ⟨r', -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      rw [hs, hs] at h
      rw [h]
    generalize Finset.univ.image s = S at hS
    by_cases hc : c w = 0
    · refine ⟨Option S × ι, inferInstance, _, step hb (fun o => o.elim
        (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w)) * (aff (atFin w (unif w)) 0)⁻¹)
        (fun u => aff (atFin w (unif w)) ((u : w.adicCompletionIntegers F) : w.adicCompletion F))) ?_ ?_ ?_⟩
      · intro V _ _ ρ x hx
        rw [(uopSum F w V ρ (c w) x hx).2 S hS, if_pos hc, Fintype.sum_option, add_comm, ← Finset.sum_coe_sort S]
        rfl
      · intro j
        cases j with
        | none => exact det_centralSection _
        | some u => exact det_aff _ _
      · exact fun h => absurd hc h
    · refine ⟨S × ι, inferInstance, _, step hb (fun u : S => aff (atFin w (unif w))
        ((u : w.adicCompletionIntegers F) : w.adicCompletion F)) ?_ (fun _ => det_aff _ _) (fun _ u => ⟨u, rfl⟩)⟩
      intro V _ _ ρ x hx
      rw [(uopSum F w V ρ (c w) x hx).2 S hS, if_neg hc, add_zero, ← Finset.sum_coe_sort S]

end UpperTheory.Esk.DeterminantRepresentatives

open UpperTheory.Esk.DeterminantRepresentatives in
theorem UpperTheory.Esk.dReps : UpperTheory.Esk.DReps := by
  intro F _ _ c W
  obtain ⟨ι, _, a, ha⟩ := ex c W
  exact ⟨Fintype.card ι, a ∘ (Fintype.equivFin ι).symm, reindex _ ha⟩

import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoeffInfinitePlacesWeightRep
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem rFin_const {a : ℕ} (c : ℂ) : RFin (fun _ : GL (Fin a) ℂ => c) := by
  refine ⟨continuous_const, Submodule.span ℂ {fun _ => (1 : ℂ)}, FiniteDimensional.span_singleton ℂ _, fun y => ?_⟩
  exact Submodule.mem_span_singleton.2 ⟨c, by funext n; simp⟩

private theorem rFin_add {a : ℕ} {p q : GL (Fin a) ℂ → ℂ} (hp : RFin p) (hq : RFin q) :
    RFin (fun h => p h + q h) := by
  obtain ⟨cp, A, fA, mA⟩ := hp
  obtain ⟨cq, B, fB, mB⟩ := hq
  refine ⟨cp.add cq, A ⊔ B, inferInstance, fun y => ?_⟩
  have h := Submodule.add_mem_sup (mA y) (mB y)
  exact h

private theorem rFin_mul {a : ℕ} {p q : GL (Fin a) ℂ → ℂ} (hp : RFin p) (hq : RFin q) :
    RFin (fun h => p h * q h) := by
  obtain ⟨cp, A, fA, mA⟩ := hp
  obtain ⟨cq, B, fB, mB⟩ := hq
  refine ⟨cp.mul cq, A * B, ?_, fun y => ?_⟩
  · have h1 : A.FG := (Submodule.fg_iff_finiteDimensional A).2 fA
    have h2 : B.FG := (Submodule.fg_iff_finiteDimensional B).2 fB
    exact (Submodule.fg_iff_finiteDimensional _).1 (h1.mul h2)
  · have h := Submodule.mul_mem_mul (mA y) (mB y)
    exact h

private theorem rFin_entry {a : ℕ} (i j : Fin a) :
    RFin (fun h : GL (Fin a) ℂ => (h : Matrix (Fin a) (Fin a) ℂ) i j) := by
  refine ⟨Units.continuous_val.matrix_elem i j,
    Submodule.span ℂ (Set.range fun r : Fin a => fun n : GL (Fin a) ℂ => (n : Matrix (Fin a) (Fin a) ℂ) i r),
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _), fun y => ?_⟩
  have h : (fun n : GL (Fin a) ℂ => ((n * y : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) =
      ∑ r, (y : Matrix (Fin a) (Fin a) ℂ) r j • fun n : GL (Fin a) ℂ => (n : Matrix (Fin a) (Fin a) ℂ) i r := by
    funext n
    simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
  rw [h]
  exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)

private theorem rFin_of_rep {a : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : GL (Fin a) ℂ →* (V →ₗ[ℂ] V)) (l : V →ₗ[ℂ] ℂ) (v : V) (X : GL (Fin a) ℂ)
    (hc : Continuous fun h : GL (Fin a) ℂ => l (ρ h v)) : RFin fun n => l (ρ (X * n) v) := by
  refine ⟨hc.comp (continuous_const.mul continuous_id),
    LinearMap.range (LinearMap.pi fun n : GL (Fin a) ℂ => l ∘ₗ ρ (X * n)), inferInstance,
    fun y => ⟨ρ y v, ?_⟩⟩
  funext n
  change l (ρ (X * n) (ρ y v)) = l (ρ (X * (n * y)) v)
  rw [← mul_assoc, map_mul ρ (X * n) y]
  rfl

private theorem rFin_delta {a : ℕ} (ν : DomWeight a) (X : GL (Fin a) ℂ) : RFin fun n => delta ν (X * n) := by
  haveI : FiniteDimensional ℂ (nablaSq ℂ a ν) := inferInstance
  exact rFin_of_rep (sqRep ℂ a ν) (ev1 ν) (top ν) X (GlobalTheory.BCT.TrKer.continuous_coef_sqRep a ν (top ν) (ev1 ν))

theorem UpperTheory.Gal.Wt.rFinEx_of :
    UpperTheory.Gal.Wt.RFinEx := by
  intro a
  refine ⟨rFin_delta, fun P => ?_⟩
  induction P using MvPolynomial.induction_on with
  | C c =>
    have h : pev (MvPolynomial.C c : MvPolynomial (Fin a × Fin a) ℂ) = fun _ => c := by
      funext g
      simp [pev]
    rw [h]
    exact rFin_const c
  | add p q hp hq =>
    have h : pev (p + q) = fun g => pev p g + pev q g := by
      funext g
      simp [pev]
    rw [h]
    exact rFin_add hp hq
  | mul_X p n hp =>
    have h : pev (p * MvPolynomial.X n) = fun g => pev p g * (g : Matrix (Fin a) (Fin a) ℂ) n.1 n.2 := by
      funext g
      simp [pev]
    rw [h]
    exact rFin_mul hp (rFin_entry n.1 n.2)

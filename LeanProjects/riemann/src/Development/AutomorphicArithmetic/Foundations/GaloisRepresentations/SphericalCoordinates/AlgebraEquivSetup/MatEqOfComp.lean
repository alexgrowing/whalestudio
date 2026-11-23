import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtPLoc
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap below)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem exists_over (v : Plc ℚ) : ∃ w : Plc E, below ℚ w = v := by
  haveI := v.isMaximal
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  exact ⟨⟨Q, hQm.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hQo.over.symm⟩

private theorem fam_inj : Function.Injective (finiteAdeleMap ℚ E) := by
  intro x y h
  refine FiniteAdeleRing.ext (K := ℚ) fun v => ?_
  obtain ⟨w, rfl⟩ := exists_over (E := E) v
  have h1 := congrArg (fun z : FiniteAdeleRing (𝓞 E) E => z w) h
  exact (GroundTheory.Global.SemiLocal.completionMap (below ℚ w) w).injective h1

variable {n : ℕ}

private theorem mat_eq_of_comp {g g' : GUf E n} (h : ∀ w, comp w g = comp w g') : mat g = mat g' := by
  refine Units.ext (Matrix.ext fun i k => GlobalTheory.EulerTw.pLoc_ext E fun w => ?_)
  exact congrArg (fun x : GL (Fin n) (w.adicCompletion E) => x.val i k) (h w)

private theorem sim_eq_of_mat (hn : 1 ≤ n) {g g' : GUf E n} (h : mat g = mat g') : sim g = sim g' := by
  have h1 := UpperTheory.Gal.CertificateRingHomMap.mem_Sim.1 g.2
  have h2 := UpperTheory.Gal.CertificateRingHomMap.mem_Sim.1 g'.2
  have h3 : (g : GL (Fin n) (Af E) × AfQˣ).1 = (g' : GL (Fin n) (Af E) × AfQˣ).1 := h
  rw [h3, h2] at h1
  have h4 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h4
  exact Units.ext (fam_inj h4.symm)

private theorem eq_of_comp (hn : 1 ≤ n) {g g' : GUf E n} (h : ∀ w, comp w g = comp w g') : g = g' :=
  Subtype.ext (Prod.ext (mat_eq_of_comp h) (sim_eq_of_mat hn (mat_eq_of_comp h)))

private theorem map_eq_iff {p : ℕ} [Fact p.Prime] (T : AdT p E) (x y : GL (Fin n) (Af E)) :
    x.val.map T.Φ = y.val.map T.Φ ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal →
      GeneralLinearGroup.map (pLoc E w) x = GeneralLinearGroup.map (pLoc E w) y := by
  constructor
  · intro h w hw
    refine Units.ext (Matrix.ext fun i k => ?_)
    have h1 : T.Φ (x.val i k - y.val i k) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.2 (congrFun (congrFun h i) k)
    have h2 := (T.Φ_ker _).1 h1 w hw
    rw [map_sub] at h2
    exact sub_eq_zero.1 h2
  · intro h
    refine Matrix.ext fun i k => ?_
    have h1 : T.Φ (x.val i k - y.val i k) = 0 := by
      refine (T.Φ_ker _).2 fun w hw => ?_
      rw [map_sub]
      exact sub_eq_zero.2 (congrArg (fun z : GL (Fin n) (w.adicCompletion E) => z.val i k) (h w hw))
    rw [map_sub] at h1
    exact sub_eq_zero.1 h1

private theorem conj_comp_iff (a : GL (Fin n) (Af E)) (w : Plc E) (g g' : GUf E n) :
    GeneralLinearGroup.map (pLoc E w) (a * mat g * a⁻¹) = GeneralLinearGroup.map (pLoc E w) (a * mat g' * a⁻¹) ↔
      comp w g = comp w g' := by
  have e : ∀ h : GUf E n, GeneralLinearGroup.map (pLoc E w) (a * mat h * a⁻¹) =
      GeneralLinearGroup.map (pLoc E w) a * comp w h * (GeneralLinearGroup.map (pLoc E w) a)⁻¹ := fun h => by
    rw [map_mul, map_mul, map_inv]; rfl
  rw [e, e, mul_left_inj, mul_right_inj]

private theorem algMap_inj {p : ℕ} [Fact p.Prime] (hn : 1 ≤ n)
    (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)) (hμ : IsMu μ)
    {c c' : AfP p} (h : c ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E) = c' ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E)) : c = c' := by
  have h1 := congrFun (congrFun (congrArg μ h) ⟨0, hn⟩) ⟨0, hn⟩
  rw [hμ, hμ, Matrix.one_apply_eq] at h1
  exact Algebra.TensorProduct.includeLeft_injective (R := ℚ) (S := ℚ) (A := AfP p) (B := E)
    (algebraMap ℚ E).injective h1

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.pJEq :
    JEq := by
  intro E _ _ _ A n p _ S T μ hμ a j hj
  refine ⟨fun g g' h => eq_of_comp S.facts.pos h, fun g g' => ?_⟩
  have key : S.mx (j g) = S.mx (j g') ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w g = comp w g' := by
    rw [← μ.injective.eq_iff, hj, hj, map_eq_iff]
    exact forall₂_congr fun w _ => conj_comp_iff a w g g'
  rw [← key]
  refine ⟨fun h => congrArg S.mx h, fun h => ?_⟩
  have h1 : (((j g : S.G.GAf) : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1) = ((j g' : S.G.GAf) : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1 := Units.ext h
  refine Subtype.ext (Prod.ext h1 (Units.ext ?_))
  have e1 := mem_uGroup.1 (j g).2
  have e2 := mem_uGroup.1 (j g').2
  rw [h1, e2] at e1
  exact algMap_inj S.facts.pos μ hμ e1.symm

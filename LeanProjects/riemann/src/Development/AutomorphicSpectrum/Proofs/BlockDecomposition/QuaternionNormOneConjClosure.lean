import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionConjugateApproximationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionClassNumberFiniteStatement
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.ConjStep

variable {F : Type} [Field F] [NumberField F] {d β : F}

theorem conj_mem_suppAt {T : Set (Pl F)} (c : (Q d β (AF F))ˣ) {g : Q d β (AF F)}
    (hg : g ∈ SuppAt d β T) :
    ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * g * (c : Q d β (AF F)) ∈ SuppAt d β T := by
  have hcc : ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * (c : Q d β (AF F)) = 1 := c.inv_mul
  refine ⟨?_, fun u hu => ?_⟩
  · rw [qn_mul, qn_mul, hg.1, mul_one, ← qn_mul, hcc, qn_one]
  · rw [map_mul, map_mul, hg.2 u hu, mul_one, ← map_mul, hcc, map_one]

theorem star_mem_suppAt {T : Set (Pl F)} {g : Q d β (AF F)} (hg : g ∈ SuppAt d β T) :
    star g ∈ SuppAt d β T := by
  have h1 : star g * g = 1 := by rw [star_mul_eq, hg.1, map_one]
  refine ⟨by rw [qn_star, hg.1], fun u hu => ?_⟩
  have h2 := congrArg (qmap (proj u)) h1
  rwa [map_mul, hg.2 u hu, mul_one, map_one] at h2

theorem conj_central {A : Type*} [Ring A] (c ci D Di Z Zi X : A) (hZ : Z * X = X * Z)
    (hZZ : Z * Zi = 1) : (c * D * Z) * X * (Zi * Di * ci) = c * (D * X * Di) * ci := by
  calc (c * D * Z) * X * (Zi * Di * ci) = c * D * (Z * X) * Zi * Di * ci := by
        simp only [mul_assoc]
    _ = c * D * X * (Z * Zi) * Di * ci := by rw [hZ]; simp only [mul_assoc]
    _ = c * (D * X * Di) * ci := by rw [hZZ]; simp only [mul_assoc, mul_one]

theorem conj_mem_SAQ {s : Pl F} {b : Q d β (AF F)} {y c : (Q d β (AF F))ˣ} {δ : (Q d β F)ˣ} {z : (AF F)ˣ}
    {x : Q d β F} (hx : qn x = 1) {h : Q d β (AF F)} (hh : h ∈ SuppAt d β {s})
    (hy : y = c * Units.map (rat (R := AF F) : Q d β F →+* Q d β (AF F)).toMonoidHom δ *
      Units.map (algebraMap (AF F) (Q d β (AF F))).toMonoidHom z)
    (e : (y : Q d β (AF F)) * rat x * ((y⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) = b * h) :
    ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * b * (c : Q d β (AF F)) ∈ SAQ d β s := by
  set ci : Q d β (AF F) := ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) with hci
  have hcc : ci * (c : Q d β (AF F)) = 1 := c.inv_mul
  have hsh : h * star h = 1 := by rw [mul_star_eq, hh.1, map_one]
  let ρ : Q d β F := (δ : Q d β F) * x * ((δ⁻¹ : (Q d β F)ˣ) : Q d β F)
  have hρ : qn ρ = 1 := by
    have h1 : ((δ⁻¹ : (Q d β F)ˣ) : Q d β F) * (δ : Q d β F) = 1 := δ.inv_mul
    have h2 : qn ((δ⁻¹ : (Q d β F)ˣ) : Q d β F) * qn (δ : Q d β F) = 1 := by
      rw [← qn_mul, h1, qn_one]
    simp only [ρ, qn_mul, hx, mul_one]
    rw [mul_comm]; exact h2
  have hconj : (y : Q d β (AF F)) * rat x * ((y⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) =
      (c : Q d β (AF F)) * rat ρ * ci := by
    subst hy
    have hZZ : algebraMap (AF F) (Q d β (AF F)) (z : AF F) *
        algebraMap (AF F) (Q d β (AF F)) ((z⁻¹ : (AF F)ˣ) : AF F) = 1 := by
      rw [← map_mul, z.mul_inv, map_one]
    have := conj_central (c : Q d β (AF F)) ci (rat (δ : Q d β F))
      (rat ((δ⁻¹ : (Q d β F)ˣ) : Q d β F)) (algebraMap (AF F) (Q d β (AF F)) (z : AF F))
      (algebraMap (AF F) (Q d β (AF F)) ((z⁻¹ : (AF F)ˣ) : AF F)) (rat x)
      (Algebra.commutes _ _) hZZ
    simp only [ρ, map_mul]
    rw [← this]
    simp [mul_inv_rev, hci, mul_assoc]
  have hb : b = (c : Q d β (AF F)) * rat ρ * ci * star h := by
    rw [← hconj, e, mul_assoc, hsh, mul_one]
  refine ⟨ρ, hρ, ci * star h * (c : Q d β (AF F)), conj_mem_suppAt c (star_mem_suppAt hh), ?_⟩
  rw [hb]
  calc ci * ((c : Q d β (AF F)) * rat ρ * ci * star h) * (c : Q d β (AF F))
      = (ci * (c : Q d β (AF F))) * rat ρ * (ci * star h * (c : Q d β (AF F))) := by
        simp only [mul_assoc]
    _ = rat ρ * (ci * star h * (c : Q d β (AF F))) := by rw [hcc, one_mul]

theorem exists_conj_mem_closure : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∀ s w : Pl F, (∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0) → w ≠ s →
  ∀ a ∈ SuppAt d β {w}, (qmap (proj w) a).re ^ 2 ≠ 1 →
    ∃ c : (Q d β (AF F))ˣ, ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ closure (SAQ d β s) := by
  intro F _ _ d β hdiv s w hs hws a ha hre
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.T.quaternion_class_number_finite d β hdiv
  by_contra hne
  push_neg at hne
  let f : (Q d β (AF F))ˣ × Q d β (AF F) → Q d β (AF F) := fun p =>
    ((p.1⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * p.2 * (p.1 : Q d β (AF F))
  have hf : Continuous f :=
    ((Units.continuous_val.comp (continuous_inv.comp continuous_fst)).mul continuous_snd).mul
      (Units.continuous_val.comp continuous_fst)
  have hopen : IsOpen (f ⁻¹' (closure (SAQ d β s))ᶜ) := isClosed_closure.isOpen_compl.preimage hf
  have hsub : C ×ˢ ({a} : Set (Q d β (AF F))) ⊆ f ⁻¹' (closure (SAQ d β s))ᶜ := by
    rintro ⟨c, b⟩ ⟨-, hb⟩
    obtain rfl : b = a := hb
    exact hne c
  obtain ⟨u, v, -, hv, hCu, hav, huv⟩ := generalized_tube_lemma hC isCompact_singleton hopen hsub
  obtain ⟨b, hb, y, x, hx, h, hh, e⟩ :=
    GlobalTheory.T.quaternion_conjugate_approximation d β hdiv s w hs hws a ha hre v (hv.mem_nhds (hav rfl))
  obtain ⟨c, hc, δ, z, hy⟩ := hcov y
  exact huv (Set.mk_mem_prod (hCu hc) hb) (subset_closure (conj_mem_SAQ hx hh hy e))

end GlobalTheory.CompanionTheory.PlaneSA.ConjStep

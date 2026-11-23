import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow

noncomputable section

namespace GlobalTheory.Grow

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open GlobalTheory.AdelicU (absFin absBar finEmb FvBar compFin compInf htFin htInf normFin)
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (infHt finHt finNorm finCoord)

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {ι : Type} [Fintype ι]
  (b : Module.Basis ι F E)

theorem absFin_le_coord (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) {K c : ℝ≥0}
    (hK : ∀ k, absFin F v ((1 : Fv F v) ⊗ₜ[F] b k) ≤ K)
    (hc : ∀ k, ‖(Algebra.TensorProduct.basis (Fv F v) b).repr y k‖₊ ≤ c) : absFin F v y ≤ K * c := by
  rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr y]
  refine GlobalTheory.AdelicU.absFin_sum_le F v _ _ fun k _ => ?_
  have e : ∀ a : Fv F v, a • (Algebra.TensorProduct.basis (Fv F v) b) k =
      ((1 : Fv F v) ⊗ₜ[F] b k) * (a ⊗ₜ[F] (1 : E)) := fun a => by
    simp [TensorProduct.smul_tmul']
  rw [e]
  refine (GlobalTheory.AdelicU.absFin_mul_le F v _ _).trans (mul_le_mul' (hK k) ?_)
  rw [GlobalTheory.AdelicU.absFin_tmul_one]
  exact hc k

theorem exists_trace_eq_repr : ∃ b' : ι → E, ∀ x k, Algebra.trace F E (b' k * x) = b.repr x k := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine ⟨fun k => ((Algebra.traceForm F E).toDual (traceForm_nondegenerate F E)).symm (b.coord k), fun x k => ?_⟩
  exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate F E) (b.coord k) x

theorem coord_le_absFin {b' : ι → E} (hb : ∀ x k, Algebra.trace F E (b' k * x) = b.repr x k)
    (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) (k : ι) :
    ‖(Algebra.TensorProduct.basis (Fv F v) b).repr y k‖₊ ≤ absFin F v ((1 : Fv F v) ⊗ₜ[F] b' k) * absFin F v y := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have e : algebraMap (Fv F v) (FvBar F v) ((Algebra.TensorProduct.basis (Fv F v) b).repr y k) =
      ∑ τ : E →ₐ[F] FvBar F v, finEmb F v τ (((1 : Fv F v) ⊗ₜ[F] b' k) * y) := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, mul_add, Finset.sum_add_distrib]
    | tmul a x =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, GlobalTheory.AdelicU.finEmb_tmul, ← Finset.mul_sum]
      rw [← trace_eq_sum_embeddings (FvBar F v), hb, Algebra.TensorProduct.basis_repr_tmul,
        IsScalarTower.algebraMap_apply F (Fv F v) (FvBar F v), ← map_mul]
      simp
  rw [← GlobalTheory.AdelicU.absBar_algebraMap, e]
  refine Valuation.map_sum_le (GlobalTheory.AdelicU.valBar F v) fun τ _ => ?_
  exact (GlobalTheory.AdelicU.le_absFin F v τ _).trans (GlobalTheory.AdelicU.absFin_mul_le F v _ _)

theorem exists_absFin_bound (x : ι → E) : ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧
    ∀ v, 1 ≤ K v ∧ ∀ k, absFin F v ((1 : Fv F v) ⊗ₜ[F] x k) ≤ K v := by
  refine ⟨fun v => max 1 (Finset.univ.sup fun k => absFin F v ((1 : Fv F v) ⊗ₜ[F] x k)), ?_, fun v =>
    ⟨le_max_left _ _, fun k => le_max_of_le_right
      (Finset.le_sup (f := fun k => absFin F v ((1 : Fv F v) ⊗ₜ[F] x k)) (Finset.mem_univ k))⟩⟩
  have h := eventually_all.2 fun k => GlobalTheory.AdelicU.eventually_absFin_le_one F ((1 : AF F) ⊗ₜ[F] x k)
  refine (eventually_cofinite.1 h).subset fun v hv hv' => hv (max_eq_left (Finset.sup_le fun k _ => ?_))
  simpa [compFin] using hv' k

theorem evalV_repr (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) (k : ι) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((Algebra.TensorProduct.basis (Af F) b).repr
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) k) =
      (Algebra.TensorProduct.basis (Fv F v) b).repr (compFin F E v z) k := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x => simp [compFin, GlobalTheory.AdelicU.evFin, Algebra.TensorProduct.basis_repr_tmul]

end Local

theorem finprod_le_mul {α : Type} {f g K : α → ℝ≥0} (hf : (Function.mulSupport f).Finite)
    (hg : (Function.mulSupport g).Finite) (hK : (Function.mulSupport K).Finite) (h : ∀ a, f a ≤ K a * g a) :
    ∏ᶠ a, f a ≤ (∏ᶠ a, K a) * ∏ᶠ a, g a := by
  rw [← finprod_mul_distrib hK hg]
  exact finprod_le_finprod' hf ((hK.union hg).subset (Function.mulSupport_mul _ _)) h

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (V : HSp D)

theorem evalV_finCoord (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V) (i j : Fin V.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v (finCoord D (finMat D.sp.cm.sig V.gram g i j) k) =
      (Algebra.TensorProduct.basis (Fv D.host.F v) (Module.finBasis D.host.F D.host.E)).repr
        (compFin D.host.F D.host.E v ((Formalism.L2.Theta.matHom V g).1 i j)) k :=
  evalV_repr (Module.finBasis D.host.F D.host.E) v ((Formalism.L2.Theta.matHom V g).1 i j) k

theorem finNorm_le_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {g : GA D V} {c : ℝ≥0} : finNorm V v g ≤ c ↔
    ∀ i j k, ‖(Algebra.TensorProduct.basis (Fv D.host.F v) (Module.finBasis D.host.F D.host.E)).repr
      (compFin D.host.F D.host.E v ((Formalism.L2.Theta.matHom V g).1 i j)) k‖₊ ≤ c := by
  simp only [finNorm, Finset.sup_le_iff, Finset.mem_univ, true_imp_iff, Prod.forall, evalV_finCoord]

theorem exists_finNorm_comparison : ∃ K : HeightOneSpectrum (𝓞 D.host.F) → ℝ≥0, (Function.mulSupport K).Finite ∧
    ∀ v, 1 ≤ K v ∧ ∀ g : GA D V,
      finNorm V v g ≤ K v * normFin D.host.F v (bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g)).1 ∧
      normFin D.host.F v (bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g)).1 ≤ K v * finNorm V v g := by
  obtain ⟨b', hb⟩ := exists_trace_eq_repr (Module.finBasis D.host.F D.host.E)
  obtain ⟨K, hK, h⟩ := exists_absFin_bound (F := D.host.F) (Sum.elim (Module.finBasis D.host.F D.host.E) b')
  refine ⟨K, hK, fun v => ⟨(h v).1, fun g => ⟨(finNorm_le_iff V).2 fun i j k => ?_,
    (GlobalTheory.AdelicU.normFin_le_iff _ v).2 fun i j => ?_⟩⟩⟩
  · exact (coord_le_absFin _ hb v _ _).trans (mul_le_mul' ((h v).2 (.inr _))
      (GlobalTheory.AdelicU.absFin_le_normFin _ v (bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g)).1 i j))
  · exact absFin_le_coord (Module.finBasis D.host.F D.host.E) v
      (compFin D.host.F D.host.E v ((Formalism.L2.Theta.matHom V g).1 i j)) (fun k => (h v).2 (.inl k))
      ((finNorm_le_iff V).1 le_rfl i j)

theorem height_comparison (hθ : IsInfFam θ) : ∃ C : ℝ, 0 < C ∧ ∀ g : GA D V,
    (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) ≤ C * height V g ∧ height V g ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) := by
  obtain ⟨K, hK, h⟩ := exists_finNorm_comparison V
  have key : ∀ {k a a' c c' : ℝ≥0}, 1 ≤ k → a ≤ k * c → a' ≤ k * c' → max 1 (max a a') ≤ k * max 1 (max c c') :=
    fun hk h1 h2 => max_le (one_le_mul_of_one_le_of_one_le hk (le_max_left _ _)) (max_le
      (h1.trans (mul_le_mul_right (le_max_of_le_right (le_max_left _ _)) _))
      (h2.trans (mul_le_mul_right (le_max_of_le_right (le_max_right _ _)) _)))
  have h1 : (1 : ℝ≥0) ≤ ∏ᶠ v, K v := one_le_finprod' fun v => (h v).1
  refine ⟨(∏ᶠ v, K v : ℝ≥0), by exact_mod_cast zero_lt_one.trans_le h1, fun g => ?_⟩
  have e : ∏ w, htInf D.host.F w (bc (compInf D.host.F D.host.E w) (Formalism.L2.Theta.matHom V g)) = ∏ τ, infHt θ V τ g :=
    (Function.Bijective.prod_comp (GlobalTheory.CMTypePlaces.places_bijective D) _).symm.trans
      (Finset.prod_congr rfl fun τ _ => htInf_eq_infHt V hθ τ g)
  have hi := fun v => (h v).2 g⁻¹
  simp only [map_inv] at hi
  have f1 := GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite V g
  have f2 := GlobalTheory.AdelicU.finite_mulSupport_htFin D.host.F (Formalism.L2.Theta.matHom V g)
  have a1 := finprod_le_mul f1 f2 hK fun v => key (h v).1 ((h v).2 g).1 (hi v).1
  have a2 := finprod_le_mul f2 f1 hK fun v => key (h v).1 ((h v).2 g).2 (hi v).2
  unfold height GlobalTheory.AdelicU.heightGL GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height
  rw [e]
  constructor
  · exact_mod_cast (mul_le_mul_right a1 _).trans_eq (mul_left_comm _ _ _)
  · exact_mod_cast (mul_le_mul_right a2 _).trans_eq (mul_left_comm _ _ _)

end GlobalTheory.Grow

end

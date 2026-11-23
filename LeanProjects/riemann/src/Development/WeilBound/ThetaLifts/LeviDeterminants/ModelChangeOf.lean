import Development.WeilBound.ThetaLifts.LeviDeterminants.ExistsNeOfSurjOn
import Development.WeilBound.ThetaLifts.LeviDeterminants.EvalZeroMemAdelicSchwartzAdmittedForms
import Development.WeilBound.ThetaLifts.LeviDeterminants.ChiIndep
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.DarbouxModelRationalLatticeOf

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

theorem exists_linearEquiv_of_rational {K R E α β κ : Type} [Field K] [CommRing R] [Algebra K R] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Fintype α] [Fintype β] [Fintype κ]
    (hinj : Function.Injective (algebraMap K R))
    (e : Matrix α β (R ⊗[K] E) ≃ₗ[R] (κ → R) × (κ → R))
    (h : ∀ x : Matrix α β E, ∃ y z : κ → K, e (x.map fun t => (1 : R) ⊗ₜ[K] t) =
      (fun i => algebraMap K R (y i), fun i => algebraMap K R (z i))) :
    ∃ d₀ : Matrix α β E ≃ₗ[K] (κ → K) × (κ → K), ∀ x, e (x.map fun t => (1 : R) ⊗ₜ[K] t) =
      (fun i => algebraMap K R ((d₀ x).1 i), fun i => algebraMap K R ((d₀ x).2 i)) := by
  classical
  haveI : Nontrivial R := hinj.nontrivial
  choose y z hyz using h
  have hadd : ∀ a b : Matrix α β E, ((a + b).map fun t => (1 : R) ⊗ₜ[K] t) =
      (a.map fun t => (1 : R) ⊗ₜ[K] t) + b.map fun t => (1 : R) ⊗ₜ[K] t := by
    intro a b
    ext i j
    simp [TensorProduct.tmul_add]
  have hsmul : ∀ (c : K) (a : Matrix α β E), ((c • a).map fun t => (1 : R) ⊗ₜ[K] t) =
      algebraMap K R c • a.map fun t => (1 : R) ⊗ₜ[K] t := by
    intro c a
    ext i j
    change (1 : R) ⊗ₜ[K] (c • a i j) = algebraMap K R c • ((1 : R) ⊗ₜ[K] a i j)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let f : Matrix α β E →ₗ[K] (κ → K) × (κ → K) :=
    { toFun := fun x => (y x, z x)
      map_add' := by
        intro a b
        have key := hyz (a + b)
        rw [hadd, map_add, hyz a, hyz b] at key
        have h1 : ∀ i, algebraMap K R (y a i) + algebraMap K R (y b i) = algebraMap K R (y (a + b) i) :=
          fun i => congrFun (congrArg Prod.fst key) i
        have h2 : ∀ i, algebraMap K R (z a i) + algebraMap K R (z b i) = algebraMap K R (z (a + b) i) :=
          fun i => congrFun (congrArg Prod.snd key) i
        refine Prod.ext (funext fun i => hinj ?_) (funext fun i => hinj ?_)
        · change algebraMap K R (y (a + b) i) = algebraMap K R (y a i + y b i)
          rw [map_add, h1]
        · change algebraMap K R (z (a + b) i) = algebraMap K R (z a i + z b i)
          rw [map_add, h2]
      map_smul' := by
        intro c a
        have key := hyz (c • a)
        rw [hsmul, map_smul, hyz a] at key
        have h1 : ∀ i, algebraMap K R c * algebraMap K R (y a i) = algebraMap K R (y (c • a) i) :=
          fun i => congrFun (congrArg Prod.fst key) i
        have h2 : ∀ i, algebraMap K R c * algebraMap K R (z a i) = algebraMap K R (z (c • a) i) :=
          fun i => congrFun (congrArg Prod.snd key) i
        refine Prod.ext (funext fun i => hinj ?_) (funext fun i => hinj ?_)
        · change algebraMap K R (y (c • a) i) = algebraMap K R (c * y a i)
          rw [map_mul, h1]
        · change algebraMap K R (z (c • a) i) = algebraMap K R (c * z a i)
          rw [map_mul, h2] }
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : y a = y b := congrArg Prod.fst hab
    have h2 : z a = z b := congrArg Prod.snd hab
    have h3 : (a.map fun t => (1 : R) ⊗ₜ[K] t) = b.map fun t => (1 : R) ⊗ₜ[K] t :=
      e.injective (by rw [hyz a, hyz b, h1, h2])
    ext i j
    exact Algebra.TensorProduct.includeRight_injective (R := K) (A := R) (B := E) hinj (congrFun (congrFun h3 i) j)
  have hdim : Module.finrank K (Matrix α β E) = Module.finrank K ((κ → K) × (κ → K)) := by
    have h1 := e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_prod, Module.finrank_pi, Module.finrank_baseChange] at h1
    rw [Module.finrank_matrix, Module.finrank_prod, Module.finrank_pi]
    simpa using h1
  refine ⟨LinearMap.linearEquivOfInjective f hf hdim, fun x => ?_⟩
  simpa [f] using hyz x

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem ratRel_of_good {ψ : AddChar (AF F) ℂ} {M M₁ : Model σ X W} (h : M.IsGood ψ) (h₁ : M₁.IsGood ψ) : RatRel M.co M₁.co := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨d₀, hd⟩ := exists_linearEquiv_of_rational (AdeleRing.algebraMap_injective (𝓞 F) F) M.co.e h.rat
  intro y z
  obtain ⟨x, hx⟩ := d₀.surjective (y, z)
  obtain ⟨y', z', h'⟩ := h₁.rat x
  refine ⟨incM F x, y', z', ?_, h'⟩
  have := hd x
  rw [hx] at this
  exact this

theorem modelChange_of_parts (hA : PositivityTheory.Mix.AdelSt) (hC : SiegelChar) : ModelChange := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ om₁ hP₁
  classical
  have hψ := hP.base.std
  have hr := ratRel_of_good hP.good hP₁.good
  have hr' := ratRel_of_good hP₁.good hP.good
  obtain ⟨e₁, ei, ev, hsurj, hmaps, hheis, hSB, hvac, hstd, hpure⟩ :=
    PositivityTheory.Mix.darboux_model_rational_lattice_of hA F E σ B n d X W M r s r' s' hP.base hP.herm hP.skew hP.good M₁.co hP₁.good.rat
  choose c hc0 hc using fun v => vac_line hP.base hP.herm hP.skew M₁ v (hP₁.good.vac v) (φ' := ev v (M.vac v)) (hvac v)
  have hc1 : ∀ᶠ v in cofinite, c v = 1 := by
    filter_upwards [hstd, hP₁.good.std] with v h1 h2
    have h' := hc v
    rw [h1, h2] at h'
    have h := congrFun h' 0
    have hm : (0 : Fin n × Fin d → Fv F v) ∈ {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} :=
      fun i => zero_mem _
    rw [Pi.smul_apply, Set.indicator_of_mem hm, smul_eq_mul] at h
    simpa using h.symm
  have hfin0 : (Function.mulSupport c).Finite := Filter.eventually_cofinite.1 hc1
  have hk : (∏ᶠ v, c v)⁻¹ ≠ 0 := inv_ne_zero (finprod_ne_zero hc0)
  have hstd' : ∀ᶠ v in cofinite, ev v (Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hstd, hP.good.std] with v h1 h2
    rwa [h2] at h1
  have hpure' : ∀ f φ, (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
      e₁ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v) := fun f φ h1 h2 =>
    hpure f φ h1 (by filter_upwards [h2, hP.good.std] with v e1 e2; rw [e1, e2])
  have hs := surjOn_of_pure e₁ ei ev hsurj (fun v => (hSB v).ge) hstd' hpure'
  have t₁ : Tw B.ψ M.co M₁.co e₁ := ⟨hmaps, hheis,
    Span.comp_mem_adm e₁ ei ev (fun v φ hφ => hSB v ▸ Submodule.mem_map_of_mem hφ) hstd' hpure', exists_ne_of_surjOn hs⟩
  have t := t₁.smul hk
  obtain ⟨e₀, t₀⟩ := twEx hA F B.ψ hψ _ _ _ M₁.co M.co
  obtain ⟨e', t', hl1, hl2⟩ := t.exists_inv hψ t₀ hr hr'
  obtain ⟨a, ha, Ha⟩ := t.theta hψ hr
  refine ⟨_, a, ha, ⟨t.maps, fun z Φ hΦ => ?_, fun u hu => absurd hu (Set.notMem_empty u), ei, fun v => (c v)⁻¹ • ev v, ?_, ?_, ?_⟩,
    ⟨t.maps, fun x hx y hy hxy => ?_, fun Φ hΦ => ⟨e' Φ, t'.maps Φ hΦ, hl2 Φ hΦ⟩⟩, fun Φ hΦ => ⟨Ha Φ hΦ, fun x => ?_⟩⟩
  · have h1 : ∀ m, incM F (1 : Matrix (Fin m) (Fin m) E) = 1 := fun m => Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1, h1, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
    exact t.Heisenberg₂ z Φ hΦ
  · intro h
    obtain ⟨b, hb⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F (Fin n × Fin d)
    obtain ⟨f, rfl⟩ := hsurj b
    exact hb (by rw [h]; rfl)
  · intro v
    refine ⟨?_, ?_⟩
    · rw [LinearMap.smul_apply, hc v, smul_smul, inv_mul_cancel₀ (hc0 v), one_smul]
    · rw [Submodule.map_smul _ _ _ (inv_ne_zero (hc0 v)), hSB v]
  · intro f φ hφ hφv
    funext y
    rw [LinearMap.smul_apply, hpure f φ hφ hφv]
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, LinearMap.smul_apply]
    have hfin1 : (Function.mulSupport fun v : Pl F => (c v)⁻¹).Finite := by
      refine hfin0.subset fun v hv h => hv ?_
      simp [h]
    have hfin2 := GlobalTheory.PureFactor.mulSupport_finite (κ := Fin n × Fin d) (fun v => ev v (φ v)) (by
      filter_upwards [hφv, hstd] with v h1 h2
      rw [h1, h2]) y
    rw [finprod_mul_distrib hfin1 hfin2, finprod_inv_distrib]
    ring
  · rw [← hl1 x hx, hxy, hl1 y hy]
  · exact pair_tw (twEx hA) hC σ hP.base.cm M M₁ hψ hP.herm.herm (PositivityTheory.ThK.Vac.herm_det hP.herm).ne_zero hP.skew.skew
      (PositivityTheory.ThK.Vac.skew_det hP.skew).ne_zero hr hr' hP.weil hP₁.weil t x Φ hΦ

end PositivityTheory.ThKF0

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegativeFrameDomainProductOpenPreconnectedStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDomainFramesEqGramFramesUnitaryStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.BackHol

theorem continuous_place {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    {τ : L →+* ℂ} {θ : Ainf F ⊗[F] L →+* ℂ} (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) :
    Continuous fun z : AF F ⊗[F] L => θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F L) z) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] L) := ⟨rfl⟩
  have : Module.Finite F L := Module.Finite.of_restrictScalars_finite ℚ _ _
  let b := Module.finBasis F L
  let B := Algebra.TensorProduct.basis (AF F) b
  have he : (fun z : AF F ⊗[F] L => θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F L) z)) = fun z => ∑ i,
      θ (fstA F (B.coord i z) ⊗ₜ[F] (1 : L)) * τ (b i) := by
    funext z
    conv_lhs => rw [← B.sum_repr z, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← hθ.1, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Algebra.TensorProduct.map_tmul]
    rfl
  rw [he]
  refine continuous_finset_sum _ fun i _ => Continuous.mul ?_ continuous_const
  have h1 : Continuous (B.coord i) := IsModuleTopology.continuous_of_linearMap _
  have h2 : Continuous (fstA F) := continuous_fst
  exact hθ.2.comp (h2.comp h1)

variable {D : D7}

theorem continuous_archM (V : HSp D) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) : Continuous (archM V θ) := by
  have hm : Continuous fun g : GA D V =>
      ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    Units.continuous_val.comp continuous_subtype_val
  refine continuous_pi fun a => continuous_pi fun c => ?_
  exact (continuous_place hθ).comp (hm.matrix_elem a c)

theorem archM_mul (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    archM V θ (a * b) = archM V θ a * archM V θ b := by
  unfold archM
  rw [map_mul, Units.val_mul, Matrix.map_mul]

theorem archM_of_fin (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) {k : GA D V}
    (hk : k ∈ GfC V) : archM V θ k = 1 := by
  have hk' : infHom V k = 1 := hk
  rw [archM, hk', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem topGroup (V : HSp D) : IsTopologicalGroup (GA D V) := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))

theorem continuous_of_holAd {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
    (hM : HolShape M) {w : D.what₂.Tau → Fin V.rank → ℤ} {φ : GA D V → ℂ} (hφ : HolAd θ M w φ)
    (U : Subgroup (GA D V)) (hU : IsOpen (U : Set (GA D V))) (hl : ∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) :
    Continuous φ := by
  classical
  haveI := topGroup V
  obtain ⟨L, hL1, -, hLc, hUG, hLa, -, hdec, hcomm, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  have horth : ∀ τ, OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) := fun τ =>
    ((GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.2.2 hM).1
  obtain ⟨-, -, hst, hx0⟩ := GlobalTheory.HolDict.frDoms_open_preconnected_stable V.rank D.what₂.Tau (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) horth
  rw [continuous_iff_continuousAt]
  intro h
  obtain ⟨f, ⟨P, ⟨hPd, -⟩, hfP⟩, hf⟩ := hφ h
  let A : GA D V → D.what₂.Tau → Mt V.rank := fun g τ => archM V (θ τ) (h⁻¹ * g)
  have hA : Continuous A := continuous_pi fun τ =>
    (continuous_archM V (hθ τ)).comp (continuous_const.mul continuous_id)
  have hAU : ∀ g, A g ∈ UG (gramAt D V) := fun g => hUG _
  have hu : Continuous fun g => L (A g) := hLc.comp_continuous hA hAU
  have ha : Continuous fun g => (L (A g))⁻¹ * (h⁻¹ * g) := hu.inv.mul (continuous_const.mul continuous_id)
  have hafin : ∀ g, (L (A g))⁻¹ * (h⁻¹ * g) ∈ GfC V := by
    intro g
    obtain ⟨a, ha, u, hu, e⟩ := hdec (h⁻¹ * g)
    have e1 : A g = fun τ => archM V (θ τ) u := by
      funext τ
      show archM V (θ τ) (h⁻¹ * g) = _
      rw [e, archM_mul, archM_of_fin V _ ha, one_mul]
    rw [e1, hLa u hu, e, hcomm a ha u hu, inv_mul_cancel_left]
    exact ha
  have hah : (L (A h))⁻¹ * (h⁻¹ * h) ∈ U := by
    have e1 : A h = fun τ => archM V (θ τ) 1 := by
      funext τ
      show archM V (θ τ) (h⁻¹ * h) = _
      rw [inv_mul_cancel]
    rw [e1, hLa 1 (one_mem _)]
    simpa using U.one_mem
  have hN : {g | (L (A g))⁻¹ * (h⁻¹ * g) ∈ U} ∈ 𝓝 h := (hU.preimage ha).mem_nhds hah
  have hx : Continuous fun g => (fun τ => (A g τ * x0Mat M τ : Mt V.rank) : D.what₂.Tau → Fin V.rank → Fin V.rank → ℂ) :=
    continuous_pi fun τ => ((continuous_apply τ).comp hA).matrix_mul continuous_const
  have hmem : ∀ g, (fun τ => (A g τ * x0Mat M τ : Mt V.rank) : D.what₂.Tau → Fin V.rank → Fin V.rank → ℂ) ∈
      frDoms (gramAt D V) (fun τ => nNeg (M.ε τ)) := by
    intro g
    have := hst _ (hAU g) (fun _ => 1) (fun _ => ⟨by simp, fun a c hac => Matrix.one_apply_ne hac.ne'⟩) _ hx0
    simp only [Matrix.mul_one] at this
    exact this
  have hc := hPd.continuousOn.comp_continuous hx hmem
  refine hc.continuousAt.congr ?_
  filter_upwards [hN] with g hg
  have e : g = h * L (A g) * ((L (A g))⁻¹ * (h⁻¹ * g)) := by group
  have e2 : (fun τ => archM V (θ τ) (L (A g))) = A g := funext (hL1 _ (hAU g)).2
  conv_rhs => rw [e, hl _ hg (hafin g), hf _ (hL1 _ (hAU g)).1, e2, hfP _ (hAU g)]
  rfl

theorem differentiableOn_prod {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {ι : Type} {s : Set F} (u : Finset ι)
    (f : ι → F → ℂ) (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) s) : DifferentiableOn ℂ (fun x => ∏ i ∈ u, f i x) s := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert a u ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

noncomputable def trFr {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {n : ℕ} {ι : Type} (e : ι ≃ Ψ) (A : ι → Mt n)
    (x : ι → Fin n → Fin n → ℂ) : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ n :=
  fun τ => (A (e.symm τ) * Matrix.of (x (e.symm τ)) : Mt n)

open ReciprocityTheory.ChartRestriction.G.FD in

theorem holSec_of_isSec {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (X : Data E n) (la : Wt X.Ψ n)
    (P : Frame X.Ψ n → ℂ) (hP : X.IsSec la P) {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ X.Ψ) (Hm : ι → Mt n)
    (q : ι → ℕ) (A : ι → Mt n)
    (hA : ∀ x ∈ frDoms Hm q, trFr e A x ∈ X.dom)
    (m : ι → ℤ) (w : ι → Fin n → ℤ) (hw : ∀ ρ a, w ρ a = la (e ρ) a + m ρ) (κ : ℂ) :
    HolSec Hm q w fun x => κ * (∏ ρ, (Matrix.of (x ρ)).det ^ m ρ) *
      P (trFr e A x) := by
  refine ⟨?_, ?_⟩
  · refine DifferentiableOn.mul (DifferentiableOn.const_mul ?_ κ) ?_
    · refine differentiableOn_prod _
        (fun (ρ : ι) (x : ι → Fin n → Fin n → ℂ) => (Matrix.of (x ρ)).det ^ m ρ) fun ρ _ => ?_
      refine DifferentiableOn.zpow (f := fun x : ι → Fin n → Fin n → ℂ => (Matrix.of (x ρ)).det) ?_
        (Or.inl fun x hx => (hx ρ).1)
      simp only [Matrix.det_apply', Matrix.of_apply]
      refine DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_mul
        (differentiableOn_prod _ (fun (i : Fin n) (x : ι → Fin n → Fin n → ℂ) => x ρ (σ i) i) fun i _ => ?_) _
      fun_prop
    · refine hP.1.comp (f := trFr e A) ?_ hA
      refine Differentiable.differentiableOn ?_
      refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun c => ?_
      simp only [trFr, Matrix.mul_apply, Matrix.of_apply]
      fun_prop
  · intro x hx b hb
    have hbB : (fun τ => b (e.symm τ) : Frame X.Ψ n) ∈ Bor X.Ψ n := fun τ => hb (e.symm τ)
    have h1 := hP.2.1 _ (hA x hx) _ hbB
    have e1 : trFr e A (fun τ => (Matrix.of (x τ) * b τ : Mt n)) = rmul (trFr e A x) (fun τ => b (e.symm τ)) := by
      funext τ
      exact (Matrix.mul_assoc (A (e.symm τ)) (Matrix.of (x (e.symm τ))) (b (e.symm τ))).symm
    have hdet : ∀ ρ, (b ρ).det = ∏ a, b ρ a a := fun ρ =>
      Matrix.det_of_upperTriangular (fun a c hac => (hb ρ).2 a c hac)
    have hne : ∀ ρ a, b ρ a a ≠ 0 := by
      intro ρ a
      have := (hb ρ).1
      rw [hdet, Finset.prod_ne_zero_iff] at this
      exact this a (Finset.mem_univ a)
    have e2 : bchar la (fun τ => b (e.symm τ) : Frame X.Ψ n) = ∏ ρ, ∏ a, b ρ a a ^ la (e ρ) a := by
      unfold bchar
      rw [← Equiv.prod_comp e]
      simp only [Equiv.symm_apply_apply]
    have e3 : ∀ ρ, (Matrix.of (Matrix.of (x ρ) * b ρ : Mt n)).det ^ m ρ =
        (Matrix.of (x ρ)).det ^ m ρ * ∏ a, b ρ a a ^ m ρ := by
      intro ρ
      have : (Matrix.of (Matrix.of (x ρ) * b ρ : Mt n)).det = (Matrix.of (x ρ)).det * (b ρ).det := Matrix.det_mul _ _
      rw [this, mul_zpow, hdet, Finset.prod_zpow]
    have e4 : (∏ ρ, ∏ a, b ρ a a ^ w ρ a) = (∏ ρ, ∏ a, b ρ a a ^ la (e ρ) a) * ∏ ρ, ∏ a, b ρ a a ^ m ρ := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun ρ _ => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [hw, zpow_add₀ (hne ρ a)]
    show κ * (∏ ρ, (Matrix.of (Matrix.of (x ρ) * b ρ : Mt n)).det ^ m ρ) *
      P (trFr e A (fun τ => (Matrix.of (x τ) * b τ : Mt n))) = _
    rw [e1, h1, e2, e4]
    simp only [e3, Finset.prod_mul_distrib]
    ring

theorem holForm_adel : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ P : FDSec X, (∀ k, (X k).IsBddSec (la k) (P k)) → HolForm θ M w (Kf : Set (GA D V)) (fun _ => 1) (adel V dict (muPin V dict mu c) P) := by
  classical
  intro D θ V S M w r hr Comp X la dict mu c Kf hM G P hP
  have hfd := GlobalTheory.T.flagDomain_frames_eq_gramFrames_unitary D θ V S M w r hr Comp X la dict mu c Kf hM G
  subst hr
  obtain ⟨th, -, hl, hk, -, hdom, -⟩ := G.unif
  obtain ⟨hmul, hnorm, hrat, hunit⟩ := G.muUnit
  have hsec : ∀ k, (X k).IsSec (la k) (P k) := fun k => (hP k).1
  have hinv : ∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (ReciprocityTheory.ChartRestriction.G.FD.lact γ x) = P k x := by
    intro k γ hγ x hx
    rw [(hsec k).2.2 γ hγ x hx, G.chi k γ hγ, one_mul]
  have hlev : ∀ k ∈ Kf, ∀ g, adel V dict (muPin V dict mu c) P (g * k) = adel V dict (muPin V dict mu c) P g := by
    intro k hk' g
    obtain ⟨γ', hγ', he⟩ := hk k hk' g
    rw [adel_muPin, adel_muPin, he, hmul, G.muK k hk', mul_one]
    exact congrArg _ (hinv _ γ' hγ' _ (hdom g))
  have hhol : HolAd θ M w (adel V dict (muPin V dict mu c) P) := by
    obtain ⟨L, -, -, -, hUG, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ V G.inf
    have horth : ∀ τ, OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) := fun τ =>
      ((GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.2.2 hM).1
    obtain ⟨-, -, hst, hx0⟩ := GlobalTheory.HolDict.frDoms_open_preconnected_stable V.rank D.what₂.Tau (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) horth
    have hst' : ∀ u ∈ UG (gramAt D V), ∀ x ∈ frDoms (gramAt D V) (fun τ => nNeg (M.ε τ)),
        (fun τ => (u τ * Matrix.of (x τ) : Mt V.rank)) ∈ frDoms (gramAt D V) (fun τ => nNeg (M.ε τ)) := by
      intro u hu x hx
      have := hst u hu (fun _ => 1) (fun _ => ⟨by simp, fun a c hac => Matrix.one_apply_ne hac.ne'⟩) _ hx
      simp only [Matrix.mul_one] at this
      exact this
    obtain ⟨m, hmu, hw⟩ := G.wt
    intro h
    obtain ⟨γ, -, -, hγ⟩ := G.base.2.2 h
    obtain ⟨e, he, hed, -⟩ := hfd (dict h).1
    have hA : ∀ x ∈ frDoms (gramAt D V) (fun τ => nNeg (M.ε τ)),
        trFr e (fun ρ => archM V (θ ρ) (γ * h)) x ∈ (X (dict h).1).dom := by
      intro x hx
      rw [hed]
      have h1 := hst' _ (hUG (γ * h)) x hx
      have h2 : (fun ρ a b => trFr e (fun ρ => archM V (θ ρ) (γ * h)) x (e ρ) (Fin.cast rfl a) (Fin.cast rfl b)) =
          fun τ => (archM V (θ τ) (γ * h) * Matrix.of (x τ) : Mt V.rank) := by
        funext ρ a b
        simp only [trFr, Equiv.symm_apply_apply, Fin.cast_eq_self]
      rw [h2]
      exact h1
    have hs := holSec_of_isSec (X (dict h).1) (la _) (P _) (hsec _) e (gramAt D V) (fun τ => nNeg (M.ε τ))
      (fun ρ => archM V (θ ρ) (γ * h)) hA m w (fun ρ a => hw _ ρ (e ρ) (he ρ) a)
      (c (dict h).1 * mu h * (∏ ρ, (x0Mat M ρ).det ^ m ρ)⁻¹)
    refine ⟨_, ⟨_, hs, fun _ _ => rfl⟩, fun u hu => ?_⟩
    obtain ⟨γ', hγ', x, hx, hxe⟩ := hγ u hu
    have hxe' : x = trFr e (fun ρ => archM V (θ ρ) (γ * h))
        (fun ρ => (archM V (θ ρ) u * x0Mat M ρ : Mt V.rank)) := by
      funext τ
      have h1 := hxe (e.symm τ) τ (by rw [← he, Equiv.apply_symm_apply])
      rw [archM_mul, Matrix.mul_assoc] at h1
      funext a b
      exact congrFun (congrFun h1 a) b
    have hxd : x ∈ (X (dict h).1).dom := by
      rw [hxe']
      exact hA _ (hst' _ (hUG u) _ hx0)
    have hne : (∏ ρ, (x0Mat M ρ).det ^ m ρ) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun ρ _ => zpow_ne_zero _ (hx0 ρ).1
    have e3 : (∏ ρ, (Matrix.of (archM V (θ ρ) u * x0Mat M ρ : Mt V.rank)).det ^ m ρ) =
        mu u * ∏ ρ, (x0Mat M ρ).det ^ m ρ := by
      rw [hmu u hu, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun ρ _ => ?_
      rw [← mul_zpow, ← Matrix.det_mul]
      rfl
    rw [adel_muPin, hx, hmul]
    show c (dict h).1 * (mu h * mu u) * P (dict h).1 (ReciprocityTheory.ChartRestriction.G.FD.lact γ' x) =
      c (dict h).1 * mu h * (∏ ρ, (x0Mat M ρ).det ^ m ρ)⁻¹ *
        (∏ ρ, (Matrix.of (archM V (θ ρ) u * x0Mat M ρ : Mt V.rank)).det ^ m ρ) *
        P (dict h).1 (trFr e (fun ρ => archM V (θ ρ) (γ * h))
          (fun ρ => (archM V (θ ρ) u * x0Mat M ρ : Mt V.rank)))
    rw [hinv _ γ' hγ' x hxd, ← hxe', e3]
    field_simp
  obtain ⟨U, hU, hUK⟩ := G.levOpen
  have hlU : ∀ k ∈ U, k ∈ GfC V → ∀ g,
      adel V dict (muPin V dict mu c) P (g * k) = adel V dict (muPin V dict mu c) P g :=
    fun k h1 h2 => hlev k (hUK k h1 h2)
  refine ⟨⟨fun γ hγ g => ?_, ⟨U, hU, hlU⟩, continuous_of_holAd G.inf hM hhol U hU hlU⟩, ?_,
    fun k hk' g => by rw [hlev k hk' g, one_mul], hhol⟩
  · obtain ⟨γ', hγ', he⟩ := hl γ hγ g
    rw [adel_muPin, adel_muPin, he, hmul, hrat γ hγ, one_mul]
    exact congrArg _ (hinv _ γ' hγ' _ (hdom g))
  · haveI := G.fin
    choose B hB using fun k => (hP k).2
    obtain ⟨B₀, hB₀⟩ := (Set.finite_range B).bddAbove
    obtain ⟨C, hC⟩ := G.cBdd
    refine ⟨C * B₀, fun g => ?_⟩
    rw [adel_muPin, norm_mul, norm_mul, hnorm, mul_one,
      ← pnorm_eq_of_unit (X (dict g).1) (la (dict g).1) (P (dict g).1) (dict g).2 (hunit g)]
    have h0 : 0 ≤ (X (dict g).1).pnorm (la (dict g).1) (P (dict g).1) (dict g).2 := by
      rw [pnorm_eq_of_unit _ _ _ _ (hunit g)]
      exact norm_nonneg _
    exact mul_le_mul (hC _) ((hB _ _ (hdom g)).trans (hB₀ ⟨_, rfl⟩)) h0 ((norm_nonneg _).trans (hC (dict g).1))

end GlobalTheory.HolDict.BackHol

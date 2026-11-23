import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.ComponentWModel
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor

noncomputable section

namespace GlobalTheory.UnitaryGlue

section General

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cT_map {R A : Type} [CommRing R] [CommRing A] (p : R →+* A) (s : R →+* R) (t : A →+* A)
    (h : ∀ z, p (s z) = t (p z)) (M : Matrix n n R) :
    (Formalism.UG.cT s M).map p = Formalism.UG.cT t (M.map p) := by
  ext i j
  simp [Formalism.UG.cT, h]

theorem exists_glue {ι R : Type} [CommRing R] {A : ι → Type} [∀ i, CommRing (A i)] (p : ∀ i, R →+* A i)
    (hp : Function.Bijective fun (z : R) (i : ι) => p i z) (s : R →+* R) (t : ∀ i, A i →+* A i)
    (h : ∀ i z, p i (s z) = t i (p i z)) (J : Matrix n n R) (g : ∀ i, GL n (A i))
    (hg : ∀ i, g i ∈ Formalism.UG.UJ (t i) (J.map (p i))) :
    ∃ x ∈ Formalism.UG.UJ s J, ∀ i, Formalism.UG.bc (p i) x = g i := by
  have inj : ∀ M N : Matrix n n R, (∀ i, M.map (p i) = N.map (p i)) → M = N := by
    intro M N hMN
    ext a b
    exact hp.1 (funext fun i => congrFun (congrFun (hMN i) a) b)
  have sur : ∀ u : ∀ i, Matrix n n (A i), ∃ M : Matrix n n R, ∀ i, M.map (p i) = u i := by
    intro u
    choose M hM using fun a b => hp.2 (fun i => u i a b)
    exact ⟨Matrix.of M, fun i => by ext a b; exact congrFun (hM a b) i⟩
  obtain ⟨M, hM⟩ := sur fun i => (g i).1
  obtain ⟨N, hN⟩ := sur fun i => ((g i)⁻¹).1
  have h1 : ∀ i, (1 : Matrix n n R).map (p i) = 1 := fun i => Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨M, N, inj _ _ fun i => ?_, inj _ _ fun i => ?_⟩, ?_, fun i => Units.ext (hM i)⟩
  · rw [Matrix.map_mul, hM, hN, h1, Units.mul_inv]
  · rw [Matrix.map_mul, hM, hN, h1, Units.inv_mul]
  · refine inj (Formalism.UG.cT s M * J * M) J fun i => ?_
    rw [Matrix.map_mul, Matrix.map_mul, cT_map (p i) s (t i) (h i), hM]
    exact hg i

theorem exists_glue₂ {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (p : R →+* A) (q : R →+* B)
    (e : R ≃+* A × B) (he : ∀ z, (e z).1 = p z ∧ (e z).2 = q z) (s : R →+* R) (t : A →+* A) (t' : B →+* B)
    (h : ∀ z, p (s z) = t (p z)) (h' : ∀ z, q (s z) = t' (q z)) (J : Matrix n n R) (g : GL n A) (g' : GL n B)
    (hg : g ∈ Formalism.UG.UJ t (J.map p)) (hg' : g' ∈ Formalism.UG.UJ t' (J.map q)) :
    ∃ x ∈ Formalism.UG.UJ s J, Formalism.UG.bc p x = g ∧ Formalism.UG.bc q x = g' := by
  have inj : ∀ M N : Matrix n n R, M.map p = N.map p → M.map q = N.map q → M = N := by
    intro M N h1 h2
    ext a b
    refine e.injective (Prod.ext ?_ ?_)
    · rw [(he _).1, (he _).1]; exact congrFun (congrFun h1 a) b
    · rw [(he _).2, (he _).2]; exact congrFun (congrFun h2 a) b
  have sur : ∀ (u : Matrix n n A) (v : Matrix n n B), ∃ M : Matrix n n R, M.map p = u ∧ M.map q = v := by
    intro u v
    refine ⟨Matrix.of fun a b => e.symm (u a b, v a b), ?_, ?_⟩
    · ext a b
      simp [← (he _).1]
    · ext a b
      simp [← (he _).2]
  obtain ⟨M, hM, hM'⟩ := sur g.1 g'.1
  obtain ⟨N, hN, hN'⟩ := sur (g⁻¹).1 (g'⁻¹).1
  have h1 : (1 : Matrix n n R).map p = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : (1 : Matrix n n R).map q = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨M, N, inj _ _ ?_ ?_, inj _ _ ?_ ?_⟩, ?_, Units.ext hM, Units.ext hM'⟩
  · rw [Matrix.map_mul, hM, hN, h1, Units.mul_inv]
  · rw [Matrix.map_mul, hM', hN', h2, Units.mul_inv]
  · rw [Matrix.map_mul, hM, hN, h1, Units.inv_mul]
  · rw [Matrix.map_mul, hM', hN', h2, Units.inv_mul]
  · refine inj (Formalism.UG.cT s M * J * M) J ?_ ?_
    · rw [Matrix.map_mul, Matrix.map_mul, cT_map p s t h, hM]
      exact hg
    · rw [Matrix.map_mul, Matrix.map_mul, cT_map q s t' h', hM']
      exact hg'

end General

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

theorem gram_det_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E) : V.gram.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have h1 : ∀ i, V.hT (V.frame i) (V.frame.equivFun.symm v) = 0 := by
    intro i
    have := congrFun hz i
    simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at this
    rw [Module.Basis.equivFun_symm_apply, map_sum, ← this]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, mul_comm]
  have h2 : V.frame.equivFun.symm v = 0 := by
    refine V.nondeg.2 _ fun x => ?_
    rw [← V.frame.sum_repr x, map_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => by
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h1, smul_zero]
  exact hv (V.frame.equivFun.symm.injective (h2.trans (map_zero _).symm))

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S]

theorem map_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (sigR R σ z) =
      sigR S σ ((Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_map_inclR (f : R →ₐ[F] S) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) :
    (J.map (inclR R)).map (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom = J.map (inclR S) := by
  ext i j
  simp [inclR]

end Tens

theorem exists_inf_fin {D : D7} (V : HSp D) (gi : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E))
    (gf : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hi : gi ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram) (hf : gf ∈ HR (Af D.host.F) D.sp.cm.sig V.gram) :
    ∃ g : GA D V, infHom V g = gi ∧ finHom V g = gf := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  obtain ⟨x, hx, h1, h2⟩ := exists_glue₂
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom e he
    (sigR _ D.sp.cm.sig) (sigR _ D.sp.cm.sig) (sigR _ D.sp.cm.sig) (map_sigR _ _) (map_sigR _ _)
    (JR (AF D.host.F) V.gram) gi gf
    (by rw [JR, map_map_inclR]; exact hi) (by rw [JR, map_map_inclR]; exact hf)
  exact ⟨⟨x, hx⟩, h1, h2⟩

theorem adelic_glue : ∀ (D : D7) (V : HSp D), (∀ gf : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E), gf ∈ HR (Af D.host.F) D.sp.cm.sig V.gram → ∃ g ∈ GfC V, finHom V g = gf) ∧ ∀ (Ψ : Finset (D.host.E →+* ℂ)) (th : Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th τ)) → (∀ g : GA D V, (∀ τ, archM V (th τ) g = 1) → g ∈ GfC V) ∧ (∀ γ ∈ GQ V, ∃ γ₀ : GL (Fin V.rank) D.host.E, (∀ τ, archM V (th τ) γ = (γ₀ : Matrix _ _ D.host.E).map τ.1) ∧ (finHom V γ).1 = (γ₀ : Matrix _ _ D.host.E).map (inclR (Af D.host.F))) ∧ (∀ τ, Continuous (archM V (th τ))) ∧ ∀ u : Ψ → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, ((u τ).map (starRingEnd ℂ)).transpose * V.gram.map τ.1 * u τ = V.gram.map τ.1) → ∃ h ∈ GinfC V, ∀ τ, archM V (th τ) h = u τ := by
  intro D V
  letI := D.host.cmStar
  refine ⟨fun gf hf => ?_, fun Ψ th hΨ hth => ?_⟩
  · obtain ⟨g, h1, h2⟩ := exists_inf_fin V 1 gf (one_mem _) hf
    exact ⟨g, h1, h2⟩
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)
  have hτ : ∀ (τ : D.host.E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := fun τ x =>
    IsCMField.complexEmbedding_complexConj D.host.E τ x
  have hc : c ≠ 1 := fun h => IsCMField.complexConj_ne_one D.host.E (AlgEquiv.ext fun x => AlgEquiv.congr_fun h x)
  obtain ⟨hex, hall⟩ := GlobalTheory.InfAdeleCM.infAdele_tensor_bijective D.host.F D.host.E c D.sp.cm.deg2 hc
    D.sp.cm.totReal hτ
  choose θ₀ hθ₀ using hex
  classical
  let θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :=
    fun τ => if h : τ ∈ Ψ then th ⟨τ, h⟩ else θ₀ τ
  have hθt : ∀ τ : Ψ, θ τ.1 = th τ := fun τ => dif_pos τ.2
  obtain ⟨hcont, hconj, hbij⟩ := hall θ (fun τ => by
    by_cases h : τ ∈ Ψ
    · rw [hθt ⟨τ, h⟩]; exact hth ⟨τ, h⟩
    · have : θ τ = θ₀ τ := dif_neg h
      rw [this]; exact hθ₀ τ)
  have hb : Function.Bijective fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : Ψ) => th τ z := by
    have := hbij (Ψ : Set _) hΨ
    have e : (fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : Ψ) => th τ z) =
        fun z (τ : Ψ) => θ τ.1 z := by
      funext z τ; rw [hθt]
    rw [e]; exact this
  have hinc : ∀ (τ : Ψ) (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
      (M.map (inclR (Ainf D.host.F))).map (th τ) = M.map τ.1 := by
    intro τ M
    ext i j
    exact (hth τ).1 _
  refine ⟨fun g hg => ?_, fun γ hγ => ?_, fun τ => ?_, fun u hu => ?_⟩
  · refine Units.ext (Matrix.ext fun a b => hb.1 (funext fun τ => ?_))
    have h1 := congrFun (congrFun (hg τ) a) b
    have h2 : (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)).map (th τ) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    exact h1.trans (congrFun (congrFun h2 a) b).symm
  · obtain ⟨γ₀, -, h0⟩ := Subgroup.mem_subgroupOf.1 hγ
    have h1 : (matHom V γ).1 = (γ₀ : Matrix _ _ D.host.E).map (inclR (AF D.host.F)) :=
      (congrArg Units.val h0).symm
    refine ⟨γ₀, fun τ => ?_, ?_⟩
    · rw [← hinc, ← map_map_inclR (fstA D.host.F), ← h1]; rfl
    · rw [← map_map_inclR (sndA D.host.F), ← h1]; rfl
  · obtain ⟨e, he, hec, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
    refine continuous_matrix fun a b => ?_
    have h1 : Continuous (th τ) := hθt τ ▸ hcont τ.1
    have h2 : Continuous fun g : GA D V => (matHom V g).1 a b :=
      (Units.continuous_val.comp continuous_subtype_val).matrix_elem a b
    have h3 : (fun g : GA D V => archM V (th τ) g a b) = fun g => th τ (e ((matHom V g).1 a b)).1 := by
      funext g
      rw [(he _).1]; rfl
    rw [h3]
    exact h1.comp (continuous_fst.comp (hec.comp h2))
  · have hdet : ∀ τ, (u τ).det ≠ 0 := by
      intro τ h0
      have := congrArg Matrix.det (hu τ)
      rw [Matrix.det_mul, h0, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
      exact gram_det_ne_zero V (τ.1.injective (by rw [map_zero, this]))
    obtain ⟨x, hx, hxu⟩ := exists_glue (A := fun _ : Ψ => ℂ) th hb (sigR _ D.sp.cm.sig) (fun _ => starRingEnd ℂ)
      (fun τ z => hθt τ ▸ hconj τ.1 z) (JR (Ainf D.host.F) V.gram)
      (fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (u τ) (hdet τ))
      (fun τ => by rw [JR, hinc]; exact hu τ)
    obtain ⟨g, h1, h2⟩ := exists_inf_fin V x 1 hx (one_mem _)
    refine ⟨g, h2, fun τ => ?_⟩
    rw [archM, h1]
    exact congrArg Units.val (hxu τ)

end GlobalTheory.UnitaryGlue

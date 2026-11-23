import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneFunctorExactness
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparison
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PotSemistableParameterCoefficientFieldEnlargeStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem charpoly_of_exact {K M₀ M M₂ : Type} [Field K] [AddCommGroup M₀] [Module K M₀] [FiniteDimensional K M₀]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M] [AddCommGroup M₂] [Module K M₂] [FiniteDimensional K M₂]
    (f : M₀ →ₗ[K] M) (p : M →ₗ[K] M₂) (hf : Function.Injective f) (hp : Function.Surjective p)
    (he : Function.Exact f p) (T₀ : End K M₀) (T : End K M) (T₂ : End K M₂) (h₀ : ∀ x, f (T₀ x) = T (f x))
    (h₂ : ∀ x, p (T x) = T₂ (p x)) : T.charpoly = T₀.charpoly * T₂.charpoly := by
  have hA : ∀ x ∈ LinearMap.ker p, T x ∈ LinearMap.ker p := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢; rw [h₂, hx, map_zero]
  rw [GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ (LinearMap.ker p) T hA]
  congr 1
  · let e : M₀ ≃ₗ[K] ↥(LinearMap.ker p) :=
      (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.1 he).symm)
    have he' : T.restrict hA = e.conj T₀ := by
      refine LinearMap.ext fun y => ?_
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      exact Subtype.ext (h₀ x).symm
    rw [he', LinearEquiv.charpoly_conj]
  · let e := p.quotKerEquivOfSurjective hp
    have he' : (LinearMap.ker p).mapQ (LinearMap.ker p) T (fun x hx => hA x hx) = e.symm.conj T₂ := by
      refine LinearMap.ext fun y => ?_
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
      rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.symm_symm]
      apply e.injective
      rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
      simp only [e, LinearMap.quotKerEquivOfSurjective_apply_mk, h₂]
      rfl
    rw [he', LinearEquiv.charpoly_conj]

private theorem wdAt_of_model {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
    {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces B) {a : ℕ}
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (L₂ : FinExt l) (r₂ : ↥(Dec (F := E) A) →* GL (Fin a) ↥L₂.1)
    (hm₂ : IsModel B r L₂ r₂) (hV₂ : IsPst P (B.repE L₂ r₂)) :
    wdAt P ι B h hj r = wdPst P ι B h hj (B.repE L₂ r₂) := by
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι B h hj (r := r) ⟨L₂, r₂, hm₂, hV₂⟩
  have h₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have h₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have e := IsModel.unique B r (hm₁.enlarge h₁) (hm₂.enlarge h₂)
  have a₁ := GlobalTheory.T.potSemistableParameter_coefficientField_enlarge P ι B h hj h₁ r₁ hV₁
  have a₂ := GlobalTheory.T.potSemistableParameter_coefficientField_enlarge P ι B h hj h₂ r₂ hV₂
  rw [e] at a₁
  exact e₁.trans (a₁.symm.trans a₂)

section Blocks

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (B : LocBridge l E Ω Gw O)

private theorem exists_model {m : ℕ} (r : ↥Gw →* GL (Fin m) (Om l)) (L : FinExt l) (hL : B.LL.1 ≤ L.1)
    (hr : ∀ g i j, (r g : Matrix (Fin m) (Fin m) (Om l)) i j ∈ L.1) : ∃ r₂, IsModel B r L r₂ := by
  let M : ↥Gw →* Matrix (Fin m) (Fin m) ↥L.1 :=
    { toFun := fun g => Matrix.of fun i j => ⟨_, hr g i j⟩
      map_one' := by
        ext i j
        simp [Matrix.one_apply, apply_ite]
      map_mul' := fun g g' => by
        ext i j
        simp [Matrix.mul_apply] }
  exact ⟨M.toHomUnits, hL, by ext g i j; rfl⟩

private theorem blocks {n : ℕ} (r : ↥Gw →* GL (Fin (n + 1)) (Om l)) (r' : ↥Gw →* GL (Fin n) (Om l))
    (ψ : ↥Gw →* (Om l)ˣ)
    (h0 : ∀ g (i : Fin n), (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Om l)) i.succ 0 = 0)
    (h1 : ∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Om l)) 0 0 = (ψ g : Om l))
    (h2 : ∀ g (i j : Fin n), (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Om l)) i.succ j.succ =
      (r' g : Matrix (Fin n) (Fin n) (Om l)) i j)
    (L : FinExt l) (r₁ : ↥Gw →* GL (Fin (n + 1)) ↥L.1) (hm : IsModel B r L r₁) :
    ∃ (r₀ : ↥Gw →* GL (Fin 1) ↥L.1) (r₂ : ↥Gw →* GL (Fin n) ↥L.1)
      (f : (Fin 1 → ↥L.1) →ₗ[↥L.1] (Fin (n + 1) → ↥L.1)) (p : (Fin (n + 1) → ↥L.1) →ₗ[↥L.1] (Fin n → ↥L.1)),
      IsModel B (GlobalTheory.TripleGal.rk1 ψ) L r₀ ∧ IsModel B r' L r₂ ∧
      (∀ g v, f (B.repE L r₀ g v) = B.repE L r₁ g (f v)) ∧ (∀ g v, p (B.repE L r₁ g v) = B.repE L r₂ g (p v)) ∧
      Function.Injective f ∧ Function.Surjective p ∧ Function.Exact f p := by
  have e₁ : ∀ g i j, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Om l)) i j =
      (((r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥L.1) i j : ↥L.1) : Om l) := fun g i j => by rw [← hm.2]; rfl
  have eψ : ∀ g i j, (GlobalTheory.TripleGal.rk1 ψ g : Matrix (Fin 1) (Fin 1) (Om l)) i j = ψ g := fun g i j => by
    rw [Subsingleton.elim j i]
    exact Matrix.diagonal_apply_eq (fun _ : Fin 1 => (ψ g : Om l)) i
  obtain ⟨r₀, m₀⟩ := exists_model B (GlobalTheory.TripleGal.rk1 ψ) L hm.1 fun g i j => by
    rw [eψ, ← h1, e₁]; exact SetLike.coe_mem _
  obtain ⟨r₂, m₂⟩ := exists_model B r' L hm.1 fun g i j => by
    rw [← h2, e₁]; exact SetLike.coe_mem _
  have k0 : ∀ g (i : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥L.1) i.succ 0 = 0 :=
    fun g i => Subtype.ext ((e₁ g _ _).symm.trans (h0 g i))
  have k1 : ∀ g, (r₀ g : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0 = (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥L.1) 0 0 :=
    fun g => Subtype.ext (by rw [← e₁, h1, ← eψ g 0 0, ← m₀.2]; rfl)
  have k2 : ∀ g i j, (r₂ g : Matrix (Fin n) (Fin n) ↥L.1) i j =
      (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥L.1) i.succ j.succ :=
    fun g i j => Subtype.ext (by rw [← e₁, h2, ← m₂.2]; rfl)
  have ap : ∀ {m : ℕ} (s : ↥Gw →* GL (Fin m) ↥L.1) g v i,
      B.repE L s g v i = ∑ j, (s (B.e.symm g) : Matrix (Fin m) (Fin m) ↥L.1) i j * v j := fun s g v i => rfl
  refine ⟨r₀, r₂, LinearMap.single ↥L.1 (fun _ => ↥L.1) 0 ∘ₗ LinearMap.proj 0, LinearMap.funLeft ↥L.1 ↥L.1 Fin.succ,
    m₀, m₂, fun g v => funext fun i => ?_, fun g v => funext fun i => ?_, fun x y hxy => funext fun i => ?_,
    LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective n), fun x => ⟨fun hx => ?_, ?_⟩⟩
  · rw [ap]
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [ap, k1, Fin.sum_univ_succ]
    · simp [k0, Fin.sum_univ_succ]
  · rw [ap, LinearMap.funLeft_apply, ap, Fin.sum_univ_succ, k0]
    simp [k2]
  · rw [Subsingleton.elim i 0]
    simpa using congrFun hxy 0
  · refine ⟨fun _ => x 0, funext fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simpa using (congrFun hx i).symm
  · rintro ⟨y, rfl⟩
    funext i
    simp

end Blocks

set_option maxHeartbeats 1000000 in
theorem UpperTheory.deRham_rational_of_extension_by_character :
    GlobalTheory.Published.DeRhamPotSemistable → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {n : ℕ} (r : ↥(Dec (F := F) A) →* GL (Fin (n + 1)) (Qbar l)) (r' : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l)) (ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous r → (∀ g (i : Fin n), (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)) i.succ 0 = 0) → (∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)) 0 0 = (ψ g : Qbar l)) → (∀ g (i j : Fin n), (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)) i.succ j.succ = (r' g : Matrix (Fin n) (Fin n) (Qbar l)) i j) → ∀ (c : (F →+* Qbar l) → ℤ) (HT : (F →+* Qbar l) → Multiset ℤ) (β : ↥(Weil h) → ℂ) (Q : ↥(Weil h) → ℂ[X]), DRat ι h r (fun τ => c τ ::ₘ HT τ) (fun s => (X - C (β s)) * Q s) → DRat ι h (GlobalTheory.TripleGal.rk1 ψ) (fun τ => {c τ}) (fun s => X - C (β s)) → DRat ι h r' HT Q := by
  intro hB F Ω _ _ _ _ _ l _ ι A w h n r r' ψ hc h0 h1 h2 c HT β Q hr hψ O _ _ _ Bw hj
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨d₁, j₁, p₁⟩ := hr O Bw hj
  obtain ⟨-, j₀, p₀⟩ := hψ O Bw hj
  have dr : ∀ {m : ℕ} (L : FinExt l) (s : ↥(Dec (F := F) A) →* GL (Fin m) ↥L.1),
      IsDR ((UpperTheory.V.Loc.PP l).PD Bw.Kw) (Bw.repE L s) ↔ Bw.IsdRE (UpperTheory.V.Loc.PP l) L s := fun L s => by
    rw [IsDR, finrank_fin_fun]; rfl
  refine ⟨?_, fun τ LL' τ' hτ => ?_, fun s => ?_⟩
  · obtain ⟨L, r₁, hm, hd⟩ := d₁
    obtain ⟨r₀, r₂, f, p, -, m₂, hf, hp, fi, ps, ex⟩ := blocks Bw r r' ψ h0 h1 h2 L r₁ hm
    exact ⟨L, r₂, m₂, (dr L r₂).1 (GlobalTheory.Per.ExactMult.exact_hodge_add l _ _ T Bw.Kw L _ _ _ _ _ _ f p hf hp
      fi ps (LinearMap.exact_iff.1 ex).symm ((dr L r₁).2 hd)).2.1⟩
  · obtain ⟨L, r₁, hm, hd, τ₁, t₁, hcount⟩ := j₁ τ LL' τ' hτ
    obtain ⟨r₀, r₂, f, p, m₀, m₂, hf, hp, fi, ps, ex⟩ := blocks Bw r r' ψ h0 h1 h2 L r₁ hm
    obtain ⟨-, d₂, hadd⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l _ _ T Bw.Kw L _ _ _ _ _ _ f p hf hp
      fi ps (LinearMap.exact_iff.1 ex).symm ((dr L r₁).2 hd)
    refine ⟨L, r₂, m₂, (dr L r₂).1 d₂, τ₁, t₁, fun a => ?_⟩
    have a₀ := IsJumpsAt.count_eq (UpperTheory.V.Loc.PP l) m₀ t₁ (j₀ τ LL' τ' hτ) a
    have a₁ := hcount a
    have a₂ : Bw.multE (UpperTheory.V.Loc.PP l) L r₁ τ₁ a = Bw.multE (UpperTheory.V.Loc.PP l) L r₀ τ₁ a + Bw.multE (UpperTheory.V.Loc.PP l) L r₂ τ₁ a :=
      (hadd τ₁ a).2.1
    beta_reduce at a₀ a₁
    rw [← Multiset.singleton_add, Multiset.count_add, Nat.cast_add, a₀, a₂] at a₁
    exact add_left_cancel a₁
  · obtain ⟨L, r₁, hm, hV⟩ := hB.isPstAt T Bw r (Units.continuous_val.comp hc) d₁
    obtain ⟨r₀, r₂, f, p, m₀, m₂, hf, hp, fi, ps, ex⟩ := blocks Bw r r' ψ h0 h1 h2 L r₁ hm
    obtain ⟨V₀, V₂, wi, ws, wex⟩ := UpperTheory.weil_deligne_functor_exactness l ι Bw.Kw L _ _ _ _ _ _ f p hf hp fi ps ex hV
    haveI := hV.finite
    haveI := V₀.finite
    haveI := V₂.finite
    have a₀ := p₀ s
    have a₁ := p₁ s
    beta_reduce at a₀ a₁
    rw [wdAt_of_model _ ι Bw h hj _ L r₀ m₀ V₀, DpstMap.charPol_wdPst _ ι Bw h hj _ V₀] at a₀
    rw [wdAt_of_model _ ι Bw h hj _ L r₁ hm hV, DpstMap.charPol_wdPst _ ι Bw h hj _ hV,
      charpoly_of_exact _ _ wi ws wex _ _ _ (DpstMap.wdLin_wdRho _ ι Bw h hj hf s)
        (DpstMap.wdLin_wdRho _ ι Bw h hj hp s), a₀] at a₁
    rw [wdAt_of_model _ ι Bw h hj _ L r₂ m₂ V₂, DpstMap.charPol_wdPst _ ι Bw h hj _ V₂]
    exact mul_left_cancel₀ (X_sub_C_ne_zero _) a₁

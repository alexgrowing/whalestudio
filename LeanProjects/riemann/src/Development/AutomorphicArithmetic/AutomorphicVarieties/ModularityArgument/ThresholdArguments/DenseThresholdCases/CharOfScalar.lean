import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.CharOfScalar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsForm

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
section General
open UpperTheory.V.Hi Polynomial
private theorem onto_inf {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (Y S : Submodule ℂ M)
    [FiniteDimensional ℂ S] (hS : S.map T = S) (hY : ∀ F ∈ Y ⊓ S, T F ∈ Y) :
    ∀ F ∈ Y ⊓ S, ∃ F' ∈ Y ⊓ S, T F' = F := by
  have h1 : ∀ F ∈ S, T F ∈ S := fun F hF => hS ▸ Submodule.mem_map_of_mem hF
  have h2 : ∀ F ∈ Y ⊓ S, T F ∈ Y ⊓ S := fun F hF => ⟨hY F hF, h1 F hF.2⟩
  have inj : Function.Injective (T.restrict h1) := by
    refine LinearMap.injective_iff_surjective.2 fun y => ?_
    obtain ⟨z, hz, e⟩ : (y : M) ∈ S.map T := hS.symm ▸ y.2
    exact ⟨⟨z, hz⟩, Subtype.ext e⟩
  haveI : FiniteDimensional ℂ (Y ⊓ S : Submodule ℂ M) := Submodule.finiteDimensional_of_le inf_le_right
  have sur : Function.Surjective (T.restrict h2) := by
    refine LinearMap.injective_iff_surjective.1 fun a b e => Subtype.ext ?_
    have : T.restrict h1 ⟨a, a.2.2⟩ = T.restrict h1 ⟨b, b.2.2⟩ := Subtype.ext (Subtype.ext_iff.1 e :)
    exact (Subtype.ext_iff.1 (inj this) :)
  intro F hF
  obtain ⟨z, e⟩ := sur ⟨F, hF⟩
  exact ⟨z, z.2, congrArg Subtype.val e⟩
private theorem kill_poly {A N : Type} [CommRing A] [AddCommGroup N] [Module A N] [Module.Finite A N]
    (U : Module.End A N) (hU : Function.Surjective U) : ∃ q : A[X], aeval U (1 + X * q) = 0 := by
  obtain ⟨r, hr, h0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul (Ideal.span {(X : A[X])})
    (⊤ : Submodule A[X] (Module.AEval' U)) Module.Finite.fg_top (fun y _ => by
      obtain ⟨z, hz⟩ := hU ((Module.AEval'.of U).symm y)
      have : y = (X : A[X]) • Module.AEval'.of U z := by
        rw [Module.AEval'.X_smul_of, hz, LinearEquiv.apply_symm_apply]
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.subset_span rfl) trivial)
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hr
  refine ⟨q, LinearMap.ext fun y => ?_⟩
  have := h0 (Module.AEval'.of U y) trivial
  rw [show r = 1 + X * q by rw [← hq]; ring, ← Module.AEval.of_aeval_smul] at this
  exact (LinearEquiv.map_eq_zero_iff _).1 this
private theorem unit_eig {A N M κ : Type} [CommRing A] [AddCommGroup N] [Module A N] [Module.Finite A N]
    [AddCommGroup M] [Module ℂ M] [NormedField κ] [IsUltrametricDist κ] (ι : κ ≃+* ℂ) (x : A →+* κ)
    (hx : ∀ a, ‖x a‖ ≤ 1) (U : Module.End A N) (hU : Function.Surjective U) (T : Module.End ℂ M)
    (s : N →ₛₗ[ι.toRingHom.comp x] M) (hs : ∀ f, s (U f) = T (s f)) {F : M}
    (hF : F ∈ Submodule.span ℂ (Set.range s)) (h0 : F ≠ 0) {μ : ℂ} (hμ : T F = μ • F) (hle : ‖ι.symm μ‖ ≤ 1) :
    ‖ι.symm μ‖ = 1 := by
  obtain ⟨q, hq⟩ := kill_poly U hU
  have hpow : ∀ (k : ℕ) f, s ((U ^ k) f) = (T ^ k) (s f) := fun k => by
    induction k with
    | zero => exact fun _ => rfl
    | succ k ih => intro f; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hs]
  have hpol : ∀ (p : A[X]) f, s (aeval U p f) = aeval T (p.map (ι.toRingHom.comp x)) (s f) := fun p f => by
    induction p using Polynomial.induction_on' with
    | add a b ha hb => simp only [map_add, Polynomial.map_add, LinearMap.add_apply, ha, hb]
    | monomial k a =>
      rw [map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
        Module.algebraMap_end_apply, Module.algebraMap_end_apply, s.map_smulₛₗ, hpow]
  have hker : Submodule.span ℂ (Set.range s) ≤ LinearMap.ker (aeval T ((1 + X * q).map (ι.toRingHom.comp x))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← hpol, hq, LinearMap.zero_apply, map_zero]
  have h1 := hker hF
  rw [LinearMap.mem_ker, Module.End.aeval_apply_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hμ, h0⟩,
    smul_eq_zero_iff_left h0, eval_map] at h1
  have h2 : (1 + X * q).eval₂ x (ι.symm μ) = 0 := by
    apply ι.injective
    have := hom_eval₂ (1 + X * q) x ι.toRingHom (ι.symm μ)
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply] at this h1
    rw [this, h1, map_zero]
  have hb : ∀ p : A[X], ‖p.eval₂ x (ι.symm μ)‖ ≤ 1 := fun p => by
    induction p using Polynomial.induction_on' with
    | add a b ha hb => rw [eval₂_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    | monomial k a =>
      rw [eval₂_monomial, norm_mul, norm_pow]
      exact mul_le_one₀ (hx a) (by positivity) (pow_le_one₀ (norm_nonneg _) hle)
  rw [eval₂_add, eval₂_one, eval₂_mul, eval₂_X, add_eq_zero_iff_neg_eq] at h2
  have h3 := congrArg norm h2
  rw [norm_neg, norm_one, norm_mul] at h3
  refine le_antisymm hle ?_
  nlinarith [hb q, norm_nonneg (ι.symm μ), norm_nonneg (q.eval₂ x (ι.symm μ))]
private theorem char_of_scalar {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (E : Submodule ℂ M) {F₀ : M} (h₀ : F₀ ∈ E) (hne : F₀ ≠ 0) (h : ∀ t, ∃ a : ℂ, ∀ F ∈ E, ρ t F = a • F) :
    ∃ φ : G →* ℂˣ, ∀ t, ∀ F ∈ E, ρ t F = (((φ t)⁻¹ : ℂˣ) : ℂ) • F := by
  choose a ha using h
  let χ : G →* ℂ :=
    { toFun := a
      map_one' := smul_left_injective ℂ hne (by simpa using (ha 1 F₀ h₀).symm)
      map_mul' := fun s t => smul_left_injective ℂ hne (by
        have := ha (s * t) F₀ h₀
        rw [map_mul, Module.End.mul_apply, ha t F₀ h₀, map_smul, ha s F₀ h₀, smul_smul, mul_comm] at this
        exact this.symm) }
  exact ⟨χ.toHomUnits⁻¹, fun t F hF => by simpa [χ] using ha t F hF⟩
private theorem uOp_factor {σ : Type} [Finite σ] [DecidableEq σ] {G : σ → Type} [∀ v, Group (G v)] (I : ∀ v, Iwa (G v))
    {M : Type} [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (∀ v, G v) M) (v : σ) {a : G v} (ha : a ∈ (I v).P) :
    Pi.mulSingle v a ∈ (piIwa I).P ∧ ∀ F ∈ fixd π (piIwa I).N,
      (piIwa I).uOp π (Pi.mulSingle v a) F = (I v).uOp (π.comp (MonoidHom.mulSingle G v)) a F := by
  classical
  have hP : Pi.mulSingle v a ∈ (piIwa I).P := fun w _ => by
    rcases eq_or_ne w v with rfl | h
    · simpa using ha
    · simpa [Pi.mulSingle_eq_of_ne h] using (I w).P.one_mem
  have hN : ∀ u ∈ (I v).N, Pi.mulSingle v u ∈ (piIwa I).N := fun u hu => (Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu
  have hc : ∀ {H : Type} [Group H] (J : Iwa H) (b y : H), y ∈ J.Nconj b ↔ b⁻¹ * y * b ∈ J.N := fun J b y =>
    ⟨by rintro ⟨z, hz, rfl⟩; simpa [mul_assoc] using hz, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩
  refine ⟨hP, fun F hF => ?_⟩
  obtain ⟨⟨s, hs, hs'⟩, hsum⟩ := uOpSum _ (I v) ℂ M (π.comp (MonoidHom.mulSingle G v)) a ha
  have key : ∀ y ∈ (piIwa I).N, ∀ u : G v, (Pi.mulSingle v u)⁻¹ * y ∈ (piIwa I).Nconj (Pi.mulSingle v a) ↔
      u⁻¹ * y v ∈ (I v).Nconj a := fun y hy u => by
    rw [hc, hc]
    refine ⟨fun h => by simpa using h v trivial, fun h w _ => ?_⟩
    rcases eq_or_ne w v with rfl | e
    · simpa using h
    · simpa [Pi.mulSingle_eq_of_ne e] using hy w trivial
  rw [(hsum s hs hs').2 F fun u hu => hF _ (hN u hu),
    ((uOpSum _ (piIwa I) ℂ M π _ hP).2 (s.image (Pi.mulSingle v)) ?_ ?_).2 F hF,
    Finset.sum_image fun _ _ _ _ e => Pi.mulSingle_injective v e]
  · exact Finset.sum_congr rfl fun u _ => by rw [← Pi.mulSingle_mul]; rfl
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hu
    exact hN w (hs w hw)
  · intro y hy
    obtain ⟨u, ⟨hu, hu'⟩, huq⟩ := hs' (y v) (hy v trivial)
    refine ⟨_, ⟨Finset.mem_image_of_mem _ hu, (key y hy u).2 hu'⟩, ?_⟩
    rintro _ ⟨hw, hw'⟩
    obtain ⟨w, hw₁, rfl⟩ := Finset.mem_image.1 hw
    rw [huq w ⟨hw₁, (key y hy w).1 hw'⟩]
variable {G M : Type} [Group G] (I : Iwa G) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
private theorem uOp_stable {Y : Submodule ℂ M} (hY : ∀ g, ∀ F ∈ Y, ρ g F ∈ Y) {a : G} (ha : a ∈ I.P) {F : M}
    (hF : F ∈ Y) (hN : F ∈ fixd ρ I.N) : I.uOp ρ a F ∈ Y := by
  obtain ⟨⟨s, hs, hs'⟩, hsum⟩ := uOpSum _ I ℂ M ρ a ha
  rw [(hsum s hs hs').2 F hN]
  exact Y.sum_mem fun u _ => hY _ F hF
private theorem onto_prod {E : Submodule ℂ M} (hE : E ≤ fixd ρ I.N) (s : List G)
    (h : ∀ a ∈ s, a ∈ I.P ∧ ∀ F ∈ E, ∃ F' ∈ E, I.uOp ρ a F' = F) :
    s.prod ∈ I.P ∧ ∀ F ∈ E, ∃ F' ∈ E, I.uOp ρ s.prod F' = F := by
  induction s with
  | nil => exact ⟨I.P.one_mem, fun F hF => ⟨F, hF, (uOpMul _ I ℂ M ρ 1 1 I.P.one_mem I.P.one_mem F (hE hF)).2.2.1⟩⟩
  | cons a s ih =>
    obtain ⟨h1, h2⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    obtain ⟨h3, h4⟩ := h a List.mem_cons_self
    refine ⟨by rw [List.prod_cons]; exact I.P.mul_mem h3 h1, fun F hF => ?_⟩
    obtain ⟨F₁, m₁, e₁⟩ := h4 F hF
    obtain ⟨F₂, m₂, e₂⟩ := h2 F₁ m₁
    exact ⟨F₂, m₂, by rw [List.prod_cons, ← (uOpMul _ I ℂ M ρ a _ h3 h1 F₂ (hE m₂)).2.1, e₂, e₁]⟩
private theorem into_inv {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) {Y E : Submodule ℂ M}
    (hEY : E ≤ Y) (c : ℕ) (φ : I.T →* ℂˣ) (hE : E ≤ I.eig ρ c φ) (hz : ∀ F ∈ E, ∃ F' ∈ E, I.uOp ρ I.z F' = F)
    (p : M →ₗ[ℂ] V) (hp : ∀ g, ∀ y ∈ Y, p (ρ g y) = π g (p y)) {F : M} (hF : F ∈ E) :
    p F ∈ ⨅ j : ℕ, (I.eig π c φ).map (I.uOp π I.z ^ j) := by
  refine (Submodule.mem_iInf _).2 fun j => ?_
  induction j generalizing F with
  | zero =>
    obtain ⟨h1, h2, h3⟩ := hE hF
    exact ⟨p F, ⟨fun u hu => by rw [← hp u F (hEY hF), h1 u hu], fun u hu => by rw [← hp u F (hEY hF), h2 u hu],
      fun t => by rw [← hp t F (hEY hF), h3 t, map_smul]⟩, rfl⟩
  | succ j ih =>
    obtain ⟨F', m, rfl⟩ := hz F hF
    obtain ⟨w, hw, e⟩ := ih m
    refine ⟨w, hw, ?_⟩
    rw [pow_succ', Module.End.mul_apply, e]
    exact (uOpNat _ I ℂ M ρ ℂ V π p.toAddMonoidHom _ I.z_mem F' fun u _ => hp _ F' (hEY m)).symm
end General
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance high] UpperTheory.V.W.coefLocal
private theorem Uc_anti (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : ℕ} (h : a ≤ b) : Uc k b ≤ Uc k a := by
  refine Subgroup.map_mono fun u hu => ?_
  rw [MonoidHom.mem_ker, Units.ext_iff] at hu ⊢
  exact (Ideal.Quotient.eq (y := 1)).2 (Ideal.pow_le_pow_right h ((Ideal.Quotient.eq (y := 1)).1 hu))
private theorem al_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) : al k n 0 = 1 := by
  rw [al, upow, ← (diagT k (Fin n)).map_one]
  congr 1
  funext i
  simp
private theorem local_step (hLit : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ (GL (Fin n) k) M) {Y E : Submodule ℂ M} (σ : SmIrr (GL (Fin n) k)) (hσ : IsoSum ρ Y σ)
    (hY : ∀ g, ∀ F ∈ Y, ρ g F ∈ Y) (hEY : E ≤ Y) {F₀ : M} (hF₀ : F₀ ∈ E) (hF₀' : F₀ ≠ 0) (e : ℕ)
    (f : Fin n → Uo k → ℂ) (hN : E ≤ fixd ρ (glIwa k n).N) (hNm : E ≤ fixd ρ ((glIwa k n).Nm e))
    (hT : ∀ i y, ∀ F ∈ E, ρ (eT k n i y) F = (f i y)⁻¹ • F)
    (htriv : ∀ i (y : Uo k), (y : kˣ) ∈ Uc k (e + 1) → f i y = 1) (hdis : ∀ i j, i ≠ j → ∃ y, f i y ≠ f j y)
    (honto : ∀ j : Fin n, ∀ F ∈ E, ∃ F' ∈ E, (glIwa k n).uOp ρ (al k n (j + 1)) F' = F) :
    ∃ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ Nonempty (σ.ρ.Equiv (PS ω)) ∧
      (∀ i (y : Uo k), (ω i y : ℂ) * f i y = 1) ∧
      ∀ j ≤ n, ∀ F ∈ E, (glIwa k n).uOp ρ (al k n j) F = psEig ω j • F := by
  obtain ⟨-, -, -, -, -, -, -, -, hz, hgen⟩ := glBridge k n M ρ
  obtain ⟨φ, hφ⟩ := char_of_scalar (ρ.comp (glIwa k n).T.subtype) E hF₀ hF₀' fun t => by
    obtain ⟨y, hy, -⟩ := hgen t
    change ∃ a : ℂ, ∀ F ∈ E, ρ t F = a • F
    rw [hy]
    refine List.prod_induction (fun g => ∃ a : ℂ, ∀ F ∈ E, ρ g F = a • F) ?_ ⟨1, by simp⟩ ?_
    · rintro g g' ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨b * a, fun F hF => by rw [map_mul, Module.End.mul_apply, hb F hF, map_smul, ha F hF, smul_smul]⟩
    · intro g hg
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
      exact ⟨_, hT i (y i)⟩
  have hval : ∀ i y, (φ (eT k n i y) : ℂ) = f i y := fun i y => by
    have := smul_left_injective ℂ hF₀' ((hφ (eT k n i y) F₀ hF₀).symm.trans (hT i y F₀ hF₀))
    rwa [Units.val_inv_eq_inv_val, inv_inj] at this
  have hzo : ∀ F ∈ E, ∃ F' ∈ E, (glIwa k n).uOp ρ (glIwa k n).z F' = F := by
    rw [hz]
    refine (onto_prod _ _ hN _ fun a ha => ?_).2
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
    refine ⟨al_mem k n j, ?_⟩
    rcases j with _ | j
    · rw [al_zero]
      exact fun F hF => ⟨F, hF, (uOpMul _ _ ℂ _ _ 1 1 (one_mem _) (one_mem _) F (hN hF)).2.2.1⟩
    · exact honto ⟨j, by have := List.mem_range.1 hj; omega⟩
  have hinv : ∀ p : M →ₗ[ℂ] σ.V, (∀ g, ∀ y ∈ Y, p (ρ g y) = σ.ρ g (p y)) → ∀ F ∈ E, p F ∈ invPart σ.ρ e φ :=
    fun p hp F hF => into_inv (glIwa k n) ρ σ.ρ hEY e φ (fun F hF => ⟨hN hF, hNm hF, fun t => hφ t F hF⟩) hzo p hp hF
  obtain ⟨p₀, hp₀, hp₀'⟩ := isoSep hσ (hEY hF₀) hF₀'
  obtain ⟨ω, h1, h2, h3, -, h4⟩ := _root_.UpperTheory.V.Hi.exists_principal_series_of_distinct_inv_ne_bot hLit k n _ σ.ρ σ.smooth σ.irred e φ
    (fun i y hy => Units.ext (by rw [hval, htriv i y hy, Units.val_one]))
    (fun i j hij => by
      obtain ⟨y, hy⟩ := hdis i j hij
      exact ⟨y, fun h => hy (by rw [← hval, ← hval, h])⟩)
    ((Submodule.ne_bot_iff _).2 ⟨_, hinv p₀ hp₀ F₀ hF₀, hp₀'⟩)
  refine ⟨ω, h1, h3, fun i y => by rw [← hval, h2 i y, Units.mul_inv], fun j hj F hF => ?_⟩
  by_contra hc
  obtain ⟨p, hp, hp'⟩ := isoSep hσ (sub_mem (uOp_stable _ _ hY (al_mem k n j) (hEY hF) (hN hF))
    (Y.smul_mem (psEig ω j) (hEY hF))) (sub_ne_zero.2 hc)
  refine hp' ?_
  rw [map_sub, map_smul, ← h4 _ (hinv p hp F hF) j hj, sub_eq_zero]
  exact uOpNat _ _ ℂ _ _ ℂ _ σ.ρ p.toAddMonoidHom _ (al_mem k n j) F fun u _ => hp _ F (hEY hF)
theorem UpperTheory.V.Hi.goodScalB_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis →
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
      (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
      (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → H.Good θ x.toRingHom lam →
    ∀ (Y : H.PartAltAlt ι lam ξ) (K : H.Lev) (e : ℕ), c0 ≤ e → Y.Y ⊓ H.OrdAt θ ι x.toRingHom lam ξ K e ≠ ⊥ →
      ∃ ω : ∀ v : H.V, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ,
        (∀ v i, IsSmoothChar (ω v i)) ∧ (∀ v, Nonempty ((Y.σl v).ρ.Equiv (PS (ω v)))) ∧
        (∀ v i (y : Uo ((H.Sl v).adicCompletion L)), (ω v i y : ℂ) * ι (H.finPart θ x.toRingHom lam v i y) = 1) ∧
        ∀ (v : H.V) (j : Fin n), ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1))‖ = 1 ∧
          ∀ F ∈ Y.Y ⊓ H.OrdAt θ ι x.toRingHom lam ξ K e,
            H.opC ι lam d (.inr (v, j)) F = ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1)) • F := by
  intro hLit L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι x lam d ξ c0 sp hsp hgood Y K e he hne
  classical
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : IsCNL A := IsCNL.ofCO c.O A
  set S := H.OrdAt θ ι x.toRingHom lam ξ K e with hSdef
  have hSC : S ≤ H.ClAt θ ι x.toRingHom lam ξ K e := iSup_le fun _ => inf_le_left
  haveI := hsp.fin K e he
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSC
  obtain ⟨F₀, hF₀, hF₀'⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨hfin, -, hbij⟩ := ordFree _ _ _ H.X A H.m (H.τA A) θ hθ.cont (H.lev K) (hH.fin K) (hθ.free K)
  let s : H.X.Ord (H.τA A) θ (H.lev K) →ₛₗ[ι.toRingHom.comp x.toRingHom] (Fin H.m → H.X.Fn ℂ d) :=
    { toFun := fun f => sp f
      map_add' := fun f g => hsp.add K f f.2 g g.2
      map_smul' := fun b f => hsp.smul K f f.2 b }
  have hspan : Submodule.span ℂ (Set.range s) = S := by
    rw [hSdef, ← hsp.span K e he, Set.image_eq_range]
    rfl
  have hfac := fun (v : H.V) (j : ℕ) => uOp_factor (fun v : H.V => glIwa ((H.Sl v).adicCompletion L) n)
    (H.X.rpF ℂ d H.m) v (al_mem _ n j)
  have hbij' := fun (v : H.V) (j : Fin n) => hbij (alV n H.Sl v (j + 1)) (hfac v (j + 1)).1
  let U : H.V → Fin n → Module.End A (H.X.Ord (H.τA A) θ (H.lev K)) := fun v j =>
    (H.op A (.inr (v, j))).restrict (hbij' v j).mapsTo
  have hU : ∀ v j, Function.Surjective (U v j) := fun v j y => by
    obtain ⟨z, hz, ez⟩ := (hbij' v j).surjOn y.2
    exact ⟨⟨z, hz⟩, Subtype.ext ez⟩
  have hsU : ∀ v j f, s (U v j f) = H.opC ι lam d (.inr (v, j)) (s f) := fun v j f => hsp.op K _ f f.2
  have hSmap : ∀ v j, S.map (H.opC ι lam d (.inr (v, j))) = S := fun v j => by
    rw [← hspan, Submodule.map_span, ← Set.range_comp, ← (hU v j).range_comp s]
    exact congrArg (fun t => Submodule.span ℂ (Set.range t)) (funext fun f => (hsU v j f).symm)
  have hY : ∀ v g, ∀ F ∈ Y.Y, H.atV d v g F ∈ Y.Y := fun v g F hF => by
    refine (iSup_le ?_ : _ ≤ Y.Y.comap (H.atV d v g)) (Y.isoL v hF)
    rintro f _ ⟨w, rfl⟩
    exact f.2.2 ⟨_, f.2.1 g w⟩
  have hN : ∀ v, Y.Y ⊓ S ≤ fixd (H.atV d v) (glIwa _ n).N := fun v F hF u hu =>
    (hSC hF.2).1.1.2 _ ((Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu)
  have hNm : ∀ v, Y.Y ⊓ S ≤ fixd (H.atV d v) ((glIwa _ n).Nm e) := fun v F hF u hu =>
    (hSC hF.2).1.2 _ ((Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu)
  have hT : ∀ v i y, ∀ F ∈ Y.Y ⊓ S,
      H.atV d v (eT _ n i y) F = (ι (H.finPart θ x.toRingHom lam v i y))⁻¹ • F := fun v i y F hF => by
    have := (hSC hF.2).2
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at this
    exact this v i y
  have hop : ∀ v (j : Fin n), ∀ F ∈ Y.Y ⊓ S, H.opC ι lam d (.inr (v, j)) F =
      (H.lowVal ι lam v (j + 1))⁻¹ • (glIwa _ n).uOp (H.atV d v) (al _ n (j + 1)) F := fun v j F hF =>
    congrArg ((H.lowVal ι lam v (j + 1))⁻¹ • ·) ((hfac v (j + 1)).2 F (hSC hF.2).1.1.2)
  have honto : ∀ v (j : Fin n), ∀ F ∈ Y.Y ⊓ S, ∃ F' ∈ Y.Y ⊓ S,
      (glIwa _ n).uOp (H.atV d v) (al _ n (j + 1)) F' = F := fun v j F hF => by
    obtain ⟨F', m, e'⟩ := onto_inf _ Y.Y S (hSmap v j) (fun F hF => by
      rw [hop v j F hF]
      exact Y.Y.smul_mem _ (uOp_stable _ _ (hY v) (al_mem _ n _) hF.1 (hN v hF))) F hF
    rw [hop v j F' m, ← map_smul] at e'
    exact ⟨_, Submodule.smul_mem _ _ m, e'⟩
  have loc := fun v => local_step hLit (H.atV d v) (Y.σl v) (Y.isoL v) (hY v) inf_le_left hF₀ hF₀' e
    (fun i y => ι (H.finPart θ x.toRingHom lam v i y)) (hN v) (hNm v) (hT v)
    (fun i y hy => by rw [hsp.triv v i y (Uc_anti _ (by omega) hy), map_one])
    (fun i j hij => (hgood.2.2 v i j hij).imp fun y hy h => hy (ι.injective h)) (honto v)
  choose ω h1 h2 h3 h4 using loc
  have heig : ∀ v (j : Fin n), ∀ F ∈ Y.Y ⊓ S, H.opC ι lam d (.inr (v, j)) F =
      ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1)) • F := fun v j F hF => by
    rw [hop v j F hF, h4 v (j + 1) j.2 F hF, smul_smul]
  obtain ⟨-, a, -, -, ha⟩ := (UpperTheory.V.GradeZeroInterpolatingElement.coPt c A).1 x
  exact ⟨ω, h1, h2, h3, fun v j => ⟨unit_eig ι x.toRingHom (fun b => by simpa using ha 0 b (by simp)) (U v j) (hU v j) _ s
    (hsU v j) (hspan.symm ▸ hF₀.2) hF₀' (heig v j F₀ hF₀)
    (hsp.int K e he _ F₀ (hSC hF₀.2) hF₀' _ (heig v j F₀ hF₀)), heig v j⟩⟩
end

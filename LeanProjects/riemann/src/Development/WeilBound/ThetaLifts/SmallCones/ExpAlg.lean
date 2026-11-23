import Development.WeilBound.ThetaLifts.SmallCones.FourierUniq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

section Gen

variable {R : Type} [CommRing R] [Invertible (2 : R)] {V : Type} [AddCommGroup V] [Module R V] {B : V → V → R} {κ : Type}
  [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ)

theorem rho_rho (a b : V) (Φ : (κ → R) → ℂ) : d.rho ψ a (d.rho ψ b Φ) = ψ (⅟(2 : R) * B a b) • d.rho ψ (a + b) Φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, map_add, d.form,
    Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add, add_assoc]
  congr 2
  have h : ⅟(2 : R) * 2 = 1 := invOf_mul_self _
  linear_combination (-((d.e a).1 ⬝ᵥ (d.e b).2)) * h

theorem rho_zero (Φ : (κ → R) → ℂ) : d.rho ψ 0 Φ = Φ := by
  funext x
  simp [Darboux.rho, schr]

theorem rho_smul (a : V) (c : ℂ) (Φ : (κ → R) → ℂ) : d.rho ψ a (c • Φ) = c • d.rho ψ a Φ := by
  funext x
  simp [Darboux.rho, schr, mul_left_comm]

theorem rho_add (a : V) (Φ Ψ : (κ → R) → ℂ) : d.rho ψ a (Φ + Ψ) = d.rho ψ a Φ + d.rho ψ a Ψ := by
  funext x
  simp [Darboux.rho, schr, mul_add]

include d in
theorem form_anti (a b : V) : B b a = -B a b := by rw [d.form, d.form]; ring

theorem rho_comm (a b : V) (Φ : (κ → R) → ℂ) : d.rho ψ a (d.rho ψ b Φ) = ψ (B a b) • d.rho ψ b (d.rho ψ a Φ) := by
  rw [rho_rho, rho_rho, smul_smul, ← AddChar.map_add_eq_mul, form_anti d a b, add_comm b a]
  congr 2
  have h : ⅟(2 : R) * 2 = 1 := invOf_mul_self _
  linear_combination (B a b) * h

theorem rho_rho_of (a b : V) (h : B a b = 0) (Φ : (κ → R) → ℂ) : d.rho ψ a (d.rho ψ b Φ) = d.rho ψ (a + b) Φ := by
  rw [rho_rho, h, mul_zero, AddChar.map_zero_eq_one, one_smul]

def formL : V →ₗ[R] V →ₗ[R] R :=
  LinearMap.mk₂ R B (fun a b c => by simp only [d.form, map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
    (fun c a b => by simp only [d.form, map_smul, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
    (fun a b c => by simp only [d.form, map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
    (fun c a b => by simp only [d.form, map_smul, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)

theorem form_eq (a b : V) : B a b = formL d a b := rfl

include d in
theorem form_sum_left {ι : Type} (s : Finset ι) (t : ι → R) (v : ι → V) (b : V) :
    B (∑ j ∈ s, t j • v j) b = ∑ j ∈ s, t j * B (v j) b := by
  simp only [form_eq d, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

include d in
theorem form_sum_right {ι : Type} (s : Finset ι) (t : ι → R) (v : ι → V) (b : V) :
    B b (∑ j ∈ s, t j • v j) = ∑ j ∈ s, t j * B b (v j) := by
  simp only [form_eq d, map_sum, map_smul, smul_eq_mul]

end Gen

theorem pure_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ) (hf : f ≠ 0)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ≠ 0 := by
  classical
  obtain ⟨yi, hyi⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  have hS : Set.Finite {v | ¬ (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)} :=
    Filter.eventually_cofinite.mp hstd
  choose p hp using fun v => Function.ne_iff.mp (h0 v)
  set S := hS.toFinset with hSdef
  let yf : κ → FiniteAdeleRing (𝓞 F) F := fun i =>
    (⟨fun v => if v ∈ S then p v i else 0, by
      apply Filter.eventually_cofinite.mpr
      refine S.finite_toSet.subset ?_
      intro v hv
      by_contra hvS
      apply hv
      have hvS' : v ∉ S := fun h => hvS (Finset.mem_coe.mpr h)
      show (if v ∈ S then p v i else 0) ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      rw [if_neg hvS']
      exact zero_mem (v.adicCompletionIntegers F)⟩ :
      RestrictedProduct (fun v : Pl F => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)
  let x : κ → AdeleRing (𝓞 F) F := fun i =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (yi i), yf i) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  intro hz
  have hx := congrFun hz x
  have h1 : (fun i => evI F (x i)) = yi := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (yi i)) = yi i
    exact RingEquiv.apply_symm_apply _ _
  have h2 : ∀ v, (fun i => evFin F v (x i)) = fun i => if v ∈ S then p v i else 0 := fun v => rfl
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.zero_apply, h1, h2] at hx
  have hg : ∀ v, v ∉ S → φ v (fun i => if v ∈ S then p v i else 0) = 1 := by
    intro v hv
    have hv' : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      by_contra h
      exact hv (hS.mem_toFinset.mpr h)
    rw [hv']
    have hzero : (fun i : κ => if v ∈ S then p v i else 0) = fun _ => 0 := funext fun i => if_neg hv
    rw [hzero, Set.indicator_of_mem (show (fun _ : κ => (0 : Fv F v)) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun i => zero_mem _)]
    rfl
  have hsub : Function.mulSupport (fun v => φ v (fun i => if v ∈ S then p v i else 0)) ⊆ S := by
    intro v hv
    by_contra h
    exact hv (hg v h)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub] at hx
  refine (mul_ne_zero hyi (Finset.prod_ne_zero_iff.mpr fun v hv => ?_)) hx
  have hpv : (fun i : κ => if v ∈ S then p v i else 0) = p v := funext fun i => if_pos hv
  rw [hpv]
  exact hp v

theorem rat_surj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (h : Module.finrank F E = 2)
    {n d : ℕ} (c : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F))
    (hc : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      c (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (y z : Fin n × Fin d → F) : ∃ x : Matrix (Fin n) (Fin d) E,
      c (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
  have hi : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective (𝓞 F) F
  let a : (Fin n × Fin d → F) →ₗ[F] (Fin n × Fin d → AF F) := (Algebra.linearMap F (AF F)).compLeft _
  have ha : Function.Injective a := fun x y e => funext fun i => hi (congrFun e i)
  let j : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    (c.toLinearMap.restrictScalars F) ∘ₗ (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).toLinearMap.mapMatrix
  have hj : Function.Injective j := c.injective.comp fun x y e => Matrix.ext fun i k =>
    Algebra.TensorProduct.includeRight_injective hi (congrFun (congrFun e i) k)
  have : LinearMap.range j = LinearMap.range (a.prodMap a) := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, z, e⟩ := hc x
      exact ⟨(y, z), e.symm⟩
    · rw [LinearMap.finrank_range_of_inj hj, LinearMap.finrank_range_of_inj (ha.prodMap ha), Module.finrank_matrix, h]
      simp [mul_two]
  exact this.ge ⟨(y, z), rfl⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem schr_mem {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) (w) {Φ} (hΦ : Φ ∈ schA F κ) :
    schr ψ w Φ ∈ schA F κ := (GlobalTheory.T.theta_distribution_heisenberg_invariant F κ ψ h.1 (std_ne_one h) h.2.1).1 w Φ hΦ

theorem theta_schr_rat {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) (y z : κ → F) (Φ) :
    thetaSum F (schr ψ (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) Φ) = thetaSum F Φ :=
  (GlobalTheory.T.theta_distribution_heisenberg_invariant F κ ψ h.1 (std_ne_one h) h.2.1).2 (y, z) Φ

variable {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
  {I : Set (Ten F E n d)} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {u z : Fin m → Matrix (Fin n) (Fin d) E}

theorem rho_mem (M : Model σ X W) (h : IsStd B.ψ) (w) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) := schr_mem h _ hΦ

theorem ev_ne_zero (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ ι ι' I e) :
    ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0 := by
  obtain ⟨ei, ev, h0, h1, h2⟩ := he.loc
  obtain ⟨f, hf⟩ := DFunLike.ne_iff.1 h0
  have hsb : ∀ v, M.vac v ∈ SB _ := fun v => (hM.vac v).1
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac, Submodule.subset_span ⟨f, _,
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV M.vac hsb hM.std,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod M.vac hsb hM.std⟩, rfl⟩, ?_⟩
  rw [h2 f M.vac hsb (Eventually.of_forall fun _ => rfl)]
  simp only [(h1 _).1]
  exact pure_ne_zero _ hf _ (fun v => (hM₁.vac v).2.1) hM₁.std

theorem lin_add (y y' : Fin m → AF F) : lin u (y + y') = lin u y + lin u y' := by
  simp [lin, add_smul, Finset.sum_add_distrib]

theorem lin_zero : lin u (0 : Fin m → AF F) = 0 := by simp [lin]

theorem e_rho_lin_eq (h : IsStd B.ψ) (he : IsEv B M M₁ ι ι' I e) (hP : Polar σ X W X₁ W₁ ι ι' I u z) (t : Fin m → AF F)
    {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) : e (M.co.rho B.ψ (lin z t) Φ) = e Φ := by
  classical
  unfold lin
  induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
  | empty => rw [Finset.sum_empty, rho_zero]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, ← rho_rho_of, he.inv _ (hP.mem j _) _ (rho_mem M h _ hΦ), ih]
    rw [form_sum_right M.co]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [form_eq M.co, map_smul, LinearMap.smul_apply, ← form_eq M.co, show symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) _ _ = 0 from hP.zz j i, smul_zero,
      mul_zero]

theorem sy_lin_uz (M : Model σ X W) (hP : Dual σ X W I u z) (y t : Fin m → AF F) :
    sy σ X W (lin u y) (lin z t) = -(y ⬝ᵥ t) := by
  show symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) _ _ = _
  rw [form_anti M.co, lin, lin, form_sum_left M.co, dotProduct_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [form_sum_right M.co]
  simp only [show ∀ j, symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F (z i)) (incM F (u j)) = _ from hP.pair i, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem sy_lin_uu (M : Model σ X W) (hP : Polar σ X W X₁ W₁ ι ι' I u z) (y t : Fin m → AF F) :
    sy σ X W (lin u y) (lin u t) = 0 := by
  show symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) _ _ = _
  rw [lin, lin, form_sum_left M.co]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [form_sum_right M.co]
  simp only [show ∀ j, symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F (u i)) (incM F (u j)) = _ from hP.uu i, mul_zero, Finset.sum_const_zero]

theorem sy_lin_um (M : Model σ X W) (hP : Polar σ X W X₁ W₁ ι ι' I u z) (y : Fin m → AF F) (w : Ten F E n₁ d₁) :
    sy σ X W (lin u y) (incM F ι * w * (incM F ι')ᵀ) = 0 := by
  show symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) _ _ = _
  rw [lin, form_sum_left M.co]
  exact Finset.sum_eq_zero fun i _ => by rw [show symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) _ _ = _ from hP.um i w, mul_zero]

theorem sy_lin_zm (M : Model σ X W) (hP : Polar σ X W X₁ W₁ ι ι' I u z) (y : Fin m → AF F) (w : Ten F E n₁ d₁) :
    sy σ X W (lin z y) (incM F ι * w * (incM F ι')ᵀ) = 0 := by
  show symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) _ _ = _
  rw [lin, form_sum_left M.co]
  exact Finset.sum_eq_zero fun i _ => by rw [show symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) _ _ = _ from hP.zm i w, mul_zero]

theorem ev_rho_uz (h : IsStd B.ψ) (he : IsEv B M M₁ ι ι' I e) (hP : Polar σ X W X₁ W₁ ι ι' I u z) (y t : Fin m → AF F)
    {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    e (M.co.rho B.ψ (lin u y) (M.co.rho B.ψ (lin z t) Φ)) = B.ψ (-(y ⬝ᵥ t)) • e (M.co.rho B.ψ (lin u y) Φ) := by
  rw [rho_comm, map_smul, e_rho_lin_eq h he hP t (rho_mem M h _ hΦ), ← sy_lin_uz M hP.toDual]

theorem ev_rho_um (h : IsStd B.ψ) (he : IsEv B M M₁ ι ι' I e) (hP : Polar σ X W X₁ W₁ ι ι' I u z) (y : Fin m → AF F)
    (w : Ten F E n₁ d₁) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    e (M.co.rho B.ψ (lin u y) (M.co.rho B.ψ (incM F ι * w * (incM F ι')ᵀ) Φ)) =
      M₁.co.rho B.ψ w (e (M.co.rho B.ψ (lin u y) Φ)) := by
  rw [rho_comm, show symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) _ _ = _ from sy_lin_um M hP y w, AddChar.map_zero_eq_one, one_smul,
    he.Heisenberg₂ _ _ (rho_mem M h _ hΦ)]

theorem incM_lin (a : Fin m → F) : incM F (∑ j, a j • u j) = lin u fun j => algebraMap F (AF F) (a j) := by
  let j : Matrix (Fin n) (Fin d) E →ₗ[F] Ten F E n d :=
    (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).toLinearMap.mapMatrix
  show j _ = _
  rw [map_sum, lin]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, algebraMap_smul]
  rfl

theorem rho_rat (h : IsStd B.ψ) (hP : Polar σ X W X₁ W₁ ι ι' I u z) (x : Matrix (Fin n) (Fin d) E) :
    ∃ (a b : Fin m → F) (x₁ : Matrix (Fin n₁) (Fin d₁) E), ∀ Φ, M.co.rho B.ψ (incM F x) Φ =
      M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (a j)) (M.co.rho B.ψ (lin z fun j => algebraMap F (AF F) (b j))
        (M.co.rho B.ψ (incM F ι * incM F x₁ * (incM F ι')ᵀ) Φ)) := by
  obtain ⟨a, b, x₁, rfl⟩ := hP.span x
  refine ⟨a, b, x₁, fun Φ => ?_⟩
  rw [rho_rho_of _ _ _ _ (sy_lin_zm M hP _ _), rho_rho, form_eq M.co, map_add, ← form_eq M.co, ← form_eq M.co,
    show symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) _ _ = _ from sy_lin_um M hP _ _, show symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) _ _ = _ from sy_lin_uz M hP.toDual _ _, add_zero,
    show ⅟(2 : AF F) * -((fun j => algebraMap F (AF F) (a j)) ⬝ᵥ fun j => algebraMap F (AF F) (b j)) =
      algebraMap F (AF F) (2⁻¹ * -(a ⬝ᵥ b)) by
      rw [show ⅟(2 : AF F) = algebraMap F (AF F) (2⁻¹ : F) from
        invOf_eq_right_inv (by rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]; norm_num)]
      simp [dotProduct], h.2.1, one_smul, ← incM_lin, ← incM_lin, ← add_assoc]
  congr 1
  simp only [incM, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.transpose_map]

end PositivityTheory.ThKCT

import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FNil

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem span_image_finBasis_eq {k E : Type} [Field k] [Ring E] [Algebra k E] [Module.Finite k E]
    (M : Submodule k E) [DecidableEq E] :
    Submodule.span k ((Finset.univ.image (fun i => ((Module.finBasis k M i : M) : E)) : Finset E) : Set E) = M := by
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.range_comp' (fun x : M => (x : E))]
  have h := Submodule.span_image (s := Set.range (Module.finBasis k M)) M.subtype
  simp only [Submodule.coe_subtype] at h
  rw [h, (Module.finBasis k M).span_eq, Submodule.map_top, Submodule.range_subtype]

private theorem fr_mul {k E : Type} [Field k] [Ring E] [Algebra k E] [Module.Finite k E]
    (M N : Submodule k E) :
    Module.finrank k ↥(M * N) ≤ Module.finrank k M * Module.finrank k N := by
  classical
  set s : Finset E := Finset.univ.image (fun i => ((Module.finBasis k M i : M) : E)) with hs
  set t : Finset E := Finset.univ.image (fun i => ((Module.finBasis k N i : N) : E)) with ht
  have hM := span_image_finBasis_eq M
  have hN := span_image_finBasis_eq N
  rw [← hs] at hM
  rw [← ht] at hN
  have hMN : M * N = Submodule.span k ((Finset.image₂ (· * ·) s t : Finset E) : Set E) := by
    rw [Finset.coe_image₂]
    conv_lhs => rw [← hM, ← hN]
    rw [Submodule.span_mul_span]
    rfl
  have hsc : s.card ≤ Module.finrank k M := by
    rw [hs]
    refine (Finset.card_image_le).trans ?_
    simp
  have htc : t.card ≤ Module.finrank k N := by
    rw [ht]
    refine (Finset.card_image_le).trans ?_
    simp
  rw [hMN]
  calc Module.finrank k ↥(Submodule.span k ((Finset.image₂ (· * ·) s t : Finset E) : Set E))
      ≤ (Finset.image₂ (· * ·) s t).card := finrank_span_finset_le_card _
    _ ≤ s.card * t.card := Finset.card_image₂_le _ _ _
    _ ≤ _ := Nat.mul_le_mul hsc htc

private theorem fr_pow {k E : Type} [Field k] [Ring E] [Algebra k E] [Module.Finite k E]
    (M : Submodule k E) (p : ℕ) :
    Module.finrank k ↥(M ^ p) ≤ Module.finrank k M ^ p := by
  classical
  induction p with
  | zero =>
    rw [pow_zero, pow_zero, Submodule.one_eq_span]
    have h := finrank_span_finset_le_card (R := k) ({1} : Finset E)
    simp only [Finset.coe_singleton, Finset.card_singleton] at h
    exact h
  | succ p ih =>
    rw [pow_succ, pow_succ]
    exact (fr_mul _ _).trans (Nat.mul_le_mul_right _ ih)

private theorem submodule_pow_le_pow_of_le {k E : Type} [Field k] [Ring E] [Algebra k E]
    (V J : Submodule k E) (hV : V ≤ J) (p : ℕ) : V ^ p ≤ J ^ p := by
  induction p with
  | zero => exact le_rfl
  | succ p ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul' ih hV

private theorem natCast_pow_le_pow_of_exponent_le {k E : Type} [Field k] [Ring E] [Algebra k E]
    (J V : Submodule k E) (hV : V ≤ J) (hJ : J ≤ V ⊔ J * J) (p : ℕ) :
    J ^ p ≤ V ^ p ⊔ J ^ (p + 1) := by
  induction p with
  | zero =>
    rw [pow_zero, pow_zero]
    exact le_sup_left
  | succ p ih =>
    have h1 : V ^ p * J ≤ V ^ (p + 1) ⊔ J ^ (p + 1 + 1) := by
      calc V ^ p * J ≤ V ^ p * (V ⊔ J * J) := mul_le_mul' le_rfl hJ
        _ = V ^ p * V ⊔ V ^ p * (J * J) := Submodule.mul_sup _ _ _
        _ ≤ V ^ (p + 1) ⊔ J ^ (p + 1 + 1) := by
          refine sup_le_sup (le_of_eq (pow_succ V p).symm) ?_
          rw [pow_succ, pow_succ, mul_assoc]
          exact mul_le_mul' (submodule_pow_le_pow_of_le V J hV p) le_rfl
    calc J ^ (p + 1) = J ^ p * J := pow_succ J p
      _ ≤ (V ^ p ⊔ J ^ (p + 1)) * J := mul_le_mul' ih le_rfl
      _ = V ^ p * J ⊔ J ^ (p + 1) * J := Submodule.sup_mul _ _ _
      _ ≤ V ^ (p + 1) ⊔ J ^ (p + 1 + 1) := by
        refine sup_le h1 ?_
        rw [← pow_succ]
        exact le_sup_right

private theorem finrank_pow_le_pow_add_finrank_pow_succ {k E : Type} [Field k] [Ring E] [Algebra k E] [Module.Finite k E]
    (J V : Submodule k E) (hV : V ≤ J) (hJ : J ≤ V ⊔ J * J) (d : ℕ) (hd : Module.finrank k V ≤ d)
    (p : ℕ) :
    Module.finrank k ↥(J ^ p) ≤ d ^ p + Module.finrank k ↥(J ^ (p + 1)) := by
  calc Module.finrank k ↥(J ^ p) ≤ Module.finrank k ↥(V ^ p ⊔ J ^ (p + 1)) :=
        Submodule.finrank_mono (natCast_pow_le_pow_of_exponent_le J V hV hJ p)
    _ ≤ Module.finrank k ↥(V ^ p) + Module.finrank k ↥(J ^ (p + 1)) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ d ^ p + Module.finrank k ↥(J ^ (p + 1)) :=
        Nat.add_le_add_right ((fr_pow V p).trans (Nat.pow_le_pow_left hd p)) _

private theorem fr_nil {k E : Type} [Field k] [Ring E] [Algebra k E] [Module.Finite k E]
    (J V : Submodule k E) (hV : V ≤ J) (hJ : J ≤ V ⊔ J * J) (d : ℕ) (hd : Module.finrank k V ≤ d)
    (m : ℕ) :
    Module.finrank k J ≤ ∑ p ∈ Finset.range (m + 1), d ^ p + Module.finrank k ↥(J ^ (m + 1)) := by
  induction m with
  | zero =>
    have h : J ^ (0 + 1) = J := by rw [zero_add, pow_one]
    rw [h]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero]
    omega
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h := finrank_pow_le_pow_add_finrank_pow_succ J V hV hJ d hd (m + 1)
    omega

private theorem lc_of_ker {G E : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Monoid E]
    (ρ : G →* E) (h : IsOpen (ρ.ker : Set G)) : IsLocallyConstant ρ := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (ρ.ker : Set G), h.preimage (continuous_mul_left x⁻¹), ?_, ?_⟩
  · simp
  · intro y hy
    simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, map_mul] at hy
    have h2 := congrArg (fun z => ρ x * z) hy
    simp only [mul_one] at h2
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul] at h2
    exact h2

private theorem idempotent_corner_eq_proj_smul {n : ℕ} {k E : Type} [Field k] [Ring E] [Algebra k E]
    (e : Fin n → E) (π : E →ₐ[k] (Fin n → k)) (hπe : ∀ i, π (e i) = Pi.single i 1)
    (hc : ∀ i x, ∃ a : k, e i * x * e i = a • e i) (i : Fin n) (x : E) :
    e i * x * e i = π x i • e i := by
  obtain ⟨a, ha⟩ := hc i x
  have h1 := congrArg (fun y => π y i) ha
  simp only [map_mul, map_smul, hπe, Pi.mul_apply, Pi.smul_apply, Pi.single_eq_same, one_mul,
    mul_one, smul_eq_mul] at h1
  rw [ha, h1]

private theorem proj_offdiag_corner_eq_zero {n : ℕ} {k E : Type} [Field k] [Ring E] [Algebra k E]
    (e : Fin n → E) (π : E →ₐ[k] (Fin n → k)) (hπe : ∀ i, π (e i) = Pi.single i 1)
    (i j : Fin n) (hij : i ≠ j) (x : E) : π (e i * x * e j) = 0 := by
  funext l
  simp only [map_mul, hπe, Pi.mul_apply, Pi.zero_apply, Pi.single_apply]
  split_ifs with h1 h2 <;> simp_all

private theorem eq_sum_idempotent_corners {n : ℕ} {E : Type} [Ring E] (e : Fin n → E)
    (hce : CompleteOrthogonalIdempotents e) (x : E) :
    x = ∑ i, ∑ j, e i * x * e j := by
  have h1 := hce.complete
  calc x = (∑ i, e i) * x * (∑ j, e j) := by rw [h1, one_mul, mul_one]
    _ = ∑ i, ∑ j, e i * x * e j := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]

private theorem dual_offdiag_corner_cocycle {n : ℕ} {k E G : Type} [Field k] [Ring E] [Algebra k E] [Group G]
    (χ : Fin n → G →* kˣ) (ρ : G →* E) (e : Fin n → E) (π : E →ₐ[k] (Fin n → k))
    (hπρ : ∀ g i, π (ρ g) i = χ i g) (hce : CompleteOrthogonalIdempotents e)
    (hπe : ∀ i, π (e i) = Pi.single i 1) (hc : ∀ i x, ∃ a : k, e i * x * e i = a • e i)
    (f : Module.Dual k E)
    (hf : ∀ y ∈ LinearMap.ker π.toLinearMap * LinearMap.ker π.toLinearMap, f y = 0)
    (i j : Fin n) (hij : i ≠ j) (g h : G) :
    f (e i * ρ (g * h) * e j) = (χ i g : k) * f (e i * ρ h * e j) + f (e i * ρ g * e j) * (χ j h : k) := by
  have hid : ∀ l, e l * e l = e l := fun l => (hce.1.idem l).eq
  have hexp : e i * ρ (g * h) * e j = ∑ l, (e i * ρ g * e l) * (e l * ρ h * e j) := by
    have h1 : e i * ρ (g * h) * e j = e i * ρ g * (∑ l, e l) * ρ h * e j := by
      rw [hce.complete, mul_one, map_mul]
      simp only [mul_assoc]
    rw [h1, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    calc e i * ρ g * e l * ρ h * e j = e i * ρ g * (e l * e l) * ρ h * e j := by rw [hid]
      _ = e i * ρ g * e l * (e l * ρ h * e j) := by simp only [mul_assoc]
  rw [hexp, map_sum, Fintype.sum_eq_add i j hij]
  · rw [idempotent_corner_eq_proj_smul e π hπe hc i (ρ g), idempotent_corner_eq_proj_smul e π hπe hc j (ρ h), hπρ, hπρ]
    rw [smul_mul_assoc, mul_smul_comm, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have t1 : e i * (e i * ρ h * e j) = e i * ρ h * e j := by
      simp only [← mul_assoc, hid]
    have t2 : e i * ρ g * e j * e j = e i * ρ g * e j := by
      rw [mul_assoc _ (e j) (e j), hid]
    rw [t1, t2, mul_comm (χ j h : k)]
  · intro l hl
    apply hf
    apply Submodule.mul_mem_mul
    · rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply]
      exact proj_offdiag_corner_eq_zero e π hπe i l (Ne.symm hl.1) _
    · rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply]
      exact proj_offdiag_corner_eq_zero e π hπe l j hl.2 _

private theorem dual_vanishes_on_ker_of_offdiag_vanishing {n : ℕ} {k E G : Type} [Field k] [Ring E] [Algebra k E] [Group G]
    (ρ : G →* E) (e : Fin n → E) (π : E →ₐ[k] (Fin n → k))
    (hspan : Submodule.span k (Set.range ρ) = ⊤) (hce : CompleteOrthogonalIdempotents e)
    (hπe : ∀ i, π (e i) = Pi.single i 1) (hc : ∀ i x, ∃ a : k, e i * x * e i = a • e i)
    (f : Module.Dual k E) (hf : ∀ i j, i ≠ j → ∀ g, f (e i * ρ g * e j) = 0)
    (x : E) (hx : π x = 0) : f x = 0 := by
  rw [eq_sum_idempotent_corners e hce x, map_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [map_sum]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  by_cases hij : i = j
  · subst hij
    rw [idempotent_corner_eq_proj_smul e π hπe hc i x, hx]
    simp
  · have hle : Submodule.span k (Set.range ρ) ≤
        LinearMap.ker (f ∘ₗ (LinearMap.mulLeft k (e i)) ∘ₗ (LinearMap.mulRight k (e j))) := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
      rw [← mul_assoc]
      exact hf i j hij g
    have hx' := hle (by rw [hspan]; exact Submodule.mem_top (x := x))
    rw [LinearMap.mem_ker] at hx'
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply] at hx'
    rw [mul_assoc]
    exact hx'

private theorem finrank_ker_le_finrank_ker_sq_add {n h : ℕ} {k E G : Type} [Field k] [Ring E] [Algebra k E] [Module.Finite k E]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (χ : Fin n → G →* kˣ) (ρ : G →* E) (e : Fin n → E) (π : E →ₐ[k] (Fin n → k))
    (hM : MultFree χ h) (hker : IsOpen (ρ.ker : Set G)) (hspan : Submodule.span k (Set.range ρ) = ⊤)
    (hπρ : ∀ g i, π (ρ g) i = χ i g) (hce : CompleteOrthogonalIdempotents e)
    (hπe : ∀ i, π (e i) = Pi.single i 1) (hc : ∀ i x, ∃ a : k, e i * x * e i = a • e i) :
    Module.finrank k ↥(LinearMap.ker π.toLinearMap) ≤
      Module.finrank k ↥(LinearMap.ker π.toLinearMap * LinearMap.ker π.toLinearMap) + n * n * h := by
  set J := LinearMap.ker π.toLinearMap with hJdef
  set A := (J * J).dualAnnihilator with hA
  haveI hfin : ∀ p : {p : Fin n × Fin n // p.1 ≠ p.2},
      Module.Finite k ↥(Z1 (χ p.1.1) (χ p.1.2)) := fun p => (hM.fin _ _ p.2).1
  have hlc := lc_of_ker ρ hker
  let Φ : ∀ p : {p : Fin n × Fin n // p.1 ≠ p.2}, Module.Dual k E →ₗ[k] (G → k) := fun p =>
    LinearMap.pi (fun g => Module.Dual.eval k E (e p.1.1 * ρ g * e p.1.2))
  have hmem : ∀ p : {p : Fin n × Fin n // p.1 ≠ p.2}, ∀ f : A,
      (Φ p ∘ₗ A.subtype) f ∈ Z1 (χ p.1.1) (χ p.1.2) := by
    intro p f
    have hf : ∀ y ∈ J * J, (f : Module.Dual k E) y = 0 := (Submodule.mem_dualAnnihilator _).1 f.2
    refine ⟨?_, ?_⟩
    · exact hlc.comp (fun v => (f : Module.Dual k E) (e p.1.1 * v * e p.1.2))
    · intro g g'
      exact dual_offdiag_corner_cocycle χ ρ e π hπρ hce hπe hc (f : Module.Dual k E) hf p.1.1 p.1.2 p.2 g g'
  let Ψ : A →ₗ[k] (∀ p : {p : Fin n × Fin n // p.1 ≠ p.2}, ↥(Z1 (χ p.1.1) (χ p.1.2))) :=
    LinearMap.pi (fun p => LinearMap.codRestrict _ (Φ p ∘ₗ A.subtype) (hmem p))
  have hkerin : ∀ f : ↥(LinearMap.ker Ψ), ((f : A) : Module.Dual k E) ∈ J.dualAnnihilator := by
    intro f
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    have h0 : Ψ (f : A) = 0 := f.2
    refine dual_vanishes_on_ker_of_offdiag_vanishing ρ e π hspan hce hπe hc _ ?_ x hx
    intro i j hij g
    have h1 := congrArg (fun F => ((F ⟨(i, j), hij⟩ : ↥(Z1 (χ i) (χ j))) : G → k) g) h0
    exact h1
  let ι : ↥(LinearMap.ker Ψ) →ₗ[k] ↥(J.dualAnnihilator) :=
    LinearMap.codRestrict _ (A.subtype ∘ₗ (LinearMap.ker Ψ).subtype) hkerin
  have hι : Function.Injective ι := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have h2 := congrArg Subtype.val hab
    exact h2
  have e1 := LinearMap.finrank_range_add_finrank_ker Ψ
  have e2 := LinearMap.finrank_le_finrank_of_injective hι
  have e3 := Subspace.finrank_add_finrank_dualAnnihilator_eq (J * J)
  have e4 := Subspace.finrank_add_finrank_dualAnnihilator_eq J
  have e5 : Module.finrank k ↥(LinearMap.range Ψ) ≤ n * n * h := by
    refine (Submodule.finrank_le _).trans ?_
    rw [Module.finrank_pi_fintype]
    calc ∑ p : {p : Fin n × Fin n // p.1 ≠ p.2}, Module.finrank k ↥(Z1 (χ p.1.1) (χ p.1.2))
        ≤ ∑ _p : {p : Fin n × Fin n // p.1 ≠ p.2}, h :=
          Finset.sum_le_sum (fun p _ => (hM.fin _ _ p.2).2)
      _ = Fintype.card {p : Fin n × Fin n // p.1 ≠ p.2} * h := by simp
      _ ≤ Fintype.card (Fin n × Fin n) * h := Nat.mul_le_mul_right _ (Fintype.card_subtype_le _)
      _ = n * n * h := by simp
  rw [← hA] at e3
  omega

theorem UpperTheory.V.CA.f_cot :
    ∀ {n h : ℕ} {k E G : Type} [Field k] [Ring E] [Algebra k E] [Module.Finite k E] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (χ : Fin n → G →* kˣ) (ρ : G →* E) (e : Fin n → E) (π : E →ₐ[k] (Fin n → k)), MultFree χ h → IsOpen (ρ.ker : Set G) → Submodule.span k (Set.range ρ) = ⊤ → (∀ g i, π (ρ g) i = χ i g) → CompleteOrthogonalIdempotents e → (∀ i, π (e i) = Pi.single i 1) → (∀ i x, ∃ a : k, e i * x * e i = a • e i) → Module.finrank k E ≤ finBound n h := by
  intro n h k E G _ _ _ _ _ _ _ χ ρ e π hM hker hspan hπρ hce hπe hc
  obtain ⟨hA, hB⟩ := f_nil e π hce hπe hc
  cases n with
  | zero =>
    have h01 : (1 : E) = 0 := by
      have := hce.complete
      simpa using this.symm
    haveI : Subsingleton E := subsingleton_of_zero_eq_one h01.symm
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  | succ m =>
    set J := LinearMap.ker π.toLinearMap with hJdef
    have hmemJ : ∀ x, x ∈ J ↔ π x = 0 := by
      intro x
      rw [hJdef, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
    have hnil : J ^ (m + 1) = ⊥ := by
      rw [Submodule.pow_eq_span_pow_set, Submodule.span_eq_bot]
      intro a ha
      obtain ⟨f, hf⟩ := Set.mem_pow.1 ha
      rw [← hf]
      exact hB (fun s => (f s : E)) (fun s => (hmemJ _).1 (f s).2)
    have hJJ : J * J ≤ J := by
      rw [Submodule.mul_le]
      intro a ha b _
      rw [hmemJ] at ha ⊢
      rw [map_mul, ha, zero_mul]
    have hdim := finrank_ker_le_finrank_ker_sq_add χ ρ e π hM hker hspan hπρ hce hπe hc
    rw [← hJdef] at hdim
    obtain ⟨q, hq⟩ := Submodule.exists_isCompl ((J * J).comap J.subtype)
    set V := q.map J.subtype with hVdef
    have hV : V ≤ J := Submodule.map_subtype_le J q
    have hJV : J ≤ V ⊔ J * J := by
      intro x hx
      have hx' : (⟨x, hx⟩ : J) ∈ (J * J).comap J.subtype ⊔ q := by
        rw [hq.sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx'
      rw [Submodule.mem_sup]
      refine ⟨(b : E), Submodule.mem_map_of_mem hb, (a : E), ha, ?_⟩
      have := congrArg Subtype.val hab
      simp only [Submodule.coe_add] at this
      rw [add_comm]
      exact this
    have hfq : Module.finrank k ↥V = Module.finrank k ↥q := Submodule.finrank_map_subtype_eq J q
    have hfc := Submodule.finrank_add_eq_of_isCompl hq
    have hfL : Module.finrank k ↥((J * J).comap J.subtype) = Module.finrank k ↥(J * J) := by
      rw [← Submodule.finrank_map_subtype_eq J, Submodule.map_comap_subtype, inf_eq_right.2 hJJ]
    have hVd : Module.finrank k ↥V ≤ (m + 1) ^ 2 * h := by
      rw [sq]
      omega
    have hfn := fr_nil J V hV hJV ((m + 1) ^ 2 * h) hVd m
    rw [hnil, finrank_bot, add_zero] at hfn
    have hrn := LinearMap.finrank_range_add_finrank_ker π.toLinearMap
    have hr : Module.finrank k ↥(LinearMap.range π.toLinearMap) ≤ m + 1 := by
      refine (Submodule.finrank_le _).trans ?_
      rw [Module.finrank_fin_fun]
    rw [← hJdef] at hrn
    unfold finBound
    omega

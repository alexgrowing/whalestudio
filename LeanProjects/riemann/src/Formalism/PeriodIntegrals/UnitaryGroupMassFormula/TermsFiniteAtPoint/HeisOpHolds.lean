import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.CarrierRow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW.HeisW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem hsym (x y : S.V) : star (S.hT x y) = S.hT y x := by
  simpa [starRingEnd_apply] using S.herm.eq x y

def kap (e a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E) (v : S.V) (c : Fin r) : E :=
  -S.hT (a c) v + ∑ d, s c d * S.hT (e d) v

def nilF (e a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E) : S.V →ₗ[E] S.V :=
  ∑ c, ((S.hT (e c)).smulRight (a c) + (-(S.hT (a c)) + ∑ d, s c d • S.hT (e d)).smulRight (e c))

theorem nilF_apply (e a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E) (v : S.V) :
    nilF e a s v = ∑ c, (S.hT (e c) v • a c + kap e a s v c • e c) := by
  simp [nilF, kap, LinearMap.sum_apply]

theorem heis_eq (e a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E) (v : S.V) :
    PI.TermsAtPtFiniteW.heisFun e a s v = v + nilF e a s v := by
  rw [nilF_apply, PI.TermsAtPtFiniteW.heisFun]
  simp only [kap, add_smul, neg_smul, Finset.sum_smul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  abel

section Nil

variable (e a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E)
  (hiso : ∀ c d, S.hT (e c) (e d) = 0) (hea : ∀ c d, S.hT (e c) (a d) = 0)
include hiso hea

omit hiso in
theorem hae (c d : Fin r) : S.hT (a c) (e d) = 0 := by
  rw [← hsym, hea, star_zero]

theorem nil_e (c : Fin r) : nilF e a s (e c) = 0 := by
  rw [nilF_apply]
  simp [kap, hiso, hae e a hea]

theorem nil_a (c : Fin r) : nilF e a s (a c) = ∑ d, kap e a s (a c) d • e d := by
  rw [nilF_apply]
  simp [hea]

theorem nil_nil (v : S.V) :
    nilF e a s (nilF e a s v) = ∑ c, S.hT (e c) v • ∑ d, kap e a s (a c) d • e d := by
  rw [nilF_apply e a s v]
  simp only [map_sum, map_add, map_smul, nil_e e a s hiso hea, nil_a e a s hiso hea, smul_zero, add_zero]

theorem nil3 (v : S.V) : nilF e a s (nilF e a s (nilF e a s v)) = 0 := by
  rw [nil_nil e a s hiso hea v]
  simp [map_sum, map_smul, nil_e e a s hiso hea]

end Nil

theorem alg (p q P Q : Fin r → E) (s G : Matrix (Fin r) (Fin r) E)
    (h : ∀ c d, s c d + star (s d c) = -G c d) :
    (∑ c, (p c * Q c + (-P c + ∑ d, star (s c d) * p d) * q c)) +
      (∑ c, (q c * P c + (-Q c + ∑ d, s c d * q d) * p c)) + ∑ c, ∑ d, p c * q d * G c d = 0 := by
  have e1 : ∑ c, (∑ d, star (s c d) * p d) * q c = ∑ c, ∑ d, p c * q d * star (s d c) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  have e2 : ∑ c, (∑ d, s c d * q d) * p c = ∑ c, ∑ d, p c * q d * s c d := by
    simp_rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  have e3 : ∑ c, ∑ d, p c * q d * star (s d c) + ∑ c, ∑ d, p c * q d * s c d +
      ∑ c, ∑ d, p c * q d * G c d = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun d _ => ?_
    have := h c d
    linear_combination (p c * q d) * this
  have e4 : ∑ c, (p c * Q c + -P c * q c) + ∑ c, (q c * P c + -Q c * p c) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun c _ => by ring
  simp only [add_mul, Finset.sum_add_distrib] at e4 ⊢
  rw [e1, e2]
  linear_combination e3 + e4

section Form

variable (e a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E)
  (hiso : ∀ c d, S.hT (e c) (e d) = 0) (hea : ∀ c d, S.hT (e c) (a d) = 0)
  (hs : ∀ c d, s c d + star (s d c) = -S.hT (a c) (a d))
include hiso hea hs

theorem form_nil (x y : S.V) :
    S.hT (nilF e a s x) y + S.hT x (nilF e a s y) + S.hT (nilF e a s x) (nilF e a s y) = 0 := by
  have E1 : S.hT (nilF e a s x) y = ∑ c, (star (S.hT (e c) x) * S.hT (a c) y +
      (-star (S.hT (a c) x) + ∑ d, star (s c d) * star (S.hT (e d) x)) * S.hT (e c) y) := by
    rw [nilF_apply]
    simp only [map_sum, map_add, map_smulₛₗ, LinearMap.sum_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [kap, star_add, star_neg, star_sum, star_mul']
    all_goals ring
  have E2 : S.hT x (nilF e a s y) = ∑ c, (S.hT (e c) y * star (S.hT (a c) x) +
      (-S.hT (a c) y + ∑ d, s c d * S.hT (e d) y) * star (S.hT (e c) x)) := by
    rw [nilF_apply]
    simp only [map_sum, map_add, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hsym, hsym]
    simp only [kap]
    all_goals ring
  have E3 : S.hT (nilF e a s x) (nilF e a s y) =
      ∑ c, ∑ d, star (S.hT (e c) x) * S.hT (e d) y * S.hT (a c) (a d) := by
    rw [nilF_apply e a s x, nilF_apply e a s y]
    simp only [map_sum, map_add, map_smulₛₗ, map_smul, LinearMap.sum_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, hiso, hea, hae e a hea, mul_zero, add_zero,
      zero_add, Finset.sum_const_zero, Finset.mul_sum, RingHom.id_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [E1, E2, E3]
  exact alg (fun c => star (S.hT (e c) x)) (fun c => S.hT (e c) y) (fun c => star (S.hT (a c) x))
    (fun c => S.hT (a c) y) s (fun c d => S.hT (a c) (a d)) hs

theorem isom_nil (x y : S.V) :
    S.hT (x + nilF e a s x) (y + nilF e a s y) = S.hT x y := by
  have h := form_nil e a s hiso hea hs x y
  simp only [map_add, LinearMap.add_apply]
  linear_combination h

end Form

theorem isO_sum {ι : Type} (t : Finset ι) (f : ι → E) (h : ∀ i ∈ t, ∃ o : 𝓞 E, (o : E) = f i) :
    ∃ o : 𝓞 E, (o : E) = ∑ i ∈ t, f i := by
  exact Finset.sum_induction f (fun z => ∃ o : 𝓞 E, (o : E) = z)
    (fun _ _ ⟨o1, h1⟩ ⟨o2, h2⟩ => ⟨o1 + o2, by
      rw [← h1, ← h2]
      first | norm_cast | simp | exact map_add (algebraMap (𝓞 E) E) o1 o2⟩)
    ⟨0, by first | simp | norm_cast⟩ h

theorem smul_memO (Λ : Submodule (𝓞 E) S.V) {k : E} (hk : ∃ o : 𝓞 E, (o : E) = k) {x : S.V} (hx : x ∈ Λ) :
    k • x ∈ Λ := by
  obtain ⟨o, rfl⟩ := hk
  have h := Λ.smul_mem o hx
  first
    | (rw [← algebraMap_smul E o x] at h; exact h)
    | simpa using h

theorem nil_mem (Λ : Submodule (𝓞 E) S.V) (e a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 E, (o : E) = S.hT x y)
    (he : ∀ c, e c ∈ Λ) (ha : ∀ c, a c ∈ Λ) (hsO : ∀ c d, ∃ o : 𝓞 E, (o : E) = s c d)
    {v : S.V} (hv : v ∈ Λ) : nilF e a s v ∈ Λ := by
  rw [nilF_apply]
  refine Submodule.sum_mem _ fun c _ =>
    Λ.add_mem (smul_memO Λ (hint _ (he c) _ hv) (ha c)) (smul_memO Λ ?_ (he c))
  obtain ⟨o1, h1⟩ := hint _ (ha c) _ hv
  obtain ⟨o2, h2⟩ := isO_sum Finset.univ (fun d => s c d * S.hT (e d) v) (fun d _ => by
    obtain ⟨x1, hx1⟩ := hsO c d
    obtain ⟨x2, hx2⟩ := hint _ (he d) _ hv
    exact ⟨x1 * x2, by
      rw [← hx1, ← hx2]
      first | norm_cast | simp | exact map_mul (algebraMap (𝓞 E) E) x1 x2⟩)
  beta_reduce at h2
  refine ⟨-o1 + o2, ?_⟩
  rw [kap, ← h1, ← h2]
  first | norm_cast | simp

end PI.TermsAtPtFiniteW.HeisW

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef HeisW

theorem heisOp_holds : HeisOp := by
  intro E _ _ _ S r T Λ F a s hint he ha hea hsO hs
  have hiso : ∀ c d, S.hT (F.fl.e c) (F.fl.e d) = 0 := F.fl.e_iso
  have h3 := nil3 F.fl.e a s hiso hea
  have hfg : (LinearMap.id + nilF F.fl.e a s) ∘ₗ
      (LinearMap.id - nilF F.fl.e a s + nilF F.fl.e a s ∘ₗ nilF F.fl.e a s) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_add, map_sub, h3]
    abel
  have hgf : (LinearMap.id - nilF F.fl.e a s + nilF F.fl.e a s ∘ₗ nilF F.fl.e a s) ∘ₗ
      (LinearMap.id + nilF F.fl.e a s) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_add, map_sub, h3]
    abel
  refine ⟨LinearEquiv.ofLinear _ _ hfg hgf, ?_, fun v => ?_⟩
  swap
  · simp [LinearEquiv.ofLinear_apply, heis_eq]
  simp only [NLam, Set.mem_setOf_eq, IsAutLam]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro x y
    simp only [LinearEquiv.ofLinear_apply, LinearMap.add_apply, LinearMap.id_apply]
    exact isom_nil F.fl.e a s hiso hea hs x y
  · unfold Formalism.HermitianLatticesTheory.gmap
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap]
      intro v hv
      simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
        LinearEquiv.ofLinear_apply, LinearMap.add_apply, LinearMap.id_apply]
      exact Λ.add_mem hv (nil_mem Λ F.fl.e a s hint he ha hsO hv)
    · intro v hv
      rw [Submodule.mem_map]
      refine ⟨v - nilF F.fl.e a s v + nilF F.fl.e a s (nilF F.fl.e a s v), ?_, ?_⟩
      · have h1 := nil_mem Λ F.fl.e a s hint he ha hsO hv
        exact Λ.add_mem (Λ.sub_mem hv h1) (nil_mem Λ F.fl.e a s hint he ha hsO h1)
      · simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, LinearEquiv.ofLinear_apply,
          LinearMap.add_apply, LinearMap.id_apply, map_add, map_sub, h3]
        abel
  · intro j x hx
    have hN : nilF F.fl.e a s x = 0 := by
      have hle : F.fl.Xa (j + 1) ≤ LinearMap.ker (nilF F.fl.e a s) := by
        show Submodule.span E (F.fl.e '' {i | i.1 < j + 1}) ≤ _
        rw [Submodule.span_le]
        rintro _ ⟨i, -, rfl⟩
        exact LinearMap.mem_ker.2 (nil_e F.fl.e a s hiso hea i)
      exact LinearMap.mem_ker.1 (hle hx)
    simp [LinearEquiv.ofLinear_apply, hN]
  · intro x hx
    have hx' : ∀ c, S.hT (F.fl.e c) x = 0 := by
      intro c
      have hmem : F.fl.e c ∈ Xsp F := by
        show F.fl.e c ∈ Submodule.span E (Set.range F.fl.e)
        exact Submodule.subset_span ⟨c, rfl⟩
      simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
      exact hx _ hmem
    simp only [LinearEquiv.ofLinear_apply, LinearMap.add_apply, LinearMap.id_apply, add_sub_cancel_left]
    rw [nilF_apply]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [hx' c, zero_smul, zero_add]
    refine Submodule.smul_mem _ _ ?_
    show F.fl.e c ∈ Submodule.span E (Set.range F.fl.e)
    exact Submodule.subset_span ⟨c, rfl⟩

end PI.TermsAtPtFiniteW

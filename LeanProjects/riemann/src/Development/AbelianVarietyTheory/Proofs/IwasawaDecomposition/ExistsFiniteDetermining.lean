import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RightTranslationActionApply

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.TopStep

section Coord

variable {K L : Type} [Field K] [Field L] (σ : K →+* L)

theorem exists_coords : ∃ (ι : Type) (e : ι → L) (c : ι → L →+ K), (∀ i k a, c i (σ k * a) = k * c i a) ∧
    ∀ a, ∃ T : Finset ι, ∀ T' : Finset ι, T ⊆ T' → ∑ i ∈ T', e i * σ (c i a) = a := by
  letI : Algebra K L := σ.toAlgebra
  let b := Module.Basis.ofVectorSpace K L
  refine ⟨_, b, fun i => (b.coord i).toAddMonoidHom, fun i k a => ?_, fun a => ⟨(b.repr a).support, fun T' hT => ?_⟩⟩
  · exact (b.coord i).map_smul k a
  · conv_rhs => rw [← b.linearCombination_repr a, Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset _ hT _ (by simp)]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

variable {I : Type}

def coefMap (c : L →+ K) (p : MvPolynomial I L) : MvPolynomial I K :=
  ∑ m ∈ p.support, MvPolynomial.monomial m (c (p.coeff m))

theorem coeff_coefMap (c : L →+ K) (p : MvPolynomial I L) (m : I →₀ ℕ) : (coefMap c p).coeff m = c (p.coeff m) := by
  classical
  simp only [coefMap, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, map_zero]

theorem coefMap_add (c : L →+ K) (p q : MvPolynomial I L) : coefMap c (p + q) = coefMap c p + coefMap c q := by
  ext m
  simp only [coeff_coefMap, MvPolynomial.coeff_add, map_add]

theorem coefMap_zero (c : L →+ K) : coefMap c (0 : MvPolynomial I L) = 0 := by
  ext m
  simp only [coeff_coefMap, MvPolynomial.coeff_zero, map_zero]

theorem coefMap_sum {J : Type*} (c : L →+ K) (s : Finset J) (p : J → MvPolynomial I L) :
    coefMap c (∑ j ∈ s, p j) = ∑ j ∈ s, coefMap c (p j) := by
  ext m
  simp only [coeff_coefMap, MvPolynomial.coeff_sum, map_sum]

variable {σ}

theorem coefMap_smul_map {c : L →+ K} (hc : ∀ k a, c (σ k * a) = k * c a) (a : L) (p : MvPolynomial I K) :
    coefMap c (a • MvPolynomial.map σ p) = c a • p := by
  ext m
  rw [coeff_coefMap, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, smul_eq_mul,
    mul_comm, hc, mul_comm]

theorem coefMap_smul {c : L →+ K} (hc : ∀ k a, c (σ k * a) = k * c a) (k : K) (p : MvPolynomial I L) :
    coefMap c (σ k • p) = k • coefMap c p := by
  ext m
  rw [coeff_coefMap, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, coeff_coefMap, smul_eq_mul, smul_eq_mul, hc]

theorem exists_sum_coefMap {ι : Type} {e : ι → L} {c : ι → L →+ K}
    (h : ∀ a, ∃ T : Finset ι, ∀ T' : Finset ι, T ⊆ T' → ∑ i ∈ T', e i * σ (c i a) = a) (p : MvPolynomial I L) :
    ∃ T : Finset ι, ∀ T' : Finset ι, T ⊆ T' → ∑ i ∈ T', e i • MvPolynomial.map σ (coefMap (c i) p) = p := by
  classical
  choose T hT using h
  refine ⟨p.support.biUnion fun m => T (p.coeff m), fun T' hT' => ?_⟩
  ext m
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, coeff_coefMap, smul_eq_mul]
  by_cases hm : m ∈ p.support
  · exact hT _ _ ((Finset.subset_biUnion_of_mem (fun m => T (p.coeff m)) hm).trans hT')
  · simp [MvPolynomial.notMem_support_iff.1 hm]

variable (σ)

theorem linearIndependent_map_pi {D J : Type*} {f : J → D → MvPolynomial I K} (hf : LinearIndependent K f) :
    LinearIndependent L fun j d => MvPolynomial.map σ (f j d) := by
  obtain ⟨ι, e, c, hc, h⟩ := exists_coords σ
  rw [linearIndependent_iff'] at hf ⊢
  intro s g hg j hj
  have h0 : ∀ i, c i (g j) = 0 := fun i => by
    refine hf s (fun j => c i (g j)) (funext fun d => ?_) j hj
    have h1 := congrArg (coefMap (c i)) (congrFun hg d)
    rw [Finset.sum_apply, coefMap_sum, Pi.zero_apply, coefMap_zero] at h1
    rw [Finset.sum_apply, Pi.zero_apply, ← h1]
    exact Finset.sum_congr rfl fun k _ => (coefMap_smul_map (hc i) _ _).symm
  obtain ⟨T, hT⟩ := h (g j)
  rw [← hT T le_rfl]
  simp [h0]

theorem VV_induction {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {P : Pol L ι n → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hs : ∀ (a : L) (v : VV K lam), P (a • MvPolynomial.map σ v.1))
    (x : Pol L ι n) (hx : x ∈ VV L lam) : P x := by
  have e : x = ∑ i, (bVV L lam).repr ⟨x, hx⟩ i • bVVfun L lam i := by
    conv_lhs => rw [show x = ((⟨x, hx⟩ : VV L lam) : Pol L ι n) from rfl, ← (bVV L lam).sum_repr ⟨x, hx⟩]
    simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe]
  rw [e]
  refine Finset.sum_induction _ P hadd h0 fun i _ => ?_
  obtain ⟨F, hF, hF'⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc σ lam i
  rw [hF']
  exact hs _ ⟨F, hF⟩

variable {σ}

theorem coefMap_mem_VV {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {c : L →+ K}
    (hc : ∀ k a, c (σ k * a) = k * c a) (x : Pol L ι n) (hx : x ∈ VV L lam) : coefMap c x ∈ VV K lam := by
  refine VV_induction σ lam (P := fun x => coefMap c x ∈ VV K lam) ?_ (fun x y hx hy => ?_) (fun a v => ?_) x hx
  · rw [coefMap_zero]; exact zero_mem _
  · rw [coefMap_add]; exact add_mem hx hy
  · rw [coefMap_smul_map hc]; exact Submodule.smul_mem _ _ v.2

end Coord

section CForms

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (σ : X.K →+* ℂ) (lam : X.Tau → DomWeight n)

theorem coefMap_rhoC {c : ℂ →+ X.K} (hc : ∀ k a, c (σ k * a) = k * c a) (γ : UF X.E n) (x : Pol ℂ X.Tau n)
    (hx : x ∈ VV ℂ lam) :
    coefMap c (rhoC σ lam γ x) = (rhoV X.emb lam (ufGL X.E n γ) ⟨coefMap c x, coefMap_mem_VV lam hc x hx⟩).1 := by
  have h : ∃ y : VV X.K lam, y.1 = coefMap c x ∧ coefMap c (rhoC σ lam γ x) = (rhoV X.emb lam (ufGL X.E n γ) y).1 := by
    refine VV_induction σ lam (P := fun x => ∃ y : VV X.K lam, y.1 = coefMap c x ∧
      coefMap c (rhoC σ lam γ x) = (rhoV X.emb lam (ufGL X.E n γ) y).1) ⟨0, (coefMap_zero c).symm, ?_⟩ ?_ ?_ x hx
    · rw [map_zero, coefMap_zero, map_zero]
      rfl
    · rintro x y ⟨u, hu, hu'⟩ ⟨v, hv, hv'⟩
      refine ⟨u + v, by rw [coefMap_add, ← hu, ← hv]; rfl, ?_⟩
      rw [map_add, coefMap_add, hu', hv', map_add]
      rfl
    · intro a v
      refine ⟨c a • v, (coefMap_smul_map hc a v.1).symm, ?_⟩
      rw [map_smul, rhoC_map, coefMap_smul_map hc, map_smul]
      rfl
  obtain ⟨y, hy, h⟩ := h
  rw [h]
  exact congrArg (fun z => (rhoV X.emb lam (ufGL X.E n γ) z).1) (Subtype.ext hy)

variable (L : DecoSet X.E n ST SG → Submodule (𝓞 X.E) (Sp X.E n)) (Λ : LevFam X.E X.K n SG)

def coordForm {c : ℂ →+ X.K} (hc : ∀ k a, c (σ k * a) = k * c a) (F : cForms ST σ lam Λ) :
    (formGSD (squarePk X lam L) Λ).EqFun :=
  ⟨fun d => ⟨coefMap c (F.1 d), coefMap_mem_VV lam hc _ (F.2 d).1⟩, fun g d => Subtype.ext <| by
    refine (congrArg (coefMap c) ((F.2 d).2 g)).trans ?_
    rw [coefMap_smul hc, coefMap_rhoC σ lam hc _ _ (F.2 d).1]
    rfl⟩

theorem toCForm_linearIndependent {J : Type*} {φ : J → (formGSD (squarePk X lam L) Λ).EqFun} (h : LinearIndependent X.K φ) :
    LinearIndependent ℂ fun j => toCForm σ lam L Λ (φ j) := by
  refine LinearIndependent.of_comp (cForms ST σ lam Λ).subtype ?_
  let i : (formGSD (squarePk X lam L) Λ).EqFun →ₗ[X.K] (DecoSet X.E n ST SG → Pol X.K X.Tau n) :=
    { toFun := fun φ d => (φ.1 d).1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hi : Function.Injective i := fun _ _ e => Subtype.ext (funext fun d => Subtype.ext (congrFun e d))
  exact linearIndependent_map_pi σ (h.map' i (LinearMap.ker_eq_bot.2 hi))

theorem exists_finite_determining (hX : X.Ok) : ∃ s : Set (DecoSet X.E n ST SG), s.Finite ∧
    ∀ F : cForms ST σ lam Λ, (∀ d ∈ s, F.1 d = 0) → F = 0 := by
  obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
  refine ⟨s, hs, fun F hF => Subtype.ext (funext fun d => ?_)⟩
  obtain ⟨d0, hd0, g, rfl⟩ := hrep d
  have h := ((mem_cForms σ lam Λ F.1).1 F.2 d0).2 g 1
  rw [hF d0 hd0, map_zero, smul_zero] at h
  exact h

theorem toCForm_span (hX : X.Ok) : Submodule.span ℂ (Set.range (toCForm σ lam L Λ)) = ⊤ := by
  classical
  obtain ⟨ι, e, c, hc, h⟩ := exists_coords σ
  obtain ⟨s, hs, hdet⟩ := exists_finite_determining (ST := ST) σ lam Λ hX
  refine eq_top_iff.2 fun F _ => ?_
  choose T hT using fun d => exists_sum_coefMap h (F.1 d)
  have e1 : F = ∑ i ∈ hs.toFinset.biUnion T, e i • toCForm σ lam L Λ (coordForm σ lam L Λ (hc i) F) := by
    refine sub_eq_zero.1 (hdet _ fun d hd => ?_)
    rw [Submodule.coe_sub, Pi.sub_apply, Submodule.coe_sum, Finset.sum_apply, sub_eq_zero]
    exact (hT d _ (Finset.subset_biUnion_of_mem T (hs.mem_toFinset.2 hd))).symm
  rw [e1]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem toCForm_span_of_span (hX : X.Ok) {J : Type*} {φ : J → (formGSD (squarePk X lam L) Λ).EqFun}
    (h : Submodule.span X.K (Set.range φ) = ⊤) : Submodule.span ℂ (Set.range fun j => toCForm σ lam L Λ (φ j)) = ⊤ := by
  refine eq_top_iff.2 ((toCForm_span σ lam L Λ hX).ge.trans (Submodule.span_le.2 ?_))
  rintro _ ⟨ψ, rfl⟩
  have hψ : ψ ∈ Submodule.span X.K (Set.range φ) := h ▸ trivial
  induction hψ using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

def basisCForm (hX : X.Ok) {J : Type*} (b : Module.Basis J X.K (formGSD (squarePk X lam L) Λ).EqFun) :
    Module.Basis J ℂ (cForms ST σ lam Λ) :=
  Module.Basis.mk (toCForm_linearIndependent σ lam L Λ b.linearIndependent) (toCForm_span_of_span σ lam L Λ hX b.span_eq).ge

theorem basisCForm_apply (hX : X.Ok) {J : Type*} (b : Module.Basis J X.K (formGSD (squarePk X lam L) Λ).EqFun) (j : J) :
    basisCForm σ lam L Λ hX b j = toCForm σ lam L Λ (b j) := Module.Basis.mk_apply _ _ _

theorem rank_cForms (hX : X.Ok) :
    Module.rank ℂ (cForms ST σ lam Λ) = Module.rank X.K (formGSD (squarePk X lam L) Λ).EqFun := by
  let b := Module.Basis.ofVectorSpace X.K (formGSD (squarePk X lam L) Λ).EqFun
  rw [← b.mk_eq_rank'', ← (basisCForm σ lam L Λ hX b).mk_eq_rank'']

theorem finrank_cForms (hX : X.Ok) :
    Module.finrank ℂ (cForms ST σ lam Λ) = Module.finrank X.K (formGSD (squarePk X lam L) Λ).EqFun :=
  congrArg Cardinal.toNat (rank_cForms σ lam L Λ hX)

end CForms

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (σ : X.K →+* ℂ)

theorem toMtilde_linearIndependent {J : Type*} {φ : J → MtildeV W Ch sel mu P} (h : LinearIndependent X.K φ) :
    LinearIndependent ℂ fun j => toMtP W Ch sel mu P σ (φ j) := toCForm_linearIndependent σ W.sgTrue _ _ h

theorem toMtilde_span (hX : X.Ok) : Submodule.span ℂ (Set.range (toMtP W Ch sel mu P σ)) = ⊤ := toCForm_span σ W.sgTrue _ _ hX

theorem finrank_MtP (hX : X.Ok) : Module.finrank ℂ (MtP W Ch sel mu P σ) = Module.finrank X.K (MtildeV W Ch sel mu P) :=
  finrank_cForms σ W.sgTrue _ _ hX

end Rows

end GlobalTheory.Mem.Col2

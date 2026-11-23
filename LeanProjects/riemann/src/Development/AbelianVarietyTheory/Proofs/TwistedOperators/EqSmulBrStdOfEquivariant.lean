import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BranchesAlongOfIrreducible
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.BranchMultOne

instance fintypeSsIdx {n : ℕ} (ν : Fin n → ℕ) : Fintype (Formalism.GradedWeylDivisibility.ssIdx n n ν) :=
  @Fintype.ofFinite _ (Formalism.GradedWeylDivisibility.sSIdxFinite n n ν).to_subtype

def bSq {n : ℕ} (lam : DomWeight n) : Module.Basis (Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) ℂ (nablaSq ℂ n lam) :=
  (Module.Basis.span (Formalism.GradedWeylDivisibility.sSBasis ℂ n n lam.natW).choose_spec.1.1).map
    (LinearEquiv.ofEq _ _ (Formalism.GradedWeylDivisibility.sSBasis ℂ n n lam.natW).choose_spec.1.2.1)

theorem bSq_coe {n : ℕ} (lam : DomWeight n) (k : Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) :
    ((bSq lam k : nablaSq ℂ n lam) : MvPolynomial (Fin n × Fin n) ℂ) = ssB ℂ lam.natW k := by
  simp [bSq, Module.Basis.span_apply, ssB]
  rfl

theorem ssB_mem {n : ℕ} (lam : DomWeight n) (k : Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) :
    ssB ℂ lam.natW k ∈ nablaSq ℂ n lam := bSq_coe lam k ▸ (bSq lam k).2

theorem sqAct_one_of_mem {n : ℕ} (lam : DomWeight n) {f : MvPolynomial (Fin n × Fin n) ℂ} (hf : f ∈ nablaSq ℂ n lam) :
    sqAct ℂ n lam 1 f = f := by
  have h := LinearMap.congr_fun (GlobalTheory.Branching.sqRep ℂ n lam).map_one ⟨f, hf⟩
  exact congrArg Subtype.val h

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def tenAt {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (τ₀ : ι) :
    MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] Pol ℂ ι n :=
  LinearMap.mulLeft ℂ (∏ τ ∈ Finset.univ.erase τ₀, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (f τ)) ∘ₗ
    (Formalism.GradedWeylDivisibility.blockEmb ℂ (k := n) (n := n) τ₀).toLinearMap

theorem tenAt_apply {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (τ₀ : ι) (x : MvPolynomial (Fin n × Fin n) ℂ) :
    tenAt f τ₀ x = ten (Function.update f τ₀ x) := by
  simp only [tenAt, ten, LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ₀), Function.update_self, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun τ hτ => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ)]

def partCoord {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (j : VVIdx lam) : VV ℂ lam →ₗ[ℂ] nablaSq ℂ n (lam τ₀) :=
  ∑ l, ((bVV ℂ lam).coord (Function.update j τ₀ l)).smulRight (bSq (lam τ₀) l)

theorem repr_partCoord {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (j : VVIdx lam) (v : VV ℂ lam) (l) :
    (bSq (lam τ₀)).repr (partCoord lam τ₀ j v) l = (bVV ℂ lam).repr v (Function.update j τ₀ l) := by
  have : partCoord lam τ₀ j v = ∑ l, (bVV ℂ lam).repr v (Function.update j τ₀ l) • bSq (lam τ₀) l := by
    simp [partCoord, LinearMap.sum_apply]
  rw [this, Module.Basis.repr_sum_self]

theorem partCoord_bVV {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (j j' : VVIdx lam) :
    partCoord lam τ₀ j (bVV ℂ lam j') = if (∀ τ, τ ≠ τ₀ → j' τ = j τ) then bSq (lam τ₀) (j' τ₀) else 0 := by
  simp only [partCoord, LinearMap.sum_apply, LinearMap.smulRight_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs with hc
  · have hj : j' = Function.update j τ₀ (j' τ₀) := by
      funext τ
      by_cases h : τ = τ₀
      · subst h; simp
      · rw [Function.update_of_ne h, hc τ h]
    rw [Finset.sum_eq_single (j' τ₀)]
    · rw [← hj]; simp
    · intro l _ hl
      rw [if_neg, zero_smul]
      intro e
      apply hl
      have := congrFun e τ₀
      simpa using this.symm
    · simp
  · refine Finset.sum_eq_zero fun l _ => ?_
    rw [if_neg, zero_smul]
    intro e
    apply hc
    intro τ h
    rw [e, Function.update_of_ne h]

end GlobalTheory.BranchMultOne

namespace GlobalTheory.BranchMultOne

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem rhoK_update_bVV {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (g : GL (Fin n) ℂ) (j : VVIdx lam) :
    rhoK lam (Function.update 1 τ₀ g) (bVV ℂ lam j) =
      ∑ l, (bSq (lam τ₀)).repr (GlobalTheory.Branching.sqRep ℂ n (lam τ₀) g (bSq (lam τ₀) (j τ₀))) l •
        bVV ℂ lam (Function.update j τ₀ l) := by
  apply Subtype.ext
  rw [rhoK_coe, bVV_coe, bVVfun, actTen ℂ ι n lam _ _]
  have e1 : (fun τ => sqAct ℂ n (lam τ) (Function.update (1 : ι → GL (Fin n) ℂ) τ₀ g τ) (ssB ℂ (lam τ).natW (j τ))) =
      Function.update (fun τ => ssB ℂ (lam τ).natW (j τ)) τ₀ (sqAct ℂ n (lam τ₀) g (ssB ℂ (lam τ₀).natW (j τ₀))) := by
    funext τ
    by_cases h : τ = τ₀
    · subst h; simp
    · rw [Function.update_of_ne h, Function.update_of_ne h]; exact sqAct_one_of_mem _ (ssB_mem _ _)
  rw [e1, ← tenAt_apply]
  have e2 : sqAct ℂ n (lam τ₀) g (ssB ℂ (lam τ₀).natW (j τ₀)) = ∑ l, (bSq (lam τ₀)).repr
      (GlobalTheory.Branching.sqRep ℂ n (lam τ₀) g (bSq (lam τ₀) (j τ₀))) l • ssB ℂ (lam τ₀).natW l := by
    have h := (bSq (lam τ₀)).sum_repr (GlobalTheory.Branching.sqRep ℂ n (lam τ₀) g (bSq (lam τ₀) (j τ₀)))
    have h2 := congrArg Subtype.val h
    simp only [Submodule.coe_sum, Submodule.coe_smul, bSq_coe, GlobalTheory.Branching.sqRep_coe] at h2
    exact h2.symm
  rw [e2, map_sum, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, Submodule.coe_smul, bVV_coe, bVVfun, tenAt_apply]
  congr 2
  funext τ
  exact (Function.apply_update (fun τ k => ssB ℂ (lam τ).natW k) j τ₀ l τ).symm

theorem partCoord_rhoK {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (j : VVIdx lam) (g : GL (Fin n) ℂ) (v : VV ℂ lam) :
    partCoord lam τ₀ j (rhoK lam (Function.update 1 τ₀ g) v) =
      GlobalTheory.Branching.sqRep ℂ n (lam τ₀) g (partCoord lam τ₀ j v) := by
  have key : partCoord lam τ₀ j ∘ₗ rhoK lam (Function.update 1 τ₀ g) =
      GlobalTheory.Branching.sqRep ℂ n (lam τ₀) g ∘ₗ partCoord lam τ₀ j := by
    refine (bVV ℂ lam).ext fun j' => ?_
    simp only [LinearMap.comp_apply, rhoK_update_bVV, map_sum, map_smul, partCoord_bVV]
    have hc : ∀ l, ((∀ τ, τ ≠ τ₀ → Function.update j' τ₀ l τ = j τ) ↔ (∀ τ, τ ≠ τ₀ → j' τ = j τ)) := fun l =>
      forall_congr' fun τ => imp_congr_right fun h => by rw [Function.update_of_ne h]
    by_cases h : ∀ τ, τ ≠ τ₀ → j' τ = j τ
    · rw [if_pos h]
      have e : ∀ l, (if (∀ τ, τ ≠ τ₀ → Function.update j' τ₀ l τ = j τ) then
          bSq (lam τ₀) (Function.update j' τ₀ l τ₀) else 0) = bSq (lam τ₀) l := fun l => by
        rw [if_pos ((hc l).2 h), Function.update_self]
      simp only [e]
      exact (bSq (lam τ₀)).sum_repr _
    · rw [if_neg h, map_zero]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [if_neg (fun h' => h ((hc l).1 h')), smul_zero]
  exact LinearMap.congr_fun key v

def factorIncl {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (i : VVIdx lam) : nablaSq ℂ n (lam τ₀) →ₗ[ℂ] VV ℂ lam :=
  LinearMap.codRestrict (VV ℂ lam) (tenAt (fun τ => ssB ℂ (lam τ).natW (i τ)) τ₀ ∘ₗ (nablaSq ℂ n (lam τ₀)).subtype)
    fun x => by
      rw [LinearMap.comp_apply, tenAt_apply]
      refine GlobalTheory.Proof.TensorMapDescent.ten_mem lam _ fun τ => ?_
      by_cases h : τ = τ₀
      · subst h; simpa using x.2
      · rw [Function.update_of_ne h]; exact ssB_mem _ _

theorem factorIncl_coe {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (i : VVIdx lam) (x : nablaSq ℂ n (lam τ₀)) :
    (factorIncl lam τ₀ i x : Pol ℂ ι n) = ten (Function.update (fun τ => ssB ℂ (lam τ).natW (i τ)) τ₀ (x : MvPolynomial (Fin n × Fin n) ℂ)) := by
  simp [factorIncl, tenAt_apply]

theorem factorIncl_bSq {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (i : VVIdx lam) (k) :
    factorIncl lam τ₀ i (bSq (lam τ₀) k) = bVV ℂ lam (Function.update i τ₀ k) := by
  apply Subtype.ext
  rw [factorIncl_coe, bSq_coe, bVV_coe, bVVfun]
  congr 1
  funext τ
  exact (Function.apply_update (fun τ k => ssB ℂ (lam τ).natW k) i τ₀ k τ).symm

theorem factorIncl_sqRep {n : ℕ} (lam : ι → DomWeight n) (τ₀ : ι) (i : VVIdx lam) (G : GL (Fin n) ℂ) (x : nablaSq ℂ n (lam τ₀)) :
    factorIncl lam τ₀ i (GlobalTheory.Branching.sqRep ℂ n (lam τ₀) G x) = rhoK lam (Function.update 1 τ₀ G) (factorIncl lam τ₀ i x) := by
  apply Subtype.ext
  rw [rhoK_coe, factorIncl_coe, factorIncl_coe, actTen ℂ ι n lam _ _]
  congr 1
  funext τ
  by_cases h : τ = τ₀
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne h, Function.update_of_ne h, Pi.one_apply,
      sqAct_one_of_mem _ (ssB_mem _ _)]

end GlobalTheory.BranchMultOne

namespace GlobalTheory.BranchMultOne

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem eq_mul_prod_of_slices {X : ι → Type} (m : ∀ τ, X τ → ℂ) (M : (∀ τ, X τ) → ℂ)
    (h : ∀ τ ω, ∃ c, ∀ x, M (Function.update ω τ x) = c * m τ x) :
    ∃ C, ∀ ω, M ω = C * ∏ τ, m τ (ω τ) := by
  by_cases hz : ∃ τ, ∀ x, m τ x = 0
  · obtain ⟨τ, hτ⟩ := hz
    refine ⟨0, fun ω => ?_⟩
    obtain ⟨c, hc⟩ := h τ ω
    have := hc (ω τ)
    rw [Function.update_eq_self, hτ, mul_zero] at this
    rw [this, zero_mul]
  push_neg at hz
  choose xs hxs using hz
  have hP : (∏ τ, m τ (xs τ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => hxs τ
  have hp : ∀ (ω : ∀ τ, X τ) (a : ι) (y : X a),
      ∏ τ, m τ (Function.update ω a y τ) = m a y * ∏ τ ∈ Finset.univ.erase a, m τ (ω τ) := by
    intro ω a y
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun τ hτ => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ)]
  refine ⟨M xs / ∏ τ, m τ (xs τ), ?_⟩
  suffices H : ∀ s : Finset ι, ∀ ω : (∀ τ, X τ), (∀ τ, τ ∉ s → ω τ = xs τ) →
      M ω = M xs / (∏ τ, m τ (xs τ)) * ∏ τ, m τ (ω τ) from fun ω => H Finset.univ ω (by simp)
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro ω hω
    have : ω = xs := funext fun τ => hω τ (by simp)
    subst this
    field_simp
  · intro a s ha ih ω hω
    have h1 : M (Function.update ω a (xs a)) =
        M xs / (∏ τ, m τ (xs τ)) * ∏ τ, m τ (Function.update ω a (xs a) τ) := ih _ fun τ hτ => by
      by_cases e : τ = a
      · subst e; simp
      · rw [Function.update_of_ne e]; exact hω τ (by simp [e, hτ])
    obtain ⟨c, hc⟩ := h a ω
    have h2 : M ω = c * m a (ω a) := by simpa using hc (ω a)
    have h3 := hc (xs a)
    rw [h1, hp] at h3
    have hω_eq : ∏ τ, m τ (ω τ) = m a (ω a) * ∏ τ ∈ Finset.univ.erase a, m τ (ω τ) := by
      simpa using hp ω a (ω a)
    have hc' : c = M xs / (∏ τ, m τ (xs τ)) * ∏ τ ∈ Finset.univ.erase a, m τ (ω τ) := by
      apply mul_right_cancel₀ (hxs a)
      rw [← h3]; ring
    rw [h2, hω_eq, hc']
    ring

variable {N n : ℕ}

def brOneRep (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (hI : Formalism.L2.Col.Br.Interlace hN lam sg)
    (hS : Formalism.L2.Col.Br.SameShift lam sg) :
    (GlobalTheory.Branching.resRep (MonoidHom.id (GL (Fin n) ℂ)) hN.symm lam).IntertwiningMap
      (GlobalTheory.Branching.smallRep (MonoidHom.id (GL (Fin n) ℂ)) sg) :=
  ⟨(GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ hN lam sg).restrict fun f _ => GlobalTheory.BranchFormula.brOne_mem hN lam sg f,
   fun g => LinearMap.ext fun f => Subtype.ext (GlobalTheory.BranchFormula.brOne_sqAct hN hI hS g f.2)⟩

theorem brOneRep_coe (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (hI : Formalism.L2.Col.Br.Interlace hN lam sg)
    (hS : Formalism.L2.Col.Br.SameShift lam sg) (f : nablaSq ℂ N lam) :
    (((brOneRep hN lam sg hI hS).toLinearMap f : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ) =
      GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ hN lam sg f := rfl

theorem brOneRep_ne_zero (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (hI : Formalism.L2.Col.Br.Interlace hN lam sg)
    (hS : Formalism.L2.Col.Br.SameShift lam sg) : brOneRep hN lam sg hI hS ≠ 0 := by
  intro h0
  apply Formalism.L2.Ker.brStd_ne_zero (K := ℂ) hN (fun _ : Unit => lam) (fun _ : Unit => sg) (fun _ => hI) (fun _ => hS)
  refine LinearMap.ext fun G => Subtype.ext ?_
  obtain ⟨f, hf, e⟩ := GlobalTheory.BranchFormula.exists_ten_unit G.2
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ hN lam sg f = 0 := by
    have := brOneRep_coe hN lam sg hI hS ⟨f, hf⟩
    rw [h0] at this
    exact this.symm
  rw [GlobalTheory.BranchFormula.tensor ℂ Unit N n hN _ _ (fun _ => hI) (fun _ => hS) (fun _ => f) G (fun _ => hf) e, hz]
  simp [ten]

end GlobalTheory.BranchMultOne

namespace GlobalTheory.BranchMultOne

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N n : ℕ}

def brEntry (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (hI : Formalism.L2.Col.Br.Interlace hN lam sg)
    (hS : Formalism.L2.Col.Br.SameShift lam sg) (l : Formalism.GradedWeylDivisibility.ssIdx n n sg.natW) (k : Formalism.GradedWeylDivisibility.ssIdx N N lam.natW) : ℂ :=
  (bSq sg).repr ((brOneRep hN lam sg hI hS).toLinearMap (bSq lam k)) l

theorem brStd_bVV (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n)
    (hI : ∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) (hS : ∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) (i : VVIdx Λ) :
    Formalism.L2.Col.Br.brStd hN Λ σ (bVV ℂ Λ i) =
      ∑ j : VVIdx σ, (∏ τ, brEntry hN (Λ τ) (σ τ) (hI τ) (hS τ) (j τ) (i τ)) • bVV ℂ σ j := by
  apply Subtype.ext
  rw [GlobalTheory.BranchFormula.tensor ℂ ι N n hN Λ σ hI hS (fun τ => ssB ℂ (Λ τ).natW (i τ)) _ (fun τ => ssB_mem _ _)
    (by rw [bVV_coe, bVVfun])]
  have e : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ hN (Λ τ) (σ τ) (ssB ℂ (Λ τ).natW (i τ)) =
      ∑ l, brEntry hN (Λ τ) (σ τ) (hI τ) (hS τ) l (i τ) • ssB ℂ (σ τ).natW l := by
    intro τ
    have h := congrArg Subtype.val ((bSq (σ τ)).sum_repr ((brOneRep hN (Λ τ) (σ τ) (hI τ) (hS τ)).toLinearMap
      (bSq (Λ τ) (i τ))))
    simp only [Submodule.coe_sum, Submodule.coe_smul, bSq_coe, brOneRep_coe] at h
    rw [← h]
    rfl
  simp only [e, ten, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, bVV_coe, bVVfun]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr (by congr 1; exact Subsingleton.elim _ _) fun x _ => ?_
  simp only [MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]

end GlobalTheory.BranchMultOne

namespace GlobalTheory.BranchMultOne

theorem resRep_id_apply {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (g : GL (Fin n) ℂ) (x : nablaSq ℂ N lam) :
    GlobalTheory.Branching.resRep (MonoidHom.id (GL (Fin n) ℂ)) hN.symm lam g x =
      GlobalTheory.Branching.sqRep ℂ N lam (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm g) x := rfl

theorem smallRep_id_apply {n : ℕ} (sg : DomWeight n) (g : GL (Fin n) ℂ) (x : nablaSq ℂ n sg) :
    GlobalTheory.Branching.smallRep (MonoidHom.id (GL (Fin n) ℂ)) sg g x = GlobalTheory.Branching.sqRep ℂ n sg g x := rfl

theorem embGL_update {ι : Type} [DecidableEq ι] {N n : ℕ} (hN : N = n + 1) (τ₀ : ι) (g : GL (Fin n) ℂ) :
    (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (Function.update (1 : ι → GL (Fin n) ℂ) τ₀ g τ)) =
      Function.update (1 : ι → GL (Fin N) ℂ) τ₀ (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm g) := by
  funext τ
  by_cases h : τ = τ₀
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem eq_smul_brStd_of_equivariant : ∀ {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1), 1 ≤ n →
    ∀ (Λ : ι → DomWeight N) (σ : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) →
    (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) → ∀ φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ,
    (∀ (g : ι → GL (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (g τ)) v) =
      rhoK σ g (φ v)) → ∃ c : ℂ, φ = c • Formalism.L2.Col.Br.brStd hN Λ σ := by
  intro ι _ N n hN _ Λ σ hI hS φ hφ
  classical
  let B : ∀ τ, Formalism.GradedWeylDivisibility.ssIdx n n (σ τ).natW → Formalism.GradedWeylDivisibility.ssIdx N N (Λ τ).natW → ℂ :=
    fun τ => brEntry hN (Λ τ) (σ τ) (hI τ) (hS τ)
  let M : VVIdx σ → VVIdx Λ → ℂ := fun j i => (bVV ℂ σ).repr (φ (bVV ℂ Λ i)) j
  have hslice : ∀ τ₀ (j : VVIdx σ) (i : VVIdx Λ), ∃ c, ∀ l k,
      M (Function.update j τ₀ l) (Function.update i τ₀ k) = c * B τ₀ l k := by
    intro τ₀ j i
    let ψ0 : nablaSq ℂ N (Λ τ₀) →ₗ[ℂ] nablaSq ℂ n (σ τ₀) := partCoord σ τ₀ j ∘ₗ φ ∘ₗ factorIncl Λ τ₀ i
    have hψ : ∀ g, ψ0 ∘ₗ (GlobalTheory.Branching.resRep (MonoidHom.id (GL (Fin n) ℂ)) hN.symm (Λ τ₀)) g =
        (GlobalTheory.Branching.smallRep (MonoidHom.id (GL (Fin n) ℂ)) (σ τ₀)) g ∘ₗ ψ0 := fun g => LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, smallRep_id_apply, ψ0]
      rw [resRep_id_apply hN, factorIncl_sqRep, ← partCoord_rhoK, ← hφ, embGL_update hN]
    let ψ : (GlobalTheory.Branching.resRep (MonoidHom.id (GL (Fin n) ℂ)) hN.symm (Λ τ₀)).IntertwiningMap
        (GlobalTheory.Branching.smallRep (MonoidHom.id (GL (Fin n) ℂ)) (σ τ₀)) := ⟨ψ0, hψ⟩
    have h1 := (GlobalTheory.Branching.comult_id n N hN.symm (Λ τ₀) (σ τ₀)).1
      ((GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.interlace_iff hN _ _).1 (hI τ₀))
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ (brOneRep_ne_zero hN (Λ τ₀) (σ τ₀) (hI τ₀) (hS τ₀))).1 h1 ψ
    refine ⟨c, fun l k => ?_⟩
    have h2 := congrArg (fun F : (GlobalTheory.Branching.resRep (MonoidHom.id (GL (Fin n) ℂ)) hN.symm (Λ τ₀)).IntertwiningMap
        (GlobalTheory.Branching.smallRep (MonoidHom.id (GL (Fin n) ℂ)) (σ τ₀)) =>
      (bSq (σ τ₀)).repr (F.toLinearMap (bSq (Λ τ₀) k)) l) hc
    change (bVV ℂ σ).repr (φ (bVV ℂ Λ (Function.update i τ₀ k))) (Function.update j τ₀ l) = c * brEntry hN (Λ τ₀) (σ τ₀) (hI τ₀) (hS τ₀) l k
    rw [← repr_partCoord, ← factorIncl_bSq]
    change _ = (bSq (σ τ₀)).repr (ψ.toLinearMap (bSq (Λ τ₀) k)) l at h2
    have h3 : ((bSq (σ τ₀)).repr (partCoord σ τ₀ j (φ (factorIncl Λ τ₀ i (bSq (Λ τ₀) k))))) l =
        (bSq (σ τ₀)).repr (ψ.toLinearMap (bSq (Λ τ₀) k)) l := rfl
    rw [h3, ← h2]
    show (bSq (σ τ₀)).repr (c • ((brOneRep hN (Λ τ₀) (σ τ₀) (hI τ₀) (hS τ₀)).toLinearMap (bSq (Λ τ₀) k))) l = _
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rfl
  obtain ⟨C, hC⟩ := eq_mul_prod_of_slices
    (X := fun τ => Formalism.GradedWeylDivisibility.ssIdx n n (σ τ).natW × Formalism.GradedWeylDivisibility.ssIdx N N (Λ τ).natW)
    (fun τ p => B τ p.1 p.2) (fun ω => M (fun τ => (ω τ).1) (fun τ => (ω τ).2)) (fun τ ω => by
      obtain ⟨c, hc⟩ := hslice τ (fun τ => (ω τ).1) (fun τ => (ω τ).2)
      refine ⟨c, fun x => ?_⟩
      have e1 : (fun τ' => (Function.update ω τ x τ').1) = Function.update (fun τ => (ω τ).1) τ x.1 :=
        funext fun τ' => Function.apply_update (fun _ p => p.1) ω τ x τ'
      have e2 : (fun τ' => (Function.update ω τ x τ').2) = Function.update (fun τ => (ω τ).2) τ x.2 :=
        funext fun τ' => Function.apply_update (fun _ p => p.2) ω τ x τ'
      show M (fun τ' => (Function.update ω τ x τ').1) (fun τ' => (Function.update ω τ x τ').2) = c * B τ x.1 x.2
      rw [e1, e2]
      exact hc x.1 x.2)
  refine ⟨C, (bVV ℂ Λ).ext fun i => (bVV ℂ σ).ext_elem fun j => ?_⟩
  have := hC (fun τ => (j τ, i τ))
  rw [LinearMap.smul_apply, map_smul, Finsupp.smul_apply, brStd_bVV hN Λ σ hI hS i, Module.Basis.repr_sum_self,
    smul_eq_mul]
  exact this

end GlobalTheory.BranchMultOne

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem acts_zero_zero {κ : Type} [Fintype κ] (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) T (⇑(0 : SInf F κ)) (⇑(0 : SInf F κ)) := by
  intro r _
  have h : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by
    funext x; simp [tens]
  rw [h, map_zero]

variable {n d n₁ d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d} {Y₁ : Spc F E n₁} {W₁ : Spc F E d₁}

theorem kStabL_ker_inf (B : Base F E) (M : Model σ Y W) (M₁ : Model σ Y₁ W₁) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁)
    {P P₁ : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (p₁ : SInf F (Fin n₁ × Fin d₁) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E)
    (z : ℝ) (U : Submodule ℂ P) (hU : KStabL B M om p W₁ H' U) (ψ : P →ₗ[ℂ] P₁)
    (hψ : IsFrobInf B M M₁ om om₁ p p₁ H' χ z ψ) : KStabL B M om p W₁ H' (LinearMap.ker ψ ⊓ U) := by
  intro k hk k₁ hk₁ hL f hf f₁ hA hpf
  refine ⟨?_, hU k hk k₁ hk₁ hL f hf f₁ hA hpf.2⟩
  have h0 : ψ (p f) = p₁ 0 := by rw [map_zero]; exact hpf.1
  have := hψ.cpt k hk 1 k₁ hL hk₁ f hf f₁ hA 0 (Submodule.zero_mem _) 0 (acts_zero_zero _) h0
  rw [map_zero, smul_zero] at this
  exact this

theorem frob_schur (B : Base F E) (M : Model σ Y W) (M₁ : Model σ Y₁ W₁) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁)
    {P P₁ : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (p₁ : SInf F (Fin n₁ × Fin d₁) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E)
    (z : ℝ) (U : Submodule ℂ P) (hfin : FiniteDimensional ℂ U) (hU : KStabL B M om p W₁ H' U)
    (hirr : ∀ N : Submodule ℂ P, N ≤ U → KStabL B M om p W₁ H' N → N = ⊥ ∨ N = U)
    (honto : (M₁.Pol B.ψ B.emb).map p₁ = ⊤)
    (hA : ∀ k₁ ∈ KInf σ W₁ B.emb, ∃ A : SInf F (Fin n₁ × Fin d₁) →ₗ[ℂ] SInf F (Fin n₁ × Fin d₁),
      ∀ f : SInf F (Fin n₁ × Fin d₁), Acts (evI F) (om₁ (1, k₁)) (⇑f) (⇑(A f)))
    (hmap : ∀ φ φ' : P →ₗ[ℂ] P₁, IsFrobInf B M M₁ om om₁ p p₁ H' χ z φ → IsFrobInf B M M₁ om om₁ p p₁ H' χ z φ' →
      (∃ x ∈ U, φ x ≠ 0) → (∃ x ∈ U, φ' x ≠ 0) → U.map φ = U.map φ')
    (φ φ' : P →ₗ[ℂ] P₁) (hφ : IsFrobInf B M M₁ om om₁ p p₁ H' χ z φ) (hφ' : IsFrobInf B M M₁ om om₁ p p₁ H' χ z φ') :
    (∀ x ∈ U, φ x = 0) ∨ ∃ c : ℂ, ∀ x ∈ U, φ' x = c • φ x := by
  by_cases h1 : ∀ x ∈ U, φ x = 0
  · exact Or.inl h1
  right
  by_cases h2 : ∀ x ∈ U, φ' x = 0
  · exact ⟨0, fun x hx => by rw [h2 x hx, zero_smul]⟩
  push_neg at h1 h2
  have hEq := hmap φ φ' hφ hφ' h1 h2

  have inj : ∀ x ∈ U, φ x = 0 → x = 0 := by
    rcases hirr (LinearMap.ker φ ⊓ U) inf_le_right (kStabL_ker_inf B M M₁ om om₁ p p₁ H' χ z U hU φ hφ) with h | h
    · intro x hx hφx
      have hm : x ∈ LinearMap.ker φ ⊓ U := ⟨hφx, hx⟩
      rw [h] at hm
      simpa using hm
    · exfalso
      obtain ⟨x, hx, hne⟩ := h1
      have hm : x ∈ LinearMap.ker φ ⊓ U := by rw [h]; exact hx
      exact hne hm.1
  let φU : U →ₗ[ℂ] P₁ := φ.domRestrict U
  have hinj : Function.Injective φU := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact Subtype.ext (inj y y.2 hy)
  let e := LinearEquiv.ofInjective φU hinj
  have hmem : ∀ x : U, φ'.domRestrict U x ∈ LinearMap.range φU := by
    intro x
    have : φ' x ∈ U.map φ' := Submodule.mem_map_of_mem x.2
    rw [← hEq] at this
    obtain ⟨y, hy, hyx⟩ := this
    exact ⟨⟨y, hy⟩, hyx⟩
  let T : Module.End ℂ U := e.symm.toLinearMap ∘ₗ (φ'.domRestrict U).codRestrict (LinearMap.range φU) hmem
  have key : ∀ x : U, φ (T x : P) = φ' x := by
    intro x
    have h : ((e (T x) : LinearMap.range φU) : P₁) = φU (T x) := LinearEquiv.ofInjective_apply _ _
    have h' : e (T x) = (φ'.domRestrict U).codRestrict (LinearMap.range φU) hmem x := by
      simp [T, e]
    calc φ (T x : P) = φU (T x) := rfl
      _ = ((e (T x) : LinearMap.range φU) : P₁) := h.symm
      _ = φ' x := by rw [h']; rfl
  haveI := hfin
  obtain ⟨x0, hx0, hne0⟩ := h1
  haveI : Nontrivial U := by
    refine nontrivial_of_ne ⟨x0, hx0⟩ 0 ?_
    intro h
    apply hne0
    have : x0 = 0 := congrArg Subtype.val h
    rw [this, map_zero]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  let N : Submodule ℂ P := (Module.End.eigenspace T c).map U.subtype
  have hNU : N ≤ U := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.2
  have hmemN : ∀ x (hx : x ∈ U), x ∈ N ↔ φ' x = c • φ x := by
    intro x hx
    constructor
    · intro hxN
      obtain ⟨y, hy, hyx⟩ := hxN
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hy
      simp only [Submodule.subtype_apply] at hyx
      subst hyx
      have hk := key y
      rw [hy, Submodule.coe_smul, map_smul] at hk
      exact hk.symm
    · intro hxe
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      apply Subtype.ext
      rw [Submodule.coe_smul]
      apply sub_eq_zero.mp
      apply inj _ (U.sub_mem (T _).2 (U.smul_mem c hx))
      rw [map_sub, key, map_smul]
      exact sub_eq_zero.mpr hxe
  have hNstab : KStabL B M om p W₁ H' N := by
    intro k hk k₁ hk₁ hL f hf f₁ hAct hpf
    have hpfU : p f ∈ U := hNU hpf
    have hpf₁U : p f₁ ∈ U := hU k hk k₁ hk₁ hL f hf f₁ hAct hpfU
    rw [hmemN _ hpfU] at hpf
    rw [hmemN _ hpf₁U]
    have hg : φ (p f) ∈ (M₁.Pol B.ψ B.emb).map p₁ := by rw [honto]; trivial
    obtain ⟨g, hg, hgx⟩ := hg
    obtain ⟨A, hAg⟩ := hA k₁ hk₁
    have e1 := hφ.cpt k hk 1 k₁ hL hk₁ f hf f₁ hAct g hg (A g) (hAg g) hgx.symm
    have hcg : φ' (p f) = p₁ (c • g) := by rw [hpf, map_smul, hgx]
    have e2 := hφ'.cpt k hk 1 k₁ hL hk₁ f hf f₁ hAct (c • g) (Submodule.smul_mem _ c hg) (A (c • g)) (hAg _) hcg
    rw [e2, e1, map_smul, map_smul, smul_comm]
  have hvN : (v : P) ∈ N := ⟨v, hv.1, rfl⟩
  rcases hirr N hNU hNstab with h | h
  · exfalso
    rw [h] at hvN
    have : (v : P) = 0 := (Submodule.mem_bot ℂ).1 hvN
    exact hv.2 (Subtype.ext this)
  · intro x hx
    exact (hmemN x hx).1 (h ▸ hx)

end GlobalTheory.IndLine

theorem GlobalTheory.IndLine.twPart_schur_real : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      (FiniteDimensional ℂ (twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p)) ∧ KStabL B G.M om R.p G₁.W H' (twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p)) ∧
        ∀ N : Submodule ℂ R.Pi, N ≤ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p) → KStabL B G.M om R.p G₁.W H' N → N = ⊥ ∨ N = twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p)) →
      (∀ φ φ' : R.Pi →ₗ[ℂ] R₁.Pi, IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2) φ → IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2) φ' →
        (∃ x ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p), φ x ≠ 0) → (∃ x ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p), φ' x ≠ 0) → (twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p)).map φ = (twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p)).map φ') →
      ∀ φ φ' : R.Pi →ₗ[ℂ] R₁.Pi, IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2) φ → IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2) φ' →
        (∀ x ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p), φ x = 0) ∨ ∃ c : ℂ, ∀ x ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p), φ' x = c • φ x := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' _ X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ hU hmap φ φ' hφ hφ'
  obtain ⟨hfin, hstab, hirr⟩ := hU
  exact GlobalTheory.IndLine.frob_schur B G.M G₁.M om om₁ R.p R₁.p H' X.α _ _ hfin hstab hirr hM₁.real.quot.onto
    (fun k₁ hk₁ => GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G₁.V G₁.W G₁.M om₁ _ _ hM₁.triple.base hM₁.triple.geo.hM hM₁.triple.weil k₁ hk₁)
    hmap φ φ' hφ hφ'

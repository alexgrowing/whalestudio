import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionConstructedFromDoubleCosetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionFromCompactDataStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactTransversalDoubleCosetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportInducedFunctionClosedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveIntertwinerQuotientEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveIntertwinerSubrepEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedDoubleCosetCriterionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenDoubleCosetCriterionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionClosedCellStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionOpenCellStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicClosedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHPGIffConjugateParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedCellInducingCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellInducingCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothParabolicInductionProductStatement

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

section AbstractL

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W₀ W₁ W₂ : Type} [AddCommGroup W₀] [Module ℂ W₀] [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]

def stabSub {A X : Type} [Group A] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ A X) (v : X) : Subgroup A where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
    rw [hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul]; simp

theorem exists_lift [NonarchimedeanGroup G] {Q P : Subgroup G} {x : G} (hLS : LocSec Q P x)
    (σ : Representation ℂ Q W₁) (hσ : IsSmooth σ) (H : Subgroup P)
    (hH : ∀ p : P, p ∈ H ↔ x * (p : G) * x⁻¹ ∈ Q) (τ : Representation ℂ H W₂) (E : W₁ ≃ₗ[ℂ] W₂)
    (hE : ∀ (h : H) (hq : x * ((h : P) : G) * x⁻¹ ∈ Q) (v : W₁), τ h (E v) = E (σ ⟨_, hq⟩ v))
    (Y : Set G) (hY : IsOpen Y) (hxY : ∀ p : P, x * (p : G) ∈ Y) (φ : cIndSpace H τ) :
    ∃ f : smoothPart (ind Q σ), resInd σ H hH τ E hE f = φ.1 ∧ ∀ g, f.1.1 g ≠ 0 → ∃ q ∈ Q, q * g ∈ Y := by
  obtain ⟨C, hC, hsup⟩ := φ.2
  let φ' : P → W₁ := fun p => E.symm (φ.1.1.1 p)
  have hopen : IsOpen ((stabSub (ind H τ) φ.1.1 : Subgroup P) : Set P) := φ.1.2
  have hφ' : ∀ (q : Q) (p p' : P), (q : G) * x * (p : G) = x * (p' : G) → φ' p' = σ q (φ' p) := by
    intro q p p' e
    have e1 : x * ((p' * p⁻¹ : P) : G) * x⁻¹ = (q : G) := by
      have : x * (p' : G) = (q : G) * x * (p : G) := e.symm
      push_cast
      rw [← mul_assoc, this]
      group
    have hh : p' * p⁻¹ ∈ H := (hH _).2 (e1 ▸ q.2)
    have e2 : φ.1.1.1 (((⟨_, hh⟩ : H) : P) * p) = τ ⟨_, hh⟩ (φ.1.1.1 p) := φ.1.1.2 ⟨_, hh⟩ p
    have e3 : ((⟨_, hh⟩ : H) : P) * p = p' := by simp
    rw [e3] at e2
    have e4 : φ.1.1.1 p = E (φ' p) := by simp [φ']
    have hq' : x * (((⟨_, hh⟩ : H) : P) : G) * x⁻¹ ∈ Q := (hH _).1 hh
    have e5 : (⟨_, hq'⟩ : Q) = q := Subtype.ext e1
    show E.symm (φ.1.1.1 p') = _
    rw [e2, e4, hE ⟨_, hh⟩ hq', e5, LinearEquiv.symm_apply_apply]
  have hinv : ∀ (p : P), ∀ κ ∈ stabSub (ind H τ) φ.1.1, φ' (p * κ) = φ' p := by
    intro p κ hκ
    have : (ind H τ κ φ.1.1).1 p = φ.1.1.1 p := congrArg (fun F : indSpace H τ => F.1 p) hκ
    exact congrArg E.symm this
  have hsupp : ∀ p : P, φ' p ≠ 0 → ∃ c ∈ C, ∃ q : Q, x * (p : G) = (q : G) * x * (c : G) := by
    intro p hp
    have hp' : φ.1.1.1 p ≠ 0 := fun h => hp (by simp [φ', h])
    obtain ⟨h, hh, c, hc, e⟩ := hsup p hp'
    refine ⟨c, hc, ⟨_, (hH h).1 hh⟩, ?_⟩
    rw [e]
    push_cast
    group
  obtain ⟨K, hK, hKY, hWD⟩ := GlobalTheory.T.section_constructed_from_double_coset hLS σ hσ φ' hφ' _ hopen hinv C hC Y hY (fun c _ => hxY c)
  obtain ⟨f, h1, h2, h3, h4⟩ := GlobalTheory.T.induced_function_from_compact_data σ φ' C K hWD hsupp
  refine ⟨⟨⟨f, fun h g => h1 h g⟩, ?_⟩, ?_, ?_⟩
  · refine mem_smoothPart_of_nhds ?_
    filter_upwards [hK.mem_nhds (one_mem K)] with κ hκ
    exact Subtype.ext (funext fun y => h2 y κ hκ)
  · refine Subtype.ext (Subtype.ext (funext fun p => ?_))
    show E (f (x * (p : G))) = _
    rw [h3]
    simp [φ']
  · intro g hg
    obtain ⟨q, c, hc, κ, hκ, e⟩ := h4 g hg
    refine ⟨(q : G)⁻¹, inv_mem q.2, ?_⟩
    have := hKY c hc κ hκ
    rw [e]
    convert this using 1
    group

theorem resInd_mem_cInd {Q P : Subgroup G} {x : G} (hLS : LocSec Q P x) (hP : IsClosed (P : Set G))
    (B₀ : Set G) (hB : IsCompact B₀) (hB1 : B₀ ∈ 𝓝 (1 : G))
    (K₀ : Set G) (hK₀ : IsCompact K₀) (hIw : ∀ g : G, ∃ q ∈ Q, ∃ c ∈ K₀, g = q * c)
    (σ : Representation ℂ Q W₁) (H : Subgroup P)
    (hH : ∀ p : P, p ∈ H ↔ x * (p : G) * x⁻¹ ∈ Q) (τ : Representation ℂ H W₂) (E : W₁ ≃ₗ[ℂ] W₂)
    (hE : ∀ (h : H) (hq : x * ((h : P) : G) * x⁻¹ ∈ Q) (v : W₁), τ h (E v) = E (σ ⟨_, hq⟩ v))
    (f : smoothPart (ind Q σ)) (T : Set G) (hT : IsClosed T) (hTs : T ⊆ dcos Q P x)
    (hTQ : ∀ q ∈ Q, ∀ g ∈ T, q * g ∈ T) (hfT : ∀ p : P, f.1.1 (x * (p : G)) ≠ 0 → x * (p : G) ∈ T) :
    resInd σ H hH τ E hE f ∈ cIndSpace H τ := by
  obtain ⟨C, hC, hD⟩ := GlobalTheory.T.compact_transversal_double_coset hLS hP B₀ hB hB1 (K₀ ∩ T) (hK₀.inter_right hT) (fun g hg => hTs hg.2)
  refine ⟨C, hC, fun p hp => ?_⟩
  have hp' : f.1.1 (x * (p : G)) ≠ 0 := fun h => hp (by
    show E _ = 0
    rw [h, map_zero])
  obtain ⟨q, hq, c, hc, e⟩ := hIw (x * (p : G))
  have hcT : c ∈ T := by
    have := hTQ _ (inv_mem hq) _ (hfT p hp')
    rwa [e, inv_mul_cancel_left] at this
  obtain ⟨q', hq', c', hc', e'⟩ := hD c ⟨hc, hcT⟩
  refine ⟨p * c'⁻¹, (hH _).2 ?_, c', hc', by group⟩
  have e1 : x * ((p * c'⁻¹ : P) : G) * x⁻¹ = q * q' := by
    push_cast
    rw [← mul_assoc, e, e']
    group
  rw [e1]
  exact mul_mem hq hq'

theorem two_orbits [NonarchimedeanGroup G] {Q P : Subgroup G} {w : G}
    (h1 : LocSec Q P 1) (hw : LocSec Q P w) (hP : IsClosed (P : Set G))
    (B₀ : Set G) (hB : IsCompact B₀) (hB1 : B₀ ∈ 𝓝 (1 : G))
    (K₀ : Set G) (hK₀ : IsCompact K₀) (hIw : ∀ g : G, ∃ q ∈ Q, ∃ c ∈ K₀, g = q * c)
    (hcov : ∀ g : G, g ∈ dcos Q P 1 ∨ g ∈ dcos Q P w) (hcl : IsClosed (dcos Q P 1))
    (hdis : Disjoint (dcos Q P 1) (dcos Q P w))
    (σ : Representation ℂ Q W₀) (hσ : IsSmooth σ)
    (H₁ : Subgroup P) (hH₁ : ∀ p : P, p ∈ H₁ ↔ (1 : G) * (p : G) * (1 : G)⁻¹ ∈ Q)
    (τ₁ : Representation ℂ H₁ W₁) (E₁ : W₀ ≃ₗ[ℂ] W₁)
    (hE₁ : ∀ (h : H₁) (hq : (1 : G) * ((h : P) : G) * (1 : G)⁻¹ ∈ Q) (v : W₀), τ₁ h (E₁ v) = E₁ (σ ⟨_, hq⟩ v))
    (H₂ : Subgroup P) (hH₂ : ∀ p : P, p ∈ H₂ ↔ w * (p : G) * w⁻¹ ∈ Q)
    (τ₂ : Representation ℂ H₂ W₂) (E₂ : W₀ ≃ₗ[ℂ] W₂)
    (hE₂ : ∀ (h : H₂) (hq : w * ((h : P) : G) * w⁻¹ ∈ Q) (v : W₀), τ₂ h (E₂ v) = E₂ (σ ⟨_, hq⟩ v)) :
    ∃ S : Subrepresentation ((smInd Q σ).comp P.subtype),
      Nonempty ((subQuot S ⊥).Equiv (cInd H₂ τ₂)) ∧ Nonempty ((subQuot ⊤ S).Equiv (cInd H₁ τ₁)) := by
  have hQinv : ∀ q ∈ Q, ∀ g ∈ dcos Q P 1, q * g ∈ dcos Q P 1 := by
    rintro q hq _ ⟨q', hq', p, hp, rfl⟩
    exact ⟨q * q', mul_mem hq hq', p, hp, by group⟩
  have mem1 : ∀ f, resInd σ H₁ hH₁ τ₁ E₁ hE₁ f ∈ cIndSpace H₁ τ₁ := fun f =>
    resInd_mem_cInd h1 hP B₀ hB hB1 K₀ hK₀ hIw σ H₁ hH₁ τ₁ E₁ hE₁ f _ hcl subset_rfl hQinv
      (fun p _ => ⟨1, one_mem _, p, p.2, by simp⟩)
  let R : Representation.IntertwiningMap ((smInd Q σ).comp P.subtype : Representation ℂ P (smoothPart (ind Q σ))) (cInd H₁ τ₁) :=
    ⟨(resInd σ H₁ hH₁ τ₁ E₁ hE₁).codRestrict _ mem1, fun p => by
      ext f y
      show E₁ (f.1.1 ((1 : G) * (y : G) * (p : G))) = E₁ (f.1.1 ((1 : G) * ((y * p : P) : G)))
      simp [mul_assoc]⟩
  have hRs : Function.Surjective R := fun φ => by
    obtain ⟨f, hf, -⟩ := exists_lift h1 σ hσ H₁ hH₁ τ₁ E₁ hE₁ Set.univ isOpen_univ (fun _ => trivial) φ
    exact ⟨f, Subtype.ext hf⟩
  obtain ⟨S, hS, hq⟩ := GlobalTheory.T.surjective_intertwiner_quotient_equiv _ _ R hRs
  refine ⟨S, ?_, hq⟩
  have memS : ∀ f : smoothPart (ind Q σ), f ∈ S.toSubmodule ↔ ∀ p : P, f.1.1 (p : G) = 0 := by
    intro f
    rw [hS, LinearMap.mem_ker]
    constructor
    · intro h p
      have : (R f).1.1.1 p = 0 := by
        have e : R f = 0 := h
        rw [e]
        rfl
      have e2 : E₁ (f.1.1 ((1 : G) * (p : G))) = 0 := this
      rw [one_mul] at e2
      simpa using e2
    · intro h
      refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun p => ?_)))
      show E₁ (f.1.1 ((1 : G) * (p : G))) = 0
      rw [one_mul, h, map_zero]
  have vanish : ∀ f : S.toSubmodule, ∀ g ∈ dcos Q P 1, f.1.1.1 g = 0 := by
    rintro f _ ⟨q, hq, p, hp, rfl⟩
    have := (memS f.1).1 f.2 ⟨p, hp⟩
    have e := f.1.1.2 ⟨q, hq⟩ p
    rw [mul_one]
    show f.1.1.1 (((⟨q, hq⟩ : Q) : G) * p) = 0
    rw [e]
    simp only [] at this
    rw [this, map_zero]
  have mem2 : ∀ f : S.toSubmodule, resInd σ H₂ hH₂ τ₂ E₂ hE₂ f.1 ∈ cIndSpace H₂ τ₂ := fun f => by
    refine resInd_mem_cInd hw hP B₀ hB hB1 K₀ hK₀ hIw σ H₂ hH₂ τ₂ E₂ hE₂ f.1 {g | f.1.1.1 g ≠ 0}
      (GlobalTheory.T.support_induced_function_closed σ f.1) ?_ ?_ (fun p hp => hp)
    · intro g hg
      exact (hcov g).resolve_left fun h => hg (vanish f g h)
    · intro q hq g hg
      show f.1.1.1 (q * g) ≠ 0
      have e := f.1.1.2 ⟨q, hq⟩ g
      have e' : f.1.1.1 (q * g) = σ ⟨q, hq⟩ (f.1.1.1 g) := e
      rw [e']
      intro h0
      apply hg
      have := congrArg (σ (⟨q, hq⟩ : Q)⁻¹) h0
      rw [← Module.End.mul_apply, ← map_mul] at this
      simpa using this
  let O : S.toSubmodule →ₗ[ℂ] cIndSpace H₂ τ₂ :=
    ((resInd σ H₂ hH₂ τ₂ E₂ hE₂).comp S.toSubmodule.subtype).codRestrict _ mem2
  have hOinj : Function.Injective O := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))
    rcases hcov g with h | ⟨q, hq, p, hp, rfl⟩
    · exact vanish f g h
    · have e : (O f).1.1.1 ⟨p, hp⟩ = 0 := by rw [hf]; rfl
      have e2 : E₂ (f.1.1.1 (w * p)) = 0 := e
      have e3 : f.1.1.1 (w * p) = 0 := by simpa using e2
      have e4 : f.1.1.1 (((⟨q, hq⟩ : Q) : G) * (w * p)) = σ ⟨q, hq⟩ (f.1.1.1 (w * p)) := f.1.1.2 ⟨q, hq⟩ _
      show f.1.1.1 (q * w * p) = 0
      rw [mul_assoc, show f.1.1.1 (q * (w * p)) = _ from e4, e3, map_zero]
  have hOs : Function.Surjective O := fun φ => by
    have hY : IsOpen (dcos Q P 1)ᶜ := hcl.isOpen_compl
    obtain ⟨f, hf, hs⟩ := exists_lift hw σ hσ H₂ hH₂ τ₂ E₂ hE₂ _ hY (fun p h =>
      Set.disjoint_left.1 hdis h ⟨1, one_mem _, p, p.2, by simp⟩) φ
    have hfS : f ∈ S.toSubmodule := (memS f).2 fun p => by
      by_contra h
      obtain ⟨q, hq, hy⟩ := hs _ h
      exact hy ⟨q, hq, p, p.2, by simp⟩
    exact ⟨⟨f, hfS⟩, Subtype.ext hf⟩
  exact GlobalTheory.T.bijective_intertwiner_subrep_equiv _ _ S O ⟨hOinj, hOs⟩ (fun p f => by
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun y => ?_)))
    show E₂ (f.1.1.1 (w * (y : G) * (p : G))) = E₂ (f.1.1.1 (w * ((y * p : P) : G)))
    simp [mul_assoc])

end AbstractL

section ConcreteL

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem orbit_cover {i t : ℕ} (h : (i + 1) + t = i + t + 1) (ht : 0 < t) (g : GL (Fin (i + t + 1)) k) :
    g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) 1 ∨
      g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) := by
  by_cases hy : ∀ a : Fin (i + 1), ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (Fin.last (i + t)) (stdSum h (Sum.inl a)) = 0
  · exact Or.inl ((GlobalTheory.T.closed_double_coset_criterion k h ht g).2 hy)
  · push_neg at hy
    exact Or.inr ((GlobalTheory.T.open_double_coset_criterion k h ht g).2 hy)

theorem isClosed_orbit {i t : ℕ} (h : (i + 1) + t = i + t + 1) (ht : 0 < t) :
    IsClosed (dcos (parab k (two (stdSum h))) (Mir k (i + t)) 1) := by
  have e : dcos (parab k (two (stdSum h))) (Mir k (i + t)) 1 = ⋂ a : Fin (i + 1),
      {g : GL (Fin (i + t + 1)) k | ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (Fin.last (i + t)) (stdSum h (Sum.inl a)) = 0} := by
    ext g
    rw [Set.mem_iInter]
    exact GlobalTheory.T.closed_double_coset_criterion k h ht g
  rw [e]
  refine isClosed_iInter fun a => isClosed_eq ?_ continuous_const
  exact (Units.continuous_coe_inv (M := Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)).matrix_elem _ _

theorem orbits_disjoint {i t : ℕ} (h : (i + 1) + t = i + t + 1) (ht : 0 < t) :
    Disjoint (dcos (parab k (two (stdSum h))) (Mir k (i + t)) 1)
      (dcos (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h)) := by
  refine Set.disjoint_left.2 fun g h1 h2 => ?_
  obtain ⟨a, ha⟩ := (GlobalTheory.T.open_double_coset_criterion k h ht g).1 h2
  exact ha ((GlobalTheory.T.closed_double_coset_criterion k h ht g).1 h1 a)

end ConcreteL

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cast_prod {r t N : ℕ} (h : r + t = N) (π₁ : GRep k r) (π₂ : GRep k t) :
    (π₁.prod π₂).cast h = (⟨_, prod2 h π₁.ρ π₂.ρ⟩ : GRep k N) := by
  subst h; rfl

theorem mcast_prodGPn {m j n : ℕ} (h : m + j = n) (ρ : GRep k m) (τ : MRep k j) :
    mcast h (prodGPn ρ τ) = (⟨_, cInd (HGPg k h)
      ((extTensor (ρ.tw (((j + 1 : ℕ) : ℝ) / 2)).ρ (mtw τ (-((m : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h))⟩ : MRep k n) := by
  subst h; rfl

theorem core0 (i j : ℕ) (h₀ : (i + 1) + (j + 1) = i + (j + 1) + 1) (h₁ : (i + 1) + j = i + (j + 1))
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W)
    (s₁ : IsSmooth π₁) (s₂ : IsSmooth π₂) :
    ∃ S : Subrepresentation ((smInd (parab k (two (stdSum h₀))) (sQ h₀ π₁ π₂)).comp (Mir k (i + (j + 1))).subtype),
      Nonempty ((subQuot S ⊥).Equiv (cInd (HPG k i (j + 1))
        ((extTensor (mtw (gres (⟨V, π₁⟩ : GRep k (i + 1))) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (GRep.tw (⟨W, π₂⟩ : GRep k (j + 1)) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (j + 1))))) ∧
      Nonempty ((subQuot ⊤ S).Equiv (cInd (HGPg k h₁)
        ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k (i + 1)) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h₁)))) := by
  haveI := GlobalTheory.LocRankBig.nonarchimedeanGroup_GL (k := k) (i + (j + 1) + 1)
  have ho := (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin (i + (j + 1) + 1))).mem_nhds (one_mem _)
  have ht : 0 < j + 1 := by omega
  refine two_orbits (Q := parab k (two (stdSum h₀))) (P := Mir k (i + (j + 1))) (w := wGL k h₀)
    (GlobalTheory.T.local_section_closed_cell k h₀ ht) (GlobalTheory.T.local_section_open_cell k h₀) (GlobalTheory.T.mirabolic_closed k _)
    _ GlobalTheory.SplitFlip.isCompact_KO ho
    _ GlobalTheory.SplitFlip.isCompact_KO (fun g => ?_)
    (orbit_cover k h₀ ht) (isClosed_orbit k h₀ ht) (orbits_disjoint k h₀ ht)
    (sQ h₀ π₁ π₂) (GlobalTheory.T.smooth_parabolic_induction_product h₀ _ _ s₁ s₂)
    (HGPg k h₁) (fun p => ?_) _ (tE V W) (GlobalTheory.T.closed_cell_inducing_character h₁ π₁ π₂)
    (HPG k i (j + 1)) (GlobalTheory.T.mem_HPG_iff_conjugate_parabolic k h₀) _ (tE V W) (GlobalTheory.T.open_cell_inducing_character h₀ π₁ π₂)
  · obtain ⟨p, c, hc, e⟩ := GlobalTheory.SmGL.Stages.iwasawa_two (stdSum h₀) g
    exact ⟨p, p.2, c, hc, e⟩
  · rw [one_mul, inv_one, mul_one]
    rfl

theorem core (i j : ℕ) (h₀ : (i + 1) + (j + 1) = i + (j + 1) + 1) (h₁ : (i + 1) + j = i + (j + 1))
    (π₁ : GRep k (i + 1)) (π₂ : GRep k (j + 1)) (s₁ : IsSmooth π₁.ρ) (s₂ : IsSmooth π₂.ρ) :
    MExt (prodPGn (gres π₁) π₂) (gres (⟨_, prod2 h₀ π₁.ρ π₂.ρ⟩ : GRep k (i + (j + 1) + 1)))
      (⟨_, cInd (HGPg k h₁)
      ((extTensor (π₁.tw (((j + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres π₂) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProjg k h₁))⟩) := by
  obtain ⟨V, ρ₁⟩ := π₁
  obtain ⟨W, ρ₂⟩ := π₂
  have c0 := core0 i j h₀ h₁ ρ₁ ρ₂ s₁ s₂
  unfold MExt
  exact c0

end Main

theorem resSeq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ResSeq k := by
  intro k _ _ _ _ i j n hn π₁ π₂ s₁ s₂
  subst hn
  have h₀ : (i + 1) + (j + 1) = i + (j + 1) + 1 := by omega
  have h₁ : (i + 1) + j = i + (j + 1) := by omega
  have c := core i j h₀ h₁ π₁ π₂ s₁ s₂
  rw [cast_prod, mcast_prodGPn]
  exact c

end GlobalTheory.CompanionTheory.BZRes

end

import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockDiagActEq
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsSimpleModuleOfFinrankEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveKernelCoindIntertwiningMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroCoindIntertwinerOfDoubleCosetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermMatrixRepParabolicDoubleCosetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLeviDatumPermBlocksMatchStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfNeZeroMapIsotypicSumOfCopiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockGLHomConjPermMatrixOfBlocksMatchStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroIntertwiningOfCommutingIsotypicFactoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermOfBlockSizeBijectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviGeneratedCommutingBlockGLStatement

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

noncomputable section

namespace GlobalTheory.FinGL.IrrProduct

section General

variable {G V V' W W' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem nontrivial_of_irr {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : Nontrivial V := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at h
  exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule

theorem finiteDimensional_of_irr [Finite G] {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) :
    FiniteDimensional ℂ V := by
  have := nontrivial_of_irr h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S : Subrepresentation ρ := ⟨Submodule.span ℂ (Set.range fun g => ρ g v), fun g x hx => by
    refine (Submodule.span_le (p := (Submodule.span ℂ (Set.range fun g => ρ g v)).comap (ρ g))).2 ?_ hx
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨g * k, by simp⟩⟩
  rcases eq_bot_or_eq_top S with hS | hS
  · have h1 : v ∈ S.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
    rw [hS] at h1
    exact absurd h1 hv
  · have h1 : Submodule.span ℂ (Set.range fun g => ρ g v) = ⊤ := congrArg Subrepresentation.toSubmodule hS
    exact ⟨Submodule.fg_def.2 ⟨_, Set.finite_range _, h1⟩⟩

theorem isotypic_of_equiv {τ : Representation ℂ G V} {ρ : Representation ℂ G W} {ρ' : Representation ℂ G W'}
    (e : ρ.Equiv ρ') (h : IsIsotypicOf τ ρ') : IsIsotypicOf τ ρ := by
  refine top_le_iff.1 (h.ge.trans (iSup_le fun f => le_iSup_of_le (f.comp e.toIntertwiningMap) ?_))
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, rfl⟩ := e.toLinearEquiv.surjective x
  exact ⟨y, rfl⟩

theorem isotypic_conj {τ τ' : Representation ℂ G V} {ρ : Representation ℂ G W} (π : G)
    (hτ : ∀ g, τ' g = τ (π * g * π⁻¹)) (h : IsIsotypicOf τ ρ) : IsIsotypicOf τ' ρ := by
  refine top_le_iff.1 (h.ge.trans (iSup_le fun f => le_iSup_of_le ⟨f.toLinearMap ∘ₗ ρ π, fun g => ?_⟩ ?_))
  · ext x
    simp only [LinearMap.comp_apply, hτ]
    refine Eq.trans ?_ (f.isIntertwining _ _ _ _)
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    rfl
  · rintro _ ⟨x, rfl⟩
    refine ⟨ρ π⁻¹ x, ?_⟩
    simp only [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem coind_irreducible [Finite G] (P : Subgroup G) (σ : Representation ℂ P V) (hσ : σ.IsIrreducible)
    (h : ∀ K : G → V →ₗ[ℂ] V, (∀ (p' : P) (g : G) (p : P), K ((p' : G) * g * (p : G)) = σ p' ∘ₗ K g ∘ₗ σ p) →
      ∀ g, K g ≠ 0 → g ∈ P) : (Representation.coind P.subtype σ).IsIrreducible := by
  have := nontrivial_of_irr hσ
  have := finiteDimensional_of_irr hσ
  have : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨K, hi, hK⟩ := GlobalTheory.T.exists_injective_kernel_coind_intertwiningMap G P P V V σ σ
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_ne_zero_coindIntertwiner_of_doubleCoset G P P V V σ σ 1 LinearMap.id (fun e => by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (LinearMap.congr_fun e v)) (fun p p' e => by
      have : p' = p := Subtype.ext (by simpa using e)
      rw [this]; rfl)
  have hl : ∀ Ψ (p : P), K Ψ p = σ p ∘ₗ K Ψ 1 := fun Ψ p => by
    have := hK Ψ p 1 1
    simpa [Module.End.one_eq_id] using this
  have hr : ∀ Ψ (p : P), K Ψ p = K Ψ 1 ∘ₗ σ p := fun Ψ p => by
    have := hK Ψ 1 1 p
    simpa [Module.End.one_eq_id] using this
  let E : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P.subtype σ) →ₗ[ℂ]
      Representation.IntertwiningMap σ σ :=
    { toFun := fun Ψ => ⟨K Ψ 1, fun p => (hr Ψ p).symm.trans (hl Ψ p)⟩
      map_add' := fun a b => Representation.IntertwiningMap.ext (by simp)
      map_smul' := fun a b => Representation.IntertwiningMap.ext (by simp) }
  have hE : Function.Injective E := by
    rw [injective_iff_map_eq_zero]
    intro Ψ h0
    have h1 : K Ψ 1 = 0 := congrArg Representation.IntertwiningMap.toLinearMap h0
    apply hi
    rw [map_zero]
    funext g
    by_contra hg
    apply hg
    have := hl Ψ ⟨g, h _ (hK Ψ) g hg⟩
    rw [h1] at this
    simpa using this
  have hf : Module.Finite ℂ (Representation.IntertwiningMap σ σ) :=
    Module.finite_of_finrank_eq_succ (Representation.IsIrreducible.finrank_intertwiningMap_self σ)
  have hf2 := Module.Finite.of_injective E hE
  have h1 := LinearMap.finrank_le_finrank_of_injective hE
  rw [Representation.IsIrreducible.finrank_intertwiningMap_self σ] at h1
  have : Nontrivial (Representation.IntertwiningMap (Representation.coind P.subtype σ)
    (Representation.coind P.subtype σ)) := ⟨⟨Φ, 0, hΦ⟩⟩
  have h2 := le_antisymm h1 Module.finrank_pos
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  refine GlobalTheory.CuspCharCompare.isSimpleModule_of_finrank_end ?_
  rw [← h2]
  exact (Representation.IntertwiningMap.equivAlgEnd
    (ρ := Representation.coind P.subtype σ)).toLinearEquiv.finrank_eq.symm

theorem kernel_twist {P P' : Subgroup G} {σ : Representation ℂ P V} {σ' : Representation ℂ P' V'}
    {K : G → V →ₗ[ℂ] V'} (hK : ∀ (p' : P') (g : G) (p : P), K ((p' : G) * g * (p : G)) = σ' p' ∘ₗ K g ∘ₗ σ p)
    (x : G) (p : P) (p' : P') (e : (p' : G) * x = x * (p : G)) : σ' p' ∘ₗ K x = K x ∘ₗ σ p := by
  have h1 := hK p' x 1
  have h2 := hK 1 x p
  simp only [OneMemClass.coe_one, mul_one, one_mul, map_one, Module.End.one_eq_id, LinearMap.comp_id,
    LinearMap.id_comp] at h1 h2
  rw [← h1, ← h2, e]

end General

variable {F : Type} [Field F] {r : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

section Iso

variable {d d' d'' : ℕ} {W W' W'' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
  [AddCommGroup W''] [Module ℂ W''] {ρ : Representation ℂ (GL (Fin d) F) W}
  {ρ' : Representation ℂ (GL (Fin d') F) W'} {ρ'' : Representation ℂ (GL (Fin d'') F) W''}

theorem isoGL_symm (h : IsoGL ρ ρ') : IsoGL ρ' ρ := by
  obtain ⟨rfl, ⟨e⟩⟩ := h
  exact ⟨rfl, ⟨e.symm⟩⟩

theorem isoGL_trans (h : IsoGL ρ ρ') (h' : IsoGL ρ' ρ'') : IsoGL ρ ρ'' := by
  obtain ⟨rfl, ⟨e⟩⟩ := h
  obtain ⟨rfl, ⟨e'⟩⟩ := h'
  exact ⟨rfl, ⟨e.trans e'⟩⟩

theorem isFactor_of_iso {b : Fin r → ℕ} {σ : Representation ℂ (blockTri (κ := F) b) V} {c : ℕ}
    (h : IsoGL ρ ρ') (hf : IsFactor b σ c ρ') : IsFactor b σ c ρ := by
  obtain ⟨rfl, ⟨e⟩⟩ := h
  obtain ⟨hi, hc, ht⟩ := hf
  exact ⟨isIrreducible_of_equiv e.symm hi, hc, isotypic_of_equiv e ht⟩

theorem isoGL_of_twist [Finite F] {b b' : Fin r → ℕ} {σ : Representation ℂ (blockTri (κ := F) b) V}
    {σ' : Representation ℂ (blockTri (κ := F) b') V'} {w : Equiv.Perm (Fin r)}
    (hw : ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j)) {T : V →ₗ[ℂ] V'} (hT : T ≠ 0)
    (ht : ∀ (p : blockTri (κ := F) b) (p' : blockTri (κ := F) b'),
      (p' : GL (Fin r) F) * permGL F w = permGL F w * (p : GL (Fin r) F) → σ' p' ∘ₗ T = T ∘ₗ σ p)
    (i : Fin r) (hf : IsFactor b σ (b i) ρ) (hf' : IsFactor b' σ' (b' (w i)) ρ') : IsoGL ρ ρ' := by
  obtain ⟨hi, hc, hs⟩ := hf
  obtain ⟨hi', hc', hs'⟩ := hf'
  obtain ⟨h1, h2⟩ := GlobalTheory.T.blockGLHom_conj_permMatrix_of_blocks_match F r b b' w hw i
  obtain rfl : d = d' := hc.symm.trans (h1.trans hc')
  obtain ⟨π, hπ⟩ := h2 d hc hc'
  let τ' : Representation ℂ (GL (Fin d) F) V' :=
    (σ'.comp (blockHom F b' _ hc')).comp (MulAut.conj π).toMonoidHom
  refine (isoGL_iff _ _).2 (GlobalTheory.T.equiv_of_ne_zero_map_isotypicSumOfCopies _ V V' W W' _ τ' ρ ρ' hi hi' hs (isotypic_conj π (fun g => rfl) hs')
    ⟨T, fun g => (ht _ _ (hπ g)).symm⟩ fun e => hT (congrArg Representation.IntertwiningMap.toLinearMap e))

end Iso

variable [Finite F] {b b' : Fin r → ℕ} {σ : Representation ℂ (blockTri (κ := F) b) V}
  {σ' : Representation ℂ (blockTri (κ := F) b') V'}
  {d : ℕ → ℕ} {W : ℕ → Type} [∀ c, AddCommGroup (W c)] [∀ c, Module ℂ (W c)]
  {ρ : ∀ c, Representation ℂ (GL (Fin (d c)) F) (W c)}
  {d' : ℕ → ℕ} {W' : ℕ → Type} [∀ c, AddCommGroup (W' c)] [∀ c, Module ℂ (W' c)]
  {ρ' : ∀ c, Representation ℂ (GL (Fin (d' c)) F) (W' c)}

theorem exists_perm_of_kernel (h : IsRegularCusp b σ d W ρ) (h' : IsRegularCusp b' σ' d' W' ρ')
    {K : GL (Fin r) F → V →ₗ[ℂ] V'}
    (hK : ∀ (p' : blockTri (κ := F) b') (g : GL (Fin r) F) (p : blockTri (κ := F) b),
      K ((p' : GL (Fin r) F) * g * (p : GL (Fin r) F)) = σ' p' ∘ₗ K g ∘ₗ σ p) {g : GL (Fin r) F} (hg : K g ≠ 0) :
    ∃ (w : Equiv.Perm (Fin r)) (p' : blockTri (κ := F) b') (p : blockTri (κ := F) b),
      g = (p' : GL (Fin r) F) * permGL F w * (p : GL (Fin r) F) ∧ ∀ i, IsoGL (ρ (b i)) (ρ' (b' (w i))) := by
  obtain ⟨w, p', p, rfl⟩ := GlobalTheory.T.exists_permMatrix_rep_parabolic_doubleCoset F r b b' h.1.mono h'.1.mono g
  have h0 : K (permGL F w) ≠ 0 := fun e => hg (by rw [hK, e]; simp)
  have hw := GlobalTheory.T.cuspidalLeviDatum_perm_blocks_match F r b b' V V' σ σ' h.1 h'.1 w _ h0 (kernel_twist hK _)
  exact ⟨w, p', p, rfl, fun i => isoGL_of_twist hw h0 (kernel_twist hK _) i (h.2.1 _ ⟨i, rfl⟩) (h'.2.1 _ ⟨w i, rfl⟩)⟩

theorem parInd_irreducible (h : IsRegularCusp b σ d W ρ) : (parInd b σ).IsIrreducible := by
  refine coind_irreducible _ σ h.1.irr fun K hK g hg => ?_
  obtain ⟨w, p', p, rfl, hw⟩ := exists_perm_of_kernel h h hK hg
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ p'.2 (mem_blockTri.2 fun i j hij => ?_)) p.2
  rw [permGL_apply, if_neg]
  rintro rfl
  exact h.2.2 _ ⟨j, rfl⟩ _ ⟨w j, rfl⟩ hij.ne (hw j)

theorem exists_twist (h : IsRegularCusp b σ d W ρ) (h' : IsRegularCusp b' σ' d' W' ρ') {w : Equiv.Perm (Fin r)}
    (hw : ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j)) (hρ : ∀ i, IsoGL (ρ (b i)) (ρ' (b' (w i)))) :
    ∃ T : V →ₗ[ℂ] V', T ≠ 0 ∧ ∀ (p : blockTri (κ := F) b) (p' : blockTri (κ := F) b'),
      (p' : GL (Fin r) F) * permGL F w = permGL F w * (p : GL (Fin r) F) → σ' p' ∘ₗ T = T ∘ₗ σ p := by
  have := nontrivial_of_irr h.1.irr
  have := nontrivial_of_irr h'.1.irr
  have := finiteDimensional_of_irr h.1.irr
  have := finiteDimensional_of_irr h'.1.irr
  have hf : ∀ c : Set.range b, IsFactor b σ c (ρ c) := fun c => h.2.1 c c.2
  obtain ⟨f, hf1, hf2, hf3⟩ := GlobalTheory.T.exists_levi_generated_commuting_blockGL F r b (fun c => d c) fun c => (hf c).2.1
  have hL : levi F b = levi F (b' ∘ w) := levi_congr hw
  let ι : levi F b →* blockTri (κ := F) b := Subgroup.inclusion (levi_le_blockTri b)
  let ι' : levi F b →* blockTri (κ := F) b' := (Subgroup.inclusion (levi_le_blockTri b')).comp
    ((leviConj b' w).toMonoidHom.comp (Subgroup.inclusion hL.le))
  have hι' : ∀ m, (ι' m : GL (Fin r) F) = permGL F w * m * (permGL F w)⁻¹ := fun _ => rfl
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_ne_zero_intertwining_of_commuting_isotypicFactors (levi F b) (Set.range b) (fun c => GL (Fin (d c)) F) f hf2 hf3 (fun c => W c)
    (fun c => ρ c) (fun c => (hf c).1) V V' (σ.comp ι) (σ'.comp ι') (fun c => by
      have e : ι.comp (f c) = blockHom F b c (hf c).2.1 := MonoidHom.ext fun g => Subtype.ext (hf1 c g)
      have := (hf c).2.2
      rw [← e] at this
      exact this) (by
      rintro ⟨_, i, rfl⟩
      obtain ⟨-, hc', hs'⟩ := isFactor_of_iso (hρ i) (h'.2.1 _ ⟨w i, rfl⟩)
      obtain ⟨π, hπ⟩ := (GlobalTheory.T.blockGLHom_conj_permMatrix_of_blocks_match F r b b' w hw i).2 _ (hf ⟨_, i, rfl⟩).2.1 hc'
      refine isotypic_conj π (fun g => ?_) hs'
      refine congrArg σ' (Subtype.ext ?_)
      show (ι' (f ⟨_, i, rfl⟩ g) : GL (Fin r) F) = _
      rw [hι', hf1, ← hπ, mul_inv_cancel_right])
  refine ⟨T.toLinearMap, fun e => hT (Representation.IntertwiningMap.ext e), fun p p' e => ?_⟩
  have hp' : (p' : GL (Fin r) F) = permGL F w * p * (permGL F w)⁻¹ := eq_mul_inv_of_mul_eq e
  obtain ⟨m, hm, hm1⟩ := h.1.exists_blockDiag_act_eq F r V b σ p
  obtain ⟨m', hm', hm1'⟩ := h'.1.exists_blockDiag_act_eq F r V' b' σ' p'
  have hmL : (m : GL (Fin r) F) ∈ levi F b := fun i j hij => by rw [hm1, if_neg hij]
  have e' : m' = ι' ⟨m, hmL⟩ := by
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    obtain ⟨i, rfl⟩ := w.surjective i
    obtain ⟨j, rfl⟩ := w.surjective j
    rw [hι', conj_permGL_apply, hm1', hp', conj_permGL_apply]
    simp only [hm1, hw]
  rw [← hm, ← hm', e']
  exact (T.isIntertwining' ⟨m, hmL⟩).symm

theorem irrPar : IrrPar := by
  refine ⟨fun F _ _ r b V _ _ σ d W _ _ ρ h => parInd_irreducible h, ?_⟩
  intro F _ _ r b V _ _ σ d W _ _ ρ b' V' _ _ σ' d' W' _ _ ρ' h h'
  have hi := parInd_irreducible h
  have hi' := parInd_irreducible h'
  constructor
  · rintro ⟨e⟩
    obtain ⟨K, hKi, hK⟩ := GlobalTheory.T.exists_injective_kernel_coind_intertwiningMap _ _ _ V V' σ σ'
    have := nontrivial_of_irr hi
    have h0 : K e.toIntertwiningMap ≠ 0 := fun e0 => by
      have e1 := hKi (e0.trans (map_zero K).symm)
      obtain ⟨v, hv⟩ := exists_ne (0 : Representation.coindV (blockTri (κ := F) b).subtype σ)
      refine hv (e.toLinearEquiv.injective ?_)
      rw [map_zero]
      exact congrArg (fun f : Representation.IntertwiningMap (parInd b σ) (parInd b' σ') => f v) e1
    obtain ⟨g, hg⟩ := Function.ne_iff.1 h0
    obtain ⟨w, -, -, -, hw⟩ := exists_perm_of_kernel h h' (hK _) hg
    refine ⟨?_, ?_⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨_, ⟨w i, rfl⟩, hw i⟩
    · rintro _ ⟨j, rfl⟩
      obtain ⟨i, rfl⟩ := w.surjective j
      exact ⟨_, ⟨i, rfl⟩, hw i⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨w, hρ, hw⟩ := GlobalTheory.T.exists_perm_of_blockSize_bijection r b b' (fun c c' => IsoGL (ρ c) (ρ' c'))
      (fun c hc => by
        obtain ⟨c', hc', e⟩ := h1 c hc
        refine ⟨c', ⟨hc', e⟩, fun c'' ⟨hc'', e'⟩ => ?_⟩
        by_contra hne
        exact h'.2.2 _ hc'' _ hc' hne (isoGL_trans (isoGL_symm e') e))
      (fun c' hc' => by
        obtain ⟨c, hc, e⟩ := h2 c' hc'
        refine ⟨c, ⟨hc, e⟩, fun c'' ⟨hc'', e'⟩ => ?_⟩
        by_contra hne
        exact h.2.2 _ hc'' _ hc hne (isoGL_trans e' (isoGL_symm e)))
      (fun c hc c' hc' e => (h.2.1 c hc).2.1.trans (e.1.symm.trans (h'.2.1 c' hc').2.1.symm))
    obtain ⟨T, hT, ht⟩ := exists_twist h h' hw hρ
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_ne_zero_coindIntertwiner_of_doubleCoset _ _ _ V V' σ σ' _ T hT ht
    exact ⟨Φ.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero Φ).resolve_right hΦ)⟩

end GlobalTheory.FinGL.IrrProduct

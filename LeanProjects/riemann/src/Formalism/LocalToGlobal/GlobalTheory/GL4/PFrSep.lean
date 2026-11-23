import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrLoc
import Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTieSep
import Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTieIdx

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp Formalism.L2.Herm

def GenMod {E : Type} [Field E] [NumberField E] {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (M : ℕ) : Prop :=
  ∃ b : Fin r → Fin r → E, (∀ a, b a ∈ Λ) ∧
    ∀ x ∈ Λ, ∃ c : Fin r → 𝓞 E, ∃ z ∈ Λ, x = ∑ a, c a • b a + (M : E) • z

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F

theorem mem_crdLat (S : HSpace E) (L : Submodule (𝓞 E) S.V) (x : Fin S.rank → E) :
    x ∈ crdLat S L ↔ (crd S).symm x ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, by simp⟩

theorem isLat_crd (S : HSpace E) (L : Submodule (𝓞 E) S.V) (h : Submodule.IsLattice E L) :
    IsLat (crdLat S L) := by
  refine ⟨Module.Finite.iff_fg.2 (h.fg.map _), ?_⟩
  have h1 : ((crdLat S L : Submodule (𝓞 E) (Fin S.rank → E)) : Set (Fin S.rank → E)) = (crd S) '' (L : Set S.V) := by
    ext x
    rw [SetLike.mem_coe, mem_crdLat]
    constructor
    · intro hx; exact ⟨_, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  rw [h1]
  show Submodule.span E ((crd S : S.V →ₗ[E] (Fin S.rank → E)) '' (L : Set S.V)) = ⊤
  rw [Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact (crd S).surjective

theorem isLattice_dual (S : HSpace E) (L : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L)
    (hint : L ≤ Formalism.HermitianLatticesTheory.dual S.hT L) (T : ℕ) (hT : T ≠ 0)
    (hTd : ∀ x ∈ Formalism.HermitianLatticesTheory.dual S.hT L, (T : E) • x ∈ L) : Submodule.IsLattice E (Formalism.HermitianLatticesTheory.dual S.hT L) := by
  haveI : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian _ hL.fg
  let φ : Formalism.HermitianLatticesTheory.dual S.hT L →ₗ[𝓞 E] L :=
    { toFun := fun x => ⟨(T : E) • (x : S.V), hTd x x.2⟩
      map_add' := fun x y => by ext; simp [smul_add]
      map_smul' := fun a x => by ext; simp [smul_comm (T : E) a] }
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h1 : (T : E) • (x : S.V) = (T : E) • (y : S.V) := congrArg Subtype.val hxy
    have hT' : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT
    exact Subtype.ext (smul_right_injective _ hT' h1)
  haveI : IsNoetherian (𝓞 E) (Formalism.HermitianLatticesTheory.dual S.hT L) := isNoetherian_of_injective φ hinj
  refine ⟨(Submodule.fg_top _).1 (IsNoetherian.noetherian ⊤), ?_⟩
  refine eq_top_iff.2 ?_
  rw [← hL.span_eq_top]
  exact Submodule.span_mono hint

def matOf (S : HSpace E) (γ : S.V ≃ₗ[E] S.V) : GL (Fin S.rank) E :=
  Matrix.GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin S.rank → E)).symm
      (((crd S).symm.trans γ).trans (crd S)))

theorem matOf_mulVec (S : HSpace E) (γ : S.V ≃ₗ[E] S.V) (u : Fin S.rank → E) :
    (matOf S γ : Matrix (Fin S.rank) (Fin S.rank) E) *ᵥ u = crd S (γ ((crd S).symm u)) := by
  rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.coe_toLin, matOf, MulEquiv.apply_symm_apply]
  rfl

theorem hform_single {n : Type} [Fintype n] [DecidableEq n] (σ : E →+* E) (A : Matrix n n E) (i j : n) :
    hform σ A (Pi.single i 1) (Pi.single j 1) = A i j := by
  simp [hform, Pi.single_apply, apply_ite σ, ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem UJ_of_hform {n : Type} [Fintype n] [DecidableEq n] (σ : E →+* E) (J : Matrix n n E) (G : GL n E)
    (h : ∀ u w, hform σ J ((G : Matrix n n E) *ᵥ u) ((G : Matrix n n E) *ᵥ w) = hform σ J u w) : G ∈ UJ σ J := by
  show cT σ (G : Matrix n n E) * J * (G : Matrix n n E) = J
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hform_mulVec, hform_single, hform_single] at this
  exact this

theorem frames_of_tie {hc : CMData F E} {S : HSpace E} {Lb : Submodule (𝓞 E) (Fin S.rank → E)}
    {U : Subgroup (GL (Fin S.rank) (E ⊗[F] Af F))} {cls : Type} {stab : cls → Type} [∀ c, Group (stab c)]
    {lat : cls → Submodule (𝓞 E) S.V} (X : ClassTie hc S Lb U stab lat)
    (hLbd : IsLat (dualL hc S Lb)) (hΔ : ∀ c, Submodule.IsLattice E (Formalism.HermitianLatticesTheory.dual S.hT (lat c)))
    (M : ℕ) (hM : M ≠ 0) (hgen : GenMod (dualL hc S Lb) M)
    (hU : ∀ k : GL (Fin S.rank) 𝒜, k ∈ UAf hc S →
      (∀ u, u ∈ hat F Lb ↔ (k : Matrix (Fin S.rank) (Fin S.rank) 𝒜) *ᵥ u ∈ hat F Lb) →
      (∀ u ∈ hat F (dualL hc S Lb), ∃ z ∈ hat F (dualL hc S Lb),
        (k : Matrix (Fin S.rank) (Fin S.rank) 𝒜) *ᵥ u - u = (M : 𝒜) • z) → k ∈ U) :
    ∃ e : cls → Fin S.rank → S.V, (∀ c a, e c a ∈ Formalism.MainNotions.flipTwoThree.dualSub S (lat c)) ∧
      ∀ c c', Formalism.MainNotions.flipTwoThree.SameCls S M (lat c) (lat c') (e c) (e c') → c = c' := by
  obtain ⟨b, hb, hgen⟩ := hgen
  have hΔ' : ∀ c, IsLat (dl hc.sig S.gram (crdLat S (lat c))) := by
    intro c
    have := isLat_crd S _ (hΔ c)
    rwa [crdLat_dual hc] at this
  obtain ⟨e, he, hsep⟩ := frames_core (F := F) hc.sig S.gram Lb hLbd (fun c => crdLat S (lat c)) hΔ'
    (fun c => (X.y c : GL (Fin S.rank) 𝒜)) (fun c => (X.y c).2) (fun c u => X.y_lat c u) M hM b hb hgen
  have hmemd : ∀ (L : Submodule (𝓞 E) S.V) (x : Fin S.rank → E),
      x ∈ dl hc.sig S.gram (crdLat S L) ↔ (crd S).symm x ∈ Formalism.HermitianLatticesTheory.dual S.hT L := by
    intro L x
    rw [← mem_crdLat]
    show x ∈ dualL hc S (crdLat S L) ↔ _
    rw [← crdLat_dual hc]
  refine ⟨fun c a => (crd S).symm (e c a), fun c a => ?_, ?_⟩
  · rw [dualSub_eq]
    exact (hmemd _ _).1 (he c a)
  rintro c c' ⟨γ, hγ, hL, hz⟩
  set G := matOf S γ with hGdef
  have hG : G ∈ UJ (hc.sig : E →+* E) S.gram := by
    refine UJ_of_hform _ _ G fun u w => ?_
    rw [matOf_mulVec, matOf_mulVec, ← hT_crd hc, hγ, hT_crd hc]
    simp
  have hΛ : ∀ x, x ∈ crdLat S (lat c) ↔ (G : Matrix (Fin S.rank) (Fin S.rank) E) *ᵥ x ∈ crdLat S (lat c') := by
    intro x
    rw [mem_crdLat, mem_crdLat, matOf_mulVec, LinearEquiv.symm_apply_apply]
    exact hL _
  have hGe : ∀ a, ∃ w ∈ dl hc.sig S.gram (crdLat S (lat c')),
      (G : Matrix (Fin S.rank) (Fin S.rank) E) *ᵥ e c a - e c' a = (M : E) • w := by
    intro a
    obtain ⟨z, hzm, hze⟩ := hz a
    refine ⟨crd S z, (hmemd _ _).2 ?_, ?_⟩
    · rw [LinearEquiv.symm_apply_apply]
      have h := hzm
      rw [dualSub_eq] at h
      exact h
    · rw [matOf_mulVec]
      have := congrArg (crd S) hze
      rw [map_sub, LinearEquiv.apply_symm_apply, map_smul] at this
      exact this
  obtain ⟨k, hkU, hst, hcg, hyk⟩ := hsep c c' G hG hΛ hGe
  have hkUU := hU k hkU hst hcg
  refine Formalism.L2.GlobalTheoryTheory.TraceIntegrality.ClassTie.eq_of_mul X ⟨bc (inclE (F := F) (Af F)) G, bc_mem_UPts hc.sig S.gram G hG⟩
    ⟨k⁻¹, inv_mem hkU⟩ ?_ (inv_mem hkUU) ?_
  · exact Subgroup.mem_subgroupOf.2 ⟨G, hG, rfl⟩
  · exact Subtype.ext hyk

end Gen

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

end

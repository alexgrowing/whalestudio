import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import BuildAid.D3

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.CellBij

set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct

def tensorReindex {α β : Type} (e : β ≃ α) (X : α → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] : (⨂[ℂ] a, X a) ≃ₗ[ℂ] ⨂[ℂ] j, X (e j) :=
  PiTensorProduct.reindex ℂ X e.symm

theorem tensorReindex_tprod {α β : Type} (e : β ≃ α) (X : α → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (z : ∀ a, X a) :
    tensorReindex e X (PiTensorProduct.tprod ℂ z) = PiTensorProduct.tprod ℂ fun j => z (e j) := by
  exact PiTensorProduct.reindex_tprod e.symm z

theorem tensorReindex_piTensor {α β : Type} (e : β ≃ α) {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (γ : ∀ a, Γ a) (p : ∀ j, Γ (e j)) (h : ∀ j, γ (e j) = p j) (y : ⨂[ℂ] a, X a) :
    tensorReindex e X (piTensor ρ γ y) = (piTensor fun j => ρ (e j)) p (tensorReindex e X y) := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r z =>
    simp only [map_smul, piTensor_tprod, tensorReindex_tprod, h]
  | add x y hx hy =>
    simp only [map_add, hx, hy]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem occursTimes_of_equiv_lemma {G V₁ V₂ Y : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ G Y)
    {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂} (E : ρ₁.Equiv ρ₂) (r : ℕ)
    (h : OccursTimes σ ρ₁ r) : OccursTimes σ ρ₂ r := by
  obtain ⟨S, T, hTS, hST, hq⟩ := h
  let e : V₁ ≃ₗ[ℂ] V₂ := E.toLinearEquiv
  have he : ∀ (g : G) (v : V₁), e (ρ₁ g v) = ρ₂ g (e v) := by
    intro g v
    simp only [e, Representation.Equiv.toLinearEquiv_apply]
    exact Representation.IntertwiningMap.isIntertwining ρ₁ ρ₂ E.toIntertwiningMap g v
  have he' : ∀ (g : G) (w : V₂), e.symm (ρ₂ g w) = ρ₁ g (e.symm w) := by
    intro g w
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let mp : Subrepresentation ρ₁ → Subrepresentation ρ₂ := fun A =>
    { toSubmodule := A.toSubmodule.map (e : V₁ →ₗ[ℂ] V₂)
      apply_mem_toSubmodule := by
        intro g w hw
        rw [Submodule.mem_map_equiv] at hw ⊢
        rw [he']
        exact A.apply_mem_toSubmodule g hw }
  have hmono : ∀ {A B : Subrepresentation ρ₁}, A ≤ B → mp A ≤ mp B := by
    intro A B hAB x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Submodule.mem_map_of_mem (hAB hy)
  have hQ : ∀ A B : Subrepresentation ρ₁, Nonempty ((subQuot A B).Equiv (subQuot (mp A) (mp B))) := by
    intro A B
    let e1 : A.toSubmodule ≃ₗ[ℂ] (mp A).toSubmodule :=
      LinearEquiv.ofSubmodules e A.toSubmodule (mp A).toSubmodule rfl
    have hP : Submodule.map (e1 : A.toSubmodule →ₗ[ℂ] (mp A).toSubmodule)
        (Submodule.comap A.toSubmodule.subtype B.toSubmodule) =
        Submodule.comap (mp A).toSubmodule.subtype (mp B).toSubmodule := by
      ext x
      rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
      show (((e1.symm x) : A.toSubmodule) : V₁) ∈ B.toSubmodule ↔
        (x : V₂) ∈ B.toSubmodule.map (e : V₁ →ₗ[ℂ] V₂)
      rw [Submodule.mem_map_equiv, LinearEquiv.ofSubmodules_symm_apply]
    let qe := Submodule.Quotient.equiv _ _ e1 hP
    refine ⟨Representation.Equiv.mk qe ?_⟩
    intro g
    refine LinearMap.ext fun q => ?_
    refine Submodule.Quotient.induction_on _ q fun x => ?_
    show Submodule.Quotient.mk (e1 ((A.toRepresentation g) x)) =
      Submodule.Quotient.mk (((mp A).toRepresentation g) (e1 x))
    congr 1
    apply Subtype.ext
    show e (ρ₁ g (x : V₁)) = ρ₂ g (e (x : V₁))
    exact he g x
  refine Exists.intro (fun i => mp (S i)) (Exists.intro (fun i => mp (T i))
    ⟨fun i => hmono (hTS i), fun i j hij => hmono (hST i j hij), fun i => ?_⟩)
  obtain ⟨q⟩ := hQ (S i) (T i)
  obtain ⟨f⟩ := hq i
  exact ⟨q.symm.trans f⟩

theorem jhMult_of_nonempty {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ G Y)
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} (h : Nonempty (ρ.Equiv ρ')) :
    jhMult σ ρ = jhMult σ ρ' := by
  obtain ⟨E⟩ := h
  show (⨆ r, ⨆ (_ : OccursTimes σ ρ r), (r : ℕ∞)) = ⨆ r, ⨆ (_ : OccursTimes σ ρ' r), (r : ℕ∞)
  congr 1
  funext r
  rw [show OccursTimes σ ρ r = OccursTimes σ ρ' r from
    propext ⟨occursTimes_of_equiv_lemma σ E r, occursTimes_of_equiv_lemma σ E.symm r⟩]

theorem cell_bij {α β : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] (e : β ≃ α)
    (d : α → ℕ) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ i, Representation ℂ (GL (Fin (d i)) k) (X i)) (hρ : ∀ i, IsSmooth (ρ i))
    (b : SizeMatrix (fun i => Fin (d i)) (fun j => Fin (d (e j))))
    (hb : ∀ i j, b.1 i j = if e j = i then d i else 0) :
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (e j))),
      Nonempty ((cellFunctor f g (piTensor ρ)).Equiv (piTensor fun j => ρ (e j))) := by
  have hrz : ∀ i j, j ≠ e.symm i → b.1 i j = 0 := by
    intro i j hj
    rw [hb, if_neg fun h => hj (by rw [← h, Equiv.symm_apply_apply])]
  have hcz : ∀ j i, i ≠ e j → b.1 i j = 0 := by
    intro j i hi
    rw [hb, if_neg fun h => hi h.symm]
  have hrf : ∀ i, b.1 i (e.symm i) = d i := by
    intro i
    rw [hb, if_pos (e.apply_symm_apply i)]
  have hcf : ∀ j, b.1 (e j) j = d (e j) := by
    intro j
    rw [hb, if_pos rfl]
  let f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i) := fun i =>
    GlobalTheory.OneBlockCell.valEquiv (e.symm i) (hrf i) (fun j hj => hrz i j hj)
  let g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (e j)) := fun j =>
    GlobalTheory.OneBlockCell.valEquiv (e j) (hcf j) (fun i hi => hcz j i hi)
  refine ⟨f, g, ?_⟩
  have hbot : twKer (piTensor ρ) (relUnip k f) 1 = ⊥ := by
    refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    have : (n : Levi k (fun i => Fin (d i))) = 1 := funext fun i =>
      GlobalTheory.OneBlockCell.eq_one_of_mem_unipRad_single (f i) (e.symm i) (fun j hj => hrz i j hj)
        (n.2 i trivial)
    simp [this]
  have hδ : ∀ z, relDeltaHalf k (fun i j => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun i _ =>
      GlobalTheory.OneBlockCell.deltaHalf_eq_one_of_single (e.symm i) (fun j hj => hrz i j hj) (z i)
  have hδ' : ∀ z, relDeltaHalf k (fun j i => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun j _ =>
      GlobalTheory.OneBlockCell.deltaHalf_eq_one_of_single (e j) (fun i hi => hcz j i hi) (z j)
  have hP : ∀ x, x ∈ relParab k g := fun x j _ =>
    GlobalTheory.OneBlockCell.mem_parab_of_single (g j) (e j) (fun i hi => hcz j i hi) (x j)
  have hγ : ∀ (p : relParab k g) j,
      relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g p)) (e j) =
        (p : Levi k (fun j => Fin (d (e j)))) j := by
    intro p j
    rw [relEmb_apply]
    refine Units.ext (Matrix.ext fun x y => ?_)
    obtain ⟨⟨a, t⟩, rfl⟩ := (f (e j)).surjective x
    obtain ⟨⟨a', s⟩, rfl⟩ := (f (e j)).surjective y
    have ha : a = j := by
      by_contra hne
      have h1 := hrz (e j) a (by rwa [Equiv.symm_apply_apply])
      have h2 := t.2
      omega
    have ha' : a' = j := by
      by_contra hne
      have h1 := hrz (e j) a' (by rwa [Equiv.symm_apply_apply])
      have h2 := s.2
      omega
    subst ha
    subst ha'
    rw [leviEmb_apply_same]
    rfl
  have hsm : IsSmooth (piTensor fun j => ρ (e j)) := isSmooth_piTensor fun j => hρ (e j)
  let R := tensorReindex e X
  let Ψ : (⨂[ℂ] j, X (e j)) ≃ₗ[ℂ] Jacquet (piTensor ρ) (relUnip k f) :=
    R.symm.trans (Submodule.quotEquivOfEqBot _ hbot).symm
  have hΨ : ∀ u, Ψ u = Submodule.Quotient.mk (R.symm u) := fun u => rfl
  let τ := (twist ((relJac f (piTensor ρ)).comp (swapBlocks k (fun i j => Fin (b.1 i j))))
        (relDeltaHalf k (fun j i => Fin (b.1 i j)))).comp (relProj k g)
  have law : ∀ (p : relParab k g) u, τ p (Ψ u) = Ψ ((piTensor fun j => ρ (e j)) p u) := by
    intro p u
    rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, hΨ, relJac_mk, hδ, hδ', hΨ]
    simp only [inv_one, Units.val_one, one_smul]
    congr 1
    apply R.injective
    rw [tensorReindex_piTensor e ρ _ (p : Levi k (fun j => Fin (d (e j)))) (hγ p)]
    exact (congrArg (fun w => (piTensor fun j => ρ (e j))
      (p : Levi k (fun j => Fin (d (e j)))) w) (R.apply_symm_apply u)).trans
        (R.apply_symm_apply _).symm
  let F : (piTensor fun j => ρ (e j)).IntertwiningMap (cellFunctor f g (piTensor ρ)) :=
    { toFun := fun u => ⟨⟨fun x => Ψ ((piTensor fun j => ρ (e j)) x u), fun p x => by
          show Ψ ((piTensor fun j => ρ (e j)) (↑p * x) u) = _
          rw [map_mul, Module.End.mul_apply]
          exact (law p _).symm⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hsm u).mem_nhds (by simp)) fun x hx => by
          have hx' : (piTensor fun j => ρ (e j)) x u = u := hx
          refine Subtype.ext (funext fun y => ?_)
          show Ψ ((piTensor fun j => ρ (e j)) (y * x) u) = Ψ ((piTensor fun j => ρ (e j)) y u)
          rw [map_mul, Module.End.mul_apply, hx'])⟩
      map_add' := fun u w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c u => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun h => LinearMap.ext fun u => Subtype.ext (Subtype.ext (funext fun x => by
        show Ψ ((piTensor fun j => ρ (e j)) x ((piTensor fun j => ρ (e j)) h u)) =
          Ψ ((piTensor fun j => ρ (e j)) (x * h) u)
        rw [map_mul, Module.End.mul_apply])) }
  refine ⟨(LocGL.equivOfBijective F ⟨fun u w hw => ?_, fun φ => ⟨Ψ.symm (φ.1.1 1),
    Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩).symm⟩
  · have h1 : Ψ ((piTensor fun j => ρ (e j)) 1 u) = Ψ ((piTensor fun j => ρ (e j)) 1 w) :=
      congrArg (fun φ => φ.1.1 1) hw
    simpa using h1
  · show Ψ ((piTensor fun j => ρ (e j)) x (Ψ.symm (φ.1.1 1))) = φ.1.1 x
    refine (law ⟨x, hP x⟩ (Ψ.symm (φ.1.1 1))).symm.trans ?_
    refine (congrArg (τ ⟨x, hP x⟩) (Ψ.apply_symm_apply (φ.1.1 1))).trans ?_
    refine (φ.1.2 ⟨x, hP x⟩ 1).symm.trans ?_
    exact congrArg φ.1.1 (mul_one x)

theorem isIrreducible_piTensor (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {β : Type} [Fintype β]
    (x : β → IrrGL k) : (piTensor fun j => (x j).rep).IsIrreducible := by
  exact GlobalTheory.ExtTensorIrr.piTensor_isIrreducible GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k β
    (fun j => Fin (x j).1) (fun j => (x j).2.rep)

theorem jhMult_cell_comp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l c : ℕ} (x : Fin l → IrrGL k)
    (e : Fin c ≃ Fin l)
    (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (x (e j)).1))
    (hb : ∀ i j, b.1 i j = if e j = i then (x i).1 else 0) :
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (x (e j)).1),
      jhMult (piTensor fun j => (x (e j)).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
  have T4 := @cell_bij k _ _ _ _ (Fin l) (Fin c) _ _ _ _ e (fun i => (x i).1)
    (fun i => (x i).2.rep.V) _ _ (fun i => (x i).rep) (fun i => (x i).2.rep.smooth) b hb
  obtain ⟨f, hf⟩ := T4
  obtain ⟨g, hg⟩ := hf
  refine ⟨f, g, ?_⟩
  have h1 := jhMult_self (isIrreducible_piTensor hA fun j => x (e j))
  have h2 := jhMult_of_nonempty (piTensor fun j => (x (e j)).rep) hg
  exact h2.trans h1

theorem jhMult_cell_bij : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL →
    ∀ {l c : ℕ} (x : Fin l → IrrGL k) (y : Fin c → IrrGL k) (e : Fin c ≃ Fin l),
      (∀ a, y a = x (e a)) →
      ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)),
        (∀ i j, b.1 i j = if e j = i then (x i).1 else 0) →
        ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1),
          jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
  intro k _ _ _ _ hA l c x y e hy b hb
  obtain rfl : y = fun a => x (e a) := funext hy
  exact jhMult_cell_comp hA x e b hb

end GlobalTheory.CompanionTheory.CellBij

end

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjections
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.DecN

open NumberField IsDedekindDomain GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec
open PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport
open scoped Topology

variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def lvN (v : HeightOneSpectrum (𝓞 F)) (P : AddSubgroup (Fv F v)) (n M : ℕ) :
    AddSubgroup (Fin n → Fin M → Fv F v ⊗[F] E) where
  carrier := {Z | ∀ a i k, crd b (Fv F v) (Z a i) k ∈ P}
  add_mem' hx hy a i k := by
    rw [Pi.add_apply, Pi.add_apply, crd_add]
    exact add_mem (hx a i k) (hy a i k)
  zero_mem' a i k := by
    rw [Pi.zero_apply, Pi.zero_apply, crd_zero]
    exact zero_mem P
  neg_mem' hx a i k := by
    rw [Pi.neg_apply, Pi.neg_apply, crd_neg]
    exact neg_mem (hx a i k)

theorem isClopen_lvN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) (n M : ℕ) :
    IsClopen (lvN b v (P : AddSubgroup (Fv F v)) n M : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  have hc : ∀ (x : Fin n) (i : Fin M) (k : Fin d),
      Continuous (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) :=
    fun x i k => (continuous_crd b (Fv F v) k).comp ((continuous_apply i).comp (continuous_apply x))
  have e : (lvN b v (P : AddSubgroup (Fv F v)) n M : Set (Fin n → Fin M → Fv F v ⊗[F] E)) = ⋂ x, ⋂ i, ⋂ k,
      (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) ⁻¹' (P : Set (Fv F v)) := by
    ext Y
    simp [lvN]
  rw [e]
  exact ⟨isClosed_iInter fun x => isClosed_iInter fun i => isClosed_iInter fun k =>
    P.isClosed.preimage (hc x i k), isOpen_iInter_of_finite fun x =>
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => P.isOpen.preimage (hc x i k)⟩

theorem isCompact_lvN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) (hP : P ≤ intSub v) (n M : ℕ) :
    IsCompact (lvN b v (P : AddSubgroup (Fv F v)) n M : Set (Fin n → Fin M → Fv F v ⊗[F] E)) :=
  (isCompact_latV b v n M).of_isClosed_subset (isClopen_lvN b v P n M).isClosed
    fun _ hZ a i k => hP (hZ a i k)

theorem projV_subN (v : HeightOneSpectrum (𝓞 F)) {n M : ℕ} (X Y : Fin n → Fin M → Af F ⊗[F] E) :
    projV v (X - Y) = projV v X - projV v Y := by
  funext a i
  simp [projV, map_sub]

def cosVN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) {n M : ℕ}
    (a : Fin n → Fin M → Fv F v ⊗[F] E) : Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
  {Z | Z - a ∈ lvN b v (P : AddSubgroup (Fv F v)) n M}

theorem isCompact_isOpen_cosVN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) (hP : P ≤ intSub v)
    {n M : ℕ} (a : Fin n → Fin M → Fv F v ⊗[F] E) : IsCompact (cosVN b v P a) ∧ IsOpen (cosVN b v P a) := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have e : cosVN b v P a = (Homeomorph.subRight a) ⁻¹' (lvN b v (P : AddSubgroup (Fv F v)) n M : Set _) := rfl
  rw [e]
  exact ⟨(Homeomorph.subRight a).isCompact_preimage.2 (isCompact_lvN b v P hP n M),
    (isClopen_lvN b v P n M).isOpen.preimage (Homeomorph.subRight a).continuous⟩

theorem cosVN_intSub (v : HeightOneSpectrum (𝓞 F)) {n M : ℕ} {a : Fin n → Fin M → Fv F v ⊗[F] E}
    (ha : a ∈ latV b v) : cosVN b v (intSub v) a = latV b v := by
  have ha' : a ∈ lvN b v ((intSub v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M := ha
  ext Z
  have e1 : Z ∈ cosVN b v (intSub v) a ↔ Z - a ∈ lvN b v ((intSub v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M :=
    Iff.rfl
  have e2 : Z ∈ latV b v ↔ Z ∈ lvN b v ((intSub v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M := Iff.rfl
  rw [e1, e2, sub_eq_add_neg]
  exact add_mem_cancel_right (neg_mem ha')

theorem exists_box_combN {n M : ℕ} (g : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (hg : IsSB g) :
    ∃ (s : Finset (Fin n → Fin M → Af F ⊗[F] E))
      (A : (Fin n → Fin M → Af F ⊗[F] E) → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
      (S : Finset (HeightOneSpectrum (𝓞 F))),
      (∀ a v, IsCompact (A a v) ∧ IsOpen (A a v)) ∧ (∀ a ∈ s, ∀ v, v ∉ S → A a v = latV b v) ∧
        ∀ Y, g Y = ∑ a ∈ s, g a * (boxF (A a)).indicator (fun _ => (1 : ℂ)) Y := by
  classical
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have hU := invariant_mem_nhds hg.1 hg.2
  let Lc : (Fin n → Fin M → Fin d → Af F) → (Fin n → Fin M → Af F ⊗[F] E) :=
    fun c x i => ∑ k, c x i k • ((1 : Af F) ⊗ₜ[F] b k)
  have hL : Continuous Lc := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk
        continuous_const)
  have hL0 : Lc (fun _ _ _ => 0) = 0 := by
    funext x i
    simp [Lc]
  have hp : Lc ⁻¹' {u | ∀ x, g (x + u) = g x} ∈ 𝓝 (fun _ => fun _ => fun _ => (0 : Af F)) :=
    hL.continuousAt.preimage_mem_nhds (by rw [hL0]; exact hU)
  obtain ⟨W1, hW1, h1⟩ := exists_nhds_of_pi hp
  obtain ⟨W2, hW2, h2⟩ := exists_nhds_of_pi hW1
  obtain ⟨W, hW, h3⟩ := exists_nhds_of_pi hW2
  obtain ⟨T, P, hPO, hPT, hsub⟩ := exists_box_subset hW
  let B : AddSubgroup (Af F) :=
    { carrier := {y | ∀ v, y v ∈ P v}
      add_mem' := fun hx hy v => add_mem (hx v) (hy v)
      zero_mem' := fun v => zero_mem (P v)
      neg_mem' := fun hx v => neg_mem (hx v) }
  have hBo : IsOpen (B : Set (Af F)) := by
    have e : (B : Set (Af F)) = {y : Af F | ∀ v, y v ∈ v.adicCompletionIntegers F} ∩
        ⋂ v ∈ T, (fun y : Af F => y v) ⁻¹' (P v : Set (Fv F v)) := by
      ext y
      constructor
      · intro hy
        exact ⟨fun v => hPO v (hy v), Set.mem_iInter₂.2 fun v _ => hy v⟩
      · rintro ⟨hy1, hy2⟩ v
        by_cases hv : v ∈ T
        · exact Set.mem_iInter₂.1 hy2 v hv
        · rw [hPT v hv]
          exact hy1 v
    rw [e]
    refine IsOpen.inter ?_ (T.finite_toSet.isOpen_biInter fun v _ => (P v).isOpen.preimage
      (RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v))
    exact RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  let L : AddSubgroup (Fin n → Fin M → Af F ⊗[F] E) :=
    { carrier := {X | ∀ a i k, crd b (Af F) (X a i) k ∈ B}
      add_mem' := fun {x y} hx hy a i k => by
        rw [Pi.add_apply, Pi.add_apply, crd_add]
        exact add_mem (hx a i k) (hy a i k)
      zero_mem' := fun a i k => by
        rw [Pi.zero_apply, Pi.zero_apply, crd_zero]
        exact zero_mem B
      neg_mem' := fun {x} hx a i k => by
        rw [Pi.neg_apply, Pi.neg_apply, crd_neg]
        exact neg_mem (hx a i k) }
  have hLo : IsOpen (L : Set (Fin n → Fin M → Af F ⊗[F] E)) := by
    have e : (L : Set (Fin n → Fin M → Af F ⊗[F] E)) = ⋂ a, ⋂ i, ⋂ k,
        (fun X : Fin n → Fin M → Af F ⊗[F] E => crd b (Af F) (X a i) k) ⁻¹' (B : Set (Af F)) := by
      ext X
      simp [L]
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k =>
      hBo.preimage ((continuous_crd b (Af F) k).comp ((continuous_apply i).comp (continuous_apply a)))
  have hinv : ∀ x, ∀ l ∈ L, g (x + l) = g x := by
    intro x l hl
    have hl' : l = Lc fun a i k => crd b (Af F) (l a i) k := by
      funext a i
      exact eq_sum_crd b (Af F) (l a i)
    rw [hl']
    refine h1 _ (fun a => h2 _ fun i => h3 _ fun k => hsub (hl a i k)) x
  obtain ⟨s, hs⟩ := eq_sum_cosets hg.2 L hLo hinv
  have hbad : ∀ a : Fin n → Fin M → Af F ⊗[F] E, {v | ¬ projV v a ∈ latV b v}.Finite := fun a =>
    Filter.eventually_cofinite.1 (eventually_mem_latV b a)
  refine ⟨s, fun a v => cosVN b v (P v) (projV v a), T ∪ s.biUnion fun a => (hbad a).toFinset,
    fun a v => isCompact_isOpen_cosVN b v (P v) (hPO v) _, fun a ha v hv => ?_, fun Y => ?_⟩
  · have hvT : v ∉ T := fun h => hv (Finset.mem_union_left _ h)
    have hva : projV v a ∈ latV b v := by
      by_contra h
      exact hv (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a, ha, (hbad a).mem_toFinset.2 h⟩))
    show cosVN b v (P v) (projV v a) = latV b v
    rw [hPT v hvT]
    exact cosVN_intSub b v hva
  · rw [hs Y]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    ext X
    show X - a ∈ L ↔ ∀ v, projV v X - projV v a ∈ lvN b v ((P v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M
    constructor
    · intro h v i j k
      rw [← projV_subN]
      have := crd_projV b (X - a) v i j k
      rw [this]
      exact h i j k v
    · intro h i j k v
      have := crd_projV b (X - a) v i j k
      rw [← this, projV_subN]
      exact h v i j k

theorem isSchwartzArch_const_mulN {n M : ℕ} {φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ} (h : IsSchwartzArch φ) (c : ℂ) :
    IsSchwartzArch fun X => φ X * c := by
  obtain ⟨N, e, c1, c2, f, hf⟩ := h
  exact ⟨N, e, c1, c2, c • f, fun X => by simp [hf X, mul_comm]⟩

end GlobalTheory.CompanionTheory.WhitFree.DecN

namespace GlobalTheory.CompanionTheory.WhitFree

theorem schwartzBruhat_eq_sum_pureN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ → ∃ (k : ℕ) (φ : Fin k → (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : Fin k → (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E))) (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))), (∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch (φ i)) ∧ (∀ i v, IsCompact (A i v) ∧ IsOpen (A i v)) ∧ (∀ i v, v ∉ S → A i v = latV b v) ∧ ∀ X, Φ X = ∑ i, pureN (φ i) (A i) X := by
  intro F E _ _ _ _ _ σ _ M J _ n _ _ d b Φ hΦ
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  obtain ⟨k', Φinf, Φf, hi, hf, hs⟩ := hΦ
  choose s A S hA hS hdec using fun i => DecN.exists_box_combN b (Φf i) (hf i)
  let I := Σ i : Fin k', ↥(s i)
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, fun j X => Φinf (e.symm j).1 X * Φf (e.symm j).1 (e.symm j).2.1,
    fun j => A (e.symm j).1 (e.symm j).2.1, Finset.univ.biUnion S, fun j => ?_, fun j v => hA _ _ v,
    fun j v hv => ?_, fun X => ?_⟩
  · exact DecN.isSchwartzArch_const_mulN (hi _) _
  · refine hS _ _ (e.symm j).2.2 v fun h => hv (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, h⟩)
  · rw [hs X, Fintype.sum_equiv e.symm _ (fun p : I => pureN (fun Y => Φinf p.1 Y * Φf p.1 p.2.1) (A p.1 p.2.1) X)
      (fun _ => rfl), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdec i (projFin X), Finset.mul_sum, ← Finset.sum_coe_sort (s i)]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [pureN, mul_assoc]
    rfl

end GlobalTheory.CompanionTheory.WhitFree

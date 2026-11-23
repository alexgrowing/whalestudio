import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TotallyDisjointProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupportIrreducibleSmoothGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalJacquetSubquotientAtMostOneNonemptyBlock
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalPairIrreducibleProduct
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducible
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EqOfSubsingletonStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.TDSwap

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.OneBlockCell GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.LocGL GlobalTheory.LocGL.SupportUnique

set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cell_antidiag (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i))
    (b : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j))))
    (h00 : b.1 0 0 = 0) (h11 : b.1 1 1 = 0) :
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j))),
      Nonempty ((cellFunctor f g (piTensor fun i => (σ i).π)).Equiv
        (piTensor fun j => (σ (Equiv.swap 0 1 j)).π)) := by
  have r0 := b.2.1 0
  have r1 := b.2.1 1
  have c0 := b.2.2 0
  have c1 := b.2.2 1
  simp only [Fin.sum_univ_two, Fintype.card_fin, Equiv.swap_apply_left, Equiv.swap_apply_right] at r0 r1 c0 c1
  have hrz : ∀ i j, j ≠ Equiv.swap 0 1 i → b.1 i j = 0 := by
    intro i j hj
    fin_cases i <;> fin_cases j <;> simp_all
  have hcz : ∀ j i, i ≠ Equiv.swap 0 1 j → b.1 i j = 0 := by
    intro j i hi
    fin_cases i <;> fin_cases j <;> simp_all
  have hrf : ∀ i, b.1 i (Equiv.swap 0 1 i) = d i := by
    intro i
    fin_cases i <;> simp <;> omega
  have hcf : ∀ j, b.1 (Equiv.swap 0 1 j) j = d (Equiv.swap 0 1 j) := by
    intro j
    fin_cases j <;> simp <;> omega
  let f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i) := fun i =>
    valEquiv (Equiv.swap 0 1 i) (hrf i) (fun j hj => hrz i j hj)
  let g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j)) := fun j =>
    valEquiv (Equiv.swap 0 1 j) (hcf j) (fun i hi => hcz j i hi)
  refine ⟨f, g, ?_⟩
  have hbot : twKer (piTensor fun i => (σ i).π) (relUnip k f) 1 = ⊥ := by
    refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    have : (n : Levi k (fun i => Fin (d i))) = 1 := funext fun i =>
      eq_one_of_mem_unipRad_single (f i) (Equiv.swap 0 1 i) (fun j hj => hrz i j hj) (n.2 i trivial)
    simp [this]
  have hδ : ∀ z, relDeltaHalf k (fun i j => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun i _ =>
      deltaHalf_eq_one_of_single (Equiv.swap 0 1 i) (fun j hj => hrz i j hj) (z i)
  have hδ' : ∀ z, relDeltaHalf k (fun j i => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun j _ =>
      deltaHalf_eq_one_of_single (Equiv.swap 0 1 j) (fun i hi => hcz j i hi) (z j)
  have hP : ∀ x, x ∈ relParab k g := fun x j _ =>
    mem_parab_of_single (g j) (Equiv.swap 0 1 j) (fun i hi => hcz j i hi) (x j)
  have hγ : ∀ (p : relParab k g) j,
      relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g p)) (Equiv.swap 0 1 j) =
        (p : Levi k (fun j => Fin (d (Equiv.swap 0 1 j)))) j := by
    intro p j
    rw [relEmb_apply]
    refine Units.ext (Matrix.ext fun x y => ?_)
    obtain ⟨⟨a, t⟩, rfl⟩ := (f (Equiv.swap 0 1 j)).surjective x
    obtain ⟨⟨a', s⟩, rfl⟩ := (f (Equiv.swap 0 1 j)).surjective y
    have ha : a = j := by
      by_contra hne
      have h1 := hrz (Equiv.swap 0 1 j) a (by rwa [Equiv.swap_apply_self])
      have h2 := t.2
      omega
    have ha' : a' = j := by
      by_contra hne
      have h1 := hrz (Equiv.swap 0 1 j) a' (by rwa [Equiv.swap_apply_self])
      have h2 := s.2
      omega
    subst ha
    subst ha'
    rw [leviEmb_apply_same]
    rfl

  have hsm : IsSmooth (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) :=
    isSmooth_piTensor fun j => (σ (Equiv.swap 0 1 j)).smooth
  let R := PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1)
  let Ψ : (⨂[ℂ] j, (σ (Equiv.swap 0 1 j)).V) ≃ₗ[ℂ]
      Jacquet (piTensor fun i => (σ i).π) (relUnip k f) :=
    R.symm.trans (Submodule.quotEquivOfEqBot _ hbot).symm
  have hΨ : ∀ u, Ψ u = Submodule.Quotient.mk (R.symm u) := fun u => rfl
  let τ := (twist ((relJac f (piTensor fun i => (σ i).π)).comp (swapBlocks k (fun i j => Fin (b.1 i j))))
        (relDeltaHalf k (fun j i => Fin (b.1 i j)))).comp (relProj k g)
  have law : ∀ (p : relParab k g) u, τ p (Ψ u) =
        Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p u) := by
    intro p u
    rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, hΨ, relJac_mk, hδ, hδ', hΨ]
    simp only [inv_one, Units.val_one, one_smul]
    congr 1
    apply R.injective
    rw [reindex_piTensor σ _ (p : Levi k (fun j => Fin (d (Equiv.swap 0 1 j)))) (hγ p)]
    exact (congrArg (fun w => (piTensor fun j => (σ (Equiv.swap 0 1 j)).π)
      (p : Levi k (fun j => Fin (d (Equiv.swap 0 1 j)))) w) (R.apply_symm_apply u)).trans
        (R.apply_symm_apply _).symm
  let F : (piTensor fun j => (σ (Equiv.swap 0 1 j)).π).IntertwiningMap
      (cellFunctor f g (piTensor fun i => (σ i).π)) :=
    { toFun := fun u => ⟨⟨fun x => Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x u), fun p x => by
          show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) (↑p * x) u) = _
          rw [map_mul, Module.End.mul_apply]
          exact (law p _).symm⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hsm u).mem_nhds (by simp)) fun x hx => by
          have hx' : (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x u = u := hx
          refine Subtype.ext (funext fun y => ?_)
          show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) (y * x) u) =
            Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) y u)
          rw [map_mul, Module.End.mul_apply, hx'])⟩
      map_add' := fun u w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c u => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun h => LinearMap.ext fun u => Subtype.ext (Subtype.ext (funext fun x => by
        show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x
            ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) h u)) =
          Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) (x * h) u)
        rw [map_mul, Module.End.mul_apply])) }
  refine ⟨(LocGL.equivOfBijective F ⟨fun u w hw => ?_, fun φ => ⟨Ψ.symm (φ.1.1 1),
    Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩).symm⟩
  · have h1 : Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) 1 u) =
        Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) 1 w) := congrArg (fun φ => φ.1.1 1) hw
    simpa using h1
  · show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x (Ψ.symm (φ.1.1 1))) = φ.1.1 x
    refine (law ⟨x, hP x⟩ (Ψ.symm (φ.1.1 1))).symm.trans ?_
    refine (congrArg (τ ⟨x, hP x⟩) (Ψ.apply_symm_apply (φ.1.1 1))).trans ?_
    refine (φ.1.2 ⟨x, hP x⟩ 1).symm.trans ?_
    exact congrArg φ.1.1 (mul_one x)

theorem row_unique (hG : GeometricLemma) {d d' : Fin 2 → ℕ} (σ : ∀ i, Irr k (d i))
    (hσ : ∀ i, IsCuspidal (σ i).π) {b : Fin 2 → Fin 2 → ℕ}
    (f : ∀ i, (Σ j, Fin (b i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b i j)) ≃ Fin (d' j))
    {Z : Type} [AddCommGroup Z] [Module ℂ Z] [Nontrivial Z]
    {κ : Representation ℂ (Levi k fun j => Fin (d' j)) Z}
    (E : κ.Equiv (cellFunctor f g (piTensor fun i => (σ i).π))) (i j j' : Fin 2)
    (hj : 0 < b i j) (hj' : 0 < b i j') : j = j' := by
  obtain ⟨Y, _, _, υ, hυ, hs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ κ inferInstance
  have hs' : IsSubquotient υ (cellFunctor f g (piTensor fun i => (σ i).π)) :=
    hs.trans (.of_injective E.toIntertwiningMap E.toLinearEquiv.injective)
  have hsm : IsSmooth υ := hs'.isSmooth (isSmooth_relInd _ _)
  obtain ⟨s, hrow, -⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_of_cell (hG k).2 f g (fun i => (σ i).smooth)
    (fun i => hasFiniteLength_of_isIrreducible (σ i).irr) hυ hsm (jhMult_ne_zero_iff.2 hs')
  exact GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal k (d i) _ (σ i).π 2 (b i) (f i) _ (fun j => (s i j).ρ) (hσ i)
    (fun j => GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible (s i j).irr) (hrow i) j j' hj hj'

theorem piTensor_scalar {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : α → ℂ)
    (h : ∀ a v, ρ a (g a) v = c a • v) (y : ⨂[ℂ] a, X a) : piTensor ρ g y = (∏ a, c a) • y := by
  classical
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | smul_tprod r y =>
    rw [map_smul, smul_comm, piTensor_tprod, ← MultilinearMap.map_smul_univ]
    congr 2
    funext a
    exact h a _

theorem exists_map_two_step (hBZ : BernsteinZelevinskyFiniteness) {D : ℕ} (hD : 0 < D) (σ : Fin 2 → Irr k D)
    (hc : ∀ i, IsCuspidal (σ i).π) (hne : ¬ Nonempty ((σ 0).π.Equiv (σ 1).π)) {V : Type} [AddCommGroup V] [Module ℂ V]
    {μ : Representation ℂ (Levi k fun _ : Fin 2 => Fin D) V} (hμ : IsSmooth μ) (X : Subrepresentation μ)
    (a : X.toRepresentation.Equiv (piTensor fun j => (σ (Equiv.swap 0 1 j)).π))
    (q : μ.IntertwiningMap (piTensor fun i => (σ i).π)) (hqs : Function.Surjective q)
    (hq : ∀ v, q v = 0 ↔ v ∈ X.toSubmodule) :
    ∃ (φ : μ.IntertwiningMap (piTensor fun j => (σ (Equiv.swap 0 1 j)).π)) (v : V), φ v ≠ 0 := by
  let ψ : GL (Fin D) k →* Levi k (fun _ : Fin 2 => Fin D) := MonoidHom.mulSingle (fun _ : Fin 2 => GL (Fin D) k) 0
  have hirr : ∀ (s : Fin 2 → Irr k D), (piTensor fun j => (s j).π).IsIrreducible := fun s =>
    GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k (Fin 2) (fun _ => Fin D)
      (fun j => ⟨(s j).V, (s j).π, (s j).smooth, (s j).irr⟩)
  choose ω _ hω using fun i => exists_smooth_hasCentralChar (σ i).smooth (σ i).irr
  have hcent : ∀ (z : kˣ) (g : Levi k (fun _ : Fin 2 => Fin D)),
      g * ψ (GeneralLinearGroup.scalar _ z) = ψ (GeneralLinearGroup.scalar _ z) * g := by
    intro z g
    funext i
    by_cases hi : i = 0
    · subst hi
      have hcm : g 0 * GeneralLinearGroup.scalar (Fin D) z = GeneralLinearGroup.scalar (Fin D) z * g 0 := by
        ext i j
        simp [GeneralLinearGroup.scalar, mul_comm]
      simpa [ψ] using hcm
    · simp [ψ, Pi.mulSingle_eq_of_ne hi]
  have hρz : ∀ (z : kˣ) y, (piTensor fun i => (σ i).π) (ψ (GeneralLinearGroup.scalar _ z)) y = (ω 0 z : ℂ) • y := by
    intro z y
    have h1 := piTensor_scalar (fun i => (σ i).π) (ψ (GeneralLinearGroup.scalar _ z))
      (fun i => if i = 0 then (ω 0 z : ℂ) else 1) (fun i v => by
        by_cases hi : i = 0
        · subst hi
          simpa [ψ] using hω 0 z v
        · simp [ψ, Pi.mulSingle_eq_of_ne hi, hi]) y
    simpa [Fin.prod_univ_two] using h1
  by_cases hsc : ∀ (z : kˣ) v, μ (ψ (GeneralLinearGroup.scalar _ z)) v = (ω 0 z : ℂ) • v
  · have hsub : IsSubquotient (σ 0).π (μ.comp ψ : Representation ℂ (GL (Fin D) k) V) :=
      (GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun i => (σ i).π) (fun i => (σ i).irr) 0).trans
        (isSubquotient_comp (.of_surjective q hqs) ψ)
    have hsm : IsSmooth (μ.comp ψ : Representation ℂ (GL (Fin D) k) V) :=
      isSmooth_comp hμ _ (continuous_mulSingle (A := fun _ : Fin 2 => GL (Fin D) k) 0)
    obtain ⟨ι, hι⟩ := exists_map_of_isCuspidal hD (σ 0).irr (hc 0) hsm (fun z => ⟨_, hsc z⟩) hsub
    refine exists_map_of_image ψ (σ 1).irr (fun h => ?_) (hirr _) (hirr σ) X a q hqs hq ?_ ι hι ?_
    · obtain ⟨φ⟩ := nonempty_equiv_of_isSubquotient (σ 1).irr (σ 0).irr h
      exact hne ⟨φ⟩
    · exact GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (σ (Equiv.swap 0 1 j)).π)
        (fun j => (σ (Equiv.swap 0 1 j)).irr) 0
    · intro g
      refine ⟨g 0, Pi.mulSingle 1 (g 1), ?_, fun x => ?_⟩
      · funext i
        fin_cases i <;> simp [ψ]
      · funext i
        fin_cases i <;> simp [ψ]
  · push_neg at hsc
    obtain ⟨z, v, hv⟩ := hsc
    rcases central_dichotomy X a q hq _ (hcent z) _ (hρz z) with h | h
    · exact h
    · exact absurd (h v) hv

variable (k) in

theorem exists_jac_map_of_ne (hG : GeometricLemma) (n : Type) [Fintype n] [DecidableEq n] (d : Fin 2 → ℕ)
    (σ : ∀ i, Irr k (d i)) (hσ : ∀ i, 0 < d i ∧ IsCuspidal (σ i).π) (hd : d 0 ≠ d 1)
    (e : (Σ i, Fin (d i)) ≃ n) (e' : (Σ i, Fin (d (Equiv.swap 0 1 i))) ≃ n) :
    ∃ (φ : (jac e' (multiProd e fun i => (σ i).π)).IntertwiningMap
        (piTensor fun i => (σ (Equiv.swap 0 1 i)).π)) (x : Jacquet (multiProd e fun i => (σ i).π) (unipRad k e')),
      φ x ≠ 0 := by
  obtain ⟨N, b, hb⟩ := (hG k).1 (Fin 2) (Fin 2) n (fun i => Fin (d i)) (fun j => Fin (d (Equiv.swap 0 1 j))) e e'
  obtain ⟨S, hmono, h0, hN, h4⟩ := hb _ (piTensor fun i => (σ i).π) (isSmooth_piTensor fun i => (σ i).smooth)
  obtain ⟨G0, hG0⟩ : ∃ G0 : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j))),
      G0.1 = ![![0, d 0], ![d 1, 0]] := ⟨⟨![![0, d 0], ![d 1, 0]], by
      refine ⟨fun i => ?_, fun j => ?_⟩
      · fin_cases i <;> simp [Fin.sum_univ_two]
      · fin_cases j <;> simp [Fin.sum_univ_two]⟩, rfl⟩
  have hstep : ∀ t, t ≠ b.symm G0 → Subsingleton ((S t.succ).toSubmodule ⧸
      (S t.castSucc).toSubmodule.comap (S t.succ).toSubmodule.subtype) := by
    intro t ht
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    have E := (h4 t (b t).nonempty_rows.some (b t).nonempty_cols.some).some
    have hrow := row_unique (d' := fun j => d (Equiv.swap 0 1 j)) hG σ (fun i => (hσ i).2) _ _ E
    have a1 : ¬ (0 < (b t).1 0 0 ∧ 0 < (b t).1 0 1) := fun h => absurd (hrow 0 0 1 h.1 h.2) (by decide)
    have a2 : ¬ (0 < (b t).1 1 0 ∧ 0 < (b t).1 1 1) := fun h => absurd (hrow 1 0 1 h.1 h.2) (by decide)
    have r1 := (b t).2.1 1
    have c0 := (b t).2.2 0
    have r0 := (b t).2.1 0
    have c1 := (b t).2.2 1
    simp only [Fin.sum_univ_two, Fintype.card_fin, Equiv.swap_apply_left, Equiv.swap_apply_right] at r1 c0 r0 c1
    apply ht
    rw [Equiv.eq_symm_apply]
    apply Subtype.ext
    funext i j
    rw [hG0]
    fin_cases i <;> fin_cases j <;> simp <;> omega
  obtain ⟨f₀, g₀, ⟨E₀⟩⟩ := cell_antidiag d σ (b (b.symm G0)) (by rw [Equiv.apply_symm_apply, hG0]; rfl)
    (by rw [Equiv.apply_symm_apply, hG0]; rfl)
  haveI : Nontrivial (⨂[ℂ] i, (σ (Equiv.swap 0 1 i)).V) := GlobalTheory.ProdSupport.nontrivial_piTensor _
    fun j => GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible (σ (Equiv.swap 0 1 j)).irr
  exact exists_map_of_top S hmono hN (b.symm G0) (fun t ht => hstep t ht.ne')
    ((h4 (b.symm G0) f₀ g₀).some.trans E₀)

set_option maxHeartbeats 2000000 in
variable (k) in

theorem exists_jac_map_of_eq (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) (n : Type) [Fintype n]
    [DecidableEq n] {D : ℕ} (hD : 0 < D) (σ : Fin 2 → Irr k D) (hc : ∀ i, IsCuspidal (σ i).π)
    (hne : ¬ Nonempty ((σ 0).π.Equiv (σ 1).π)) (e e' : (Σ _ : Fin 2, Fin D) ≃ n) :
    ∃ (φ : (jac e' (multiProd e fun i => (σ i).π)).IntertwiningMap
        (piTensor fun i => (σ (Equiv.swap 0 1 i)).π)) (x : Jacquet (multiProd e fun i => (σ i).π) (unipRad k e')),
      φ x ≠ 0 := by
  obtain ⟨N, b, hb⟩ := (hG k).1 (Fin 2) (Fin 2) n (fun _ => Fin D) (fun _ => Fin D) e e'
  obtain ⟨S, hmono, h0, hN, h4⟩ := hb _ (piTensor fun i => (σ i).π) (isSmooth_piTensor fun i => (σ i).smooth)
  obtain ⟨G0, hG0⟩ : ∃ G0 : SizeMatrix (fun _ : Fin 2 => Fin D) (fun _ : Fin 2 => Fin D),
      G0.1 = ![![0, D], ![D, 0]] := ⟨⟨![![0, D], ![D, 0]], by
      refine ⟨fun i => ?_, fun j => ?_⟩
      · fin_cases i <;> simp [Fin.sum_univ_two]
      · fin_cases j <;> simp [Fin.sum_univ_two]⟩, rfl⟩
  obtain ⟨G1, hG1⟩ : ∃ G1 : SizeMatrix (fun _ : Fin 2 => Fin D) (fun _ : Fin 2 => Fin D),
      G1.1 = ![![D, 0], ![0, D]] := ⟨⟨![![D, 0], ![0, D]], by
      refine ⟨fun i => ?_, fun j => ?_⟩
      · fin_cases i <;> simp [Fin.sum_univ_two]
      · fin_cases j <;> simp [Fin.sum_univ_two]⟩, rfl⟩
  have hstep : ∀ t, t ≠ b.symm G0 → t ≠ b.symm G1 → Subsingleton ((S t.succ).toSubmodule ⧸
      (S t.castSucc).toSubmodule.comap (S t.succ).toSubmodule.subtype) := by
    intro t ht ht'
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    have E := (h4 t (b t).nonempty_rows.some (b t).nonempty_cols.some).some
    have hrow := row_unique (d := fun _ => D) (d' := fun _ => D) hG σ hc _ _ E
    have a1 : ¬ (0 < (b t).1 0 0 ∧ 0 < (b t).1 0 1) := fun h => absurd (hrow 0 0 1 h.1 h.2) (by decide)
    have a2 : ¬ (0 < (b t).1 1 0 ∧ 0 < (b t).1 1 1) := fun h => absurd (hrow 1 0 1 h.1 h.2) (by decide)
    have r1 := (b t).2.1 1
    have c0 := (b t).2.2 0
    have r0 := (b t).2.1 0
    have c1 := (b t).2.2 1
    simp only [Fin.sum_univ_two, Fintype.card_fin] at r1 c0 r0 c1
    by_cases h00 : (b t).1 0 0 = 0
    · apply ht
      rw [Equiv.eq_symm_apply]
      apply Subtype.ext
      funext i j
      rw [hG0]
      fin_cases i <;> fin_cases j <;> simp <;> omega
    · apply ht'
      rw [Equiv.eq_symm_apply]
      apply Subtype.ext
      funext i j
      rw [hG1]
      fin_cases i <;> fin_cases j <;> simp <;> omega
  have h01 : b.symm G0 ≠ b.symm G1 := fun h => by
    have h1 := congrArg (fun G : SizeMatrix (fun _ : Fin 2 => Fin D) (fun _ : Fin 2 => Fin D) => G.1 0 0)
      (b.symm.injective h)
    simp only [hG0, hG1] at h1
    simp at h1
    omega
  obtain ⟨f₀, g₀, ⟨E₀⟩⟩ := cell_antidiag (fun _ => D) σ (b (b.symm G0)) (by rw [Equiv.apply_symm_apply, hG0]; rfl)
    (by rw [Equiv.apply_symm_apply, hG0]; rfl)
  have hsm : IsSmooth (piTensor fun i => (σ i).π) := isSmooth_piTensor fun i => (σ i).smooth
  obtain ⟨f₁, g₁, ⟨E₁⟩⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.cell_diag (k := k) (b (b.symm G1)) (fun i j hj => by
    rw [Equiv.apply_symm_apply, hG1]
    fin_cases i <;> fin_cases j <;> simp_all) (piTensor fun i => (σ i).π) hsm
  have F₀ := (h4 (b.symm G0) f₀ g₀).some.trans E₀
  have F₁ := (h4 (b.symm G1) f₁ g₁).some.trans E₁
  haveI : Nontrivial (⨂[ℂ] i, (σ (Equiv.swap 0 1 i)).V) := GlobalTheory.ProdSupport.nontrivial_piTensor _
    fun j => GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible (σ (Equiv.swap 0 1 j)).irr
  rcases lt_or_gt_of_ne h01 with hlt | hlt
  · have hlow : S (b.symm G0).castSucc = ⊥ := (eq_of_steps S hmono 0 _ (Fin.zero_le _) fun t h1 h2 =>
      hstep t (by
        rintro rfl
        exact absurd h2 (by simp [Fin.le_def]))
        (by
        rintro rfl
        have : (b.symm G1).val + 1 ≤ (b.symm G0).val := by simpa [Fin.le_def] using h2
        have h3 : (b.symm G0).val < (b.symm G1).val := hlt
        omega)).symm.trans h0
    have hmid : S (b.symm G0).succ = S (b.symm G1).castSucc := eq_of_steps S hmono _ _
      (by simpa [Fin.le_def] using Nat.succ_le_of_lt hlt) fun t h1 h2 => hstep t (by
        rintro rfl
        have : (b.symm G0).val + 1 ≤ (b.symm G0).val := by simpa [Fin.le_def] using h1
        omega) (by
        rintro rfl
        have : (b.symm G1).val + 1 ≤ (b.symm G1).val := by simpa [Fin.le_def] using h2
        omega)
    have htop : S (b.symm G1).succ = ⊤ := (eq_of_steps S hmono _ _ (Fin.le_last _) fun t h1 _ => hstep t (by
        rintro rfl
        have : (b.symm G1).val + 1 ≤ (b.symm G0).val := by simpa [Fin.le_def] using h1
        have h3 : (b.symm G0).val < (b.symm G1).val := hlt
        omega) (by
        rintro rfl
        have : (b.symm G1).val + 1 ≤ (b.symm G1).val := by simpa [Fin.le_def] using h1
        omega)).trans hN
    obtain ⟨a⟩ := exists_sub_equiv _ _ hlow F₀
    obtain ⟨q, hqs, hq⟩ := exists_quot_map _ _ htop F₁
    exact exists_map_two_step hBZ hD σ hc hne (isSmooth_jac e' (isSmooth_parInd _ _)) _ a q hqs
      (fun v => by rw [hmid]; exact hq v)
  · exact exists_map_of_top S hmono hN (b.symm G0) (fun t ht => hstep t ht.ne' (by
      rintro rfl
      exact absurd ht (not_lt.2 (le_of_lt hlt)))) F₀

theorem swap_equiv_of_irreducible : GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (d : Fin 2 → ℕ) (σ : ∀ i, GlobalTheory.SplitRead.Irr k (d i)), (∀ i, 0 < d i ∧ GlobalTheory.SmGL.IsCuspidal (σ i).π) → GlobalTheory.LocGL.IrrGL.of (σ 0).π (σ 0).smooth (σ 0).irr ≠ GlobalTheory.LocGL.IrrGL.of (σ 1).π (σ 1).smooth (σ 1).irr → ∀ (e : (Σ i, Fin (d i)) ≃ n) (e' : (Σ i, Fin (d (Equiv.swap 0 1 i))) ≃ n), (GlobalTheory.SmGL.multiProd e fun i => (σ i).π).IsIrreducible → (GlobalTheory.SmGL.multiProd e' fun i => (σ (Equiv.swap 0 1 i)).π).IsIrreducible → Nonempty ((GlobalTheory.SmGL.multiProd e fun i => (σ i).π).Equiv (GlobalTheory.SmGL.multiProd e' fun i => (σ (Equiv.swap 0 1 i)).π)) := by
  intro hG hBZ k _ _ _ _ n _ _ d σ hσ hne e e' h1 h2
  have key : ∃ (φ : (jac e' (multiProd e fun i => (σ i).π)).IntertwiningMap
        (piTensor fun i => (σ (Equiv.swap 0 1 i)).π)) (x : Jacquet (multiProd e fun i => (σ i).π) (unipRad k e')),
      φ x ≠ 0 := by
    by_cases hd : d 0 = d 1
    · obtain ⟨D, rfl⟩ : ∃ D, d = fun _ => D := ⟨d 0, funext fun i => by
        fin_cases i
        · rfl
        · exact hd.symm⟩
      exact exists_jac_map_of_eq k hG hBZ n (hσ 0).1 σ (fun i => (hσ i).2)
        (fun ⟨φ⟩ => hne (IrrGL.of_eq_of.2 ⟨φ⟩)) e e'
    · exact exists_jac_map_of_ne k hG n d σ hσ hd e e'
  obtain ⟨φ, x, hx⟩ := key
  obtain ⟨f, hf⟩ := (GlobalTheory.SmGL.Model.evalOne_bijective e' (isSmooth_parInd _ _)
    (piTensor fun i => (σ (Equiv.swap 0 1 i)).π)).2 φ
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hv : f v ≠ 0 := fun h => hx (by
    rw [← hf]
    show (f v).1.1 1 = 0
    rw [h]; rfl)
  exact GlobalTheory.SwapTwo.nonempty_equiv_of_apply_ne_zero h1 h2 f hv

end GlobalTheory.CompanionTheory.Hypotheses₂.TDSwap

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleTensorOfJacquetSubquotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfJacquetConstituentEmptyBlock
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.OneBlockCell

def valEquiv {β : Type} {n : β → ℕ} {t : ℕ} (a₀ : β) (ha₀ : n a₀ = t) (h0 : ∀ j, j ≠ a₀ → n j = 0) :
    (Σ j, Fin (n j)) ≃ Fin t where
  toFun p := ⟨p.2.val, by
    by_cases hp : p.1 = a₀
    · have h1 := p.2.2
      have h2 : n p.1 = t := hp ▸ ha₀
      omega
    · have h1 := p.2.2
      have h2 := h0 _ hp
      omega⟩
  invFun x := ⟨a₀, ⟨x.val, by have := x.2; omega⟩⟩
  left_inv p := by
    obtain ⟨a, s⟩ := p
    by_cases ha : a = a₀
    · subst ha
      rfl
    · have h1 := s.2
      have h2 := h0 _ ha
      omega
  right_inv x := rfl

@[simp] theorem val_valEquiv {β : Type} {n : β → ℕ} {t : ℕ} (a₀ : β) (ha₀ : n a₀ = t)
    (h0 : ∀ j, j ≠ a₀ → n j = 0) (p : Σ j, Fin (n j)) : (valEquiv a₀ ha₀ h0 p).val = p.2.val := rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deltaHalf_eq_one_of_single {β : Type} [Fintype β] [LinearOrder β] {n : β → ℕ} (a₀ : β)
    (h0 : ∀ j, j ≠ a₀ → n j = 0) (g : Levi k (fun j => Fin (n j))) :
    deltaHalf k (fun j => Fin (n j)) g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  by_cases ha : a = a₀
  · subst ha
    have hs : ∀ s : Finset β, a ∉ s → ∑ b ∈ s, (Fintype.card (Fin (n b)) : ℤ) = 0 := fun s hs =>
      Finset.sum_eq_zero fun b hb => by
        have hba : b ≠ a := fun e => hs (e ▸ hb)
        simp [h0 b hba]
    have hm : modExp (fun j => Fin (n j)) a = 0 := by
      unfold modExp
      rw [hs _ (by simp), hs _ (by simp), sub_zero]
    rw [hm]
    simp
  · haveI : IsEmpty (Fin (n a)) := ⟨fun x => absurd x.2 (by have := x.2; have := h0 a ha; omega)⟩
    have : Matrix.GeneralLinearGroup.det (g a) = 1 := by
      ext
      simp [Matrix.det_isEmpty]
    rw [this, map_one]

theorem mem_parab_of_single {R : Type} [CommRing R] {β : Type} [LinearOrder β] {n : β → ℕ} {t : ℕ}
    (e : (Σ j, Fin (n j)) ≃ Fin t) (a₀ : β) (h0 : ∀ j, j ≠ a₀ → n j = 0) (x : GL (Fin t) R) :
    x ∈ parab R e := by
  refine mem_parab_iff.2 fun a b i j hab => ?_
  by_cases ha : a = a₀
  · have hb : b ≠ a₀ := fun e => by rw [e, ha] at hab; exact lt_irrefl _ hab
    exact absurd j.2 (by have := j.2; have := h0 b hb; omega)
  · exact absurd i.2 (by have := i.2; have := h0 a ha; omega)

theorem eq_one_of_mem_unipRad_single {R : Type} [CommRing R] {β : Type} [Fintype β] [LinearOrder β]
    {n : β → ℕ} {t : ℕ} (e : (Σ j, Fin (n j)) ≃ Fin t) (a₀ : β) (h0 : ∀ j, j ≠ a₀ → n j = 0)
    {g : GL (Fin t) R} (hg : g ∈ unipRad R e) : g = 1 := by
  obtain ⟨-, h2⟩ := mem_unipRad.1 hg
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
  by_cases ha : a = a₀
  · by_cases hb : b = a₀
    · obtain rfl : b = a := hb.trans ha.symm
      rw [h2 b i j]
      simp [Matrix.one_apply]
    · exact absurd j.2 (by have := j.2; have := h0 b hb; omega)
  · exact absurd i.2 (by have := i.2; have := h0 a ha; omega)

open scoped TensorProduct

theorem reindex_piTensor {d : Fin 2 → ℕ} (σ : ∀ i, Irr k (d i)) (γ : ∀ i, GL (Fin (d i)) k)
    (p : ∀ j, GL (Fin (d (Equiv.swap 0 1 j))) k) (h : ∀ j, γ (Equiv.swap 0 1 j) = p j)
    (y : ⨂[ℂ] i, (σ i).V) :
    PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1) ((piTensor fun i => (σ i).π) γ y) =
      (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p
        (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1) y) := by
  suffices H : (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1)).toLinearMap ∘ₗ
      (piTensor fun i => (σ i).π) γ = (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p ∘ₗ
      (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1)).toLinearMap from
    LinearMap.congr_fun H y
  refine PiTensorProduct.ext (MultilinearMap.ext fun z => ?_)
  have e1 : (((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p ∘ₗ
      (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1)).toLinearMap).compMultilinearMap
        (PiTensorProduct.tprod ℂ)) z = (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p
          (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1) (PiTensorProduct.tprod ℂ z)) := rfl
  have e2 := PiTensorProduct.reindex_tprod (R := ℂ) (s := fun i => (σ i).V) (Equiv.swap 0 1) z
  have e3 := piTensor_tprod (fun j => (σ (Equiv.swap 0 1 j)).π) p (fun j => z (Equiv.swap 0 1 j))
  refine Eq.trans ?_ e1.symm
  refine Eq.trans ?_ (congrArg (fun w => (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p w) e2).symm
  refine Eq.trans ?_ e3.symm
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    piTensor_tprod, PiTensorProduct.reindex_tprod]
  refine congrArg (PiTensorProduct.tprod ℂ (s := fun j => (σ (Equiv.swap 0 1 j)).V)) (funext fun j => ?_)
  show (σ (Equiv.swap 0 1 j)).π (γ (Equiv.swap 0 1 j)) (z (Equiv.swap 0 1 j)) = _
  rw [h j]

theorem cellFunctor_swap_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)), d 1 = 1 →
    ∀ (b : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j)))), b.1 1 0 = 1 →
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j))),
      Nonempty ((cellFunctor f g (piTensor fun i => (σ i).π)).Equiv
        (piTensor fun j => (σ (Equiv.swap 0 1 j)).π)) := by
  intro k _ _ _ _ d σ hd b hb
  have r0 := b.2.1 0
  have r1 := b.2.1 1
  have c0 := b.2.2 0
  have c1 := b.2.2 1
  simp only [Fin.sum_univ_two, Fintype.card_fin, Equiv.swap_apply_left, Equiv.swap_apply_right] at r0 r1 c0 c1
  have h00 : b.1 0 0 = 0 := by omega
  have h11 : b.1 1 1 = 0 := by omega
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

end GlobalTheory.OneBlockCell

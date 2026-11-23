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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CellCentral

open scoped TensorProduct

theorem twKer_piTensor_eq_top {α : Type} [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (N : Subgroup (∀ a, Γ a)) (a : α) (Na : Subgroup (Γ a)) (hN : ∀ u ∈ Na, Pi.mulSingle a u ∈ N)
    (h : twKer (ρ a) Na 1 = ⊤) : twKer (piTensor ρ) N 1 = ⊤ := by
  refine eq_top_iff.2 fun y hy0 => ?_
  clear hy0
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => exact add_mem hx hy
  | smul_tprod r x =>
    refine Submodule.smul_mem _ r ?_
    let L := (PiTensorProduct.tprod ℂ : MultilinearMap ℂ X (⨂[ℂ] i, X i)).toLinearMap x a
    have hL : ∀ w, L w = PiTensorProduct.tprod ℂ (Function.update x a w) := fun w => rfl
    have hle : twKer (ρ a) Na 1 ≤ (twKer (piTensor ρ) N 1).comap L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, v, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have hpi : piTensor ρ (Pi.mulSingle a (u : Γ a)) (PiTensorProduct.tprod ℂ (Function.update x a v)) =
          PiTensorProduct.tprod ℂ (Function.update x a (ρ a u v)) := by
        rw [piTensor_tprod]
        congr 1
        funext b
        by_cases hb : b = a
        · subst hb; simp
        · simp [Pi.mulSingle_eq_of_ne hb, Function.update_of_ne hb]
      refine Submodule.subset_span ⟨⟨_, hN u u.2⟩, PiTensorProduct.tprod ℂ (Function.update x a v), ?_⟩
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      rw [map_sub, hL, hL, hpi]
    have hx : x a ∈ twKer (ρ a) Na 1 := h ▸ Submodule.mem_top
    have := hle hx
    simpa [hL] using this

theorem deltaHalf_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (hm : ∀ a b, a ≠ b → IsEmpty (m a) ∨ IsEmpty (m b)) (g : Levi k m) : deltaHalf k m g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  by_cases ha : IsEmpty (m a)
  · have : Matrix.GeneralLinearGroup.det (g a) = 1 := Units.ext (by simp [Matrix.det_isEmpty])
    rw [this, map_one]
  · have h0 : modExp m a = 0 := by
      unfold modExp
      rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
      · intro b hb
        have hne : b ≠ a := by rintro rfl; simp at hb
        have : IsEmpty (m b) := (hm a b hne.symm).resolve_left ha
        simp
      · intro b hb
        have hne : b ≠ a := by rintro rfl; simp at hb
        have : IsEmpty (m b) := (hm a b hne.symm).resolve_left ha
        simp
    simp [h0]

theorem smInd_central {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W]
    [Module ℂ W] (H : Subgroup G) (σ : Representation ℂ H W) (z : G) (hz : z ∈ H)
    (hcen : ∀ x, x * z = z * x) (c : ℂ) (hc : ∀ w, σ ⟨z, hz⟩ w = c • w) (F : smoothPart (ind H σ)) :
    smInd H σ z F = c • F := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  show F.1.1 (x * z) = c • F.1.1 x
  rw [hcen x]
  exact (F.1.2 ⟨z, hz⟩ x).trans (hc _)

theorem one_case (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (σ : Fin 2 → Irr k 1) (hσ : ∀ i, 0 < 1 ∧ IsCuspidal (σ i).π)
    (hnt : ¬ Nonempty ((σ 0).π.Equiv (twist (σ 1).π (detChar (Fin 1) (unrChar k 1))))) :
    ∃ (z : Levi k fun _ : Fin 2 => Fin 1) (c c' : ℂ), (∀ g, g * z = z * g) ∧ c ≠ c' ∧
      (∀ x, (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) z x = c • x) ∧
      ∀ (b : SizeMatrix (fun _ : Fin 2 => Fin 1) (fun _ : Fin 2 => Fin 1)),
        b.1 1 0 = 0 → ∀ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin 1)
          (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin 1) y,
          cellFunctor f g (piTensor fun i => (σ i).π) z y = c' • y := by
  have hact : ∀ i (ψ : kˣ →* ℂˣ), (σ i).π.Equiv (detRep (Fin 1) ψ) → ∀ (g : GL (Fin 1) k) v,
      (σ i).π g v = (ψ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
    intro i ψ e g v
    apply EquivLike.injective e
    have h1 : e ((σ i).π g v) = detRep (Fin 1) ψ g (e v) :=
      LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) v
    rw [h1, map_smul]
    simp [detRep, detChar_apply, smul_eq_mul]
  have h0 := RankLeOne.exists_equiv_detRep k (Fin 1) (σ 0).V (σ 0).π (σ 0).smooth (σ 0).irr
  have h1 := RankLeOne.exists_equiv_detRep k (Fin 1) (σ 1).V (σ 1).π (σ 1).smooth (σ 1).irr
  obtain ⟨ψ₀, -, ⟨e₀⟩⟩ := h0
  obtain ⟨ψ₁, -, ⟨e₁⟩⟩ := h1
  have hψ : ∃ t, ψ₀ t ≠ ψ₁ t := by
    by_contra hc
    push_neg at hc
    have hu : unrChar k 1 = 1 := MonoidHom.ext fun x => by simp [unrChar_apply]
    have hdet : detChar (Fin 1) (1 : kˣ →* ℂˣ) = (1 : GL (Fin 1) k →* ℂˣ) :=
      MonoidHom.ext fun x => by simp
    have hψe : ψ₀ = ψ₁ := MonoidHom.ext hc
    subst hψe
    rw [hu, hdet, twist_one] at hnt
    exact hnt ⟨e₀.trans e₁.symm⟩
  obtain ⟨t, ht⟩ := hψ
  let z : Levi k fun _ : Fin 2 => Fin 1 := Pi.mulSingle 0 (Matrix.GeneralLinearGroup.scalar (Fin 1) t)
  have hcomm : ∀ (g h : GL (Fin 1) k), g * h = h * g := by
    intro g h
    ext a b
    fin_cases a; fin_cases b
    simp [Matrix.mul_apply, mul_comm]
  have hcen : ∀ g, g * z = z * g := fun g => funext fun j => hcomm _ _
  refine ⟨z, ψ₁ t, ψ₀ t, hcen, fun h => ht (Units.ext h).symm, ?_, ?_⟩
  · intro x
    refine GlobalTheory.ProdSupport.piTensor_mulSingle _ 0 _ _ (fun v => ?_) x
    have hs : Equiv.swap (0 : Fin 2) 1 0 = 1 := by simp
    rw [hact _ ψ₁ (hs ▸ e₁), GlobalTheory.ProdSupport.det_scalar_one rfl]
  · intro b hb f g y
    have hr0 := b.2.1 0
    have hr1 := b.2.1 1
    have hc0 := b.2.2 0
    have hc1 := b.2.2 1
    simp only [Fin.sum_univ_two, Fintype.card_fin] at hr0 hr1 hc0 hc1
    have h01 : b.1 0 1 = 0 := by omega
    have hoff : ∀ i j : Fin 2, i ≠ j → b.1 i j = 0 := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have hemp : ∀ i j : Fin 2, i ≠ j → IsEmpty (Fin (b.1 i j)) := fun i j hij => by
      rw [hoff i j hij]; infer_instance
    have hz : z ∈ relParab k g := by
      refine (Subgroup.mem_pi _).2 fun j _ => mem_parab.2 fun p q hpq => ?_
      rw [Subsingleton.elim p q] at hpq
      exact absurd hpq (lt_irrefl _)
    have hA : relDeltaHalf k (fun j i => Fin (b.1 i j)) (relProj k g ⟨z, hz⟩) = 1 := by
      rw [relDeltaHalf_apply]
      refine Finset.prod_eq_one fun j _ => deltaHalf_eq_one _ (fun a a' haa' => ?_) _
      by_cases h : a = j
      · subst h; exact Or.inr (hemp a' a (Ne.symm haa'))
      · exact Or.inl (hemp a j h)
    have hB : ∀ P, relDeltaHalf k (fun i j => Fin (b.1 i j)) P = 1 := by
      intro P
      rw [relDeltaHalf_apply]
      refine Finset.prod_eq_one fun i _ => deltaHalf_eq_one _ (fun a a' haa' => ?_) _
      by_cases h : a = i
      · subst h; exact Or.inr (hemp a a' haa')
      · exact Or.inl (hemp i a (Ne.symm h))
    have hC : relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g ⟨z, hz⟩)) =
        (Pi.mulSingle (0 : Fin 2) (Matrix.GeneralLinearGroup.scalar (Fin 1) t) : Levi k fun _ : Fin 2 => Fin 1) := by
      funext i
      ext p q
      obtain rfl : p = q := Subsingleton.elim p q
      obtain ⟨⟨j, r⟩, hr⟩ := (f i).surjective p
      subst hr
      rw [relEmb_apply, leviEmb_apply_same]
      have hij : i = j := by
        by_contra hne
        have := r.2
        have h0 := hoff i j hne
        omega
      subst hij
      show ((z i : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) (g i ⟨i, r⟩) (g i ⟨i, r⟩) = _
      rw [Subsingleton.elim (g i ⟨i, r⟩) (f i ⟨i, r⟩)]
    refine smInd_central _ _ z hz hcen _ (fun w => ?_) y
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    simp only [MonoidHom.comp_apply, twist_apply, relJac_mk, hA, hB, hC, inv_one, Units.val_one, one_smul]
    rw [GlobalTheory.ProdSupport.piTensor_mulSingle _ 0 _ _ (hact 0 ψ₀ e₀ _), GlobalTheory.ProdSupport.det_scalar_one rfl,
      Submodule.Quotient.mk_smul]

theorem exists_central_scalar_ne_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)), (∀ i, 0 < d i ∧ IsCuspidal (σ i).π) → d 1 = 1 →
    (∀ (h : d 0 = d 1) (α : ℂˣ), ¬ Nonempty ((h ▸ σ 0 : Irr k (d 1)).π.Equiv
      (twist (σ 1).π (detChar (Fin (d 1)) (unrChar k α))))) →
    ∃ (z : Levi k fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j))) (c c' : ℂ), (∀ g, g * z = z * g) ∧ c ≠ c' ∧
      (∀ x, (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) z x = c • x) ∧
      ∀ (b : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j)))),
        b.1 1 0 = 0 → ∀ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i))
          (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j))) y,
          cellFunctor f g (piTensor fun i => (σ i).π) z y = c' • y := by
  intro k _ _ _ _ d σ hσ hd1 hnt
  by_cases hd0 : d 0 = 1
  · have hd : d = fun _ => 1 := by
      funext i
      fin_cases i
      · exact hd0
      · exact hd1
    subst hd
    exact one_case k σ hσ (hnt rfl 1)
  · refine ⟨1, 1, 2, fun g => by simp, by norm_num, fun x => by simp, ?_⟩
    intro b hb f g y
    have hr0 := b.2.1 0
    have hr1 := b.2.1 1
    have hc0 := b.2.2 0
    have hc1 := b.2.2 1
    simp only [Fin.sum_univ_two, Fintype.card_fin, Equiv.swap_apply_left, Equiv.swap_apply_right] at hr0 hr1 hc0 hc1
    have hpos := (hσ 0).1
    have h00 : b.1 0 0 = 1 := by omega
    have h01 : 0 < b.1 0 1 := by omega
    have hne : unipRad k (f 0) ≠ ⊥ := by
      refine CuspMax.unipRad_ne_bot_iff.2 ⟨f 0 ⟨0, ⟨0, by omega⟩⟩, f 0 ⟨1, ⟨0, h01⟩⟩, ?_⟩
      simp
    have hJ : twKer (σ 0).π (unipRad k (f 0)) 1 = ⊤ :=
      Submodule.Quotient.subsingleton_iff.1 ((hσ 0).2.2 2 (b.1 0) (f 0) hne)
    have hT : twKer (piTensor fun i => (σ i).π) (relUnip k f) 1 = ⊤ := by
      refine twKer_piTensor_eq_top _ _ 0 _ (fun u hu => ?_) hJ
      refine (Subgroup.mem_pi _).2 fun i _ => ?_
      by_cases hi : i = 0
      · subst hi; simpa using hu
      · rw [Pi.mulSingle_eq_of_ne hi]; exact one_mem _
    haveI : Subsingleton (Jacquet (piTensor fun i => (σ i).π) (relUnip k f)) :=
      Submodule.Quotient.subsingleton_iff.2 hT
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact Subsingleton.elim (α := Jacquet (piTensor fun i => (σ i).π) (relUnip k f)) _ _

end GlobalTheory.CellCentral

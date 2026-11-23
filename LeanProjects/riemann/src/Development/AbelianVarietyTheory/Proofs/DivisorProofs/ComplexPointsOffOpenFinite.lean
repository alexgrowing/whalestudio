import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.SurfacePoints

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsIntegral X]

theorem genericPoint_mem_of_lt (hX : IsArithVar p 1) {A B C : IrreducibleCloseds X} (h₁ : A < B)
    (h₂ : B < C) : genericPoint X ∈ C := by
  by_contra h
  let T : IrreducibleCloseds X := ⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have h₃ : C < T := lt_of_le_not_ge (subset_univ _) fun e => h (e (mem_univ _))
  have e₁ := Order.height_add_one_le h₁
  have e₂ := Order.height_add_one_le h₂
  have e₃ := Order.height_add_one_le h₃
  have e₄ : ((Order.height T : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) :=
    (Order.height_le_krullDim T).trans hX.dim_eq.le
  have e₅ : (0 : ℕ∞) + 1 + 1 + 1 ≤ 2 :=
    (add_le_add_left ((add_le_add_left ((add_le_add_left zero_le 1).trans e₁) 1).trans e₂) 1).trans
      (e₃.trans (WithBot.coe_le_coe.1 e₄))
  exact absurd e₅ (by decide)

theorem finite_hom (hX : IsArithVar p 1) {x : X} (hx : x ≠ genericPoint X) :
    Finite (X.residueField x ⟶ CommRingCat.of ℂ) := by
  rcases isEmpty_or_nonempty (X.residueField x ⟶ CommRingCat.of ℂ) with h | ⟨⟨f⟩⟩
  · infer_instance
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  have hbij : Function.Bijective (i.residueFieldMap (genericPoint Z)).hom := by
    refine ⟨RingHom.injective _, fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
    obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
    exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩
  let E := RingEquiv.ofBijective _ hbij
  have hc' : CharZero (Z.residueField (genericPoint Z)) :=
    (RingHom.charZero_iff hbij.1).1 f.hom.charZero
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have h₁ : topologicalKrullDim Z ≤ 1 := Order.krullDim_le_one_iff.2 fun B => by
    by_contra h
    obtain ⟨hA, hC⟩ := not_or.1 h
    obtain ⟨A, hA⟩ := not_isMin_iff.1 hA
    obtain ⟨C, hC⟩ := not_isMax_iff.1 hC
    have hm := IrreducibleCloseds.map_strictMono_of_isInducing i.isClosedEmbedding.isInducing
    have hg : genericPoint X ∈ closure (i '' C) := genericPoint_mem_of_lt hX (hm hA) (hm hC)
    have h₂ := (genericPoint_spec Z).image i.continuous
    exact hx ((h₂.specializes (closure_mono (image_mono (subset_univ _)) hg)).antisymm
      (genericPoint_specializes _)).eq
  obtain ⟨d, hd⟩ := hX.exists_dim_eq i
  have h₀ := hX.dim_ne_zero i hcΓ
  obtain rfl : d = 0 + 1 := by
    rw [hd] at h₀ h₁
    norm_cast at h₀ h₁
    omega
  have := SmallSecHeight.numberField (hX.of_isClosedImmersion i hcΓ hd) hc'
  refine Finite.of_injective (fun g => g.hom.comp E.symm.toRingHom) fun g g' e => ?_
  exact CommRingCat.hom_ext ((RingHom.cancel_right E.symm.surjective).1 e)

theorem finite_charZero (hX : IsArithVar p 1) {U : X.Opens} (hU : genericPoint X ∈ U) :
    {x : X | x ∉ U ∧ CharZero (X.residueField x)}.Finite := by
  classical
  have := hX.isNoetherian
  obtain ⟨S, hS, hc, hi, hZ⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  refine (hS.image fun T => if h : IsIrreducible T then h.genericPoint else genericPoint X).subset
    fun x ⟨hx, _⟩ => ?_
  obtain ⟨T, hT, hxT⟩ := mem_sUnion.1 (hZ.le hx)
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos (hi T hT)]
  refine ((hi T hT).isGenericPoint_genericPoint (hc T hT)).eq ?_
  by_contra hne
  let C (w : X) : IrreducibleCloseds X :=
    ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hle : closure {x} ⊆ T := closure_minimal (singleton_subset_iff.2 hxT) (hc T hT)
  have h₂ : C x < ⟨T, hi T hT, hc T hT⟩ := lt_of_le_not_ge hle fun e => hne (hle.antisymm e)
  obtain ⟨z, hz, hz'⟩ := (isClosed_closure (s := {x})).exists_closed_singleton ⟨x, subset_closure rfl⟩
  have h₁ : C z < C x :=
    lt_of_le_not_ge (closure_minimal (singleton_subset_iff.2 hz) isClosed_closure) fun e => by
      obtain rfl : x = z := hz'.closure_subset (e (subset_closure rfl))
      have := hX.finite_residueField hz'
      exact not_finite (X.residueField x)
  exact hZ.ge (mem_sUnion.2 ⟨T, hT, genericPoint_mem_of_lt hX h₁ h₂⟩) hU

theorem finite_compl_ptsIn : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X],
    IsArithVar p 1 → ∀ U : X.Opens, genericPoint X ∈ U → ∀ σ : k →+* ℂ, (ptsIn p σ U)ᶜ.Finite := by
  intro k _ X p _ hX U hU σ
  have hF := finite_charZero hX hU
  have := hF.to_subtype
  have (x : {x : X | x ∉ U ∧ CharZero (X.residueField x)}) :
      Finite (X.residueField x.1 ⟶ CommRingCat.of ℂ) := finite_hom hX fun e => x.2.1 (e ▸ hU)
  refine ((finite_range fun s : Σ x : {x : X | x ∉ U ∧ CharZero (X.residueField x)},
    (X.residueField x.1 ⟶ CommRingCat.of ℂ) => (Scheme.SpecToEquivOfField ℂ X).symm ⟨s.1.1, s.2⟩).preimage
    Subtype.val_injective.injOn).subset fun y hy => ?_
  exact ⟨⟨⟨_, mt mem_ptsIn.2 hy, (Scheme.SpecToEquivOfField ℂ X y.1).2.hom.charZero⟩,
    (Scheme.SpecToEquivOfField ℂ X y.1).2⟩, (Scheme.SpecToEquivOfField ℂ X).symm_apply_apply y.1⟩

end GlobalTheory.SurfacePoints

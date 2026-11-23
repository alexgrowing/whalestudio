import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogPull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.ClosedPtIsog

theorem charP_of_notMem_basicOpen {X : Scheme.{0}} {k : Type} [Field k] {p : ℕ} (hp : p.Prime) (h : Sp k ⟶ X)
    (hz : h (IsLocalRing.closedPoint k) ∉ X.basicOpen ((p : ℕ) : Γ(X, ⊤))) : CharP k p := by
  refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
  by_contra hne
  apply hz
  have hu : IsUnit ((p : ℕ) : Γ(Sp k, h ⁻¹ᵁ ⊤)) := by
    have := (IsUnit.mk0 _ hne).map
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.map (homOfLE (le_top (a := h ⁻¹ᵁ ⊤))).op).hom)
    rwa [map_natCast] at this
  have hm : IsLocalRing.closedPoint k ∈ h ⁻¹ᵁ X.basicOpen ((p : ℕ) : Γ(X, ⊤)) := by
    rw [Scheme.preimage_basicOpen, map_natCast, Scheme.basicOpen_of_isUnit _ hu]
    trivial
  exact hm

theorem exists_isPIsog_closedPoint : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ z : M.X, z ∉ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)) → {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z} ⊆ {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u} := by
  intro p _ D R _ _ _ _ b N hN hNp _ c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ z hz u hu
  obtain ⟨V, K, _, _, _, _, _, _, y', z', x, hy, hz', hyu, hzz⟩ := hu
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V K
  have hyz : y' ≫ M.s = z' ≫ M.s :=
    GlobalTheory.ExtUnique.hom_ext_of_dominant (Spec.map (CommRingCat.ofHom (Int.castRingHom R))) (specZIsTerminal.hom_ext _ _)
      (spMap (algebraMap V K)) (by rw [reassoc_of% hy, reassoc_of% hz', hst])
  have pull : ∀ {S S' : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (f : S' ⟶ S) (σ : S' ⟶ Sp R), f ≫ s = σ →
      ∃ o₁ : Obj b N σ, Nonempty (ObjMap o₁ o f) := by
    rintro S S' s o f σ rfl
    exact GlobalTheory.HTPull.exists_objMap_pull p D R b N S S' s f o
  obtain ⟨oV, ⟨mV⟩⟩ := pull M.univ y' (z' ≫ M.s) hyz
  obtain ⟨oV', ⟨mV'⟩⟩ := pull M.univ z' (z' ≫ M.s) rfl
  obtain ⟨oK, ⟨nK⟩⟩ := pull o₀ x _ rfl
  obtain ⟨oK', ⟨nK'⟩⟩ := pull o₀' x _ rfl
  obtain ⟨ψK, hψK, -⟩ := ValExt.isPIsog_pull p D R b N c _ _ _ _ x o₀ o₀' oK oK' nK nK' ψ₀ hψ
  have m₁ : ObjMap oK M.univ (spMap (algebraMap V K) ≫ y') := hy ▸ GlobalTheory.UPel.HT.ObjMap.comp nK ms₀
  have m₁' : ObjMap oK' M.univ (spMap (algebraMap V K) ≫ z') := hz' ▸ GlobalTheory.UPel.HT.ObjMap.comp nK' mt₀
  obtain ⟨n₁, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m₁ mV
  obtain ⟨n₁', -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m₁' mV'
  obtain ⟨e, he⟩ := hψ.exists_eq_pow
  have hdom : IsDominant (spMap (algebraMap V K)) := inferInstance
  obtain ⟨ψV, hψV, -⟩ := PIsogExt.exists_isPIsog_extend p D R b N hN hNp 0 c
    ⟨e, he, fun h => absurd h (lt_irrefl 0)⟩ _ _ (spMap (algebraMap V K)) _ (z' ≫ M.s)
    (GlobalTheory.isOpenImmersion_spMap_of_isDiscreteValuationRing V K) hdom inferInstance
    (fun y => (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_Sp V y).2)
    (fun y => (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_Sp V y).1) oV oV' oK oK' n₁ n₁' ψK hψK
  let k := AlgebraicClosure (IsLocalRing.ResidueField V)
  let φ : V →+* k := (algebraMap (IsLocalRing.ResidueField V) k).comp (IsLocalRing.residue V)
  let g : Sp k ⟶ Sp V := spMap φ
  have hg : g (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint φ
  have hζ : (g ≫ z') (IsLocalRing.closedPoint k) = z :=
    (Scheme.Hom.comp_apply g z' _).trans ((congrArg z' hg).trans hzz)
  have hυ : (g ≫ y') (IsLocalRing.closedPoint k) = u :=
    (Scheme.Hom.comp_apply g y' _).trans ((congrArg y' hg).trans hyu)
  obtain ⟨ou, ⟨nu⟩⟩ := pull oV g ((g ≫ z') ≫ M.s) (Category.assoc _ _ _).symm
  obtain ⟨oz, ⟨nz⟩⟩ := pull oV' g ((g ≫ z') ≫ M.s) (Category.assoc _ _ _).symm
  obtain ⟨ψk, hψk, -⟩ := ValExt.isPIsog_pull p D R b N c _ _ _ _ g oV oV' ou oz nu nz ψV hψV
  exact ⟨k, inferInstance, inferInstance, charP_of_notMem_basicOpen Fact.out (g ≫ z') (hζ ▸ hz), g ≫ z', g ≫ y', ou, oz,
    GlobalTheory.UPel.HT.ObjMap.comp nu mV, GlobalTheory.UPel.HT.ObjMap.comp nz mV', ψk,
    by rw [Category.assoc, Category.assoc, hyz], hψk, hζ, hυ⟩

end GlobalTheory.UPel.HT.ES.ClosedPtIsog

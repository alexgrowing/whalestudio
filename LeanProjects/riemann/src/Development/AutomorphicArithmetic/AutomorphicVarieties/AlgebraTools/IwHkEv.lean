import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]

private theorem hkEv_coe (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (x : G)
    (v : fixd ρ I) : (hk ρ I x v : M) = dc ρ I I x v := by
  have h := (UpperTheory.V.Hi.dcSum A G M ρ I I x (hI x)).2.1
  unfold hk hk2
  rw [dif_pos h]
  rfl

private noncomputable def hkEv_phi (ρ : Representation A G M) (I : Subgroup G) (m : M) :
    MonoidAlgebra A (G ⧸ I) →ₗ[A] M :=
  Finsupp.linearCombination A (fun q : G ⧸ I => ρ q.out m) ∘ₗ (MonoidAlgebra.coeffLinearEquiv A).toLinearMap

private theorem hkEv_phi_single (ρ : Representation A G M) (I : Subgroup G) (m : fixd ρ I) (g : G) (c : A) :
    hkEv_phi ρ I m (MonoidAlgebra.single (g : G ⧸ I) c) = c • ρ g m := by
  have h1 : g⁻¹ * (g : G ⧸ I).out ∈ I := QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
  have h2 : ρ (g⁻¹ * (g : G ⧸ I).out) m = m := m.2 _ h1
  have h3 : ρ (g : G ⧸ I).out m = ρ g m := by
    calc ρ (g : G ⧸ I).out m = ρ (g * (g⁻¹ * (g : G ⧸ I).out)) m := by rw [mul_inv_cancel_left]
      _ = ρ g (ρ (g⁻¹ * (g : G ⧸ I).out) m) := by rw [map_mul ρ g]; rfl
      _ = ρ g m := by rw [h2]
  rw [← h3]
  simp [hkEv_phi]

private theorem hkEv_phi_equiv (ρ : Representation A G M) (I : Subgroup G) (m : fixd ρ I) (h : G)
    (a : MonoidAlgebra A (G ⧸ I)) : hkEv_phi ρ I m (permRep A I h a) = ρ h (hkEv_phi ρ I m a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single q c =>
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Representation.ofMulAction_single]
    have : h • (g : G ⧸ I) = ((h * g : G) : G ⧸ I) := rfl
    rw [this, hkEv_phi_single, hkEv_phi_single, map_smul, map_mul]
    rfl

private noncomputable def hkEv_psi (ρ : Representation A G M) (I : Subgroup G) (m : fixd ρ I) :
    fixd (permRep A I) I →ₗ[A] fixd ρ I :=
  (hkEv_phi ρ I m).restrict (fun a ha u hu => by rw [← hkEv_phi_equiv, ha u hu])

private theorem hkEv_psi_hk (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (m : fixd ρ I)
    (x : G) (a : fixd (permRep A I) I) :
    hkEv_psi ρ I m (hk (permRep A I) I x a) = hk ρ I x (hkEv_psi ρ I m a) := by
  apply Subtype.ext
  rw [hkEv_coe ρ I hI]
  change hkEv_phi ρ I m (hk (permRep A I) I x a : MonoidAlgebra A (G ⧸ I)) = dc ρ I I x (hkEv_phi ρ I m a)
  rw [hkEv_coe _ I hI]
  exact (UpperTheory.V.Hi.dcSum A G _ (permRep A I) I I x (hI x)).2.2.2 A M ρ
    (hkEv_phi ρ I m).toAddMonoidHom (hkEv_phi_equiv ρ I m) a

private theorem hkEv_psi_surj (ρ : Representation A G M) (I : Subgroup G) (m : fixd ρ I) :
    ∃ a, hkEv_psi ρ I m a = m := by
  refine ⟨⟨MonoidAlgebra.single ((1 : G) : G ⧸ I) 1, fun u hu => ?_⟩, Subtype.ext ?_⟩
  · rw [Representation.ofMulAction_single]
    congr 1
    change ((u * 1 : G) : G ⧸ I) = _
    exact QuotientGroup.eq.mpr (by simpa using hu)
  · change hkEv_phi ρ I m (MonoidAlgebra.single ((1 : G) : G ⧸ I) 1) = m
    rw [hkEv_phi_single]
    simp

private def hkEv_R (ρ : Representation A G M) (I : Subgroup G)
    (T : Module.End A (fixd (permRep A I) I)) (E : Module.End A (fixd ρ I)) : Prop :=
  ∀ m a, hkEv_psi ρ I m (T a) = E (hkEv_psi ρ I m a)

private theorem hkEv_uniq {ρ : Representation A G M} {I : Subgroup G}
    {T : Module.End A (fixd (permRep A I) I)} {E E' : Module.End A (fixd ρ I)}
    (h : hkEv_R ρ I T E) (h' : hkEv_R ρ I T E') : E = E' := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨a, ha⟩ := hkEv_psi_surj ρ I m
  rw [← ha, ← h, ← h']

private theorem hkEv_alg (ρ : Representation A G M) (I : Subgroup G) (c : A) :
    hkEv_R ρ I (algebraMap A _ c) (algebraMap A _ c) := fun m a => by
  simp only [Module.algebraMap_end_apply, map_smul]

private theorem hkEv_add {ρ : Representation A G M} {I : Subgroup G}
    {T T' : Module.End A (fixd (permRep A I) I)} {E E' : Module.End A (fixd ρ I)}
    (h : hkEv_R ρ I T E) (h' : hkEv_R ρ I T' E') : hkEv_R ρ I (T + T') (E + E') := fun m a => by
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add, h, h']

private theorem hkEv_mul {ρ : Representation A G M} {I : Subgroup G}
    {T T' : Module.End A (fixd (permRep A I) I)} {E E' : Module.End A (fixd ρ I)}
    (h : hkEv_R ρ I T E) (h' : hkEv_R ρ I T' E') : hkEv_R ρ I (T * T') (E * E') := fun m a => by
  rw [Module.End.mul_apply, Module.End.mul_apply, h, h']

private theorem hkEv_ex (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (T : HkAlg A I) :
    ∃ E, hkEv_R ρ I T.1 E := by
  obtain ⟨T, hT⟩ := T
  induction hT using Algebra.adjoin_induction with
  | mem T h =>
    obtain ⟨x, rfl⟩ := h
    exact ⟨hk ρ I x, fun m a => hkEv_psi_hk ρ I hI m x a⟩
  | algebraMap c => exact ⟨_, hkEv_alg ρ I c⟩
  | add T T' _ _ h h' =>
    obtain ⟨E, h⟩ := h
    obtain ⟨E', h'⟩ := h'
    exact ⟨_, hkEv_add h h'⟩
  | mul T T' _ _ h h' =>
    obtain ⟨E, h⟩ := h
    obtain ⟨E', h'⟩ := h'
    exact ⟨_, hkEv_mul h h'⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.hkEv :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I : Subgroup G), HeckePair I → ∃ ev : HkAlg A I →ₐ[A] Module.End A (fixd ρ I), ∀ x : G, ev (hT A I x) = hk ρ I x := by
  intro A G M _ _ _ _ ρ I hI
  choose f hf using hkEv_ex ρ I hI
  have halg : ∀ c : A, f (algebraMap A _ c) = algebraMap A _ c := fun c =>
    hkEv_uniq (hf _) (hkEv_alg ρ I c)
  refine ⟨{ toFun := f
            map_one' := by simpa using halg 1
            map_mul' := fun T T' => hkEv_uniq (hf _) (hkEv_mul (hf T) (hf T'))
            map_zero' := by simpa using halg 0
            map_add' := fun T T' => hkEv_uniq (hf _) (hkEv_add (hf T) (hf T'))
            commutes' := halg }, fun x => ?_⟩
  exact hkEv_uniq (hf _) (fun m a => hkEv_psi_hk ρ I hI m x a)

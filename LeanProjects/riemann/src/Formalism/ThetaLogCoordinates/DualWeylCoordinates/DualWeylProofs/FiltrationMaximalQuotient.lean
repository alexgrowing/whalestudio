import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.MemSpanStandardIffProjZero

noncomputable section

open Finset Module

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

lemma qb_std_can (mu : Fin n → ℤ) : StdT (canT mu) := by
  intro c hc t
  apply card_le_card
  apply filter_subset_filter
  intro b hb
  rw [qb_mem_canT] at hb ⊢
  refine lt_of_lt_of_le hb ?_
  unfold colH
  refine card_le_card fun m hm => ?_
  simp only [mem_filter, mem_univ, true_and] at hm ⊢
  omega

def standardBasis (hS : SBasis) (mu : Fin n → ℤ) (hmu : Dominant mu) : Basis {I : TIdx mu // StdT I} ℤ ↥(SMu mu) :=
  (Basis.span (hS n mu hmu).1).map (LinearEquiv.ofEq _ _ (hS n mu hmu).2)

lemma standardBasis_coe (hS : SBasis) (mu : Fin n → ℤ) (hmu : Dominant mu) (I : {I : TIdx mu // StdT I}) :
    ((standardBasis hS mu hmu I : ↥(SMu mu)) : GLCoord ℤ n) = brk mu I.1 := by
  simp [standardBasis]

def qb_bS (hS : SBasis) {nu mu : Fin n → ℤ} (hnu : Dominant nu) (h : nu = mu) :
    Basis {I : TIdx nu // StdT I} ℤ ↥(SMu mu) := h ▸ standardBasis hS nu hnu

lemma qb_bS_coe (hS : SBasis) {nu mu : Fin n → ℤ} (hnu : Dominant nu) (h : nu = mu) (I : {I : TIdx nu // StdT I}) :
    ((qb_bS hS hnu h I : ↥(SMu mu)) : GLCoord ℤ n) = brk nu I.1 := by
  subst h
  exact standardBasis_coe hS nu hnu I

def qb_canIdx {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) (j : {j : CF.J // CF.mu j = mu}) : qb_Idx CF :=
  ⟨j.1, canT _, qb_std_can _⟩

lemma qb_canIdx_inj {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) : Function.Injective (qb_canIdx CF mu) :=
  fun j j' h => Subtype.ext (congrArg Sigma.fst h)

lemma qb_can_li (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) :
    LinearIndependent ℤ (fun j : {j : CF.J // CF.mu j = mu} => CF.vec j.1 (canT (CF.mu j.1))) := by
  have h := (qb_basisR hA CF ℤ).1
  rw [qb_vecF_int] at h
  exact h.comp (qb_canIdx CF mu) (qb_canIdx_inj CF mu)

lemma qb_can_span {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) :
    Submodule.span ℤ (Set.range fun j : {j : CF.J // CF.mu j = mu} => CF.vec j.1 (canT (CF.mu j.1))) = CF.MM mu := by
  unfold ColFam.MM
  congr 1
  ext x
  constructor
  · rintro ⟨⟨j, hj⟩, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩

def qb_bM (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) :
    Basis {j : CF.J // CF.mu j = mu} ℤ ↥(CF.MM mu) :=
  (Basis.span (qb_can_li hA CF mu)).map (LinearEquiv.ofEq _ _ (qb_can_span CF mu))

lemma qb_bM_coe (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) (j : {j : CF.J // CF.mu j = mu}) :
    ((qb_bM hA CF mu j : ↥(CF.MM mu)) : M.ι → ℤ) = CF.vec j.1 (canT (CF.mu j.1)) := by
  simp [qb_bM]

section abs

variable {R : Type*} [CommRing R] {V A B W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup W] [Module R W] {ι κ : Type*} [DecidableEq κ] {φ : κ → Type*}

def qb_aT (bA : ∀ k, Basis (φ k) R A) (bB : Basis κ R B) : Basis (Σ k, φ k) R (TensorProduct R A B) :=
  (Finsupp.basis bA).map (TensorProduct.equivFinsuppOfBasisRight bB).symm

lemma qb_aT_apply (bA : ∀ k, Basis (φ k) R A) (bB : Basis κ R B) (x : Σ k, φ k) :
    qb_aT bA bB x = bA x.1 x.2 ⊗ₜ bB x.1 := by
  rw [qb_aT, Basis.map_apply, Finsupp.coe_basis, TensorProduct.equivFinsuppOfBasisRight_symm_apply]
  exact Finsupp.sum_single_index (TensorProduct.zero_tmul _ _)

def qb_aPsi (b : Basis ι R V) (s : Set ι) (c : Basis ↥s R W) : V →ₗ[R] W :=
  c.repr.symm.toLinearMap ∘ₗ Finsupp.lsubtypeDomain s ∘ₗ b.repr.toLinearMap

lemma qb_aPsi_basis (b : Basis ι R V) (s : Set ι) (c : Basis ↥s R W) (i : ι) (hi : i ∈ s) :
    qb_aPsi b s c (b i) = c ⟨i, hi⟩ := by
  classical
  simp only [qb_aPsi, LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.repr_self]
  rw [← Basis.repr_symm_single_one]
  congr 1
  ext z
  simp only [Finsupp.lsubtypeDomain_apply, Finsupp.subtypeDomain_apply, Finsupp.single_apply]
  congr 1
  exact propext ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

lemma qb_aPsi_eq_zero_iff (b : Basis ι R V) (s : Set ι) (c : Basis ↥s R W) (x : V) :
    qb_aPsi b s c x = 0 ↔ ∀ i ∈ s, b.repr x i = 0 := by
  simp only [qb_aPsi, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff]
  rw [Finsupp.ext_iff]
  constructor
  · intro h y hy; exact h ⟨y, hy⟩
  · rintro h ⟨y, hy⟩; exact h y hy

lemma qb_quot_equiv {N T : Type*} [AddCommGroup N] [Module R N] [AddCommGroup T] [Module R T]
    (f : N →ₗ[R] T) (hs : Function.Surjective f) (p : Submodule R N) (hk : LinearMap.ker f = p) :
    ∃ Phi : (N ⧸ p) ≃ₗ[R] T, ∀ x, Phi (Submodule.Quotient.mk x) = f x := by
  subst hk
  exact ⟨f.quotKerEquivOfSurjective hs, fun x => f.quotKerEquivOfSurjective_apply_mk hs x⟩

theorem qb_aQuot (b : Basis ι R V) (s t : Set ι) (hst : s ⊆ t) (c : Basis ↥s R W) (P Q : Submodule R V)
    (hP : P = Submodule.span R (b '' t)) (hQ : Q = Submodule.span R (b '' (t \ s))) :
    ∃ Phi : (↥P ⧸ Q.comap P.subtype) ≃ₗ[R] W,
      ∀ (x : ↥P) (i : ι) (hi : i ∈ s), x.1 = b i → Phi (Submodule.Quotient.mk x) = c ⟨i, hi⟩ := by
  subst hP hQ
  have hker : LinearMap.ker (qb_aPsi b s c ∘ₗ (Submodule.span R (b '' t)).subtype) =
      (Submodule.span R (b '' (t \ s))).comap (Submodule.span R (b '' t)).subtype := by
    ext x
    have hx : ((b.repr x.1).support : Set ι) ⊆ t := (Basis.mem_span_image b).1 x.2
    rw [LinearMap.mem_ker, Submodule.mem_comap, Basis.mem_span_image]
    constructor
    · intro h y hy
      exact ⟨hx hy, fun hy' => (Finsupp.mem_support_iff.1 hy) ((qb_aPsi_eq_zero_iff b s c x.1).1 h y hy')⟩
    · intro h
      refine (qb_aPsi_eq_zero_iff b s c x.1).2 fun y hy => ?_
      by_contra hne
      exact (h (Finsupp.mem_support_iff.2 hne)).2 hy
  have hsurj : Function.Surjective (qb_aPsi b s c ∘ₗ (Submodule.span R (b '' t)).subtype) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← c.span_eq, Submodule.span_le]
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    exact ⟨⟨b y, Submodule.subset_span ⟨y, hst hy, rfl⟩⟩, qb_aPsi_basis b s c y hy⟩
  obtain ⟨Phi, hPhi⟩ := qb_quot_equiv _ hsurj _ hker
  refine ⟨Phi, fun x i hi hx => ?_⟩
  rw [hPhi, LinearMap.comp_apply, Submodule.subtype_apply, hx, qb_aPsi_basis b s c i hi]

end abs

def qb_sMu {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) : Set (qb_Idx CF) := {y | CF.mu y.1 = mu}

def qb_eqS {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) :
    (Σ j : {j : CF.J // CF.mu j = mu}, {I : TIdx (CF.mu j.1) // StdT I}) ≃ ↥(qb_sMu CF mu) where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl

theorem filtration_maximal_quotient_of : LemmaA → SBasis → FiltrationMaximalQuotient := by
  intro hA hS n _ M CF pi hpi mu hmu hmax
  have hlow : DomLowerSet (pi \ {mu}) :=
    ⟨fun nu h => hpi.1 nu h.1, fun nu h la hla hle =>
      ⟨hpi.2 nu h.1 la hla hle, fun heq => h.2 (hmax nu h.1 (by rw [← (heq : la = mu)]; exact hle))⟩⟩
  obtain ⟨Phi, hPhi⟩ := qb_aQuot (qb_basis hA CF ℤ) (qb_sMu CF mu) {y | CF.mu y.1 ∈ pi}
    (fun y hy => by rw [Set.mem_setOf_eq, (hy : CF.mu y.1 = mu)]; exact hmu)
    ((qb_aT (fun j : {j : CF.J // CF.mu j = mu} => qb_bS hS (CF.dom j.1) j.2) (qb_bM hA CF mu)).reindex
      (qb_eqS CF mu))
    (CF.Mpi pi) (CF.Mpi (pi \ {mu})) (qb_Mpi_eq_image hA CF pi hpi) (qb_Mpi_eq_image hA CF (pi \ {mu}) hlow)
  refine ⟨Phi.toAddEquiv.toIntLinearEquiv, ?_⟩
  intro j I x y z hj hI hx hy hz
  have h1 := hPhi x ⟨j, I, hI⟩ hj (by rw [hx, qb_basis_apply, qb_vecF_int])
  rw [Basis.reindex_apply, qb_aT_apply] at h1
  refine Eq.trans h1 ?_
  congr 1
  · exact Subtype.ext ((qb_bS_coe hS _ _ _).trans hy.symm)
  · exact Subtype.ext ((qb_bM_coe hA CF mu _).trans hz.symm)

end Formalism.InvariantFactorPaths.ColumnFamilies

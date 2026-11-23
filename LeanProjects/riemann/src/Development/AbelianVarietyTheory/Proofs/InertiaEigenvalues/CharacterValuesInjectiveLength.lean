import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonomialsSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfResidueSpanEqTopStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrthogonalIdempotentsHeckeSpanRepStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetGenericSumMemHeckeAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDetMemHeckeAlgebraOfHeckeSpanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetPencilMemHeckeAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentRankConstOfCharpolyInLocalFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockCharPolyEqCharpolyImageStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeSpanCorrectionDistinctEigenvaluesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankIdempotentBlockCharPolyOfProjectionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankEqOfActsThroughFirstBlockStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixRankMapFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDecompositionBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectiveRootsOfNcardRootSetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDvrExtensionForMonicFamilyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockRootFactorsRankOneDomainStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdOtherRootFactorsActionFirstCoordinateStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjOnCharValuesAndLengthQuotientStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlockActionStatement
import Development.AutomorphicArithmetic.CyclotomicBounds.FactorizationConductorLeLocalLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanMapRepEqTop

noncomputable section

namespace GlobalTheory.ConsExists

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

section Base

theorem charZero_of_finite (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : CharZero O := by
  have hinj : Function.Injective (algebraMap ℤ_[l] O) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h
    have hp : (RingHom.ker (algebraMap ℤ_[l] O)).IsPrime := RingHom.ker_isPrime _
    have hm : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal := Ideal.IsPrime.isMaximal hp h
    have := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l]) (⊥ : Ideal O) hm
    exact IsDiscreteValuationRing.not_isField O (Ring.isField_iff_maximal_bot.2 this)
  exact charZero_of_injective_algebraMap hinj

variable {Γ X A : Type} [Group Γ] [CommRing A] {n r t : ℕ}

theorem blockPol_map {B : Type} [CommRing B] (f : A →+* B) (e M : Matrix (Fin n) (Fin n) A) :
    (blockPol e M).map f = blockPol (e.map f) (M.map f) := by
  unfold blockPol
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, Matrix.one_apply]

theorem overK_apply {k : ℕ} (σ : Γ →* GL (Fin k) A) (g : Γ) (u : Fin k → FractionRing A) :
    overK σ g u = ((mat σ g).map (toFr A)).mulVec u := rfl

theorem blockPol_coeff_mem {T : Subalgebra A (X → A)} {rep : X → (Γ →* GL (Fin n) A)}
    (hT : CharPolyIn T rep) {e M : X → Matrix (Fin n) (Fin n) A} (he : InRing T rep e)
    (hM : InRing T rep M) (j : ℕ) : (fun x => (blockPol (e x) (M x)).coeff j) ∈ T := by
  have := GlobalTheory.T.coeff_det_pencil_mem_heckeAlgebra T rep hT e (1 - e - M) he (inRing_sub (inRing_sub inRing_one he) hM) j
  convert this using 4 with x
  unfold blockPol
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, Matrix.one_apply] <;> ring

theorem rank_const [IsDomain A] [IsLocalRing A] {T : Subalgebra A (X → A)}
    {rep : X → (Γ →* GL (Fin n) A)} (hl : IsLocalRing T)
    (hT : CharPolyIn T rep) {e : X → Matrix (Fin n) (Fin n) A} (he : InRing T rep e) (hee : e * e = e)
    (x y : X) : ((e x).map (toFr A)).rank = ((e y).map (toFr A)).rank := by
  refine GlobalTheory.T.idempotent_rank_const_of_charpoly_in_local_functions T e hl hee (fun j => ?_) x y
  have := blockPol_coeff_mem hT inRing_one he j
  convert this using 3 with x
  unfold blockPol Matrix.charpoly Matrix.charmatrix
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, Matrix.one_apply]

theorem corner_act {K : Type} [Field K] (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K)))
    {E G : Matrix (Fin n) (Fin n) K} {P : Matrix (Fin r) (Fin r) K} {d : Fin t → K}
    (hE : ∀ u, e (E.mulVec u) = (0, (e u).2))
    (hG : ∀ u, e (G.mulVec u) = (P.mulVec (e u).1, fun c => d c * (e u).2 c)) (u : Fin n → K) :
    e ((E * G * E).mulVec u) = (0, fun c => d c * (e u).2 c) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hE, hG, hE]

theorem choice_facts [IsDomain A] [IsLocalRing A] {T : Subalgebra A (X → A)}
    {rep : X → (Γ →* GL (Fin n) A)} {ρ : X → (Γ →* GL (Fin r) A)} {χ : ℕ → (Γ →* Aˣ)} {π : X} {g0 : Γ}
    {L : ℕ} {eB e1 X0 : X → Matrix (Fin n) (Fin n) A} (hl : IsLocalRing T) (hT : CharPolyIn T rep)
    (h : IsChoice t T rep ρ χ π g0 L eB e1 X0) :
    (∀ x, ((eB x).map (toFr A)).rank = t) ∧ (∀ x, ((e1 x).map (toFr A)).rank = 1) ∧
    InRing T rep X0 ∧ eB * X0 = X0 ∧ X0 * eB = X0 ∧
    ∃ e, IsDecomp (t := t) (rep π) (ρ π) χ e ∧
      (∀ u, e (((eB π).map (toFr A)).mulVec u) = (0, (e u).2)) ∧
      ∀ u, e (((X0 π).map (toFr A)).mulVec u) =
        (0, fun c : Fin t => toFr A ((χ ((c : ℕ) + 1) g0 : Aˣ) : A) * (e u).2 c) := by
  obtain ⟨⟨hB, h1, hBB, h11, -, -⟩, ⟨e, hd, heB, ε, hε, he1⟩, ⟨ϖ, s, -, hs, hX⟩, -⟩ := h
  have hBx : ∀ x, eB x * eB x = eB x := congrFun hBB
  have hact : ∀ u, e (((X0 π).map (toFr A)).mulVec u) =
      (0, fun c : Fin t => toFr A ((χ ((c : ℕ) + 1) g0 : Aˣ) : A) * (e u).2 c) := by
    intro u
    have : X0 π = eB π * mat (rep π) g0 * eB π := by
      rw [hX]; simp [InMatrixCongruenceModule.eval_eq_zero hs]
    rw [this, Matrix.map_mul, Matrix.map_mul]
    exact corner_act e heB (hd g0) u
  refine ⟨fun x => ?_, fun x => ?_, ?_, ?_, ?_, e, hd, heB, hact⟩
  · rw [rank_const hl hT hB hBB x π]
    exact (GlobalTheory.T.rank_idempotentBlockCharPoly_of_projection e _ _ _ heB hact).1
  · rw [rank_const hl hT h1 h11 x π, GlobalTheory.T.rank_eq_of_mulVec_through_first_block e _ ε he1, hε]
  · rw [hX]
    exact inRing_add (inRing_mul (inRing_mul hB (inRing_mat g0)) hB) (inRing_smul _ (InMatrixCongruenceModule.inRing hB hs))
  · funext x
    rw [hX]
    simp only [Pi.mul_apply, mul_add, Matrix.mul_smul, (InMatrixCongruenceModule.corner hBB hs x).1, ← mul_assoc, hBx]
  · funext x
    rw [hX]
    simp only [Pi.mul_apply, add_mul, Matrix.smul_mul, (InMatrixCongruenceModule.corner hBB hs x).2, mul_assoc, hBx]

theorem span_top [IsLocalRing A] {ρ : Γ →* GL (Fin r) A}
    (h : AbsIrrSub (mapRep (IsLocalRing.residue A) ρ) ⊤) :
    Submodule.span A (Set.range (mat ρ)) = ⊤ :=
  GlobalTheory.T.span_repMatrix_eq_top_of_residue_span_eq_top ρ (GlobalTheory.T.span_repMatrix_eq_top_of_absIrreducible _ h)

theorem exists_choice (l : ℕ) [Fact l.Prime] [Finite X] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A] {T : Subalgebra A (X → A)} {Z : Finset X}
    {rep : X → (Γ →* GL (Fin n) A)} {ρ : X → (Γ →* GL (Fin r) A)} {χ : ℕ → (Γ →* Aˣ)}
    (hr : 2 ≤ r) (hS : HidaSetting t T Z rep ρ χ) {π : X} (hπ : π ∈ Z) (g0 : Γ)
    (hinj : Function.Injective fun c : Fin t => ((χ ((c : ℕ) + 1) g0 : Aˣ) : A)) (L : ℕ) :
    ∃ eB e1 X0, IsChoice t T rep ρ χ π g0 L eB e1 X0 := by
  haveI := charZero_of_finite l A
  obtain ⟨hl, hsep, -, hT, hirr, -, hdec, habs⟩ := hS
  obtain ⟨e, hd⟩ := hdec π hπ
  obtain ⟨eB, e1, hid, heB, he1⟩ := GlobalTheory.T.exists_orthogonal_idempotents_heckeSpan_rep l T rep (ρ π) χ π e hr (span_top (habs π hπ)) hd
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hat := GlobalTheory.T.rank_idempotentBlockCharPoly_of_projection e _ _ _ heB (corner_act e heB (hd g0))
  obtain ⟨s, hs, hroots⟩ := GlobalTheory.T.exists_heckeSpan_correction_distinct_eigenvalues (t := t) T rep π g0 eB (ϖ ^ L) (pow_ne_zero _ hϖ.ne_zero) hsep hirr
    hid.1 hid.2.2.1 (fun x => by rw [rank_const hl hT hid.1 hid.2.2.1 x π]; exact hat.1) (by
      rw [blockPol_map, Matrix.map_mul, Matrix.map_mul]
      refine hat.2 ▸ Polynomial.separable_prod_X_sub_C_iff.2 ?_
      exact (IsFractionRing.injective A (FractionRing A)).comp hinj)
  exact ⟨eB, e1, _, hid, ⟨e, hd, heB, he1⟩, ⟨ϖ, s, hϖ, hs, rfl⟩, hroots⟩

theorem blockPol_monic [IsDomain A] {e M : Matrix (Fin n) (Fin n) A} (hee : e * e = e)
    (hr : (e.map (toFr A)).rank = t) (h1 : e * M = M) (h2 : M * e = M) :
    ((blockPol e M).map (toFr A)).Monic ∧ ((blockPol e M).map (toFr A)).natDegree = t := by
  obtain ⟨a, b, -, -, h⟩ := GlobalTheory.T.idempotentBlockCharPoly_eq_charpoly_image (e.map (toFr A)) (by rw [← Matrix.map_mul, hee]) hr
  have := h (M.map (toFr A))
  rw [← Matrix.map_mul, ← Matrix.map_mul, h1, h2] at this
  rw [blockPol_map, this]
  exact ⟨Matrix.charpoly_monic _, by simp⟩

variable {B : Type} [CommRing B] [Algebra A B]

theorem inRing_map {T : Subalgebra A (X → A)} {T' : Subalgebra B (X → B)}
    {rep : X → (Γ →* GL (Fin n) A)} (hT : ∀ f ∈ T, (fun x => algebraMap A B (f x)) ∈ T')
    {a : X → Matrix (Fin n) (Fin n) A} (ha : InRing T rep a) :
    InRing T' (fun x => mapRep (algebraMap A B) (rep x)) (fun x => (a x).map (algebraMap A B)) := by
  obtain ⟨m, f, h, hf, rfl⟩ := ha
  refine ⟨m, fun k x => algebraMap A B (f k x), h, fun k => hT _ (hf k), ?_⟩
  funext x
  ext i j
  simp [Matrix.sum_apply, mat, mapRep]
  exact Finset.sum_congr rfl fun k _ => (Algebra.smul_def _ _).symm

theorem charPolyIn_map {T : Subalgebra A (X → A)} {T' : Subalgebra B (X → B)}
    {rep : X → (Γ →* GL (Fin n) A)} (hT : ∀ f ∈ T, (fun x => algebraMap A B (f x)) ∈ T')
    (h : CharPolyIn T rep) : CharPolyIn T' (fun x => mapRep (algebraMap A B) (rep x)) := by
  intro g d
  convert hT _ (h g d) using 2 with x
  rw [← Polynomial.coeff_map]
  congr 1
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases hab : a = b <;> simp [hab, Matrix.one_apply, mat, mapRep]

theorem span_top_map {ρ : Γ →* GL (Fin r) A} (h : Submodule.span A (Set.range (mat ρ)) = ⊤) :
    Submodule.span B (Set.range (mat (mapRep (algebraMap A B) ρ))) = ⊤ :=
  _root_.GlobalTheory.SpanMapTop.span_mapRep_eq_top h

end Base

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

theorem two_le_r (R : Ranks) : 2 ≤ R.r := by
  have := R.two_le_m; have := R.m_add_three_le_k; unfold Ranks.r; omega

theorem two_le_ranks_t (R : Ranks) : 2 ≤ R.t := by
  have := R.rank_add_five_le; omega

theorem character_values_injective_length {g0 : GE N} (hg : IsInertiaCyclotomicGeneratorElement N i g0) :
    Set.InjOn (fun c => ((N.chi i c g0 : (N.O i)ˣ) : N.O i)) (Finset.Icc 1 R.t : Set ℕ) ∧
    lenUnit (O := N.O i) (N.l i) (N.O i ⧸ Ideal.span {∏ c ∈ Finset.Ioc 1 R.t,
      (((N.chi i 1 g0 : (N.O i)ˣ) : N.O i) - ((N.chi i c g0 : (N.O i)ˣ) : N.O i))}) = N.vdel i := by
  haveI := charZero_of_finite (N.l i) (N.O i)
  obtain ⟨-, v, hv⟩ := hg
  refine GlobalTheory.T.injOn_charValues_and_length_quotient (N.l i) (N.s0 i) R.t (cycZ (F := H.E) (Ω := N.Om) (N.l i) g0) v
    (fun c => N.chi i c g0) ?_ ?_ hv ?_
  · exact UpperTheory.KStar.S0.one_le_localLevel N i
  · exact UpperTheory.KStar.S0.two_le_localLevel_of_eq_two N i
  · intro c h1 h2
    rw [N.chi_def i c h1 h2]
    simp

def root {X O : Type} [Zero O] {t : ℕ} (β : X → Fin t → O) (c : ℕ) (x' : X × Equiv.Perm (Fin t)) : O :=
  if h : c - 1 < t then β x'.1 (x'.2 ⟨c - 1, h⟩) else 0

theorem root_succ {X O : Type} [Zero O] {t : ℕ} (β : X → Fin t → O) (c : Fin t)
    (x' : X × Equiv.Perm (Fin t)) : root β ((c : ℕ) + 1) x' = β x'.1 (x'.2 c) := by
  simp [root]

theorem exists_succ {t c : ℕ} (hc : c ∈ Finset.Icc 1 t) : ∃ a : Fin t, c = (a : ℕ) + 1 := by
  rw [Finset.mem_Icc] at hc
  exact ⟨⟨c - 1, by omega⟩, by simp; omega⟩

theorem prod_Icc_eq {M : Type} [CommMonoid M] (t : ℕ) (f : ℕ → M) :
    ∏ c ∈ Finset.Icc 1 t, f c = ∏ a : Fin t, f ((a : ℕ) + 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun a => f (a + 1)) t, Finset.range_eq_Ico,
    Finset.prod_Ico_add' f 0 t 1]
  rfl

theorem exists_good (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) (g0 : GE N) (hg : IsInertiaCyclotomicGeneratorElement N i g0)
    (eB e1 X0 : N.X i → MatN N i) (hT : CharPolyIn (N.T i) rep)
    (hspan : Submodule.span (N.O i) (Set.range (mat (ρ π))) = ⊤)
    (hid : InRing (N.T i) rep eB ∧ InRing (N.T i) rep e1 ∧ eB * eB = eB ∧ e1 * e1 = e1 ∧ eB * e1 = 0 ∧
      e1 * eB = 0 ∧ (∀ x, ((eB x).map (toK N i)).rank = R.t) ∧ (∀ x, ((e1 x).map (toK N i)).rank = 1))
    (e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)))
    (hd : IsDecomp (t := R.t) (rep π) (ρ π) (N.chi i) e)
    (heB : ∀ u, e (((eB π).map (toK N i)).mulVec u) = (0, (e u).2))
    (hX : InRing (N.T i) rep X0) (hX1 : eB * X0 = X0) (hX2 : X0 * eB = X0)
    (hXπ : ∀ u, e (((X0 π).map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => toK N i ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i) * (e u).2 c))
    (hβ : ∀ x, ∃ β : Fin R.t → N.O i, Function.Injective β ∧
      blockPol (eB x) (X0 x) = ∏ c, (Polynomial.X - Polynomial.C (β c))) :
    ∃ S : IdempotentChoiceData N i, S.g0 = g0 ∧ S.eB = eB ∧ S.e1 = e1 ∧ S.X0 = X0 ∧ GoodCongruenceObjects N rep ρ π S := by
  classical
  obtain ⟨hinjχ, hvdel⟩ := character_values_injective_length N i hg

  have hβ' : ∀ x, ∃ β : Fin R.t → N.O i, Function.Injective β ∧
      blockPol (eB x) (X0 x) = ∏ c, (Polynomial.X - Polynomial.C (β c)) ∧
      (x = π → ∀ c, β c = ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i)) := by
    intro x
    by_cases hx : x = π
    · subst hx
      refine ⟨fun c => ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i), fun a b hab => ?_, ?_,
        fun _ _ => rfl⟩
      · have := hinjχ (x₁ := (a : ℕ) + 1) (by simp) (x₂ := (b : ℕ) + 1) (by simp) hab
        exact Fin.ext (by omega)
      · apply Polynomial.map_injective (toK N i) (IsFractionRing.injective _ _)
        rw [blockPol_map, (GlobalTheory.T.rank_idempotentBlockCharPoly_of_projection e _ _ _ heB hXπ).2, Polynomial.map_prod]
        simp
    · obtain ⟨β, h1, h2⟩ := hβ x
      exact ⟨β, h1, h2, fun h => absurd h hx⟩
  choose β hβi hβp hβπ using hβ'
  have hrπ : ∀ c ∈ Finset.Icc 1 R.t, root β c (π, 1) = ((N.chi i c g0 : (N.O i)ˣ) : N.O i) := by
    intro c hc
    obtain ⟨a, rfl⟩ := exists_succ hc
    rw [root_succ]
    exact hβπ π rfl a
  have hset : (fun c => root β c) '' (Finset.Icc 1 R.t : Set ℕ) =
      Set.range fun c : Fin R.t => fun x' : N.X i × Equiv.Perm (Fin R.t) => β x'.1 (x'.2 c) := by
    ext f
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨a, rfl⟩ := exists_succ hc
      exact ⟨a, funext fun x' => (root_succ β a x').symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : ℕ) + 1, by simp, funext fun x' => root_succ β a x'⟩
  let T' : Subalgebra (N.O i) (N.X i × Equiv.Perm (Fin R.t) → N.O i) :=
    Algebra.adjoin (N.O i) ((fun f : N.X i → N.O i => fun x' => f x'.1) '' (N.T i : Set _) ∪
      (fun c => root β c) '' (Finset.Icc 1 R.t : Set ℕ))
  have hTT : ∀ f ∈ N.T i, (fun x' : N.X i × Equiv.Perm (Fin R.t) => f x'.1) ∈ T' :=
    fun f hf => Algebra.subset_adjoin (Or.inl ⟨f, hf, rfl⟩)
  have hT' : CharPolyIn T' (fun x' => rep x'.1) := fun h d => hTT _ (hT h d)
  obtain ⟨ψρ, ψχ, hψ, hψs⟩ := GlobalTheory.T.exists_block_action_of_decomposition T' (fun x' => rep x'.1) (ρ π) (N.chi i) (π, 1) e hspan hd
  have hpol : ∀ x' : N.X i × Equiv.Perm (Fin R.t),
      ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (root β c x')) =
        blockPol (eB x'.1) (X0 x'.1) := by
    intro x'
    rw [prod_Icc_eq, hβp, ← Equiv.prod_comp x'.2 (fun c => Polynomial.X - Polynomial.C (β x'.1 c))]
    simp only [root_succ]
  have hE := fun x' : N.X i × Equiv.Perm (Fin R.t) =>
    GlobalTheory.T.idempotentBlock_rootFactors_rank_one_domain R.nV R.t (eB x'.1) (X0 x'.1) (fun c => root β c x') (two_le_ranks_t R)
      (congrFun hid.2.2.1 _) (congrFun hX1 _) (congrFun hX2 _) (by
        intro c hc c' hc' h
        obtain ⟨a, rfl⟩ := exists_succ hc
        obtain ⟨a', rfl⟩ := exists_succ hc'
        simp only [root_succ] at h
        rw [x'.2.injective (hβi _ h)]) (hpol x')
  refine ⟨{ eB := eB, e1 := e1, g0 := g0, X0 := X0, X' := N.X i × Equiv.Perm (Fin R.t), p := Prod.fst,
            T' := T', rr := root β, π' := (π, 1), e := e, ψρ := ψρ, ψχ := ψχ }, rfl, rfl, rfl, rfl,
    hid, hd, hψ, hψs, hg.1, hg.2, ⟨hX, hX1, hX2, hXπ⟩, ⟨hTT, ?_, rfl, ?_, ?_⟩, hpol, ⟨rfl, hrπ⟩,
    ⟨fun x' => (hE x').1, fun x' => (hE x').2, ?_, ?_⟩, GlobalTheory.T.coeff_det_generic_sum_mem_heckeAlgebra T' _ hT', GlobalTheory.T.blockDet_mem_heckeAlgebra_of_heckeSpan T' _ hT'⟩
  · exact fun c hc => Algebra.subset_adjoin (Or.inr ⟨c, hc, rfl⟩)
  · have := GlobalTheory.SplittingAlgebra.main (N.T i) R.t β hβi (N.T_sep i) (fun j => by
      simpa only [hβp] using blockPol_coeff_mem hT hid.1 hX j)
    simp only [← hset] at this
    exact this
  · intro x
    have : {x' : N.X i × Equiv.Perm (Fin R.t) // x'.1 = x} ≃ Equiv.Perm (Fin R.t) :=
      { toFun := fun a => a.1.2
        invFun := fun σ => ⟨(x, σ), rfl⟩
        left_inv := by rintro ⟨⟨y, σ⟩, rfl⟩; rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr this).trans (by simp [Fintype.card_perm])
  · refine GlobalTheory.T.prod_other_root_factors_action_first_coordinate e (eB π) (X0 π) (fun c => root β c (π, 1)) (two_le_ranks_t R) heB (fun u => ?_)
    rw [hXπ]
    congr 1
    funext c
    rw [hrπ _ (by simp)]
  · rw [← hvdel]
    have : del51 N (⟨eB, e1, g0, X0, N.X i × Equiv.Perm (Fin R.t), Prod.fst, T', root β, (π, 1), e, ψρ, ψχ⟩ :
        IdempotentChoiceData N i) (π, 1) = ∏ c ∈ Finset.Ioc 1 R.t,
        (((N.chi i 1 g0 : (N.O i)ˣ) : N.O i) - ((N.chi i c g0 : (N.O i)ˣ) : N.O i)) := by
      refine Finset.prod_congr rfl fun c hc => ?_
      have h2 := two_le_ranks_t R
      show root β 1 (π, 1) - root β c (π, 1) = _
      rw [hrπ 1 (by simp; omega), hrπ c (Finset.Ioc_subset_Icc_self hc)]
    exact congrArg (fun z => lenUnit (O := N.O i) (N.l i) (N.O i ⧸ Ideal.span {z})) this

theorem consExist : ConsExist N i := by
  intro rep ρ A _ _ _ _ _ _ _ TA repA ρA χA _ hE hS
  obtain ⟨hinj, hTO, hrep, hρ, hχ⟩ := hE
  haveI := charZero_of_finite (N.l i) A
  refine ⟨fun π hπ g0 hg L => ?_, fun g0 L eB e1 X0 h => ?_, fun π hπ g0 L eB e1 X0 hg hc hroot => ?_⟩
  · refine exists_choice (N.l i) (two_le_r R) hS hπ g0 (fun a b hab => ?_) L
    have := (character_values_injective_length N i hg).1 (x₁ := (a : ℕ) + 1) (by simp) (x₂ := (b : ℕ) + 1) (by simp) (by
      simp only
      rw [hχ _ (by omega) (by omega), hχ _ (by omega) (by omega)]
      exact congrArg _ hab)
    exact Fin.ext (by omega)
  · obtain ⟨B, i1, i2, i3, i4, h1, h2, h3⟩ := GlobalTheory.T.exists_dvr_extension_for_monic_family (N.l i) (ι := N.Z i × N.X i) R.t
      (fun p => blockPol (eB p.1 p.2) (X0 p.1 p.2)) (fun p => by
        have hc := (h p.1 p.1.2).2
        obtain ⟨hr, -, -, hX1, hX2, -⟩ := choice_facts hS.1 hS.2.2.2.1 hc
        exact blockPol_monic (congrFun hc.1.2.2.1 _) (hr _) (congrFun hX1 _) (congrFun hX2 _))
    exact ⟨B, i1, i2, i3, i4, h1, h2, fun π hπ x => h3 (⟨π, hπ⟩, x)⟩
  · obtain ⟨hrB, hr1, hX, hX1, hX2, e, hd, heB, hXπ⟩ := choice_facts hS.1 hS.2.2.2.1 hc
    obtain ⟨⟨hB, h1, hBB, h11, hB1, h1B⟩, -, -, hdist⟩ := hc
    let φ : FractionRing A →+* KK N i := IsFractionRing.lift (g := (toK N i).comp (algebraMap A (N.O i)))
      ((IsFractionRing.injective (N.O i) (KK N i)).comp hinj)
    have hφ : ∀ a : A, φ (toFr A a) = toK N i (algebraMap A (N.O i) a) := fun a =>
      IsFractionRing.lift_algebraMap _ a
    have hφM : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) A),
        (M.map (algebraMap A (N.O i))).map (toK N i) = (M.map (toFr A)).map φ := by
      intro k M
      ext a b
      exact (hφ _).symm
    obtain ⟨e', he'⟩ := GlobalTheory.T.block_mulVec_decomposition_map_of_decomposition φ e
    have hTT : ∀ f ∈ TA, (fun x => algebraMap A (N.O i) (f x)) ∈ N.T i := by
      intro f hf
      rw [← Subalgebra.mem_toSubmodule, hTO]
      exact Submodule.subset_span ⟨f, hf, rfl⟩
    obtain rfl : rep = fun x => mapRep (algebraMap A (N.O i)) (repA x) := funext hrep
    have hmul : ∀ {a b c : N.X i → Matrix (Fin R.nV) (Fin R.nV) A}, a * b = c →
        (fun x => (a x).map (algebraMap A (N.O i))) * (fun x => (b x).map (algebraMap A (N.O i))) =
          fun x => (c x).map (algebraMap A (N.O i)) := by
      rintro a b c rfl
      funext x
      simp [Matrix.map_mul]
    obtain ⟨S, s0, s1, s2, s3, hG⟩ := exists_good N i _ ρ π g0 hg
      (fun x => (eB x).map (algebraMap A (N.O i))) (fun x => (e1 x).map (algebraMap A (N.O i)))
      (fun x => (X0 x).map (algebraMap A (N.O i))) (charPolyIn_map hTT hS.2.2.2.1)
      (by rw [hρ π hπ]; exact span_top_map (span_top (hS.2.2.2.2.2.2.2 π hπ)))
      ⟨inRing_map hTT hB, inRing_map hTT h1, hmul hBB, hmul h11,
        (hmul hB1).trans (by funext x; simp), (hmul h1B).trans (by funext x; simp),
        fun x => by rw [hφM, GlobalTheory.T.rank_map_ringHom, hrB], fun x => by rw [hφM, GlobalTheory.T.rank_map_ringHom, hr1]⟩
      e' (by
        intro g u
        rw [hρ π hπ, overK_apply, overK_apply]
        have := he' ((mat (repA π) g).map (toFr A)) ((mat (ρA π) g).map (toFr A)) _ (hd g) u
        rw [← hφM, ← hφM] at this
        refine this.trans ?_
        congr 1
        funext c
        rw [hφ, hχ _ (by omega) (by omega)])
      (by
        intro u
        have := he' ((eB π).map (toFr A)) 0 (fun _ => 1) (fun u => by rw [heB]; simp) u
        rw [← hφM] at this
        simpa using this)
      (inRing_map hTT hX) (hmul hX1) (hmul hX2)
      (by
        intro u
        have := he' ((X0 π).map (toFr A)) 0 _ (fun u => by rw [hXπ]; simp; rfl) u
        rw [← hφM] at this
        refine this.trans ?_
        congr 1
        · simp
        · funext c
          rw [hφ, hχ _ (by omega) (by omega)])
      (fun x => by
        obtain ⟨α, hα⟩ := hroot x
        obtain ⟨β, hβ, hP⟩ := GlobalTheory.T.exists_injective_roots_of_ncard_rootSet' R.t _ α hinj (hdist x) hα
        exact ⟨β, hβ, by rw [← blockPol_map, hP]⟩)
    exact ⟨S, s0, congrFun s1, congrFun s2, congrFun s3, hG⟩

end Record

end GlobalTheory.ConsExists

end

import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicUnitarySplitPlaceComponent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialOfSplitPlaceStabilizer

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParahoricLift

section Block

variable {κ : Type} [CommRing κ] {n r : ℕ}

def splitIx (hr : r ≤ n) : Fin r ⊕ Fin (n - r) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hr))

theorem splitIx_inl (hr : r ≤ n) (a : Fin r) : splitIx hr (Sum.inl a) = Fin.castLE hr a := Fin.ext rfl

theorem splitIx_inr (hr : r ≤ n) (a : Fin (n - r)) : (splitIx hr (Sum.inr a)).val = r + a.val := rfl

def diagMat (hr : r ≤ n) (M : Matrix (Fin r) (Fin r) κ) : Matrix (Fin n) (Fin n) κ :=
  (Matrix.fromBlocks M 0 0 1).submatrix (splitIx hr).symm (splitIx hr).symm

theorem diagMat_mul (hr : r ≤ n) (M N : Matrix (Fin r) (Fin r) κ) :
    diagMat hr M * diagMat hr N = diagMat hr (M * N) := by
  unfold diagMat
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem diagMat_one (hr : r ≤ n) : diagMat hr (1 : Matrix (Fin r) (Fin r) κ) = 1 := by
  unfold diagMat
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

def diagOne (hr : r ≤ n) (g : GL (Fin r) κ) : GL (Fin n) κ where
  val := diagMat hr g.1
  inv := diagMat hr (g⁻¹).1
  val_inv := by rw [diagMat_mul, Units.mul_inv, diagMat_one]
  inv_val := by rw [diagMat_mul, Units.inv_mul, diagMat_one]

theorem diagOne_mem (hr : r ≤ n) (t : ℕ) (g : GL (Fin r) κ) : diagOne hr g ∈ blockTri (blkOf r t) := by
  intro i j hij
  obtain ⟨a, rfl⟩ := (splitIx hr).surjective i
  obtain ⟨b, rfl⟩ := (splitIx hr).surjective j
  show diagMat hr g.1 _ _ = 0
  unfold diagMat
  rw [Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases a with a | a
  · have : blkOf r t (splitIx hr (Sum.inl a)) = 0 := if_pos a.2
    have h2 : blkOf r t (splitIx hr b) < blkOf r t (splitIx hr (Sum.inl a)) := hij
    omega
  · rcases b with b | b
    · rfl
    · refine Matrix.one_apply_ne ?_
      rintro rfl
      exact lt_irrefl _ hij

theorem topLeftBlock_blockDiagWithIdentityGL (hr : r ≤ n) (g : GL (Fin r) κ) : upperLeftBlock hr (diagOne hr g) = g := by
  apply Units.ext
  rw [upper_block_val_submatrix hr (blockTri_blkOf_le r 1 (diagOne_mem hr 1 g))]
  ext a b
  show diagMat hr g.1 _ _ = _
  unfold diagMat
  rw [Matrix.submatrix_apply, ← splitIx_inl, ← splitIx_inl, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

end Block

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem frame_mulVec (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hβ : IsFrame β Λ)
    (Y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) :
    ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      (β.1 * Y.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1) *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  intro y hy
  rw [hβ] at hy ⊢
  intro i
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
    ← Matrix.mulVec_mulVec]
  show ∑ j : Fin n, _ * _ ∈ _
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (Y i j).2 (hy j)

theorem redFn_of_smul_eq (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hS : x ∈ St β) (φ : Formalism.L2.Herm.intAf F E) (hφ : resS F PP φ = 1)
    (Y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E))
    (hx : (φ : E ⊗[F] Formalism.L2.Herm.Af F) • x.1 =
      (φ : E ⊗[F] Formalism.L2.Herm.Af F) • (β.1 * Y.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1)) :
    (redFn β PP x).1 = Y.map (resS F PP) := by
  obtain ⟨y, rfl⟩ := hS
  rw [redFn_frGL]
  have e1 : ((frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
    β.1 * y.1.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 := rfl
  rw [e1] at hx
  have h2 := congrArg (fun M => (β⁻¹).1 * M * β.1) hx
  simp only [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
  simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one] at h2
  ext i j
  have h3 : φ * y.1 i j = φ * Y i j := Subtype.ext (congrFun (congrFun h2 i) j)
  have h4 := congrArg (resS F PP) h3
  rw [map_mul, map_mul, hφ, one_mul, one_mul] at h4
  exact h4

theorem idem_dvd (PP : Pl E) (φ : Formalism.L2.Herm.intAf F E) (hφ : φ * φ = φ) (h0 : resS F PP φ = 0) :
    ∃ x ∈ PP.asIdeal, x ≠ 0 ∧ ∃ s, s * oToS F E x = φ := by
  have h1 : φ ∈ idS F PP.asIdeal := by
    unfold resS at h0
    rw [RingHom.comp_apply] at h0
    exact Ideal.Quotient.eq_zero_iff_mem.1 ((RingEquiv.map_eq_zero_iff _).1 h0)
  let I : nonZeroDivisors (Ideal (𝓞 E)) := ⟨PP.asIdeal, mem_nonZeroDivisors_of_ne_zero PP.ne_bot⟩
  obtain ⟨h, hh, e⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite (ClassGroup.mk0 I))
  rw [← map_pow] at e
  have hp : (PP.asIdeal ^ h).IsPrincipal := (ClassGroup.mk0_eq_one_iff (I ^ h).2).1 e
  obtain ⟨x, hx⟩ := hp
  have hx' : PP.asIdeal ^ h = Ideal.span {x} := hx
  refine ⟨x, Ideal.pow_le_self hh.ne' (hx' ▸ Ideal.mem_span_singleton_self x), ?_, ?_⟩
  · rintro rfl
    exact pow_ne_zero h PP.ne_bot (by rw [hx']; simp)
  · have h2 := Ideal.pow_mem_pow h1 h
    rw [IsIdempotentElem.pow_eq hφ hh.ne'] at h2
    unfold idS at h2
    rw [← Ideal.map_pow, hx', Ideal.map_span, Set.image_singleton] at h2
    exact Ideal.mem_span_singleton'.1 h2

end Frame

section Alg

variable {A : Type} [CommRing A] {n : ℕ}

theorem hform_add_left (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (x x' y : Fin n → A) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_zero_left (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (y : Fin n → A) :
    Formalism.UG.hform σ J 0 y = 0 := by
  simp [Formalism.UG.hform]

theorem stab_of_part {S : Subring A} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (H : Submodule S (Fin n → A))
    (hH : ∀ y, y ∈ H ↔ ∀ z ∈ H, Formalism.UG.hform σ J z y ∈ S) {p : A} (hp : p ∈ S) (hq : σ p ∈ S) (g : GL (Fin n) A)
    (hg : Formalism.UG.cT σ g.1 * J * g.1 = J) (hs : (p + σ p) • (g.1 - 1) = g.1 - 1) (m m' : Matrix (Fin n) (Fin n) A)
    (hm : ∀ y ∈ H, m *ᵥ y ∈ H) (hm' : ∀ y ∈ H, m' *ᵥ y ∈ H) (hmm : p • (m * m') = p • (1 : Matrix (Fin n) (Fin n) A))
    (hgm : p • g.1 = p • m) : (∀ y ∈ H, g.1 *ᵥ y ∈ H) ∧ ∀ y ∈ H, (g⁻¹).1 *ᵥ y ∈ H := by
  have e : ∀ y, p • g.1 *ᵥ y = p • m *ᵥ y := fun y => by
    rw [← Matrix.smul_mulVec, hgm, Matrix.smul_mulVec]
  have key := GlobalTheory.SplitStab.stab_of_half σ J S.toAddSubgroup H.toAddSubgroup hH (p := p)
    (fun y hy => H.smul_mem ⟨p, hp⟩ hy) (fun y hy => H.smul_mem ⟨σ p, hq⟩ hy) hg
    (fun i j => congrFun (congrFun hs i) j)
    (fun y hy => by
      show p • g.1 *ᵥ y ∈ H
      rw [e]; exact H.smul_mem ⟨p, hp⟩ (hm y hy))
    (fun y hy => ⟨m' *ᵥ y, hm' y hy, by
      show p • y = p • g.1 *ᵥ (m' *ᵥ y)
      rw [e, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, hmm, Matrix.smul_mulVec, Matrix.one_mulVec]⟩)
  refine ⟨fun y hy => (key y).1 hy, fun y hy => (key _).2 ?_⟩
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  exact hy

theorem conj_inv_part {S : Subring A} (β : GL (Fin n) A) (p u : S) (Y : Matrix (Fin n) (Fin n) S) (h : u * Y.det = p)
    (hp : p * p = p) :
    (p : A) • ((β.1 * Y.map S.subtype * (β⁻¹).1) * (β.1 * (u • Y.adjugate).map S.subtype * (β⁻¹).1)) =
      (p : A) • (1 : Matrix (Fin n) (Fin n) A) := by
  have e1 : Y * (u • Y.adjugate) = p • (1 : Matrix (Fin n) (Fin n) S) := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, h]
  have e2 : Y.map S.subtype * (u • Y.adjugate).map S.subtype = (p : A) • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [← Matrix.map_mul, e1]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have e3 : (β.1 * Y.map S.subtype * (β⁻¹).1) * (β.1 * (u • Y.adjugate).map S.subtype * (β⁻¹).1) =
      β.1 * (Y.map S.subtype * (u • Y.adjugate).map S.subtype) * (β⁻¹).1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (β⁻¹).1 β.1, Units.inv_mul, Matrix.one_mul]
  have hp' : (p : A) * p = p := congrArg Subtype.val hp
  rw [e3, e2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.mul_inv, smul_smul, hp']

end Alg

section Dual

open GlobalTheory.LevSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem swp_hermA (c : E ≃ₐ[F] E) (σ : E →ₐ[F] E) (hσ : ∀ x, σ x = c x) (J : Matrix (Fin n) (Fin n) E)
    (x : Fin n → E) (y : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :
    swp F E (GlobalTheory.AdLat.hermA c Jᵀ y (GlobalTheory.AdLat.fv F x)) =
      Formalism.UG.hform (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F)) (J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)))
        (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) (fun i => swp F E (y i)) := by
  unfold Formalism.UG.hform GlobalTheory.AdLat.hermA
  rw [Finset.sum_comm, map_sum (swp F E)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum (swp F E)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have e1 : swp F E (GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (GlobalTheory.AdLat.fv F x a)) =
      Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x a)) := by
    show c (x a) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) = σ (x a) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)
    rw [hσ]
  have e2 : swp F E ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] Jᵀ b a) =
      (J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) a b := rfl
  rw [RingHom.map_mul, RingHom.map_mul, e1, e2]
  ring

def HatSelfDual (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ y : Fin n → E ⊗[F] Formalism.L2.Herm.Af F, y ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔ ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ,
    Formalism.UG.hform (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F)) (J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) z y ∈
      Formalism.L2.Herm.intAf F E

theorem hatL_selfDual_gen (c : E ≃ₐ[F] E) (σ : E →ₐ[F] E) (hσ : ∀ x, σ x = c x) (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG) (hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (hcc : ∀ x, c (c x) = x) (hG : ∀ a b, c (Jᵀ a b) = Jᵀ b a) (hdet : Jᵀ.det ≠ 0)
    (hL : ∀ v : Fin n → E, (∀ y ∈ Λ, (∑ a, ∑ b, v a * Jᵀ a b * c (y b)) ∈
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) ↔ v ∈ Λ)
    (hint : ∀ s ∈ Formalism.L2.Herm.intAf F E, Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) s ∈ Formalism.L2.Herm.intAf F E)
    (hI : ∀ z, z ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) ↔
      swp F E z ∈ Formalism.L2.Herm.intAf F E) : HatSelfDual σ J Λ := by
  intro y
  choose y' hy' using fun i => (swp_bij (F := F) (E := E)).2 (y i)
  obtain rfl : y = fun i => swp F E (y' i) := funext fun i => (hy' i).symm
  have key := GlobalTheory.AdLat.hat_selfDual F E n Λ c Jᵀ 1 hfg hspan hcc hG hdet one_ne_zero hL y'
  have k2 : (∀ x ∈ Λ, Formalism.UG.hform (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F))
      (J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)))
        (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) (fun i => swp F E (y' i)) ∈
          Formalism.L2.Herm.intAf F E) ↔ (fun i => swp F E (y' i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
    refine Iff.trans ?_ (key.trans (latHat_iff Λ y'))
    refine forall₂_congr fun x _ => ?_
    rw [hI, swp_hermA c σ hσ]
  constructor
  · intro hy z hz
    refine Submodule.span_induction (p := fun z _ => Formalism.UG.hform (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F))
        (J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) z (fun i => swp F E (y' i)) ∈
          Formalism.L2.Herm.intAf F E) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨x, hx, rfl⟩
      exact k2.2 hy x hx
    · rw [hform_zero_left]; exact zero_mem _
    · intro a b _ _ ha hb
      rw [hform_add_left]; exact add_mem ha hb
    · intro s a _ ha
      have := GlobalTheory.SplitStab.hform_smul_left (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F))
        (J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) s.1 a (fun i => swp F E (y' i))
      have e : s • a = fun i => s.1 * a i := rfl
      rw [e, this]
      exact mul_mem (hint _ s.2) ha
  · intro h
    exact k2.1 fun x hx => h _ (Submodule.subset_span ⟨x, hx, rfl⟩)

theorem mem_St_of_part (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hβ : IsFrame β Λ) (hΛ : HatSelfDual σ J Λ)
    (p u : Formalism.L2.Herm.intAf F E) (hp : p * p = p)
    (hq : Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) p ∈ Formalism.L2.Herm.intAf F E)
    (Y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) (hu : u * Y.det = p)
    (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hg : g ∈ Formalism.UG.UPts σ J (Formalism.L2.Herm.Af F))
    (f : E ⊗[F] Formalism.L2.Herm.Af F) (hf : f = p + Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) p) (hs : f • (g.1 - 1) = g.1 - 1)
    (hY : (p : E ⊗[F] Formalism.L2.Herm.Af F) • g.1 =
      (p : E ⊗[F] Formalism.L2.Herm.Af F) • (β.1 * Y.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1)) : g ∈ St β := by
  subst hf
  exact (mem_St_iff β Λ hβ g).2 (stab_of_part _ _ _ hΛ p.2 hq g hg hs _ _ (frame_mulVec β Λ hβ Y)
    (frame_mulVec β Λ hβ _) (conj_inv_part β p u Y hu hp) hY)

end Dual

section Adelic

open GlobalTheory.LevSplit Formalism.L2.NTheta

variable {D : D7}

theorem mem_L0c_iff_mem_intVec_of_span_frame (V : HSp D) (x : Fin V.rank → D.host.E) : x ∈ L0c D V ↔ x ∈ GlobalTheory.Member.latC V := by
  rw [GlobalTheory.Member.mem_latC, Module.Basis.equivFun_symm_apply]
  rfl

theorem base_lattice {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {N : ℕ} (hB : IsBaseFrame V β Λ N) :
    Λ.FG ∧ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) = ⊤ := by
  obtain ⟨-, -, hN, h01, h10⟩ := hB
  obtain ⟨-, -, hfg, hspan, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hN' : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  constructor
  · let f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
      (LinearMap.lsmul D.host.E _ (N : D.host.E)).restrictScalars _
    refine Submodule.fg_of_fg_map_injective f (fun a b h => smul_right_injective _ hN' h) ?_
    refine Submodule.FG.of_le hfg ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_L0c_iff_mem_intVec_of_span_frame V _).1 (h10 x hx)
  · rw [eq_top_iff, ← hspan, Submodule.span_le]
    intro x hx
    have h1 : (N : D.host.E) • x ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span (h01 x ((mem_L0c_iff_mem_intVec_of_span_frame V x).2 hx))
    exact (Submodule.smul_mem_iff _ hN').1 h1

theorem hform_eq_sum (V : HSp D) (v y : Fin V.rank → D.host.E) :
    Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram y v =
      ∑ a, ∑ b, v a * V.gramᵀ a b * GlobalTheory.Member.cF D (y b) := by
  unfold Formalism.UG.hform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm, mul_comm ((D.sp.cm.sig : D.host.E →+* D.host.E) _), ← mul_assoc]
  rfl

theorem mem_dual_iff {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (h : Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ) (v : Fin V.rank → D.host.E) :
    (∀ y ∈ Λ, (∑ a, ∑ b, v a * V.gramᵀ a b * GlobalTheory.Member.cF D (y b)) ∈
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ v ∈ Λ := by
  simp only [FractionalIdeal.mem_one_iff]
  constructor
  · intro hv
    rw [← h]
    exact Submodule.subset_span fun y hy => by rw [hform_eq_sum]; exact hv y hy
  · intro hv y hy
    rw [← h] at hv
    refine Submodule.span_induction (p := fun v _ => ∃ x : 𝓞 D.host.E, algebraMap _ D.host.E x =
      ∑ a, ∑ b, v a * V.gramᵀ a b * GlobalTheory.Member.cF D (y b)) ?_ ?_ ?_ ?_ hv
    · intro v hv
      rw [← hform_eq_sum]; exact hv y hy
    · exact ⟨0, by simp⟩
    · rintro a b _ _ ⟨s, hs⟩ ⟨t, ht⟩
      exact ⟨s + t, by rw [map_add, hs, ht]; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]⟩
    · rintro c a _ ⟨s, hs⟩
      exact ⟨c * s, by
        rw [map_mul, hs]; simp only [Pi.smul_apply, Algebra.smul_def, Finset.mul_sum, mul_assoc]⟩

theorem hatL_selfDual {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ} (hB : IsBaseFrame V β Λ N) :
    HatSelfDual D.sp.cm.sig V.gram Λ := by
  obtain ⟨hfg, hspan⟩ := base_lattice hB
  obtain ⟨-, -, -, -, hcc, -, -, hG, hdet, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have h1 : ∀ s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun _ h => sigR_int h
  have h2 : ∀ z, z ∈ GlobalTheory.AdLat.hat1 D.host.F
      ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) ↔
      swp D.host.F D.host.E z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro z
    rw [← GlobalTheory.LatDual.integralTensorAdeles_eq_adelicCompletion_one]
    exact GlobalTheory.IdemSupport.mem_intAE_iff z
  have h3 : ∀ x, D.sp.cm.sig x = GlobalTheory.Member.cF D x := fun _ => rfl
  exact hatL_selfDual_gen (GlobalTheory.Member.cF D) D.sp.cm.sig h3 V.gram Λ hfg hspan hcc hG hdet
    (mem_dual_iff hB.2.1) h1 h2

theorem isConjPl_symm {P P' : Pl D.host.E} (h : Lev.IsConjPl P P') : Lev.IsConjPl P' P := by
  rw [GlobalTheory.IdemSupport.isConjPl_iff] at h ⊢
  subst h
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO]

theorem exists_isIdemAt {P : Pl D.host.E} (h : ¬ Lev.IsConjPl P P) : ∃ e, IsIdemAt e P := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨e, f, hP⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  have hd := (GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hP).1
  rcases hP with ⟨h1, -⟩ | ⟨-, ⟨v, ε, -, rfl⟩, -⟩
  · exact ⟨e, h1⟩
  · have hd' := GlobalTheory.IdemSupport.delta_conj hΦ hd
    rw [GlobalTheory.IdemSupport.cA_algebraMap] at hd'
    rw [GlobalTheory.IdemSupport.isConjPl_iff] at h
    exact absurd (hd.2.1.symm.trans (hd'.2.2 P h)) one_ne_zero

end Adelic

section Local

open GlobalTheory.LevSplit Formalism.L2.NTheta

variable {D : D7}

theorem part_map {R T : Type} [CommRing R] [CommRing T] {n : ℕ} (ψ : R →+* T) (p : R) (A B : Matrix (Fin n) (Fin n) R) :
    p • A = p • B → ψ p • A.map ψ = ψ p • B.map ψ := by
  intro h
  ext i j
  have := congrArg ψ (congrFun (congrFun h i) j)
  simpa only [Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.map_apply] using this

theorem part_lift {R T : Type} [CommRing R] [CommRing T] {n : ℕ} (ψ : R →+* T) (hψ : Function.Bijective ψ) (p : R)
    (m m' : Matrix (Fin n) (Fin n) T) (h : ψ p • (m * m') = ψ p • (1 : Matrix (Fin n) (Fin n) T)) :
    ∃ M M' : Matrix (Fin n) (Fin n) R, M.map ψ = m ∧ p • (M * M') = p • (1 : Matrix (Fin n) (Fin n) R) := by
  choose M hM using fun i j => hψ.2 (m i j)
  choose M' hM' using fun i j => hψ.2 (m' i j)
  have e : Matrix.map (Matrix.of M) ψ = m := Matrix.ext hM
  have e' : Matrix.map (Matrix.of M') ψ = m' := Matrix.ext hM'
  refine ⟨Matrix.of M, Matrix.of M', e, Matrix.ext fun i j => hψ.1 ?_⟩
  rw [← e, ← e', ← Matrix.map_mul, ← Matrix.map_one ψ (map_zero _) (map_one _)] at h
  have := congrFun (congrFun h i) j
  simpa only [Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.map_apply] using this

theorem split_lift_fin (V : HSp D) {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e)
    (m m' : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D))
    (h : finSw D e • (m * m') = finSw D e • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D))) :
    ∃ g : GA D V, Formalism.L2.Theta.SuppAt e V g ∧ finSw D e • (finE V g).1 = finSw D e • m := by
  obtain ⟨M, M', hM, hMM⟩ := part_lift (swapAE D) (swp_bij (F := D.host.F) (E := D.host.E)) (finPart D e) m m' h
  obtain ⟨g, h1, h2⟩ := GlobalTheory.SplitLift.split_lift V e he M M' hMM
  refine ⟨g, h1, ?_⟩
  rw [← hM]
  exact part_map (swapAE D) _ _ _ h2

theorem finSw_div_int {P : Pl D.host.E} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P) {d : 𝓞 D.host.E}
    (hd : d ∉ P.asIdeal) : ∃ u : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (u : Lev.EAf D) * (oToS D.host.F D.host.E d : Formalism.L2.Herm.intAf D.host.F D.host.E) = finSw D e := by
  have d0 : d ≠ 0 := fun h0 => hd (h0 ▸ P.asIdeal.zero_mem)
  refine ⟨⟨_, swapAE_int (not_not.1 fun hn => hd ((he.2 d d0).2 hn))⟩, ?_⟩
  show finSw D (e * incA D ((d : D.host.E)⁻¹)) * finSw D (incA D (d : D.host.E)) = _
  have : (d : D.host.E) ≠ 0 := by simpa using d0
  rw [← RingHom.map_mul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ this, RingHom.map_one, mul_one]

theorem succ_mul_succ_sub_one_div_succ {K R T : Type} [Field K] [CommRing R] [CommRing T] (ψ : R →+* T) (ι : K →+* R) {x : K} (hx : x ≠ 0)
    {e : R} {s : T} (h : s * ψ (ι x) = ψ e) : ψ (e * ι x⁻¹) = s := by
  rw [map_mul, ← h, mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel₀ hx, map_one, map_one, mul_one]

theorem res_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (P : Pl E)
    (p : Formalism.L2.Herm.intAf F E) (hp : p * p = p) (h : ∀ x ∈ P.asIdeal, x ≠ 0 → ∀ s, s * oToS F E x ≠ p) :
    resS F P p = 1 := by
  have := P.isPrime
  have h1 : IsIdempotentElem (resS F P p) := by
    show _ * _ = _
    rw [← RingHom.map_mul, hp]
  refine (IsIdempotentElem.iff_eq_zero_or_one.1 h1).resolve_left fun h0 => ?_
  obtain ⟨x, hx, hx0, s, hs⟩ := idem_dvd P p hp h0
  exact h x hx hx0 s hs

theorem finSw_div_not_int {P : Pl D.host.E} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P) {x : 𝓞 D.host.E}
    (hx : x ∈ P.asIdeal) (hx0 : x ≠ 0) :
    finSw D (e * incA D ((x : D.host.E)⁻¹)) ∉ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  fun h => (he.2 x hx0).1 hx ((GlobalTheory.IdemSupport.mem_intAE_iff _).2 h)

theorem exists_idem_int {P : Pl D.host.E} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P) :
    ∃ p : Formalism.L2.Herm.intAf D.host.F D.host.E, (p : Lev.EAf D) = finSw D e ∧ p * p = p ∧ resS D.host.F P p = 1 := by
  obtain ⟨u, hu⟩ := finSw_div_int he (d := 1) ((Ideal.ne_top_iff_one _).1 P.isPrime.ne_top)
  obtain ⟨p, hp⟩ : ∃ p : Formalism.L2.Herm.intAf D.host.F D.host.E, (p : Lev.EAf D) = finSw D e :=
    ⟨u * oToS D.host.F D.host.E 1, hu⟩
  have hpp : p * p = p := Subtype.ext (by
    show (p : Lev.EAf D) * p = p
    rw [hp, ← RingHom.map_mul, he.1.1])
  refine ⟨p, hp, hpp, res_eq_one P p hpp fun x hx hx0 s hs => finSw_div_not_int he hx hx0 ?_⟩
  have hx' : (x : D.host.E) ≠ 0 := fun h => hx0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have e0 : (s : Lev.EAf D) * (oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) = p :=
    congrArg Subtype.val hs
  have e3 : ((oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
    finSw D (incA D (x : D.host.E)) := rfl
  rw [e3, hp] at e0
  have e2 := succ_mul_succ_sub_one_div_succ (finSw D) (incA D) (x := (x : D.host.E)) hx' (e := e) (s := (s : Lev.EAf D)) e0
  rw [e2]
  exact s.2

theorem exists_matrix_lift {R T : Type} [CommRing R] [CommRing T] {n : ℕ} (ψ : R →+* T) (hψ : Function.Surjective ψ)
    [Nontrivial T] (k : GL (Fin n) T) : ∃ Y : Matrix (Fin n) (Fin n) R, Y.map ψ = k.1 ∧ ψ Y.det ≠ 0 := by
  choose M hM using fun i j => hψ (k.1 i j)
  have e : Matrix.map (Matrix.of M) ψ = k.1 := Matrix.ext hM
  refine ⟨Matrix.of M, e, ?_⟩
  rw [RingHom.map_det, RingHom.mapMatrix_apply, e]
  exact (Matrix.isUnits_det_units k).ne_zero

set_option maxHeartbeats 1000000 in

theorem exists_local_lift {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ} (hB : IsBaseFrame V β Λ N)
    {P : Pl D.host.E} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P) (k : GL (Fin V.rank) (kP P)) :
    ∃ κ : GA D V, Formalism.L2.Theta.SuppAt e V κ ∧ κ ∈ GfC V ∧ finE V κ ∈ St β ∧ redFn β P (finE V κ) = k ∧
      ∀ P', P' ≠ P → ¬ Lev.IsConjPl P P' → redFn β P' (finE V κ) = 1 := by
  have := P.isPrime
  obtain ⟨p, hp, hpp, hres⟩ := exists_idem_int he
  obtain ⟨Y₀, hY₀, hdet⟩ := exists_matrix_lift (Ideal.Quotient.mk P.asIdeal) Ideal.Quotient.mk_surjective k
  obtain ⟨u, hu⟩ := finSw_div_int he (d := Y₀.det) fun h => hdet (Ideal.Quotient.eq_zero_iff_mem.2 h)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Y₀.map (oToS D.host.F D.host.E) := ⟨_, rfl⟩
  have hu' : u * Y.det = p := by
    rw [hY, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact Subtype.ext (hu.trans hp.symm)
  have hmm := conj_inv_part β p u Y hu' hpp
  rw [hp] at hmm
  obtain ⟨κ, hs, hκ⟩ := split_lift_fin V he.1 _ _ hmm
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have hsf := supp_fin V (f := e + cA D e) hs
  rw [← hp] at hκ
  have hf : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
    rw [RingHom.map_add, finSw_cA, hp]
  have hSt : finE V κ ∈ St β :=
    mem_St_of_part D.sp.cm.sig V.gram Λ β hB.1 (hatL_selfDual hB) p u hpp (sigR_int p.2) Y hu' (finE V κ)
      (finE_mem_UA V κ) _ hf hsf hκ
  refine ⟨κ, hs, (T3 P e _ hP).2.2.1 κ hs, hSt, Units.ext ?_, fun P' h1 h2 => ?_⟩
  · rw [redFn_of_smul_eq β P _ hSt p hres Y hκ, hY, ← hY₀]
    exact Matrix.ext fun i j => resS_oToS P _
  · obtain ⟨y, y', hy, hyy, a1, a2⟩ := exists_sep h1 fun h => h2 (isConjPl_symm h)
    obtain ⟨w, hw⟩ := idem_div_int hP y y' hyy a1 a2
    refine redFn_eq_one β P' _ hSt (w * oToS D.host.F D.host.E y) ?_ ?_
    · rw [RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hy, mul_zero]
    · have e1 : ((w * oToS D.host.F D.host.E y : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
          finSw D (e + cA D e) := hw
      rw [e1]
      exact hsf

theorem prod_map_single {ι M : Type} [Monoid M] {l : List ι} (hl : l.Nodup) {a : ι} (ha : a ∈ l) (f : ι → M)
    (h : ∀ b, b ≠ a → f b = 1) : (l.map f).prod = f a := by
  classical
  rw [List.prod_map_eq_pow_single a f fun b hb _ => h b hb, List.count_eq_one_of_mem hl ha, pow_one]

theorem redFn_list_prod (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (l : List (GA D V))
    (h : ∀ g ∈ l, finE V g ∈ St β) :
    finE V l.prod ∈ St β ∧ ∀ P, redFn β P (finE V l.prod) = (l.map fun g => redFn β P (finE V g)).prod := by
  induction l with
  | nil =>
    rw [List.prod_nil, MonoidHom.map_one]
    exact ⟨Subgroup.one_mem _, fun P => redFn_one P⟩
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih fun g hg => h g (List.mem_cons_of_mem _ hg)
    have ha := h a List.mem_cons_self
    rw [List.prod_cons, MonoidHom.map_mul]
    exact ⟨Subgroup.mul_mem _ ha h1, fun P => by rw [redFn_mul ha h1, h2, List.map_cons, List.prod_cons]⟩

theorem exists_lift_prod (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (hB : IsBaseFrame V β Λ N)
    (hc : ∀ PP ∈ L.Pg, ∀ PP', PP' ∈ L.Pg ∨ PP' ∈ L.Q → ¬ Lev.IsConjPl PP PP') (hd : Disjoint L.Pg L.Q)
    (g0 : G0 L.Pg L.r) :
    ∃ (e : L.Pg → Formalism.L2.Theta.AE D) (κ : L.Pg → GA D V),
      (∀ PP : L.Pg, IsIdemAt (e PP) PP.1 ∧ Formalism.L2.Theta.SuppAt (e PP) V (κ PP) ∧ κ PP ∈ GfC V ∧ finE V (κ PP) ∈ St β ∧
        redFn β PP.1 (finE V (κ PP)) = diagOne L.hr (g0 PP) ∧
        ∀ PP', PP' ∈ L.Pg ∨ PP' ∈ L.Q → PP' ≠ PP.1 → redFn β PP' (finE V (κ PP)) = 1) ∧
      ∀ l : List L.Pg, l.Nodup → (∀ PP, PP ∈ l) → IsLevelLift V β L g0 (l.map κ).prod ∧
        (∀ PP : L.Pg, redFn β PP.1 (finE V (l.map κ).prod) = diagOne L.hr (g0 PP)) ∧
        ∀ PP ∈ L.Q, redFn β PP (finE V (l.map κ).prod) = 1 := by
  choose e he using fun PP : L.Pg => exists_isIdemAt (hc PP.1 PP.2 PP.1 (Or.inl PP.2))
  choose κ h1 h2 h3 h4 h5 using fun PP : L.Pg => exists_local_lift hB (he PP) (diagOne L.hr (g0 PP))
  have h6 : ∀ (PP : L.Pg) PP', PP' ∈ L.Pg ∨ PP' ∈ L.Q → PP' ≠ PP.1 → redFn β PP' (finE V (κ PP)) = 1 :=
    fun PP PP' a b => h5 PP PP' b (hc PP.1 PP.2 PP' a)
  refine ⟨e, κ, fun PP => ⟨he PP, h1 PP, h2 PP, h3 PP, h4 PP, h6 PP⟩, fun l hl hall => ?_⟩
  obtain ⟨hS, hr⟩ := redFn_list_prod V β (l.map κ) (by
    intro g hg
    obtain ⟨PP, -, rfl⟩ := List.mem_map.1 hg
    exact h3 PP)
  have rg : ∀ PP : L.Pg, redFn β PP.1 (finE V (l.map κ).prod) = diagOne L.hr (g0 PP) := by
    intro PP
    rw [hr, List.map_map, prod_map_single hl (hall PP) ((fun g => redFn β PP.1 (finE V g)) ∘ κ) (fun a ha =>
      h6 a PP.1 (Or.inl PP.2) fun h => ha (Subtype.ext h.symm))]
    exact h4 PP
  have rq : ∀ PP ∈ L.Q, redFn β PP (finE V (l.map κ).prod) = 1 := by
    intro PP hP
    rw [hr, List.map_map]
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact h6 a PP (Or.inr hP) fun h => Finset.disjoint_left.1 hd a.2 (h ▸ hP)
  refine ⟨⟨Subgroup.list_prod_mem _ fun g hg => ?_,
    mem_parLev.2 ⟨finE_mem_UA V _, hS, fun PP hP => ?_, fun PP hP => ?_⟩, funext fun PP => ?_⟩, rg, rq⟩
  · obtain ⟨PP, -, rfl⟩ := List.mem_map.1 hg
    exact h2 PP
  · rw [rg ⟨PP, hP⟩]; exact diagOne_mem _ _ _
  · rw [rq PP hP]; exact Subgroup.one_mem _
  · show upperLeftBlock L.hr (redFn β PP.1 _) = _
    rw [rg PP, topLeftBlock_blockDiagWithIdentityGL]

end Local

theorem liftsExist : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), ∀ (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → (∀ PP ∈ L.Pg, ∀ PP', PP' ∈ L.Pg ∨ PP' ∈ L.Q → ¬ IsConjPl PP PP') → Disjoint L.Pg L.Q → LiftsExist V β L := by
  intro D V β L Λ N hB hc hd g0
  obtain ⟨-, κ, -, h⟩ := exists_lift_prod V β L Λ N hB hc hd g0
  exact ⟨_, (h Finset.univ.toList (Finset.nodup_toList _) fun PP => Finset.mem_toList.2 (Finset.mem_univ PP)).1⟩

end GlobalTheory.ParahoricLift

end

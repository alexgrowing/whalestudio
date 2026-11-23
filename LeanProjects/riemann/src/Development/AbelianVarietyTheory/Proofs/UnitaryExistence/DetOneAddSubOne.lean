import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalLevelEqHalfMarkingStabilizer

namespace GlobalTheory.MarkDet

section General

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem prod_sub_prod {ι : Type} (M : ℕ) (s : Finset ι) (I : ι → FractionalIdeal (𝓞 E)⁰ E)
    (y z : ι → RA F E) (hy : ∀ i, y i ∈ hat1 F (I i : Set E)) (hz : ∀ i, z i ∈ hat1 F (I i : Set E)) :
    ∃ w ∈ hat1 F ((∏ i ∈ s, I i : FractionalIdeal (𝓞 E)⁰ E) : Set E),
      ∏ i ∈ s, (y i + M • z i) - ∏ i ∈ s, y i = M • w := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, zero_mem _, by simp⟩
  | insert a s ha ih =>
    obtain ⟨w, hw, e⟩ := ih
    have hp := prod_mem_adelicCompletionOfElementSet F s I y (fun i _ => hy i)
    have mul := (adelicCompletion_fractionalIdeal_properties F E).1 (I a) (∏ i ∈ s, I i)
    refine ⟨y a * w + z a * (∏ i ∈ s, y i + M • w), ?_, ?_⟩
    · rw [Finset.prod_insert ha]
      exact add_mem (mul _ (hy a) _ hw) (mul _ (hz a) _ (add_mem hp (nsmul_mem hw M)))
    · rw [Finset.prod_insert ha, Finset.prod_insert ha, sub_eq_iff_eq_add.1 e]
      simp only [nsmul_eq_mul]
      ring

theorem det_one_add_sub_one {n : ℕ} (M : ℕ) (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E) (hc : ∀ a, cI a ≠ 0)
    (K : Matrix (Fin n) (Fin n) (RA F E))
    (h : ∀ i j, K i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E)) :
    ∃ w ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E), (1 + M • K).det - 1 = M • w := by
  have h1 : ∀ i j, (1 : Matrix (Fin n) (Fin n) (RA F E)) i j ∈
      hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, mul_inv_cancel₀ (hc i), Algebra.TensorProduct.one_def]
      exact one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.one_mem_one _)
    · rw [Matrix.one_apply_ne hij]
      exact zero_mem _
  have key : ∀ σ : Equiv.Perm (Fin n), ∃ w ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E),
      ∏ j, (1 + M • K) (σ j) j - ∏ j, (1 : Matrix (Fin n) (Fin n) (RA F E)) (σ j) j = M • w := by
    intro σ
    have := prod_sub_prod F M Finset.univ (fun j => cI (σ j) * (cI j)⁻¹)
      (fun j => (1 : Matrix (Fin n) (Fin n) (RA F E)) (σ j) j) (fun j => K (σ j) j)
      (fun j => h1 _ _) (fun j => h _ _)
    rw [Finset.prod_mul_distrib, Equiv.prod_comp σ cI, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (hc i)] at this
    exact this
  choose w hw e using key
  refine ⟨∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • w σ, sum_mem fun σ _ => ?_, ?_⟩
  · rw [Units.smul_def]
    exact zsmul_mem (hw σ) _
  · have d1 : (1 : RA F E) = (1 : Matrix (Fin n) (Fin n) (RA F E)).det := Matrix.det_one.symm
    rw [d1, Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← smul_sub, e, Units.smul_def, Units.smul_def, smul_comm]

theorem det_sub_one_of_cong {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : ℕ) (hM : M ≠ 0)
    (G : Matrix (Fin n) (Fin n) (RA F E))
    (hg : ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ y ∈ hat F (L : Set (Fin n → E)), G *ᵥ z - z = M • y) :
    ∃ w ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), G.det - 1 = M • w := by
  have hone : ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) = Set.range (algebraMap (𝓞 E) E) := by
    ext x
    exact FractionalIdeal.mem_one_iff _
  rw [← hone]
  obtain ⟨-, e, cI, hc, hL, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
  have key := mem_hat_pseudoBasis_iff F E n L e cI hL
  let P : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i a => fv F (e a) i
  let Q : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun b i =>
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b
  have hP : ∀ w : Fin n → RA F E, P *ᵥ w = ∑ a, w a • fv F (e a) := by
    intro w
    funext i
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hQ : ∀ w b, (Q *ᵥ w) b = adCoord F e b w := by
    intro w b
    change ∑ i : Fin n, _ = ∑ i : Fin n, _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hQP : Q * P = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    funext b
    rw [← Matrix.mulVec_mulVec, hQ, hP, adCoord_sum, Matrix.one_mulVec]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have key' : ∀ w, P *ᵥ w ∈ hat F (L : Set (Fin n → E)) ↔ ∀ a, w a ∈ hat1 F (cI a : Set E) := by
    intro w; rw [hP]; exact key w
  have hMF : (M : F) ≠ 0 := Nat.cast_ne_zero.mpr hM
  obtain ⟨m, hm⟩ : ∃ m : RA F E, m * (M : RA F E) = 1 :=
    ⟨algebraMap F (RA F E) (M : F)⁻¹, by
      rw [← map_natCast (algebraMap F (RA F E)) M, ← map_mul, inv_mul_cancel₀ hMF, map_one]⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) (RA F E), N = m • (G - 1) := ⟨_, rfl⟩
  have hGN : G = 1 + M • N := by
    rw [hN, ← Nat.cast_smul_eq_nsmul (RA F E), smul_smul, mul_comm, hm, one_smul, add_sub_cancel]
  have hNz : ∀ z ∈ hat F (L : Set (Fin n → E)), N *ᵥ z ∈ hat F (L : Set (Fin n → E)) := by
    intro z hz
    obtain ⟨y, hy, ey⟩ := hg z hz
    rw [hN, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ey,
      ← Nat.cast_smul_eq_nsmul (RA F E), smul_smul, hm, one_smul]
    exact hy
  obtain ⟨k, hk0⟩ : ∃ k : Matrix (Fin n) (Fin n) (RA F E), k = Q * N * P := ⟨_, rfl⟩
  have hPk : P * k = N * P := by
    simp only [hk0, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hkdet : (1 + M • k).det = G.det := by
    have h1 : Q.det * P.det = 1 := by rw [← Matrix.det_mul, hQP, Matrix.det_one]
    have h2 : 1 + M • k = Q * G * P := by
      rw [hGN, hk0, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hQP, Matrix.mul_smul, Matrix.smul_mul]
    rw [h2]
    simp only [Matrix.det_mul]
    linear_combination G.det * h1
  have hk : ∀ i j, k i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    refine mem_adelicCompletion_mul_inv_fractionalIdeal F _ _ _ (hc j) fun x hx => ?_
    have h1 : P *ᵥ (Pi.single j ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x)) ∈
        hat F (L : Set (Fin n → E)) := by
      rw [key']
      intro a
      by_cases ha : a = j
      · subst ha
        rw [Pi.single_eq_same]
        exact one_tmul_mem_adelicCompletionOfElementSet F hx
      · rw [Pi.single_eq_of_ne ha]
        exact zero_mem _
    have h2 := hNz _ h1
    rw [Matrix.mulVec_mulVec, ← hPk, ← Matrix.mulVec_mulVec, key'] at h2
    have h3 := h2 i
    rwa [Matrix.mulVec_single, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op] at h3
  rw [← hkdet]
  exact det_one_add_sub_one F M cI hc k hk

end General

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

theorem finCong_of_marks {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H) (V : HSp D)
    (g g' : GA D V) (hL : latG V g = latG V g')
    (hm : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • latG V 1, ∃ x, ∃ w ∈ latGHat V g,
      ∃ w' ∈ latGHat V g', x - (finHom V g).1 *ᵥ finVec V a = (l.M : ℕ) • w ∧
        x - (finHom V g').1 *ᵥ finVec V a = (l.M : ℕ) • w') : FinCong V l.M (g⁻¹ * g') := by
  refine (finCong_iff_half D H l V _).2 (((GlobalTheory.Member.AALev.congruences_agree D V _).2 l.M _).2 fun a ha => ?_)
  obtain ⟨x, w, hw, w', hw', e, e'⟩ := hm a ha
  obtain ⟨-, -, -, h4, h5, -⟩ := latG_lattice_and_completion D V g
  have h5' := (latG_lattice_and_completion D V g').2.2.2.2.1
  have h51 := (latG_lattice_and_completion D V 1).2.2.2.2.1
  rw [h5', ← hL, ← h5] at hw'
  have hd := sub_mem hw hw'
  rw [← SetLike.mem_coe, h4, ← h51] at hd
  obtain ⟨y, hy, ey⟩ := hd
  refine ⟨y, hy, ?_⟩
  have hinv : ∀ z, (finHom V g⁻¹).1 *ᵥ ((finHom V g).1 *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  have e3 : (finHom V g').1 *ᵥ finVec V a - (finHom V g).1 *ᵥ finVec V a = (l.M : ℕ) • ((finHom V g).1 *ᵥ y) := by
    rw [ey, nsmul_sub, ← e, ← e']
    abel
  have e4 := congrArg (fun z => (finHom V g⁻¹).1 *ᵥ z) e3
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hinv] at e4
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  exact e4

theorem gLat_eq_of_finCong {D : D7} {V : HSp D} {N : ℕ} {u : GA D V} (hu : FinCong V N u) :
    gLat V u = latHat V := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact PrincLevel.finCong_map hu y hy
  · intro hz
    refine ⟨_, PrincLevel.finCong_map (PrincLevel.finCong_inv hu) z hz, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]

set_option maxHeartbeats 800000 in

theorem exists_finCong_det : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h h' γ γ' k, C.Mark h k γ → C.Mark h' k γ' → ∃ u : GA D V, gLat V u = latHat V ∧ FinCong V l.M u ∧ finHom V (γ' * h') = finHom V (γ * h) * finHom V u ∧ ∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom V (u)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w := by
  intro D H Dw l Xo c σ V r C hC h h' γ γ' k hm hm'
  obtain rfl : V.rank = r := C.hr
  obtain ⟨-, hΛ, hk⟩ := hm
  obtain ⟨-, hΛ', hk'⟩ := hm'
  have hL : (C.M.X k).Λ = latG V (γ * h) := SetLike.ext' (hΛ.trans (Set.image_id _))
  have hL' : (C.M.X k).Λ = latG V (γ' * h') := SetLike.ext' (hΛ'.trans (Set.image_id _))
  have hu : FinCong V l.M ((γ * h)⁻¹ * (γ' * h')) := by
    refine finCong_of_marks l V _ _ (hL.symm.trans hL') fun a ha => ?_
    rw [← hC.iota.emb.2, ← Submodule.map_top, ← Submodule.map_smul''] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨w, hw, e⟩ := hk b hb
    obtain ⟨w', hw', e'⟩ := hk' b hb
    exact ⟨_, w, hw, w', hw', e, e'⟩
  refine ⟨_, gLat_eq_of_finCong hu, hu, by rw [← map_mul, mul_inv_cancel_left], ?_⟩
  obtain ⟨h1, -, h3, h4, -⟩ := latHat_eq_hat_and_gram D V
  unfold FinCong at hu
  rw [h1] at hu
  exact det_sub_one_of_cong D.host.F (latC V) h3 h4 l.M (by have := l.three_le; omega) _ hu

end GlobalTheory.MarkDet

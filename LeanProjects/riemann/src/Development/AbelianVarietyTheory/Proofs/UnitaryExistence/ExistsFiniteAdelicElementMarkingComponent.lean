import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealDivisibleEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramePeriods
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsInverseUnitTower
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGramStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletionStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceFormStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplitStatement

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem onto_dom_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP hg using X.signature
  have hs : ∀ a : ℕ, sgn X.p0 a ≠ 0 := fun a => by unfold sgn; split_ifs <;> norm_num
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have e : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [show gram τ.1 X.Gm (mat (fun τ => P τ) τ) = gram τ.1 X.Gm (P τ) from rfl, hg τ,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  rw [e, Complex.ofReal_re]
  have h0 : psgn X.p0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hs a
  exact mul_self_pos.2 h0

theorem onto_adelic_of_tower (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L Λ : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (hLs : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hΛ : Λ.FG) (hΛs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    {A B : Type} [AddCommGroup A] [Module (𝓞 E) A] [AddCommGroup B] [Module (𝓞 E) B]
    (ι : A ≃ₗ[𝓞 E] L) (φ : B ≃ₗ[𝓞 E] Λ) (EA : A → A → ℤ) (EB : B → B → ℤ) (f : ℕ → A →ₗ[𝓞 E] B)
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (ξ : E) (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hJ : ∀ z : E, z ∈ J ↔ ∀ a : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (ξ * (a * z)) = m)
    (hA : ∀ x y, Algebra.trace ℚ E (ξ * ∑ a, ∑ b, (ι x : Fin n → E) a * G a b * c ((ι y : Fin n → E) b)) =
      -(EA x y : ℚ))
    (hB : ∀ x y, Algebra.trace ℚ E (ξ * ∑ a, ∑ b, (φ x : Fin n → E) a * G a b * c ((φ y : Fin n → E) b)) =
      -(EB x y : ℚ))
    (h1 : ∀ N m : ℕ, 0 < N → 0 < m → ∀ a, ∃ e, f (N * m) a = f N a + N • e)
    (h2 : ∀ N : ℕ, 0 < N → (∀ a, (∃ e, f N a = N • e) ↔ ∃ e, a = N • e) ∧ ∀ a', ∃ a e, a' = f N a + N • e)
    (h3 : ∀ N : ℕ, 0 < N → ∀ a a', (N : ℤ) ∣ EB (f N a) (f N a') - EA a a') :
    ∃ g : GL (Fin n) (GlobalTheory.AdLat.RA F E),
      (g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)).mulVec '' (GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) =
        GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) ∧
      (∀ N : ℕ, 0 < N → ∀ a : A, ∃ w ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)),
        (g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ GlobalTheory.AdLat.fv F (ι a : Fin n → E) =
          GlobalTheory.AdLat.fv F (φ (f N a) : Fin n → E) + N • w) ∧
      ∀ x y, GlobalTheory.AdLat.hermA c G ((g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ x)
        ((g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ y) = GlobalTheory.AdLat.hermA c G x y := by
  let f' : ℕ → (L →ₗ[𝓞 E] Λ) := fun N => φ.toLinearMap ∘ₗ f N ∘ₗ ι.symm.toLinearMap
  have hf' : ∀ N a, f' N (ι a) = φ (f N a) := fun N a => by simp [f']
  have hlin : ∀ (s : 𝓞 E) (x y : Fin n → E), (s : E) * ∑ a, ∑ b, x a * G a b * c (y b) =
      ∑ a, ∑ b, (s • x) a * G a b * c (y b) := by
    intro s x y
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change _ = ((s : E) * x a) * _ * _
    ring
  obtain ⟨g, hg1, hg2, hg3⟩ := GlobalTheory.AdLat.exists_adelic_matrix_of_tower F E n L Λ f' hL hLs hΛ hΛs
    (fun N m hN hm a => by
      obtain ⟨a, rfl⟩ := ι.surjective a
      obtain ⟨e, he⟩ := h1 N m hN hm a
      exact ⟨φ e, by rw [hf', hf', he, map_add, map_nsmul]⟩)
    (fun N hN => ⟨fun a => by
      obtain ⟨a, rfl⟩ := ι.surjective a
      rw [hf']
      constructor
      · rintro ⟨v, hv⟩
        obtain ⟨e, he⟩ := ((h2 N hN).1 a).1 ⟨φ.symm v, by rw [← map_nsmul, ← hv, LinearEquiv.symm_apply_apply]⟩
        exact ⟨ι e, by rw [he, map_nsmul]⟩
      · rintro ⟨v, hv⟩
        obtain ⟨e, he⟩ := ((h2 N hN).1 a).2 ⟨ι.symm v, by rw [← map_nsmul, ← hv, LinearEquiv.symm_apply_apply]⟩
        exact ⟨φ e, by rw [he, map_nsmul]⟩, fun a' => by
      obtain ⟨a', rfl⟩ := φ.surjective a'
      obtain ⟨a, e, he⟩ := (h2 N hN).2 a'
      exact ⟨ι a, φ e, by rw [hf', he, map_add, map_nsmul]⟩⟩)
  refine ⟨g, hg1, fun N hN a => by rw [← hf']; exact hg2 N hN (ι a), hg3 c G J ?_ ?_⟩
  · intro x hx y hy
    obtain ⟨x', hx'⟩ := φ.surjective ⟨x, hx⟩
    obtain ⟨y', hy'⟩ := φ.surjective ⟨y, hy⟩
    rw [hJ]
    intro s
    refine ⟨-EB (s • x') y', ?_⟩
    rw [hlin, Int.cast_neg, ← hB, map_smul, hx', hy']
    rfl
  · intro N hN x y
    obtain ⟨x, rfl⟩ := ι.surjective x
    obtain ⟨y, rfl⟩ := ι.surjective y
    have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [hf', hf']
    refine ⟨(N : E)⁻¹ * ((∑ a, ∑ b, (φ (f N x) : Fin n → E) a * G a b * c ((φ (f N y) : Fin n → E) b)) -
      ∑ a, ∑ b, (ι x : Fin n → E) a * G a b * c ((ι y : Fin n → E) b)), ?_, ?_⟩
    · rw [hJ]
      intro s
      obtain ⟨m, hm⟩ := h3 N hN (s • x) y
      refine ⟨-m, ?_⟩
      have e1 := hA (s • x) y
      have e2 := hB (f N (s • x)) (f N y)
      rw [map_smul, Submodule.coe_smul, ← hlin] at e1
      rw [show (φ (f N (s • x)) : Fin n → E) = s • (φ (f N x) : Fin n → E) by
        rw [map_smul, map_smul, Submodule.coe_smul], ← hlin] at e2
      have hm' : (EB (f N (s • x)) (f N y) : ℚ) - EA (s • x) y = N * m := by exact_mod_cast hm
      generalize (∑ a, ∑ b, (φ (f N x) : Fin n → E) a * G a b * c ((φ (f N y) : Fin n → E) b)) = u at e2 ⊢
      generalize (∑ a, ∑ b, (ι x : Fin n → E) a * G a b * c ((ι y : Fin n → E) b)) = v at e1 ⊢
      have e3 : ξ * ((s : E) * ((N : E)⁻¹ * (u - v))) = (N : ℚ)⁻¹ • (ξ * (s * u) - ξ * (s * v)) := by
        rw [Algebra.smul_def, map_inv₀, map_natCast]; ring
      rw [e3, map_smul, map_sub, e1, e2, smul_eq_mul]
      push_cast
      field_simp
      linear_combination -hm'
    · rw [nsmul_eq_mul, mul_inv_cancel_left₀ hN0, add_sub_cancel]

theorem onto_marking_sub (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n N : ℕ}
    {u v e : Fin n → E} {z w : Fin n → GlobalTheory.AdLat.RA F E} (h : u = v + N • e)
    (hz : z = GlobalTheory.AdLat.fv F u + N • w) : GlobalTheory.AdLat.fv F v - z = N • -(GlobalTheory.AdLat.fv F e + w) := by
  rw [hz, h, GlobalTheory.AdLat.cap_fv_add, GlobalTheory.AdLat.cap_fv_nsmul, smul_neg, smul_add]
  abel

theorem exists_finite_mark : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ k, ∃ h ∈ GfC V, C.Mark h k 1 := by
  intro D H Dw l Xo c σ V r C hC k
  obtain rfl : V.rank = r := C.hr
  have hneg := (GlobalTheory.T.exists_memberDictionaryContext_goodEmbedding D H Dw l Xo c σ V _ rfl C.ι hC.iota hC.pos hC.lA hC.good).2.1 C hC
  obtain ⟨Pf, -, -, hPf, -⟩ := GlobalTheory.exists_framePeriods D.host.E H Dw l Xo c σ C.g C.e C.F _ C.M hC.good hC.base hneg k
  obtain ⟨x, hx⟩ := onto_dom_nonempty (C.M.X k)
  obtain ⟨f, h1, h2, h3, h4⟩ := GlobalTheory.familyUnif_lattice_genus D.host.E H Dw l Xo _ C.g _ C.F k (Pf x) (hPf x hx)
  obtain ⟨-, hfv, -, -, -, hcc, -, -, -, hT, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  obtain ⟨hL, hLs, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V 1
  let ι : Dw.La ≃ₗ[𝓞 D.host.E] latG V 1 :=
    (LinearEquiv.ofInjective C.ι hC.iota.emb.1).trans (LinearEquiv.ofEq _ _ hC.iota.emb.2)
  have hι : ∀ a, (ι a : Fin V.rank → D.host.E) = C.ι a := fun a => rfl
  have hherm : ∀ x y : Fin V.rank → D.host.E, (∑ a, ∑ b, x a * V.gramᵀ a b * cF D (y b)) = -herm (-V.gramᵀ) x y := by
    intro x y
    simp only [herm, hcc, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
  have hGm : (C.M.X k).Gm = -V.gramᵀ := (hC.modelW k).1
  have hxi : (C.M.X k).ξ0 = -D.host.xi0 := (hC.modelW k).2
  obtain ⟨g, hg1, hg2, hg3⟩ := onto_adelic_of_tower D.host.F D.host.E V.rank (latG V 1) (C.M.X k).Λ hL hLs
    (C.M.X k).Λ_fg (C.M.X k).Λ_span ι (C.M.φ k) (fun a b => Dw.EF a b) (fun a b => (C.F.Di k).EF a b) f
    (cF D) V.gramᵀ D.host.xi0 _ (GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm D V 1 _ rfl).1
    (fun x y => by
      have halt : Dw.EF y x = -Dw.EF x y := by
        have := Dw.alt (x + y)
        simp only [map_add, LinearMap.add_apply, Dw.alt] at this
        linear_combination this
      rw [hherm, hι, hι, ← hT, ← hC.iota.isom, halt, Int.cast_neg])
    (fun x y => by
      rw [hherm, hC.base.ef k x y, hGm, hxi, neg_neg, mul_neg, map_neg])
    h1 h2 h3
  obtain ⟨h, hh, rfl⟩ := (GlobalTheory.T.adelicUnitary_eq_real_mul_finite_split D V).2.2.2.1 g hg3
  obtain ⟨-, -, hlat, hhat, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V h
  have hcap := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank (C.M.X k).Λ (C.M.X k).Λ_fg
    (C.M.X k).Λ_span).1
  rw [hg1] at hhat
  refine ⟨h, hh, one_mem _, ?_, fun a ha => ?_⟩
  · rw [one_mul, hlat]
    ext v
    rw [SetLike.mem_coe, ← hcap, ← SetLike.mem_coe, ← hg1]
    constructor
    · intro hv
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact hv
  · rw [one_mul]
    obtain ⟨e, he⟩ := h4 a ha
    obtain ⟨w, hw, hw'⟩ := hg2 l.M (lt_of_lt_of_le (by norm_num) l.three_le) a
    refine ⟨-(GlobalTheory.AdLat.fv D.host.F (C.M.φ k e : Fin V.rank → D.host.E) + w), ?_, ?_⟩
    · have h0 := (hcap _).2 (C.M.φ k e).2
      have h5 := AddSubgroup.neg_mem _ (AddSubgroup.add_mem _ h0 hw)
      rw [← SetLike.mem_coe, ← hhat] at h5
      exact h5
    · rw [hfv, hfv, ← hι]
      change GlobalTheory.AdLat.fv D.host.F (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) - _ = _
      have he' : (C.M.φ k (f l.M a) : Fin V.rank → D.host.E) =
          (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) + l.M • (C.M.φ k e : Fin V.rank → D.host.E) := by
        rw [he, (C.M.φ k).map_add, map_nsmul (C.M.φ k)]
        rfl
      exact onto_marking_sub D.host.F he' hw'

end GlobalTheory.Member

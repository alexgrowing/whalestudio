import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranspOfMovesAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryTriangularPeriodsOfFramePointMove
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRationalIsometryOfTraceIsometry
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotAntiIsometryOfTriangularRelatedPeriods
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FramesDifferByIsometryAndTriangularOfPeriods
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPoints
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShareOn.OneFrame

section Alg

variable {R : Type} [CommRing R] {M N P : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

def BijMod (I : Ideal R) (f : M →ₗ[R] N) : Prop :=
  (∀ a, f a ∈ I • (⊤ : Submodule R N) → a ∈ I • (⊤ : Submodule R M)) ∧
    ∀ z, ∃ a, z - f a ∈ I • (⊤ : Submodule R N)

theorem map_mem_smul_top (I : Ideal R) (f : M →ₗ[R] N) {a : M} (ha : a ∈ I • (⊤ : Submodule R M)) :
    f a ∈ I • (⊤ : Submodule R N) :=
  Submodule.smul_top_le_comap_smul_top I f ha

theorem BijMod.comp {I : Ideal R} {f : M →ₗ[R] N} {g : N →ₗ[R] P} (hf : BijMod I f) (hg : BijMod I g) :
    BijMod I (g ∘ₗ f) := by
  refine ⟨fun a ha => hf.1 a (hg.1 _ ha), fun z => ?_⟩
  obtain ⟨b, hb⟩ := hg.2 z
  obtain ⟨a, ha⟩ := hf.2 b
  refine ⟨a, ?_⟩
  have := Submodule.add_mem _ hb (map_mem_smul_top I g ha)
  rwa [map_sub, sub_add_sub_cancel] at this

theorem bijMod_equiv (I : Ideal R) (f : M ≃ₗ[R] N) : BijMod I f.toLinearMap :=
  ⟨fun a ha => by simpa using map_mem_smul_top I f.symm.toLinearMap ha,
    fun z => ⟨f.symm z, by simp⟩⟩

theorem bijMod_of_inv {I : Ideal R} (f : M →ₗ[R] N) (g : N →ₗ[R] M) {m : R} (hm : m ∈ I)
    (h₁ : ∀ a, a = g (f a) + m • a) (h₂ : ∀ z, z = f (g z) + m • z) : BijMod I f := by
  refine ⟨fun a ha => ?_, fun z => ⟨g z, ?_⟩⟩
  · rw [h₁ a]
    exact Submodule.add_mem _ (map_mem_smul_top I g ha) (Submodule.smul_mem_smul hm Submodule.mem_top)
  · rw [sub_eq_iff_eq_add'.2 (h₂ z)]
    exact Submodule.smul_mem_smul hm Submodule.mem_top

theorem bijMod_of_nat {I : Ideal R} (f : M →ₗ[R] N) {n : ℕ} (hn : (n : R) ∈ I)
    (h₁ : ∀ a, (∃ b, f a = n • b) → ∃ b, a = n • b) (h₂ : ∀ b, ∃ a e, b = f a + n • e) : BijMod I f := by
  have hM : ∀ e : M, n • e ∈ I • (⊤ : Submodule R M) := fun e => by
    rw [← Nat.cast_smul_eq_nsmul R]; exact Submodule.smul_mem_smul hn Submodule.mem_top
  have hN : ∀ e : N, n • e ∈ I • (⊤ : Submodule R N) := fun e => by
    rw [← Nat.cast_smul_eq_nsmul R]; exact Submodule.smul_mem_smul hn Submodule.mem_top
  refine ⟨fun a ha => ?_, fun z => ?_⟩
  · have key : ∀ z ∈ I • (⊤ : Submodule R N), ∃ a ∈ I • (⊤ : Submodule R M), ∃ e, z = f a + n • e := by
      intro z hz
      refine Submodule.smul_induction_on hz (fun c hc b _ => ?_) ?_
      · obtain ⟨a, e, rfl⟩ := h₂ b
        exact ⟨c • a, Submodule.smul_mem_smul hc Submodule.mem_top, c • e, by
          rw [smul_add, map_smul, smul_comm c n e]⟩
      · rintro _ _ ⟨a, ha, e, rfl⟩ ⟨a', ha', e', rfl⟩
        exact ⟨a + a', Submodule.add_mem _ ha ha', e + e', by rw [map_add, smul_add]; abel⟩
    obtain ⟨a', ha', e, he⟩ := key _ ha
    obtain ⟨b, hb⟩ := h₁ (a - a') ⟨e, by rw [map_sub, he, add_sub_cancel_left]⟩
    rw [sub_eq_iff_eq_add.1 hb]
    exact Submodule.add_mem _ (hM b) ha'
  · obtain ⟨a, e, rfl⟩ := h₂ z
    exact ⟨a, by rw [add_sub_cancel_left]; exact hN e⟩

def BijMod.equiv {I : Ideal R} {f : M →ₗ[R] N} (hf : BijMod I f) :
    (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R] (N ⧸ (I • (⊤ : Submodule R N))) :=
  LinearEquiv.ofBijective (Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top I f))
    ⟨(injective_iff_map_eq_zero _).2 fun q hq => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
      exact (Submodule.Quotient.mk_eq_zero _).2 (hf.1 a hq),
    fun q => by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨a, ha⟩ := hf.2 z
      exact ⟨Submodule.Quotient.mk a, by
        rw [Submodule.mapQ_apply]; exact ((Submodule.Quotient.eq _).2 ha).symm⟩⟩

theorem BijMod.equiv_mk {I : Ideal R} {f : M →ₗ[R] N} (hf : BijMod I f) (a : M) :
    hf.equiv (Submodule.Quotient.mk a) = Submodule.Quotient.mk (f a) := rfl

theorem BijMod.reads {I : Ideal R} {f : M →ₗ[R] N} {f' : M →ₗ[R] P} (hf : BijMod I f) (hf' : BijMod I f')
    (γ : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R] (M ⧸ (I • (⊤ : Submodule R M)))) (g : M → M)
    (hg : ∀ a, Submodule.Quotient.mk (g a) = γ (Submodule.Quotient.mk a)) (A : N →ₗ[R] P)
    (hA : ∀ a, A (f (g a)) - f' a ∈ I • (⊤ : Submodule R P)) (w : N) :
    Submodule.Quotient.mk (A w) = hf'.equiv (γ.symm (hf.equiv.symm (Submodule.Quotient.mk w))) := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (γ.symm (hf.equiv.symm (Submodule.Quotient.mk w)))
  have h1 : (Submodule.Quotient.mk (f (g a)) : N ⧸ (I • (⊤ : Submodule R N))) = Submodule.Quotient.mk w := by
    rw [← hf.equiv_mk, hg, ha]; simp
  rw [← ha, hf'.equiv_mk]
  have h2 := map_mem_smul_top I A ((Submodule.Quotient.eq _).1 h1.symm)
  have := Submodule.add_mem _ h2 (hA a)
  rw [map_sub, sub_add_sub_cancel] at this
  exact (Submodule.Quotient.eq _).2 this

end Alg

section Geo

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open scoped Matrix CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l}

theorem natCast_M_mem (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) : (l.M : 𝓞 E) ∈ l.Mb :=
  Ideal.mul_le_left (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) (by rw [l.prod]; exact Ideal.mem_span_singleton_self _)

theorem familyUniformisation_marking_bijectiveModuloLevel {g : ℕ} {σ : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) (i : Fin F.n) :
    BijMod l.Mb (F.t i) := by
  refine bijMod_of_nat (F.t i) (n := l.M') ?_ (fun a => (F.t_inj i a).1) (F.t_surj i)
  obtain ⟨d, hd⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  rw [hd, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (natCast_M_mem l)

theorem marking_of_levMove {g : ℕ} {σ : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} {gM gA : Dw.La →ₗ[𝓞 E] Dw.La}
    (hν : IsLevMove ρ ν gM gA) {i j : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)} {P' : (F.Di j).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di j) ty P') (hu : F.u i P ≫ ρ = F.u j P')
    (gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hh : ∀ a, P' (gam a) = h (P a)) (hex : ∀ z, (F.ex j P' (h z)).left = (F.ex i P z).left ≫ ν.φ) (a : Dw.La) :
    gam (F.t i (gM a)) - F.t j a ∈ l.Mb • (⊤ : Submodule (𝓞 E) (F.Di j).La) := by
  have hM0 : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  have key : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      gam (F.t i (gM a)) - F.t j a ∈ l.Mb • (⊤ : Submodule (𝓞 E) (F.Di j).La) := by
    intro a ha
    have e1 := congrArg (fun f => f.left) (F.ex_eta i P hP (gM a) (map_mem_smul_top _ gM ha))
    have e2 := congrArg (fun f => f.left) (F.ex_eta j P' hP' a ha)
    simp only [Over.comp_left] at e1 e2
    have e3 : F.ex j P' ((l.M : ℂ)⁻¹ • P' (gam (F.t i (gM a)))) = F.ex j P' ((l.M : ℂ)⁻¹ • P' (F.t j a)) := by
      apply Over.OverMorphism.ext
      rw [hh, ← map_smul, hex, ← e1, ← e2, Category.assoc, hν.2.1, ← Category.assoc]
      congr 1
    have e4 : F.ex j P' ((l.M : ℂ)⁻¹ • P' (gam (F.t i (gM a)) - F.t j a)) = 1 := by
      have := F.ex_add j P' hP' ((l.M : ℂ)⁻¹ • P' (gam (F.t i (gM a)) - F.t j a)) ((l.M : ℂ)⁻¹ • P' (F.t j a))
      rw [← smul_add, ← map_add, sub_add_cancel, e3] at this
      exact (mul_eq_right.1 this.symm)
    obtain ⟨e, he⟩ := (F.ex_ker j P' hP' _).1 e4
    have e5 : gam (F.t i (gM a)) - F.t j a = l.M • e := by
      apply hP'.2.1
      rw [map_nsmul, he, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hM0, one_smul]
    rw [e5, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (natCast_M_mem l) Submodule.mem_top
  obtain ⟨β, hβ, m, hμ, h1⟩ := Submodule.mem_sup.1 (l.coprime ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ _)
  have k1 := key (m • a) (Submodule.smul_mem_smul hμ Submodule.mem_top)
  simp only [map_smul] at k1
  rw [← smul_sub] at k1
  rw [← one_smul (𝓞 E) (gam (F.t i (gM a)) - F.t j a), ← h1, add_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem_smul hβ Submodule.mem_top) k1

variable {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}

set_option maxHeartbeats 1000000 in

theorem exists_marking_tri (hU : Formalism.L2.PjFree.IsUnf U) :
    ∃ T : ∀ k, Dw.La →ₗ[𝓞 E] (U.X k).Λ, (∀ k, BijMod l.Mb (T k)) ∧
      ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La), IsLevMove ρ ν gM gA →
      ∀ (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
      FrMove ρ ν (U.un k x) y' → FrBor t (U.un k' x') y' →
      ∃ (gam : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k').Λ) (A : (E →+* ℂ) → ℕ → ℕ → ℂ),
        (∀ u v : (U.X k).Λ,
          Algebra.trace ℚ E (-(U.X k').ξ0 * herm (U.X k').Gm (gam u : Fin r → E) (gam v : Fin r → E)) =
            Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E))) ∧
        (∀ τ i j, j < i → A τ i j = 0) ∧
        (∀ τ, ∀ i < Dw.mult τ, ∀ v : (U.X k).Λ,
          Formalism.L2.PjFree.perFr (U.X k') x'.1 (gam v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) i =
            ∑ j ∈ Finset.range (Dw.mult τ), A τ i j *
              Formalism.L2.PjFree.perFr (U.X k) x.1 (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j) ∧
        ∀ a, gam (T k (gM a)) - T k' a ∈ l.Mb • (⊤ : Submodule (𝓞 E) (U.X k').Λ) := by
  classical
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  refine ⟨fun k => (φ k).toLinearMap ∘ₗ F.t (ik k), fun k => (familyUniformisation_marking_bijectiveModuloLevel F _).comp (bijMod_equiv _ _), ?_⟩
  intro ρ ν gM gA hν k k' x x' y' t hM hB
  obtain ⟨P, hP, p, hPx, hv, -⟩ := hpt k x
  obtain ⟨P', hP', p', hPx', hv', -⟩ := hpt k' x'
  have hu : F.u (ik k) P ≫ ρ = F.u (ik k') P' := by rw [← hPx, ← hPx', ← hB.1]; exact hM.1.symm
  obtain ⟨gam, h, hiso, hh, hex⟩ := exists_isometry_of_sabMap F ν p p' hu
  have hmk := marking_of_levMove F hν p p' hu gam h hh hex
  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hcol : ∀ τ i, h.toLinearMap (Pi.single (e.symm ⟨τ, i⟩) 1) =
      (∑ j, (show ℂ from cf τ i j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ i
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ P' p' _ ((U.un k' x').u τ) _ (hv' τ) (cf τ i)
      (y'.u τ i)).1 (hPx' ▸ hcf3 τ i)
    have d0 := FibreDeriv.isDerivAt0_comp (hv τ i) ν.φ
    simp only [← hex] at d0
    have d2 := (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F _ P' p') h.toLinearMap _ _).1 d0
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P' p'
    rw [hM.2.1] at d1
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  refine ⟨(φ k).symm ≪≫ₗ gam ≪≫ₗ φ k',
    fun τ i j => if hij : i < Dw.mult τ ∧ j < Dw.mult τ then
      Formalism.L2.PjFree.toC (cf τ ⟨j, hij.2⟩ ⟨i, hij.1⟩) else 0, fun u v => ?_, fun τ i j hji => ?_,
    fun τ i hi v => ?_, fun a => ?_⟩
  · obtain ⟨u, rfl⟩ := (φ k).surjective u
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [← hEF, ← hEF, hiso]
  · beta_reduce
    split_ifs with hij
    · exact hcf2 τ _ _ hji
    · rfl
  · obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    have a1 := hP' (gam v) (e.symm ⟨τ, ⟨i, hi⟩⟩)
    rw [Equiv.apply_symm_apply] at a1
    rw [← a1, hh, Finset.sum_range]
    refine (apply_of_cols e h.toLinearMap (fun τ i j => cf τ i j) hcol (P v) τ ⟨i, hi⟩).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [hP, Equiv.apply_symm_apply, dif_pos ⟨hi, j.2⟩]
    rfl
  · have := map_mem_smul_top _ (φ k').toLinearMap (hmk a)
    simpa only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      map_sub] using this

theorem exists_marking_match (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ r)
    (hxi : ∀ k k' (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ‖τ (U.X k').ξ0‖) :
    ∃ T : ∀ k, Dw.La →ₗ[𝓞 E] (U.X k).Λ, (∀ k, BijMod l.Mb (T k)) ∧
      ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La), IsLevMove ρ ν gM gA →
      ∀ (k : U.Comp) (x : (U.X k).dom) (y' : FrPt Xo c (CAt σ)), FrMove ρ ν (U.un k x) y' →
      ∃ (k' : U.Comp) (a : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k') a) (gam : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k').Λ),
        (∀ v : (U.X k).Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) = (gam v : Fin r → E)) ∧
        (∀ u, gam (T k (gM u)) - T k' u ∈ l.Mb • (⊤ : Submodule (𝓞 E) (U.X k').Λ)) ∧
        ∃ t, FrBor t (U.un k' ⟨lact a (castFr h.psi x.1), h.mem_dom x.2⟩) y' := by
  obtain ⟨T, hT, hmv⟩ := exists_marking_tri hU
  refine ⟨T, hT, fun ρ ν gM gA hν k x y' hm => ?_⟩
  obtain ⟨k', x', t, hb⟩ := hU.2.2.1 y'
  obtain ⟨gam, A, htr, hA0, hA, hmk⟩ := hmv ρ ν gM gA hν k k' x x' y' t hm hb
  obtain ⟨a, ε, hε, hξ, hav, hlat, hiso⟩ :=
    GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry E r (U.X k) (U.X k') (hxi k k') gam htr
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hrr, hty, -, hfib, -⟩ := hU
  have hΨ : (U.X k).Ψ = (U.X k').Ψ := Finset.ext fun τ => ((hty k).2 τ).trans ((hty k').2 τ).symm
  have hp : (U.X k).p0 = (U.X k').p0 := (hty k).1.trans (hty k').1.symm
  let e := Equiv.ofBijective _ hbij
  have he : ∀ τ, Formalism.L2.PjFree.relab c σ (e.symm τ) = τ := e.apply_symm_apply
  have m1 : ∀ τ ∈ (U.X k).Ψ, Dw.mult (e.symm τ) = r - (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_pos ((hrt _).1 (by rw [he]; exact ((hty k).2 τ).1 hτ)), (hty k).1]
    omega
  have m2 : ∀ τ ∉ (U.X k).Ψ, Dw.mult (e.symm τ) = (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg (fun h => hτ (((hty k).2 τ).2 (by rw [← he τ]; exact (hrt _).2 h))), (hty k).1]
  have hrel : ∀ τ, ∀ i < Dw.mult (e.symm τ), ∀ v ∈ (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k') x'.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
        ∑ j ∈ Finset.range (Dw.mult (e.symm τ)), A (e.symm τ) i j * Formalism.L2.PjFree.perFr (U.X k) x.1 v τ j :=
    fun τ i hi v hv => by
      have := hA (e.symm τ) i hi ⟨v, hv⟩
      rwa [he, ← hav] at this
  rcases hε with rfl | rfl
  · have h : IsMatch (U.X k) (U.X k') a :=
      ⟨hΨ, hp, by rw [hξ, _root_.one_mul], fun u v => by rw [hiso, _root_.one_mul], hlat⟩
    obtain ⟨b, hbB, hxb, -⟩ := GlobalTheory.PeriodBorel.borel_of_periods E r _ _ a h (fun τ => Dw.mult (e.symm τ)) m1 m2
      x.1 x.2 x'.1 x'.2 (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel
    obtain ⟨t₀, ht₀⟩ := (hfib k' k' ⟨lact a (castFr h.psi x.1), h.mem_dom x.2⟩ x').2
      ⟨1, one_mem _, b, hbB, by rw [GlobalTheory.FrameNorm.UnitFr.lact_one', ← hxb]⟩
    exact ⟨k', a, h, gam, hav, hmk, _, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c _).2.1 _ _ _ _ _ ht₀ hb⟩
  · exact (GlobalTheory.AntiIsom.not_antiIsometry E r _ _ hΨ hp hr a hiso (fun τ => Dw.mult (e.symm τ)) m1 m2 x.1 x.2
      x'.1 x'.2 (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel).elim

end Geo

section Lat

open NumberField Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA

theorem exists_scalars (D : D7) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) :
    ∃ (s α : D.host.E) (m : 𝓞 D.host.E), (∀ a ∈ D.host.AA, ∃ c : 𝓞 D.host.E, (c : D.host.E) = s * a) ∧
      α ∈ D.host.AA ∧ m ∈ I ∧ s * α + (m : D.host.E) = 1 := by
  obtain ⟨s, hs⟩ := IsDedekindDomain.exists_add_spanSingleton_mul_eq (K := D.host.E) (a := (I : FractionalIdeal _ _))
    (b := D.host.AA) (c := 1) FractionalIdeal.coeIdeal_le_one (FractionalIdeal.coeIdeal_ne_zero.2 hI)
    (GlobalTheory.ModelLatticeCheck.AA_ne_zero D)
  have h1 : (1 : D.host.E) ∈ (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) +
      FractionalIdeal.spanSingleton _ s * D.host.AA := by
    rw [hs]; exact FractionalIdeal.one_mem_one _
  obtain ⟨u, hu, w, hw, huw⟩ := (FractionalIdeal.mem_add _ _ _).1 h1
  obtain ⟨m, hm, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hu
  obtain ⟨α, hα, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hw
  refine ⟨s, α, m, fun a ha => ?_, hα, hm, by rw [add_comm]; exact huw⟩
  have h2 : s * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [← hs]
    exact (FractionalIdeal.mem_add _ _ _).2 ⟨0, FractionalIdeal.zero_mem _, s * a,
      FractionalIdeal.mem_singleton_mul.2 ⟨a, ha, rfl⟩, zero_add _⟩
  exact (FractionalIdeal.mem_one_iff _).1 h2

theorem exists_scale (D : D7) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) (r : ℕ) :
    ∃ (s : D.host.E) (f : ∀ Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E), Λ →ₗ[𝓞 D.host.E] lattice₂ D Λ),
      (∀ Λ, BijMod I (f Λ)) ∧ ∀ Λ z, (f Λ z : Fin r → D.host.E) = s • (z : Fin r → D.host.E) := by
  obtain ⟨s, α, m, hs, hα, hm, h1⟩ := exists_scalars D hI
  let f : ∀ Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E), Λ →ₗ[𝓞 D.host.E] lattice₂ D Λ := fun Λ =>
    { toFun := fun z => ⟨s • (z : Fin r → D.host.E), mem_latP.2 fun a ha => by
        obtain ⟨c, hc⟩ := hs a ha
        rw [smul_smul, mul_comm, ← hc]
        exact Λ.smul_mem c z.2⟩
      map_add' := fun z w => Subtype.ext (smul_add _ _ _)
      map_smul' := fun c z => Subtype.ext (smul_comm s c (z : Fin r → D.host.E)) }
  let g : ∀ Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E), lattice₂ D Λ →ₗ[𝓞 D.host.E] Λ := fun Λ =>
    { toFun := fun z => ⟨α • (z : Fin r → D.host.E), mem_latP.1 z.2 α hα⟩
      map_add' := fun z w => Subtype.ext (smul_add _ _ _)
      map_smul' := fun c z => Subtype.ext (smul_comm α c (z : Fin r → D.host.E)) }
  refine ⟨s, f, fun Λ => bijMod_of_inv (f Λ) (g Λ) hm (fun a => Subtype.ext ?_) (fun a => Subtype.ext ?_),
    fun _ _ => rfl⟩
  · change (a : Fin r → D.host.E) = α • s • (a : Fin r → D.host.E) + (m : D.host.E) • (a : Fin r → D.host.E)
    rw [smul_smul, ← add_smul, mul_comm, h1, one_smul]
  · change (a : Fin r → D.host.E) = s • α • (a : Fin r → D.host.E) + (m : D.host.E) • (a : Fin r → D.host.E)
    rw [smul_smul, ← add_smul, h1, one_smul]

def latPMap (D : D7) {r : ℕ} {Λ Λ' : Submodule (𝓞 D.host.E) (Fin r → D.host.E)}
    (A : Matrix (Fin r) (Fin r) D.host.E) (h : ∀ w, w ∈ Λ ↔ A.mulVec w ∈ Λ') :
    lattice₂ D Λ →ₗ[𝓞 D.host.E] lattice₂ D Λ' where
  toFun w := ⟨A.mulVec w, (mem_localLattice_iff_mulVec D A h w).1 w.2⟩
  map_add' z w := Subtype.ext (Matrix.mulVec_add A (z : Fin r → D.host.E) w)
  map_smul' c z := Subtype.ext (Matrix.mulVec_smul A (c : D.host.E) (z : Fin r → D.host.E))

end Lat

end GlobalTheory.ShareOn.OneFrame

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

open GlobalTheory.ShareOn.OneFrame in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.ShareOn.exists_movesAt_readsInv : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∃ ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k, ∀ (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k : (uAt r v i).Comp) (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom), ∃ (k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E) (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a), ReadsInv p r i v ψ γ k k' a ∧ MovesAt p r i v γ k k' a hm x hx := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hp := (h.laws v).p
  have hpin := hp.pins
  have hσ := (r.used v).full.toCore.good_σ₀
  have hpq : 1 ≤ ((r.used v).full.Q.Dw ((i : ℕ) + 1)).p + ((r.used v).full.Q.Dw ((i : ℕ) + 1)).q := by
    rw [(hpin.2.2.2 _ hj).1, (hpin.2.2.2 _ hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.FullLevelAction.actLev_levFull D (r.used v).full.Q _ hpq hpin.2.1.2
  have hU := hp.unf _ hj _ hσ
  obtain ⟨T, hTb, hmv⟩ := exists_marking_match (U := Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hσ hU (hU.1 ▸ hpq)
    (fun k k' τ => (hp.xiAbs _ hj _ hσ k τ).trans (hp.xiAbs _ hj _ hσ k' τ).symm)
  have hI : p.T.Q.l.Mb ≠ ⊥ := fun e => by
    have h1 := natCast_M_mem p.T.Q.l
    rw [e, Ideal.mem_bot, Nat.cast_eq_zero] at h1
    have := p.T.Q.l.three_le
    omega
  obtain ⟨s, f, hf, hfs⟩ := exists_scale D hI D.R.r
  have hb : ∀ k : (uAt r v i).Comp, BijMod p.T.Q.l.Mb (f ((uAt r v i).X k).Λ ∘ₗ T k) := fun k => (hTb k).comp (hf _)
  refine ⟨fun k => (hb k).equiv, fun γ k x hx => ?_⟩
  obtain ⟨ρ, ν, -, hν, hm⟩ := mvPt_spec hL.total γ ((uAt r v i).un k ⟨x, hx⟩)
  obtain ⟨k', a, ha, gam, hav, hmk, t, ht⟩ := hmv ρ ν _ _ hν k ⟨x, hx⟩ _ hm
  refine ⟨k', a, ha, fun w => ⟨(mem_localLattice_iff_mulVec D _ ha.lat _).1 w.2, ?_⟩, ha.mem_dom hx, t, ht⟩
  refine (hb k).reads (hb k') γ (liftLa γ) (liftLa_spec γ) (latPMap D _ ha.lat) (fun u => ?_) w
  have h1 := map_mem_smul_top _ (f ((uAt r v i).X k').Λ) (hmk u)
  have h2 : latPMap D _ ha.lat (f ((uAt r v i).X k).Λ (T k (liftLa γ u))) =
      f ((uAt r v i).X k').Λ (gam (T k (liftLa γ u))) := by
    refine Subtype.ext ?_
    refine (congrArg (Matrix.mulVec _) (hfs _ _)).trans (Eq.trans ?_ (hfs _ _).symm)
    rw [Matrix.mulVec_smul]
    exact congrArg _ (hav _)
  have h3 := (f ((uAt r v i).X k').Λ).map_sub (gam (T k (liftLa γ u))) (T k' u)
  rw [← h2] at h3
  exact h3 ▸ h1

end

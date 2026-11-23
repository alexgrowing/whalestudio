import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitsCOfModEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
import Formalism.LocalToGlobal.Columns.LevGCount
import Formalism.HermitianLattices.FinalMass
import Formalism.HermitianLattices.HermitianLatticesProofs.AutFinite

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
open Formalism.MainNotions Formalism.L2.Col
open scoped TensorProduct

namespace GlobalTheory.Mem.DuInt

theorem idx_eq (g k : ℕ) (hg : g.Prime) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) = StandardLattice.idxColLoc g k ∧ Nat.card (GL (Fin k) (ZMod g)) = g ^ (k * (k - 1) / 2) * n := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  have h1 : Nat.card {A : GL (Fin k) (ZMod g) // StandardLattice.IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} =
      Nat.card (HU (ZMod g) k) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun A => ⟨fun h => ?_, fun h => isUpperUni_of_mem_uniUT le_rfl h⟩)
    have : A ∈ uSet (ZMod g) (fun i j : Fin k => i < j) :=
      ⟨h.2, fun i j hne hij => h.1 i j (lt_of_le_of_ne (not_lt.1 hij) hne.symm)⟩
    rw [← uniUT_full_eq] at this
    exact this
  have h2 := (HU (ZMod g) k).card_mul_index
  have h3 := card_HU (ZMod g) k
  rw [Nat.card_zmod] at h3
  refine ⟨(HU (ZMod g) k).index, Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite, ?_, by rw [← h2, h3]⟩
  unfold StandardLattice.idxColLoc StandardLattice.idxLoc
  rw [h1, ← h2]
  have h4 : (0 : ℝ) < Nat.card (HU (ZMod g) k) := by exact_mod_cast Nat.card_pos
  push_cast
  field_simp

theorem dimV_nat {R : Ranks} (P : HCParam R) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) = StandardLattice.dimV fun i => ((P.u i : ℚ) : ℝ) := by
  have hk : 0 < R.k := by have := R.m_add_three_le_k; omega
  have hanti : StrictAnti P.u := by
    have key : ∀ d : ℕ, ∀ (a : ℕ) (h : a + d + 1 < R.k), P.u ⟨a + d + 1, h⟩ < P.u ⟨a, by omega⟩ := by
      intro d
      induction d with
      | zero => intro a h; exact (P.v_gt_u ⟨a, by omega⟩).trans (P.u_gt_v ⟨a, by omega⟩)
      | succ d ih =>
        intro a h
        exact ((P.v_gt_u ⟨a + d + 1, by omega⟩).trans (P.u_gt_v ⟨a + d + 1, by omega⟩)).trans (ih a (by omega))
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (show a < b from hab)
    exact key d a hb
  choose z hz using P.u_half
  have gen : ∀ (N : ℕ) (_ : 0 < N) (u : Fin N → ℚ) (z : Fin N → ℤ), StrictAnti u → (∀ i, u i = z i + 1 / 2) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) = StandardLattice.dimV fun i => ((u i : ℚ) : ℝ) := by
    intro N hN u z hu hz
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    obtain ⟨c, hc⟩ := Matrix.superFactorial_dvd_vandermonde_det (fun i => - z i)
    have e1 : StandardLattice.vand (fun i => ((u i : ℚ) : ℝ)) = ((Matrix.vandermonde fun i => - z i).det : ℤ) := by
      rw [Matrix.det_vandermonde]
      unfold StandardLattice.vand
      push_cast
      refine Finset.prod_congr rfl fun a _ => Finset.prod_congr (by ext; simp) fun b _ => ?_
      rw [hz a, hz b]
      push_cast
      ring
    have e2 : StandardLattice.facProd (M + 1) = (M.superFactorial : ℕ) := by
      unfold StandardLattice.facProd
      rw [← Nat.prod_range_succ_factorial]
      push_cast
      rfl
    have h3 : (0 : ℝ) < (M.superFactorial : ℕ) := by
      rw [← e2]
      exact Finset.prod_pos fun i _ => by positivity
    have h4 : 0 < StandardLattice.vand (fun i => ((u i : ℚ) : ℝ)) := by
      refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
      have := hu (Finset.mem_filter.1 hb).2
      have : ((u b : ℚ) : ℝ) < u a := by exact_mod_cast this
      linarith
    have e5 : StandardLattice.dimV (fun i => ((u i : ℚ) : ℝ)) = c := by
      unfold StandardLattice.dimV
      rw [e1, e2, hc]
      push_cast
      field_simp
    have h6 : (0 : ℝ) < c := by
      rw [← e5]
      exact div_pos h4 (e2 ▸ h3)
    have h7 : 0 < c := by exact_mod_cast h6
    refine ⟨c.toNat, by omega, ?_⟩
    rw [e5]
    exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) (Int.toNat_of_nonneg h7.le)
  exact gen R.k hk P.u z hanti hz

section Lat

variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

def resHom (N : Submodule (𝓞 E) V) : autLat (E := E) N →* Module.End (𝓞 E) N where
  toFun γ := ((γ.1 : V →ₗ[E] V).restrictScalars (𝓞 E)).restrict fun _ hx => autLat_apply γ.2 hx
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

theorem finrank_red (N : Submodule (𝓞 E) V) (hN : Submodule.IsLattice E N) (w : Ideal (𝓞 E)) [w.IsMaximal] :
    Module.finrank (𝓞 E ⧸ w) ((𝓞 E ⧸ w) ⊗[𝓞 E] N) = Module.finrank E V := by
  have : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hN))
  have : Module.IsTorsionFree (𝓞 E) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 E) E V
  have : Module.Flat (𝓞 E) N := inferInstance
  have hr : Module.finrank (𝓞 E) N = Module.finrank E V := by
    have : IsLocalizedModule (nonZeroDivisors (𝓞 E)) N.subtype := by
      refine ⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩
      · have := isLocalizedModule_id (nonZeroDivisors (𝓞 E)) V E
        exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (LinearMap.id : V →ₗ[𝓞 E] V) s
      · have hy : y ∈ Submodule.span E (N : Set V) := hN.span_eq_top ▸ Submodule.mem_top
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ y hy
        rw [Submodule.span_eq] at ht
        exact ⟨(⟨_, ht⟩, t), rfl⟩
    rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 E)) N.subtype le_rfl,
      IsFractionRing.finrank_right_eq (𝓞 E) E V]
  letI : Field (𝓞 E ⧸ w) := Ideal.Quotient.field _
  have h1 := Module.rankAtStalk_baseChange (R := 𝓞 E) (M := N) (S := 𝓞 E ⧸ w) ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank, hr] at h1
  exact h1

theorem card_dvd_card_GL (N : Submodule (𝓞 E) V) (hN : Submodule.IsLattice E N) (w : Ideal (𝓞 E)) [hw : w.IsMaximal]
    {g : ℕ} (hg : g.Prime) (hgw : (g : 𝓞 E) ∈ w) (hn : Ideal.absNorm w = g)
    (hbig : Module.finrank ℚ E * Module.finrank E V + 1 < g) (Γ : Subgroup (V ≃ₗ[E] V)) [Finite Γ] (hΓ : Γ ≤ autLat N) :
    Nat.card Γ ∣ Nat.card (GL (Fin (Module.finrank E V)) (ZMod g)) := by
  have : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hN))
  have : Module.IsTorsionFree (𝓞 E) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 E) E V
  letI : Field (𝓞 E ⧸ w) := Ideal.Quotient.field _
  have hc : Nat.card (𝓞 E ⧸ w) = g := by rw [← hn, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ w) := Nat.finite_of_card_ne_zero (hc ▸ hg.ne_zero)
  letI : Fintype (𝓞 E ⧸ w) := Fintype.ofFinite _
  haveI : NeZero g := ⟨hg.ne_zero⟩
  let e : ZMod g ≃+* 𝓞 E ⧸ w := ZMod.ringEquivOfPrime _ hg (by rw [← hc, Nat.card_eq_fintype_card])
  let b := Module.finBasisOfFinrankEq (𝓞 E ⧸ w) ((𝓞 E ⧸ w) ⊗[𝓞 E] N) (finrank_red N hN w)
  let φ : Module.End (𝓞 E ⧸ w) ((𝓞 E ⧸ w) ⊗[𝓞 E] N) ≃*
      Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) (ZMod g) :=
    (LinearMap.toMatrixAlgEquiv b).toMulEquiv.trans e.symm.mapMatrix.toMulEquiv
  let ρ : Γ →* Module.End (𝓞 E ⧸ w) ((𝓞 E ⧸ w) ⊗[𝓞 E] N) :=
    ((Module.End.baseChangeHom (𝓞 E) (𝓞 E ⧸ w) N : _ →* _).comp (resHom N)).comp (Subgroup.inclusion hΓ)
  refine Subgroup.card_dvd_of_injective (φ.toMonoidHom.comp ρ).toHomUnits ?_
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have h1 : ρ γ = 1 := φ.injective (by rw [map_one]; exact congrArg Units.val hγ)
  refine Subtype.ext (stab0 hw.ne_top hN.fg hN.span_eq_top hg hgw hbig ⟨hΓ γ.2, 1, fun x hx => ?_⟩
    (Submonoid.isOfFinOrder_coe.mpr (isOfFinOrder_of_finite γ)))
  have h2 : (1 : 𝓞 E ⧸ w) ⊗ₜ[𝓞 E] (resHom N ⟨γ.1, hΓ γ.2⟩ ⟨x, hx⟩) = (1 : 𝓞 E ⧸ w) ⊗ₜ[𝓞 E] (⟨x, hx⟩ : N) :=
    LinearMap.congr_fun h1 ((1 : 𝓞 E ⧸ w) ⊗ₜ[𝓞 E] (⟨x, hx⟩ : N))
  have h3 := congrArg (TensorProduct.quotTensorEquivQuotSMul N w) h2
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
    Submodule.Quotient.eq] at h3
  have h4 := Submodule.mem_map_of_mem (f := N.subtype) h3
  rw [Submodule.map_smul'', Submodule.map_subtype_top] at h4
  rw [pow_one]
  exact h4

theorem mass_mul_idx [StarRing E] (h : V →ₗ⋆[E] V →ₗ[E] E) (hs : h.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ E (h x x))
    (L : Submodule (𝓞 E) V) (hL : Submodule.IsLattice E L) (w : Ideal (𝓞 E)) [hw : w.IsMaximal]
    {g : ℕ} (hg : g.Prime) (hgw : (g : 𝓞 E) ∈ w) (hn : Ideal.absNorm w = g)
    (hbig : Module.finrank ℚ E * Module.finrank E V + 1 < g) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) = Formalism.HermitianLatticesTheory.mass h L * StandardLattice.idxColLoc g (Module.finrank E V) := by
  obtain ⟨⟨s, hs₀⟩, hm, hp⟩ := Formalism.HermitianLatticesTheory.final_massBasic E V h hs hpos L hL
  obtain ⟨m, hm0, hm1, hm2⟩ := idx_eq g (Module.finrank E V) hg
  have key : ∀ M ∈ s, ((m / Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) = ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ * m := by
    intro M hM
    have hMl := (hs₀.1 M hM).1
    have hfin := Formalism.HermitianLatticesTheory.autFinite E V h hs hpos M hMl
    have : Finite (Formalism.HermitianLatticesTheory.isom h ⊓ autLat M : Subgroup (V ≃ₗ[E] V)) := hfin.to_subtype
    have e : Nat.card (Formalism.ThetaLiftIndependence.autL h M) = Nat.card (Formalism.HermitianLatticesTheory.isom h ⊓ autLat M : Subgroup (V ≃ₗ[E] V)) := rfl
    have h1 := card_dvd_card_GL M hMl w hg hgw hn hbig (Formalism.HermitianLatticesTheory.isom h ⊓ autLat M) inf_le_right
    have h2 : (Nat.card (Formalism.HermitianLatticesTheory.isom h ⊓ autLat M : Subgroup (V ≃ₗ[E] V))).Coprime g := by
      rw [Nat.coprime_comm, hg.coprime_iff_not_dvd]
      intro hd
      have := prime_le_of_dvd_card _ hg hd
      omega
    rw [hm2] at h1
    have h3 := (h2.pow_right _).dvd_of_dvd_mul_left h1
    rw [e, Nat.cast_div h3 (by exact_mod_cast Nat.card_pos.ne'), div_eq_inv_mul]
  have e : ((∑ M ∈ s, m / Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) =
      Formalism.HermitianLatticesTheory.mass h L * StandardLattice.idxColLoc g (Module.finrank E V) := by
    rw [hm s hs₀, ← hm1, Finset.sum_mul, Nat.cast_sum]
    exact Finset.sum_congr rfl key
  refine ⟨_, ?_, e⟩
  have : (0 : ℝ) < Formalism.HermitianLatticesTheory.mass h L * StandardLattice.idxColLoc g (Module.finrank E V) :=
    mul_pos hp (by rw [← hm1]; exact_mod_cast hm0)
  rw [← e] at this
  exact_mod_cast this

end Lat

theorem duStarOf_nat : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (hc : Tau R → HCParam R), (∀ i, H.g i % (H.QS * H.q * H.d) = 1) → (∀ i, 2 * R.f * R.k < H.g i - 1) → ∃ n : ℕ, 0 < n ∧ (n : ℝ) = duStarOf H hc := by
  intro R H hc hmod hbig
  letI := H.cmStar
  have hg := H.g_prime 0
  have hdeg : Module.finrank ℚ H.E = 4 * R.ord := H.finrank_cmField
  have hdeg' : Module.finrank ℚ H.E = 2 * R.f := by
    rw [hdeg, show R.f = 2 * R.ord from rfl]; ring
  have hs : SplitsC H.E (H.g 0) := by
    refine splitsC_of_modEq_one R H _ hg ?_
    have := Nat.mod_modEq (H.g 0) (H.QS * H.q * H.d)
    rw [hmod 0] at this
    exact this.symm
  obtain ⟨v, hv⟩ : {v : HeightOneSpectrum (𝓞 H.E) | ((H.g 0 : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [show Set.ncard _ = _ from hs]; exact Module.finrank_pos.ne')
  have hn := (splitsC_main R H _ hg hs v hv).1
  haveI := v.isMaximal
  haveI := H.isCMField_hostE
  have hconj : ∀ (φ : H.E →+* ℂ) (x : H.E), φ (star x) = starRingEnd ℂ (φ x) := fun φ x =>
    IsCMField.complexEmbedding_complexConj H.E φ x
  have hsym : (StandardLattice.stdForm H.E R.k).IsSymm := by
    refine LinearMap.isSymm_def.mpr fun x y => ?_
    show starRingEnd H.E (∑ i, star (x i) * y i) = ∑ i, star (y i) * x i
    simp only [map_sum, starRingEnd_apply, star_mul, star_star]
  have hpos : ∀ x : Fin R.k → H.E, x ≠ 0 → 0 < Algebra.trace ℚ H.E (StandardLattice.stdForm H.E R.k x x) := fun x hx => by
    have := hStd_trace_pos hconj x hx
    rw [hStd_apply] at this
    exact this
  have hL : Submodule.IsLattice H.E (StandardLattice.stdLat H.E R.k) := by
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [StandardLattice.stdLat, Submodule.span_span_of_tower, ← (Pi.basisFun H.E (Fin R.k)).span_eq]
    congr 2
    funext i
    simp
  obtain ⟨n₁, p₁, e₁⟩ := mass_mul_idx _ hsym hpos _ hL v.asIdeal hg hv hn
    (by rw [Module.finrank_fin_fun, hdeg']; have := hbig 0; omega)
  rw [Module.finrank_fin_fun] at e₁
  obtain ⟨n₂, p₂, e₂, -⟩ := idx_eq (H.g 0) R.k hg
  obtain ⟨n₃, p₃, e₃, -⟩ := idx_eq (H.g 1) R.k (H.g_prime 1)
  choose d pd ed using fun τ => dimV_nat (hc τ)
  obtain ⟨f, hf⟩ : ∃ f, R.f = f + 1 := ⟨R.f - 1, by
    have : 0 < R.f := Nat.mul_pos two_pos R.ord_pos
    omega⟩
  refine ⟨n₁ * n₂ ^ f * n₃ ^ R.f * ∏ τ, d τ, ?_, ?_⟩
  · have := Finset.prod_pos (s := Finset.univ) fun τ _ => pd τ
    positivity
  · unfold duStarOf
    push_cast
    simp only [ed]
    rw [e₁, e₂, e₃, hf]
    ring

end GlobalTheory.Mem.DuInt

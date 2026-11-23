import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.Test

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem existsUnique_isKForm (D : Datum H) (ε : ℤˣ) : ∃! h, IsKForm D ε h := by
  refine ⟨fun x y => ((((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : OK H) +
    (((ε : ℤ) * D.EF x y : ℤ) : OK H) * wK H), ?_, ?_⟩
  · intro x y
    have hw : ((wK H : OK H) : 𝓞 E) = H.w0 := rfl
    push_cast [hw]
    rfl
  · intro h' hh'
    funext x y
    apply Subtype.ext
    have hw : ((wK H : OK H) : 𝓞 E) = H.w0 := rfl
    rw [hh' x y]
    push_cast [hw]
    rfl

theorem cm_generator_sq_quadratic_eq (H : Host E) : H.w0 * H.w0 = H.w0 - (((H.d + 1) / 4 : ℕ) : 𝓞 E) := by
  obtain ⟨k, hk⟩ : ∃ k, H.d + 1 = 4 * k := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  have hk' : (H.d + 1) / 4 = k := by omega
  rw [hk']
  have hd : (H.d : 𝓞 E) = 4 * k - 1 := by
    have e : ((H.d + 1 : ℕ) : 𝓞 E) = ((4 * k : ℕ) : 𝓞 E) := by rw [hk]
    push_cast at e
    linear_combination e
  have h4 : (4 : 𝓞 E) * (H.w0 * H.w0 - (H.w0 - k)) = 0 := by
    linear_combination (2 * H.w0 - 1 + H.rt) * H.two_weight_eq_one_add_root + H.rt_sq - hd
  have h40 : (4 : 𝓞 E) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h h40
  · linear_combination h

theorem bar_rt (H : Host E) : H.bar H.rt = -H.rt := by
  have hsq : (H.bar H.rt - H.rt) * (H.bar H.rt + H.rt) = 0 := by
    have e : H.bar (H.rt ^ 2) = H.bar (-(H.d : 𝓞 E)) := by rw [H.rt_sq]
    rw [map_pow, map_neg, map_natCast, ← H.rt_sq] at e
    linear_combination e
  rcases mul_eq_zero.mp hsq with h | h
  · exfalso
    have hfix : H.bar H.rt = H.rt := sub_eq_zero.mp h
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hc := H.bar_eq H.rt
    rw [hfix] at hc
    have hconj : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
      rw [← NumberField.IsCMField.complexEmbedding_complexConj, ← hc]
    have hsqC : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
      rw [← map_pow]
      have e : ((H.rt ^ 2 : 𝓞 E) : E) = ((-(H.d : 𝓞 E) : 𝓞 E) : E) := by rw [H.rt_sq]
      push_cast at e
      rw [e]
      simp
    have him : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.mp hconj
    have hre := congrArg Complex.re hsqC
    simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re, Complex.natCast_re] at hre
    have hd : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
  · linear_combination h

theorem cmHost_bar_halfIntegerGenerator (H : Host E) : H.bar H.w0 = 1 - H.w0 := by
  have h := congrArg H.bar H.two_weight_eq_one_add_root
  simp only [map_mul, map_add, map_one, map_ofNat, bar_rt] at h
  have h2 : (2 : 𝓞 E) * (H.bar H.w0 - (1 - H.w0)) = 0 := by
    linear_combination h + H.two_weight_eq_one_add_root
  have h20 : (2 : 𝓞 E) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact absurd h' h20
  · linear_combination h'

variable {D : Datum H} {ε : ℤˣ} {h : D.La → D.La → OK H}

theorem isHermitianForm_linear_left (hh : IsKForm D ε h) (x y : D.La) : h (H.w0 • x) y = wK H * h x y := by
  apply Subtype.ext
  have hw : ((wK H : OK H) : 𝓞 E) = H.w0 := rfl
  have hw2 := cm_generator_sq_quadratic_eq H
  generalize (H.d + 1) / 4 = c at hw2
  have e1 : H.w0 • H.w0 • x = H.w0 • x - c • x := by
    rw [smul_smul, hw2, sub_smul, Nat.cast_smul_eq_nsmul]
  rw [Subalgebra.coe_mul, hh, hh, hw, e1]
  simp only [map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul]
  push_cast
  linear_combination (-(((ε : ℤ) : 𝓞 E) * (D.EF x y : 𝓞 E))) * hw2

theorem ef_swap (D : Datum H) (x y : D.La) : D.EF y x = -D.EF x y := by
  have e := D.alt (x + y)
  simp only [map_add, LinearMap.add_apply, D.alt x, D.alt y] at e
  linarith

theorem isKForm_herm (hh : IsKForm D ε h) (x y : D.La) : (h y x : 𝓞 E) = H.bar (h x y) := by
  have a1 : D.EF x (H.w0 • y) = D.EF x y - D.EF (H.w0 • x) y := by
    have e := D.adj (1 - H.w0) x y
    simp only [map_sub, map_one, cmHost_bar_halfIntegerGenerator, sub_sub_cancel, sub_smul, one_smul, LinearMap.sub_apply] at e
    exact e.symm
  rw [hh, hh, ef_swap D x y, ef_swap D x (H.w0 • y), a1]
  simp only [map_add, map_mul, map_intCast, cmHost_bar_halfIntegerGenerator]
  push_cast
  ring

theorem isKForm_self (hh : IsKForm D ε h) (x : D.La) :
    (h x x : 𝓞 E) = (((ε : ℤ) * D.EF (H.w0 • x) x : ℤ) : 𝓞 E) := by
  rw [hh, D.alt x]
  simp

theorem isKForm_adj (hh : IsKForm D ε h) (s : 𝓞 E) (x y : D.La) : h (s • x) y = h x (H.bar s • y) := by
  apply Subtype.ext
  rw [hh, hh, smul_comm H.w0 s x, D.adj s (H.w0 • x) y, D.adj s x y]

variable {K : Type} [Field K] [NumberField K]

theorem nonempty_genFib (hB : Out.PolBaseChangeSt) (P : Out.PolAV (Sp (𝓞 K))) : Nonempty (GenFib P) := by
  obtain ⟨P', φ, hg, hpb, hL⟩ := GlobalTheory.PureType.exists_baseChange hB (spMap (algebraMap (𝓞 K) K)) P
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis P'.A P'.smoothDim
  exact ⟨⟨P', φ, ⟨hg, hpb, hL.symm⟩, v, hv⟩⟩

theorem existsUnique_isCoord {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) {u : epsR (𝓞 K) ⟶ P.A} (hu : IsTangent u) :
    ∃! c, F.IsCoord u c := by
  unfold GenFib.IsCoord
  have hfib : F.P₀.g = P.g ∧ IsGrpPullback F.P₀.A P.A (spMap (algebraMap (𝓞 K) K)) F.φ ∧
      LBIso (P.L.pull F.φ) F.P₀.L := F.fib
  obtain ⟨-, hpb, -⟩ := hfib
  have hpb' : IsPullback F.φ F.P₀.A.hom P.A.hom (spMap (algebraMap (𝓞 K) K)) := hpb.1
  obtain ⟨v', hv', hvo⟩ := GlobalTheory.PureType.exists_tangent_over (algebraMap (𝓞 K) K) hpb hu
  have huniq : ∀ w : epsR K ⟶ F.P₀.A, IsVecOver (algebraMap (𝓞 K) K) F.φ u w → w = v' := by
    intro w hw
    apply Over.OverMorphism.ext
    apply hpb'.hom_ext
    · exact Eq.trans hw hvo.symm
    · rw [Over.w w, Over.w v']
  have hb : (∀ i, IsTangent (F.v i)) ∧ ∀ w, IsTangent w → ∃! c, IsLieComb c F.v w := F.basis
  obtain ⟨c, hc, hcu⟩ := hb.2 v' hv'
  refine ⟨c, ⟨hu, v', hvo, hc⟩, ?_⟩
  rintro c' ⟨-, w, hw, hc'⟩
  rw [huniq w hw] at hc'
  exact hcu c' hc'

theorem eigLat_le {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) {O : Type} [CommRing O] (act : OAct O P.A)
    (τ : O →+* 𝓞 K) : F.eigLat act τ ≤ F.lieLat := by
  unfold GenFib.eigLat GenFib.lieLat
  apply Submodule.span_mono
  rintro c ⟨u, hu, -⟩
  exact ⟨u, hu⟩

theorem isDiffOf_id {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) : F.IsDiffOf F (𝟙 _) LinearMap.id := by
  unfold GenFib.IsDiffOf
  intro u c hc
  simpa only [Category.comp_id, LinearMap.id_apply] using hc

theorem exists_genFib_dim_one (hB : Out.PolBaseChangeSt) (hC : CMCurve) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (P : Out.PolAV (Sp (𝓞 M))) (F : GenFib P), F.P₀.g = 1 := by
  have hdeg : (Polynomial.X ^ 2 + Polynomial.C (7 : ℚ)).natDegree = 2 := by compute_degree!
  have hirr : Irreducible (Polynomial.X ^ 2 + Polynomial.C (7 : ℚ)) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]; decide
    · intro x hx
      simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C] at hx
      nlinarith [sq_nonneg x]
  have : Fact (Irreducible (Polynomial.X ^ 2 + Polynomial.C (7 : ℚ))) := ⟨hirr⟩
  have hne : (Polynomial.X ^ 2 + Polynomial.C (7 : ℚ)) ≠ 0 := hirr.ne_zero
  have : FiniteDimensional ℚ (AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C (7 : ℚ))) :=
    (AdjoinRoot.powerBasis hne).finite
  have : CharZero (AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C (7 : ℚ))) :=
    charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  have : NumberField (AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C (7 : ℚ))) := ⟨⟩
  have hfin : Module.finrank ℚ (AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C (7 : ℚ))) = 2 := by
    rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have hroot : AdjoinRoot.root (Polynomial.X ^ 2 + Polynomial.C (7 : ℚ)) ^ 2 =
      -((7 : ℕ) : AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C (7 : ℚ))) := by
    have h0 := AdjoinRoot.eval₂_root (Polynomial.X ^ 2 + Polynomial.C (7 : ℚ))
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_ofNat,
      map_ofNat] at h0
    push_cast
    linear_combination h0
  have hsq : Squarefree 7 := (Nat.prime_iff.mp (by norm_num)).squarefree
  obtain ⟨M, hM, -, P, -, -, hg, -⟩ := hC 7 (by norm_num) hsq (by norm_num)
    (AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C (7 : ℚ))) hfin ⟨_, hroot⟩
  obtain ⟨F⟩ := nonempty_genFib hB P
  have hfib : F.P₀.g = P.g ∧ IsGrpPullback F.P₀.A P.A (spMap (algebraMap (𝓞 M) M)) F.φ ∧
      LBIso (P.L.pull F.φ) F.P₀.L := F.fib
  exact ⟨M, hM, P, F, hfib.1.trans hg⟩

theorem exists_root_of_splits (H : Host E) (h : Splits E K) : ∃ ρ : 𝓞 K, ρ ^ 2 = -(H.d : 𝓞 K) := by
  have h' : Nat.card (𝓞 E →+* 𝓞 K) = Module.finrank ℚ E := h
  have hpos : 0 < Nat.card (𝓞 E →+* 𝓞 K) := by
    rw [h']
    exact Module.finrank_pos
  obtain ⟨τ⟩ := (Nat.card_pos_iff.mp hpos).1
  exact ⟨τ H.rt, by rw [← map_pow, H.rt_sq, map_neg, map_natCast]⟩

def objOfPure {ρ : 𝓞 K} (σ₁ : K →+* ℂ) (hs : Splits E K) (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) (A : Bool → PAT H (Sp (𝓞 K)))
    (h₁ : HasType H (A true).t.act ρ 1 0) (h₂ : HasType H (A false).t.act ρ 0 1) : CMObj H K ρ σ₁ 1 0 where
  split := hs
  ρ_sq := hρ
  A := A
  B := A true
  typeP := h₁
  typeM := h₂
  typeB := h₁
  hh _ := 1
  φ j := match j with
    | .inl _ => 𝟙 _
    | .inr i => i.elim0
  lin j := match j with
    | .inl _ => Serre.IsLinearHom.id _
    | .inr i => i.elim0
  onto y := ⟨fun j => match j with
    | .inl _ => y
    | .inr i => i.elim0, by
      show y = (y ≫ 𝟙 _) * 1
      simp⟩
  weil j := match j with
    | .inl _ => fun n x y c _ _ _ => by rw [OAct.one]; rfl
    | .inr i => i.elim0

theorem hasType_neg {ρ : 𝓞 K} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) {G : Over (Sp (𝓞 K))} [GrpObj G] {act : OAct (𝓞 E) G}
    {p q : ℕ} (h : HasType H act ρ p q) : HasType H act (-ρ) q p := by
  intro k _ _ β hβ τ
  obtain ⟨h1, h2⟩ := h k β hβ τ
  have e1 : τ H.rt ^ 2 = -(H.d : k) := by rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have e2 : β ρ ^ 2 = -(H.d : k) := by rw [← map_pow, hρ, map_neg, map_natCast]
  have hτ : (τ H.rt - β ρ) * (τ H.rt + β ρ) = 0 := by linear_combination e1 - e2
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    have hd0 : ((H.d : ℕ) : 𝓞 K) = 0 := by
      have e := hρ
      rw [zero_pow two_ne_zero] at e
      exact neg_eq_zero.mp e.symm
    exact H.d_prime.ne_zero (by exact_mod_cast hd0)
  have h2k : (2 : k) ≠ 0 := by
    intro h0
    have e : β 2 = β 0 := by rw [map_ofNat, h0, map_zero]
    have := hβ e
    norm_num at this
  have hβρ : β ρ ≠ 0 := by
    intro h0
    exact hρ0 (hβ (h0.trans (map_zero β).symm))
  have hne : β ρ ≠ -β ρ := by
    intro h0
    have e : (2 : k) * β ρ = 0 := by linear_combination h0
    rcases mul_eq_zero.mp e with e' | e'
    · exact h2k e'
    · exact hβρ e'
  constructor
  · intro hneg
    rw [map_neg] at hneg
    apply h2
    intro heq
    rw [heq] at hneg
    exact hne hneg
  · intro hne'
    apply h1
    rcases mul_eq_zero.mp hτ with h0 | h0
    · exact sub_eq_zero.mp h0
    · exfalso
      apply hne'
      rw [map_neg]
      exact eq_neg_of_add_eq_zero_left h0

end GlobalTheory.CM.Test
end

import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TauInvStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TyFact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsInvertibleHeckeFunctionAtFinitePlaces
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfAdm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.IwInvT
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PConvSupp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwahoriRegularSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeedOrbKVanish
import Development.AutomorphicArithmetic.IwahoriCommensurability.IwahoriDoubleCosetTorusMulOfStrictAnti
import Development.AutomorphicArithmetic.IwahoriCommensurability.IsCommensuratedIwahoriSubgroupGlFin
import Development.AutomorphicArithmetic.IwahoriCommensurability.CharpolySmulSeparable
import Development.AutomorphicArithmetic.IwahoriCommensurability.ExistsLevelSubgroupCentralScalarOfPos
import Development.AutomorphicArithmetic.IwahoriCommensurability.ExistsPrimePowScalarIntegralOfGoodPrime

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj GLw)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open Formalism.UG (Hecke conv dosetInd IsCommensurated)
open scoped Classical

namespace UpperTheory.Gal.Spc

section Abstract

variable {X : Type} [Group X]

private def trl (z : X) (f : X → ℂ) : X → ℂ := fun g => f (z * g)

private theorem trl_mem {K : Subgroup X} {z : X} (hz : ∀ g, z * g = g * z) {f : X → ℂ} (hf : f ∈ Hecke ℂ K) :
    trl z f ∈ Hecke ℂ K := by
  obtain ⟨hb, S, hS⟩ := hf
  refine ⟨fun a b g => ?_, S.image (z⁻¹ * ·), fun g hg => ?_⟩
  · show f (z * (a * g * b)) = f (z * g)
    rw [← hb a b (z * g), ← mul_assoc, ← mul_assoc, hz a, mul_assoc (a : X) z g]
  · obtain ⟨s, hs, a, b, e⟩ := hS _ hg
    refine ⟨z⁻¹ * s, Finset.mem_image_of_mem _ hs, a, b, ?_⟩
    have h1 : (a : X) * z⁻¹ = z⁻¹ * a := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hz a, inv_mul_cancel_left]
    rw [← mul_assoc, h1, mul_assoc z⁻¹, mul_assoc z⁻¹, ← e, inv_mul_cancel_left]

private theorem conv_trl_right (K : Subgroup X) {z : X} (hz : ∀ g, z * g = g * z) (f f' : X → ℂ) :
    conv K f (trl z f') = trl z (conv K f f') := by
  funext g
  unfold conv trl
  refine finsum_congr fun x => ?_
  rw [← mul_assoc, hz, mul_assoc]

private theorem conv_trl_left {K : Subgroup X} (z : X) {f f' : X → ℂ} (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K) :
    conv K (trl z f) f' = trl z (conv K f f') := by
  funext g
  unfold conv trl
  beta_reduce
  rw [← finsum_comp_equiv (MulAction.toPerm z : X ⧸ K ≃ X ⧸ K) (f := fun x : X ⧸ K => f x.out * f' (x.out⁻¹ * (z * g)))]
  refine finsum_congr fun y => ?_
  have hy : (MulAction.toPerm z : X ⧸ K ≃ X ⧸ K) y = (QuotientGroup.mk (z * y.out) : X ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' y]
    rfl
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K (z * y.out)
  simp only [hy, hh]
  congr 1
  · simpa using (hf.1 1 h (z * y.out)).symm
  · rw [← hf'.1 h⁻¹ 1 (y.out⁻¹ * g)]
    congr 1
    simp only [Subgroup.coe_inv, OneMemClass.coe_one]
    group

private theorem comm_span {K : Subgroup X} (hK : IsCommensurated K) {u : X → ℂ} (hu : u ∈ Hecke ℂ K) {s : Set (X → ℂ)}
    (hs : ∀ f ∈ s, f ∈ Hecke ℂ K ∧ conv K u f = conv K f u) :
    ∀ f ∈ Submodule.span ℂ s, f ∈ Hecke ℂ K ∧ conv K u f = conv K f u := by
  have fin : ∀ a ∈ Hecke ℂ K, ∀ b : X ⧸ K → ℂ, (Function.support fun x : X ⧸ K => a x.out * b x).Finite := fun a ha b =>
    (Formalism.UG.P.finite_support_cosets hK ha.2).subset fun x hx => left_ne_zero_of_mul hx
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f h => exact hs f h
  | zero => exact ⟨zero_mem _, by funext g; simp [conv]⟩
  | add f f' _ _ h h' =>
    refine ⟨add_mem h.1 h'.1, funext fun g => ?_⟩
    have e := congrFun h.2 g
    have e' := congrFun h'.2 g
    unfold conv at e e' ⊢
    simp only [Pi.add_apply, mul_add, add_mul]
    rw [finsum_add_distrib (fin u hu _) (fin u hu _), finsum_add_distrib (fin f h.1 _) (fin f' h'.1 _), e, e']
  | smul c f _ h =>
    refine ⟨Submodule.smul_mem _ c h.1, funext fun g => ?_⟩
    have e := congrFun h.2 g
    unfold conv at e ⊢
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm _ c]
    rw [← mul_finsum, ← mul_finsum, e]

private theorem tf_supp {M : Type} [Group M] (T : TyLev X M) {h g : X} (e : T.tf h g ≠ 0) :
    ∃ a ∈ T.K, ∃ b ∈ T.K, g = a * h * b := by
  refine DoubleCoset.mem_doubleCoset.1 ?_
  by_contra hn
  apply e
  simp [TyLev.tf, dosetInd, Set.indicator_of_notMem hn]

end Abstract

private theorem locT (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    ∃ t : GL (Fin n) k,
      (∃ φ ∈ Hecke ℂ (GlobalTheory.SmGL.iwahori k (Fin n)), conv (GlobalTheory.SmGL.iwahori k (Fin n)) φ (dosetInd ℂ (GlobalTheory.SmGL.iwahori k (Fin n)) t) =
        dosetInd ℂ (GlobalTheory.SmGL.iwahori k (Fin n)) 1) ∧
      (∀ m : ℕ, ∀ a ∈ DoubleCoset.doubleCoset t (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n)),
        ∀ b ∈ DoubleCoset.doubleCoset (t ^ m) (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n)),
        a * b ∈ DoubleCoset.doubleCoset (t ^ (m + 1)) (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n))) ∧
      ∀ m : ℕ, 1 ≤ m →
        ∀ y ∈ DoubleCoset.doubleCoset (t ^ m) (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n)),
          y.val.charpoly.Separable := by
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (ValuativeRel.uniformizer k)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact ValuativeRel.uniformizer_ne_zero hx.symm
  have hν : StrictAnti fun i : Fin n => -(i : ℤ) := fun i j hij => by
    have : (i : ℕ) < j := hij
    show -((j : ℕ) : ℤ) < -((i : ℕ) : ℤ)
    omega
  refine ⟨_, CertificateRingHomMap.iwInvT k n (Units.mk0 x hx0) hx _ hν.antitone, UpperTheory.iwahori_doubleCoset_torus_mul_of_strictAnti k n (Units.mk0 x hx0) hx _ hν, fun m hm y hy => ?_⟩
  rw [GlobalTheory.TorusElementPower.torusElt_pow_eq] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hy
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  exact (GlobalTheory.IwahoriRegular.regular_split k n (Units.mk0 x hx0) hx _
    (fun i j hij => mul_lt_mul_of_pos_left (hν hij) hm') a ha b hb).1

private theorem integ_mul {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {a b : G.GAf}
    (ha : Integ L a) (hb : Integ L b) : Integ L (a * b) := fun v hv => by
  rw [map_mul, Module.End.mul_apply]
  exact ha _ (hb v hv)

private theorem scal_comm {k : Type} [Field k] {n : ℕ} {s : GL (Fin n) k} {a : k} (hs : s.val = a • (1 : Matrix (Fin n) (Fin n) k))
    (y : GL (Fin n) k) : Commute s y :=
  Units.ext (by rw [Units.val_mul, Units.val_mul, hs, smul_mul_assoc, mul_smul_comm, one_mul, mul_one])

private theorem scal_sep {k : Type} [Field k] {n : ℕ} {s : GL (Fin n) k} {a : k} (ha : a ≠ 0)
    (hs : s.val = a • (1 : Matrix (Fin n) (Fin n) k)) (m : ℕ) (y : GL (Fin n) k) (h : (s ^ m * y).val.charpoly.Separable) :
    y.val.charpoly.Separable := by
  have := UpperTheory.charpoly_smul_separable k n (a ^ m)⁻¹ (inv_ne_zero (pow_ne_zero m ha)) _ h
  rwa [Units.val_mul, Units.val_pow_eq_pow_val, hs, _root_.smul_pow, one_pow, smul_mul_assoc, one_mul, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero m ha), one_smul] at this

private theorem cen_ex {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
    (F : Frame S) (c : ℕ) (hc : 0 < c) : ∃ d : GUf E n, (∀ g, F.j d * g = g * F.j d) ∧
      (∀ w : Plc E, (comp w d).val = (c : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ∧
      ∀ v, S.L.actG (F.j d) v = c • v := by
  first
    | exact UpperTheory.exists_levelSubgroup_central_scalar_of_pos E A n p S F c hc
    | (obtain ⟨y, -, -, h1, -, h2, h3⟩ := UpperTheory.exists_levelSubgroup_central_scalar_of_pos E A n p S F c hc; exact ⟨_, h2, h1, h3⟩)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem auxFn : ExistsIdempotentHeckeOperatorWithRegularSupport := by
  intro E _ _ _ A n p _ S F x U w₀ Up V hn hsc hgen hoff hq r W hA N hrN hst L hw Ty hTy
  obtain ⟨hF, -, c, hc, -, hcK⟩ := tyFact E A n p S F x U w₀ Up V hn hsc hgen hoff hq r W hA N hrN hst L hw Ty hTy
  choose t hti htm hts using fun w : Spl E p => locT (w.1.adicCompletion E) n
  obtain ⟨τ, hτ, hτ0, hτw, hcm, u', hu', hu'τ⟩ := exists_invertible_hecke_function_at_finite_places _ _ Ty (Spl E p) (fun w => GLw n w.1) L (fun w => Iw n w.1) t W hF
    fun w _ => ⟨UpperTheory.isCommensurated_iwahoriSubgroup_gl_fin _ n, hti w⟩
  obtain ⟨g₀, hg₀, hg₀u⟩ : ∃ g₀ : GUf E n, F.j g₀ = τ⁻¹ ∧ ∀ u : Plc E, (r : 𝓞 E) ∉ u.asIdeal → comp u g₀ = 1 := by
    have hτ' := inv_mem hτ
    generalize τ⁻¹ = σ at hτ'
    haveI : Fact r.Prime := ⟨hA.prime⟩
    induction hτ' using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨w, hwW, rfl⟩ := hy
      exact ⟨CertificateRingHomMap.loc w.2.1 (t w), ((hTy.fac w).2 _).symm, fun u hu =>
        CertificateRingHomMap.comp_loc_of_apart w.2.1 (Ne.symm (apart_of_not_mem hu (hA.half.above w hwW))) _⟩
    | one => exact ⟨1, map_one _, fun _ _ => map_one _⟩
    | mul a b _ _ ha hb =>
      obtain ⟨a', rfl, ha⟩ := ha
      obtain ⟨b', rfl, hb⟩ := hb
      exact ⟨a' * b', map_mul _ _ _, fun u hu => by rw [map_mul, ha u hu, hb u hu, one_mul]⟩
    | inv a _ ha =>
      obtain ⟨a', rfl, ha⟩ := ha
      exact ⟨a'⁻¹, map_inv _ _, fun u hu => by rw [map_inv, ha u hu, inv_one]⟩
  obtain ⟨M, hM⟩ := UpperTheory.exists_primePow_scalar_integral_of_good_prime E A n p S F r hA.prime hA.good g₀ hg₀u
  obtain ⟨dc, hdc, hdcw, hdcv⟩ := cen_ex F c hc
  obtain ⟨dr, hdr, hdrw, -⟩ := cen_ex F (r ^ M) (pow_pos hA.prime.pos M)
  have hI := hM dr hdrw
  rw [map_mul, hg₀] at hI
  have hK : ∀ k ∈ Ty.K, Integ S.L (k * F.j dc) := fun k hk v hv => by
    rw [map_mul, Module.End.mul_apply, hdcv, map_nsmul]
    exact hcK k hk v hv
  obtain ⟨D, hD⟩ : ∃ D, D = F.j dc * F.j dr * F.j dc := ⟨_, rfl⟩
  have hDc : ∀ g, D * g = g * D := fun g => by
    rw [hD, mul_assoc, hdc g, ← mul_assoc, mul_assoc _ _ g, hdr g, ← mul_assoc, hdc g]
    simp only [mul_assoc]
  have hDc' : ∀ g, D⁻¹ * g = g * D⁻¹ := fun g => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hDc g, mul_inv_cancel_right]
  have hs : ∀ w : Spl E p, ((L w).pr D).val =
      ((c * r ^ M * c : ℕ) : w.1.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) := fun w => by
    rw [hD, ← map_mul, ← map_mul, (hTy.fac w).1, map_mul, map_mul, Units.val_mul, Units.val_mul, hdcw, hdrw]
    simp only [smul_mul_assoc, one_mul, smul_smul, Nat.cast_mul]
  have hs0 : ∀ w : Spl E p, ((c * r ^ M * c : ℕ) : w.1.adicCompletion E) ≠ 0 := fun w => by
    haveI : CharZero (w.1.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
    exact Nat.cast_ne_zero.2 (Nat.mul_pos (Nat.mul_pos hc (pow_pos hA.prime.pos M)) hc).ne'
  have hτH : Ty.tf τ ∈ Hecke ℂ Ty.K₀ := (pTfAdm _ _ Ty τ hτ0).1.1
  have h1H : Ty.tf 1 ∈ Hecke ℂ Ty.K₀ := (pTfAdm _ _ Ty 1 (map_one _)).1.1
  have hid := (tfIdem_holds _ _ Ty τ hτ0).2
  have hue : conv Ty.K₀ (trl D (Ty.tf τ)) (Ty.tf 1) = trl D (Ty.tf τ) := by rw [conv_trl_left D hτH h1H, hid.1]
  have hsupp : ∀ g, trl D (Ty.tf τ) g ≠ 0 → Integ S.L g⁻¹ ∧
      ∀ w ∈ W, (L w).pr D * (L w).pr g ∈ DoubleCoset.doubleCoset (t w) (Iw n w.1 : Set (GLw n w.1)) (Iw n w.1) := by
    intro g hg
    obtain ⟨a, ha, b, hb, e⟩ := tf_supp Ty hg
    refine ⟨?_, fun w hwW => ?_⟩
    · have e' : g⁻¹ = b⁻¹ * F.j dc * (τ⁻¹ * F.j dr * (a⁻¹ * F.j dc)) := by
        have e1 : g⁻¹ = b⁻¹ * τ⁻¹ * a⁻¹ * D := by
          rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, ← mul_assoc, ← e, _root_.mul_inv_rev, inv_mul_cancel_right]
        rw [e1, mul_assoc b⁻¹ (F.j dc), hdc, mul_assoc τ⁻¹, hdr, hD]
        simp only [mul_assoc]
      rw [e']
      exact integ_mul (hK _ (inv_mem hb)) (integ_mul hI (hK _ (inv_mem ha)))
    · rw [← map_mul, e, map_mul, map_mul, hτw w hwW]
      exact DoubleCoset.mem_doubleCoset.2 ⟨_, (hF w hwW).1.2 a ha, _, (hF w hwW).1.2 b hb, rfl⟩
  have hpow : ∀ m : ℕ, ∀ g, powFn Ty.K₀ (trl D (Ty.tf τ)) (Ty.tf 1) (m + 1) g ≠ 0 → Integ S.L g⁻¹ ∧
      ∀ w ∈ W, (L w).pr D ^ (m + 1) * (L w).pr g ∈
        DoubleCoset.doubleCoset (t w ^ (m + 1)) (Iw n w.1 : Set (GLw n w.1)) (Iw n w.1) := by
    intro m
    induction m with
    | zero =>
      intro g hg
      simp only [zero_add, pow_one]
      refine hsupp g ?_
      rw [← hue]
      exact hg
    | succ m ih =>
      intro g hg
      unfold powFn at hg
      rw [Function.iterate_succ_apply'] at hg
      obtain ⟨a, b, ha, hb, rfl⟩ := pConvSupp _ _ _ _ _ hg
      obtain ⟨a1, a2⟩ := hsupp a ha
      obtain ⟨b1, b2⟩ := ih b hb
      refine ⟨by rw [_root_.mul_inv_rev]; exact integ_mul b1 a1, fun w hwW => ?_⟩
      have := htm w (m + 1) _ (a2 w hwW) _ (b2 w hwW)
      rwa [mul_assoc, ← mul_assoc ((L w).pr a), ← ((scal_comm (hs w) ((L w).pr a)).pow_left (m + 1)).eq, mul_assoc,
        ← mul_assoc, ← pow_succ', ← map_mul] at this
  refine ⟨trl D (Ty.tf τ), trl_mem hDc hτH, trl D⁻¹ u', trl_mem hDc' hu', ?_, hue, ?_, fun f hf => ?_, fun m hm => ?_⟩
  · rw [conv_trl_right _ hDc, hid.2]
  · rw [conv_trl_left _ hu' (trl_mem hDc hτH), conv_trl_right _ hDc, hu'τ]
    funext g
    simp [trl]
  · obtain ⟨hfH, hfc⟩ := comm_span Ty.cms hτH (by
      rintro f ⟨h, h0, h1, rfl⟩
      exact ⟨(pTfAdm _ _ Ty h h0).1.1, hcm h h0 h1⟩) f hf
    rw [conv_trl_left D hτH hfH, conv_trl_right _ hDc, hfc]
  · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    refine ⟨fun w => {y | (L w).pr D ^ (m + 1) * y ∈
      DoubleCoset.doubleCoset (t w ^ (m + 1)) (Iw n w.1 : Set (GLw n w.1)) (Iw n w.1)}, fun w _ y hy => ⟨?_, fun a ha => ?_⟩, hpow m⟩
    · exact scal_sep (hs0 w) (hs w) _ y (hts w _ hm _ hy)
    · obtain ⟨a₁, h₁, a₂, h₂, e⟩ := DoubleCoset.mem_doubleCoset.1 hy
      refine DoubleCoset.mem_doubleCoset.2 ⟨a * a₁, mul_mem ha h₁, a₂, h₂, ?_⟩
      rw [← mul_assoc, ((scal_comm (hs w) a).pow_left (m + 1)).eq, mul_assoc, e]
      simp only [mul_assoc]

end UpperTheory.Gal.Spc

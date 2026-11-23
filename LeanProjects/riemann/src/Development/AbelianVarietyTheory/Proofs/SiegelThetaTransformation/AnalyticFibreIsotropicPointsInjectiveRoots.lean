import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ZGeo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {r g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
  {L : Lt E r} {y : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y)

theorem epi_spMap {K k : Type} [Field K] [Field k] (β : K →+* k) : Epi (spMap β) := by
  have hff : (CommRingCat.ofHom β).hom.FaithfullyFlat := by
    letI := β.toAlgebra
    show Module.FaithfullyFlat K k
    infer_instance
  obtain ⟨h1, h2⟩ := (AlgebraicGeometry.flat_and_surjective_SpecMap_iff (CommRingCat.ofHom β)).2 hff
  exact AlgebraicGeometry.Flat.epi_of_flat_of_surjective _

noncomputable def ptHom : (Fin r → E) →+ Additive (ptO Xo y.x ⟶ Xo.univ.t.G) :=
  AddMonoidHom.mk' (fun v => Additive.ofMul (A.ex (pv X idx x v))) fun u v => by
    rw [← ofMul_mul, ← A.ex_add, pv, per_add]; rfl

theorem ex_eq (v : Fin r → E) : A.ex (pv X idx x v) = (ptHom A v).toMul := rfl

theorem ex_add (u v : Fin r → E) : A.ex (pv X idx x (u + v)) = A.ex (pv X idx x u) * A.ex (pv X idx x v) := by
  have h : pv X idx x (u + v) = pv X idx x u + pv X idx x v := by
    funext j
    simp only [pv, per_add, Function.comp_apply, Pi.add_apply]
  rw [h, A.ex_add]

theorem ex_pow (m : ℕ) (v : Fin r → E) : A.ex (pv X idx x v) ^ m = A.ex (pv X idx x (m • v)) := by
  induction m with
  | zero =>
    have hz : pv X idx x 0 = 0 := by
      funext j
      simp only [pv, per_zero, Function.comp_apply, Pi.zero_apply]
    have h0 : A.ex 0 = 1 := by
      have h := A.ex_add 0 0
      rw [add_zero] at h
      exact mul_left_cancel (a := A.ex 0) (b := A.ex 0) (c := 1) (by rw [_root_.mul_one, ← h])
    rw [pow_zero, zero_smul, hz, h0]
  | succ m ih =>
    rw [pow_succ, ih, ← GlobalTheory.Dict.ZGeo.ex_add, succ_nsmul]

theorem ex_of_mem {v : Fin r → E} (hv : v ∈ L) : A.ex (pv X idx x v) = 1 := by
  exact (A.ex_ker _).2 ⟨v, hv, rfl⟩

theorem ex_act (a : 𝓞 E) (v : Fin r → E) :
    A.ex (pv X idx x v) ≫ Xo.univ.t.act.act a = A.ex (pv X idx x ((a : E) • v)) := by
  rw [pv_smul idx x (a : E) v, A.ex_lin]

theorem ex_prod {n : ℕ} (v : Fin n → Fin r → E) :
    (List.ofFn fun j => A.ex (pv X idx x (v j))).prod = A.ex (pv X idx x (∑ j, v j)) := by
  induction n with
  | zero =>
    have h0 := GlobalTheory.Dict.ZGeo.ex_pow A 0 (0 : Fin r → E)
    rw [pow_zero, smul_zero] at h0
    rw [List.ofFn_zero, List.prod_nil, Fin.sum_univ_zero]
    exact h0
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => v j.succ), Fin.sum_univ_succ, GlobalTheory.Dict.ZGeo.ex_add]

theorem sub_mem_of_ex_eq (hinj : Function.Injective (pv X idx x)) {u v : Fin r → E}
    (h : A.ex (pv X idx x u) = A.ex (pv X idx x v)) : u - v ∈ L := by
  have h1 : A.ex (pv X idx x (u - v)) = 1 := by
    have h2 := GlobalTheory.Dict.ZGeo.ex_add A (u - v) v
    rw [sub_add_cancel, h] at h2
    exact mul_right_cancel (a := A.ex (pv X idx x (u - v))) (b := A.ex (pv X idx x v)) (c := 1)
      (by rw [_root_.one_mul]; exact h2.symm)
  obtain ⟨w, hw, hpw⟩ := (A.ex_ker _).1 h1
  rw [hinj hpw]
  exact hw

omit [IsCMField E] in

theorem sum_mem_of_tens {n : ℕ} {Λ : Lt E n} {mu : Matrix (Fin n) (Fin n) E}
    (hmu : ∀ v ∈ Λ, mu.mulVec v ∈ stdLat E n) {u : Matrix (Fin n) (Fin r) E} (hu : u ∈ tens Λ L) (i : Fin n) :
    ∑ j, mu i j • u j ∈ L := by
  unfold tens at hu
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨w, hw, l', hl', rfl⟩ := hy
    have hi : (mu.mulVec w) i ∈ (1 : Submodule (𝓞 E) E) := by
      have hmw := hmu w hw
      rw [stdLat, Submodule.mem_pi] at hmw
      exact hmw i (Set.mem_univ i)
    obtain ⟨c', hc⟩ := Submodule.mem_one.1 hi
    have hs : ∑ j, mu i j • vecMulVec w l' j = (mu.mulVec w) i • l' := by
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMulVec_apply, mulVec, dotProduct,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hs, ← hc, algebraMap_smul]
    exact L.smul_mem c' hl'
  | zero =>
    have hs : ∑ j, mu i j • (0 : Matrix (Fin n) (Fin r) E) j = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [show (0 : Matrix (Fin n) (Fin r) E) j = 0 from rfl, smul_zero]
    rw [hs]
    exact L.zero_mem
  | add y z _ _ hy hz =>
    have hs : ∑ j, mu i j • (y + z) j = ∑ j, mu i j • y j + ∑ j, mu i j • z j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← smul_add]
      rfl
    rw [hs]
    exact L.add_mem hy hz
  | neg y _ hy =>
    have hs : ∑ j, mu i j • (-y) j = -∑ j, mu i j • y j := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← smul_neg]
      rfl
    rw [hs]
    exact L.neg_mem hy

omit [IsCMField E] in
theorem nsmul_inv_smul {N : ℕ} (hN : 0 < N) (v : Fin r → E) : N • ((N : E)⁻¹ • v) = v := by
  rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), one_smul]

theorem inZh {n N : ℕ} (hN : 0 < N) {Λ : Lt E n} {u : Matrix (Fin n) (Fin r) E} (hu : u ∈ tens Λ L)
    (h2 : ∀ b, ∃ u' ∈ L, N • u b = (2 : ℕ) • u') :
    InZh Xo (⟨Λ⟩ : GenLat E n) N (fun b => A.ex (pv X idx x ((N : E)⁻¹ • u b))) := by
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold InZh
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · obtain ⟨u', hu', he⟩ := h2 b
    rw [GlobalTheory.Dict.ZGeo.ex_pow, sq, mul_smul, nsmul_inv_smul hN, he]
    exact ex_of_mem A (nsmul_mem hu' 2)
  · have hj : ∀ j, A.ex (pv X idx x ((N : E)⁻¹ • u j)) ≫ Xo.univ.t.act.act (cm i j) =
        A.ex (pv X idx x (mu i j • u j)) := by
      intro j
      rw [ex_act, hcm, smul_smul]
      congr 3
      rw [mul_comm ((N : E) * mu i j) ((N : E)⁻¹), ← _root_.mul_assoc, inv_mul_cancel₀ hN0, _root_.one_mul]
    simp only [hj]
    rw [ex_prod]
    exact ex_of_mem A (sum_mem_of_tens hmu hu i)

theorem geoInj (hinj : Function.Injective (pv X idx x)) {n N : ℕ} (hN : 0 < N) {Jx : Type}
    (u : Jx → Matrix (Fin n) (Fin r) E) (hu : ∀ i i', (∀ b, ∃ u' ∈ L, u i b - u i' b = N • u') → i = i') :
    GeoInj Xo y.x (fun i b => A.ex (pv X idx x ((N : E)⁻¹ • u i b))) := by
  unfold GeoInj
  intro k _ ψ g hg i i' hii
  have hepi : Epi g := by
    have : Epi g.left := by
      rw [hg]
      exact epi_spMap ψ
    exact Over.epi_of_epi_left g
  apply hu
  intro b
  have hb : g ≫ A.ex (pv X idx x ((N : E)⁻¹ • u i b)) = g ≫ A.ex (pv X idx x ((N : E)⁻¹ • u i' b)) :=
    congrFun hii b
  have he := (cancel_epi g).1 hb
  refine ⟨(N : E)⁻¹ • u i b - (N : E)⁻¹ • u i' b, sub_mem_of_ex_eq A hinj he, ?_⟩
  rw [← smul_sub, nsmul_inv_smul hN]

omit [Algebra c.F ℂ] in

theorem levPt_levRep {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) (a : Dw.La) :
    levPt Xo x0 (levRep (l := l) (Submodule.Quotient.mk a)) = levPt Xo x0 a := by
  have hs : (Submodule.Quotient.mk (levRep (l := l) (Submodule.Quotient.mk a : LevQ Dw l)) : LevQ Dw l) =
      Submodule.Quotient.mk a :=
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ _)
  have hq := (Submodule.Quotient.eq _).1 hs
  have he : Xo.univ.eta (levRep (l := l) (Submodule.Quotient.mk a : LevQ Dw l)) = Xo.univ.eta a := by
    rw [← sub_add_cancel (levRep (l := l) (Submodule.Quotient.mk a : LevQ Dw l)) a, Xo.univ.eta_add,
      Xo.univ.eta_ker _ hq, _root_.one_mul]
  unfold levPt
  rw [he]
set_option maxHeartbeats 1000000 in

theorem roots {N : ℕ} (hN : 0 < N) {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hm : IsMark l L mk) (hA : A.Marked mk)
    (hM : l.M ∣ N) {Y : Fin r → E} {q : LevQ Dw l}
    (h1 : ∃ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), Submodule.Quotient.mk a = q ∧ Y - ((l.M : E)⁻¹) • mk a ∈ L)
    (h2 : ∃ j : ℕ, ∀ s ∈ l.Mb ^ j, ∃ u ∈ L, s • Y = (2 * N) • u) :
    A.ex (pv X idx x ((N : E)⁻¹ • Y)) ^ N = levPt Xo y.x (levRep q) ∧
      (∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (A.ex (pv X idx x ((N : E)⁻¹ • Y)))) ∧
      ∃ u ∈ L, (N ^ 2 : ℕ) • ((N : E)⁻¹ • Y) = (2 : ℕ) • u := by
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  obtain ⟨a, ha, hq, hw⟩ := h1
  obtain ⟨j, hj⟩ := h2
  refine ⟨?_, ⟨j, ?_⟩, ?_⟩
  · rw [GlobalTheory.Dict.ZGeo.ex_pow, nsmul_inv_smul hN, ← hq, levPt_levRep, hA a ha,
      ← sub_add_cancel Y ((l.M : E)⁻¹ • mk a), GlobalTheory.Dict.ZGeo.ex_add, ex_of_mem A hw, _root_.one_mul]
  · intro s hs
    rw [ex_act]
    apply ex_of_mem A
    obtain ⟨w, hw', hsw⟩ := hj s hs
    have e : (s : E) • ((N : E)⁻¹ • Y) = w + w := by
      funext t
      have h3 := congrFun hsw t
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] at h3 ⊢
      have hs' : algebraMap (𝓞 E) E s = (s : E) := rfl
      rw [Algebra.smul_def, hs'] at h3
      field_simp
      linear_combination h3
    rw [e]
    exact L.add_mem hw' hw'
  · have hMb : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
      have hm2 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
        rw [l.prod]
        exact Ideal.mem_span_singleton_self _
      exact SetLike.le_def.1 (Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))) hm2
    obtain ⟨u', hu', hsu⟩ := hj _ (Ideal.pow_mem_pow hMb j)
    obtain ⟨t, ht⟩ := (l.odd.pow : Odd (l.M ^ j))
    obtain ⟨k, hk⟩ := hM
    have hM0 : 0 < l.M := by have := l.three_le; omega
    have e1 : N • ((l.M : E)⁻¹ • mk a) = k • mk a := by
      rw [hk, mul_comm, mul_smul, nsmul_inv_smul hM0]
    have hV : N • Y ∈ L := by
      have e2 : N • Y = N • (Y - (l.M : E)⁻¹ • mk a) + N • ((l.M : E)⁻¹ • mk a) := by
        rw [← smul_add, sub_add_cancel]
      rw [e2, e1]
      exact L.add_mem (nsmul_mem hw N) (nsmul_mem (hm.mem a) k)
    refine ⟨N • N • u' - t • (N • Y), L.sub_mem (nsmul_mem (nsmul_mem hu' N) N) (nsmul_mem hV t), ?_⟩
    have ht' : ((l.M : E)) ^ j = 2 * (t : E) + 1 := by exact_mod_cast ht
    funext i
    have h3 := congrFun hsu i
    simp only [← Nat.cast_smul_eq_nsmul E] at h3 ⊢
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at h3 ⊢
    rw [Algebra.smul_def, map_pow, map_natCast, ht'] at h3
    have hh : (N : E) ^ 2 * ((N : E)⁻¹ * Y i) = N * Y i := by
      rw [sq, _root_.mul_assoc, mul_inv_cancel_left₀ hN0]
    linear_combination hh + (N : E) * h3

end GlobalTheory.Dict.ZGeo

namespace GlobalTheory.Dict

theorem points_inZh_geoInj_roots : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (n N : ℕ) (Λ : Lt E n), 0 < N → (∀ (Jx : Type) (u : Jx → Matrix (Fin n) (Fin r) E), (∀ i, u i ∈ tens Λ L ∧ ∀ b, ∃ u' ∈ L, N • u i b = (2 : ℕ) • u') → (∀ i i', (∀ b, ∃ u' ∈ L, u i b - u i' b = N • u') → i = i') → (∀ i, InZh Xo (⟨Λ⟩ : GenLat E n) N (fun b => A.ex (pv X idx x ((N : E)⁻¹ • u i b)))) ∧ GeoInj Xo y.x (fun i b => A.ex (pv X idx x ((N : E)⁻¹ • u i b)))) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → A.Marked mk → l.M ∣ N → ∀ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → ∀ q b, A.ex (pv X idx x ((N : E)⁻¹ • Y q b)) ^ N = levPt Xo y.x (levRep (q b)) ∧ (∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (A.ex (pv X idx x ((N : E)⁻¹ • Y q b)))) ∧ ∃ u ∈ L, (N ^ 2 : ℕ) • ((N : E)⁻¹ • Y q b) = (2 : ℕ) • u := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx _ n N Λ hN
  have hinj : Function.Injective (pv X idx x) :=
    (hx_laws E r X g bas idx 0 hs ⟨0, rfl⟩ x hx).2.2.2.2.2.1
  refine ⟨fun Jx u hu hdist => ⟨fun i => ZGeo.inZh A hN (hu i).1 (hu i).2, ZGeo.geoInj A hinj hN u hdist⟩, ?_⟩
  intro mk hm hA hM Y hY q b
  exact ZGeo.roots A hN hm hA hM (hY q b).1 (hY q b).2

end GlobalTheory.Dict

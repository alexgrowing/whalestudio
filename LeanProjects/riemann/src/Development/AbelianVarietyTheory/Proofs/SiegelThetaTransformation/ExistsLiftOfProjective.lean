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

namespace GlobalTheory.Dict

theorem exists_lift_of_projective {R P V Q : Type} [CommRing R] [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup V] [Module R V] [Group Q] (act : R → Q → Q) (L : Submodule R V) (ev : P → Q) (φ : V → Q)
    (ev_add : ∀ a b, ev (a + b) = ev a * ev b) (ev_lin : ∀ (s : R) a, ev (s • a) = act s (ev a))
    (φ_add : ∀ a b, φ (a + b) = φ a * φ b) (φ_lin : ∀ (s : R) a, φ (s • a) = act s (φ a))
    (onto : ∀ a, ∃ v ∈ L, ev a = φ v) : ∃ mk : P →ₗ[R] V, ∀ a, mk a ∈ L ∧ ev a = φ (mk a) := by
  have hev0 : ev 0 = 1 := mul_left_cancel (a := ev 0) (by rw [_root_.mul_one, ← ev_add, add_zero])
  have hφ0 : φ 0 = 1 := mul_left_cancel (a := φ 0) (by rw [_root_.mul_one, ← φ_add, add_zero])

  let W : Submodule R (P × L) :=
    { carrier := {x | ev x.1 = φ (x.2 : V)}
      add_mem' := by
        rintro ⟨a, v⟩ ⟨b, w⟩ ha hb
        simp only [Set.mem_ofPred_eq, Prod.mk_add_mk, Submodule.coe_add] at *
        rw [ev_add, φ_add, ha, hb]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, Prod.fst_zero, Prod.snd_zero, ZeroMemClass.coe_zero]
        rw [hev0, hφ0]
      smul_mem' := by
        rintro s ⟨a, v⟩ ha
        simp only [Set.mem_ofPred_eq, Prod.smul_mk, Submodule.coe_smul] at *
        rw [ev_lin, φ_lin, ha] }
  let f : W →ₗ[R] P := (LinearMap.fst R P L).comp W.subtype
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨v, hv, he⟩ := onto a
    exact ⟨⟨(a, ⟨v, hv⟩), he⟩, rfl⟩
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨L.subtype.comp ((LinearMap.snd R P L).comp (W.subtype.comp h)), fun a => ⟨((h a : W) : P × L).2.2, ?_⟩⟩
  have h1 : ((h a : W) : P × L).1 = a := LinearMap.congr_fun hh a
  have h2 : ev ((h a : W) : P × L).1 = φ (((h a : W) : P × L).2 : V) := (h a).2
  rw [h1] at h2
  exact h2

private theorem pv_add_siegel_theta_transformation {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
    (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) (u v : Fin r → E) :
    pv X idx x (u + v) = pv X idx x u + pv X idx x v := by
  have hemb : ∀ τ : E →+* ℂ, ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (u + v) =
      ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ u + ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := fun τ => by
    funext a
    simp [ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
  funext j
  simp only [pv, Function.comp_apply, Pi.add_apply, GlobalTheory.ThFr.per, hemb]
  split_ifs
  · simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  · rw [Matrix.mulVec_add, Pi.add_apply]

theorem exists_mark : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∃ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk ∧ A.Marked mk := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL
  have := Dw.proj
  obtain ⟨-, I, -, -, hI⟩ := Xo.univ.geom ℂ y.x _ y.x_over

  obtain ⟨m, hm, c0, hc0, hmc⟩ : ∃ m ∈ l.Mb, ∃ c0 ∈ Mfr l, m + c0 = 1 := by
    have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ Mfr l := by rw [Mfr, l.coprime]; exact Submodule.mem_top
    exact Submodule.mem_sup.mp h1
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hME : (l.M : E) ≠ 0 := Nat.cast_ne_zero.mpr hM0.ne'
  have hMC : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM0.ne'
  have hex0 : A.ex 0 = 1 := mul_left_cancel (a := A.ex 0) (by rw [_root_.mul_one, ← A.ex_add, add_zero])
  have hexn : ∀ (n : ℕ) z, A.ex (n • z) = A.ex z ^ n := by
    intro n z
    induction n with
    | zero => rw [zero_smul, hex0, pow_zero]
    | succ n ih => rw [succ_nsmul, A.ex_add, ih, pow_succ]
  have hpvs : ∀ (a : E) (v : Fin r → E), pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j :=
    fun a v => pv_smul idx x a v
  have hinj : Function.Injective (pv X idx x) := (hx_laws E r X g bas idx 0 hs ⟨0, rfl⟩ x hx).2.2.2.2.2.1
  have hsv : ∀ (s : 𝓞 E) (v : Fin r → E), s • v = (s : E) • v := fun _ _ => rfl

  let φ : (Fin r → E) → (ptO Xo y.x ⟶ Xo.univ.t.G) := fun v => A.ex (pv X idx x ((l.M : E)⁻¹ • v))
  have hφadd : ∀ u v, φ (u + v) = φ u * φ v := fun u v => by
    simp only [φ, smul_add, pv_add_siegel_theta_transformation, A.ex_add]
  have hφlin : ∀ (s : 𝓞 E) v, φ (s • v) = φ v ≫ Xo.univ.t.act.act s := fun s v => by
    simp only [φ]
    rw [← A.ex_lin, ← hpvs, hsv, smul_comm]

  have heta : ∀ a, Xo.univ.eta a = Xo.univ.eta (c0 • a) := by
    intro a
    have h1 : a = c0 • a + m • a := by rw [← add_smul, add_comm, hmc, one_smul]
    conv_lhs => rw [h1]
    rw [Xo.univ.eta_add, Xo.univ.eta_ker (m • a) (Submodule.smul_mem_smul hm Submodule.mem_top),
      _root_.mul_one]
  have hlev : ∀ a, levPt Xo y.x a = I.ev l.M (c0 • a) := by
    intro a
    rw [levPt, heta a]
    exact hI _ (Submodule.smul_mem_smul hc0 Submodule.mem_top)
  obtain ⟨mk, hmk⟩ := exists_lift_of_projective (fun s q => q ≫ Xo.univ.t.act.act s) L
    (fun a => I.ev l.M (c0 • a)) φ (fun a b => by rw [smul_add, I.add])
    (fun s a => by rw [smul_comm c0 s a, I.lin]) hφadd hφlin (by
      intro a
      obtain ⟨z, hz⟩ := A.ex_onto (I.ev l.M (c0 • a))
      have hp : A.ex z ^ l.M = 1 := by
        rw [hz]
        exact (I.onto l.M hM0 _).mpr ⟨_, rfl⟩
      rw [← hexn] at hp
      obtain ⟨v, hv, hzv⟩ := (A.ex_ker _).mp hp
      refine ⟨v, hv, ?_⟩
      rw [← hz]
      show A.ex z = A.ex (pv X idx x ((l.M : E)⁻¹ • v))
      congr 1
      rw [hpvs, ← hzv]
      funext j
      simp only [Pi.smul_apply, nsmul_eq_mul, map_inv₀, map_natCast]
      rw [inv_mul_cancel_left₀ hMC])

  have hevmk : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), I.ev l.M a = φ (mk a) := by
    intro a ha
    rw [← hI a ha, ← (hmk a).2]
    exact hlev a

  have hdiff : ∀ u v, φ u = φ v → ∃ w ∈ L, u - v = l.M • w := by
    intro u v huv
    have h1 : φ (u - v) = 1 := by
      have h2 := hφadd (u - v) v
      rw [sub_add_cancel, huv] at h2
      exact mul_right_cancel (h2.symm.trans (_root_.one_mul _).symm)
    obtain ⟨w, hw, hw'⟩ := (A.ex_ker _).mp h1
    refine ⟨w, hw, ?_⟩
    have h3 := hinj hw'
    rw [← h3, ← Nat.cast_smul_eq_nsmul E, smul_inv_smul₀ hME]

  have hML : ∀ v ∈ Mfr l • L, ∃ u ∈ L, m • v = l.M • u := by
    intro v hv
    have h1 : m • v ∈ (l.Mb * Mfr l) • L := by
      rw [Submodule.mul_smul]
      exact Submodule.smul_mem_smul hm hv
    rw [Mfr, l.prod, Submodule.ideal_span_singleton_smul] at h1
    obtain ⟨u, hu, hu'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact ⟨u, hu, by rw [← hu', Nat.cast_smul_eq_nsmul]⟩
  refine ⟨mk, ⟨fun a => (hmk a).1, ?_, ?_⟩, fun a _ => (hlev a).trans (hmk a).2⟩
  · intro a ha hau
    obtain ⟨u, hu, hau⟩ := hau
    apply (I.ker l.M hM0 a).mp
    rw [hevmk a ha]
    show A.ex (pv X idx x ((l.M : E)⁻¹ • mk a)) = 1
    rw [hau, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hME]
    exact (A.ex_ker _).mpr ⟨u, hu, rfl⟩
  · intro v hv
    have hvL : v ∈ L := Submodule.smul_le_right hv
    have hp : φ v ^ l.M = 1 := by
      have h1 : l.M • pv X idx x ((l.M : E)⁻¹ • v) = pv X idx x v := by
        rw [hpvs]
        funext j
        simp only [Pi.smul_apply, nsmul_eq_mul, map_inv₀, map_natCast]
        rw [mul_inv_cancel_left₀ hMC]
      show A.ex (pv X idx x ((l.M : E)⁻¹ • v)) ^ l.M = 1
      rw [← hexn, h1]
      exact (A.ex_ker _).mpr ⟨v, hvL, rfl⟩
    obtain ⟨a0, ha0⟩ := (I.onto l.M hM0 (φ v)).mp hp
    have haM : c0 • a0 ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := Submodule.smul_mem_smul hc0 Submodule.mem_top
    have h3 : φ (mk (c0 • a0)) = φ (c0 • v) := by
      rw [← hevmk _ haM, I.lin, ha0, hφlin]
    obtain ⟨w, hw, hw'⟩ := hdiff _ _ h3.symm
    obtain ⟨u', hu', hmv⟩ := hML v hv
    refine ⟨c0 • a0, haM, u' + w, L.add_mem hu' hw, ?_⟩
    calc v = m • v + c0 • v := by rw [← add_smul, hmc, one_smul]
      _ = mk (c0 • a0) + (l.M • u' + l.M • w) := by rw [hmv, ← hw']; abel
      _ = mk (c0 • a0) + l.M • (u' + w) := by rw [smul_add]

end GlobalTheory.Dict

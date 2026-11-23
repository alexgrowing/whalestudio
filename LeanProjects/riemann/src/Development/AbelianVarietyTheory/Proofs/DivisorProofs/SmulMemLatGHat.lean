import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion

namespace GlobalTheory.AdMark

open scoped Matrix

theorem exists_lift {R S La U A : Type} [CommRing R] [CommRing S] [AddCommGroup La] [Module R La] [Module.Projective R La]
    [AddCommGroup U] [Module R U] [AddCommGroup A] [Module S A] (φ : R → S) (fv : U →+ A)
    (hfv : ∀ c x, fv (c • x) = φ c • fv x) (K : A →ₗ[S] A) (hKi : Function.Injective K) (H₁ Hk : AddSubgroup A)
    (hsm : ∀ c, ∀ z ∈ Hk, φ c • z ∈ Hk) (L : Submodule R U) (ι : La →ₗ[R] U) (hι : Function.Injective ι) (N : ℕ)
    (hL : ∀ v, v ∈ L ↔ fv v ∈ Hk) (hK : ∀ z, z ∈ Hk ↔ ∃ y ∈ H₁, K y = z)
    (h1 : ∀ v, fv v ∈ H₁ ↔ ∃ a, ι a = v)
    (ap1 : ∀ y ∈ H₁, ∃ a, ∃ w ∈ H₁, y = fv (ι a) + N • w)
    (apk : ∀ z ∈ Hk, ∃ x ∈ L, ∃ w ∈ Hk, z = fv x + N • w)
    (hdiv : ∀ x z, fv x = N • z → ∃ w, fv w = z ∧ x = N • w) :
    ∃ mk : La →ₗ[R] U, (∀ a, mk a ∈ L) ∧ (∀ a, ∃ w ∈ Hk, fv (mk a) - K (fv (ι a)) = N • w) ∧
      (∀ a, (∃ u ∈ L, mk a = N • u) → ∃ b, a = N • b) ∧ ∀ v ∈ L, ∃ a, ∃ u ∈ L, v = mk a + N • u := by
  let P : Submodule R (U × La) :=
    { carrier := {p | p.1 ∈ L ∧ ∃ w ∈ Hk, fv p.1 - K (fv (ι p.2)) = N • w}
      zero_mem' := ⟨L.zero_mem, 0, zero_mem _, by simp⟩
      add_mem' := by
        rintro p q ⟨hp, w, hw, e⟩ ⟨hq, w', hw', e'⟩
        refine ⟨L.add_mem hp hq, w + w', add_mem hw hw', ?_⟩
        rw [smul_add, ← e, ← e']
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        abel
      smul_mem' := by
        rintro c p ⟨hp, w, hw, e⟩
        refine ⟨L.smul_mem c hp, φ c • w, hsm c w hw, ?_⟩
        rw [smul_comm N, ← e]
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, hfv, smul_sub] }
  have hs : Function.Surjective ((LinearMap.snd R U La) ∘ₗ P.subtype) := by
    intro a
    obtain ⟨x, hx, w, hw, e⟩ := apk _ ((hK _).2 ⟨_, (h1 _).2 ⟨a, rfl⟩, rfl⟩)
    exact ⟨⟨(x, a), hx, -w, neg_mem hw, by rw [e]; simp⟩, rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hs
  have hs2 : ∀ a, (s a).1.2 = a := fun a => LinearMap.congr_fun hs a
  let mk : La →ₗ[R] U := (LinearMap.fst R U La) ∘ₗ P.subtype ∘ₗ s
  have m1 : ∀ a, mk a ∈ L := fun a => (s a).2.1
  have m2 : ∀ a, ∃ w ∈ Hk, fv (mk a) - K (fv (ι a)) = N • w := fun a => by
    obtain ⟨w, hw, e⟩ := (s a).2.2
    rw [hs2] at e
    exact ⟨w, hw, e⟩
  refine ⟨mk, m1, m2, ?_, ?_⟩
  · rintro a ⟨u, hu, e⟩
    obtain ⟨w, hw, e'⟩ := m2 a
    obtain ⟨y, hy, ey⟩ := (hK _).1 (sub_mem ((hL u).1 hu) hw)
    have : fv (ι a) = N • y := by
      apply hKi
      rw [map_nsmul, ey, smul_sub, ← e', e, map_nsmul]
      abel
    obtain ⟨x, rfl, ex⟩ := hdiv _ _ this
    obtain ⟨b, rfl⟩ := (h1 _).1 hy
    exact ⟨b, hι (by rw [ex, map_nsmul])⟩
  · intro v hv
    obtain ⟨y, hy, ey⟩ := (hK _).1 ((hL v).1 hv)
    obtain ⟨a, w, hw, rfl⟩ := ap1 y hy
    obtain ⟨w', hw', e'⟩ := m2 a
    obtain ⟨u, hu, eu⟩ := hdiv (v - mk a) (K w - w') (by
      rw [map_sub, ← ey, smul_sub, ← e', map_add, map_nsmul]
      abel)
    refine ⟨a, u, (hL u).2 (hu ▸ sub_mem ((hK _).2 ⟨w, hw, rfl⟩) hw'), ?_⟩
    rw [← eu]
    abel

theorem sub_congr {A : Type} [AddCommGroup A] {x y z w w' : A} {M N c : ℕ} (hc : N = M * c) (e : y - z = M • w)
    (e' : x - z = N • w') : x - y = M • (c • w' - w) := by
  rw [smul_sub, ← mul_smul, ← hc, ← e, ← e']
  abel

end GlobalTheory.AdMark

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdMark

theorem latR_rfl {E : Type} [Field E] [NumberField E] {m : ℕ} (L : Submodule (𝓞 E) (Fin m → E)) :
    latR rfl L = L := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem smul_mem_latGHat {D : D7} (W : HSp D) (k : GA D W) (c : 𝓞 D.host.E) :
    ∀ z ∈ latGHat W k, ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • z ∈ latGHat W k := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨c • a, (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha, z, hz, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, ← _root_.mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_marking : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l l₂ : Geo.Tor.Level H) (W : HSp D) (r : ℕ) (hr : W.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), LatEmb W ι → l.M ∣ l₂.M → l₂.Mb ≤ l.Mb → ∀ k : GA D W, ∃ mk₂ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), IsMark l₂ (latR hr (latG W k)) mk₂ ∧ MarkAd l₂ W hr ι k mk₂ ∧ ∀ mk, (∀ a, mk a ∈ latR hr (latG W k)) → MarkAd l W hr ι k mk → MarkOver l l₂ (latR hr (latG W k)) mk mk₂ := by
  intro D H Dw l l₂ W r hr ι hι hM hMb k
  subst hr
  rw [latR_rfl]
  haveI := Dw.proj
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hM2 : l₂.M ≠ 0 := by have := l₂.three_le; omega
  let fv : (Fin W.rank → D.host.E) →+ (Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (finVec W) (GlobalTheory.AdLat.cap_fv_add D.host.F)
  have ap : ∀ g : GA D W, ∀ z ∈ latGHat W g, ∃ x ∈ latG W g, ∃ w ∈ latGHat W g, z = fv x + l₂.M • w := by
    intro g
    obtain ⟨a1, a2, -, -, a5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D W g
    rw [a5]
    exact (GlobalTheory.AdLat.hat_rational_points_and_approx _ _ _ _ a1 a2).2.1 l₂.M (Nat.pos_of_ne_zero hM2)
  obtain ⟨mk₂, m1, m2, m3, m4⟩ := exists_lift (fun c : 𝓞 D.host.E => (1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) fv
    (fun c x => by
      funext i
      change (1 : Af D.host.F) ⊗ₜ[D.host.F] ((c : D.host.E) * x i) = _ * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one])
    (finHom W k).1.mulVecLin
    (fun x y h => by
      have := congrArg (fun v => ((finHom W k)⁻¹).1 *ᵥ v) h
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using this)
    (latGHat W 1) (latGHat W k) (smul_mem_latGHat W k) (latG W k) ι hι.1 l₂.M
    (GlobalTheory.MarkCoset.latG_spec D W k).1 (GlobalTheory.MarkCoset.latG_spec D W k).2
    (fun v => ((GlobalTheory.MarkCoset.latG_spec D W 1).1 v).symm.trans (by rw [← hι.2]; rfl))
    (fun y hy => by
      obtain ⟨x, hx, h⟩ := ap 1 y hy
      rw [← hι.2] at hx
      obtain ⟨a, rfl⟩ := hx
      exact ⟨a, h⟩)
    (ap k) (GlobalTheory.MarkCoset.finVec_div W l₂.M hM2)
  refine ⟨mk₂, ⟨m1, fun a _ => m3 a, fun v hv => ?_⟩, fun a _ => m2 a, fun mk _ hmk a ha => ?_⟩
  · refine Submodule.smul_induction_on hv (fun m hm v hv => ?_) (fun x y hx hy => ?_)
    · obtain ⟨a, u, hu, rfl⟩ := m4 v hv
      refine ⟨m • a, Submodule.smul_mem_smul hm trivial, m • u, Submodule.smul_mem _ m hu, ?_⟩
      rw [smul_add, map_smul, smul_comm m]
    · obtain ⟨a, ha, u, hu, rfl⟩ := hx
      obtain ⟨a', ha', u', hu', rfl⟩ := hy
      exact ⟨a + a', add_mem ha ha', u + u', add_mem hu hu', by rw [map_add, smul_add]; abel⟩
  · obtain ⟨c, hc⟩ := hM
    obtain ⟨w, hw, e⟩ := hmk a (Submodule.smul_mono_left (Ideal.map_mono hMb) ha)
    obtain ⟨w', hw', e'⟩ := m2 a
    replace e : fv (mk a) - (finHom W k).1.mulVecLin (fv (ι a)) = l.M • w := e
    obtain ⟨u, hu, eu⟩ := GlobalTheory.MarkCoset.finVec_div W l.M hM0 (mk₂ a - mk a) (c • w' - w) (by
      exact (fv.map_sub _ _).trans (sub_congr hc e e'))
    refine ⟨u, ((GlobalTheory.MarkCoset.latG_spec D W k).1 u).2 (hu ▸ sub_mem (nsmul_mem hw' c) hw), ?_⟩
    rw [← eu]
    abel

end GlobalTheory.AdMark

import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationOneElementAtGridPlaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.DepthShift

open GlobalTheory.StdFrames (cpt mem_OA_iff comp_toAd toAd toAd_spec)
open scoped Pointwise

variable {D : D7}

theorem modul_mem_shiftId {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {r : 𝓞 D.host.E}
    (hr : r ∈ G.modul) : (r : D.host.E) ∈ shiftId G := by
  have h0 : G.pl.modulBar sc ≠ ⊥ := by
    intro h
    apply G.pl.modul_ne_bot sc
    unfold Places.modulBar at h
    have := congrArg (fun J => D.host.conj⁻¹ • J) h
    simpa using this
  have h1 := FractionalIdeal.one_mem_inv_coe_ideal (K := D.host.E) h0
  have h2 : (r : D.host.E) ∈ ((G.modul : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
    FractionalIdeal.mem_coeIdeal_of_mem _ hr
  simpa [shiftId] using FractionalIdeal.mul_mem_mul h2 h1

theorem smul_mem_idLat {n : ℕ} {I J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {r : 𝓞 D.host.E} (hr : (r : D.host.E) ∈ J)
    {t : Fin n → D.host.E} (ht : t ∈ idLat I Λ) : r • t ∈ idLat (I * J) Λ := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨s * r, FractionalIdeal.mul_mem_mul hs hr, y, hy, ?_⟩
    rw [mul_comm, mul_smul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

variable {S B : HSp D} {LS : Lat S} {LT LT' : Lat B}

theorem inc_smul_mem {r : 𝓞 D.host.E} (hr : ∀ t ∈ LT, r • t ∈ LT') {u : WO S B}
    (hu : u ∈ latO S B (LS : Set _) (LT : Set _) fun _ => True) :
    incA D (r : D.host.E) • u ∈ latO S B (LS : Set _) (LT' : Set _) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, r • t, hr t ht, ?_⟩
    ext i j
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] (r : D.host.E)) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] _) =
      pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * ((r : D.host.E) * t i) * _)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    ring
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mul_eq_of_toEAf {b b' x : AE D} (h : toEAf D b = toEAf D b') (h0 : infPart D x = 0) : b * x = b' * x := by
  have h1 : infPart D ((b - b') * x) = 0 := ((infPart D).map_mul _ _).trans (by rw [h0, mul_zero])
  have h2 : toEAf D (b - b') = 0 := ((toEAf D).map_sub _ _).trans (sub_eq_zero.2 h)
  have h3 : toEAf D ((b - b') * x) = 0 := ((toEAf D).map_mul _ _).trans (by rw [h2, zero_mul])
  have h4 := (comp_toAd D).ext _ h1 ((congrArg (toAd D) h3).trans (toAd D).map_zero)
  exact sub_eq_zero.1 ((sub_mul b b' x).symm.trans h4)

theorem exists_lift_int (c : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∃ c' : AE D, toEAf D c' = c.1 ∧ finPart D c' ∈ intAE D := by
  obtain ⟨c', -, hc'⟩ := (comp_toAd D).surj (toAd D c.1)
  refine ⟨c', GlobalTheory.AdeleBaseChange.map_injective (toAd_spec D) hc', ((comp_toAd D).int c').2 fun Q => ?_⟩
  rw [hc']
  exact (mem_OA_iff _).1 c.2 Q

set_option maxHeartbeats 800000 in

theorem smul_mem_of_idS {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : ∀ r ∈ 𝔪, ∀ t ∈ LT, r • t ∈ LT') {u : WO S B}
    (hu : u ∈ latO S B (LS : Set _) (LT : Set _) fun _ => True) {s : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (hs : s ∈ Formalism.L2.DIV.idS D.host.F 𝔪) {b : AE D} (hb : toEAf D b = s.1) :
    b • u ∈ latO S B (LS : Set _) (LT' : Set _) fun _ => True := by
  have key : ∃ b' : AE D, toEAf D b' = s.1 ∧ b' • u ∈ latO S B (LS : Set _) (LT' : Set _) fun _ => True := by
    clear hb
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, hr, rfl⟩ := hx
      exact ⟨incA D (r : D.host.E), rfl, inc_smul_mem (h𝔪 r hr) hu⟩
    | zero => exact ⟨0, RingHom.map_zero _, by rw [zero_smul]; exact zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨c, hc, hc'⟩ := hy
      exact ⟨a + c, by rw [RingHom.map_add, ha, hc, Subring.coe_add], by rw [add_smul]; exact add_mem ha' hc'⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨c', hc, hc'⟩ := exists_lift_int c
      refine ⟨c' * a, ((toEAf D).map_mul c' a).trans (congrArg₂ (· * ·) hc ha), ?_⟩
      rw [mul_smul]
      exact GlobalTheory.LatticeStable.smul_mem_latO D S B _ _ _ _ hc' _ ha'
  obtain ⟨b', hb', hm⟩ := key
  have e : b • u = b' • u := Matrix.ext fun i j =>
    mul_eq_of_toEAf (hb.trans hb'.symm) (GlobalTheory.FinPl.LatMem.mem_idAt_iff.1 (GlobalTheory.FinPl.LatMem.latO_mxAt hu i j)).1
  rw [e]
  exact hm

theorem mem_latO_shift : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts} (G : GridData L sc) {S B : HSp D} (LS : Lat S) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ₀ : Lat B), IsSelfDualC S LS → IsSelfDualC B (idLat I Λ₀) → IsSelfDualC B (idLat (I * shiftId G) Λ₀) → ∀ z : WO S B, z ∈ latO S B (LS : Set _) (idLat I Λ₀ : Set _) (fun _ => True) → (∃ e, IsIdemSum e G.pl.W0 ∧ e • z ∈ hatMx (G.modul • homLat LS (idLat I Λ₀))) → z ∈ latO S B (LS : Set _) (idLat (I * shiftId G) Λ₀ : Set _) (fun _ => True) := by
  intro D hOff T L μ0 hL sc G S B LS I Λ₀ hS _ _ z hz ⟨e, he, hez⟩
  have h𝔪 : ∀ r ∈ G.modul, ∀ t ∈ idLat I Λ₀, r • t ∈ idLat (I * shiftId G) Λ₀ :=
    fun r hr t ht => smul_mem_idLat (modul_mem_shiftId G hr) ht
  have hle : G.modul • homLat LS (idLat I Λ₀) ≤ homLat LS (idLat (I * shiftId G) Λ₀) :=
    Submodule.smul_le.2 fun r hr x hx y hy => by
      rw [smul_mulVec]
      exact h𝔪 r hr _ (hx y hy)
  have h1 : e • z ∈ latO S B (LS : Set _) (idLat (I * shiftId G) Λ₀ : Set _) fun _ => True := by
    refine GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hS he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hOff hL G) (fun i j => ?_) ?_
    · change e * (e * z i j) = e * z i j
      rw [← mul_assoc, GlobalTheory.PlaceDatum.idemSum_mul_self he]
    · refine AddSubgroup.closure_mono ?_ hez
      rintro _ ⟨α, hα, x, hx, rfl⟩
      exact ⟨α, hα, x, hle hx, rfl⟩
  obtain ⟨-, e1, e2⟩ := Comparison₂.cpt_idemSum he
  have hint : toEAf D (1 - e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    refine (mem_OA_iff _).2 fun Q => ?_
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one]
    by_cases hQ : Q ∈ G.pl.W0
    · rw [e1 Q hQ, sub_self]; exact zero_mem _
    · rw [e2 Q hQ, sub_zero]; exact one_mem _
  have hid : (⟨_, hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ Formalism.L2.DIV.idS D.host.F G.modul := by
    refine (Comparison₂.mem_idS_modul G _).2 fun w hw => ?_
    change Valued.v (cpt (D := D) w (toEAf D (1 - e))) ≤ _
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one, e1 w hw, sub_self, Valuation.map_zero]
    exact zero_le
  have h2 := smul_mem_of_idS (LS := LS) h𝔪 hz hid rfl
  have h3 := add_mem h1 h2
  rwa [← add_smul, add_sub_cancel, one_smul] at h3

end GlobalTheory.DepthShift

end

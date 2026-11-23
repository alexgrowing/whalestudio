import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SelfDualLoc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicSpanOfLatticeIffForallPlaceStatement

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.Dual

section Form

variable {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem add_right (x y y' : Fin n → A) : hform σ J x (y + y') = hform σ J x y + hform σ J x y' :=
  PI.SelfDualLoc.W.hform_add_right σ J x y y'

theorem smul_right (x : Fin n → A) (c : A) (y : Fin n → A) : hform σ J x (c • y) = c * hform σ J x y :=
  PI.SelfDualLoc.W.hform_smul_right σ J x c y

theorem add_left (x x' y : Fin n → A) : hform σ J (x + x') y = hform σ J x y + hform σ J x' y :=
  PI.SelfDualLoc.W.hform_add_left σ J x x' y

theorem smul_left (c : A) (x y : Fin n → A) : hform σ J (c • x) y = σ c * hform σ J x y :=
  PI.SelfDualLoc.W.hform_smul_left σ J c x y

theorem zero_left (y : Fin n → A) : hform σ J 0 y = 0 := PI.SelfDualLoc.W.hform_zero_left σ J y

theorem zero_right (x : Fin n → A) : hform σ J x 0 = 0 := PI.SelfDualLoc.W.hform_zero_right σ J x

theorem sum_right {ι : Type} (s : Finset ι) (x : Fin n → A) (f : ι → Fin n → A) :
    hform σ J x (∑ k ∈ s, f k) = ∑ k ∈ s, hform σ J x (f k) :=
  PI.SelfDualLoc.W.hform_sum_right σ J s x f

theorem sum_left {ι : Type} (s : Finset ι) (f : ι → Fin n → A) (y : Fin n → A) :
    hform σ J (∑ k ∈ s, f k) y = ∑ k ∈ s, hform σ J (f k) y :=
  PI.SelfDualLoc.W.hform_sum_left σ J s f y

end Form

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

omit [NumberField F] [NumberField E] in
theorem hR_incl (R : Type) [CommRing R] [Algebra F R] (a b : Fin n → E) :
    hR σ J R (fun i => inclE (F := F) R (a i)) (fun i => inclE (F := F) R (b i)) =
      inclE (F := F) R (hform (σ : E →+* E) J a b) :=
  PI.SelfDualLoc.W.hform_map (σ : E →+* E) J (sigR σ R) (inclE (F := F) R)
    (fun e => (PI.SelfDualLoc.W.sigR_inclE σ R e).symm) a b

omit [NumberField F] in
theorem mem_dualL (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ dualL σ J L ↔ ∀ x ∈ L, hform (σ : E →+* E) J x y ∈ intOE E := by
  refine ⟨fun hy => ?_, fun h => Submodule.subset_span h⟩
  intro x hx
  induction hy using Submodule.span_induction with
  | mem w hw => exact hw x hx
  | zero => rw [zero_right]; exact zero_mem _
  | add w w' _ _ h1 h2 => rw [add_right]; exact add_mem h1 h2
  | smul c w _ h1 =>
    rw [PI.SelfDualLoc.W.LB.smul_OE, smul_right]
    exact mul_mem ⟨c, rfl⟩ h1

theorem sig_int (R : Type) [CommRing R] [Algebra F R] (S : Subring R) (c : E ⊗[F] R)
    (hc : c ∈ tensInt (F := F) R (intOE E) S) : sigR σ R c ∈ tensInt (F := F) R (intOE E) S := by
  change c ∈ Subring.closure _ at hc
  induction hc using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
    · exact Subring.subset_closure (Or.inl ⟨⟨σ e, PI.SelfDualLoc.W.intOE_map σ he⟩,
        (PI.SelfDualLoc.W.sigR_tmul σ R e 1).symm⟩)
    · refine Subring.subset_closure (Or.inr ⟨⟨b, hb⟩, ?_⟩)
      have := PI.SelfDualLoc.W.sigR_tmul σ R 1 b
      rw [map_one] at this
      exact this.symm
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem test_gen (R : Type) [CommRing R] [Algebra F R] (S : Subring R) (L : Submodule (𝓞 E) (Fin n → E))
    (y : Fin n → E ⊗[F] R)
    (h : ∀ a ∈ L, hR σ J R (fun i => inclE (F := F) R (a i)) y ∈ tensInt (F := F) R (intOE E) S) :
    ∀ z ∈ latS (F := F) R (tensInt (F := F) R (intOE E) S) L, hR σ J R z y ∈ tensInt (F := F) R (intOE E) S := by
  intro z hz
  change z ∈ Submodule.span _ _ at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, ha, rfl⟩ := hw
    exact h a ha
  | zero => unfold hR; rw [zero_left]; exact zero_mem _
  | add w w' _ _ h1 h2 => unfold hR at h1 h2 ⊢; rw [add_left]; exact add_mem h1 h2
  | smul c w _ h1 =>
    unfold hR at h1 ⊢
    rw [Subring.smul_def, smul_left]
    exact mul_mem (sig_int σ R S c c.2) h1

theorem fwd (R : Type) [CommRing R] [Algebra F R] (S : Subring R) (L : Submodule (𝓞 E) (Fin n → E))
    (y : Fin n → E ⊗[F] R) (hy : y ∈ latS (F := F) R (tensInt (F := F) R (intOE E) S) (dualL σ J L)) :
    ∀ z ∈ latS (F := F) R (tensInt (F := F) R (intOE E) S) L, hR σ J R z y ∈ tensInt (F := F) R (intOE E) S := by
  apply test_gen
  intro a ha
  change y ∈ Submodule.span _ _ at hy
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, hb, rfl⟩ := hw
    rw [hR_incl]
    exact Subring.subset_closure (Or.inl ⟨⟨_, (mem_dualL σ J L b).1 hb a ha⟩, rfl⟩)
  | zero => unfold hR; rw [zero_right]; exact zero_mem _
  | add w w' _ _ h1 h2 => unfold hR at h1 h2 ⊢; rw [add_right]; exact add_mem h1 h2
  | smul c w _ h1 =>
    unfold hR at h1 ⊢
    rw [Subring.smul_def, smul_right]
    exact mul_mem c.2 h1

omit [NumberField F] [NumberField E] in
theorem nondeg (hJ : J.det ≠ 0) (x : Fin n → Fin n → E) (hx : Submodule.span E (Set.range x) = ⊤)
    (w : Fin n → E) (hw : ∀ i, hform (σ : E →+* E) J (x i) w = 0) : w = 0 := by
  have h1 : ∀ z : Fin n → E, hform (σ : E →+* E) J z w = 0 := by
    intro z
    have hz : z ∈ Submodule.span E (Set.range x) := hx ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem a ha => obtain ⟨i, rfl⟩ := ha; exact hw i
    | zero => exact zero_left _ _ _
    | add a b _ _ h1 h2 => rw [add_left, h1, h2, add_zero]
    | smul c a _ h1 => rw [smul_left, h1, mul_zero]
  apply Matrix.eq_zero_of_mulVec_eq_zero hJ
  ext i
  have := h1 (Pi.single i 1)
  unfold hform at this
  rw [Finset.sum_eq_single i] at this
  · simpa [Matrix.mulVec, dotProduct] using this
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

theorem exists_dual_basis (hJ : J.det ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsLat L)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (x y : Fin n → Fin n → E) (s : 𝓞 F), s ∉ v.asIdeal ∧ (∀ i, x i ∈ L) ∧
      (∀ i j, hform (σ : E →+* E) J (x i) (y j) = if i = j then 1 else 0) ∧
      (∀ w : Fin n → E, ∃ c : Fin n → E, w = ∑ j, c j • y j) ∧
      ∀ j, algebraMap F E (s : F) • y j ∈ dualL σ J L := by
  obtain ⟨x, s, hs, hxL, hxs⟩ := PI.SelfDualLoc.W.locBasis F E n v L hL.1 hL.2
  have hsE : algebraMap F E (s : F) ≠ 0 := PI.SelfDualLoc.W.LB.algF_ne_zero v hs
  have hxspan : Submodule.span E (Set.range x) = ⊤ := by
    rw [eq_top_iff, ← hL.2, Submodule.span_le]
    intro z hz
    obtain ⟨a, ha⟩ := hxs z hz
    have hz' : z = (algebraMap F E (s : F))⁻¹ • ∑ i, ((a i : 𝓞 E) : E) • x i := by
      rw [← ha, smul_smul, inv_mul_cancel₀ hsE, one_smul]
    rw [hz']
    exact Submodule.smul_mem _ _
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  obtain ⟨yb, hdu, hysp⟩ := PI.SelfDualLoc.W.dualBasis F E n σ J x hxspan (nondeg σ J hJ x hxspan)
  have hdu' : ∀ i j, hform (σ : E →+* E) J (x i) (yb j) = if i = j then 1 else 0 := hdu
  refine ⟨x, yb, s, hs, hxL, hdu', hysp, fun j => ?_⟩
  rw [mem_dualL]
  intro z hz
  obtain ⟨a, ha⟩ := hxs z hz
  have hsz : hform (σ : E →+* E) J (algebraMap F E (s : F) • z) (yb j) =
      algebraMap F E (s : F) * hform (σ : E →+* E) J z (yb j) := by
    rw [smul_left]
    congr 1
    exact σ.commutes _
  rw [smul_right, ← hsz, ha, sum_left]
  simp only [smul_left, hdu', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact PI.SelfDualLoc.W.intOE_map σ ⟨a j, rfl⟩

theorem isLat_dual (hJ : J.det ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsLat L) : IsLat (dualL σ J L) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩
  obtain ⟨x, y, s, hs, hxL, hdu, hysp, hyL⟩ := exists_dual_basis σ J hJ L hL v
  have hsE : algebraMap F E (s : F) ≠ 0 := PI.SelfDualLoc.W.LB.algF_ne_zero v hs
  constructor
  · have hle : dualL σ J L ≤ Submodule.span (𝓞 E) (Set.range y) := by
      intro w hw
      obtain ⟨c, hc⟩ := hysp w
      have hci : ∀ i, c i ∈ intOE E := by
        intro i
        have := (mem_dualL σ J L w).1 hw (x i) (hxL i)
        rw [hc, sum_right] at this
        simpa [smul_right, hdu] using this
      choose a ha using hci
      rw [hc]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [← ha j]
      have := Submodule.smul_mem (Submodule.span (𝓞 E) (Set.range y)) (a j) (Submodule.subset_span ⟨j, rfl⟩)
      rwa [PI.SelfDualLoc.W.LB.smul_OE] at this
    have hfg : (Submodule.span (𝓞 E) (Set.range y)).FG := Submodule.fg_span (Set.finite_range y)
    exact Module.Finite.iff_fg.mpr (hfg.of_le hle)
  · rw [eq_top_iff]
    intro w _
    obtain ⟨c, hc⟩ := hysp w
    rw [hc]
    refine Submodule.sum_mem _ fun j _ => ?_
    have := Submodule.smul_mem (Submodule.span E (dualL σ J L : Set (Fin n → E))) (c j * (algebraMap F E (s : F))⁻¹)
      (Submodule.subset_span (hyL j))
    rwa [smul_smul, mul_assoc, inv_mul_cancel₀ hsE, mul_one] at this

theorem bwd_loc (hJ : J.det ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsLat L)
    (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → E ⊗[F] v.adicCompletion F)
    (hy : ∀ a ∈ L, hR σ J (v.adicCompletion F) (fun i => inclE (F := F) (v.adicCompletion F) (a i)) y ∈ intV E v) :
    y ∈ loc v (dualL σ J L) := by
  obtain ⟨x, yb, s, hs, hxL, hdu, hysp, hyL⟩ := exists_dual_basis σ J hJ L hL v
  obtain ⟨us, husO, hus⟩ := PI.SelfDualLoc.W.unitLoc F E v s hs
  have husO' : us ∈ intV E v := husO
  have hus' : inclE (F := F) (v.adicCompletion F) (algebraMap F E (s : F)) * us = 1 := hus
  choose c hc using fun k : Fin n => hysp (Pi.single k 1 : Fin n → E)
  obtain ⟨C, hyC⟩ : ∃ C : Fin n → E ⊗[F] v.adicCompletion F,
      y = ∑ j, C j • (fun i => inclE (F := F) (v.adicCompletion F) (yb j i)) := by
    refine ⟨fun j => ∑ k, y k * inclE (F := F) (v.adicCompletion F) (c k j), ?_⟩
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    have h2 : ∀ k, ∑ j, y k * inclE (F := F) (v.adicCompletion F) (c k j) *
        inclE (F := F) (v.adicCompletion F) (yb j i) =
        y k * inclE (F := F) (v.adicCompletion F) ((Pi.single k 1 : Fin n → E) i) := by
      intro k
      rw [hc k]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum,
        mul_assoc]
    simp only [h2]
    simp [Pi.single_apply, apply_ite (inclE (F := F) (v.adicCompletion F))]
  have hCO : ∀ j, C j ∈ intV E v := by
    intro j
    have h1 := hy (x j) (hxL j)
    have h3 : hR σ J (v.adicCompletion F) (fun i => inclE (F := F) (v.adicCompletion F) (x j i)) y = C j := by
      have h4 := fun k => hR_incl σ J (v.adicCompletion F) (x j) (yb k)
      rw [hyC]
      unfold hR at h4 ⊢
      rw [sum_right]
      simp only [smul_right, h4, hdu, apply_ite (inclE (F := F) (v.adicCompletion F)),
        map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [h3] at h1
    exact h1
  rw [hyC]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hg : (fun i => inclE (F := F) (v.adicCompletion F)
      ((algebraMap F E (s : F) • yb j) i)) ∈ loc v (dualL σ J L) :=
    Submodule.subset_span ⟨_, hyL j, rfl⟩
  have hmem := Submodule.smul_mem _ (⟨C j * us, mul_mem (hCO j) husO'⟩ : intV E v) hg
  rw [Subring.smul_def] at hmem
  convert hmem using 1
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  linear_combination (-(C j * inclE (F := F) (v.adicCompletion F) (yb j i))) * hus'

omit [NumberField E] in
theorem prV_tmul (v : HeightOneSpectrum (𝓞 F)) (e : E) (a : Ad F) :
    prV (E := E) v (e ⊗ₜ[F] a) = e ⊗ₜ[F] (a v) := rfl

theorem prV_int (v : HeightOneSpectrum (𝓞 F)) (c : E ⊗[F] Ad F) (hc : c ∈ OAd F E) :
    prV (E := E) v c ∈ intV E v := by
  change c ∈ Subring.closure _ at hc
  induction hc using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
    · exact Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨⟨b v, hb v⟩, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

omit [NumberField E] in
theorem prV_hR (v : HeightOneSpectrum (𝓞 F)) (a : Fin n → E) (x : Fin n → E ⊗[F] Ad F) :
    prV (E := E) v (hR σ J (Ad F) (fun i => inclE (F := F) (Ad F) (a i)) x) =
      hR σ J (v.adicCompletion F) (fun i => inclE (F := F) (v.adicCompletion F) (a i)) (prVec v x) := by
  unfold hR hform prVec
  simp only [map_sum, map_mul, Matrix.map_apply]
  rfl

end GlobalTheory.St.G.Dual

namespace GlobalTheory.St.G

theorem dualL_local_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat (dualL cm.sig J L) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E ⊗[F] v.adicCompletion F), x ∈ loc v (dualL cm.sig J L) ↔ ∀ z ∈ loc v L, hR cm.sig J (v.adicCompletion F) z x ∈ intV E v) ∧ ∀ x : Fin n → E ⊗[F] Ad F, x ∈ hat F (dualL cm.sig J L) ↔ ∀ z ∈ hat F L, hR cm.sig J (Ad F) z x ∈ OAd F E := by
  intro F E _ _ _ _ _ _ cm n J _ hJ L hL
  have hD := Dual.isLat_dual cm.sig J hJ L hL
  refine ⟨hD, fun v x => ⟨fun hx => Dual.fwd cm.sig J _ _ L x hx, fun h => ?_⟩,
    fun x => ⟨fun hx => Dual.fwd cm.sig J _ _ L x hx, fun h => ?_⟩⟩
  · exact Dual.bwd_loc cm.sig J hJ L hL v x fun a ha => h _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  · rw [GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place F E n _ hD]
    intro v
    refine Dual.bwd_loc cm.sig J hJ L hL v _ fun a ha => ?_
    rw [← Dual.prV_hR]
    exact Dual.prV_int v _ (h _ (Submodule.subset_span ⟨a, ha, rfl⟩))

end GlobalTheory.St.G

end

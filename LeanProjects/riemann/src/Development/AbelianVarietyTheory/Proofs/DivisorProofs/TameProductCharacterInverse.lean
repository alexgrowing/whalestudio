import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.GeoActCompare.TameAB

variable {D : D7}

abbrev cFin (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  sigR (Af D.host.F) D.sp.cm.sig

theorem cFin_tmul (a : Af D.host.F) (e : D.host.E) :
    cFin D (a ⊗ₜ e) = a ⊗ₜ IsCMField.complexConj D.host.E e := rfl

theorem finPart_cA (z : AE D) : finPart D (cA D z) = cFin D (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy]
  | tmul a e => rfl

theorem cFin_mem_intAE (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ intAE D) : cFin D z ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, x, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨a, ha, H.bar x, by rw [cFin_tmul, H.bar_eq]⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

theorem swapAE_mem {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) : swapAE D z ∈ LatticeBasisLifts.OAf D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, x, rfl⟩ := hw
    have h1 : (1 : D.host.E) ⊗ₜ[D.host.F] a ∈ LatticeBasisLifts.OAf D :=
      Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
    have h2 : (x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F) ∈ LatticeBasisLifts.OAf D :=
      Subring.subset_closure (Or.inl ⟨⟨x, x, rfl⟩, rfl⟩)
    have := mul_mem h2 h1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
    exact this
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

theorem swapAE_idealHat {I : Ideal (𝓞 D.host.E)} {z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ LevelLiftConditions.idealHat D I) :
    ∃ s ∈ Formalism.L2.DIV.idS D.host.F I, ((s : LatticeBasisLifts.OAf D) : EAf D) = swapAE D z := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨b, hb, y, hy, rfl⟩ := hw
    refine ⟨Formalism.L2.DIV.oToS D.host.F D.host.E b * ⟨_, swapAE_mem hy⟩,
      Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb), ?_⟩
    rw [RingHom.map_mul]
    rfl
  | zero => exact ⟨0, zero_mem _, by rw [RingHom.map_zero]; rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, e⟩ := hx
    obtain ⟨t, ht, e'⟩ := hy
    exact ⟨s + t, add_mem hs ht, by rw [RingHom.map_add, ← e, ← e']; rfl⟩
  | neg x _ hx =>
    obtain ⟨s, hs, e⟩ := hx
    exact ⟨-s, neg_mem hs, by rw [RingHom.map_neg, ← e]; rfl⟩

theorem bar_bar (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (a : 𝓞 D.host.E) : H.bar (H.bar a) = a :=
  Subtype.ext (by
    have h := H.bar_eq (H.bar a)
    rw [H.bar_eq a, IsCMField.complexConj_apply_apply] at h
    exact h)

theorem cFin_idealHat (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {I : Ideal (𝓞 D.host.E)}
    {z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ LevelLiftConditions.idealHat D (I.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E))) :
    cFin D z ∈ LevelLiftConditions.idealHat D I := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨b, hb, y, hy, rfl⟩ := hw
    obtain ⟨c, hc, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)
      H.bar.surjective).1 hb
    refine AddSubgroup.subset_closure ⟨c, hc, _, cFin_mem_intAE H hy, ?_⟩
    rw [RingHom.map_mul, cFin_tmul, ← H.bar_eq]
    exact congrArg (fun t : 𝓞 D.host.E => ((1 : Af D.host.F) ⊗ₜ[D.host.F] (t : D.host.E)) * cFin D y) (bar_bar H c)
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

theorem exists_unit_subring {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (S : Subring B) (x : Aˣ)
    (h : f (x : A) ∈ S) (h' : f ((x⁻¹ : Aˣ) : A) ∈ S) : ∃ u : Sˣ, ((u : S) : B) = f (x : A) :=
  ⟨⟨⟨_, h⟩, ⟨_, h'⟩, Subtype.ext (by simp [← map_mul]), Subtype.ext (by simp [← map_mul])⟩, rfl⟩

theorem resS_eq_of_cong {I : Ideal (𝓞 D.host.E)} (w : Formalism.L2.DIV.Pl D.host.E) (hw : I ≤ w.asIdeal)
    (s : LatticeBasisLifts.OAf D) (z : Af D.host.F ⊗[D.host.F] D.host.E) (hs : (s : EAf D) = swapAE D z) (a : 𝓞 D.host.E)
    (hz : z - (1 : Af D.host.F) ⊗ₜ (a : D.host.E) ∈ LevelLiftConditions.idealHat D I) :
    Formalism.L2.DIV.resS D.host.F w s = Ideal.Quotient.mk w.asIdeal a := by
  obtain ⟨t, ht, e⟩ := swapAE_idealHat hz
  rw [resS_eq_resI, resI_eq_mk_iff]
  have : s - Formalism.L2.DIV.oToS D.host.F D.host.E a = t := by
    apply Subtype.ext
    rw [e, RingHom.map_sub, ← hs]
    rfl
  rw [this]
  exact Ideal.map_mono hw ht

theorem isInvTame_chiProd : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (hle : ∀ w : ↥Pg, l.Mb ≤ w.1.asIdeal) (K : Type) [Field K] (σ : K →+* ℂ) (μ : (AE D)ˣ →* Circle) (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* Kˣ), LatticeBasisLifts.IsInvTame σ Pg μ χ → LevelLiftConditions.IsInvTame σ l.Mb (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) μ (chiProd hle χ) := by
  intro D H l Pg hle K _ σ μ χ h x hx u ub hub h1 h2
  obtain ⟨hinf, hi, hi'⟩ := hx
  obtain ⟨U, hU⟩ := exists_unit_subring ((swapAE D).comp (finPart D)) (LatticeBasisLifts.OAf D) x (swapAE_mem hi) (swapAE_mem hi')
  obtain ⟨Ub, hUb⟩ := exists_unit_subring ((swapAE D).comp ((cFin D).comp (finPart D))) (LatticeBasisLifts.OAf D) x
    (swapAE_mem (cFin_mem_intAE H hi)) (swapAE_mem (cFin_mem_intAE H hi'))
  have key := h x U Ub hinf hU (by rw [finPart_cA]; exact hUb)
  have e1 : ∀ w : ↥Pg, Units.map (Formalism.L2.DIV.resS D.host.F w.1).toMonoidHom U =
      Units.map (Ideal.Quotient.factor (hle w)).toMonoidHom ub := fun w => Units.ext (by
    have := resS_eq_of_cong w.1 (hle w) U _ hU u h1
    refine this.trans ?_
    change _ = Ideal.Quotient.factor (hle w) (ub : 𝓞 D.host.E ⧸ l.Mb)
    rw [hub]
    rfl)
  have e2 : ∀ w : ↥Pg, Units.map (Formalism.L2.DIV.resS D.host.F w.1).toMonoidHom Ub = 1 := fun w => Units.ext (by
    have h3 := cFin_idealHat H h2
    rw [RingHom.map_sub, cFin_tmul, ← H.bar_eq, map_one] at h3
    exact resS_eq_of_cong w.1 (hle w) Ub _ hUb 1 h3)
  rw [key, chiProd_apply, Units.coe_prod, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun w _ => ?_
  rw [e1, e2, map_one, Units.val_one, map_one, mul_one]
  exact mul_inv_cancel₀ ((map_ne_zero σ).2 (Units.ne_zero _))

end GlobalTheory.GeoActCompare.TameAB

end

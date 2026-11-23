import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.SharpRestriction.GlobalSchurBounds.FormalGroupJets
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds
import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.SharpRestriction.GlobalSchurBounds.KernelEntryData
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Formalism.LocalRingCardinality.SpanPowerMembership

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory.Inhab

open Formalism.BasicNotions NumberField

theorem GaugeFam_nonempty (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) :
    Nonempty (GenusMassVolumes.GaugeFam F E σ) := ⟨⟨fun _ _ => 0⟩⟩

theorem Tor_nonempty (D : D7) : Nonempty (Formalism.MainNotions.TaylorLogMetric.Tor D) := ⟨Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK 1⟩

theorem Shape_nonempty : Nonempty Formalism.MainNotions.KernelEntryData.Shape := ⟨⟨1, fun _ => 2, 1, 1⟩⟩

theorem IsPart_zero (n' r0 : ℕ) : Formalism.MainNotions.KernelEntryData.IsPart (n' := n') r0 (fun _ _ => 0) :=
  ⟨fun _ _ => le_rfl, fun _ _ _ => le_rfl, fun _ _ _ => rfl⟩

theorem lam_nonempty (p : ℕ) [Fact p.Prime] : Nonempty (Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) := by
  have : Algebra.IsAlgebraic ℚ Formalism.MainNotions.TaylorLogMetric.Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  have f : Formalism.MainNotions.TaylorLogMetric.Qbar →ₐ[ℚ] PadicAlgCl p := IsAlgClosed.lift
  exact ⟨(algebraMap (PadicAlgCl p) ℂ_[p]).comp (f : Formalism.MainNotions.TaylorLogMetric.Qbar →+* PadicAlgCl p)⟩

theorem local_datum_nonempty (p : ℕ) [Fact p.Prime] : Nonempty (Formalism.MainNotions.GL3Theta.G1 p) := by
  obtain ⟨lam⟩ := lam_nonempty p
  exact ⟨⟨lam, ⊥, 1, 0, 0⟩⟩

def ChiEx (D : D7) : Prop := ∃ χ, Formalism.MainNotions.TaylorLogMetric.IsChi D χ

theorem theta_family_nonempty (D : D7) (h : ChiEx D) : Nonempty (Formalism.MainNotions.product_first_zeroth_parts.Th22 D) := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (Formalism.MainNotions.TaylorLogMetric.discr (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK 1))
    (by norm_num : 0 < 12)
  obtain ⟨χ, hχ⟩ := h
  exact ⟨⟨D.host.ccK, δ, χ, fun _ _ _ _ _ => 0, Formalism.MainNotions.GlobalTheoryTheory.jnt_ccK_curve D, hδ, hχ⟩⟩

theorem ChiEx_of_pinned (D : D7) (idl : D.Dt ⧸ D.UO → Formalism.MainNotions.TaylorLogMetric.IdE D) (h : Formalism.MainNotions.TaylorLogMetric.RelDetPinned D idl) :
    ChiEx D := ⟨_, Formalism.MainNotions.TaylorLogMetric.isChi_chiRec D idl h⟩

theorem HeckeU_nonempty_even (D : D7) (N : ℕ) (h : Even N) : Nonempty (Formalism.MainNotions.StandardLatticesGL3.HeckeU D N) :=
  ⟨{ f := 1
     n := fun _ => 0
     unitary := fun _ => by simp
     cont := ⟨1, one_pos, fun _ _ _ => rfl⟩
     aut := fun _ => by simp
     norm := fun _ => rfl
     par := fun _ => by simpa using h
     unr := fun _ _ _ => rfl }⟩

section PosSec

open Formalism.FrobeniusOrbits

def prPsi (e : Formalism.HC.Frame) : e.GG →* e.GG where
  toFun g := ((g.1.1 * g.1.2, 1), g.2)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp [mul_mul_mul_comm]
    · simp
    · simp

theorem prPsi_mem (e : Formalism.HC.Frame) (g : e.GG) : prPsi e g ∈ e.Psi := (Formalism.HC.Frame.mem_Psi_iff _).2 rfl

theorem prPsi_of_mem (e : Formalism.HC.Frame) (g : e.GG) (h : g ∈ e.Psi) : prPsi e g = g := by
  have h2 : g.1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff g).1 h
  obtain ⟨⟨a, b⟩, c⟩ := g
  simp only at h2
  subst h2
  simp [prPsi]

theorem prPsi_of_not_mem (e : Formalism.HC.Frame) (g : e.GG) (h : g ∉ e.Psi) : prPsi e g = e.cc * g := by
  have h2 : g.1.2 ≠ 1 := fun h' => h ((Formalism.HC.Frame.mem_Psi_iff g).2 h')
  obtain ⟨⟨a, b⟩, c⟩ := g
  simp only at h2
  have hb : b = -1 := (Int.units_eq_one_or b).resolve_left h2
  subst hb
  simp [prPsi, Formalism.HC.Frame.cc, c0]

theorem prPsi_eq_one (e : Formalism.HC.Frame) (g : e.GG) (h : prPsi e g = 1) : g = 1 ∨ g = e.cc := by
  by_cases hg : g ∈ e.Psi
  · left; rwa [prPsi_of_mem e g hg] at h
  · right
    rw [prPsi_of_not_mem e g hg] at h
    have hcc : e.cc * e.cc = 1 := by ext <;> simp [Formalism.HC.Frame.cc, c0]
    calc g = (e.cc * e.cc) * g := by rw [hcc, one_mul]
      _ = e.cc * (e.cc * g) := mul_assoc _ _ _
      _ = e.cc := by rw [h, mul_one]

theorem letterOf_eq (D : D7) (φ : D.R.GG) {d : ℕ} (τ0 : D.what₂.Tau) (s : ZMod d) :
    ((D.eTau (Formalism.MainNotions.TaylorLogMetric.letterOf D φ τ0 s) : D.R.Psi) : D.R.GG) =
      (D.eTau τ0 : D.R.GG) * prPsi D.R.toFrame φ ^ s.val := by
  have key : prPsi D.R.toFrame (Formalism.MainNotions.TaylorLogMetric.posG D φ τ0 s) = (D.eTau τ0 : D.R.GG) * prPsi D.R.toFrame φ ^ s.val := by
    unfold Formalism.MainNotions.TaylorLogMetric.posG
    rw [map_mul, map_pow, prPsi_of_mem _ _ (D.eTau τ0).2]
  rw [← key]
  unfold Formalism.MainNotions.TaylorLogMetric.letterOf
  by_cases h : Formalism.MainNotions.TaylorLogMetric.posG D φ τ0 s ∈ D.R.Psi
  · rw [dif_pos h, Equiv.apply_symm_apply, prPsi_of_mem _ _ h]
  · have h' : D.R.cc * Formalism.MainNotions.TaylorLogMetric.posG D φ τ0 s ∈ D.R.Psi := by
      rw [← prPsi_of_not_mem _ _ h]; exact prPsi_mem _ _
    rw [dif_neg h, dif_pos h', Equiv.apply_symm_apply, prPsi_of_not_mem _ _ h]

def IsFrobOf (D : D7) (p : ℕ) (φ : D.R.GG) : Prop :=
  ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})],
    IsArithFrobAt ℤ (D.host.sigmaOf φ) P

theorem orderOf_prPsi (e : Formalism.HC.Frame) (φ : e.GG) (hc : e.cc ∉ Subgroup.zpowers φ) :
    orderOf (prPsi e φ) = orderOf φ := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [← map_pow]
  constructor
  · intro h
    rcases prPsi_eq_one e _ h with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ Subgroup.npow_mem_zpowers φ n) hc
  · intro h; rw [h, map_one]

theorem Pos_nonempty (D : D7) (p : ℕ) (φ : D.R.GG) (hφ : IsFrobOf D p φ)
    (hc : D.R.cc ∉ Subgroup.zpowers φ) : Nonempty (Formalism.MainNotions.TaylorLogMetric.Pos D p (orderOf φ)) := by
  classical
  have : Finite (D.R.Psi) := Finite.of_equiv _ D.eTau
  set ψ : D.R.Psi := ⟨prPsi D.R.toFrame φ, prPsi_mem _ _⟩ with hψ
  have hfin : IsOfFinOrder ψ := isOfFinOrder_of_finite ψ
  have hord : orderOf ψ = orderOf φ := by
    rw [← orderOf_prPsi _ φ hc, ← Subgroup.orderOf_coe ψ]
  have hpos : 0 < orderOf φ := hord ▸ hfin.orderOf_pos
  have : NeZero (orderOf φ) := ⟨hpos.ne'⟩
  obtain ⟨S, hS, -⟩ := (Subgroup.zpowers ψ).exists_isComplement_left 1
  have hval : ∀ (τ0 : D.what₂.Tau) (s : ZMod (orderOf φ)),
      D.eTau (Formalism.MainNotions.TaylorLogMetric.letterOf D φ τ0 s) = D.eTau τ0 * ψ ^ s.val := by
    intro τ0 s
    apply Subtype.ext
    rw [letterOf_eq]; simp [hψ]
  refine ⟨⟨φ, hφ, rfl, Finset.univ.filter (fun τ => D.eTau τ ∈ S), ?_, ?_⟩⟩
  · rintro ⟨⟨v, hv⟩, s⟩ ⟨⟨v', hv'⟩, s'⟩ h
    have hv1 : D.eTau v ∈ S := (Finset.mem_filter.1 hv).2
    have hv2 : D.eTau v' ∈ S := (Finset.mem_filter.1 hv').2
    have h1 : D.eTau v * ψ ^ s.val = D.eTau v' * ψ ^ s'.val := by
      rw [← hval, ← hval]; exact congrArg D.eTau h
    have h2 := @hS.1 (⟨D.eTau v, hv1⟩, ⟨ψ ^ s.val, Subgroup.npow_mem_zpowers ψ _⟩)
      (⟨D.eTau v', hv2⟩, ⟨ψ ^ s'.val, Subgroup.npow_mem_zpowers ψ _⟩) h1
    have h3 : D.eTau v = D.eTau v' := congrArg (fun x => (x.1 : D.R.Psi)) h2
    have h4 : ψ ^ s.val = ψ ^ s'.val := congrArg (fun x => (x.2 : D.R.Psi)) h2
    have h5 : s.val = s'.val :=
      pow_injOn_Iio_orderOf (by simpa [hord] using ZMod.val_lt s) (by simpa [hord] using ZMod.val_lt s') h4
    have h6 : v = v' := D.eTau.injective h3
    subst h6
    rw [ZMod.val_injective _ h5]
  · intro τ
    obtain ⟨⟨⟨a, ha⟩, ⟨z, hz⟩⟩, haz⟩ := hS.2 (D.eTau τ)
    have haz' : a * z = D.eTau τ := haz
    obtain ⟨n, hn, hnz⟩ := (hfin.mem_zpowers_iff_mem_range_orderOf.1 hz |> Finset.mem_image.1)
    have hn' : n < orderOf φ := by simpa [hord] using hn
    refine ⟨(⟨D.eTau.symm a, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using ha⟩⟩, (n : ZMod (orderOf φ))), ?_⟩
    apply D.eTau.injective
    rw [hval]
    simp only [Equiv.apply_symm_apply, ZMod.val_natCast_of_lt hn', hnz, haz']

theorem Pos_cc_not_mem (D : D7) (p d : ℕ) (Po : Formalism.MainNotions.TaylorLogMetric.Pos D p d) : D.R.cc ∉ Subgroup.zpowers Po.φ := by
  classical
  intro hc
  have : Finite (D.R.Psi) := Finite.of_equiv _ D.eTau
  have : Finite (D.R.GG) := by
    have : Finite (D.R.MA) := inferInstance
    infer_instance
  have hfin : IsOfFinOrder Po.φ := isOfFinOrder_of_finite _
  have hpos : 0 < d := Po.d_eq ▸ hfin.orderOf_pos
  have : NeZero d := ⟨hpos.ne'⟩
  obtain ⟨n, hn, hnz⟩ := (hfin.mem_zpowers_iff_mem_range_orderOf.1 hc |> Finset.mem_image.1)
  have hn' : n < d := by simpa [Po.d_eq] using hn
  obtain ⟨⟨v, s⟩, -⟩ := Po.bij.2 (D.eTau.symm 1)
  have h0 : Formalism.MainNotions.TaylorLogMetric.letterOf D Po.φ v.1 (n : ZMod d) = Formalism.MainNotions.TaylorLogMetric.letterOf D Po.φ v.1 (0 : ZMod d) := by
    apply D.eTau.injective
    apply Subtype.ext
    rw [letterOf_eq, letterOf_eq, ZMod.val_natCast_of_lt hn', ZMod.val_zero, ← map_pow, hnz]
    have : prPsi D.R.toFrame (D.R.cc) = 1 := by ext <;> simp [prPsi, Formalism.HC.Frame.cc, c0]
    rw [this, pow_zero]
  have h1 := @Po.bij.1 (v, (n : ZMod d)) (v, 0) h0
  have h2 : (n : ZMod d) = 0 := congrArg Prod.snd h1
  have h3 : n = 0 := by
    have := congrArg ZMod.val h2
    rwa [ZMod.val_natCast_of_lt hn', ZMod.val_zero] at this
  subst h3
  rw [pow_zero] at hnz
  have : (D.R.cc).1.1 = 1 := by rw [← hnz]; rfl
  simp [Formalism.HC.Frame.cc, c0] at this

end PosSec

section Std

variable (D : D7)

theorem mem_stdL {N : ℕ} (x : Fin N → D.host.E) :
    x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N ↔ ∀ i, x i ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  unfold Formalism.MainNotions.StandardLatticesGL3.stdL
  simp [Submodule.mem_pi, Submodule.mem_one]

theorem single_mem_stdL {N : ℕ} (a : Fin N) : (Pi.single a 1 : Fin N → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
  rw [mem_stdL]
  intro i
  by_cases h : i = a
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem star_mem_range (x : D.host.E) (h : x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    (letI := D.host.cmStar; star x) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  let _ := D.host.cmStar
  have h1 : IsIntegral ℤ x := (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).2 h
  have h2 : IsIntegral ℤ (starRingEnd D.host.E x) := map_isIntegral_int (starRingEnd D.host.E) h1
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1 h2

theorem stdL_isSD (N : ℕ) : (letI := D.host.cmStar; IsSDLat D.host.E N (Formalism.MainNotions.StandardLatticesGL3.stdL D N)) := by
  let _ := D.host.cmStar
  refine ⟨?_, ?_, ?_⟩
  · have : Formalism.MainNotions.StandardLatticesGL3.stdL D N =
        Submodule.span (𝓞 D.host.E) (Set.range fun a : Fin N => (Pi.single a 1 : Fin N → D.host.E)) := by
      apply le_antisymm
      · intro x hx
        rw [mem_stdL] at hx
        choose c hc using hx
        have : x = ∑ a, c a • (Pi.single a 1 : Fin N → D.host.E) := by
          funext i
          simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hc]
        rw [this]
        exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        exact single_mem_stdL D a
    rw [this]
    exact Submodule.fg_span (Set.finite_range _)
  · rw [Submodule.eq_top_iff']
    intro x
    have : x = ∑ a, x a • (Pi.single a 1 : Fin N → D.host.E) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_stdL D a))
  · intro y
    constructor
    · intro hy x hx
      rw [mem_stdL] at hx hy
      unfold stdH
      exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (star_mem_range D _ (hx i)) (hy i)
    · intro h
      rw [mem_stdL]
      intro i
      have := h _ (single_mem_stdL D i)
      unfold stdH at this
      simpa [Pi.single_apply, apply_ite star] using this

theorem SDLat_nonempty (N : ℕ) : (letI := D.host.cmStar; Nonempty (SDLat D.host.E N)) :=
  ⟨⟨_, stdL_isSD D N⟩⟩

theorem Adm_std (N N' : ℕ) (h : Even N) (h' : Even N') :
    Formalism.MainNotions.TaylorLogMetric.admitted D N N' (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') :=
  ⟨h, h', stdL_isSD D N, stdL_isSD D N'⟩

theorem standard_integral_lattice_exists (N : ℕ) : (letI := D.host.cmStar; ∃ L0 : SDLat D.host.E N,
    ∀ x : Fin N → D.host.E, x ∈ L0.1 ↔ ∀ k, IsIntegral ℤ (x k)) := by
  refine ⟨⟨_, stdL_isSD D N⟩, fun x => ?_⟩
  rw [mem_stdL]
  exact forall_congr' fun k => (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).symm

theorem LocBasisW_std {p : ℕ} [Fact p.Prime] (ρ : D.host.E → ℂ_[p]) (hρ : ‖ρ 1‖ = 1) (N : ℕ) :
    Formalism.MainNotions.TaylorLogMetric.LocBasisW D ρ (Formalism.MainNotions.StandardLatticesGL3.stdL D N) 1 := by
  refine ⟨by simp, fun a => ⟨1, by simpa using hρ, ?_⟩, fun x hx => ⟨1, by simpa using hρ, ?_⟩⟩
  · rw [one_smul, Matrix.transpose_one]
    have : (1 : Matrix (Fin N) (Fin N) D.host.E) a = Pi.single a 1 := by
      funext j; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [this]; exact single_mem_stdL D a
  · rw [mem_stdL] at hx
    choose c hc using hx
    refine ⟨c, ?_⟩
    funext i
    simp [Finset.sum_apply, Matrix.one_apply, Algebra.smul_def, hc]

theorem OrthoBasisW_std {p : ℕ} [Fact p.Prime] (ρ : D.host.E → ℂ_[p]) (hρ : ‖ρ 1‖ = 1) (N : ℕ) :
    Formalism.MainNotions.TaylorLogMetric.OrthoBasisW D ρ (Formalism.MainNotions.StandardLatticesGL3.stdL D N) 1 :=
  ⟨LocBasisW_std D ρ hρ N, by simp⟩

theorem lamC_one {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) : Formalism.MainNotions.TaylorLogMetric.lamC lam 1 = 1 := by
  unfold Formalism.MainNotions.TaylorLogMetric.lamC
  rw [dif_pos (one_mem _)]
  exact map_one lam

theorem posEmb_one {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (φ : D.R.GG) {d : ℕ}
    (τ0 : D.what₂.Tau) (s : ZMod d) : ‖Formalism.MainNotions.TaylorLogMetric.posEmb D lam φ τ0 s 1‖ = 1 := by
  unfold Formalism.MainNotions.TaylorLogMetric.posEmb
  rw [map_one, lamC_one, norm_one]

theorem tauEmb_one {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) :
    ‖Formalism.MainNotions.TaylorLogMetric.tauEmb D lam τ 1‖ = 1 := by
  unfold Formalism.MainNotions.TaylorLogMetric.tauEmb
  rw [map_one, lamC_one, norm_one]

end Std

section KernelEntryData

variable (p : ℕ) [Fact p.Prime]

theorem mem_unit_ball_iff_norm_le_one (x : ℂ_[p]) : x ∈ Formalism.MainNotions.KernelEntryData.valuationRingCp p ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro hx
    let B : Subring ℂ_[p] :=
      { carrier := {x | ‖x‖ ≤ 1}
        mul_mem' := fun {a b} ha hb => by
          show ‖a * b‖ ≤ 1
          rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
        one_mem' := by show ‖(1 : ℂ_[p])‖ ≤ 1; rw [norm_one]
        add_mem' := fun {a b} ha hb => (PadicComplex.isNonarchimedean p a b).trans (max_le ha hb)
        zero_mem' := by show ‖(0 : ℂ_[p])‖ ≤ 1; rw [norm_zero]; exact zero_le_one
        neg_mem' := fun {a} ha => by show ‖-a‖ ≤ 1; rw [norm_neg]; exact ha }
    exact (Subring.closure_le (t := B)).2 (fun y hy => hy) hx
  · intro hx; exact Subring.subset_closure hx

theorem norm_p_Cp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]

theorem valuation_ring_unit_ball : Formalism.MainNotions.KernelEntryData.ValR p (Formalism.MainNotions.KernelEntryData.valuationRingCp p) := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [mem_unit_ball_iff_norm_le_one, mem_unit_ball_iff_norm_le_one, norm_inv]
    rcases le_total ‖x‖ 1 with h | h
    · exact Or.inl h
    · exact Or.inr (inv_le_one_of_one_le₀ h)
  · rw [mem_unit_ball_iff_norm_le_one, norm_inv, norm_p_Cp, inv_inv, not_le]
    exact_mod_cast (Fact.out : p.Prime).one_lt

theorem setting_nonempty_even_orbits (h5 : 5 ≤ p) (Sh : Formalism.MainNotions.KernelEntryData.Shape) (he : ∀ v, Even (Sh.n' v)) (h2 : ∀ v, 2 ≤ Sh.n' v) :
    ∃ vp : ℂ_[p], Formalism.MainNotions.KernelEntryData.HidaSetting p (Formalism.MainNotions.KernelEntryData.valuationRingCp p) Sh Sh.r0 (fun _ _ _ => 0) vp := by
  have hpos : 0 < p ^ 2 - 1 := by
    have : 5 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left h5 2
    omega
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (p : PadicAlgCl p) hpos
  refine ⟨algebraMap (PadicAlgCl p) ℂ_[p] z, Fact.out, h5, valuation_ring_unit_ball p, ?_, he, h2, fun v => IsPart_zero _ _, le_rfl⟩
  rw [← map_pow, hz, map_natCast]

end KernelEntryData

section ReadsSec

open Formalism.MainNotions.Lnk Formalism.D5 Formalism.FrobeniusOrbits Formalism.LFunctionChainParameters.LHost Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
  Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

theorem Reads_nonempty {D : D7} (L : SizeData₂ D) :
    ∃ (TT : Finset D.R.A) (a : D.R.A → ℝ) (w : Fin D.R.m → E0 × D.R.A → ℝ),
      Reads L D.R.toFrame D.R.m TT a w := by
  classical
  refine ⟨Finset.univ.filter (fun h => hval D.R.toFrame h ∈ D.host.TT.image Formalism.HC.Frame.A.val),
    fun h => if hh : ∃ t : D.host.TT, hval D.R.toFrame h = (t : D.R.A).val then (L.aT hh.choose : ℝ) else 0,
    fun j g => if hh : ∃ τ : D.what₂.Tau, gcode _ ((D.eTau τ : D.R.Psi) : D.R.GG) = mcode D.R.toFrame g
      then wj D (j.val + 1) hh.choose else 0, rfl, rfl, fun h => by simp only [Finset.mem_filter, Finset.mem_univ, true_and], ?_, ?_⟩
  · intro t h hh
    have hex : ∃ t : D.host.TT, hval D.R.toFrame h = (t : D.R.A).val := ⟨t, hh⟩
    have hc : hex.choose = t :=
      Subtype.ext (Formalism.HC.Frame.A.val_injective _ (hex.choose_spec.symm.trans hh))
    simp only [dif_pos hex, hc]
  · intro j g τ hh
    have hex : ∃ τ : D.what₂.Tau, gcode _ ((D.eTau τ : D.R.Psi) : D.R.GG) = mcode D.R.toFrame g := ⟨τ, hh⟩
    have hc : hex.choose = τ :=
      D.eTau.injective (Subtype.ext (gcode_injective _ (hex.choose_spec.trans hh.symm)))
    simp only [dif_pos hex, hc]

end ReadsSec

section FrobSec

open Formalism.FrobeniusOrbits
open scoped Pointwise

theorem IsFrobOf_exists (D : D7) (p : ℕ) [Fact p.Prime] : ∃ φ, IsFrobOf D p φ := by
  have := Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.factQ D
  have := Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.factD D
  refine ⟨(Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.Teq D.R.toFrame).symm ((Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.Md D).frob p), fun P _ _ => ?_⟩
  refine ((Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.fld D p P _).2).mpr ?_
  rw [Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.galE_sigmaOf, Equiv.apply_symm_apply, sub_self]
  exact zero_mem _

theorem cc_not_mem_of_allSplit (D : D7) (p : ℕ) [hp : Fact p.Prime] (φ : D.R.GG) (hφ : IsFrobOf D p φ)
    (hs : Formalism.MainNotions.TaylorLogMetric.AllSplit D p) : D.R.cc ∉ Subgroup.zpowers φ := by
  intro hc
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp.out)
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 D.host.E)) := inferInstance
  have hmem : (p : 𝓞 D.host.E) ∈ P := by
    have := (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) (p : ℤ)).1 (Ideal.mem_span_singleton_self _)
    simpa using this
  have hne : P ≠ ⊥ := by
    rintro rfl
    have h0 : (p : 𝓞 D.host.E) = 0 := by simpa using hmem
    exact hp.out.ne_zero (by exact_mod_cast h0)
  have hst : D.host.sigmaOf φ ∈ MulAction.stabilizer (D.host.E ≃ₐ[ℚ] D.host.E) P := (hφ P).mem_stabilizer
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hconj : D.host.conj = D.host.sigmaOf φ ^ k := by
    show (D.host.gal).symm (D.R.cc) = ((D.host.gal).symm φ) ^ k
    rw [← map_zpow, hk]
  have hcs : D.host.conj ∈ MulAction.stabilizer (D.host.E ≃ₐ[ℚ] D.host.E) P := hconj ▸ Subgroup.zpow_mem _ hst k
  exact hs P hPp hne hmem (MulAction.mem_stabilizer_iff.1 hcs)

theorem Pos_nonempty_of_allSplit (D : D7) (p : ℕ) [Fact p.Prime] (hs : Formalism.MainNotions.TaylorLogMetric.AllSplit D p) :
    ∃ d : ℕ, d ≠ 0 ∧ Nonempty (Formalism.MainNotions.TaylorLogMetric.Pos D p d) := by
  obtain ⟨φ, hφ⟩ := IsFrobOf_exists D p
  have : Finite (D.R.GG) := by
    have : Finite (D.R.MA) := inferInstance
    infer_instance
  exact ⟨orderOf φ, (isOfFinOrder_of_finite φ).orderOf_pos.ne', Pos_nonempty D p φ hφ (cc_not_mem_of_allSplit D p φ hφ hs)⟩

theorem structure_hypotheses_exist (D : D7) (p : ℕ) [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (h5 : 5 ≤ p)
    (hs : Formalism.MainNotions.TaylorLogMetric.AllSplit D p) (N N' : ℕ) (hN : Even N) (hN' : Even N') :
    ∃ (d : ℕ) (_ : NeZero d) (Po : Formalism.MainNotions.TaylorLogMetric.Pos D p d) (ϖ : ℂ_[p]),
      Formalism.MainNotions.TaylorLogMetric.admitted D N N' (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') ∧
      (∀ v : {v // v ∈ Po.V}, Formalism.MainNotions.TaylorLogMetric.LocBasisW D (Formalism.MainNotions.TaylorLogMetric.posEmb D lam Po.φ v.1 (0 : ZMod d))
        (Formalism.MainNotions.StandardLatticesGL3.stdL D N) 1) ∧
      (∀ v : {v // v ∈ Po.V}, Formalism.MainNotions.TaylorLogMetric.LocBasisW D (Formalism.MainNotions.TaylorLogMetric.posEmb D lam Po.φ v.1 (0 : ZMod d))
        (Formalism.MainNotions.StandardLatticesGL3.stdL D N') 1) ∧
      ϖ ^ (p ^ 2 - 1) = (p : ℂ_[p]) := by
  obtain ⟨d, hd, ⟨Po⟩⟩ := Pos_nonempty_of_allSplit D p hs
  obtain ⟨ϖ, hϖ⟩ := setting_nonempty_even_orbits p h5 ⟨0, fun _ => 2, 0, 0⟩ (fun v => v.elim0) (fun v => v.elim0)
  exact ⟨d, ⟨hd⟩, Po, ϖ, Adm_std D N N' hN hN', fun v => LocBasisW_std D _ (posEmb_one D lam _ _ _) N,
    fun v => LocBasisW_std D _ (posEmb_one D lam _ _ _) N', hϖ.vp_pow⟩

end FrobSec

section Junk

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem volume_zero_gauge_eq_zero (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) : volHE (⟨fun _ _ => 0⟩ : GaugeFam F E σ) M J = 0 := by
  unfold volHE MeasureTheory.covolume
  split_ifs <;> simp

theorem SWc3G_junk (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) :
    Formalism.MainNotions.UnusedSlot34.SWc3G F E σ (⟨fun _ _ => 0⟩ : GaugeFam F E σ) := by
  intro M J J' x β B _ _ _ _ _ _ _ _
  rw [volume_zero_gauge_eq_zero, volume_zero_gauge_eq_zero]

theorem zero_family_not_vectors (D : D7) (T : Formalism.MainNotions.TaylorLogMetric.Tor D) : ¬ Formalism.MainNotions.TaylorLogMetric.vec22 D T (fun _ _ _ _ _ => 0) :=
  fun h => (h 0 0 _ _ (Adm_std D 0 0 (by simp) (by simp))).2.1 rfl

def GaugeEx (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) : Prop :=
  ∃ G : GaugeFam F E σ, G.IsGauge

end Junk

end Formalism.MainNotions.GlobalTheoryTheory.Inhab

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory.Inhab

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem dens_const_mul (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (c : ℂ) (Th : (Gx D i → ℂ) → ℂ)
    (z : Gx D i → ℂ) : dens D i s (fun z => c * Th z) z = ‖c‖ ^ 2 * dens D i s Th z := by
  unfold dens
  rw [norm_mul, mul_pow]; ring

theorem admis_const_mul {D : D7} {i : ℕ} {s : D.what₂.LL →+* ℂ} (T : Torus D i s) (c : ℂ)
    {Th : (Gx D i → ℂ) → ℂ} (h : T.Admis Th) : T.Admis (fun z => c * Th z) := by
  refine ⟨h.1.const_mul c, fun y hy z => ?_, ?_⟩
  · rw [dens_const_mul, dens_const_mul, h.2.1 y hy z]
  · have : dens D i s (fun z => c * Th z) = fun z => ‖c‖ ^ 2 * dens D i s Th z :=
      funext (dens_const_mul D i s c Th)
    rw [this]
    exact h.2.2.const_mul _

theorem l2_norm_sq_const_mul {D : D7} {i : ℕ} {s : D.what₂.LL →+* ℂ} (T : Torus D i s) (c : ℂ)
    (Th : (Gx D i → ℂ) → ℂ) : T.l2Sq (fun z => c * Th z) = ‖c‖ ^ 2 * T.l2Sq Th := by
  unfold Torus.l2Sq
  simp_rw [dens_const_mul]
  exact MeasureTheory.integral_const_mul _ _

theorem admis_zero {D : D7} {i : ℕ} {s : D.what₂.LL →+* ℂ} (T : Torus D i s) :
    T.Admis (fun _ => 0) ∧ T.l2Sq (fun _ => 0) = 0 := by
  have hd : dens D i s (fun _ => 0) = fun _ => 0 := by
    funext z; simp [dens]
  refine ⟨⟨differentiable_const _, fun y _ z => by rw [hd], ?_⟩, ?_⟩
  · rw [hd]; exact MeasureTheory.integrableOn_zero
  · unfold Torus.l2Sq; rw [hd]; simp

def TorusEx (D : D7) : Prop := ∀ (i : ℕ) (s : D.what₂.LL →+* ℂ), Nonempty (Torus D i s)

def ThetaEx (D : D7) : Prop :=
  ∀ (i : ℕ) (s : D.what₂.LL →+* ℂ), ∃ (T : Torus D i s) (Th : (Gx D i → ℂ) → ℂ) (cf : (Gx D i →₀ ℕ) → ℂ),
    T.Admis Th ∧ T.l2Sq Th = 1 ∧ ∀ z, HasSum (fun e => cf e * e.prod fun g n => z g ^ n) (Th z)

theorem TorusEx_of_ThetaEx (D : D7) (h : ThetaEx D) : TorusEx D := fun i s =>
  let ⟨T, _⟩ := h i s; ⟨T⟩

theorem KerData_nonempty (D : D7) (u : D.what₂.Word) (h : ThetaEx D) : Nonempty (KerData D u) := by
  classical
  choose T Th cf hA hN hS using h
  have key : ∀ (r : ℝ), 0 ≤ r → ∀ i s, r ^ 2 = (T i s).l2Sq (fun z => (r : ℂ) * Th i s z) := by
    intro r _ i s
    rw [l2_norm_sq_const_mul, hN, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_one]
  exact ⟨{
    embS := fun _ _ => 0
    ipS := fun _ _ _ => 0
    tor := fun i s _ _ => T i s
    Th := fun i s L L' z => (((D.fm u).thFree i s L L' : ℝ) : ℂ) * Th i s z
    cf := fun i s L L' e => (((D.fm u).thFree i s L L' : ℝ) : ℂ) * cf i s e
    cf_sum := fun i _ s L L' z => by
      simpa [mul_assoc] using (hS i s z).mul_left (((D.fm u).thFree i s L L' : ℝ) : ℂ)
    e0 := fun i s L L' z => (((D.fm u).thFree i s L L' : ℝ) : ℂ) * Th i s z
    initial_theta_admissible := fun i _ s L L' => admis_const_mul (T i s) _ (hA i s)
    levelZeroComparison_norm := fun i _ s L L' => key _ ((D.fm u).thFree_nonneg i s L L') i s
    Q := fun _ _ _ _ _ _ => 0 }⟩

theorem KerData_nonempty_of_zero (D : D7) (u : D.what₂.Word) (h : TorusEx D)
    (h0 : ∀ i < D.R.m, ∀ s L L', (D.fm u).thFree i s L L' = 0) :
    Nonempty (KerData D u) := by
  classical
  have T : ∀ (i : ℕ) (s : D.what₂.LL →+* ℂ), Torus D i s := fun i s => (h i s).some
  exact ⟨{
    embS := fun _ _ => 0
    ipS := fun _ _ _ => 0
    tor := fun i s _ _ => T i s
    Th := fun _ _ _ _ _ => 0
    cf := fun _ _ _ _ _ => 0
    cf_sum := fun i _ s L L' z => by simp [hasSum_zero]
    e0 := fun _ _ _ _ _ => 0
    initial_theta_admissible := fun i _ s _ _ => (admis_zero (T i s)).1
    levelZeroComparison_norm := fun i hi s L L' => by rw [h0 i hi s L L', (admis_zero (T i s)).2]; norm_num
    Q := fun _ _ _ _ _ _ => 0 }⟩

theorem torus_of_KerData {D : D7} {u : D.what₂.Word} (X : KerData D u) (i : ℕ) (s : D.what₂.LL →+* ℂ)
    (L : (D.mem u).C.cls i) (L' : (D.mem u).C.cls (i + 1)) : Nonempty (Torus D i s) := ⟨X.tor i s L L'⟩

theorem theta_of_KerData {D : D7} {u : D.what₂.Word} (X : KerData D u) (i : ℕ) (hi : i < D.R.m)
    (s : D.what₂.LL →+* ℂ) (L : (D.mem u).C.cls i) (L' : (D.mem u).C.cls (i + 1))
    (h : (D.fm u).thFree i s L L' ≠ 0) :
    ∃ (T : Torus D i s) (Th : (Gx D i → ℂ) → ℂ), T.Admis Th ∧ T.l2Sq Th ≠ 0 :=
  ⟨X.tor i s L L', X.e0 i s L L', X.initial_theta_admissible i hi s L L', by
    rw [← X.levelZeroComparison_norm i hi s L L']; exact pow_ne_zero 2 h⟩

theorem emb_zero_of_ConjMetric {D : D7} {u : D.what₂.Word} (X : KerData D u) (h : X.ConjMetric)
    (h0 : ∀ i s, X.embS i s = 0) : ∀ i ≤ D.R.m, (D.fm u).emb i = 0 := fun i hi => by
  rw [← (h.1 i hi).1, h0]

theorem ker_zero_of_Q_zero {D : D7} {u : D.what₂.Word} (X : KerData D u) (s : D.what₂.LL →+* ℂ) (h : X.KerAt s)
    (h0 : ∀ i s L L' x y, X.Q i s L L' x y = 0) :
    ∀ i < D.R.m, ∀ (hK : (D.fm u).KRat i) x y L',
      X.ipS (i + 1) s L' (X.embS (i + 1) s y L') (X.embS (i + 1) s ((D.fm u).KL i hK x) L') = 0 := by
  intro i hi hK x y L'
  rw [(h i hi hK x y).1 L']
  simp [h0, jet]

theorem Hq_sub (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (z x : Gx D i → ℂ) :
    Hq D i s (z - x) = Hq D i s z - 2 * (Hherm D i s z x).re + Hq D i s x := by
  unfold Hq Hherm
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Complex.div_ofReal_re, Pi.sub_apply, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_sub, Complex.star_def]
  ring

theorem dens_trans (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (x : Gx D i → ℂ) (Th : (Gx D i → ℂ) → ℂ)
    (z : Gx D i → ℂ) : dens D i s (trans D i s x Th) z = dens D i s Th (z - x) := by
  unfold dens flipTwoThree.trans
  rw [norm_mul, mul_pow, Complex.norm_exp, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, Hq_sub]
  congr 2
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  push_cast
  ring

theorem dens_trans_periodic {D : D7} {i : ℕ} {s : D.what₂.LL →+* ℂ} (T : Torus D i s) (x : Gx D i → ℂ)
    {Th : (Gx D i → ℂ) → ℂ} (h : T.Admis Th) (y : Gx D i → ℂ) (hy : y ∈ T.La) (z : Gx D i → ℂ) :
    dens D i s (trans D i s x Th) (z + y) = dens D i s (trans D i s x Th) z := by
  rw [dens_trans, dens_trans, add_sub_right_comm, h.2.1 y hy]

theorem trans_zero (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (Th : (Gx D i → ℂ) → ℂ) :
    trans D i s 0 Th = Th := by
  funext z
  simp [flipTwoThree.trans, Hherm, Hq]

theorem theta_condition_of_proposition {D : D7} {u : D.what₂.Word} (X : KerData D u) (C : ℝ)
    (thN : ∀ i, (D.what₂.LL →+* ℂ) → (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) → ℝ)
    (hp : ∀ i < D.R.m, ∀ s L L' z, ((D.fm u).thFree i s L L' : ℂ) * X.Th i s L L' z =
      (thN i s L L' : ℂ) * X.e0 i s L L' z)
    (hs : ∀ i < D.R.m, ∀ s L L', 0 < (D.fm u).thFree i s L L' ∧
      (thN i s L L' / (D.fm u).thFree i s L L') ^ 2 ≤ Real.exp (C * D.R.f *
        ((D.R.m : ℝ) ^ 2 * D.R.N (i + 1) + (D.R.N i : ℝ) * D.R.N (i + 1)) *
        (Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1)))) :
    adm5 X C := by
  intro i hi s L L'
  obtain ⟨h0, hb⟩ := hs i hi s L L'
  refine ⟨((thN i s L L' / (D.fm u).thFree i s L L' : ℝ) : ℂ), 1, fun _ => 1, fun _ => 0, fun z => ?_, ?_⟩
  · have hne : ((D.fm u).thFree i s L L' : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
    have := hp i hi s L L' z
    simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, trans_zero]
    push_cast
    field_simp
    linear_combination this
  · have e1 : ‖((thN i s L L' / (D.fm u).thFree i s L L' : ℝ) : ℂ)‖ ^ 2 =
        (thN i s L L' / (D.fm u).thFree i s L L') ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [e1]
    simpa using hb

theorem conjMetric_at_embLL {D : D7} {u : D.what₂.Word} (X : KerData D u) (i : ℕ)
    (h : X.embS i D.what₂.embLL = (D.fm u).emb i ∧ X.ipS i D.what₂.embLL = (D.fm u).ipV i)
    (x : ((D.fm u).lat i).V) :
    (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat i).b ((D.fm u).lat i).X (InfinitePlace.mk D.what₂.embLL) x x).re =
      ∑ c, ((Nat.card ((D.mem u).C.stab i c) : ℝ))⁻¹ * X.nrm i D.what₂.embLL c x := by
  rw [(D.fm u).emb_norm i x, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold KerData.nrm
  rw [h.1, h.2]
  have hw : (D.mem u).C.wt i c = (((Nat.card ((D.mem u).C.stab i c) : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp [ColumnChain.wt]
  rw [hw, Complex.re_ofReal_mul]

theorem conjMetric_conj {D : D7} {u : D.what₂.Word} (X : KerData D u) (h : X.ConjMetric) (i : ℕ) (hi : i ≤ D.R.m)
    (s : D.what₂.LL →+* ℂ) (x : ((D.fm u).lat i).V) :
    ∑ c, ((Nat.card ((D.mem u).C.stab i c) : ℝ))⁻¹ * X.nrm i (ComplexEmbedding.conjugate s) c x =
      ∑ c, ((Nat.card ((D.mem u).C.stab i c) : ℝ))⁻¹ * X.nrm i s c x := by
  rw [← h.2.2 i hi s x, ← h.2.2 i hi (ComplexEmbedding.conjugate s) x, InfinitePlace.mk_conjugate_eq]

end Formalism.MainNotions.GlobalTheoryTheory.Inhab

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory.Inhab

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem majAt_self_re_nonneg {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    0 ≤ (Formalism.HermitianLatticesTheory.majAt b X v x x).re := by
  unfold Formalism.HermitianLatticesTheory.majAt
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  have : (star (Formalism.HermitianLatticesTheory.fcoord b X v x i) * Formalism.HermitianLatticesTheory.fcoord b X v x i).re =
      Complex.normSq (Formalism.HermitianLatticesTheory.fcoord b X v x i) := by
    simp [Complex.normSq_apply, Complex.mul_re]
  rw [this]; exact Complex.normSq_nonneg _

theorem ColVal_cls_nonempty {D : D7} {u : D.what₂.Word} (CV : ColVal D u) : Nonempty ((D.mem u).C.cls 0) := CV.ne

theorem ColVal_pos_at {D : D7} {u : D.what₂.Word} (CV : ColVal D u) (τ : D.what₂.Tau)
    (v : InfinitePlace D.what₂.LL) (y : (D.sp.X 0).V) :
    0 ≤ (v.embedding (CV.rho τ ((D.sp.X 0).hT y y))).re := by
  obtain ⟨c⟩ := CV.ne
  rw [← CV.bc_norm c τ v y]
  exact majAt_self_re_nonneg _ _ _ _

theorem exists_ext (D : D7) (ρ : D.host.E →+* D.what₂.LL) (σ : D.host.E →+* ℂ) :
    ∃ s : D.what₂.LL →+* ℂ, ∀ a, s (ρ a) = σ a := by
  let _ := ρ.toAlgebra
  let _ := σ.toAlgebra
  have : Algebra.IsAlgebraic D.host.E D.what₂.LL := by
    have : IsScalarTower ℚ D.host.E D.what₂.LL := IsScalarTower.of_algebraMap_eq (fun q => by
      simp [RingHom.algebraMap_toAlgebra])
    exact Algebra.IsAlgebraic.tower_top (K := ℚ) D.host.E
  let f : D.what₂.LL →ₐ[D.host.E] ℂ := IsAlgClosed.lift
  exact ⟨f.toRingHom, fun a => f.commutes a⟩

theorem ColVal_pos {D : D7} {u : D.what₂.Word} (CV : ColVal D u) (τ : D.what₂.Tau)
    (σ : D.host.E →+* ℂ) (y : (D.sp.X 0).V) : 0 ≤ (σ ((D.sp.X 0).hT y y)).re := by
  obtain ⟨s, hs⟩ := exists_ext D (CV.rho τ) σ
  have h := ColVal_pos_at CV τ (InfinitePlace.mk s) y
  rcases InfinitePlace.embedding_mk_eq s with h1 | h1
  · rw [h1, hs] at h; exact h
  · rw [h1, ComplexEmbedding.conjugate_coe_eq, hs, Complex.conj_re] at h; exact h

theorem ColVal_isEmpty_of_neg (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (σ : D.host.E →+* ℂ)
    (y : (D.sp.X 0).V) (h : (σ ((D.sp.X 0).hT y y)).re < 0) : IsEmpty (ColVal D u) :=
  ⟨fun CV => absurd (ColVal_pos CV τ σ y) (not_le.mpr h)⟩

structure ColBase (D : D7) (u : D.what₂.Word) where
  rho : D.what₂.Tau → (D.host.E →+* D.what₂.LL)
  Q : (D.mem u).C.cls 0 → D.what₂.Tau → HLat D.what₂.LL
  Q_good : ∀ c τ, (Q c τ).Good
  eQ : ∀ c τ, (Q c τ).ι ≃ Fin (D.R.N 0)
  bc : ∀ c τ, (D.sp.X 0).V →+ (Q c τ).V
  bc_smul : ∀ c τ (a : D.host.E) y, bc c τ (a • y) = rho τ a • bc c τ y
  bc_L : ∀ c τ, (Q c τ).L = Submodule.span (𝓞 D.what₂.LL) (bc c τ '' (D.clsLat u 0 c : Set (D.sp.X 0).V))
  bc_norm : ∀ c τ (v : InfinitePlace D.what₂.LL) y,
    (Formalism.HermitianLatticesTheory.majAt (Q c τ).b (Q c τ).X v (bc c τ y) (bc c τ y)).re =
      (v.embedding (rho τ ((D.sp.X 0).hT y y))).re

def ColTie {D : D7} {u : D.what₂.Word} (B : ColBase D u) : Prop :=
  Nonempty ((D.mem u).C.cls 0) ∧
  (∀ c, LatT (D.sp.X 0) (Tu D u ^ (2 * D.R.f)) (D.clsLat u 0 c)) ∧
  ∃ co : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL),
    Function.Injective co ∧
    (∀ F, (∃ x, co x = F) ↔ ∀ c, F c ∈ TSpan D.what₂.LL ((D.fm u).lam 0)) ∧
    (∀ (w : D.what₂.places.Pl)
      (γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL),
      (∀ c τ, LocBasis D w (B.Q c τ) (B.eQ c τ) (γ c τ)) →
      ∀ x, x ∈ locW D.what₂.places w ((D.fm u).lat 0).L ↔
        ∀ c, actAll ((D.fm u).lam 0) (fun τ => (γ c τ)⁻¹) (co x c) ∈ IntSpanAt D w ((D.fm u).lam 0)) ∧
    ∀ (v : InfinitePlace D.what₂.LL) x,
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re =
        ∑ c, (nfAll ((D.fm u).lam 0)
          (actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))
          (actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))).re

theorem ColVal_nonempty_iff (D : D7) (u : D.what₂.Word) :
    Nonempty (ColVal D u) ↔ ∃ B : ColBase D u, ColTie B := by
  constructor
  · rintro ⟨CV⟩
    exact ⟨⟨CV.rho, CV.Q, CV.Q_good, CV.eQ, CV.bc, CV.bc_smul, CV.bc_L, CV.bc_norm⟩,
      CV.ne, CV.latT, CV.co, CV.co_inj, CV.co_range, CV.fin, CV.inf⟩
  · rintro ⟨B, hne, hT, co, h1, h2, h3, h4⟩
    exact ⟨⟨hne, B.rho, B.Q, B.Q_good, B.eQ, B.bc, B.bc_smul, B.bc_L, B.bc_norm, hT, co, h1, h2, h3, h4⟩⟩

def PosFrame (D : D7) : Prop :=
  ∀ σ : D.host.E →+* ℂ, ∃ Y : Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) ℂ, IsUnit Y.det ∧
    ∀ y : (D.sp.X 0).V, ∑ i, ‖(Y.mulVec fun j => σ ((D.sp.X 0).frame.repr y j)) i‖ ^ 2 =
      (σ ((D.sp.X 0).hT y y)).re

section Base

variable {E LL : Type} [Field E] [NumberField E] [StarRing E] [Field LL] [NumberField LL] [StarRing LL]
  (S : HSpace E) (ρ : E →+* LL)

def bcFun : S.V →+ (Fin S.rank → LL) where
  toFun y i := ρ (S.frame.repr y i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

theorem bcFun_smul (a : E) (y : S.V) : bcFun S ρ (a • y) = ρ a • bcFun S ρ y := by
  funext i; simp [bcFun]

theorem bcFun_smulO (a : 𝓞 E) (y : S.V) :
    bcFun S ρ (a • y) = (RingOfIntegers.mapRingHom ρ a) • bcFun S ρ y := by
  have h1 : a • y = (a : E) • y := (algebraMap_smul E a y).symm
  rw [h1, bcFun_smul]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Algebra.smul_def]
  congr 1

theorem bcFun_frame (i : Fin S.rank) : bcFun S ρ (S.frame i) = Pi.single i 1 := by
  funext j
  simp only [bcFun, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Module.Basis.repr_self]
  by_cases h : j = i
  · subst h; simp
  · rw [Finsupp.single_eq_of_ne (by simpa using h), Pi.single_eq_of_ne h, map_zero]

def mkQ (Lc : Submodule (𝓞 E) S.V) (Y : InfinitePlace LL → Matrix (Fin S.rank) (Fin S.rank) ℂ) : HLat LL where
  V := Fin S.rank → LL
  ι := Fin S.rank
  b := Pi.basisFun LL (Fin S.rank)
  X := fun v => (Y v)⁻¹
  L := Submodule.span (𝓞 LL) (bcFun S ρ '' (Lc : Set S.V))

theorem mkQ_fg (Lc : Submodule (𝓞 E) S.V) (h : Lc.FG) :
    (Submodule.span (𝓞 LL) (bcFun S ρ '' (Lc : Set S.V))).FG := by
  classical
  obtain ⟨s, hs⟩ := h
  refine ⟨s.image (bcFun S ρ), ?_⟩
  apply le_antisymm
  · apply Submodule.span_mono
    rw [Finset.coe_image]
    apply Set.image_mono
    rw [← hs]; exact Submodule.subset_span
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [← hs] at hy
    rw [Finset.coe_image]
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [bcFun_smulO]; exact Submodule.smul_mem _ _ hx

theorem mkQ_span (Lc : Submodule (𝓞 E) S.V) (h : Submodule.span E (Lc : Set S.V) = ⊤) :
    Submodule.span LL ((Submodule.span (𝓞 LL) (bcFun S ρ '' (Lc : Set S.V)) : Submodule (𝓞 LL) (Fin S.rank → LL)) :
      Set (Fin S.rank → LL)) = ⊤ := by
  have key : ∀ y : S.V, bcFun S ρ y ∈ Submodule.span LL (bcFun S ρ '' (Lc : Set S.V)) := by
    intro y
    have hy : y ∈ Submodule.span E (Lc : Set S.V) := by rw [h]; trivial
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [bcFun_smul]; exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ i, w i • (Pi.single i 1 : Fin S.rank → LL) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [hw]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  rw [← bcFun_frame S ρ i]
  exact Submodule.span_mono Submodule.subset_span (key _)

theorem mkQ_norm (Lc : Submodule (𝓞 E) S.V) (Y : InfinitePlace LL → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (hY : ∀ v, IsUnit (Y v).det) (v : InfinitePlace LL) (y : S.V) :
    (Formalism.HermitianLatticesTheory.majAt (mkQ S ρ Lc Y).b (mkQ S ρ Lc Y).X v (bcFun S ρ y) (bcFun S ρ y)).re =
      ∑ i, ‖((Y v).mulVec fun j => (v.embedding.comp ρ) (S.frame.repr y j)) i‖ ^ 2 := by
  unfold Formalism.HermitianLatticesTheory.majAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : Formalism.HermitianLatticesTheory.fcoord (mkQ S ρ Lc Y).b (mkQ S ρ Lc Y).X v (bcFun S ρ y) =
      (Y v).mulVec fun j => (v.embedding.comp ρ) (S.frame.repr y j) := by
    unfold Formalism.HermitianLatticesTheory.fcoord
    have : ((mkQ S ρ Lc Y).X v)⁻¹ = Y v := Matrix.nonsing_inv_nonsing_inv _ (hY v)
    rw [this]
    congr 1
  rw [h1]
  simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]

theorem base_exists (Lc : Submodule (𝓞 E) S.V) (hfg : Lc.FG) (hsp : Submodule.span E (Lc : Set S.V) = ⊤)
    (n : ℕ) (hr : S.rank = n)
    (hpos : ∀ σ : E →+* ℂ, ∃ Y : Matrix (Fin S.rank) (Fin S.rank) ℂ, IsUnit Y.det ∧
      ∀ y : S.V, ∑ i, ‖(Y.mulVec fun j => σ (S.frame.repr y j)) i‖ ^ 2 = (σ (S.hT y y)).re) :
    ∃ (Q : HLat LL) (_ : Q.ι ≃ Fin n) (bc : S.V →+ Q.V), Q.Good ∧ (∀ (a : E) y, bc (a • y) = ρ a • bc y) ∧
      Q.L = Submodule.span (𝓞 LL) (bc '' (Lc : Set S.V)) ∧
      ∀ (v : InfinitePlace LL) y, (Formalism.HermitianLatticesTheory.majAt Q.b Q.X v (bc y) (bc y)).re = (v.embedding (ρ (S.hT y y))).re := by
  choose Y hY hN using hpos
  refine ⟨mkQ S ρ Lc (fun v => Y (v.embedding.comp ρ)), finCongr hr, bcFun S ρ,
    ⟨fun v => Matrix.isUnit_nonsing_inv_det _ (hY _), mkQ_fg S ρ Lc hfg, mkQ_span S ρ Lc hsp⟩,
    bcFun_smul S ρ, rfl, fun v y => ?_⟩
  exact (mkQ_norm S ρ Lc (fun v => Y (v.embedding.comp ρ)) (fun v => hY _) v y).trans (hN _ y)

end Base

theorem ColBase_exists (D : D7) (u : D.what₂.Word) (h : PosFrame D)
    (rho : D.what₂.Tau → (D.host.E →+* D.what₂.LL)) : ∃ B : ColBase D u, B.rho = rho := by
  have key := fun (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) =>
    base_exists (LL := D.what₂.LL) (D.sp.X 0) (rho τ) (D.clsLat u 0 c) (D.clsLat_lat u 0 c).fg
      (D.clsLat_lat u 0 c).span_eq_top (D.R.N 0) (D.sp.X_rank 0 (Nat.zero_le _)) h
  choose Q eQ bc h1 h2 h3 h4 using key
  exact ⟨⟨rho, Q, h1, eQ, bc, h2, h3, h4⟩, rfl⟩

theorem ColBase_nonempty (D : D7) (u : D.what₂.Word) (h : PosFrame D) : Nonempty (ColBase D u) :=
  let ⟨B, _⟩ := ColBase_exists D u h (fun _ => D.embE); ⟨B⟩

theorem posFrame_of_sig {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (σ : E →+* ℂ)
    (hσ : ∀ a, σ (star a) = (starRingEnd ℂ) (σ a)) (h : Formalism.UG.HasSignature (S.gram.map σ) S.rank 0) :
    ∃ Y : Matrix (Fin S.rank) (Fin S.rank) ℂ, IsUnit Y.det ∧
      ∀ y : S.V, ∑ i, ‖(Y.mulVec fun j => σ (S.frame.repr y j)) i‖ ^ 2 = (σ (S.hT y y)).re := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq S.rank 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  set Pm : Matrix (Fin S.rank ⊕ Fin 0) (Fin S.rank ⊕ Fin 0) ℂ := P.val with hPm
  set Qm : Matrix (Fin S.rank ⊕ Fin 0) (Fin S.rank ⊕ Fin 0) ℂ := (P⁻¹).val with hQm
  have hPQ : Pm * Qm = 1 := by rw [hPm, hQm, ← Units.val_mul, mul_inv_cancel]; rfl
  have hcT : Formalism.UG.cT (starRingEnd ℂ) Pm = Pm.conjTranspose := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT, hJ] at hP
  set G : Matrix (Fin S.rank) (Fin S.rank) ℂ := S.gram.map σ with hG
  have hGr : G.reindex e e = Qm.conjTranspose * Qm := by
    have h1 : Qm.conjTranspose * (Pm.conjTranspose * G.reindex e e * Pm) * Qm = Qm.conjTranspose * Qm := by
      rw [hP, Matrix.mul_one]
    have h2 : Qm.conjTranspose * Pm.conjTranspose = 1 := by
      rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
    rw [← h1]
    calc G.reindex e e = (Qm.conjTranspose * Pm.conjTranspose) * G.reindex e e * (Pm * Qm) := by
          rw [h2, hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  let Y : Matrix (Fin S.rank) (Fin S.rank) ℂ := Qm.submatrix e e
  have hGY : G = Y.conjTranspose * Y := by
    have : G = (G.reindex e e).submatrix e e := by ext i j; simp
    rw [this, hGr]
    ext i j
    simp only [Y, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact (Equiv.sum_comp e _).symm
  refine ⟨Y, ?_, fun y => ?_⟩
  · have : Y.det = Qm.det := Matrix.det_submatrix_equiv_self e Qm
    rw [this]
    exact (Matrix.isUnit_iff_isUnit_det _).mp ⟨P⁻¹, rfl⟩
  · set z : Fin S.rank → ℂ := fun j => σ (S.frame.repr y j) with hz
    have h1 : ∑ i, ‖(Y.mulVec z) i‖ ^ 2 = (star (Y.mulVec z) ⬝ᵥ Y.mulVec z).re := by
      simp [dotProduct, Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
    have h2 : star (Y.mulVec z) ⬝ᵥ Y.mulVec z = star z ⬝ᵥ G.mulVec z := by
      rw [hGY, Matrix.star_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (star z)]
    have h3 : σ (S.hT y y) = star z ⬝ᵥ G.mulVec z := by
      have := LinearMap.sum_repr_mul_repr_mulₛₗ S.frame S.frame (B := S.hT) y y
      rw [← this, Finsupp.sum_fintype _ _ (by intro i; simp)]
      simp only [dotProduct, Matrix.mulVec, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.sum_fintype _ _ (by intro j; simp), map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [smul_eq_mul, map_mul, RingHom.id_apply, hG, hz, Matrix.map_apply, HSpace.gram, Pi.star_apply]
      rw [starRingEnd_apply, hσ]
      simp only [starRingEnd_apply]
      ring
    rw [h1, h2, h3]

theorem host_emb_star (D : D7) (σ : D.host.E →+* ℂ) (a : D.host.E) : σ (star a) = (starRingEnd ℂ) (σ a) := by
  have := D.host.isCMField_hostE
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E σ a

theorem PosFrame_of_posDef (D : D7) (h : (D.sp.X 0).IsPosDef) : PosFrame D := fun σ =>
  posFrame_of_sig (D.sp.X 0) σ (host_emb_star D σ) (by have := D.sp.X_sig 0 σ; rw [h σ] at this; exact this)

theorem PosFrame_of_fact (D : D7) (h : BaseSpacePosDef D.R D.host.F D.host.E) : PosFrame D :=
  PosFrame_of_posDef D (h D.sp)

theorem ColVal_equiv {D : D7} {u : D.what₂.Word} (CV : ColVal D u) :
    Nonempty (((D.fm u).lat 0).V ≃ₗ[D.what₂.LL]
      (∀ _ : (D.mem u).C.cls 0, ↥(TSpan D.what₂.LL ((D.fm u).lam 0)))) := by
  let f : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      (∀ _ : (D.mem u).C.cls 0, ↥(TSpan D.what₂.LL ((D.fm u).lam 0))) :=
    LinearMap.pi fun c => LinearMap.codRestrict (TSpan D.what₂.LL ((D.fm u).lam 0))
      ((LinearMap.proj c).comp CV.co) (fun x => (CV.co_range (CV.co x)).mp ⟨x, rfl⟩ c)
  refine ⟨LinearEquiv.ofBijective f ⟨fun x y hxy => CV.co_inj ?_, fun g => ?_⟩⟩
  · funext c
    exact congrArg Subtype.val (congrFun hxy c)
  · obtain ⟨x, hx⟩ := (CV.co_range (fun c => (g c : MvPolynomial _ D.what₂.LL))).mpr (fun c => (g c).2)
    refine ⟨x, ?_⟩
    funext c
    exact Subtype.ext (congrFun hx c)

theorem ColVal_latT {D : D7} {u : D.what₂.Word} (CV : ColVal D u) (c : (D.mem u).C.cls 0) :
    LatT (D.sp.X 0) (Tu D u ^ (2 * D.R.f)) (D.clsLat u 0 c) := CV.latT c

theorem ColVal_nonempty (D : D7) (u : D.what₂.Word) (hX : PosFrame D)
    (rho : D.what₂.Tau → (D.host.E →+* D.what₂.LL))
    (hT : ∀ B : ColBase D u, B.rho = rho → ColTie B) : Nonempty (ColVal D u) := by
  obtain ⟨B, hB⟩ := ColBase_exists D u hX rho
  exact (ColVal_nonempty_iff D u).mpr ⟨B, hT B hB⟩

section LocB

variable {LL : Type} [Field LL] (Pl : Rows.Places LL) (w : Pl.Pl) {V : Type} [AddCommGroup V] [Module LL V]

theorem exists_li_gen (s : Finset V) : ∃ t : Finset V,
    Submodule.span (intW Pl w) (t : Set V) = Submodule.span (intW Pl w) (s : Set V) ∧
    LinearIndependent LL ((↑) : t → V) := by
  classical
  induction' hn : s.card using Nat.strong_induction_on with n ih generalizing s
  by_cases hli : LinearIndependent LL ((↑) : s → V)
  · exact ⟨s, rfl, hli⟩
  rw [Fintype.linearIndependent_iff] at hli
  push Not at hli
  obtain ⟨g, hsum, i0, hi0⟩ := hli
  obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ (fun i => Pl.val w (g i)) ⟨i0, Finset.mem_univ _⟩
  have hgj : g j ≠ 0 := by
    intro h0
    have h1 := hj i0 (Finset.mem_univ _)
    simp only [h0, AddValuation.map_zero, top_le_iff] at h1
    exact hi0 ((AddValuation.top_iff _).mp h1)
  have hmem : ∀ i, g i / g j ∈ intW Pl w := by
    intro i
    show (0 : WithTop ℤ) ≤ Pl.val w (g i / g j)
    have h1 : Pl.val w (g i) = Pl.val w (g i / g j) + Pl.val w (g j) := by
      rw [← AddValuation.map_mul, div_mul_cancel₀ _ hgj]
    have h2 := hj i (Finset.mem_univ _)
    have h3 : Pl.val w (g j) ≠ ⊤ := fun h => hgj ((AddValuation.top_iff _).mp h)
    rw [h1] at h2
    by_contra hneg
    push Not at hneg
    have := WithTop.add_lt_add_right h3 hneg
    rw [zero_add] at this
    exact absurd h2 (not_le.mpr this)
  have key : (j : V) = ∑ i ∈ Finset.univ.erase j, (-(g i / g j)) • (i : V) := by
    have h0 := hsum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at h0
    have h1 : (j : V) = (g j)⁻¹ • (g j • (j : V)) := by rw [smul_smul, inv_mul_cancel₀ hgj, one_smul]
    rw [h1, eq_neg_of_add_eq_zero_left h0, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, neg_smul, inv_mul_eq_div]
  have hjm : (j : V) ∈ Submodule.span (intW Pl w) ((s.erase (j : V) : Finset V) : Set V) := by
    have hS : (∑ i ∈ Finset.univ.erase j, (-(g i / g j)) • (i : V)) ∈
        Submodule.span (intW Pl w) ((s.erase (j : V) : Finset V) : Set V) := ?_
    · rwa [← key] at hS
    refine Submodule.sum_mem _ fun i hi => ?_
    have h1 : (-(g i / g j)) • (i : V) = (⟨-(g i / g j), neg_mem (hmem i)⟩ : intW Pl w) • (i : V) := rfl
    rw [h1]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rw [Finset.mem_coe, Finset.mem_erase]
    exact ⟨fun h => (Finset.ne_of_mem_erase hi) (Subtype.ext h), i.2⟩
  have hsp : Submodule.span (intW Pl w) ((s.erase (j : V) : Finset V) : Set V) =
      Submodule.span (intW Pl w) (s : Set V) := by
    apply le_antisymm
    · exact Submodule.span_mono (by exact_mod_cast Finset.erase_subset _ _)
    · rw [Submodule.span_le]
      intro x hx
      by_cases hxj : x = (j : V)
      · rw [hxj]; exact hjm
      · exact Submodule.subset_span (by rw [Finset.mem_coe, Finset.mem_erase]; exact ⟨hxj, hx⟩)
  obtain ⟨t, ht, hli'⟩ := ih (s.erase (j : V)).card (by rw [← hn]; exact Finset.card_erase_lt_of_mem j.2) _ rfl
  exact ⟨t, ht.trans hsp, hli'⟩

end LocB

def IntInW (D : D7) (w : D.what₂.places.Pl) : Prop := ∀ z : 𝓞 D.what₂.LL, (z : D.what₂.LL) ∈ intW D.what₂.places w

theorem LocBasis_exists (D : D7) (w : D.what₂.places.Pl) (hO : IntInW D w) (Q : HLat D.what₂.LL) (hQ : Q.Good) {n : ℕ}
    (e : Q.ι ≃ Fin n) : ∃ γ : Matrix (Fin n) (Fin n) D.what₂.LL, LocBasis D w Q e γ := by
  classical
  obtain ⟨-, ⟨s, hs⟩, hspan⟩ := hQ
  have h1 : locW D.what₂.places w Q.L = Submodule.span (intW D.what₂.places w) (s : Set Q.V) := by
    unfold locW
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      rw [SetLike.mem_coe, ← hs] at hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span hx
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | smul a x _ hx =>
        have h2 : a • x = (⟨(a : D.what₂.LL), hO a⟩ : intW D.what₂.places w) • x :=
          (algebraMap_smul D.what₂.LL a x).symm
        rw [SetLike.mem_coe, h2]
        exact Submodule.smul_mem _ _ hx
    · apply Submodule.span_mono
      rw [← hs]; exact Submodule.subset_span
  obtain ⟨t, ht, hli⟩ := exists_li_gen D.what₂.places w s
  have htop : Submodule.span D.what₂.LL (t : Set Q.V) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    intro x hx
    have h2 : x ∈ Submodule.span (intW D.what₂.places w) (t : Set Q.V) := by
      rw [ht, ← h1]; exact Submodule.subset_span hx
    exact Submodule.span_subset_span (intW D.what₂.places w) D.what₂.LL _ h2
  let bt : Module.Basis t D.what₂.LL Q.V := Module.Basis.mk hli (by rw [Subtype.range_coe]; exact htop.ge)
  let bt' : Module.Basis (Fin n) D.what₂.LL Q.V := bt.reindex ((bt.indexEquiv Q.b).trans e)
  let b' : Module.Basis (Fin n) D.what₂.LL Q.V := Q.b.reindex e
  have hcol : ∀ a, ∑ i, b'.toMatrix bt' i a • Q.b (e.symm i) = bt' a := by
    intro a
    have := b'.sum_repr (bt' a)
    simpa [Module.Basis.toMatrix_apply, b'] using this
  have hrange : Set.range (fun a => bt' a) = (t : Set Q.V) := by
    have : Set.range (fun a => bt' a) = Set.range bt :=
      Module.Basis.range_reindex bt ((bt.indexEquiv Q.b).trans e)
    rw [this]
    simp [bt]
  refine ⟨b'.toMatrix bt', Matrix.isUnit_det_of_right_inverse (b'.toMatrix_mul_toMatrix_flip bt'), ?_⟩
  have hfun : (fun a => bt' a) = fun a => ∑ i, b'.toMatrix bt' i a • Q.b (e.symm i) :=
    funext fun a => (hcol a).symm
  rw [h1, ← ht, ← hrange, hfun]

theorem intInW (D : D7) (w : D.what₂.places.Pl) : IntInW D w := by
  intro z
  show (0 : WithTop ℤ) ≤ D.what₂.places.val w (z : D.what₂.LL)
  by_cases hz : (z : D.what₂.LL) = 0
  · rw [hz, AddValuation.map_zero]; exact le_top
  rw [D.val_eq w _ hz]
  have h1 : (D.plEq w).valuation D.what₂.LL (z : D.what₂.LL) ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one (D.plEq w) z
  have h0 : (D.plEq w).valuation D.what₂.LL (z : D.what₂.LL) ≠ 0 := (Valuation.ne_zero_iff _).mpr hz
  have h2 : WithZero.log ((D.plEq w).valuation D.what₂.LL (z : D.what₂.LL)) ≤ 0 := by
    rw [← WithZero.log_one]
    exact (WithZero.log_le_log h0 one_ne_zero).mpr h1
  have h3 : (0 : ℤ) ≤ vAdd (D.plEq w) (z : D.what₂.LL) := by unfold vAdd; omega
  exact_mod_cast h3

theorem LocBasis_exists' (D : D7) (w : D.what₂.places.Pl) (Q : HLat D.what₂.LL) (hQ : Q.Good) {n : ℕ}
    (e : Q.ι ≃ Fin n) : ∃ γ : Matrix (Fin n) (Fin n) D.what₂.LL, LocBasis D w Q e γ :=
  LocBasis_exists D w (intInW D w) Q hQ e

theorem ColVal_fin_nonvacuous {D : D7} {u : D.what₂.Word} (CV : ColVal D u) (w : D.what₂.places.Pl) :
    ∃ γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL,
      (∀ c τ, LocBasis D w (CV.Q c τ) (CV.eQ c τ) (γ c τ)) ∧
      ∀ x, x ∈ locW D.what₂.places w ((D.fm u).lat 0).L ↔
        ∀ c, actAll ((D.fm u).lam 0) (fun τ => (γ c τ)⁻¹) (CV.co x c) ∈ IntSpanAt D w ((D.fm u).lam 0) := by
  choose γ hγ using fun c τ => LocBasis_exists' D w (CV.Q c τ) (CV.Q_good c τ) (CV.eQ c τ)
  exact ⟨γ, hγ, CV.fin w γ hγ⟩

end Formalism.MainNotions.GlobalTheoryTheory.Inhab

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory.Inhab

open Formalism.BasicNotions Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem level_first_classes_nonempty (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    Nonempty ((D.mem u).C.cls 0) := by
  obtain ⟨c, -⟩ := (Lv u).y_bij.2 (Quotient.mk'' 1)
  exact ⟨c⟩

theorem LevelData_isEmpty_of (D : D7) (u : D.what₂.Word) (h : IsEmpty ((D.mem u).C.cls 0)) :
    IsEmpty (LevelData D) :=
  ⟨fun Lv => h.elim (level_first_classes_nonempty D Lv u).some⟩

theorem level_card_first_classes (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    Nat.card ((D.mem u).C.cls 0) = Nat.card (Formalism.UG.ClassSet
      ((Formalism.UG.ratPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers D.host.F) D.host.F)).subgroupOf
        (Formalism.UG.UPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers D.host.F) D.host.F)))
      ((Lv u).U.subgroupOf (Formalism.UG.UPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers D.host.F) D.host.F)))) :=
  Nat.card_congr (Equiv.ofBijective _ (Lv u).y_bij)

theorem Pend_interlace {D : D7} {u : D.what₂.Word} (P : product_first_zeroth_parts.Pend D u) : (D.fm u).SgInterlace := P.interlace

theorem Pend_isEmpty_of_not_interlace (D : D7) (u : D.what₂.Word) (h : ¬ (D.fm u).SgInterlace) :
    IsEmpty (product_first_zeroth_parts.Pend D u) := ⟨fun P => h P.interlace⟩

def BeOnIsNorm (D : D7) (u : D.what₂.Word) : Prop :=
  ∃ br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ),
    ∀ τ, (D.fm u).beOn τ = product_first_zeroth_parts.opNorm D u τ (br τ)

theorem Pend_beOn {D : D7} {u : D.what₂.Word} (P : product_first_zeroth_parts.Pend D u) : BeOnIsNorm D u := ⟨P.br, P.beOn_eq⟩

theorem opNorm_zero (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : product_first_zeroth_parts.opNorm D u τ 0 = 0 := by
  unfold product_first_zeroth_parts.opNorm
  apply le_antisymm
  · apply Real.sSup_le _ le_rfl
    rintro x ⟨f, -, rfl⟩
    simp [normFock, Formalism.REAL.fockF]
  · apply Real.sSup_nonneg
    rintro x ⟨f, -, rfl⟩
    exact Real.sqrt_nonneg _

def pendJunk (D : D7) (u : D.what₂.Word) (hE : IsEmpty (D.fm u).clsP) (hC : (D.fm u).ptC = ⊥)
    (hI : (D.fm u).SgInterlace)
    (br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
      MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))
    (hb : ∀ τ, (D.fm u).beOn τ = product_first_zeroth_parts.opNorm D u τ (br τ)) : product_first_zeroth_parts.Pend D u where
  br := br
  coM := fun _ _ => 0
  coP := fun _ => 0
  coM_mem := fun _ c => hE.elim c
  coM_inj := fun _ c => hE.elim c
  coP_mem := fun _ _ _ c => hE.elim c
  coP_inj := fun _ z hz _ => by rw [hC] at hz; exact (Submodule.mem_bot ℂ).1 hz
  Pt_eq := fun _ _ _ c => hE.elim c
  lat_co := fun _ _ _ c => hE.elim c
  pt_co := fun w z hz => by
    rw [hC] at hz
    have hz0 : z = 0 := (Submodule.mem_bot ℂ).1 hz
    exact ⟨fun _ c => hE.elim c, fun _ => ⟨0, Submodule.zero_mem _, by rw [hz0, map_zero]⟩⟩
  gP := fun _ _ _ => 1
  ipV_co := fun _ c => hE.elim c
  re_petersson_self_eq_sum_coord := fun w z hz => by
    rw [hC] at hz
    have hz0 : z = 0 := (Submodule.mem_bot ℂ).1 hz
    subst hz0
    simp
  beOn_eq := hb
  interlace := hI

theorem Pend_nonempty_iff_of_isEmpty (D : D7) (u : D.what₂.Word) (hE : IsEmpty (D.fm u).clsP) :
    Nonempty (product_first_zeroth_parts.Pend D u) ↔ (D.fm u).ptC = ⊥ ∧ (D.fm u).SgInterlace ∧ BeOnIsNorm D u := by
  constructor
  · rintro ⟨P⟩
    refine ⟨?_, P.interlace, Pend_beOn P⟩
    obtain ⟨p, hp, hpp⟩ := Ring.not_isField_iff_exists_prime.1 (NumberField.RingOfIntegers.not_isField D.what₂.LL)
    let w : D.what₂.places.Pl := D.plEq.symm ⟨p, hpp, hp⟩
    rw [eq_bot_iff]
    intro z hz
    exact (Submodule.mem_bot ℂ).2 (P.coP_inj w z hz (funext fun c => hE.elim c))
  · rintro ⟨hC, hI, br, hb⟩
    exact ⟨pendJunk D u hE hC hI br hb⟩

theorem Pend_nonempty_junk (D : D7) (u : D.what₂.Word) (hE : IsEmpty (D.fm u).clsP) (hC : (D.fm u).ptC = ⊥)
    (hI : (D.fm u).SgInterlace) (hb : ∀ τ, (D.fm u).beOn τ = 0) : Nonempty (product_first_zeroth_parts.Pend D u) :=
  ⟨pendJunk D u hE hC hI (fun _ => 0) (fun τ => by rw [hb τ, opNorm_zero])⟩

theorem branching_condition_zero_false (D : D7) (u : D.what₂.Word) (P : product_first_zeroth_parts.Pend D u) (h0 : ∀ τ, P.br τ = 0)
    (τ : D.what₂.Tau) : ¬ product_first_zeroth_parts.ArchimedeanSignatureMatching P := by
  intro h
  obtain ⟨-, -, ⟨f, -, hf⟩, -⟩ := h τ
  exact hf (by rw [h0 τ]; rfl)

theorem branching_condition_of_isEmpty (D : D7) (u : D.what₂.Word) (hE : IsEmpty (D.fm u).clsP) (hC : (D.fm u).ptC = ⊥)
    (hI : (D.fm u).SgInterlace)
    (br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
      MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))
    (hbr : ∀ τ, Formalism.MainNotions.PrimeDegreeVariant.IsBr (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) (br τ))
    (hb : ∀ τ, (D.fm u).beOn τ = product_first_zeroth_parts.opNorm D u τ (br τ)) : ∃ P : product_first_zeroth_parts.Pend D u, product_first_zeroth_parts.ArchimedeanSignatureMatching P :=
  ⟨pendJunk D u hE hC hI br hb, hbr⟩

theorem emb_mem_Fi (D : D7) (u : D.what₂.Word) (i : ℕ) (x : ((D.fm u).lat i).V) :
    (D.fm u).emb i x ∈ (D.fm u).Fi i := by
  rw [← ((D.fm u).emb_basis i).2, ← ((D.fm u).lat i).b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem blk_IntSpan (D : D7) {n n' : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n)
    (sg : D.what₂.Tau → DomWeight n')
    (br : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ)
    (h : ∀ τ, ∀ f ∈ delSq ℤ n (lam τ), ∃ g ∈ delSq ℤ n' (sg τ),
      br τ (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) g)
    (p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) (hp : p ∈ product_first_zeroth_parts.IntSpan D w lam) :
    product_first_zeroth_parts.blk (fun τ => br τ) p ∈ product_first_zeroth_parts.IntSpan D w sg := by
  unfold product_first_zeroth_parts.IntSpan at hp
  induction hp using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r, f, hr, hf, rfl⟩ := hp
    choose g hg hbg using fun τ => h τ (f τ) (hf τ)
    rw [map_smul, product_first_zeroth_parts.blk_ten]
    exact AddSubgroup.subset_closure ⟨r, g, hr, hg, by simp only [hbg]⟩
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [map_neg]; exact AddSubgroup.neg_mem _ ha

theorem Pend_integral {D : D7} {u : D.what₂.Word} (P : product_first_zeroth_parts.Pend D u) (h4 : product_first_zeroth_parts.ArchimedeanSignatureMatching P)
    (w : D.what₂.places.Pl) (x : ((D.fm u).lat D.R.m).V) (hx : x ∈ (D.fm u).S D.R.m w)
    (hC : product_first_zeroth_parts.Pt D u ((D.fm u).emb D.R.m x) ∈ (D.fm u).ptC) :
    ∃ y ∈ (D.fm u).SP w, (D.fm u).ptEmb y = product_first_zeroth_parts.Pt D u ((D.fm u).emb D.R.m x) := by
  refine (P.pt_co w _ hC).2 fun c => ?_
  rw [P.Pt_eq w _ (emb_mem_Fi D u D.R.m x) c]
  refine blk_IntSpan D w _ _ P.br (fun τ f hf => ?_) _ (P.lat_co w x hx c)
  have h := (h4 τ).1 f (by unfold product_first_zeroth_parts.lamTr; rw [product_first_zeroth_parts.delSq_wSh]; exact hf)
  unfold product_first_zeroth_parts.sgTr at h
  rwa [product_first_zeroth_parts.delSq_wSh] at h

theorem levelData_exampleRecord_isEmpty (G : Formalism.BasicNotions.Examples₂.LocalGap Formalism.BasicNotions.Examples₂.H0) :
    IsEmpty (LevelData (Formalism.BasicNotions.Examples₂.exampleRecord G)) :=
  LevelData_isEmpty_of _ (Formalism.BasicNotions.Examples₂.exampleRecord G).u₀ (⟨fun x => Empty.elim x⟩)

theorem Pend_exampleRecord_isEmpty (G : Formalism.BasicNotions.Examples₂.LocalGap Formalism.BasicNotions.Examples₂.H0) (u : (Formalism.BasicNotions.Examples₂.exampleRecord G).what₂.Word)
    (τ : (Formalism.BasicNotions.Examples₂.exampleRecord G).what₂.Tau) : IsEmpty (product_first_zeroth_parts.Pend (Formalism.BasicNotions.Examples₂.exampleRecord G) u) := by
  refine Pend_isEmpty_of_not_interlace _ _ fun h => ?_
  have hN : 3 < (Formalism.BasicNotions.Examples₂.exampleRecord G).R.N (Formalism.BasicNotions.Examples₂.exampleRecord G).R.m - 1 := by
    show 3 < Formalism.BasicNotions.Examples₂.R0.N Formalism.BasicNotions.Examples₂.R0.m - 1
    simp [Ranks.N, Formalism.BasicNotions.Examples₂.R0]
  have h0 := (h τ ⟨0, by omega⟩).2
  have h1 := h τ ⟨1, by omega⟩
  have h2 := (h τ ⟨2, by omega⟩).1
  have e1 := ((Formalism.BasicNotions.Examples₂.exampleRecord G).fm u).lam_eq (Formalism.BasicNotions.Examples₂.exampleRecord G).R.m le_rfl τ ⟨1, by omega⟩
  have e2 := ((Formalism.BasicNotions.Examples₂.exampleRecord G).fm u).lam_eq (Formalism.BasicNotions.Examples₂.exampleRecord G).R.m le_rfl τ ⟨2, by omega⟩
  have hk8 : Formalism.BasicNotions.Examples₂.R0.k = 8 := rfl
  have hk1 : 1 < (Formalism.BasicNotions.Examples₂.exampleRecord G).R.k := by show 1 < Formalism.BasicNotions.Examples₂.R0.k; rw [hk8]; norm_num
  have hk2 : 2 < (Formalism.BasicNotions.Examples₂.exampleRecord G).R.k := by show 2 < Formalism.BasicNotions.Examples₂.R0.k; rw [hk8]; norm_num
  have a1 : (((Formalism.BasicNotions.Examples₂.exampleRecord G).fm u).lam (Formalism.BasicNotions.Examples₂.exampleRecord G).R.m τ).w ⟨1, by omega⟩ = 0 :=
    le_antisymm (show _ ≤ (0 : ℤ) from h0) (show (0 : ℤ) ≤ _ from h1.1)
  have a2 : (((Formalism.BasicNotions.Examples₂.exampleRecord G).fm u).lam (Formalism.BasicNotions.Examples₂.exampleRecord G).R.m τ).w ⟨2, by omega⟩ = 0 :=
    le_antisymm (show _ ≤ (0 : ℤ) from h1.2) (show (0 : ℤ) ≤ _ from h2)
  rw [dif_pos hk1, a1] at e1
  rw [dif_pos hk2, a2] at e2
  have u1 := Formalism.BasicNotions.Examples₂.exampleWeight_middle_entries 0 (by rw [hk8]; norm_num)
  have u2 := Formalism.BasicNotions.Examples₂.exampleWeight_middle_entries 1 (by rw [hk8]; norm_num)
  have g0 := Formalism.BasicNotions.Examples₂.exampleWeight_cloud_gap_four 0 (by rw [hk8]; norm_num)
  have e1' : ((0 : ℤ) : ℚ) = Formalism.BasicNotions.Examples₂.hc0.u ⟨0 + 1, by rw [hk8]; norm_num⟩ -
      ((((Formalism.BasicNotions.Examples₂.R0.k : ℕ) : ℚ) - 1) / 2 - ((1 : ℕ) : ℚ)) := e1
  have e2' : ((0 : ℤ) : ℚ) = Formalism.BasicNotions.Examples₂.hc0.u ⟨1 + 1, by rw [hk8]; norm_num⟩ -
      ((((Formalism.BasicNotions.Examples₂.R0.k : ℕ) : ℚ) - 1) / 2 - ((2 : ℕ) : ℚ)) := e2
  rw [u1] at e1'
  rw [u2] at e2'
  push_cast at e1' e2'
  linarith

end Formalism.MainNotions.GlobalTheoryTheory.Inhab

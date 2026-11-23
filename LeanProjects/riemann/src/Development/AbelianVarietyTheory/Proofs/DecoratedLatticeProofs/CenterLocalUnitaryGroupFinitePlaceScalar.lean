import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.CenterLocU

open Matrix Formalism.UG

section Gen

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem cT_add' (σ : A →+* A) (M N : Matrix n n A) : cT σ (M + N) = cT σ M + cT σ N := by
  ext i j; simp [cT]

theorem cT_sub' (σ : A →+* A) (M N : Matrix n n A) : cT σ (M - N) = cT σ M - cT σ N := by
  ext i j; simp [cT]

theorem cT_smul' (σ : A →+* A) (c : A) (M : Matrix n n A) : cT σ (c • M) = σ c • cT σ M := by
  ext i j; simp [cT]

theorem cT_cT' (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (M : Matrix n n A) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, hσ]

theorem cayley_unitary (σ : A →+* A) (J B V : Matrix n n A) (s : A) (hs : σ s = s)
    (hB : cT σ B * J + J * B = 0) (hV1 : (s • (1 : Matrix n n A) - B) * V = 1) :
    cT σ ((s • (1 : Matrix n n A) + B) * V) * J * ((s • (1 : Matrix n n A) + B) * V) = J := by
  set S : Matrix n n A := s • (1 : Matrix n n A) with hSdef
  have hS : cT σ S = S := by rw [hSdef, cT_smul', cT_one, hs]
  have hc : ∀ M : Matrix n n A, S * M = M * S := fun M => by
    rw [hSdef, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have key : cT σ (S + B) * J * (S + B) = cT σ (S - B) * J * (S - B) := by
    rw [cT_add', cT_sub', hS]
    have e1 : (S + cT σ B) * J * (S + B) - (S - cT σ B) * J * (S - B)
        = (S * J * B + cT σ B * J * S) + (S * J * B + cT σ B * J * S) := by noncomm_ring
    have e2 : S * J * B + cT σ B * J * S = 0 := by
      rw [Matrix.mul_assoc (cT σ B) J S, ← hc J, ← Matrix.mul_assoc, ← hc (cT σ B),
        Matrix.mul_assoc S J B, Matrix.mul_assoc S (cT σ B) J, ← Matrix.mul_add, add_comm, hB, Matrix.mul_zero]
    rw [e2, add_zero] at e1
    exact sub_eq_zero.1 e1
  calc cT σ ((S + B) * V) * J * ((S + B) * V) = cT σ V * (cT σ (S + B) * J * (S + B)) * V := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT σ V * (cT σ (S - B) * J * (S - B)) * V := by rw [key]
    _ = cT σ ((S - B) * V) * J * ((S - B) * V) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [hV1, cT_one, Matrix.one_mul, Matrix.mul_one]

theorem comm_of_comm_cayley (g B V : Matrix n n A) (s : A) (h2s : IsUnit (2 * s))
    (hV1 : (s • (1 : Matrix n n A) - B) * V = 1) (hV2 : V * (s • (1 : Matrix n n A) - B) = 1)
    (hg : g * ((s • (1 : Matrix n n A) + B) * V) = ((s • (1 : Matrix n n A) + B) * V) * g) :
    g * B = B * g := by
  have e : s • (1 : Matrix n n A) + B = (2 * s) • (1 : Matrix n n A) - (s • (1 : Matrix n n A) - B) := by
    rw [two_mul, add_smul]; abel
  rw [e, Matrix.sub_mul, hV1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, sub_left_inj] at hg
  have hgV : g * V = V * g := by
    have := congrArg (fun M => (↑h2s.unit⁻¹ : A) • M) hg
    simp only [smul_smul, IsUnit.val_inv_mul, one_smul] at this
    exact this
  have hU : (s • (1 : Matrix n n A) - B) * g = g * (s • (1 : Matrix n n A) - B) := by
    calc (s • (1 : Matrix n n A) - B) * g
        = (s • (1 : Matrix n n A) - B) * g * (V * (s • (1 : Matrix n n A) - B)) := by rw [hV2, Matrix.mul_one]
      _ = (s • (1 : Matrix n n A) - B) * (g * V) * (s • (1 : Matrix n n A) - B) := by simp only [Matrix.mul_assoc]
      _ = (s • (1 : Matrix n n A) - B) * (V * g) * (s • (1 : Matrix n n A) - B) := by rw [hgV]
      _ = ((s • (1 : Matrix n n A) - B) * V) * g * (s • (1 : Matrix n n A) - B) := by simp only [Matrix.mul_assoc]
      _ = g * (s • (1 : Matrix n n A) - B) := by rw [hV1, Matrix.one_mul]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    sub_right_inj] at hU
  exact hU.symm

theorem comm_of_comm_skew (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (J : Matrix n n A) (hJ : cT σ J = J)
    (hJu : IsUnit J.det) (h2 : IsUnit (2 : A)) (δ : A) (hδ : IsUnit δ) (hδσ : σ δ = -δ)
    (g : Matrix n n A) (hg : ∀ B : Matrix n n A, cT σ B * J + J * B = 0 → g * B = B * g)
    (M : Matrix n n A) : g * M = M * g := by
  have hJJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJu
  have hJJ' : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hJu
  have hJi : J⁻¹ = cT σ J⁻¹ := Matrix.inv_eq_left_inv (by
    have := cT_mul σ J J⁻¹
    rw [hJ, hJJ, cT_one] at this
    exact this.symm)
  have hsk : ∀ X : Matrix n n A, cT σ X = -X → g * (J⁻¹ * X) = (J⁻¹ * X) * g := fun X hX => hg _ (by
    rw [cT_mul, hX, ← hJi, neg_mul, ← neg_mul, Matrix.mul_assoc, hJJ', Matrix.mul_one, ← Matrix.mul_assoc, hJJ,
      Matrix.one_mul, neg_add_cancel])
  set Y := J * M
  have h1 := hsk (Y - cT σ Y) (by rw [cT_sub', cT_cT' σ hσ, neg_sub])
  have h2' := hsk (δ • (Y + cT σ Y)) (by rw [cT_smul', cT_add', cT_cT' σ hσ, hδσ, neg_smul, add_comm])
  have e : (2 : A) • M = J⁻¹ * (Y - cT σ Y) + (↑hδ.unit⁻¹ : A) • (J⁻¹ * (δ • (Y + cT σ Y))) := by
    rw [Matrix.mul_smul, smul_smul, IsUnit.val_inv_mul, one_smul, ← Matrix.mul_add,
      sub_add_add_cancel, ← two_smul A Y, Matrix.mul_smul, ← Matrix.mul_assoc, hJJ', Matrix.one_mul]
  have h3 : g * ((2 : A) • M) = ((2 : A) • M) * g := by
    rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h1, h2']
  rw [Matrix.mul_smul, Matrix.smul_mul] at h3
  have := congrArg (fun N => (↑h2.unit⁻¹ : A) • N) h3
  simp only [smul_smul, IsUnit.val_inv_mul, one_smul] at this
  exact this

theorem exists_nat_isUnit_sub (K : Type) [Field K] [CharZero K] [Algebra K A] [FiniteDimensional K A]
    (B : Matrix n n A) : ∃ m : ℕ, m ≠ 0 ∧ IsUnit ((m : A) • (1 : Matrix n n A) - B) := by
  let L : Module.End K (n → A) := (Matrix.mulVecLin B).restrictScalars K
  have hfin : {m : ℕ | L.HasEigenvalue (m : K)}.Finite :=
    (Module.End.finite_hasEigenvalue L).preimage Nat.cast_injective.injOn
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N + 1, by omega, ?_⟩
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  let T : Module.End K (n → A) :=
    (Matrix.mulVecLin (((N + 1 : ℕ) : A) • (1 : Matrix n n A) - B)).restrictScalars K
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have hT : (((N + 1 : ℕ) : A) • (1 : Matrix n n A) - B) *ᵥ x = 0 := hx
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hT
    have hev : L.HasEigenvalue ((N + 1 : ℕ) : K) := by
      refine Module.End.hasEigenvalue_of_hasEigenvector (x := x) ⟨?_, hx0⟩
      rw [Module.End.mem_eigenspace_iff]
      show B *ᵥ x = ((N + 1 : ℕ) : K) • x
      rw [← hT, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    have := hN hev
    omega
  exact LinearMap.injective_iff_surjective.1 hinj

end Gen

end GlobalTheory.CenterLocU

namespace GlobalTheory.CenterLocU
open Matrix Formalism.UG

section Gen2

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem scalar_of_comm_UJ (K : Type) [Field K] [CharZero K] [Algebra K A] [FiniteDimensional K A]
    (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (J : Matrix n n A) (hJ : cT σ J = J) (hJu : IsUnit J.det)
    (δ : A) (hδ : IsUnit δ) (hδσ : σ δ = -δ) (g : Matrix n n A)
    (hg : ∀ h ∈ UJ σ J, g * (h : Matrix n n A) = (h : Matrix n n A) * g) :
    ∃ c : A, g = c • (1 : Matrix n n A) := by
  have h2 : IsUnit (2 : A) := by
    have : (2 : A) = algebraMap K A 2 := (map_ofNat (algebraMap K A) 2).symm
    rw [this]; exact (IsUnit.mk0 (2 : K) two_ne_zero).map _
  have hskew : ∀ B : Matrix n n A, cT σ B * J + J * B = 0 → g * B = B * g := by
    intro B hB
    obtain ⟨m, hm, hU⟩ := exists_nat_isUnit_sub K B
    have hUd := (Matrix.isUnit_iff_isUnit_det _).1 hU
    have hV1 : ((m : A) • (1 : Matrix n n A) - B) * ((m : A) • (1 : Matrix n n A) - B)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ hUd
    have hV2 : ((m : A) • (1 : Matrix n n A) - B)⁻¹ * ((m : A) • (1 : Matrix n n A) - B) = 1 :=
      Matrix.nonsing_inv_mul _ hUd
    have hC := cayley_unitary σ J B _ (m : A) (map_natCast σ m) hB hV1
    have hWC : (J⁻¹ * cT σ (((m : A) • (1 : Matrix n n A) + B) * ((m : A) • (1 : Matrix n n A) - B)⁻¹) * J) *
        (((m : A) • (1 : Matrix n n A) + B) * ((m : A) • (1 : Matrix n n A) - B)⁻¹) = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ _), hC, Matrix.nonsing_inv_mul J hJu]
    let Cu : GL n A := ⟨_, _, mul_eq_one_comm.1 hWC, hWC⟩
    have hCm : Cu ∈ UJ σ J := hC
    have h2m : IsUnit (2 * (m : A)) := by
      have : (2 * (m : A)) = algebraMap K A (2 * m) := by rw [map_mul, map_ofNat, map_natCast]
      rw [this]; exact (IsUnit.mk0 _ (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 hm))).map _
    exact comm_of_comm_cayley g B _ (m : A) h2m hV1 hV2 (hg Cu hCm)
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (M := g)
    (fun i j _ => (comm_of_comm_skew σ hσ J hJ hJu h2 δ hδ hδσ g hskew _).symm)
  exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

end Gen2

end GlobalTheory.CenterLocU

namespace GlobalTheory.CenterLocU

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem exists_anti (D : D7) : ∃ e : D.host.E, D.sp.cm.sig e = -e ∧ e ≠ 0 := by
  have hx : ∃ x : D.host.E, x ∉ Set.range (algebraMap D.host.F D.host.E) := by
    by_contra h
    push_neg at h
    have htop : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ :=
      eq_top_iff.2 fun x _ => Algebra.mem_bot.2 (h x)
    have := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 htop
    rw [D.sp.cm.deg2] at this
    norm_num at this
  obtain ⟨x, hx⟩ := hx
  refine ⟨x - star x, ?_, ?_⟩
  · show star (x - star x) = -(x - star x)
    rw [star_sub, star_star, neg_sub]
  · intro h0
    exact hx (RingHom.mem_range.1 ((D.sp.cm.fixed x).1 (sub_eq_zero.1 h0).symm))

theorem center_scalar_loc : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)) (g : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v), g ∈ Subgroup.center (GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v) → ∃ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig V.gram g).1 = c • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
  intro D V v g hg
  have hσ : ∀ x : D.host.E, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  obtain ⟨e, he, he0⟩ := exists_anti D
  have hJ : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv D.host.F v) D.sp.cm.sig) (JR (Fv D.host.F v) V.gram) =
      JR (Fv D.host.F v) V.gram := by
    ext i j
    exact congrArg (inclR (Fv D.host.F v)) (V.herm.eq (V.frame j) (V.frame i))
  have hδσ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv D.host.F v) D.sp.cm.sig (inclR (Fv D.host.F v) e) =
      -inclR (Fv D.host.F v) e := by
    show inclR (Fv D.host.F v) (D.sp.cm.sig e) = _
    exact (congrArg _ he).trans (map_neg _ _)
  have hgc : ∀ h ∈ Formalism.UG.UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv D.host.F v) D.sp.cm.sig) (JR (Fv D.host.F v) V.gram),
      ((GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig V.gram g).1) * (h : Matrix (Fin V.rank) (Fin V.rank) _) =
        (h : Matrix (Fin V.rank) (Fin V.rank) _) * ((GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig V.gram g).1) := by
    intro h hh
    let h' : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v := ⟨h, hh⟩
    have e1 := congrArg (fun x => (GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig V.gram x).1)
      (Subgroup.mem_center_iff.1 hg h')
    simp only [map_mul, Units.val_mul] at e1
    exact e1.symm
  exact scalar_of_comm_UJ (Fv D.host.F v)
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv D.host.F v) D.sp.cm.sig) (GlobalTheory.Doubling.sigR_invol hσ)
    (JR (Fv D.host.F v) V.gram) hJ
    (GlobalTheory.Doubling.isUnit_det_JR (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero)
    (inclR (Fv D.host.F v) e) ((isUnit_iff_ne_zero.2 he0).map _) hδσ
    ((GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig V.gram g).1) hgc

end GlobalTheory.CenterLocU

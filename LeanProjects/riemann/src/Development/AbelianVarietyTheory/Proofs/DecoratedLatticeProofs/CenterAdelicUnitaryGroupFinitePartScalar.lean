import Mathlib
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory.CentreScalar

open Matrix Formalism.UG

section Alg

variable {E : Type} [Field E] [CharZero E] {n : Type} [Fintype n] [DecidableEq n]

theorem cT_smul' (σ : E →+* E) (c : E) (M : Matrix n n E) : cT σ (c • M) = σ c • cT σ M := by
  ext i j; simp [cT]

theorem cT_add' (σ : E →+* E) (M N : Matrix n n E) : cT σ (M + N) = cT σ M + cT σ N := by
  ext i j; simp [cT]

theorem cT_sub' (σ : E →+* E) (M N : Matrix n n E) : cT σ (M - N) = cT σ M - cT σ N := by
  ext i j; simp [cT]

theorem cT_natCast' (σ : E →+* E) (N : ℕ) : cT σ (N : Matrix n n E) = N := by
  ext i j
  simp only [cT, transpose_apply, map_apply, Matrix.natCast_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem map_natCast' {R : Type} [CommRing R] (ψ : E →+* R) (N : ℕ) : (N : Matrix n n E).map ψ = N := by
  ext i j
  simp only [map_apply, Matrix.natCast_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem commute_of_skew {R : Type} [CommRing R] (ψ : E →+* R) (σ : E →+* E) (J : Matrix n n E) (hJ : J.det ≠ 0)
    (Z : Matrix n n R) (hZ : ∀ g ∈ UJ σ J, Commute Z ((g : Matrix n n E).map ψ))
    (A : Matrix n n E) (hA : cT σ A * J + J * A = 0) : Commute Z (A.map ψ) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (A.charpoly).eval (((k + 1 : ℕ) : E)) ≠ 0 := by
    by_contra h
    push_neg at h
    have hfin : {x : E | A.charpoly.IsRoot x}.Finite :=
      Polynomial.finite_setOf_isRoot A.charpoly_monic.ne_zero
    have hsub : Set.range (fun k : ℕ => (((k + 1 : ℕ) : E))) ⊆ {x | A.charpoly.IsRoot x} := by
      rintro _ ⟨k, rfl⟩; exact h k
    have hinj : Function.Injective (fun k : ℕ => (((k + 1 : ℕ) : E))) := fun a b hab => by
      have := Nat.cast_injective (R := E) hab
      omega
    exact Set.infinite_range_of_injective hinj (hfin.subset hsub)
  set N : ℕ := k + 1 with hNdef
  set s : Matrix n n E := (N : Matrix n n E) with hs
  set B : Matrix n n E := s - A with hBdef
  set P : Matrix n n E := s + A with hPdef
  have hB : B.det ≠ 0 := by
    rw [hBdef, hs, ← map_natCast (Matrix.scalar n) N, ← Matrix.eval_charpoly]; exact hk
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have hBBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBu
  have hBiB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBu
  have hsA : s * A = A * s := (Nat.cast_commute N A).eq
  have hcs : cT σ s = s := cT_natCast' σ N
  have hcA : cT σ A * J = -(J * A) := eq_neg_of_add_eq_zero_left hA
  have key : cT σ P * J * P = cT σ B * J * B := by
    rw [hPdef, hBdef, cT_add', cT_sub', hcs]
    have e1 : (s + cT σ A) * J * (s + A) - (s - cT σ A) * J * (s - A)
        = (2 : ℕ) • (s * J * A + cT σ A * J * s) := by noncomm_ring
    have e2 : cT σ A * J * s = s * (cT σ A * J) := by
      rw [← (Nat.cast_commute N (cT σ A * J)).eq]
    have e3 : s * J * A + cT σ A * J * s = 0 := by
      rw [e2, hcA, Matrix.mul_assoc, ← Matrix.mul_add, add_neg_cancel, Matrix.mul_zero]
    rw [e3, smul_zero] at e1
    exact sub_eq_zero.1 e1
  set g : Matrix n n E := P * B⁻¹ with hgdef
  have hg : cT σ g * J * g = J := by
    rw [hgdef, cT_mul]
    calc cT σ B⁻¹ * cT σ P * J * (P * B⁻¹) = cT σ B⁻¹ * (cT σ P * J * P) * B⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = cT σ B⁻¹ * (cT σ B * J * B) * B⁻¹ := by rw [key]
      _ = (cT σ B⁻¹ * cT σ B) * J * (B * B⁻¹) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [← cT_mul, hBBi, cT_one, Matrix.one_mul, Matrix.mul_one]
  have hgdet : g.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hg
    rw [det_mul, det_mul, h0, mul_zero] at this
    exact hJ this.symm
  let g' : GL n E := Matrix.GeneralLinearGroup.mkOfDetNeZero g hgdet
  have hg'm : g' ∈ UJ σ J := by
    show cT σ (g' : Matrix n n E) * J * (g' : Matrix n n E) = J
    exact hg
  have hZg : Commute Z (g.map ψ) := hZ g' hg'm

  have hgB : g * B = P := by rw [hgdef, Matrix.mul_assoc, hBiB, Matrix.mul_one]
  have hBP : B * P = P * B := by
    rw [hBdef, hPdef]
    simp only [sub_mul, mul_sub, add_mul, mul_add, hsA]
    abel
  have hB1g : B * (1 + g) = ((2 * N : ℕ) : Matrix n n E) := by
    rw [Matrix.mul_add, Matrix.mul_one, hgdef, ← Matrix.mul_assoc, hBP, Matrix.mul_assoc, hBBi, Matrix.mul_one,
      hBdef, hPdef, hs]
    push_cast
    rw [two_mul]
    abel

  set X : Matrix n n R := Z * A.map ψ - A.map ψ * Z with hX
  have hsR : s.map ψ = (N : Matrix n n R) := by rw [hs]; exact map_natCast' ψ N
  have hZs : Z * (N : Matrix n n R) = (N : Matrix n n R) * Z := ((Nat.cast_commute N Z).eq).symm
  have hPR : P.map ψ = (N : Matrix n n R) + A.map ψ := by
    rw [hPdef, Matrix.map_add _ (map_add ψ), hsR]
  have hBR : B.map ψ = (N : Matrix n n R) - A.map ψ := by
    rw [hBdef, Matrix.map_sub _ (map_sub ψ), hsR]
  have hgBR : g.map ψ * B.map ψ = P.map ψ := by rw [← Matrix.map_mul, hgB]
  have h1 : Z * P.map ψ - P.map ψ * Z = X := by
    rw [hPR, hX, Matrix.mul_add, Matrix.add_mul, hZs]; abel
  have h2 : Z * B.map ψ - B.map ψ * Z = -X := by
    rw [hBR, hX, Matrix.mul_sub, Matrix.sub_mul, hZs]; abel
  have h3 : Z * P.map ψ - P.map ψ * Z = g.map ψ * (Z * B.map ψ - B.map ψ * Z) := by
    rw [← hgBR, Matrix.mul_sub, ← Matrix.mul_assoc, hZg.eq, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [h1, h2] at h3
  have h4 : (1 + g.map ψ) * X = 0 := by
    calc (1 + g.map ψ) * X = X + g.map ψ * X := by rw [Matrix.add_mul, Matrix.one_mul]
      _ = 0 := by nth_rewrite 1 [h3]; rw [Matrix.mul_neg, neg_add_cancel]
  have h5 : ((2 * N : ℕ) : Matrix n n R) * X = 0 := by
    have : ((B * (1 + g)).map ψ) * X = 0 := by
      rw [Matrix.map_mul, Matrix.map_add _ (map_add ψ), Matrix.map_one _ (map_zero ψ) (map_one ψ), Matrix.mul_assoc, h4,
        Matrix.mul_zero]
    rwa [hB1g, map_natCast'] at this
  have hN0 : ((2 * N : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hinv : ψ (((2 * N : ℕ) : E)⁻¹) * ((2 * N : ℕ) : R) = 1 := by
    rw [← map_natCast ψ, ← map_mul, inv_mul_cancel₀ hN0, map_one]
  have hX0 : X = 0 := by
    calc X = (ψ (((2 * N : ℕ) : E)⁻¹) * ((2 * N : ℕ) : R)) • X := by rw [hinv, one_smul]
      _ = ψ (((2 * N : ℕ) : E)⁻¹) • (((2 * N : ℕ) : Matrix n n R) * X) := by
          rw [mul_smul, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
      _ = 0 := by rw [h5, smul_zero]
  exact sub_eq_zero.1 hX0

end Alg

end GlobalTheory.CentreScalar

namespace GlobalTheory.CentreScalar

open Matrix Formalism.UG

section Alg2

variable {E : Type} [Field E] [CharZero E] {n : Type} [Fintype n] [DecidableEq n]

theorem commute_all {R : Type} [CommRing R] (ψ : E →+* R) (σ : E →+* E) (hσσ : ∀ x, σ (σ x) = x)
    (δ : E) (hδ : σ δ = -δ) (hδ0 : δ ≠ 0) (J : Matrix n n E) (hJh : cT σ J = J) (hJ : J.det ≠ 0)
    (Z : Matrix n n R) (hZ : ∀ g ∈ UJ σ J, Commute Z ((g : Matrix n n E).map ψ))
    (M : Matrix n n E) : Commute Z (M.map ψ) := by
  let S : Submodule E (Matrix n n E) :=
    { carrier := {M | Commute Z (M.map ψ)}
      add_mem' := by
        intro a b ha hb
        show Commute Z ((a + b).map ψ)
        rw [Matrix.map_add _ (map_add ψ)]
        exact ha.add_right hb
      zero_mem' := by
        show Commute Z ((0 : Matrix n n E).map ψ)
        rw [Matrix.map_zero _ (map_zero ψ)]
        exact Commute.zero_right Z
      smul_mem' := by
        intro c a ha
        show Commute Z ((c • a).map ψ)
        have : (c • a).map ψ = ψ c • a.map ψ := by ext i j; simp
        rw [this]
        exact ha.smul_right (ψ c) }
  have hmem : ∀ M, M ∈ S ↔ Commute Z (M.map ψ) := fun M => Iff.rfl
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ
  have hcc : ∀ N : Matrix n n E, cT σ (cT σ N) = N := by
    intro N; ext i j; simp [cT, hσσ]
  have hskew : ∀ K : Matrix n n E, cT σ K = -K → J⁻¹ * K ∈ S := by
    intro K hK
    rw [hmem]
    refine commute_of_skew ψ σ J hJ Z hZ _ ?_
    rw [cT_mul, hK, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv J hJu, Matrix.one_mul]
    have : cT σ J⁻¹ * J = 1 := by
      calc cT σ J⁻¹ * J = cT σ J⁻¹ * cT σ J := by rw [hJh]
        _ = cT σ (J * J⁻¹) := (cT_mul σ J J⁻¹).symm
        _ = 1 := by rw [Matrix.mul_nonsing_inv J hJu, cT_one]
    rw [_root_.neg_mul, _root_.neg_mul, Matrix.mul_assoc, this, Matrix.mul_one, neg_add_cancel]
  have hall : ∀ N : Matrix n n E, J⁻¹ * N ∈ S := by
    intro N
    have hK1 : cT σ (N - cT σ N) = -(N - cT σ N) := by
      rw [cT_sub', hcc]; abel
    have hK2 : cT σ (δ • (N + cT σ N)) = -(δ • (N + cT σ N)) := by
      rw [cT_smul', cT_add', hcc, hδ, neg_smul, add_comm (cT σ N) N]
    have hdec : N = (1 / 2 : E) • (N - cT σ N) + (2 * δ)⁻¹ • (δ • (N + cT σ N)) := by
      rw [smul_smul, show (2 * δ)⁻¹ * δ = (1 / 2 : E) by field_simp]
      module
    rw [hdec, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
    exact S.add_mem (S.smul_mem _ (hskew _ hK1)) (S.smul_mem _ (hskew _ hK2))
  have := hall (J * M)
  rwa [Matrix.nonsing_inv_mul_cancel_left _ _ hJu] at this

theorem eq_smul_one {R : Type} [CommRing R] (ψ : E →+* R) (σ : E →+* E) (hσσ : ∀ x, σ (σ x) = x)
    (δ : E) (hδ : σ δ = -δ) (hδ0 : δ ≠ 0) (J : Matrix n n E) (hJh : cT σ J = J) (hJ : J.det ≠ 0)
    (Z : Matrix n n R) (hZ : ∀ g ∈ UJ σ J, Commute Z ((g : Matrix n n E).map ψ)) :
    ∃ c : R, Z = c • (1 : Matrix n n R) := by
  have h : Z ∈ Set.range (Matrix.scalar n) := by
    apply Matrix.mem_range_scalar_of_commute_single
    intro i j _
    have := commute_all ψ σ hσσ δ hδ hδ0 J hJh hJ Z hZ (Matrix.single i j 1)
    rw [Matrix.map_single, map_one] at this
    exact this.symm
  obtain ⟨c, hc⟩ := h
  exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

end Alg2

end GlobalTheory.CentreScalar

noncomputable section

namespace GlobalTheory.CentreScalar

open Matrix Formalism.UG Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

def ratE (D : D7) : D.host.E →+* Formalism.IndefR.Lev.EAf D :=
  (Formalism.IndefR.Lev.swapAE D).comp
    ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom.comp
      (inclR (AF D.host.F)))

def ratPt {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (γ : GL (Fin V.rank) D.host.E)
    (hγ : γ ∈ UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) : GA D V :=
  ⟨bc (inclR (F := D.host.F) (AF D.host.F)) γ, by
    show cT (sigR (AF D.host.F) D.sp.cm.sig) ((γ : Matrix _ _ _).map (inclR (F := D.host.F) (AF D.host.F))) *
        JR (AF D.host.F) V.gram * (γ : Matrix _ _ _).map (inclR (F := D.host.F) (AF D.host.F)) = JR (AF D.host.F) V.gram
    rw [GlobalTheory.AutFunCounterexample.cT_map_gen, JR, ← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun M => M.map (inclR (F := D.host.F) (AF D.host.F))) hγ⟩

theorem finE_ratPt {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (γ : GL (Fin V.rank) D.host.E)
    (hγ : γ ∈ UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) :
    (Formalism.IndefR.Lev.finE V (ratPt V γ hγ)).val =
      (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (ratE D) := rfl

theorem finE_center_scalar : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (z : GA D V), z ∈ Subgroup.center (GA D V) →
    z ∈ GfC V → ∃ c : Formalism.IndefR.Lev.EAf D,
      (Formalism.IndefR.Lev.finE V z).val = c • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) := by
  intro D V z hz _
  set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσdef
  have hσσ : ∀ x, σ (σ x) = x := fun x => star_star x
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra h
    push_neg at h
    have htop : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rw [Algebra.mem_bot]
      obtain ⟨a, ha⟩ := (D.sp.cm.fixed y).1 (h y)
      exact ⟨a, ha⟩
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 htop
    rw [D.sp.cm.deg2] at h1
    norm_num at h1
  refine eq_smul_one (ratE D) σ hσσ (x - σ x) ?_ (sub_ne_zero.2 (Ne.symm hx)) V.gram
    (GlobalTheory.AutFunCounterexample.gram_herm V) (GlobalTheory.AutFunCounterexample.gram_det_ne V) _ ?_
  · rw [map_sub, hσσ]; abel
  · intro γ hγ
    have hc := (Subgroup.mem_center_iff.1 hz) (ratPt V γ hγ)
    have h2 := congrArg (fun g => (Formalism.IndefR.Lev.finE V g).val) hc
    simp only [map_mul, Units.val_mul] at h2
    rw [finE_ratPt] at h2
    exact h2.symm

end GlobalTheory.CentreScalar

end

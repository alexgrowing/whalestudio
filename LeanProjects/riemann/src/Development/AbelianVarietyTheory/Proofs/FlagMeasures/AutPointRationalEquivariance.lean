import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEquiv

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

noncomputable section

namespace GlobalTheory.PointEquivariance

section Transfer

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι K V) (X X' : InfinitePlace K → Matrix ι ι ℂ)
  (Φ : Submodule (𝓞 K) V ≃o Submodule (𝓞 K) V)

theorem sizeQ_eq (hz : ∀ N, zl (Formalism.HermitianLatticesTheory.realize b X') (Φ N) = zl (Formalism.HermitianLatticesTheory.realize b X) N)
    (hr : ∀ N, rkK (Φ N) = rkK N) (A B : Submodule (𝓞 K) V) :
    sizeQ b X' (Φ A) (Φ B) = sizeQ b X A B := by
  simp only [sizeQ, htQ, hz, hr]

theorem leastSize_eq (hz : ∀ N, zl (Formalism.HermitianLatticesTheory.realize b X') (Φ N) = zl (Formalism.HermitianLatticesTheory.realize b X) N)
    (hr : ∀ N, rkK (Φ N) = rkK N) (A : Submodule (𝓞 K) V) :
    leastSize b X' (Φ A) = leastSize b X A := by
  have hs : ∀ N, size b X' (Φ N) = size b X N := by
    intro N
    simp only [size, ht, hz, hr]
  unfold leastSize
  congr 1
  ext t
  constructor
  · rintro ⟨R, hR, h0, rfl⟩
    refine ⟨Φ.symm R, Φ.symm_apply_le.2 hR, fun h => h0 ?_, ?_⟩
    · rw [← Φ.apply_symm_apply R, h, Φ.map_bot]
    · rw [← hs, Φ.apply_symm_apply]
  · rintro ⟨R, hR, h0, rfl⟩
    refine ⟨Φ R, Φ.le_iff_le.2 hR, fun h => h0 ?_, hs R⟩
    rw [← Φ.map_bot] at h
    exact Φ.injective h

theorem largestSize_eq (hz : ∀ N, zl (Formalism.HermitianLatticesTheory.realize b X') (Φ N) = zl (Formalism.HermitianLatticesTheory.realize b X) N)
    (hr : ∀ N, rkK (Φ N) = rkK N) (A : Submodule (𝓞 K) V) :
    largestSize b X' (Φ A) = largestSize b X A := by
  have hsat : ∀ S, IsSat (Formalism.HermitianLatticesTheory.realize b X') (Φ A) (Φ S) ↔ IsSat (Formalism.HermitianLatticesTheory.realize b X) A S := by
    intro S
    simp only [IsSat, hz, Φ.le_iff_le]
  unfold largestSize
  congr 1
  ext t
  constructor
  · rintro ⟨S, hS, hne, rfl⟩
    refine ⟨Φ.symm S, ?_, fun h => hne ?_, ?_⟩
    · rw [← hsat, Φ.apply_symm_apply]
      exact hS
    · rw [← h, Φ.apply_symm_apply]
    · rw [← sizeQ_eq b X X' Φ hz hr, Φ.apply_symm_apply]
  · rintro ⟨S, hS, hne, rfl⟩
    exact ⟨Φ S, (hsat S).2 hS, fun h => hne (Φ.injective h), sizeQ_eq b X X' Φ hz hr A S⟩

omit [NumberField K] [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem sSup_eq (A : Submodule (𝓞 K) V) (p p' : Submodule (𝓞 K) V → Prop) (hp : ∀ N, p' (Φ N) ↔ p N) :
    sSup {N | N ≤ Φ A ∧ N ≠ ⊥ ∧ p' N} = Φ (sSup {N | N ≤ A ∧ N ≠ ⊥ ∧ p N}) := by
  rw [OrderIso.map_sSup Φ, ← sSup_image]
  congr 1
  ext N
  constructor
  · rintro ⟨hN, h0, hpN⟩
    refine ⟨Φ.symm N, ⟨Φ.symm_apply_le.2 hN, fun h => h0 ?_, ?_⟩, Φ.apply_symm_apply N⟩
    · rw [← Φ.apply_symm_apply N, h, Φ.map_bot]
    · rw [← hp, Φ.apply_symm_apply]
      exact hpN
  · rintro ⟨M, ⟨hM, h0, hpM⟩, rfl⟩
    refine ⟨Φ.le_iff_le.2 hM, fun h => h0 ?_, (hp M).2 hpM⟩
    rw [← Φ.map_bot] at h
    exact Φ.injective h

end Transfer

section Points

variable (I : AutInst) (x x' : I.GA)
  (Φ : Submodule (𝓞 I.E) (Fin I.n → I.E) ≃o Submodule (𝓞 I.E) (Fin I.n → I.E))

theorem step_eq (hl : lamX I x' = Φ (lamX I x))
    (hz : ∀ N, zl (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x')) (Φ N) = zl (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) N)
    (hr : ∀ N, rkK (Φ N) = rkK N) (t : ℝ) :
    stepLe I x' t = Φ (stepLe I x t) ∧ stepLt I x' t = Φ (stepLt I x t) := by
  have hls : ∀ N, Formalism.HN.largestSize (bas I) (frm I x') (Φ N) = Formalism.HN.largestSize (bas I) (frm I x) N :=
    largestSize_eq (bas I) (frm I x) (frm I x') Φ hz hr
  constructor
  · unfold stepLe
    rw [hl]
    exact sSup_eq Φ (lamX I x) _ _ (fun N => by rw [hls])
  · unfold stepLt
    rw [hl]
    exact sSup_eq Φ (lamX I x) _ _ (fun N => by rw [hls])

theorem hasType_of (hl : lamX I x' = Φ (lamX I x))
    (hz : ∀ N, zl (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x')) (Φ N) = zl (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) N)
    (hr : ∀ N, rkK (Φ N) = rkK N) {m : ℕ} (j : Fin m → ℕ) (τ : Fin m → ℝ) (h : HasType I x j τ) :
    HasType I x' j τ := by
  obtain ⟨S, ⟨h0, hmono, hlast, hτ, hi, hall⟩, hrk⟩ := h
  have hst := fun t => step_eq I x x' Φ hl hz hr t
  refine ⟨fun i => Φ (S i), ⟨?_, Φ.strictMono.comp hmono, ?_, hτ, fun i => ?_, fun t ht => ?_⟩, fun i => ?_⟩
  · dsimp only
    rw [h0, Φ.map_bot]
  · dsimp only
    rw [hlast, (hst _).2]
  · obtain ⟨h1, h2, h3, h4⟩ := hi i
    refine ⟨h1, h2, ?_, ?_⟩
    · dsimp only
      rw [h3, (hst _).1]
    · dsimp only
      rw [sizeQ_eq (bas I) (frm I x) (frm I x') Φ hz hr]
      exact h4
  · obtain ⟨k, hk⟩ := hall t ht
    exact ⟨k, by dsimp only; rw [hk, (hst t).1]⟩
  · dsimp only
    rw [hr, hr]
    exact hrk i

theorem lamX_eq : lamX I x = Formalism.UG.CS.globLat (F := I.F) (x.2 : GL (Fin I.n) _) I.L := by
  have hL : I.Lf = Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    rw [AutInst.Lf, lamAf, Formalism.UG.latS, Set.image_eq_range]
    rfl
  have hset : {y : Fin I.n → I.E | I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf} =
      (Formalism.UG.CS.globLat (F := I.F) (x.2 : GL (Fin I.n) _) I.L : Set (Fin I.n → I.E)) := by
    ext y
    rw [hL]
    rfl
  rw [lamX, hset, Submodule.span_eq]

theorem embedding_eq (w : InfinitePlace I.E) :
    w.embedding = I.φ (w.comap (algebraMap I.F I.E)) ∨
      w.embedding = (starRingEnd ℂ).comp (I.φ (w.comap (algebraMap I.F I.E))) := by
  have hcm := I.cm
  have hconj : ∀ (ψ : I.E →+* ℂ) (e : I.E), ψ (star e) = starRingEnd ℂ (ψ e) := hcm.cmUnram.2.1
  have hF : ∀ c : I.F, w.embedding (algebraMap I.F I.E c) =
      I.φ (w.comap (algebraMap I.F I.E)) (algebraMap I.F I.E c) := by
    intro c
    rw [I.φ_over]
    have hmk : w.comap (algebraMap I.F I.E) = InfinitePlace.mk (w.embedding.comp (algebraMap I.F I.E)) := by
      conv_lhs => rw [← InfinitePlace.mk_embedding w]
      exact InfinitePlace.comap_mk _ _
    have hre : ComplexEmbedding.IsReal (w.embedding.comp (algebraMap I.F I.E)) := by
      have := hcm.totReal
      rw [← InfinitePlace.isReal_mk_iff, ← hmk]
      exact IsTotallyReal.isReal _
    rw [hmk]
    rcases InfinitePlace.embedding_mk_eq (w.embedding.comp (algebraMap I.F I.E)) with h | h
    · rw [h]
      rfl
    · rw [h, ComplexEmbedding.isReal_iff.1 hre]
      rfl
  generalize I.φ (w.comap (algebraMap I.F I.E)) = ψ at hF ⊢
  have hpt : ∀ e : I.E, ψ e = w.embedding e ∨ ψ e = starRingEnd ℂ (w.embedding e) := by
    intro e
    obtain ⟨s, hs⟩ := (hcm.fixed (e + star e)).1 (by rw [star_add, star_star, add_comm])
    obtain ⟨p, hp⟩ := (hcm.fixed (e * star e)).1 (by rw [star_mul, star_star, mul_comm])
    have ht : ψ e + ψ (star e) = w.embedding e + w.embedding (star e) := by
      rw [← map_add, ← map_add, ← hs]
      exact (hF s).symm
    have hn : ψ e * ψ (star e) = w.embedding e * w.embedding (star e) := by
      rw [← map_mul, ← map_mul, ← hp]
      exact (hF p).symm
    have h0 : (ψ e - w.embedding e) * (ψ e - w.embedding (star e)) = 0 := by
      linear_combination (ψ e) * ht - hn
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · rw [← hconj]
      exact Or.inr (sub_eq_zero.1 h)
  by_cases h1 : ψ = w.embedding
  · exact Or.inl h1.symm
  · right
    by_cases h2 : ψ = (starRingEnd ℂ).comp w.embedding
    · ext e
      rw [RingHom.comp_apply, h2, RingHom.comp_apply, Complex.conj_conj]
    · exfalso
      obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 h1
      obtain ⟨b, hb⟩ := DFunLike.ne_iff.1 h2
      rw [RingHom.comp_apply] at hb
      have ha' := (hpt a).resolve_left ha
      have hb' := (hpt b).resolve_right hb
      rcases hpt (a + b) with h | h
      · rw [map_add, map_add, hb'] at h
        exact ha (add_right_cancel h)
      · rw [map_add, map_add, map_add, ha'] at h
        exact hb (add_left_cancel h)

end Points

section Rational

variable (I : AutInst) (x a : I.GA) (γ : GL (Fin I.n) I.E)

theorem frm_det (w : InfinitePlace I.E) : IsUnit (frm I x w).det := by
  have h1 : IsUnit (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))).det := by
    rw [Matrix.det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit _)).mul
      ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _))
  simp only [frm]
  split_ifs
  · exact h1
  · have e := RingHom.map_det (starRingEnd ℂ)
      (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]
    exact h1.map _

theorem frm_mul (k : I.GA) (w : InfinitePlace I.E) :
    frm I (x * k) w = frm I x w * uMat (k.1 (w.comap (algebraMap I.F I.E))) ∨
      frm I (x * k) w = frm I x w * (uMat (k.1 (w.comap (algebraMap I.F I.E)))).map (starRingEnd ℂ) := by
  have hm : uMat ((x * k).1 (w.comap (algebraMap I.F I.E))) =
      uMat (x.1 (w.comap (algebraMap I.F I.E))) * uMat (k.1 (w.comap (algebraMap I.F I.E))) := rfl
  simp only [frm]
  by_cases h : w.embedding = I.φ (w.comap (algebraMap I.F I.E))
  · left
    rw [if_pos h, if_pos h, hm, Matrix.mul_assoc]
  · right
    rw [if_neg h, if_neg h, hm, ← Matrix.mul_assoc, Matrix.map_mul]

theorem frm_rat
    (h : ∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
    (w : InfinitePlace I.E) :
    frm I (a * x) w = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map w.embedding * frm I x w := by
  have hP : I.P (w.comap (algebraMap I.F I.E)) * (I.P (w.comap (algebraMap I.F I.E)))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit _))
  have hm : uMat ((a * x).1 (w.comap (algebraMap I.F I.E))) =
      uMat (a.1 (w.comap (algebraMap I.F I.E))) * uMat (x.1 (w.comap (algebraMap I.F I.E))) := rfl
  have key : I.P (w.comap (algebraMap I.F I.E)) * uMat ((a * x).1 (w.comap (algebraMap I.F I.E))) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ (w.comap (algebraMap I.F I.E))) *
        (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))) := by
    rw [hm, h]
    simp only [← Matrix.mul_assoc, hP, Matrix.one_mul]
  simp only [frm]
  by_cases h' : w.embedding = I.φ (w.comap (algebraMap I.F I.E))
  · rw [if_pos h', if_pos h', key, h']
  · have he := (embedding_eq I w).resolve_left h'
    rw [if_neg h', if_neg h', key, Matrix.map_mul, he, Matrix.map_map]
    rfl

theorem fcoord_rat
    (h : ∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
    (w : InfinitePlace I.E) (y : Fin I.n → I.E) :
    Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I (a * x)) w ((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) =
      Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y := by
  have hvec : Formalism.HermitianLatticesTheory.vecAt (bas I) w ((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map w.embedding *ᵥ Formalism.HermitianLatticesTheory.vecAt (bas I) w y := by
    ext i
    simp only [Formalism.HermitianLatticesTheory.vecAt, Pi.basisFun_repr]
    exact RingHom.map_mulVec _ _ _ _
  have hγ : IsUnit ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map w.embedding).det := by
    have e := RingHom.map_det w.embedding (γ : Matrix (Fin I.n) (Fin I.n) I.E)
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).map _
  simp only [Formalism.HermitianLatticesTheory.fcoord, hvec, frm_rat I x a γ h w, Matrix.mul_inv_rev, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hγ, Matrix.mul_one]

def ratEquiv : (Fin I.n → I.E) ≃ₗ[I.E] (Fin I.n → I.E) :=
  LinearEquiv.ofLinear (Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E))
    (Matrix.toLin' ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E))
    (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])

def ratIso : Submodule (𝓞 I.E) (Fin I.n → I.E) ≃o Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  Submodule.orderIsoMapComap ((ratEquiv I γ).restrictScalars (𝓞 I.E))

theorem ratIso_apply (N : Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    ratIso I γ N =
      N.map ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E)) := rfl

theorem rkK_ratIso (N : Submodule (𝓞 I.E) (Fin I.n → I.E)) : rkK (ratIso I γ N) = rkK N := by
  unfold Formalism.HN.rkK
  rw [ratIso_apply, Submodule.map_coe, LinearMap.coe_restrictScalars]
  have e : Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E) =
      ((ratEquiv I γ : (Fin I.n → I.E) ≃ₗ[I.E] (Fin I.n → I.E)) : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E)) := rfl
  rw [e, Submodule.span_image, LinearEquiv.finrank_map_eq]

theorem zl_ratIso
    (h : ∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
    (N : Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    zl (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (a * x))) (ratIso I γ N) =
      zl (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) N := by
  have hr : ∀ y, Formalism.HermitianLatticesTheory.realize (bas I) (frm I (a * x)) ((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) =
      Formalism.HermitianLatticesTheory.realize (bas I) (frm I x) y := by
    intro y
    have hraw : Formalism.HermitianLatticesTheory.realizeRaw (bas I) (frm I (a * x)) ((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) =
        Formalism.HermitianLatticesTheory.realizeRaw (bas I) (frm I x) y := by
      funext p
      simp only [Formalism.HermitianLatticesTheory.realizeRaw, AddMonoidHom.coe_mk, ZeroHom.coe_mk, fcoord_rat I x a γ h]
    simp only [Formalism.HermitianLatticesTheory.realize, AddMonoidHom.coe_comp, Function.comp_apply, hraw]
  rw [ratIso_apply]
  unfold zl
  ext z
  show z ∈ AddSubgroup.map _ _ ↔ z ∈ AddSubgroup.map _ _
  simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_map,
    LinearMap.coe_restrictScalars, Matrix.toLin'_apply, exists_exists_and_eq_and, hr]

theorem lamX_rat
    (h : I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))) :
    lamX I (a * x) = ratIso I γ (lamX I x) := by
  have hinv : I.fmat a.2⁻¹ = ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map
      (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
    have h1 : I.fmat a.2 * ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map
        (Formalism.UG.inclE (F := I.F) (Af I.F)) = 1 := by
      rw [h, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : I.fmat a.2⁻¹ * I.fmat a.2 = 1 := Units.inv_mul (a.2 : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)))
    calc I.fmat a.2⁻¹ = I.fmat a.2⁻¹ * (I.fmat a.2 * ((γ⁻¹ : GL (Fin I.n) I.E) :
          Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))) := by
          rw [h1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hmem : ∀ y : Fin I.n → I.E,
      (I.fmat (a * x).2⁻¹ *ᵥ fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) =
        I.fmat x.2⁻¹ *ᵥ fun i => Formalism.UG.inclE (F := I.F) (Af I.F)
          ((((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) i) := by
    intro y
    have e1 : I.fmat (a * x).2⁻¹ = I.fmat x.2⁻¹ * I.fmat a.2⁻¹ := by
      show ((((a.2 * x.2)⁻¹ : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) :
        Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) = _
      rw [_root_.mul_inv_rev]
      rfl
    rw [e1, ← Matrix.mulVec_mulVec, hinv]
    congr 1
    ext i
    exact (RingHom.map_mulVec _ _ _ i).symm
  have hS : {y : Fin I.n → I.E | I.fmat (a * x).2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf} =
      ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E)) ''
        {y : Fin I.n → I.E | I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_image, hmem, LinearMap.coe_restrictScalars, Matrix.toLin'_apply]
    constructor
    · intro hy
      refine ⟨_, hy, ?_⟩
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    · rintro ⟨z, hz, rfl⟩
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at *
      exact hz
  rw [ratIso_apply]
  unfold lamX
  rw [hS, Submodule.span_image]

theorem lamX_mul_eq_iff (k : I.GA) : k.2 ∈ I.Kset ↔ lamX I (x * k) = lamX I x := by
  have hL : I.Lf = Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    rw [AutInst.Lf, lamAf, Formalism.UG.latS, Set.image_eq_range]
    rfl
  have hmem : ∀ (G : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) (y : Fin I.n → I.E),
      y ∈ Formalism.UG.CS.globLat (F := I.F) G I.L ↔
        ((G⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) :
          Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ
            (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf := by
    intro G y
    rw [hL]
    rfl
  have hK : k.2 ∈ I.Kset ↔ ∀ v, v ∈ I.Lf ↔
      ((k.2 : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) :
        Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ v ∈ I.Lf := Iff.rfl
  have hxk : ((x * k).2 : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) =
      (x.2 : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *
        (k.2 : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) := rfl
  rw [hK, lamX_eq, lamX_eq, hxk]
  generalize (x.2 : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) = g
  generalize (k.2 : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) = u
  constructor
  · intro hk
    ext y
    rw [hmem, hmem, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, hk,
      Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  · intro he v
    have hrec := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds I.F I.E (Fin I.n) I.L
      (Module.Finite.iff_fg.2 I.L_fg) I.L_span
    have h1 := hrec (g * u) ((g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ
      ((u : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ v))
    have h2 := hrec g ((g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ
      ((u : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ v))
    rw [he] at h1
    have h3 := h1.symm.trans h2
    have e1 : (((g * u)⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) :
        Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ
          ((g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ
            ((u : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ v)) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, mul_assoc,
        inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have e2 : ((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) :
        Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ
          ((g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ
            ((u : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ v)) =
          (u : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ v := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [e1, e2] at h3
    rw [hL]
    exact h3

end Rational

theorem equivariance : ∀ (I : AutInst) (x : I.GA) (γ : GL (Fin I.n) I.E) (a : I.GA), γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) → I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) → lamX I (a * x) = (lamX I x).map ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E)) ∧ (∀ w y, Formalism.HermitianLatticesTheory.normAt (bas I) (frm I (a * x)) w ((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) = Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y) ∧ least I (a * x) = least I x ∧ (∀ t, stepLe I (a * x) t = (stepLe I x t).map ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E)) ∧ stepLt I (a * x) t = (stepLt I x t).map ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E))) ∧ (∀ (m : ℕ) (j : Fin m → ℕ) (τ : Fin m → ℝ), HasType I (a * x) j τ ↔ HasType I x j τ) ∧ ((x⁻¹ * a * x).2 ∈ I.Kset ↔ (lamX I x).map ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E)) = lamX I x) ∧ ∀ w, (frm I x w)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map w.embedding * frm I x w = uMat ((x⁻¹ * a * x).1 (w.comap (algebraMap I.F I.E))) ∨ (frm I x w)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map w.embedding * frm I x w = (uMat ((x⁻¹ * a * x).1 (w.comap (algebraMap I.F I.E)))).map (starRingEnd ℂ) := by
  intro I x γ a _hγ h1 h2
  have hl : lamX I (a * x) = ratIso I γ (lamX I x) := lamX_rat I x a γ h2
  have hz : ∀ N, zl (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (a * x))) (ratIso I γ N) =
      zl (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) N := zl_ratIso I x a γ h1
  have hr : ∀ N, rkK (ratIso I γ N) = rkK N := rkK_ratIso I γ
  have hl' : lamX I x = (ratIso I γ).symm (lamX I (a * x)) := by
    rw [hl, OrderIso.symm_apply_apply]
  have hz' : ∀ N, zl (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) ((ratIso I γ).symm N) =
      zl (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (a * x))) N := by
    intro N
    rw [← hz, OrderIso.apply_symm_apply]
  have hr' : ∀ N, rkK ((ratIso I γ).symm N) = rkK N := by
    intro N
    rw [← hr, OrderIso.apply_symm_apply]
  have hxk : x * (x⁻¹ * a * x) = a * x := by
    rw [mul_assoc x⁻¹, mul_inv_cancel_left]
  refine ⟨by rw [hl, ratIso_apply], fun w y => ?_, ?_, fun t => ?_,
    fun m j τ => ⟨hasType_of I (a * x) x (ratIso I γ).symm hl' hz' hr' j τ,
      hasType_of I x (a * x) (ratIso I γ) hl hz hr j τ⟩, ?_, fun w => ?_⟩
  · simp only [Formalism.HermitianLatticesTheory.normAt, fcoord_rat I x a γ h1]
  · unfold least
    rw [hl]
    exact leastSize_eq (bas I) (frm I x) (frm I (a * x)) (ratIso I γ) hz hr (lamX I x)
  · rw [(step_eq I x (a * x) (ratIso I γ) hl hz hr t).1, (step_eq I x (a * x) (ratIso I γ) hl hz hr t).2,
      ratIso_apply, ratIso_apply]
    exact ⟨rfl, rfl⟩
  · rw [lamX_mul_eq_iff I x (x⁻¹ * a * x), hxk, hl, ratIso_apply]
  · have e1 := frm_mul I x (x⁻¹ * a * x) w
    rw [hxk, frm_rat I x a γ h1 w] at e1
    have hF := frm_det I x w
    rcases e1 with e | e
    · left
      rw [Matrix.mul_assoc, e, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hF, Matrix.one_mul]
    · right
      rw [Matrix.mul_assoc, e, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hF, Matrix.one_mul]

end GlobalTheory.PointEquivariance

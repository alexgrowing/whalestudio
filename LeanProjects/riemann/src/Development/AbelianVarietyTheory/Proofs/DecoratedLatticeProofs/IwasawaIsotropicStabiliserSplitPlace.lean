import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular

noncomputable section

namespace GlobalTheory.Core.Rk.IwFlagSplit

section Pure

variable {A R : Type} [CommRing A] [CommRing R] {n ρ s : Type} [Fintype n] [Fintype ρ] [Fintype s] [DecidableEq n]
  [DecidableEq ρ] [DecidableEq s]

theorem map_keeps (f : A →+* R) {M : Matrix n n A} {j : Matrix n ρ A} {p : Matrix ρ n A} (hp : p * j = 1)
    {a : Matrix ρ ρ R} (h : M.map f * j.map f = j.map f * a) : (M * j).map f = (j * (p * (M * j))).map f := by
  have h1 : p.map f * j.map f = 1 := by rw [← Matrix.map_mul, hp, Matrix.map_one _ (map_zero f) (map_one f)]
  rw [Matrix.map_mul (L := j), Matrix.map_mul (L := p), Matrix.map_mul, h, ← Matrix.mul_assoc (p.map f), h1,
    Matrix.one_mul]

def lev : (ρ ⊕ s) ⊕ ρ → ℕ := Sum.elim (Sum.elim (fun _ => 0) fun _ => 1) fun _ => 2

omit [DecidableEq ρ] [DecidableEq s] in

theorem keeps_cols (ε : n ≃ (ρ ⊕ s) ⊕ ρ) {e e' : Matrix n ρ A} {i : Matrix n s A} {B b : GL n A}
    (hB : B.1 = (Matrix.fromCols (Matrix.fromCols e i) e').submatrix id ε) (hb : b.1.BlockTriangular (lev ∘ ε)) :
    ∃ a : Matrix ρ ρ A, (B * b * B⁻¹).1 * e = e * a := by
  refine ⟨Matrix.of fun k l => b.1 (ε.symm (.inl (.inl k))) (ε.symm (.inl (.inl l))), ?_⟩
  have h : (B * b * B⁻¹).1 * B.1 = B.1 * b.1 := by rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
  generalize (B * b * B⁻¹).1 = x at h
  ext k l
  have h1 := congrFun (congrFun h k) (ε.symm (.inl (.inl l)))
  have h2 : ∀ t, b.1 (ε.symm (.inl (.inr t))) (ε.symm (.inl (.inl l))) = 0 := fun t => hb (by simp [lev])
  have h3 : ∀ t, b.1 (ε.symm (.inr t)) (ε.symm (.inl (.inl l))) = 0 := fun t => hb (by simp [lev])
  rw [hB, Matrix.mul_apply, Matrix.mul_apply, ← ε.symm.sum_comp fun t => _ * b.1 t _] at h1
  simpa [Matrix.mul_apply, h2, h3] using h1

omit [DecidableEq ρ] [DecidableEq s] in

theorem keeps_rows (ε : n ≃ (ρ ⊕ s) ⊕ ρ) {p p' : Matrix ρ n A} {q : Matrix s n A} {B b : GL n A}
    (hB : (B⁻¹).1 = (Matrix.fromRows (Matrix.fromRows p q) p').submatrix ε id) (hb : b.1.BlockTriangular (lev ∘ ε)) :
    ∃ c : Matrix ρ ρ A, p' * (B * b * B⁻¹).1 = c * p' := by
  refine ⟨Matrix.of fun k l => b.1 (ε.symm (.inr k)) (ε.symm (.inr l)), ?_⟩
  have h : (B⁻¹).1 * (B * b * B⁻¹).1 = b.1 * (B⁻¹).1 := by
    rw [← Units.val_mul, mul_assoc, inv_mul_cancel_left, Units.val_mul]
  generalize (B * b * B⁻¹).1 = x at h
  ext k l
  have h1 := congrFun (congrFun h (ε.symm (.inr k))) l
  have h2 : ∀ t, b.1 (ε.symm (.inr k)) (ε.symm (.inl t)) = 0 := fun t => hb (by rcases t with t | t <;> simp [lev])
  rw [hB, Matrix.mul_apply, Matrix.mul_apply, ← ε.symm.sum_comp fun t => b.1 _ t * _] at h1
  simpa [Matrix.mul_apply, h2] using h1

omit [DecidableEq s] [Fintype s] in

theorem keeps_dual {G x x' : Matrix n n A} {e f : Matrix n ρ A} {c : Matrix ρ ρ A} {xi Gi : Matrix n n A}
    (hx : x * xi = 1) (hG : G * Gi = 1) (h : x'.transpose * G * x = G) (hf : e.transpose * G * f = 1)
    (hc : e.transpose * G * x = c * (e.transpose * G)) : ∃ a : Matrix ρ ρ A, x' * e = e * a := by
  have h1 : e.transpose * G = c * (e.transpose * G * xi) := by
    rw [← Matrix.mul_assoc, ← hc, Matrix.mul_assoc _ x, hx, Matrix.mul_one]
  have h2 : c * (e.transpose * G * xi * f) = 1 := by rw [← Matrix.mul_assoc, ← h1, hf]
  have h3 := mul_eq_one_comm.1 h2
  generalize e.transpose * G * xi * f = c' at h3
  have h4 : e.transpose * G * xi = c' * (e.transpose * G) := by
    rw [h1, ← Matrix.mul_assoc c', h3, Matrix.one_mul, ← h1]
  have h5 : x'.transpose * G = G * xi := by
    conv_rhs => rw [← h, Matrix.mul_assoc, hx, Matrix.mul_one]
  refine ⟨c'.transpose, Matrix.transpose_injective ?_⟩
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    ← Matrix.mul_one (e.transpose * _), ← hG, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ G, h5, ← Matrix.mul_assoc, h4,
    Matrix.mul_assoc, Matrix.mul_assoc, hG, Matrix.mul_one]

end Pure

section Local

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open Formalism.UG (bc GLint)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)} {ρ s : Type} [Fintype ρ] [Fintype s] [DecidableEq ρ]
  [DecidableEq s]

theorem emb_keeps (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (q : GLoc σ J v) {j : Matrix (Fin n) ρ (AF F ⊗[F] E)}
    {p : Matrix ρ (Fin n) (AF F ⊗[F] E)} (hp : p * j = 1) {e : Matrix (Fin n) ρ E} (hj : j = e.map (inclR (AF F)))
    {a a' : Matrix ρ ρ (Fv F v)} (h1 : (splitHom σ J τ q).1 * e.map τ = e.map τ * a)
    (h2 : (splitHom σ J (τ.comp σ) q).1 * e.map (τ.comp σ) = e.map (τ.comp σ) * a') :
    (matHom _ σ J (emb σ J v q)).1 * j = j * (p * ((matHom _ σ J (emb σ J v q)).1 * j)) := by
  have key : ∀ (τ : E →ₐ[F] Fv F v) {a : Matrix ρ ρ (Fv F v)}, (splitHom σ J τ q).1 * e.map τ = e.map τ * a →
      (matHom _ σ J (emb σ J v q)).1.map (((splitProj τ).toRingHom).comp (compFin F E v)) *
        j.map (((splitProj τ).toRingHom).comp (compFin F E v)) =
        j.map (((splitProj τ).toRingHom).comp (compFin F E v)) * a := fun τ a ha => by
    have e1 : (matHom _ σ J (emb σ J v q)).1.map (((splitProj τ).toRingHom).comp (compFin F E v)) =
        (splitHom σ J τ q).1 := by
      conv_rhs => rw [← proj_emb_self σ J v q]
      rfl
    have e2 : j.map (((splitProj τ).toRingHom).comp (compFin F E v)) = e.map τ := by
      ext k l
      simp [hj, inclR, compFin]
    rw [e1, e2, ha]
  ext k l
  refine GlobalTheory.Doubling.adele_ext (fun w => ?_) fun u => ?_
  · have e1 : (matHom _ σ J (emb σ J v q)).1.map (compInf F E w) = 1 := by
      change (matHom _ σ J (projArch σ J w (emb σ J v q))).1 = 1
      rw [projArch_emb, map_one, Units.val_one]
    exact congrFun (congrFun (map_keeps (compInf F E w) hp (a := 1) (by rw [e1, Matrix.one_mul, Matrix.mul_one])) k) l
  · by_cases hu : u = v
    · subst hu
      exact split_ext h τ (congrFun (congrFun (map_keeps _ hp (key τ h1)) k) l)
        (congrFun (congrFun (map_keeps _ hp (key _ h2)) k) l)
    · have e1 : (matHom _ σ J (emb σ J v q)).1.map (compFin F E u) = 1 := by
        change (matHom _ σ J (proj σ J u (emb σ J v q))).1 = 1
        rw [proj_emb_ne σ J hu, map_one, Units.val_one]
      exact congrFun (congrFun (map_keeps (compFin F E u) hp (a := 1) (by rw [e1, Matrix.one_mul, Matrix.mul_one])) k) l

theorem exists_flag_basis (τ : E →ₐ[F] Fv F v) (hJ : IsHermND σ J) {e e' : Matrix (Fin n) ρ E}
    {i : Matrix (Fin n) s E} {p : Matrix ρ (Fin n) E} {q : Matrix s (Fin n) E} (ε : Fin n ≃ (ρ ⊕ s) ⊕ ρ)
    (hsum : e * p + i * q + e' * ((e.map σ)ᵀ * J) = 1) (hf : (e.map σ)ᵀ * J * e' = 1) :
    ∃ (B : GL (Fin n) (Fv F v)) (lv : Fin n → ℕ), ∀ g : GLoc σ J v, (B⁻¹ * splitHom σ J τ g * B).1.BlockTriangular lv →
      (∃ a : Matrix ρ ρ (Fv F v), (splitHom σ J τ g).1 * e.map τ = e.map τ * a) ∧
        ∃ a : Matrix ρ ρ (Fv F v), (splitHom σ J (τ.comp σ) g).1 * e.map (τ.comp σ) = e.map (τ.comp σ) * a := by
  have hm : ((e.map σ)ᵀ * J).map τ = (e.map (τ.comp σ))ᵀ * J.map τ := Matrix.map_mul (f := (τ : E →+* Fv F v))
  have hB : (Matrix.fromCols (Matrix.fromCols (e.map τ) (i.map τ)) (e'.map τ)).submatrix id ε *
      (Matrix.fromRows (Matrix.fromRows (p.map τ) (q.map τ)) ((e.map (τ.comp σ))ᵀ * J.map τ)).submatrix ε id = 1 := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows,
      ← hm]
    have := congrArg (τ : E →+* Fv F v).mapMatrix hsum
    rw [map_add, map_add, map_one] at this
    simp only [RingHom.mapMatrix_apply, Matrix.map_mul] at this
    rw [hm]
    exact this
  refine ⟨⟨_, _, hB, mul_eq_one_comm.1 hB⟩, lev ∘ ε, fun g hg => ?_⟩
  generalize hBe : (⟨_, _, hB, mul_eq_one_comm.1 hB⟩ : GL (Fin n) (Fv F v)) = B at hg
  have hx : B * (B⁻¹ * splitHom σ J τ g * B) * B⁻¹ = splitHom σ J τ g := by group
  obtain ⟨c, hc⟩ := keeps_rows ε (B := B) (by rw [← hBe]; rfl) hg
  refine ⟨hx ▸ keeps_cols ε (B := B) (by rw [← hBe]) hg, ?_⟩
  rw [hx] at hc
  refine keeps_dual (G := J.map τ) (f := e'.map τ) (Units.mul_inv _) (splitGram hJ τ).mul_inv (splitHom_unitary τ g) ?_ hc
  rw [← hm]
  exact (Matrix.map_mul (f := (τ : E →+* Fv F v))).symm.trans
    (by rw [hf, Matrix.map_one _ (map_zero _) (map_one _)])

theorem iwasawa_of_triangular (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (hL : IsSelfDualAt σ J L v) (Q : Subgroup (GLoc σ J v))
    (B : GL (Fin n) (Fv F v)) (lv : Fin n → ℕ)
    (hQ : ∀ g : GLoc σ J v, (B⁻¹ * splitHom σ J τ g * B).1.BlockTriangular lv → g ∈ Q) (y : GLoc σ J v) :
    ∃ q k : GLoc σ J v, q ∈ Q ∧ k ∈ stabLoc σ J L v ∧ y = q * k := by
  obtain ⟨β, hβ⟩ := exists_isSplitBasis τ L h
  have iw : ∀ x : GL (Fin n) (Fv F v), ∃ q ∈ Q, ∃ k ∈ stabLoc σ J L v,
      x * β = splitHom σ J τ q * B * β⁻¹ * splitHom σ J τ k * β := fun x => by
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    obtain ⟨b, hb, w, hw, e⟩ := GlobalTheory.SplitWeil.iwasawa_blockTriangular (Fv F v) (Fin n) lv (B⁻¹ * x * β)
    rw [← (GLint_eq_KO_and_princ_eq_KOne v n).1] at hw
    refine ⟨(splitEquivIn h hJ τ B).symm b, hQ _ ?_, (splitEquivIn h hJ τ β).symm w,
      (mem_stabLoc_iff_GLint h hJ hL hβ).2 ?_, ?_⟩
    · rwa [← splitEquivIn_apply h hJ, ContinuousMulEquiv.apply_symm_apply]
    · rwa [ContinuousMulEquiv.apply_symm_apply]
    · rw [splitHom_splitEquivIn_symm, splitHom_splitEquivIn_symm]
      calc x * β = B * (B⁻¹ * x * β) := by group
        _ = _ := by rw [e]; group
  obtain ⟨q₀, hq₀, k₀, hk₀, e₀⟩ := iw 1
  obtain ⟨q₁, hq₁, k₁, hk₁, e₁⟩ := iw (splitHom σ J τ y)
  refine ⟨q₁ * q₀⁻¹, k₀⁻¹ * k₁, mul_mem hq₁ (inv_mem hq₀), mul_mem (inv_mem hk₀) hk₁, splitHom_injective h hJ τ ?_⟩
  rw [mul_left_inj] at e₀ e₁
  rw [e₁, map_mul, map_mul, map_mul, map_inv, map_inv]
  generalize splitHom σ J τ q₀ = a₀, splitHom σ J τ q₁ = a₁, splitHom σ J τ k₀ = c₀, splitHom σ J τ k₁ = c₁ at e₀ ⊢
  rw [eq_inv_of_mul_eq_one_right e₀.symm]
  group

end Local

section Record

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

theorem iwasawa_stab_split : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (v : FinPl D), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → ∀ y : Gv T v, ∃ q k : Gv T v, emb D.sp.cm.sig T.gram v q ∈ stab d ∧ k ∈ stabLoc D.sp.cm.sig T.gram (frameLat T) v ∧ y = q * k := by
  intro D T T₀ r d v ⟨P, P', hne, hP, hP'⟩ y
  obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq (isCMExt_host D) (v := v) hne (HeightOneSpectrum.ext hP)
    (HeightOneSpectrum.ext hP')
  haveI := SelfDual.isLattice_frameLat T
  have hf : d.qY ⬝ d.e' = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.pY_jY)
  obtain ⟨B, lv, hB⟩ := exists_flag_basis τ (GlobalTheory.Doubling.isHermND_gram T) (e := d.e) (e' := d.e') (i := d.i₀)
    (p := d.qX) (q := d.q0) (Fintype.equivOfCardEq (by simp [← d.rank_add]; ring)) d.sum_eq_one_rat hf
  refine iwasawa_of_triangular (isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram T) τ (frameLat T)
    (SelfDual.isSelfDualAt_frameLat D T v) ((stab d).comap (emb D.sp.cm.sig T.gram v)) B lv (fun g hg => ?_) y
  obtain ⟨⟨a, ha⟩, a', ha'⟩ := hB g hg
  have h1 : mt T (emb D.sp.cm.sig T.gram v g) ⬝ d.jX =
      d.jX ⬝ (d.pX ⬝ (mt T (emb D.sp.cm.sig T.gram v g) ⬝ d.jX)) :=
    emb_keeps (isCMExt_host D) τ g d.pX_jX rfl ha ha'
  rw [Subgroup.mem_comap]
  generalize emb D.sp.cm.sig T.gram v g = x at h1 ⊢
  have h2 : (d.pX ⬝ (mt T x⁻¹ ⬝ d.jX)) ⬝ (d.pX ⬝ (mt T x ⬝ d.jX)) = 1 := by
    rw [Matrix.mul_assoc d.pX, Matrix.mul_assoc (mt T x⁻¹), ← h1, ← Matrix.mul_assoc (mt T x⁻¹), ← mt_mul,
      inv_mul_cancel, mt_one, Matrix.one_mul, d.pX_jX]
  exact ⟨⟨_, _, mul_eq_one_comm.1 h2, h2⟩, h1⟩

end Record

end GlobalTheory.Core.Rk.IwFlagSplit

end

import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL4.MemDualCrdLat
import Formalism.LocalToGlobal.Columns.BrpStarLatLattice
import Formalism.SharpRestriction.GlobalSchurBounds.TotallyPositiveTraceGeOfNormDiscr
import Formalism.LocalToGlobal.GlobalTheory.GL4.PZBasis

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.Herm Formalism.L2.Geo.Def.G1

section BC

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [IsTotallyComplex E]
  [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

theorem emb_hform (σ : E →+* ℂ) (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) {n : ℕ} (H : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) :
    σ (Formalism.DivisionValues.hform H x y) = ∑ i, ∑ j, starRingEnd ℂ (σ (x i)) * σ (H i j) * σ (y j) := by
  rw [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, smul_eq_mul, map_mul, map_mul, starRingEnd_apply, hσ, RingHom.id_apply]
  ring

theorem maj_ratHerm (hconj : ∀ (σ : E →+* ℂ) a, σ (star a) = starRingEnd ℂ (σ a)) {n : ℕ} (H : Matrix (Fin n) (Fin n) E)
    (X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace E)
    (hX : ((X v)⁻¹).conjTranspose * (X v)⁻¹ = H.map v.embedding) (x : Fin n → E) :
    majAt (Pi.basisFun E (Fin n)) X v x x = v.embedding (Formalism.DivisionValues.hform H x x) := by
  rw [emb_hform v.embedding (hconj _) H x x]
  have hkl : ∀ k l, ∑ i, star ((X v)⁻¹ i k) * (X v)⁻¹ i l = v.embedding (H k l) := fun k l => by
    have := congrFun (congrFun hX k) l
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using this
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Pi.basisFun_repr, Matrix.mulVec, dotProduct,
    starRingEnd_apply]
  conv_rhs => simp only [← hkl, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => enter [2, k]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [star_mul']
  ring

theorem re_comap (ρ : E →+* K) (w : InfinitePlace K) (z : E) : ((w.comap ρ).embedding z).re = (w.embedding (ρ z)).re := by
  have h1 : w.comap ρ = InfinitePlace.mk (w.embedding.comp ρ) := by
    rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  rw [h1]
  rcases InfinitePlace.embedding_mk_eq (w.embedding.comp ρ) with h | h
  · rw [h]; rfl
  · rw [h, ComplexEmbedding.conjugate_coe_eq]; simp

private theorem hform_crd_lemma (S : HSpace E) (y : S.V) :
    Formalism.DivisionValues.hform S.gram (crd S y) (crd S y) = S.hT y y := by
  unfold crd
  conv_rhs => rw [← S.frame.sum_equivFun y]
  rw [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, Finset.smul_sum, Formalism.BasicNotions.HSpace.gram,
    smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem normE (hc : CMData F E) (S : HSpace E) (X : InfinitePlace E → Matrix (Fin S.rank) (Fin S.rank) ℂ) (v : InfinitePlace E)
    (hX : ((X v)⁻¹).conjTranspose * (X v)⁻¹ = S.gram.map v.embedding) (y : S.V) :
    normAt (Pi.basisFun E (Fin S.rank)) X v (crd S y) = Real.sqrt ((v.embedding (S.hT y y)).re) := by
  have hm := maj_ratHerm hc.cmUnram.2.1 S.gram X v hX (crd S y)
  rw [hform_crd_lemma] at hm
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm
  congr 1
  rw [← hm]
  simp only [Formalism.HermitianLatticesTheory.majAt, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem pull_coords (Q : HLat K) (hQ : Q.Good) {n : ℕ} (f : (Fin n → K) →ₗ[K] Q.V) (hinj : Function.Injective f)
    (hsurj : Function.Surjective f) :
    ∃ XK : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ v, IsUnit (XK v).det) ∧
      (∀ v z, normAt (Pi.basisFun K (Fin n)) XK v z = normAt Q.b Q.X v (f z)) ∧
      (Q.L.comap (f.restrictScalars (𝓞 K))).FG ∧
      Q.mu = muDef (Pi.basisFun K (Fin n)) XK (Q.L.comap (f.restrictScalars (𝓞 K))) := by
  obtain ⟨hP1, -, hP3, hP4, -⟩ := Formalism.L2.GlobalTheoryTheory.HLatOps.pull_spec K Q (Fin n → K) (Fin n)
    (Pi.basisFun K (Fin n)) f hQ.1 hinj
  obtain ⟨hfg, -, hmu, -, -⟩ := hP4 hQ.2.1
  have hrange : Q.L ⊓ (LinearMap.range f).restrictScalars (𝓞 K) = Q.L := by
    rw [LinearMap.range_eq_top.2 hsurj]
    exact inf_eq_left.2 fun _ _ => trivial
  rw [hrange] at hmu
  exact ⟨_, hP1, hP3, hfg, hmu.symm⟩

theorem bc_mu (hc : CMData F E) (S : HSpace E) (hsig : S.SigOK) (hpos : S.IsPosDef) (hn : 0 < S.rank) [Algebra E K]
    (Q : HLat K) (hQ : Q.Good) (hcard : Fintype.card Q.ι = S.rank) (bc : S.V →+ Q.V)
    (bc_smul : ∀ (a : E) y, bc (a • y) = algebraMap E K a • bc y) (L : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L)
    (bc_L : Q.L = Submodule.span (𝓞 K) (bc '' (L : Set S.V)))
    (bc_norm : ∀ (v : InfinitePlace K) y, (majAt Q.b Q.X v (bc y) (bc y)).re = (v.embedding (algebraMap E K (S.hT y y))).re) :
    Q.mu = muDef (Pi.basisFun E (Fin S.rank)) (fun v => Formalism.L2.Geo.Def.frameOf (S.gram.map v.embedding)) (crdLat S L) := by
  classical
  have hM := crdLat_lattice S L hL
  have hY : ∀ v : InfinitePlace E, IsUnit (Formalism.L2.Geo.Def.frameOf (S.gram.map v.embedding)).det ∧
      ((Formalism.L2.Geo.Def.frameOf (S.gram.map v.embedding))⁻¹).conjTranspose * (Formalism.L2.Geo.Def.frameOf (S.gram.map v.embedding))⁻¹ =
        S.gram.map v.embedding := by
    intro v
    apply frameOf_spec
    apply exists_frame_of_sig _ S.rank
    have h1 := hsig v.embedding
    rwa [hpos v.embedding] at h1

  let f : (Fin S.rank → K) →ₗ[K] Q.V := Fintype.linearCombination K fun a => bc (S.frame a)
  let ιm : (Fin S.rank → E) → (Fin S.rank → K) := fun x i => algebraMap E K (x i)
  have hf : ∀ y : S.V, f (ιm (crd S y)) = bc y := by
    intro y
    show ∑ a, algebraMap E K (crd S y a) • bc (S.frame a) = bc y
    conv_rhs => rw [← S.frame.sum_repr y]
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => (bc_smul _ _).symm
  have hset : bc '' (L : Set S.V) = f '' (ιm '' (crdLat S L : Set (Fin S.rank → E))) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, ⟨_, (crdLat_mem S L y).2 hy, rfl⟩, hf y⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨y, rfl⟩ := (crd S).surjective x
      exact ⟨y, (crdLat_mem S L y).1 hx, (hf y).symm⟩
  have hQL : Q.L = (Submodule.span (𝓞 K) (ιm '' (crdLat S L : Set (Fin S.rank → E)))).map (f.restrictScalars (𝓞 K)) := by
    rw [bc_L, hset, Submodule.map_span]
    rfl
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hQ.2.2, Submodule.span_le]
    intro z hz
    rw [hQL] at hz
    obtain ⟨x, -, rfl⟩ := hz
    exact ⟨x, rfl⟩
  have hfr : finrank K (Fin S.rank → K) = finrank K Q.V := by
    rw [Module.finrank_eq_card_basis Q.b, hcard]; simp
  haveI : FiniteDimensional K Q.V := Module.Finite.of_basis Q.b
  have hinj : Function.Injective f := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).2 hsurj
  obtain ⟨XK, hP1, hP3, hfg0, hmu'⟩ := pull_coords Q hQ f hinj hsurj
  rw [hmu']
  have hcomap : Q.L.comap (f.restrictScalars (𝓞 K)) = Submodule.span (𝓞 K) (ιm '' (crdLat S L : Set (Fin S.rank → E))) := by
    rw [hQL]
    exact Submodule.comap_map_eq_of_injective (f := f.restrictScalars (𝓞 K)) hinj _
  rw [hcomap] at hfg0 ⊢
  have hbc := Formalism.HermiteSiegelSlopes.baseChange E K (Fin S.rank) (fun v => Formalism.L2.Geo.Def.frameOf (S.gram.map v.embedding)) XK
    (fun v => (hY v).1) hP1
    (fun w x => by
      obtain ⟨y, rfl⟩ := (crd S).surjective x
      have h1 : normAt (Pi.basisFun K (Fin S.rank)) XK w (ιm (crd S y)) =
          Real.sqrt ((w.embedding (algebraMap E K (S.hT y y))).re) := by
        rw [hP3, hf y, Formalism.L2.GlobalTheoryTheory.HLatOps.normAt_eq_sqrt, bc_norm]
      have h2 := normE hc S (fun v => Formalism.L2.Geo.Def.frameOf (S.gram.map v.embedding)) (w.comap (algebraMap E K)) (hY _).2 y
      rw [re_comap] at h2
      exact h1.trans h2.symm) (crdLat S L) hM.fg
  have hE : Nontrivial (Fin S.rank → E) := Pi.nontrivial_at ⟨0, hn⟩
  have hrM : rkK (crdLat S L) = S.rank := by
    show finrank E (Submodule.span E ((crdLat S L : Submodule (𝓞 E) (Fin S.rank → E)) : Set (Fin S.rank → E))) = _
    rw [hM.span_eq_top]; simp
  have hneM : crdLat S L ≠ ⊥ := Formalism.L2.Col.isLattice_ne_bot hM
  have hfgT := hfg0
  have hrT : rkK (Submodule.span (𝓞 K) (ιm '' (crdLat S L : Set (Fin S.rank → E)))) = S.rank := hbc.1.trans hrM
  have hneT : Submodule.span (𝓞 K) (ιm '' (crdLat S L : Set (Fin S.rank → E))) ≠ ⊥ := by
    intro h0
    rw [h0] at hrT
    have : rkK (⊥ : Submodule (𝓞 K) (Fin S.rank → K)) = 0 := by
      show finrank K (Submodule.span K ((⊥ : Submodule (𝓞 K) (Fin S.rank → K)) : Set (Fin S.rank → K))) = 0
      simp
    omega
  rw [Formalism.L2.Col.brp_mu_degT _ _ hP1 _ hfgT hneT (by rw [hrT]; exact hn),
    Formalism.L2.Col.brp_mu_degT _ _ (fun v => (hY v).1) _ hM.fg hneM (by rw [hrM]; exact hn), hrM, hrT]
  congr 2
  exact hbc.2

end BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem q_lattice_slope (D : D7) : QSlope D := by
  intro u CV c τ
  have H := columnHypotheses D u
  haveI := H.tcE
  have hn : 0 < (D.sp.X 0).rank := by rw [H.rank]; exact H.npos
  letI : Algebra D.host.E D.what₂.LL := (CV.rho τ).toAlgebra
  have h1 := bc_mu D.sp.cm (D.sp.X 0) (D.sp.X_sig 0) (D.X_posDef 0 (Nat.zero_le _)) hn (CV.Q c τ) (CV.Q_good c τ)
    (by rw [Fintype.card_congr (CV.eQ c τ), Fintype.card_fin, H.rank]) (CV.bc c τ) (CV.bc_smul c τ) (D.clsLat u 0 c) (H.lat c)
    (CV.bc_L c τ) (CV.bc_norm c τ)
  have hT : (Tu D u) ^ (2 * D.R.f) ≠ 0 := pow_ne_zero _ H.Tpos.ne'
  rw [h1, eLat_mu D.sp.cm (D.sp.X 0) (D.sp.X_sig 0) (D.X_posDef 0 (Nat.zero_le _)) hn _ (H.lat c) _ hT (CV.latT c), H.deg, H.rank,
    Ranks.N_zero]
  have hf : (0 : ℝ) < (D.R.f : ℝ) := by
    have : 0 < 2 * D.R.f := by rw [← H.deg]; exact Module.finrank_pos
    exact_mod_cast (by omega : 0 < D.R.f)
  have hk : (0 : ℝ) < (D.R.k : ℝ) := by exact_mod_cast columnCount_pos D
  push_cast
  rw [Real.log_pow]
  push_cast
  field_simp

theorem column_lattice_exact_slope (D : D7) : ColSlopeEq D := colSlopeEq_of_Q D (q_lattice_slope D)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end

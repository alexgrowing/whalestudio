import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.NearPair

section Ring

variable {R : Type} [CommRing R] {M : ℕ}

def rowV (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) : Fin M → R :=
  fun j => ∑ i, c (a i) * Jm i j

theorem row_dot (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) :
    ∑ j, rowV c Jm a j * a j = Formalism.UG.hform c Jm a a := by
  unfold rowV Formalism.UG.hform
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

theorem qr_eq (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) (k : R) :
    qr c Jm a k = 1 + k • Matrix.vecMulVec a (rowV c Jm a) := rfl

theorem qr_mul_qr (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) {k k' : R}
    (h : k + k' + k * k' * Formalism.UG.hform c Jm a a = 0) : qr c Jm a k * qr c Jm a k' = 1 := by
  set N := Matrix.vecMulVec a (rowV c Jm a) with hNdef
  have hN : N * N = Formalism.UG.hform c Jm a a • N := by
    ext i j
    simp only [hNdef, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← row_dot, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [qr_eq, qr_eq, ← hNdef]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hN,
    smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (N i j) * h

theorem cT_qr (c : R →+* R) (hc : ∀ x, c (c x) = x) (Jm : Matrix (Fin M) (Fin M) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) (a : Fin M → R) (k : R) :
    Formalism.UG.cT c (qr c Jm a k) * Jm = Jm * qr c Jm a (c k) := by
  set N := Matrix.vecMulVec a (rowV c Jm a) with hNdef
  have hcv : ∀ i, c (rowV c Jm a i) = ∑ m, Jm i m * a m := by
    intro i
    simp only [rowV, map_sum, map_mul, hc, hJ]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hN : Formalism.UG.cT c N * Jm = Jm * N := by
    ext i j
    simp only [hNdef, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.vecMulVec_apply,
      map_mul]
    have e1 : ∑ m, c (a m) * c (rowV c Jm a i) * Jm m j = c (rowV c Jm a i) * rowV c Jm a j := by
      simp only [rowV, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [e1, hcv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hadd : ∀ A B : Matrix (Fin M) (Fin M) R, Formalism.UG.cT c (A + B) = Formalism.UG.cT c A + Formalism.UG.cT c B := by
    intro A B
    ext i j
    simp [Formalism.UG.cT]
  have hsmul : ∀ (t : R) (A : Matrix (Fin M) (Fin M) R), Formalism.UG.cT c (t • A) = c t • Formalism.UG.cT c A := by
    intro t A
    ext i j
    simp [Formalism.UG.cT]
  rw [qr_eq, qr_eq, ← hNdef, hadd, hsmul, Formalism.UG.cT_one]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hN]

theorem hform_fix (c : R →+* R) (hc : ∀ x, c (c x) = x) (Jm : Matrix (Fin M) (Fin M) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) (a : Fin M → R) :
    c (Formalism.UG.hform c Jm a a) = Formalism.UG.hform c Jm a a := by
  simp only [Formalism.UG.hform, map_sum, map_mul, hc, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem qr_conj (c : R →+* R) (hc : ∀ x, c (c x) = x) (Jm : Matrix (Fin M) (Fin M) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) {a : Fin M → R} {l k : R} (hu : IsUnit (Formalism.UG.hform c Jm a a))
    (hl : l * c l = 1) (hk : k * Formalism.UG.hform c Jm a a = l - 1) :
    qr c Jm a k * qr c Jm a (c k) = 1 ∧ qr c Jm a (c k) * qr c Jm a k = 1 := by
  set u := Formalism.UG.hform c Jm a a with hudef
  have hcu : c u = u := hform_fix c hc Jm hJ a
  have hck : c k * u = c l - 1 := by
    have := congrArg c hk
    rwa [map_mul, hcu, map_sub, map_one] at this
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h : k + c k + k * c k * u = 0 := by
    linear_combination (-(k + c k + k * c k * u)) * hw + w * (1 + c k * u) * hk + w * l * hck + w * hl
  refine ⟨qr_mul_qr c Jm a h, qr_mul_qr c Jm a ?_⟩
  linear_combination h

theorem pair_facts (c : R →+* R) (hc : ∀ x, c (c x) = x) (Jm : Matrix (Fin M) (Fin M) R)
    (hJ : ∀ i j, c (Jm j i) = Jm i j) {a b : Fin M → R} {l ka kb : R} (hua : IsUnit (Formalism.UG.hform c Jm a a))
    (hub : IsUnit (Formalism.UG.hform c Jm b b)) (hl : l * c l = 1) (hka : ka * Formalism.UG.hform c Jm a a = l - 1)
    (hkb : kb * Formalism.UG.hform c Jm b b = c l - 1) :
    (qr c Jm a ka * qr c Jm b kb) * (qr c Jm b (c kb) * qr c Jm a (c ka)) = 1 ∧
    (qr c Jm b (c kb) * qr c Jm a (c ka)) * (qr c Jm a ka * qr c Jm b kb) = 1 ∧
    Formalism.UG.cT c (qr c Jm a ka * qr c Jm b kb) * Jm * (qr c Jm a ka * qr c Jm b kb) = Jm := by
  obtain ⟨a1, a2⟩ := qr_conj c hc Jm hJ hua hl hka
  have hl' : c l * c (c l) = 1 := by rw [hc, mul_comm, hl]
  obtain ⟨b1, b2⟩ := qr_conj c hc Jm hJ hub hl' hkb
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (qr c Jm b kb), b1, Matrix.one_mul, a1]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (qr c Jm a (c ka)), a2, Matrix.one_mul, b2]
  · have ha : Formalism.UG.cT c (qr c Jm a ka) * Jm * qr c Jm a ka = Jm := by
      rw [cT_qr c hc Jm hJ, Matrix.mul_assoc, a2, Matrix.mul_one]
    have hb : Formalism.UG.cT c (qr c Jm b kb) * Jm * qr c Jm b kb = Jm := by
      rw [cT_qr c hc Jm hJ, Matrix.mul_assoc, b2, Matrix.mul_one]
    rw [Formalism.UG.cT_mul]
    calc Formalism.UG.cT c (qr c Jm b kb) * Formalism.UG.cT c (qr c Jm a ka) * Jm * (qr c Jm a ka * qr c Jm b kb)
        = Formalism.UG.cT c (qr c Jm b kb) * (Formalism.UG.cT c (qr c Jm a ka) * Jm * qr c Jm a ka) * qr c Jm b kb := by
          simp only [Matrix.mul_assoc]
      _ = Jm := by rw [ha, hb]

end Ring

theorem exists_inv_near {K R : Type} [NontriviallyNormedField K] [CommRing R] [Algebra K R] [Module.Finite K R]
    [TopologicalSpace R] [IsModuleTopology K R] (u₀ : R) (hu : IsUnit u₀) :
    ∃ g : R → R, ContinuousAt g u₀ ∧ ∀ᶠ u in 𝓝 u₀, u * g u = 1 := by
  classical
  haveI : ContinuousAdd R := IsModuleTopology.toContinuousAdd K R
  let b := Module.finBasis K R
  let L : R →ₐ[K] Matrix _ _ K := Algebra.leftMulMatrix b
  have hL : Continuous fun u => L u := by
    refine continuous_matrix fun i j => ?_
    exact IsModuleTopology.continuous_of_linearMap ((Matrix.entryLinearMap K K i j) ∘ₗ L.toLinearMap)
  have hd0 : (L u₀).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (hu.map L)).ne_zero
  have hdetC : Continuous fun u => (L u).det := hL.matrix_det
  have hadjC : Continuous fun u => (L u).adjugate := hL.matrix_adjugate
  have hinv : ContinuousAt (fun u => (L u)⁻¹) u₀ := by
    have e : (fun u => (L u)⁻¹) = fun u => ((L u).det)⁻¹ • (L u).adjugate := by
      funext u
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [e]
    exact (hdetC.continuousAt.inv₀ hd0).smul hadjC.continuousAt
  have hsymm : Continuous b.equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
  have hmv : ContinuousAt (fun u => Matrix.mulVec (L u)⁻¹ (b.equivFun 1)) u₀ :=
    ContinuousAt.comp (f := fun u => (L u)⁻¹) (g := fun A => Matrix.mulVec A (b.equivFun 1))
      (Continuous.matrix_mulVec continuous_id continuous_const).continuousAt hinv
  refine ⟨fun u => b.equivFun.symm (Matrix.mulVec (L u)⁻¹ (b.equivFun 1)), hsymm.continuousAt.comp hmv, ?_⟩
  have hev : ∀ᶠ u in 𝓝 u₀, (L u).det ≠ 0 := hdetC.continuousAt.eventually_ne hd0
  filter_upwards [hev] with u hdu
  have e : ∀ x y : R, b.equivFun (x * y) = Matrix.mulVec (L x) (b.equivFun y) := by
    intro x y
    simp only [Module.Basis.equivFun_apply, L, Algebra.leftMulMatrix_mulVec_repr]
  apply b.equivFun.injective
  rw [e, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdu), Matrix.one_mulVec]

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_invol' (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (K : Type) [CommRing K] [Algebra F K] (t : K ⊗[F] E) :
    sigR K σ (sigR K σ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [sigR, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem continuous_sigR' (σ : E →ₐ[F] E) (K : Type) [NontriviallyNormedField K] [Algebra F K] :
    Continuous (sigR K σ) := by
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (K ⊗[F] E) := IsModuleTopology.toContinuousAdd K _
  have hfix : ∀ t : K, sigR K σ (algebraMap K (K ⊗[F] E) t) = algebraMap K (K ⊗[F] E) t := by
    intro t
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  let cl : K ⊗[F] E →ₗ[K] K ⊗[F] E :=
    { toFun := sigR K σ
      map_add' := map_add _
      map_smul' := fun t x => by
        rw [Algebra.smul_def, map_mul, hfix, RingHom.id_apply, Algebra.smul_def] }
  exact IsModuleTopology.continuous_of_linearMap cl

end Top

section Cont

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {M : ℕ}

theorem continuous_hform (c : R →+* R) (hc : Continuous c) (Jm : Matrix (Fin M) (Fin M) R) :
    Continuous fun a : Fin M → R => Formalism.UG.hform c Jm a a := by
  unfold Formalism.UG.hform
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact ((hc.comp (continuous_apply i)).mul continuous_const).mul (continuous_apply j)

theorem continuous_qr (c : R →+* R) (hc : Continuous c) (Jm : Matrix (Fin M) (Fin M) R) :
    Continuous fun q : (Fin M → R) × R => qr c Jm q.1 q.2 := by
  refine continuous_matrix fun i j => ?_
  simp only [qr, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  refine continuous_const.add (continuous_snd.mul (((continuous_apply i).comp continuous_fst).mul ?_))
  refine continuous_finset_sum _ fun m _ => ?_
  exact (hc.comp ((continuous_apply m).comp continuous_fst)).mul continuous_const

theorem contAt_pair (c : R →+* R) (hc : Continuous c) (Jm : Matrix (Fin M) (Fin M) R) {P : Type} [TopologicalSpace P]
    (p₀ : P) (f g : P → Fin M → R) (s t : P → R) (hf : ContinuousAt f p₀) (hg : ContinuousAt g p₀)
    (hs : ContinuousAt s p₀) (ht : ContinuousAt t p₀) :
    ContinuousAt (fun p => qr c Jm (f p) (s p) * qr c Jm (g p) (t p)) p₀ := by
  have hq := continuous_qr c hc Jm
  have h : Continuous fun q : ((Fin M → R) × R) × ((Fin M → R) × R) => qr c Jm q.1.1 q.1.2 * qr c Jm q.2.1 q.2.2 :=
    (hq.comp continuous_fst).matrix_mul (hq.comp continuous_snd)
  exact ContinuousAt.comp (f := fun p => ((f p, s p), (g p, t p)))
    (g := fun q : ((Fin M → R) × R) × ((Fin M → R) × R) => qr c Jm q.1.1 q.1.2 * qr c Jm q.2.1 q.2.2)
    h.continuousAt ((hf.prodMk hs).prodMk (hg.prodMk ht))

end Cont

section Core

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {M : ℕ}

theorem near_unit {P : Type} [TopologicalSpace P] (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R)
    (x : Formalism.UG.UJ c Jm) (V : Set (Formalism.UG.UJ c Jm)) (hV : V ∈ 𝓝 x) (X Y : P → Matrix (Fin M) (Fin M) R) (p₀ : P)
    (hXC : ContinuousAt X p₀) (hYC : ContinuousAt Y p₀)
    (hX0 : X p₀ = ((x.1 : GL (Fin M) R) : Matrix (Fin M) (Fin M) R)) (hXY0 : X p₀ * Y p₀ = 1)
    (hfac : ∀ᶠ p in 𝓝 p₀, X p * Y p = 1 ∧ Y p * X p = 1 ∧ Formalism.UG.cT c (X p) * Jm * X p = Jm) :
    ∀ᶠ p in 𝓝 p₀, ∃ x' ∈ V, ((x'.1 : GL (Fin M) R) : Matrix (Fin M) (Fin M) R) = X p := by
  have hY0 : Y p₀ = (((x.1)⁻¹ : GL (Fin M) R) : Matrix (Fin M) (Fin M) R) := by
    symm
    apply Units.inv_eq_of_mul_eq_one_right
    rw [← hX0, hXY0]
  let emb : Formalism.UG.UJ c Jm → Matrix (Fin M) (Fin M) R × (Matrix (Fin M) (Fin M) R)ᵐᵒᵖ :=
    fun y => Units.embedProduct _ y.1
  have hemb : Topology.IsInducing emb :=
    (Units.isEmbedding_embedProduct (M := Matrix (Fin M) (Fin M) R)).isInducing.comp
      Topology.IsInducing.subtypeVal
  have hV' : V ∈ Filter.comap emb (𝓝 (emb x)) := by
    rw [← hemb.nhds_eq_comap]
    exact hV
  obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.1 hV'
  have hΦ : ContinuousAt (fun p => (X p, MulOpposite.op (Y p))) p₀ :=
    hXC.prodMk (MulOpposite.continuous_op.continuousAt.comp hYC)
  have hΦ0 : (X p₀, MulOpposite.op (Y p₀)) = emb x := by
    rw [hX0, hY0]
    rfl
  have E3 : ∀ᶠ p in 𝓝 p₀, (X p, MulOpposite.op (Y p)) ∈ W :=
    hΦ.eventually (show ∀ᶠ y in 𝓝 (X p₀, MulOpposite.op (Y p₀)), y ∈ W by rw [hΦ0]; exact hW)
  filter_upwards [E3, hfac] with p h3 ⟨f1, f2, f3⟩
  exact ⟨⟨⟨X p, Y p, f1, f2⟩, f3⟩, hWV h3, rfl⟩

theorem near_core (c : R →+* R) (hc : ∀ x, c (c x) = x) (hcC : Continuous c) (Jm : Matrix (Fin M) (Fin M) R)
    (hJR : ∀ i j, c (Jm j i) = Jm i j)
    (hinv : ∀ u₀ : R, IsUnit u₀ → ∃ g : R → R, ContinuousAt g u₀ ∧ ∀ᶠ u in 𝓝 u₀, u * g u = 1)
    (a₀ b₀ : Fin M → R) (x : Formalism.UG.UJ c Jm)
    (hx : IsQPairOf c Jm a₀ b₀ ((x.1 : GL (Fin M) R) : Matrix (Fin M) (Fin M) R))
    (V : Set (Formalism.UG.UJ c Jm)) (hV : V ∈ 𝓝 x) :
    ∀ᶠ p in 𝓝 (a₀, b₀), ∃ x' ∈ V,
      IsQPairOf c Jm p.1 p.2 ((x'.1 : GL (Fin M) R) : Matrix (Fin M) (Fin M) R) := by
  obtain ⟨l, ka, kb, hua, hub, hl, hka, hkb, hX⟩ := hx
  have hhC := continuous_hform c hcC Jm
  obtain ⟨ga, hgaC, hga⟩ := hinv _ hua
  obtain ⟨gb, hgbC, hgb⟩ := hinv _ hub
  let hh : (Fin M → R) → R := fun a => Formalism.UG.hform c Jm a a
  let p₀ : (Fin M → R) × (Fin M → R) := (a₀, b₀)
  let A : (Fin M → R) × (Fin M → R) → R := fun p => (l - 1) * ga (hh p.1)
  let B : (Fin M → R) × (Fin M → R) → R := fun p => (c l - 1) * gb (hh p.2)
  have hAC : ContinuousAt A p₀ := continuousAt_const.mul
    (ContinuousAt.comp (f := fun p : (Fin M → R) × (Fin M → R) => hh p.1) (g := ga) hgaC
      (hhC.comp continuous_fst).continuousAt)
  have hBC : ContinuousAt B p₀ := continuousAt_const.mul
    (ContinuousAt.comp (f := fun p : (Fin M → R) × (Fin M → R) => hh p.2) (g := gb) hgbC
      (hhC.comp continuous_snd).continuousAt)
  have E1 : ∀ᶠ p in 𝓝 p₀, hh p.1 * ga (hh p.1) = 1 :=
    ((hhC.comp continuous_fst).continuousAt (x := p₀)).eventually hga
  have E2 : ∀ᶠ p in 𝓝 p₀, hh p.2 * gb (hh p.2) = 1 :=
    ((hhC.comp continuous_snd).continuousAt (x := p₀)).eventually hgb
  have hA0 : A p₀ = ka := by
    have h1 : hh a₀ * ga (hh a₀) = 1 := E1.self_of_nhds
    have h2 : ka * hh a₀ = l - 1 := hka
    change (l - 1) * ga (hh a₀) = ka
    rw [← h2]
    linear_combination ka * h1
  have hB0 : B p₀ = kb := by
    have h1 : hh b₀ * gb (hh b₀) = 1 := E2.self_of_nhds
    have h2 : kb * hh b₀ = c l - 1 := hkb
    change (c l - 1) * gb (hh b₀) = kb
    rw [← h2]
    linear_combination kb * h1
  let X : (Fin M → R) × (Fin M → R) → Matrix (Fin M) (Fin M) R :=
    fun p => qr c Jm p.1 (A p) * qr c Jm p.2 (B p)
  let Y : (Fin M → R) × (Fin M → R) → Matrix (Fin M) (Fin M) R :=
    fun p => qr c Jm p.2 (c (B p)) * qr c Jm p.1 (c (A p))
  have hXC : ContinuousAt X p₀ :=
    contAt_pair c hcC Jm p₀ Prod.fst Prod.snd A B continuousAt_fst continuousAt_snd hAC hBC
  have hYC : ContinuousAt Y p₀ :=
    contAt_pair c hcC Jm p₀ Prod.snd Prod.fst (fun p => c (B p)) (fun p => c (A p)) continuousAt_snd continuousAt_fst
      (hcC.continuousAt.comp hBC) (hcC.continuousAt.comp hAC)
  have hu : ((x.1 : GL (Fin M) R) : Matrix (Fin M) (Fin M) R) = qr c Jm a₀ ka * qr c Jm b₀ kb := hX
  have hX0 : X p₀ = ((x.1 : GL (Fin M) R) : Matrix (Fin M) (Fin M) R) := by
    rw [hu]
    change qr c Jm a₀ (A p₀) * qr c Jm b₀ (B p₀) = _
    rw [hA0, hB0]
  have hXY0 : X p₀ * Y p₀ = 1 := by
    change (qr c Jm a₀ (A p₀) * qr c Jm b₀ (B p₀)) * (qr c Jm b₀ (c (B p₀)) * qr c Jm a₀ (c (A p₀))) = 1
    rw [hA0, hB0]
    exact (pair_facts c hc Jm hJR hua hub hl hka hkb).1
  have key : ∀ᶠ p in 𝓝 p₀, IsUnit (Formalism.UG.hform c Jm p.1 p.1) ∧ IsUnit (Formalism.UG.hform c Jm p.2 p.2) ∧
      A p * Formalism.UG.hform c Jm p.1 p.1 = l - 1 ∧ B p * Formalism.UG.hform c Jm p.2 p.2 = c l - 1 := by
    filter_upwards [E1, E2] with p h1 h2
    refine ⟨isUnit_iff_exists_inv.2 ⟨_, h1⟩, isUnit_iff_exists_inv.2 ⟨_, h2⟩, ?_, ?_⟩
    · change (l - 1) * ga (hh p.1) * hh p.1 = l - 1
      linear_combination (l - 1) * h1
    · change (c l - 1) * gb (hh p.2) * hh p.2 = c l - 1
      linear_combination (c l - 1) * h2
  have hfac : ∀ᶠ p in 𝓝 p₀, X p * Y p = 1 ∧ Y p * X p = 1 ∧ Formalism.UG.cT c (X p) * Jm * X p = Jm := by
    filter_upwards [key] with p ⟨h1, h2, h3, h4⟩
    exact pair_facts c hc Jm hJR h1 h2 hl h3 h4
  filter_upwards [near_unit c Jm x V hV X Y p₀ hXC hYC hX0 hXY0 hfac, key] with p ⟨x', hx'V, hx'⟩ ⟨h1, h2, h3, h4⟩
  exact ⟨x', hx'V, l, A p, B p, h1, h2, hl, h3, h4, hx'⟩

end Core

theorem near_pair_main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (a₀ b₀ : Fin M → K ⊗[F] E) (x : HA K σ J), IsQPairOf (sigR K σ) (JR K J) a₀ b₀ ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) → ∀ V ∈ nhds x, ∀ᶠ p in nhds (a₀, b₀), ∃ x' ∈ V, IsQPairOf (sigR K σ) (JR K J) p.1 p.2 ((HA.mat K σ J x').1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ K _ _ a₀ b₀ x hx V hV
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (K ⊗[F] E) := IsModuleTopology.isTopologicalRing K _
  have hσ : ∀ x, σ (σ x) = x := by
    intro y
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  exact near_core (sigR K σ) (sigR_invol' σ hσ K) (continuous_sigR' σ K) (JR (F := F) K J)
    (fun i j => map_mem_HermR K σ J hJ.1 i j) (fun u₀ hu => exists_inv_near (K := K) u₀ hu) a₀ b₀ x hx V hV

end GlobalTheory.CompanionTheory.SaGen.NearPair

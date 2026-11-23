import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxCutE
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.DIV.CyclotomicLifting

namespace EigenprojectionMatrices

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v0 : InfinitePlace K} {s : ℕ}

theorem eig_rat (h : BlockHyp B ℓ v0 s) (hH : B.OkH) (C : (B.Pl × ℕ → K) → Prop) :
    SubHasRatBasis (B.inV0 ℓ (Col.eigSum B.op C)) := by
  classical
  have hg := good_at_spec K v0 h.conj G ℓ.X h.irr ℓ.P ℓ.ψ
  have hεrat : ∀ i j, B.vProj ℓ i j ∈ cmMax K := gaMat_rat B.S B.r h.ok.actRat _ hg.rat
  have hεadj : (B.vProj ℓ)ᴴ * B.S.H = B.S.H * B.vProj ℓ := by
    have := group_action_matrix_adjoint K B.S G B.r h.ok.act (goodAt ℓ.X ℓ.P ℓ.ψ)
    rwa [hg.selfAdj] at this
  let 𝒯 : Set (Matrix (Fin B.S.dim) (Fin B.S.dim) K) := B.heckeSet ∪ {B.vProj ℓ}
  let Z : Submodule K (Fin B.S.dim → K) := B.coord (Col.eigSum B.op C) ⊓ LinearMap.range (B.vProj ℓ).mulVecLin
  have hTrat : ∀ T ∈ 𝒯, ∀ i j, T i j ∈ cmMax K := by
    rintro T (⟨i, rfl⟩ | rfl)
    · exact hH.rat i
    · exact hεrat
  have hTcomm : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T * T' = T' * T := by
    rintro T (⟨i, rfl⟩ | rfl) T' (⟨j, rfl⟩ | rfl)
    · exact opMat_comm h.ok.comm i j
    · exact opMat_gaMat h.ok.opG i _
    · exact (opMat_gaMat h.ok.opG j _).symm
    · rfl
  have hTadj : IsAdjStable B.S.H 𝒯 := by
    rintro T (⟨i, rfl⟩ | rfl)
    · obtain ⟨i', hi'⟩ := hH.adj i
      refine ⟨B.opMat i', Or.inl ⟨i', rfl⟩, fun x y => ?_⟩
      rw [hform_eq_csum, hform_eq_csum, I_opMat, I_opMat, CSD.I_apply, CSD.I_apply]
      exact hi' _ _
    · exact ⟨B.vProj ℓ, Or.inr rfl, hform_adj hεadj⟩
  have hZ : IsCommStable 𝒯 Z := by
    intro M hM z hz
    obtain ⟨hz1, hz2⟩ := hz
    refine ⟨?_, ?_⟩
    · obtain ⟨f, hf, rfl⟩ := hz1
      let g : Module.End K B.S.Forms := Matrix.toLin B.S.basis B.S.basis M
      have hgc : ∀ i, Commute (B.op i) g := by
        intro i
        have e : B.op i = Matrix.toLin B.S.basis B.S.basis (B.opMat i) :=
          (Matrix.toLin_toMatrix B.S.basis B.S.basis (B.op i)).symm
        show B.op i * g = g * B.op i
        rw [e, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin_mul, ← Matrix.toLin_mul,
          hM (B.opMat i) (Or.inl ⟨i, rfl⟩)]
      have hgf : g f ∈ Col.eigSum B.op C := Col.eigSum_le_comap hgc _ hf
      refine ⟨g f, hgf, ?_⟩
      have h1 := LinearMap.toMatrix_mulVec_repr B.S.basis B.S.basis g f
      rw [LinearMap.toMatrix_toLin] at h1
      funext a
      have := congrFun h1 a
      simpa [Basis.equivFun_apply] using this.symm
    · obtain ⟨y, rfl⟩ := hz2
      refine ⟨M.mulVec y, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        hM (B.vProj ℓ) (Or.inr rfl)]
  have htw := commuting_twist K (cmMax K) ConjugateWeightGram.isCMSub_cmMax v0 h.conj B.S.dim B.S.H h.ok.hrat h.ok.hpos
    𝒯 hTrat hTcomm hTadj Z hZ
  obtain ⟨d, z, -, hspan, hzrat⟩ := descent_cm_field K B.S.dim Z htw
  obtain ⟨hinj, hrange⟩ := image_idempotent_spec K B.S.dim (B.vProj ℓ)
  have hinj' : Function.Injective (B.vE ℓ).mulVec := hinj
  have hrange' : LinearMap.range (B.vE ℓ).mulVecLin = LinearMap.range (B.vProj ℓ).mulVecLin := hrange
  have hzr : ∀ a, ∃ x, (B.vE ℓ).mulVecLin x = z a := by
    intro a
    have hza : z a ∈ Z := by rw [← hspan]; exact Submodule.subset_span ⟨a, rfl⟩
    have := hza.2
    rw [← hrange'] at this
    exact this
  choose x hx using hzr
  refine subHasRat_of_span (B.inV0 ℓ (Col.eigSum B.op C)) (Set.range x) ?_ ?_
  · apply Submodule.map_injective_of_injective (f := (B.vE ℓ).mulVecLin) hinj'
    rw [Submodule.map_span, ← Set.range_comp]
    have e : (B.vE ℓ).mulVecLin ∘ x = z := funext hx
    rw [e, hspan]
    show Z = Submodule.map (B.vE ℓ).mulVecLin ((B.coord (Col.eigSum B.op C)).comap (B.vE ℓ).mulVecLin)
    rw [Submodule.map_comap_eq, hrange', inf_comm]
  · rintro _ ⟨a, rfl⟩ i
    refine rat_of_mulVec (B.vE ℓ) hinj' (hv_spec h).1 (x a) (fun i => ?_) i
    have := hx a
    rw [Matrix.mulVecLin_apply] at this
    rw [this]
    exact hzrat a i

end EigenprojectionMatrices

namespace EigenprojectionMatrices

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v0 : InfinitePlace K} {s : ℕ}

section Proj

variable (hc : Col.PairComm B.op) (hs : Col.SplitOver B.op) (C : (B.Pl × ℕ → K) → Prop)

def pMat : Matrix (Fin B.S.dim) (Fin B.S.dim) K :=
  LinearMap.toMatrix B.S.basis B.S.basis (Col.eigProj hc hs C)

private theorem hform_eq_lemma {L : Type} [Field L] [StarRing L] {n : ℕ} (H : Matrix (Fin n) (Fin n) L)
    (x y : Fin n → L) : hform H x y = star x ⬝ᵥ H *ᵥ y := by
  simp only [hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Pi.star_apply, starRingEnd_apply,
    RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Proj

end EigenprojectionMatrices

namespace EigenprojectionMatrices

section Cx

variable {n d : ℕ} {I : Type}

def linF (N : I → Matrix (Fin n) (Fin n) ℂ) : I → Module.End ℂ (Fin n → ℂ) := fun i => Matrix.toLin' (N i)

theorem linF_commute {M M' : Matrix (Fin n) (Fin n) ℂ} (h : M * M' = M' * M) :
    Commute (Matrix.toLin' M) (Matrix.toLin' M') := by
  have h2 := congrArg Matrix.toLin' h
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul] at h2
  exact h2

variable (N : I → Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)

private theorem dotProduct_mulVec_eigAt_eq_zero_of_ne (hA : A.PosDef) (adj : ∀ i, ∃ i', A * N i = (N i')ᴴ * A)
    (hc : Col.PairComm (linF N)) {a b : I → ℂ} (hab : a ≠ b) {x y : Fin n → ℂ}
    (hx : x ∈ Col.eigAt (linF N) a) (hy : y ∈ Col.eigAt (linF N) b) : star x ⬝ᵥ A *ᵥ y = 0 := by
  obtain ⟨i, hne⟩ := Function.ne_iff.mp hab
  obtain ⟨i', hi⟩ := adj i
  have hAh : Aᴴ = A := hA.1
  have hi2 : A * N i' = (N i)ᴴ * A := by
    have e := congrArg Matrix.conjTranspose hi
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hAh] at e
    exact e.symm
  have hpos : ∀ z : Fin n → ℂ, star z ⬝ᵥ A *ᵥ z = 0 → z = 0 := by
    intro z h0
    by_contra hz
    have h1 := hA.dotProduct_mulVec_pos hz
    rw [h0] at h1
    exact lt_irrefl _ h1
  have hF : ∀ u v : Fin n → ℂ, star u ⬝ᵥ A *ᵥ (N i *ᵥ v) = star (N i' *ᵥ u) ⬝ᵥ A *ᵥ v := by
    intro u v
    conv_lhs => rw [Matrix.mulVec_mulVec, hi, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    rw [Matrix.star_mulVec]
  have hF2 : ∀ u v : Fin n → ℂ, star u ⬝ᵥ A *ᵥ (N i' *ᵥ v) = star (N i *ᵥ u) ⬝ᵥ A *ᵥ v := by
    intro u v
    conv_lhs => rw [Matrix.mulVec_mulVec, hi2, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    rw [Matrix.star_mulVec]
  have ipR : ∀ (l : ℂ) (u v : Fin n → ℂ), star u ⬝ᵥ A *ᵥ ((Matrix.toLin' (N i) - l • 1) v) =
      star ((Matrix.toLin' (N i') - star l • 1) u) ⬝ᵥ A *ᵥ v := by
    intro l u v
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Matrix.toLin'_apply,
      Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul, star_sub, star_smul, star_star,
      sub_dotProduct, smul_dotProduct, hF]
  have ipR2 : ∀ (l : ℂ) (u v : Fin n → ℂ), star u ⬝ᵥ A *ᵥ ((Matrix.toLin' (N i') - l • 1) v) =
      star ((Matrix.toLin' (N i) - star l • 1) u) ⬝ᵥ A *ᵥ v := by
    intro l u v
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Matrix.toLin'_apply,
      Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul, star_sub, star_smul, star_star,
      sub_dotProduct, smul_dotProduct, hF2]
  have hTS : ∀ (c d : ℂ), Commute (Matrix.toLin' (N i) - c • 1) (Matrix.toLin' (N i') - d • 1) := by
    intro c d
    have hc' := hc i i'
    simp only [linF] at hc'
    exact (hc'.sub_right ((Commute.one_right _).smul_right d)).sub_left ((Commute.one_left _).smul_left c)
  have K1 : ∀ (l : ℂ) (z : Fin n → ℂ), (Matrix.toLin' (N i) - l • 1) z = 0 →
      (Matrix.toLin' (N i') - star l • 1) z = 0 := by
    intro l z hz
    apply hpos
    have hcm : (Matrix.toLin' (N i) - l • 1) ((Matrix.toLin' (N i') - star l • 1) z) =
        (Matrix.toLin' (N i') - star l • 1) ((Matrix.toLin' (N i) - l • 1) z) := by
      rw [← Module.End.mul_apply, (hTS l (star l)).eq, Module.End.mul_apply]
    rw [ipR2 (star l), star_star, hcm, hz, map_zero, star_zero, zero_dotProduct]
  have K2 : ∀ (l : ℂ) (z : Fin n → ℂ), (Matrix.toLin' (N i) - l • 1) ((Matrix.toLin' (N i) - l • 1) z) = 0 →
      (Matrix.toLin' (N i) - l • 1) z = 0 := by
    intro l z hz
    apply hpos
    rw [ipR l, K1 l _ hz, star_zero, zero_dotProduct]
  have K3 : ∀ (l : ℂ) (k : ℕ) (z : Fin n → ℂ), ((Matrix.toLin' (N i) - l • 1) ^ k) z = 0 →
      (Matrix.toLin' (N i) - l • 1) z = 0 := by
    intro l k
    induction k with
    | zero => intro z hz; rw [pow_zero, Module.End.one_apply] at hz; rw [hz, map_zero]
    | succ k ih => intro z hz; rw [pow_succ, Module.End.mul_apply] at hz; exact K2 l z (ih _ hz)
  simp only [Col.eigAt, Submodule.mem_iInf, linF] at hx hy
  obtain ⟨kx, hkx⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp (hx i)
  obtain ⟨ky, hky⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp (hy i)
  have hRa := K3 (a i) kx x hkx
  have hRb := K3 (b i) ky y hky
  have hRa' := K1 (a i) x hRa
  have e1 : star ((Matrix.toLin' (N i') - star (b i) • 1) x) ⬝ᵥ A *ᵥ y = 0 := by
    rw [← ipR (b i) x y, hRb, Matrix.mulVec_zero, dotProduct_zero]
  have e2 : (Matrix.toLin' (N i') - star (b i) • 1) x = (star (a i) - star (b i)) • x := by
    have e3 : (Matrix.toLin' (N i') - star (b i) • 1) x =
        (Matrix.toLin' (N i') - star (a i) • 1) x + (star (a i) - star (b i)) • x := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_smul]
      abel
    rw [e3, hRa', zero_add]
  rw [e2, star_smul, smul_dotProduct, smul_eq_mul, mul_eq_zero] at e1
  rcases e1 with h | h
  · exfalso
    apply hne
    simpa only [star_sub, star_star, sub_eq_zero] using h
  · exact h

private theorem dotProduct_mulVec_eigSum_eq_zero_of_disjoint (hA : A.PosDef) (adj : ∀ i, ∃ i', A * N i = (N i')ᴴ * A)
    (hc : Col.PairComm (linF N)) {C1 C2 : (I → ℂ) → Prop} (h12 : ∀ y, C2 y → ¬ C1 y) {x y : Fin n → ℂ}
    (hx : x ∈ Col.eigSum (linF N) C1) (hy : y ∈ Col.eigSum (linF N) C2) : star x ⬝ᵥ A *ᵥ y = 0 := by
  have stepA : ∀ a, C1 a → ∀ x' ∈ Col.eigAt (linF N) a, hform A x' y = 0 := by
    intro a ha x' hx'
    have hle : Col.eigSum (linF N) C2 ≤ LinearMap.ker (hform A x') := by
      unfold Col.eigSum
      refine iSup₂_le fun b hb => ?_
      intro y' hy'
      rw [LinearMap.mem_ker, hform_eq_lemma]
      exact dotProduct_mulVec_eigAt_eq_zero_of_ne N A hA adj hc (a := a) (b := b) (fun hab => h12 b hb (hab ▸ ha)) hx' hy'
    have h := hle hy
    rwa [LinearMap.mem_ker] at h
  have hle : Col.eigSum (linF N) C1 ≤ LinearMap.ker ((hform A).flip y) := by
    unfold Col.eigSum
    refine iSup₂_le fun a ha => ?_
    intro x' hx'
    rw [LinearMap.mem_ker, LinearMap.flip_apply]
    exact stepA a ha x' hx'
  have h := hle hx
  rw [LinearMap.mem_ker, LinearMap.flip_apply, hform_eq_lemma] at h
  exact h

theorem cx_proj_adj (hA : A.PosDef) (adj : ∀ i, ∃ i', A * N i = (N i')ᴴ * A)
    (hc : Col.PairComm (linF N)) (hs : Col.SplitOver (linF N)) (C : (I → ℂ) → Prop) :
    (LinearMap.toMatrix' (Col.eigProj hc hs C))ᴴ * A = A * LinearMap.toMatrix' (Col.eigProj hc hs C) := by
  have hsym : ∀ u v : Fin n → ℂ, star (LinearMap.toMatrix' (Col.eigProj hc hs C) *ᵥ u) ⬝ᵥ A *ᵥ v =
      star u ⬝ᵥ A *ᵥ (LinearMap.toMatrix' (Col.eigProj hc hs C) *ᵥ v) := by
    intro u v
    simp only [LinearMap.toMatrix'_mulVec]
    have o1 : star (Col.eigProj hc hs C u) ⬝ᵥ A *ᵥ (v - Col.eigProj hc hs C v) = 0 :=
      dotProduct_mulVec_eigSum_eq_zero_of_disjoint N A hA adj hc (C1 := C) (C2 := fun x => ¬ C x) (fun y hy => hy)
        (Col.eigProj_apply_mem hc hs C u) (Col.sub_eigProj_mem hc hs C v)
    have o2 : star (u - Col.eigProj hc hs C u) ⬝ᵥ A *ᵥ (Col.eigProj hc hs C v) = 0 :=
      dotProduct_mulVec_eigSum_eq_zero_of_disjoint N A hA adj hc (C1 := fun x => ¬ C x) (C2 := C) (fun y hy hn => hn hy)
        (Col.sub_eigProj_mem hc hs C u) (Col.eigProj_apply_mem hc hs C v)
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_eq_zero] at o1
    rw [star_sub, sub_dotProduct, sub_eq_zero] at o2
    exact o1.trans o2.symm
  have key : ∀ u v : Fin n → ℂ, star u ⬝ᵥ ((LinearMap.toMatrix' (Col.eigProj hc hs C))ᴴ * A) *ᵥ v =
      star u ⬝ᵥ (A * LinearMap.toMatrix' (Col.eigProj hc hs C)) *ᵥ v := by
    intro u v
    conv_lhs => rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    rw [← Matrix.mulVec_mulVec]
    exact hsym u v
  have hz : ∀ v : Fin n → ℂ, ((LinearMap.toMatrix' (Col.eigProj hc hs C))ᴴ * A) *ᵥ v =
      (A * LinearMap.toMatrix' (Col.eigProj hc hs C)) *ᵥ v := by
    intro v
    have h0 := key (((LinearMap.toMatrix' (Col.eigProj hc hs C))ᴴ * A) *ᵥ v -
      (A * LinearMap.toMatrix' (Col.eigProj hc hs C)) *ᵥ v) v
    rw [← sub_eq_zero, ← dotProduct_sub] at h0
    exact sub_eq_zero.mp (dotProduct_star_self_eq_zero.mp h0)
  exact Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact hz v)

theorem cx_eig_orth (hA : A.PosDef) (adj : ∀ i, ∃ i', A * N i = (N i')ᴴ * A)
    (hc : Col.PairComm (linF N)) (hs : Col.SplitOver (linF N)) {C C' : (I → ℂ) → Prop} (hCC : ∀ y, C' y → ¬ C y)
    {f g : Fin n → ℂ} (hf : f ∈ Col.eigSum (linF N) C) (hg : g ∈ Col.eigSum (linF N) C') :
    star f ⬝ᵥ A *ᵥ g = 0 := by
  have hadj := cx_proj_adj N A hA adj hc hs C
  have hf2 : LinearMap.toMatrix' (Col.eigProj hc hs C) *ᵥ f = f := by
    rw [LinearMap.toMatrix'_mulVec]; exact Col.eigProj_apply_of_mem hc hs hf
  have hg2 : LinearMap.toMatrix' (Col.eigProj hc hs C) *ᵥ g = 0 := by
    rw [LinearMap.toMatrix'_mulVec]
    exact Col.eigProj_apply_of_mem_not hc hs (Col.eigSum_mono (fun y hy => hCC y hy) hg)
  rw [← hf2, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hadj,
    ← Matrix.mulVec_mulVec, hg2]
  simp

end Cx

end EigenprojectionMatrices

namespace EigenprojectionMatrices

section CxQ

variable {n d : ℕ} {I : Type} (N : I → Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)

theorem cx_quot_orth (hA : A.PosDef) (adj : ∀ i, ∃ i', A * N i = (N i')ᴴ * A) (P : Matrix (Fin d) (Fin n) ℂ)
    (M : I → Matrix (Fin d) (Fin d) ℂ) (hPN : ∀ i, P * N i = M i * P) (hR : IsUnit (P * A⁻¹ * Pᴴ).det)
    (hc : Col.PairComm (linF N)) (hs : Col.SplitOver (linF N)) {C C' : (I → ℂ) → Prop} (hCC : ∀ y, C' y → ¬ C y)
    {u u' : Fin n → ℂ} (hu : u ∈ Col.eigSum (linF N) C) (hu' : u' ∈ Col.eigSum (linF N) C') :
    star (P *ᵥ u) ⬝ᵥ (P * A⁻¹ * Pᴴ)⁻¹ *ᵥ (P *ᵥ u') = 0 := by
  have hdA : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdA
  have hAA' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hdA
  generalize hRdef : P * A⁻¹ * Pᴴ = R at hR ⊢
  have hRR : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have hRR' : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hR
  have hQ : ∀ i, (A⁻¹ * Pᴴ * R⁻¹ * P) * N i = N i * (A⁻¹ * Pᴴ * R⁻¹ * P) := by
    intro i
    obtain ⟨i', hi⟩ := adj i
    have hNA : N i * A⁻¹ = A⁻¹ * (N i')ᴴ := by
      calc N i * A⁻¹ = A⁻¹ * (A * N i) * A⁻¹ := by rw [← Matrix.mul_assoc, hAA', Matrix.one_mul]
        _ = A⁻¹ * ((N i')ᴴ * A) * A⁻¹ := by rw [hi]
        _ = A⁻¹ * (N i')ᴴ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hAA, Matrix.mul_one]
    have e1 : Pᴴ * (M i')ᴴ = (N i')ᴴ * Pᴴ := by
      rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, hPN]
    have hMR : M i * R = R * (M i')ᴴ := by
      rw [← hRdef]
      calc M i * (P * A⁻¹ * Pᴴ) = M i * P * A⁻¹ * Pᴴ := by simp only [Matrix.mul_assoc]
        _ = P * N i * A⁻¹ * Pᴴ := by rw [← hPN i]
        _ = P * (N i * A⁻¹) * Pᴴ := by simp only [Matrix.mul_assoc]
        _ = P * (A⁻¹ * (N i')ᴴ) * Pᴴ := by rw [hNA]
        _ = P * A⁻¹ * ((N i')ᴴ * Pᴴ) := by simp only [Matrix.mul_assoc]
        _ = P * A⁻¹ * (Pᴴ * (M i')ᴴ) := by rw [e1]
        _ = P * A⁻¹ * Pᴴ * (M i')ᴴ := by simp only [Matrix.mul_assoc]
    have hRM : R⁻¹ * M i = (M i')ᴴ * R⁻¹ := by
      calc R⁻¹ * M i = R⁻¹ * (M i * R) * R⁻¹ := by
            rw [Matrix.mul_assoc R⁻¹, Matrix.mul_assoc (M i), hRR, Matrix.mul_one]
        _ = R⁻¹ * (R * (M i')ᴴ) * R⁻¹ := by rw [hMR]
        _ = (M i')ᴴ * R⁻¹ := by rw [← Matrix.mul_assoc R⁻¹ R, hRR', Matrix.one_mul]
    calc (A⁻¹ * Pᴴ * R⁻¹ * P) * N i = A⁻¹ * Pᴴ * R⁻¹ * (P * N i) := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * Pᴴ * R⁻¹ * (M i * P) := by rw [hPN]
      _ = A⁻¹ * Pᴴ * (R⁻¹ * M i) * P := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * Pᴴ * ((M i')ᴴ * R⁻¹) * P := by rw [hRM]
      _ = A⁻¹ * (Pᴴ * (M i')ᴴ) * R⁻¹ * P := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * ((N i')ᴴ * Pᴴ) * R⁻¹ * P := by rw [e1]
      _ = N i * A⁻¹ * Pᴴ * R⁻¹ * P := by rw [hNA]; simp only [Matrix.mul_assoc]
      _ = N i * (A⁻¹ * Pᴴ * R⁻¹ * P) := by simp only [Matrix.mul_assoc]
  have hcomm : ∀ i, Commute (linF N i) (Matrix.toLin' (A⁻¹ * Pᴴ * R⁻¹ * P)) :=
    fun i => linF_commute (hQ i).symm
  have hQu : (A⁻¹ * Pᴴ * R⁻¹ * P) *ᵥ u' ∈ Col.eigSum (linF N) C' := Col.eigSum_le_comap hcomm C' hu'
  have key : star (P *ᵥ u) ⬝ᵥ R⁻¹ *ᵥ (P *ᵥ u') = star u ⬝ᵥ A *ᵥ ((A⁻¹ * Pᴴ * R⁻¹ * P) *ᵥ u') := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
    simp only [Matrix.mulVec_mulVec]
    congr 2
    simp only [← Matrix.mul_assoc, hAA, Matrix.one_mul]
  rw [key]
  exact cx_eig_orth N A hA adj hc hs hCC hu hQu

end CxQ

end EigenprojectionMatrices

namespace EigenprojectionMatrices

section Transfer

theorem eigSum_le_comap_of {k V W I : Type} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) (op : I → Module.End k V) (op' : I → Module.End k W) (hf : ∀ i v, f (op i v) = op' i (f v))
    (C : (I → k) → Prop) : Col.eigSum op C ≤ (Col.eigSum op' C).comap f := by
  have key : ∀ (i : I) (μ : k) (m : ℕ) (v : V),
      f (((op i - μ • 1) ^ m) v) = ((op' i - μ • 1) ^ m) (f v) := by
    intro i μ m
    induction m with
    | zero => intro v; simp
    | succ m ih =>
      intro v
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
      simp [hf]
  have hat : ∀ x, Col.eigAt op x ≤ (Col.eigAt op' x).comap f := by
    intro x v hv
    simp only [Col.eigAt, Submodule.mem_iInf, Submodule.mem_comap] at hv ⊢
    intro i
    obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp (hv i)
    exact (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨m, by rw [← key, hm, map_zero]⟩
  simp only [Col.eigSum]
  refine iSup₂_le fun x hx => (hat x).trans (Submodule.comap_mono ?_)
  exact le_iSup₂_of_le x hx le_rfl

variable {K : Type} [Field K] {I : Type} {N' : ℕ}

theorem toLin'_sub_pow (M : Matrix (Fin N') (Fin N') K) (c : K) (m : ℕ) (u : Fin N' → K) :
    ((Matrix.toLin' M - c • (1 : Module.End K (Fin N' → K))) ^ m) u = ((M - c • 1) ^ m) *ᵥ u := by
  have h1 : Matrix.toLin' M - c • (1 : Module.End K (Fin N' → K)) = Matrix.toLinAlgEquiv' (M - c • 1) := by
    rw [map_sub, map_smul, map_one]; rfl
  rw [h1, ← map_pow]; rfl

theorem emb_mem_eigSum (σ : K →+* ℂ) (M : I → Matrix (Fin N') (Fin N') K) (C : (I → K) → Prop) {u : Fin N' → K}
    (hu : u ∈ Col.eigSum (fun i => Matrix.toLin' (M i)) C) :
    (fun a => σ (u a)) ∈ Col.eigSum (linF fun i => (M i).map σ) (fun y => ∃ x, C x ∧ y = fun i => σ (x i)) := by
  have hM : ∀ (i : I) (c : K) (m : ℕ) (v : Fin N' → K),
      (fun a => σ ((((M i - c • 1) ^ m) *ᵥ v) a)) = (((M i).map σ - σ c • 1) ^ m) *ᵥ (fun a => σ (v a)) := by
    intro i c m v
    have hX : ((M i - c • 1) ^ m).map σ = ((M i).map σ - σ c • 1) ^ m := by
      rw [← RingHom.mapMatrix_apply, map_pow, map_sub, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply]
      congr 2
      ext p q
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    funext a
    rw [RingHom.map_mulVec, hX]
    rfl
  have hat : ∀ x, ∀ v ∈ Col.eigAt (fun i => Matrix.toLin' (M i)) x,
      (fun a => σ (v a)) ∈ Col.eigAt (linF fun i => (M i).map σ) (fun i => σ (x i)) := by
    intro x v hv
    simp only [Col.eigAt, Submodule.mem_iInf] at hv ⊢
    intro i
    obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp (hv i)
    refine (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨m, ?_⟩
    rw [toLin'_sub_pow] at hm
    have e := toLin'_sub_pow ((M i).map σ) (σ (x i)) m (fun a => σ (v a))
    simp only [linF]
    rw [e, ← hM i (x i) m v, hm]
    funext a
    simp
  let g : (Fin N' → K) →ₛₗ[σ] (Fin N' → ℂ) :=
    { toFun := fun v a => σ (v a)
      map_add' := fun v w => by funext a; simp
      map_smul' := fun c v => by funext a; simp }
  have hle : Col.eigSum (fun i => Matrix.toLin' (M i)) C ≤ (Col.eigSum (linF fun i => (M i).map σ)
      (fun y => ∃ x, C x ∧ y = fun i => σ (x i))).comap g := by
    unfold Col.eigSum
    refine iSup₂_le fun x hx => ?_
    intro v hv
    have h1 : Col.eigAt (linF fun i => (M i).map σ) (fun i => σ (x i)) ≤
        ⨆ (y) (_ : ∃ x, C x ∧ y = fun i => σ (x i)), Col.eigAt (linF fun i => (M i).map σ) y :=
      le_iSup₂_of_le (fun i => σ (x i)) ⟨x, hx, rfl⟩ le_rfl
    exact h1 (hat x v hv)
  exact hle hu

theorem mem_eigSum_of_emb {n m : ℕ} (N : I → Matrix (Fin n) (Fin n) ℂ) (Nf : I → Matrix (Fin m) (Fin m) ℂ)
    (Φ : Matrix (Fin m) (Fin n) ℂ) (Ψ : Matrix (Fin n) (Fin m) ℂ) (hΨ : Ψ * Φ = 1) (hΦ : ∀ i, Φ * N i = Nf i * Φ)
    (hc : Col.PairComm (linF N)) (hs : Col.SplitOver (linF N)) (hcf : Col.PairComm (linF Nf))
    (C : (I → ℂ) → Prop) {w : Fin n → ℂ} (hw : Φ *ᵥ w ∈ Col.eigSum (linF Nf) C) :
    w ∈ Col.eigSum (linF N) C := by
  have hf : ∀ i v, Matrix.toLin' Φ (linF N i v) = linF Nf i (Matrix.toLin' Φ v) := by
    intro i v
    simp only [linF, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hΦ i]
  have h1 : Φ *ᵥ Col.eigProj hc hs C w ∈ Col.eigSum (linF Nf) C :=
    eigSum_le_comap_of (Matrix.toLin' Φ) (linF N) (linF Nf) hf C (Col.eigProj_apply_mem hc hs C w)
  have h2 : Φ *ᵥ (w - Col.eigProj hc hs C w) ∈ Col.eigSum (linF Nf) (fun x => ¬ C x) :=
    eigSum_le_comap_of (Matrix.toLin' Φ) (linF N) (linF Nf) hf _ (Col.sub_eigProj_mem hc hs C w)
  have h3 : Φ *ᵥ (w - Col.eigProj hc hs C w) ∈ Col.eigSum (linF Nf) C := by
    rw [Matrix.mulVec_sub]
    exact Submodule.sub_mem _ hw h1
  have h4 : Φ *ᵥ (w - Col.eigProj hc hs C w) = 0 :=
    Submodule.disjoint_def.mp (Col.disjoint_eigSum hcf (C := C) (C' := fun x => ¬ C x)
      (fun x hx hn => hn hx)) _ h3 h2
  have h5 : w - Col.eigProj hc hs C w = 0 := by
    rw [← Matrix.one_mulVec (w - Col.eigProj hc hs C w), ← hΨ, ← Matrix.mulVec_mulVec, h4, Matrix.mulVec_zero]
  rw [sub_eq_zero] at h5
  rw [h5]
  exact Col.eigProj_apply_mem hc hs C w

end Transfer

end EigenprojectionMatrices

namespace EigenprojectionMatrices

theorem adj_transfer {R : Type} [CommRing R] [StarRing R] {n m : ℕ} (E : Matrix (Fin m) (Fin n) R)
    (H : Matrix (Fin m) (Fin m) R) (c : R) (T T' : Matrix (Fin n) (Fin n) R) (O O' : Matrix (Fin m) (Fin m) R)
    (hT : E * T = O * E) (hT' : E * T' = O' * E) (hO : H * O = O'ᴴ * H) :
    (c • (Eᴴ * H * E)) * T = T'ᴴ * (c • (Eᴴ * H * E)) := by
  have e1 : Eᴴ * H * E * T = (E * T')ᴴ * (H * E) := by
    rw [hT', Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [hT, ← Matrix.mul_assoc H O E, hO]
    simp only [Matrix.mul_assoc]
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  rw [e1, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v0 : InfinitePlace K} {s : ℕ} {Z : Submodule K B.S.Forms}

def tV (B : BlockDat K G Pl0) (ℓ : Lvl K G) (i : B.Pl × ℕ) : Matrix (Fin (B.nV ℓ)) (Fin (B.nV ℓ)) K :=
  B.vPr ℓ * B.opMat i * B.vE ℓ

theorem vE_tV (h : BlockHyp B ℓ v0 s) (i : B.Pl × ℕ) : B.vE ℓ * tV B ℓ i = B.opMat i * B.vE ℓ := by
  obtain ⟨⟨hPE, -⟩, hG⟩ := BlockDat.lf_v_proj h
  unfold tV
  calc B.vE ℓ * (B.vPr ℓ * B.opMat i * B.vE ℓ) = (B.vE ℓ * B.vPr ℓ) * B.opMat i * B.vE ℓ := by
        simp only [Matrix.mul_assoc]
    _ = B.opMat i * (B.vE ℓ * B.vPr ℓ) * B.vE ℓ := by rw [hG, ← CyclotomicLifting.opMat_gaMat h.ok.opG i]
    _ = B.opMat i * B.vE ℓ * (B.vPr ℓ * B.vE ℓ) := by simp only [Matrix.mul_assoc]
    _ = B.opMat i * B.vE ℓ := by rw [hPE, Matrix.mul_one]

theorem tV_comm (h : BlockHyp B ℓ v0 s) (i j : B.Pl × ℕ) : tV B ℓ i * tV B ℓ j = tV B ℓ j * tV B ℓ i := by
  have hij : B.opMat i * B.opMat j = B.opMat j * B.opMat i := by
    unfold BlockDat.opMat
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, (h.ok.comm i j).eq]
  have e : ∀ a b, tV B ℓ a * tV B ℓ b = B.vPr ℓ * (B.opMat a * B.opMat b) * B.vE ℓ := by
    intro a b
    calc tV B ℓ a * tV B ℓ b = B.vPr ℓ * B.opMat a * (B.vE ℓ * tV B ℓ b) := by
          unfold tV
          simp only [Matrix.mul_assoc]
      _ = B.vPr ℓ * (B.opMat a * B.opMat b) * B.vE ℓ := by
          rw [vE_tV h]
          simp only [Matrix.mul_assoc]
  rw [e, e, hij]

private theorem isHermitian_H_of_blockHyp (h : BlockHyp B ℓ v0 s) : (B.S.H)ᴴ = B.S.H := by
  ext a b
  have hH := (h.ok.hpos v0).1
  have e : ((B.S.H.map v0.embedding)ᴴ) a b = (B.S.H.map v0.embedding) a b := by rw [hH]
  apply v0.embedding.injective
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply] at e ⊢
  rw [(show ∀ τ : K →+* ℂ, τ (star (B.S.H b a)) = starRingEnd ℂ (τ (B.S.H b a)) from h.ok.hrat b a) v0.embedding,
    starRingEnd_apply]
  exact e

theorem tV_adj (h : BlockHyp B ℓ v0 s) (hH : B.OkH) (i : B.Pl × ℕ) :
    ∃ i', B.HV ℓ * tV B ℓ i = (tV B ℓ i')ᴴ * B.HV ℓ := by
  obtain ⟨i', hi'⟩ := CyclotomicLifting.opMat_adj hH i
  have hHh := isHermitian_H_of_blockHyp h
  have hO : B.S.H * B.opMat i = (B.opMat i')ᴴ * B.S.H := by
    have e := congrArg Matrix.conjTranspose hi'
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh] at e
    exact e
  refine ⟨i', ?_⟩
  rw [BlockDat.lf_HV_eq]
  exact adj_transfer (B.vE ℓ) B.S.H _ (tV B ℓ i) (tV B ℓ i') (B.opMat i) (B.opMat i') (vE_tV h i) (vE_tV h i') hO

theorem tV_zE (h : BlockHyp B ℓ v0 s) (hZ : ∀ i, Z ≤ Z.comap (B.op i)) (i : B.Pl × ℕ) :
    tV B ℓ i * B.zE ℓ Z = B.zE ℓ Z * (B.Pq ℓ Z * tV B ℓ i * B.zE ℓ Z) := by
  have hco : ∀ F, B.S.basis.equivFun (B.op i F) = B.opMat i *ᵥ B.S.basis.equivFun F := by
    intro F
    unfold BlockDat.opMat
    rw [Basis.equivFun_apply, Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
  have hmem : ∀ v ∈ B.Z0 ℓ Z, tV B ℓ i *ᵥ v ∈ B.Z0 ℓ Z := by
    intro v hv
    simp only [BlockDat.Z0, BlockDat.inV0, BlockDat.coord, Submodule.mem_comap, Submodule.mem_map,
      Matrix.mulVecLin_apply, LinearEquiv.coe_coe] at hv ⊢
    obtain ⟨F, hF, hFv⟩ := hv
    refine ⟨B.op i F, hZ i hF, ?_⟩
    rw [Matrix.mulVec_mulVec, vE_tV h i, ← Matrix.mulVec_mulVec, ← hFv, hco]
  have hr := (subspace_image_spec K (B.nV ℓ) (B.Z0 ℓ Z)).2
  have hPE := (BlockDat.Pq_orth h.conj h.ok h.irr : IsOrthProj (B.HV ℓ) (B.zE ℓ Z) (B.Pq ℓ Z)).1
  have key : ∀ w, (tV B ℓ i * B.zE ℓ Z) *ᵥ w = (B.zE ℓ Z * (B.Pq ℓ Z * tV B ℓ i * B.zE ℓ Z)) *ᵥ w := by
    intro w
    have hz : B.zE ℓ Z *ᵥ w ∈ B.Z0 ℓ Z := by
      rw [← hr]
      exact LinearMap.mem_range_self _ w
    have ht := hmem _ hz
    rw [← hr] at ht
    obtain ⟨w', hw'⟩ := ht
    have hw'' : B.zE ℓ Z *ᵥ w' = tV B ℓ i *ᵥ (B.zE ℓ Z *ᵥ w) := hw'
    simp only [← Matrix.mulVec_mulVec]
    rw [← hw'']
    congr 1
    rw [Matrix.mulVec_mulVec, hPE, Matrix.one_mulVec]
  exact Matrix.toLin'.injective (LinearMap.ext fun w => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact key w)

end EigenprojectionMatrices

namespace EigenprojectionMatrices

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v0 : InfinitePlace K} {s : ℕ} {Z : Submodule K B.S.Forms}

theorem HZ_unit (h : BlockHyp B ℓ v0 s) : IsUnit ((B.zE ℓ Z)ᴴ * B.HV ℓ * B.zE ℓ Z) := by
  have hv0' : ∀ a : K, v0.embedding (star a) = star (v0.embedding a) := fun a => by
    rw [h.conj a, starRingEnd_apply]
  have hposK : ∀ c : Fin B.S.dim → K, star c ⬝ᵥ B.S.H *ᵥ c = 0 → c = 0 := by
    intro c h0
    have h1 : star (fun i => v0.embedding (c i)) ⬝ᵥ (B.S.H.map v0.embedding) *ᵥ (fun i => v0.embedding (c i)) =
        v0.embedding (star c ⬝ᵥ B.S.H *ᵥ c) := by
      simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, hv0', Matrix.map_apply]
    rw [h0, map_zero] at h1
    by_contra hc0
    have hne : (fun i => v0.embedding (c i)) ≠ 0 := by
      intro h2
      apply hc0
      funext i
      have h3 := congrFun h2 i
      simpa using h3
    have h4 := (h.ok.hpos v0).dotProduct_mulVec_pos hne
    rw [h1] at h4
    exact lt_irrefl _ h4
  obtain ⟨⟨hPE, -⟩, -⟩ := BlockDat.lf_v_proj h
  have hinj := (subspace_image_spec K (B.nV ℓ) (B.Z0 ℓ Z)).1
  have hcard : (Nat.card ℓ.P : K)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hsm : ∀ (c : K) (M : Matrix (Fin (B.dZ ℓ Z)) (Fin (B.dZ ℓ Z)) K) (v : Fin (B.dZ ℓ Z) → K),
      (c • M) *ᵥ v = c • (M *ᵥ v) := fun c M v => by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hw0
  have h1 : star w ⬝ᵥ ((B.zE ℓ Z)ᴴ * B.HV ℓ * B.zE ℓ Z) *ᵥ w = 0 := by rw [hw, dotProduct_zero]
  rw [BlockDat.lf_HV_eq, Matrix.mul_smul, Matrix.smul_mul, hsm, dotProduct_smul, smul_eq_mul,
    mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 hcard
  simp only [← Matrix.mulVec_mulVec] at h1
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec] at h1
  have h3 := hposK _ h1
  have h5 : B.zE ℓ Z *ᵥ w = 0 := by
    have h4 := congrArg (fun x => B.vPr ℓ *ᵥ x) h3
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hPE, Matrix.one_mul, Matrix.mulVec_zero] at h4
    exact h4
  apply hinj
  show B.zE ℓ Z *ᵥ w = B.zE ℓ Z *ᵥ 0
  rw [h5, Matrix.mulVec_zero]

theorem Pq_tV (h : BlockHyp B ℓ v0 s) (hH : B.OkH) (hZ : ∀ i, Z ≤ Z.comap (B.op i)) (i : B.Pl × ℕ) :
    B.Pq ℓ Z * tV B ℓ i = (B.Pq ℓ Z * tV B ℓ i * B.zE ℓ Z) * B.Pq ℓ Z := by
  obtain ⟨hPE, hEH⟩ := (BlockDat.Pq_orth h.conj h.ok h.irr : IsOrthProj (B.HV ℓ) (B.zE ℓ Z) (B.Pq ℓ Z))
  obtain ⟨i', hi'⟩ := tV_adj h hH i
  have hX := tV_zE h hZ i'
  have hW : IsUnit ((B.zE ℓ Z)ᴴ * B.HV ℓ * B.zE ℓ Z) := HZ_unit h
  have key : (B.zE ℓ Z)ᴴ * B.HV ℓ * tV B ℓ i * (1 - B.zE ℓ Z * B.Pq ℓ Z) = 0 := by
    calc (B.zE ℓ Z)ᴴ * B.HV ℓ * tV B ℓ i * (1 - B.zE ℓ Z * B.Pq ℓ Z)
        = (B.zE ℓ Z)ᴴ * (B.HV ℓ * tV B ℓ i) * (1 - B.zE ℓ Z * B.Pq ℓ Z) := by
          simp only [Matrix.mul_assoc]
      _ = (B.zE ℓ Z)ᴴ * ((tV B ℓ i')ᴴ * B.HV ℓ) * (1 - B.zE ℓ Z * B.Pq ℓ Z) := by rw [hi']
      _ = (tV B ℓ i' * B.zE ℓ Z)ᴴ * B.HV ℓ * (1 - B.zE ℓ Z * B.Pq ℓ Z) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (B.zE ℓ Z * (B.Pq ℓ Z * tV B ℓ i' * B.zE ℓ Z))ᴴ * B.HV ℓ * (1 - B.zE ℓ Z * B.Pq ℓ Z) := by
          rw [hX]
      _ = (B.Pq ℓ Z * tV B ℓ i' * B.zE ℓ Z)ᴴ * ((B.zE ℓ Z)ᴴ * B.HV ℓ * (1 - B.zE ℓ Z * B.Pq ℓ Z)) := by
          rw [Matrix.conjTranspose_mul (B.zE ℓ Z)]
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hEH, Matrix.mul_zero]
  have hWP : (B.zE ℓ Z)ᴴ * B.HV ℓ = ((B.zE ℓ Z)ᴴ * B.HV ℓ * B.zE ℓ Z) * B.Pq ℓ Z := by
    have e := hEH
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at e
    exact e.trans (Matrix.mul_assoc _ _ _).symm
  have hdet : IsUnit ((B.zE ℓ Z)ᴴ * B.HV ℓ * B.zE ℓ Z).det := (Matrix.isUnit_iff_isUnit_det _).mp hW
  have hP : ((B.zE ℓ Z)ᴴ * B.HV ℓ * B.zE ℓ Z)⁻¹ * ((B.zE ℓ Z)ᴴ * B.HV ℓ) = B.Pq ℓ Z := by
    have e := congrArg (fun M => ((B.zE ℓ Z)ᴴ * B.HV ℓ * B.zE ℓ Z)⁻¹ * M) hWP
    rw [e, ← Matrix.mul_assoc ((B.zE ℓ Z)ᴴ * B.HV ℓ * B.zE ℓ Z)⁻¹, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have h3 : B.Pq ℓ Z * tV B ℓ i * (1 - B.zE ℓ Z * B.Pq ℓ Z) = 0 := by
    calc B.Pq ℓ Z * tV B ℓ i * (1 - B.zE ℓ Z * B.Pq ℓ Z)
        = ((B.zE ℓ Z)ᴴ * B.HV ℓ * B.zE ℓ Z)⁻¹ * ((B.zE ℓ Z)ᴴ * B.HV ℓ) * tV B ℓ i *
          (1 - B.zE ℓ Z * B.Pq ℓ Z) := by rw [hP]
      _ = ((B.zE ℓ Z)ᴴ * B.HV ℓ * B.zE ℓ Z)⁻¹ *
          ((B.zE ℓ Z)ᴴ * B.HV ℓ * tV B ℓ i * (1 - B.zE ℓ Z * B.Pq ℓ Z)) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [key, Matrix.mul_zero]
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h3
  exact h3.trans (by simp only [Matrix.mul_assoc])

end EigenprojectionMatrices

section Main

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
variable (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)
variable (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)

theorem proviso_at {s : ℕ} (hOk : A.fam.Ok s) (hH : HeckeRatL A) (P : Subgroup G) (ψ : P →* Kˣ)
    {C : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop} (hC : LiftsEig A X P ψ C) :
    (A.fam.side P ψ X.zs).Proviso :=
  A.fam.side_Proviso hOk P ψ X.zs fun j => by
    show SubHasRatBasis ((A.fam.L j A.fam.μ0).Z0 (A.fam.lvlA P ψ) (X.Zl j A.fam.μ0))
    rw [hC j]
    exact EigenprojectionMatrices.eig_rat (A.fam.blockHyp_lift hOk P ψ j A.fam.μ0) (hH j) (C j)

theorem types_at {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep) (hst : X.zs.Stable) (P : Subgroup G)
    (ψ : P →* Kˣ) {C : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop} (hC : LiftsEig A X P ψ C)
    (hT : LiftsTyp A C) : (A.fam.side P ψ X.zs).Types :=
  A.fam.side_Types hOk P ψ X.zs hst hsep fun j => by
    show (A.fam.L j A.fam.μ0).Z0 (A.fam.lvlA P ψ) (X.Zl j A.fam.μ0) ≤ _
    rw [hC j]
    exact (A.fam.L j A.fam.μ0).good_part_coordinates_mono _ (Col.eigSum_mono fun x hx => hT j x hx)

theorem cutProviso : CutProviso A X P0 ψ0 P1 ψ1 Dc Sp Zsc := by
  intro s C0 C1 hOk hH h0 h1 b
  cases b
  · exact proviso_at A X hOk hH P0 ψ0 h0
  · exact proviso_at A X hOk hH P1 ψ1 h1

theorem cutTypes : CutTypes A X P0 ψ0 P1 ψ1 Dc Sp Zsc := by
  intro s C0 C1 hOk hsep hst h0 h1 t0 t1 b
  cases b
  · exact types_at A X hOk hsep hst P0 ψ0 h0 t0
  · exact types_at A X hOk hsep hst P1 ψ1 h1 t1

end Main

end Formalism.IndefR.Cx

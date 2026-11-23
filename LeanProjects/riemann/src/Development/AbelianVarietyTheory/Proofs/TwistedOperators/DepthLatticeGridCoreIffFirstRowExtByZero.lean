import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumRestrictionRankZero
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionFunctionIncZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationXiZeroEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMatrixSandwichMemCompletedIdealLatticeHo
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionCoreProjMulCoreEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CoreRowLat

variable {D : D7}

theorem gen_negSp (S T : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * (negSp S).gram k j) : WO S T) =
      -(Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) := by
  ext i j; simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem latO_negSp (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P = latO S T LS LT P := by
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩
    show _ ∈ latO S T LS LT P
    rw [gen_negSp S T α a s t]
    exact neg_mem (AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩)
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩
    rw [← neg_neg (Matrix.of _), ← gen_negSp S T α a s t]
    exact neg_mem (AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩)

theorem latO_mul_left {S T T' : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {LT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)} {P : HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (A : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (hA : ∀ t ∈ LT, A *ᵥ t ∈ LT') {u : WO S T}
    (hu : u ∈ latO S T LS (LT : Set _) P) : (rat A : Mx D T'.rank T.rank) * u ∈ latO S T' LS (LT' : Set _) P :=
  GlobalTheory.OverTgt.mul_mem_latO (rat A) (fun _ hy => GlobalTheory.SeeSaw.CoreGlue.rat_mulVec_mem A hA hy) hu

theorem latO_mul_right {S S' T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LS' : Set (Fin S'.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)} {P : HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (M : Matrix (Fin S.rank) (Fin S'.rank) D.host.E)
    (hM : ∀ s ∈ LS, ∃ s' ∈ LS', ∀ j, ∑ l, (∑ k, star (s k) * S.gram k l) * M l j = ∑ k, star (s' k) * S'.gram k j)
    {u : WO S T} (hu : u ∈ latO S T LS LT P) : u * (rat M : Mx D S.rank S'.rank) ∈ latO S' T LS' LT P := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩ := hw
    obtain ⟨s', hs', hss⟩ := hM s hs
    refine AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s', hs', t, ht, ?_⟩
    ext i j
    rw [Matrix.mul_apply, Matrix.of_apply, ← hss j, Finset.mul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.of_apply]
    show _ * incA D (M l j) = _
    rw [GlobalTheory.RankZeroVac.incA_tmul', Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc]
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_mul]; exact neg_mem hx

theorem hatMx_mul_left {m m' n : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)}
    (A : Matrix (Fin m') (Fin m) D.host.E) (hA : ∀ t ∈ Λ', A *ᵥ t ∈ Λ'') {x : Mx D m n}
    (hx : x ∈ hatMx (I • homLat Λ Λ')) : (rat A : Mx D m' m) * x ∈ hatMx (I • homLat Λ Λ'') := by
  have h := GlobalTheory.TwistHatMx.rat_conj_mem_hatMx I 1 A (fun y hy => by rwa [Matrix.one_mulVec]) hA x hx
  rwa [rat_one, Matrix.mul_one] at h

theorem hatMx_mul_right {m n n' : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)}
    (N : Matrix (Fin n) (Fin n') D.host.E) (hN : ∀ s ∈ Λ₁, N *ᵥ s ∈ Λ) {x : Mx D m n}
    (hx : x ∈ hatMx (I • homLat Λ Λ')) : x * (rat N : Mx D n n') ∈ hatMx (I • homLat Λ₁ Λ') := by
  have h := GlobalTheory.TwistHatMx.rat_conj_mem_hatMx I N 1 hN (fun y hy => by rwa [Matrix.one_mulVec]) x hx
  rwa [rat_one, Matrix.one_mul] at h

theorem wittEmbedding_preserves_hermitianForm {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (s : Fin S₀.rank → D.host.E) (j : Fin S₀.rank) :
    ∑ l, (∑ k, star ((d.i₀ *ᵥ s) k) * S.gram k l) * d.i₀ l j = ∑ k, star (s k) * S₀.gram k j := by
  have h : Matrix.vecMul (Matrix.vecMul (star (d.i₀ *ᵥ s)) S.gram) d.i₀ = Matrix.vecMul (star s) S₀.gram := by
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, d.iso]
  have hj := congrFun h j
  simpa only [Matrix.vecMul, dotProduct, Pi.star_apply] using hj

end GlobalTheory.CoreRowLat

namespace GlobalTheory.CoreRowLat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem std_zA_lat {F : Frames G} (hF : Std F) : (∀ y ∈ G.Λ (.grid 0 0), F.oz.iA *ᵥ y ∈ G.Λ (.core 0)) ∧
    ∀ x ∈ G.Λ (.core 0), F.oz.qA *ᵥ x ∈ G.Λ (.grid 0 0) := by
  have hΛ : G.Λ (.core 0) = sumLat (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι) (L.ΛY 0) G.sp.dec0.a (fun _ => 1) :=
    G.sp.lat0
  have hqi : F.oz.qA * F.oz.iA = 1 := rat_injective (by rw [rat_mul, rat_one]; exact F.oz.pA_jA)
  have hperp := G.sp.dec0.perp
  have hqa : F.oz.qA * G.sp.dec0.a = 0 := by
    change (HSpace.gram (Yc D 0))⁻¹ * (F.oz.iAᴴ * HSpace.gram (G.V (.core 0))) * G.sp.dec0.a = 0
    rw [hF.zA, Matrix.mul_assoc, Matrix.mul_assoc]
    have hp : (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι)ᴴ * HSpace.gram (G.sp.P 0).sp * G.sp.dec0.a = 0 := hperp
    rw [← Matrix.mul_assoc (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι)ᴴ, hp, Matrix.mul_zero]
  refine ⟨fun y hy => ?_, fun x hx => ?_⟩
  · rw [hΛ]
    refine ⟨y, hy, 0, fun _ => (FractionalIdeal.mem_one_iff _).2 ⟨0, map_zero _⟩, ?_⟩
    rw [Matrix.mulVec_zero, add_zero, hF.zA]
  · rw [hΛ] at hx
    obtain ⟨y, hy, u, -, rfl⟩ := hx
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hF.zA, hqi, hqa, Matrix.one_mulVec,
      Matrix.zero_mulVec, add_zero]
    exact hy

theorem std_aJ_lat {F : Frames G} (hF : Std F) (h : 2 * 0 + 2 ≤ D.R.m) :
    (∀ y ∈ G.Λ (.core 1), (F.dJ 0 h).i₀ *ᵥ y ∈ G.Λ (.grid 1 0)) ∧
    (∀ x ∈ G.Λ (.grid 1 0), ∃ y ∈ G.Λ (.core 1), x = (F.dJ 0 h).i₀ *ᵥ y) ∧
    ∀ x ∈ G.Λ (.grid 1 0), (F.dJ 0 h).q0 *ᵥ x ∈ G.Λ (.core 1) := by
  have h1 : 1 ≤ D.R.m := by omega
  have hΛ : G.Λ (.grid 1 0) = sumLat (frameMat (G.V (.grid 1 0)) (G.V (.core 1)) (G.colDec 1 le_rfl h1).ι) (G.Λ (.core 1))
      (G.colDec 1 le_rfl h1).a (stairId (G.pl.stA sc) (G.pl.stAbar sc) (1 - 1)) := G.sp.colLat 1 le_rfl h1
  have hi : (F.dJ 0 h).i₀ = frameMat (G.V (.grid 1 0)) (G.V (.core 1)) (G.colDec 1 le_rfl h1).ι := hF.aJ 0 h
  have hqi : (F.dJ 0 h).q0 * (F.dJ 0 h).i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact (F.dJ 0 h).p0_j0)
  have mem : ∀ x, x ∈ G.Λ (.grid 1 0) ↔ ∃ y ∈ G.Λ (.core 1), x = (F.dJ 0 h).i₀ *ᵥ y := by
    intro x
    rw [hΛ, hi]
    constructor
    · rintro ⟨y, hy, u, -, rfl⟩
      refine ⟨y, hy, ?_⟩
      have : (G.colDec 1 le_rfl h1).a *ᵥ u = 0 := by
        funext i; simp [Matrix.mulVec, dotProduct]
      rw [this, add_zero]
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, 0, fun p => p.elim0, by rw [Matrix.mulVec_zero, add_zero]⟩
  refine ⟨fun y hy => (mem _).2 ⟨y, hy, rfl⟩, fun x hx => (mem x).1 hx, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := (mem x).1 hx
  rwa [Matrix.mulVec_mulVec, hqi, Matrix.one_mulVec]

end GlobalTheory.CoreRowLat

namespace GlobalTheory.CoreRowLat

variable {D : D7}

theorem depthLattice_generalPosition_iff_extByZero {P₁ P₀ Y Lz S : HSp D} (o : OrthDec P₀ Y Lz) (d : HypDec S P₁ 0)
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin P₁.rank → D.host.E)} {Λ₀ : Submodule (𝓞 D.host.E) (Fin P₀.rank → D.host.E)}
    {ΛY : Submodule (𝓞 D.host.E) (Fin Y.rank → D.host.E)} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    (I : Ideal (𝓞 D.host.E)) (Q : AE D → Prop)
    (hiA : ∀ y ∈ ΛY, o.iA *ᵥ y ∈ Λ₀) (hqA : ∀ x ∈ Λ₀, o.qA *ᵥ x ∈ ΛY)
    (hi0 : ∀ y ∈ Λ₁, d.i₀ *ᵥ y ∈ ΛS) (hq0 : ∀ x ∈ ΛS, ∃ y ∈ Λ₁, x = d.i₀ *ᵥ y) (hq0' : ∀ x ∈ ΛS, d.q0 *ᵥ x ∈ Λ₁)
    (a : WO P₁ Y) :
    (o.jA * a ∈ latO (negSp P₁) P₀ (Λ₁ : Set _) (Λ₀ : Set _) (fun _ => True) ∧
      ∀ e : AE D, Q e → e • (o.jA * a) ∈ hatMx (I • homLat Λ₁ Λ₀)) ↔
    (d.ext0 Y a ∈ latO (negSp S) Y (ΛS : Set _) (ΛY : Set _) (fun _ => True) ∧
      ∀ e : AE D, Q e → e • d.ext0 Y a ∈ hatMx (I • homLat ΛS ΛY)) := by
  have hpj : d.p0 * (rat d.i₀ : Mx D _ _) = 1 := d.p0_j0
  have hpA : (rat o.qA : Mx D _ _) * o.jA = 1 := o.pA_jA
  have cB : ∀ x : WO P₁ Y, x * d.p0 * (rat d.i₀ : Mx D _ _) = x := fun x => by
    rw [Matrix.mul_assoc, hpj, Matrix.mul_one]
  have cA : ∀ x : WO P₁ Y, (rat o.qA : Mx D _ _) * (o.jA * x) = x := fun x => by
    rw [← Matrix.mul_assoc, hpA, Matrix.one_mul]
  have ext : d.ext0 Y a = a * d.p0 := rfl
  rw [ext, latO_negSp, latO_negSp]
  have hA1 : o.jA * a ∈ latO P₁ P₀ (Λ₁ : Set _) (Λ₀ : Set _) (fun _ => True) ↔
      a ∈ latO P₁ Y (Λ₁ : Set _) (ΛY : Set _) (fun _ => True) := by
    constructor
    · intro hu
      have := latO_mul_left o.qA hqA hu
      rwa [cA] at this
    · intro hu; exact latO_mul_left o.iA hiA hu
  have hB1 : a ∈ latO P₁ Y (Λ₁ : Set _) (ΛY : Set _) (fun _ => True) ↔
      a * d.p0 ∈ latO S Y (ΛS : Set _) (ΛY : Set _) (fun _ => True) := by
    constructor
    · intro hu
      exact latO_mul_right d.q0 (fun s hs => ⟨d.i₀ *ᵥ s, hi0 s hs, fun j => GlobalTheory.RankZeroVac.wittDecomposition_gram_projection_identity d s j⟩) hu
    · intro hu
      have := latO_mul_right d.i₀ (fun s hs => by
        obtain ⟨y, hy, rfl⟩ := hq0 s hs
        exact ⟨y, hy, fun j => wittEmbedding_preserves_hermitianForm d y j⟩) hu
      rwa [cB] at this
  have hA2 : ∀ e : AE D, e • (o.jA * a) ∈ hatMx (I • homLat Λ₁ Λ₀) ↔ e • a ∈ hatMx (I • homLat Λ₁ ΛY) := by
    intro e
    rw [← Matrix.mul_smul]
    constructor
    · intro hx
      have := hatMx_mul_left I o.qA hqA hx
      rwa [cA] at this
    · intro hx; exact hatMx_mul_left I o.iA hiA hx
  have hB2 : ∀ e : AE D, e • a ∈ hatMx (I • homLat Λ₁ ΛY) ↔ e • (a * d.p0) ∈ hatMx (I • homLat ΛS ΛY) := by
    intro e
    rw [← Matrix.smul_mul]
    constructor
    · intro hx; exact hatMx_mul_right I d.q0 hq0' hx
    · intro hx
      have := hatMx_mul_right I d.i₀ hi0 hx
      rwa [cB] at this
  exact and_congr (hA1.trans hB1) (forall_congr' fun e => imp_congr_right fun _ => (hA2 e).trans (hB2 e))

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem jA_mem_latCore_iff : OnStd fun {D} _ _ _ {G} _ F => ∀ (h : 2 * 0 + 2 ≤ D.R.m) (a : WO (G.V (.core 1)) (Yc D 0)),
    F.oz.jA * a ∈ latCore G 0 ↔ (F.dJ 0 h).ext0 (Yc D 0) a ∈ latRow G 0 := by
  intro D _ T L _ _ sc G W M _ F hF h a
  obtain ⟨hiA, hqA⟩ := std_zA_lat hF
  obtain ⟨hi0, hq0, hq0'⟩ := std_aJ_lat hF h
  exact depthLattice_generalPosition_iff_extByZero F.oz (F.dJ 0 h) G.modul (fun e => IsIdemSum e G.pl.W0) hiA hqA hi0 hq0 hq0' a

end GlobalTheory.CoreRowLat

end

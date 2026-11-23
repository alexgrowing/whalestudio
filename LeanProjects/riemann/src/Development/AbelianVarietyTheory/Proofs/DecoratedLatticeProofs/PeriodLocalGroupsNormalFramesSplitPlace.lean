import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemRootExchangeParabolicAndFourierJacobiIffEntri
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizesSelfDualIffFrameMatrixStabilizes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocGrpIff
open GlobalTheory.LocGrp

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {Y : Type} [Fintype Y] [DecidableEq Y]

theorem transfer_back {K : Type} [Field K] {Z : Type} [Fintype Z] [DecidableEq Z] {m : ℕ} {β : Matrix (Fin m) Y K}
    {γ : Matrix Y (Fin m) K} (h : γ * β = 1) {β' : Matrix (Fin m) Z K}
    {γ' : Matrix Z (Fin m) K} (h' : γ' * β' = 1) (τ : Z → Y) (hτ : Function.Surjective τ) (t : Z → K)
    (ht : ∀ r z, β r (τ z) = t z * β' r z) (N : Matrix Y Y K) (z z' : Z) (hN : (γ' * (β * N * γ) * β') z z' = 0) :
    N (τ z) (τ z') = 0 := by
  have e : γ' * (β * N * γ) * β' = γ' * β * N * (γ * β') := by simp only [Matrix.mul_assoc]
  have a0 : ∀ w, (γ' * β) z (τ w) = t w * (1 : Matrix Z Z K) z w := fun w => by
    rw [← h']
    simp only [Matrix.mul_apply, ht, mul_left_comm _ (t w), ← Finset.mul_sum]
  have a1 : ∀ r, r ≠ τ z → (γ' * β) z r = 0 := fun r hr => by
    obtain ⟨w, rfl⟩ := hτ r
    rw [a0, Matrix.one_apply_ne (fun e => hr (by rw [e])), mul_zero]
  have a2 : ∀ w s, t w * (γ * β') s w = (1 : Matrix Y Y K) s (τ w) := fun w s => by
    rw [← h]
    simp only [Matrix.mul_apply, ht, mul_left_comm _ (t w), ← Finset.mul_sum]
  have a3 : t z ≠ 0 := fun e0 => by
    have := a2 z (τ z)
    rw [e0, zero_mul, Matrix.one_apply_eq] at this
    exact zero_ne_one this
  have a4 : t z' * (γ' * β * N * (γ * β')) z z' = (γ' * β * N * (1 : Matrix Y Y K)) z (τ z') := by
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [mul_left_comm, a2]
  rw [← e, hN, mul_zero, Matrix.mul_one, Matrix.mul_apply, Finset.sum_eq_single (τ z) (fun r _ hr => by rw [a1 r hr, zero_mul])
    (fun h => absurd (Finset.mem_univ _) h), a0, Matrix.one_apply_eq, mul_one] at a4
  exact (mul_eq_zero.1 a4.symm).resolve_left a3

section Witt
variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem flag_cols {g : GA D S} (hg : g ∈ flagN d) : ∃ (T : Mx D ρ ρ) (B : Mx D ρ S₀.rank), GlobalTheory.BesselChar.StrictUp T ∧
    (mt S g - 1) ⬝ d.jX = d.jX ⬝ T ∧ (mt S g - 1) ⬝ d.j0 = d.jX ⬝ B := by
  obtain ⟨⟨T, hT, h1⟩, h2⟩ := (GlobalTheory.BesselChar.mem_NFlag_iff S d.e (GlobalTheory.MixPer.Decomp.linInd d) g).1 hg
  obtain ⟨B, hB⟩ := GlobalTheory.MixPer.Decomp.exists_B d h2
  have h1' : mt S g ⬝ d.jX = d.jX + d.jX ⬝ T := h1
  refine ⟨T, B, hT, ?_, ?_⟩
  · rw [Matrix.sub_mul, Matrix.one_mul, h1', add_sub_cancel_left]
  · rw [Matrix.sub_mul, Matrix.one_mul, hB, add_sub_cancel_left]

theorem flag_YY {g : GA D S} (hg : g ∈ flagN d) {i j : Fin ρ} (hij : i ≤ j) : (d.pY ⬝ ((mt S g - 1) ⬝ d.jY)) i j = 0 := by
  obtain ⟨T, -, hT, h1, -⟩ := flag_cols d (inv_mem hg)
  have e1 : adj (mt S g⁻¹) ⬝ gA S = gA S ⬝ mt S g := by
    conv_rhs => rw [← inv_inv g, GlobalTheory.MixModel.mt_inv, gA_giA_cancel]
  have e2 : d.pY ⬝ ((mt S g - 1) ⬝ d.jY) = adj ((mt S g⁻¹ - 1) ⬝ d.jX) ⬝ (gA S ⬝ d.jY) := by
    simp only [d.pY_eq, adj_mul, adj_sub, adj_one, Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      cancel₂ e1]
  rw [e2, h1, adj_mul, Matrix.mul_assoc, d.gram_XY, Matrix.mul_one]
  change cA D (T j i) = 0
  rw [hT j i hij, RingHom.map_zero]

theorem tri_of_flag (F₀ : Frame k S₀.rank Y) {g : GA D S} (hg : g ∈ flagN d) : Tri p d F₀ ((mt S g).map p.π - 1) := by
  obtain ⟨T, B, hT, hX, h0⟩ := flag_cols d hg
  have z0 : ∀ {a b : ℕ}, (0 : Mx D a b).map p.π = 0 := Matrix.map_zero _ (map_zero _)
  have m1 : (mt S g).map p.π - 1 = (mt S g - 1).map p.π := by
    rw [Matrix.map_sub _ (map_sub p.π), Matrix.map_one _ (map_zero _) (map_one _)]
  have cX : (mt S g - 1).map p.π * d.jX.map p.π = d.jX.map p.π * T.map p.π := by
    rw [← Matrix.map_mul, hX, Matrix.map_mul]
  have c0 : (mt S g - 1).map p.π * (d.j0.map p.π * F₀.β) = d.jX.map p.π * (B.map p.π * F₀.β) := by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, h0, Matrix.map_mul, Matrix.mul_assoc]
  have r0 : ∀ {Z : Type} (C : Matrix (Fin ρ) Z k), F₀.γ * d.p0.map p.π * (d.jX.map p.π * C) = 0 := fun C => by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ C, ← Matrix.map_mul, d.p0_jX, z0, Matrix.zero_mul, Matrix.mul_zero]
  have rY : ∀ {Z : Type} (C : Matrix (Fin ρ) Z k), d.pY.map p.π * (d.jX.map p.π * C) = 0 := fun C => by
    rw [← Matrix.mul_assoc _ _ C, ← Matrix.map_mul, d.pY_jX, z0, Matrix.zero_mul]
  have rX : ∀ {Z : Type} (C : Matrix (Fin ρ) Z k), d.pX.map p.π * (d.jX.map p.π * C) = C := fun C => by
    rw [← Matrix.mul_assoc _ _ C, ← Matrix.map_mul, d.pX_jX, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rw [m1]
  intro z z' hz
  rw [Matrix.mul_assoc]
  rcases z with a | i | i <;> rcases z' with b | j | j <;> simp only [wlev, Sum.elim_inr, Sum.elim_inl] at hz
  · change (F₀.γ * d.p0.map p.π * ((mt S g - 1).map p.π * (d.j0.map p.π * F₀.β))) a b = 0
    rw [c0, r0]; rfl
  · change (F₀.γ * d.p0.map p.π * ((mt S g - 1).map p.π * d.jX.map p.π)) a j = 0
    rw [cX, r0]; rfl
  · omega
  · omega
  · change (d.pX.map p.π * ((mt S g - 1).map p.π * d.jX.map p.π)) i j = 0
    rw [cX, rX, Matrix.map_apply, hT i j (by rw [Fin.le_def]; omega), RingHom.map_zero]
  · omega
  · change (d.pY.map p.π * ((mt S g - 1).map p.π * (d.j0.map p.π * F₀.β))) i b = 0
    rw [c0, rY]; rfl
  · change (d.pY.map p.π * ((mt S g - 1).map p.π * d.jX.map p.π)) i j = 0
    rw [cX, rY]; rfl
  · change (d.pY.map p.π * ((mt S g - 1).map p.π * d.jY.map p.π)) i j = 0
    rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, flag_YY d hg (by rw [Fin.le_def]; omega), RingHom.map_zero]

def FlagFrame (F : Frame k S.rank Y) (l : Y → ℕ) : Prop :=
  (∀ g q, p.IsLoc F g q → Radical.Uni l q.val → g ∈ flagN d) ∧
    ∀ g ∈ flagN d, Radical.Uni l (coordHom S p.π F.β F.γ F.βγ F.γβ g).val

theorem flagFrame {Y₀ : Type} [Fintype Y₀] [DecidableEq Y₀]
    (F₀ : Frame k S₀.rank Y₀) (F : Frame k S.rank Y) (τ : Y₀ ⊕ (Fin ρ ⊕ Fin ρ) → Y) (hτ : Function.Surjective τ)
    (t : Y₀ ⊕ (Fin ρ ⊕ Fin ρ) → k) (ht : ∀ r z, F.β r (τ z) = t z * wβ p d F₀ r z) (l l' : Y → ℕ)
    (hl : ∀ z, l (τ z) = wlev Y₀ ρ z) (hl' : ∀ r s, l s ≤ l r ↔ l' s ≤ l' r) : FlagFrame p d F l' := by
  refine ⟨fun g q hg hq => flag_of_strict p d F₀ F τ hτ t ht l hl hg fun r s hrs => ?_, fun g hg r s hrs => ?_⟩
  · rw [Matrix.sub_apply, hq r s ((hl' r s).1 hrs), sub_self]
  · obtain ⟨z, rfl⟩ := hτ r
    obtain ⟨z', rfl⟩ := hτ s
    have h := tri_of_flag p d F₀ hg z z' (by rw [← hl, ← hl]; exact (hl' _ _).2 hrs)
    have e : (mt S g).map p.π - 1 = F.β * ((coordHom S p.π F.β F.γ F.βγ F.γβ g).val - 1) * F.γ := by
      rw [(eq_coordHom_iff S p.π F.β F.γ F.βγ F.γβ g _).2 rfl, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, F.βγ]
    rw [e] at h
    have := transfer_back F.γβ (wγ_wβ p d F₀) τ hτ t ht _ z z' h
    rwa [Matrix.sub_apply, sub_eq_zero] at this

end Witt

theorem intertwine' {S T : HSp D} {g : GA D S} {h : GA D T} {j : Mx D S.rank T.rank} (e : mt S g ⬝ j = j ⬝ mt T h)
    (F₀ : Frame k T.rank Y) : (mt S g).map p.π * (j.map p.π * F₀.β) =
      j.map p.π * F₀.β * (coordHom T p.π F₀.β F₀.γ F₀.βγ F₀.γβ h).val := by
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, e, Matrix.map_mul, coordHom_val]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F₀.β, F₀.βγ, Matrix.one_mul]

variable {n : Type} [Fintype n] [DecidableEq n] {c ρ : ℕ}

theorem flagFrame_jac (J : JacLev D ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c))
    (hF : p.IsJacFrame J s hh F₀ F) :
    FlagFrame p J.d F (Sum.elim (fun _ => 2 * ρ + 1) fun i : Fin c => 2 * (i.val + 1)) := by
  obtain ⟨rfl, h0, hX, hY⟩ := hF
  refine flagFrame p J.d F₀ F
      (Sum.map id (Sum.elim (fun i : Fin ρ => (⟨i.val, by omega⟩ : Fin (2 * ρ))) fun i : Fin ρ => ⟨2 * ρ - 1 - i.val, by omega⟩))
      ?_ (Sum.elim (fun _ => 1)
        (Sum.elim (fun i => s * p.xi ^ (ρ - i.val)) fun i => s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val))) ?_
      (Sum.elim (fun _ => ρ + 1) fun j => if j.val < ρ then j.val + 1 else j.val + 2) _ ?_ ?_
  · rintro (a | j)
    · exact ⟨Sum.inl a, rfl⟩
    · by_cases h : j.val < ρ
      · exact ⟨Sum.inr (Sum.inl ⟨j.val, h⟩), rfl⟩
      · exact ⟨Sum.inr (Sum.inr ⟨2 * ρ - 1 - j.val, by omega⟩), congrArg Sum.inr (Fin.ext (by simp only [Sum.elim_inr]; omega))⟩
  · rintro r (a | i | i)
    · exact (h0 r a).trans (one_mul _).symm
    · exact hX i _ rfl r
    · exact hY i _ (by simp only [Sum.elim_inr]; omega) r
  · rintro (a | i | i)
    · rfl
    · simp [wlev]
    · simp only [wlev, Sum.map_inr, Sum.elim_inr]
      rw [if_neg (by omega)]
      omega
  · rintro (a | i) (b | j) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> (try split_ifs) <;> omega

theorem flagFrame_bes (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c))
    (hF : p.IsBesFrame B s FA F) : FlagFrame p B.d F (lev (ρ + 1)) := by
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  obtain ⟨F₀, h₀⟩ := Witness.exists_core p B one_ne_zero FA
  refine flagFrame p B.d F₀ F
    (Sum.elim (Sum.map id fun _ => (⟨ρ, by omega⟩ : Fin (2 * ρ + 1)))
      (Sum.elim (fun i : Fin ρ => Sum.inr (⟨i.val, by omega⟩ : Fin (2 * ρ + 1)))
        fun i : Fin ρ => Sum.inr ⟨2 * ρ - i.val, by omega⟩)) ?_
    (Sum.elim (Sum.elim (fun _ => 1) fun _ => s)
      (Sum.elim (fun i => s * p.xi ^ (ρ - i.val)) fun i => s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val))) ?_
    (lev (ρ + 1)) _ ?_ fun _ _ => Iff.rfl
  · rintro (a | j)
    · exact ⟨Sum.inl (Sum.inl a), rfl⟩
    · rcases lt_trichotomy j.val ρ with h | h | h
      · exact ⟨Sum.inr (Sum.inl ⟨j.val, h⟩), rfl⟩
      · exact ⟨Sum.inl (Sum.inr ()), congrArg Sum.inr (Fin.ext h.symm)⟩
      · exact ⟨Sum.inr (Sum.inr ⟨2 * ρ - j.val, by omega⟩), congrArg Sum.inr (Fin.ext (by simp only; omega))⟩
  · rintro r ((a | ⟨⟩) | i | i)
    · refine (h0 r a).trans (Eq.trans ?_ (one_mul _).symm)
      change ((B.d.i₀ * B.o.iA).map (Witness.prH p) * FA.β) r a = (B.d.i₀.map (Witness.prH p) * F₀.β) r (Sum.inl a)
      rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun u _ => by rw [h₀.1]; rfl
    · refine (hz _ rfl r).trans (congrArg (s * ·) ?_)
      change Witness.prH p (∑ u, B.d.i₀ r u * vecB B.o B.ζ u) = (B.d.i₀.map (Witness.prH p) * F₀.β) r (Sum.inr ())
      rw [Matrix.mul_apply, map_sum]
      exact Finset.sum_congr rfl fun u _ => by rw [h₀.2, one_mul, RingHom.map_mul]; rfl
    · exact hX i _ rfl r
    · exact hY i _ (by simp only; omega) r
  · rintro ((a | ⟨⟩) | i | i) <;> rfl

theorem fourierJacobiFrame_localMatrix_embedding (J : JacLev D ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c))
    (hF : p.IsJacFrame J s hh F₀ F) (h : GA D J.W₀) :
    (mt J.W (J.d.emb0 h)).map p.π = F.β * (embX c (coordHom J.W₀ p.π F₀.β F₀.γ F₀.βγ F₀.γβ h)).val * F.γ := by
  obtain ⟨rfl, h0, hX, hY⟩ := hF
  refine eq_embX F _ _ (J.d.j0.map p.π * F₀.β) h0 (intertwine' p (J.d.wittDecomp_anisotropicEmbedding_inclAnisotropic h) F₀) fun j => ?_
  by_cases hj : j.val < ρ
  · exact fix_col (map_fix p (J.d.wittDecomp_anisotropicEmbedding_inclX h)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · exact fix_col (map_fix p (J.d.wittDecomp_anisotropicEmbedding_inclY h)) _ ⟨2 * ρ - 1 - j.val, by omega⟩ (hY _ j (by simp only; omega))

theorem coord_embA (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c))
    (hF : p.IsBesFrame B s FA F) (h : GA D B.A) :
    (mt B.V (embA B.d B.o h)).map p.π = F.β * (embX c (coordHom B.A p.π FA.β FA.γ FA.βγ FA.γβ h)).val * F.γ := by
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  have eA : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ mt B.A h := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]
  have eB : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA) := (rat_mul _ _).symm
  have rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB) := (rat_mul _ _).symm
  rw [rA] at eA
  rw [rB] at eB
  rw [embA_apply]
  refine eq_embX F _ _ ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 (intertwine' p eA FA) fun j => ?_
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · exact fix_col (map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · refine fix_vec (map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r => (hz j hj r).trans (congrArg (s * ·) ?_)
    rw [vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec (Witness.prH p) _ _ r
  · exact fix_col (map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩ (hY _ j (by simp only; omega))

theorem coord_mem_RFJ (J : JacLev D ρ) (hρ : 1 ≤ ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c))
    (hF : p.IsJacFrame J s hh F₀ F) {x : GA D J.W} (hx : x ∈ jacGrp J.d) :
    coordHom J.W p.π F.β F.γ F.βγ F.γβ x ∈ RFJ k n c ρ := by
  have hle : jacGrp J.d ≤ (RFJ k n c ρ).comap (coordHom J.W p.π F.β F.γ F.βγ F.γβ) := by
    refine sup_le (fun g hg => ?_) ?_
    · exact ((ParabolicEntries.mem_R_iff_and_mem_RFJ_iff k n c ρ).2 hρ (by have := hF.1; omega) _).2
        fun r s' _ hrs => (flagFrame_jac p J s hh F₀ F hF).2 g hg r s' hrs
    · rintro _ ⟨h, rfl⟩
      rw [Subgroup.mem_comap, ← (eq_coordHom_iff _ _ _ _ _ _ _ _).1 (fourierJacobiFrame_localMatrix_embedding p J s hh F₀ F hF h)]
      exact Subgroup.mem_sup_left (ParabolicEntries.embX_mem_R ρ _)
  exact hle hx

theorem coord_mem_R (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c))
    (hF : p.IsBesFrame B s FA F) {x : GA D B.V} (hx : x ∈ besGrp B.d B.o) :
    coordHom B.V p.π F.β F.γ F.βγ F.γβ x ∈ R k n c (ρ + 1) := by
  have hle : besGrp B.d B.o ≤ (R k n c (ρ + 1)).comap (coordHom B.V p.π F.β F.γ F.βγ F.γβ) := by
    refine sup_le (fun g hg => ?_) ?_
    · exact ((ParabolicEntries.mem_R_iff_and_mem_RFJ_iff k n c (ρ + 1)).1 _).2
        fun r s' _ hrs => (flagFrame_bes p B s FA F hF).2 g hg r s' hrs
    · rintro _ ⟨h, rfl⟩
      rw [Subgroup.mem_comap, ← (eq_coordHom_iff _ _ _ _ _ _ _ _).1 (coord_embA p B s FA F hF h)]
      exact ParabolicEntries.embX_mem_R _ _
  exact hle hx

theorem mem_jacGrp_of_RFJ (J : JacLev D ρ) (hρ : 1 ≤ ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n)
    (F : Frame k J.W.rank (n ⊕ Fin c)) (hF : p.IsJacFrame J s hh F₀ F) (gl : GL (n ⊕ Fin c) k →* GA D J.W)
    (hgl : ∀ g, p.IsLoc F (gl g) g) {g : GL (n ⊕ Fin c) k} (hg : g ∈ RFJ k n c ρ) : gl g ∈ jacGrp J.d := by
  have hp := ((ParabolicEntries.mem_R_iff_and_mem_RFJ_iff k n c ρ).2 hρ (by have := hF.1; omega) _).1 hg
  obtain ⟨x, u, hu, rfl⟩ :=
    ParabolicEntries.exists_eq_embX_mul (L := 2 * ρ + 1) (b := fun i : Fin c => 2 * (i.val + 1)) hp
  rw [map_mul]
  refine mul_mem ?_ (Subgroup.mem_sup_left ((flagFrame_jac p J s hh F₀ F hF).1 _ u (hgl u) hu))
  obtain ⟨h, hh'⟩ := Witness.exists_isLoc p F₀ x
  have e := fourierJacobiFrame_localMatrix_embedding p J s hh F₀ F hF h
  rw [← (eq_coordHom_iff _ _ _ _ F₀.βγ F₀.γβ _ _).1 hh'.2] at e
  rw [isLoc_unique p (hgl _) ⟨suppAt_wittLeviEmbedding J.d hh'.1, e⟩]
  exact Subgroup.mem_sup_right ⟨h, rfl⟩

theorem coord_mul_off (q : GlobalTheory.FinPl.SplitPt D k) {S : HSp D} (F : Frame k S.rank Y) {x y : GA D S} {g : GL Y k}
    (hx : (ofSplit q).IsLoc F x g) (hy : y ∈ GlobalTheory.FinPl.grpOff S (· = q.v)) :
    coordHom S (ofSplit q).π F.β F.γ F.βγ F.γβ (x * y) = g := by
  refine ((eq_coordHom_iff _ _ _ _ _ _ _ _).1 ?_).symm
  have e : (mt S y).map (ofSplit q).π = 1 := GlobalTheory.FrameMoves.map_pr_of_grpOff q S hy
  rw [GlobalTheory.MixModel.mt_mul, Matrix.map_mul, e, Matrix.mul_one, hx.2]

end GlobalTheory.LocGrpIff

theorem GlobalTheory.LocGrpIff.local_groups_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), (∀ (J : JacLev D ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c)) (gl : GL (n ⊕ Fin c) k →* GA D J.W), 1 ≤ ρ → s ≠ 0 → hh ≠ 0 → (ofSplit q).IsJacFrame J s hh F₀ F → (∀ g, (ofSplit q).IsLoc F (gl g) g) → (∀ g, gl g ∈ jacGrp J.d ↔ g ∈ RFJ k n c ρ) ∧ ∀ g, ∀ y ∈ GlobalTheory.FinPl.grpOff J.W (· = q.v), gl g * y ∈ jacGrp J.d → gl g ∈ jacGrp J.d) ∧ ∀ (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)) (gl : GL (n ⊕ Fin c) k →* GA D B.V), s ≠ 0 → (ofSplit q).IsBesFrame B s FA F → (∀ g, (ofSplit q).IsLoc F (gl g) g) → (∀ g, gl g ∈ besGrp B.d B.o ↔ g ∈ R k n c (ρ + 1)) ∧ ∀ g, ∀ y ∈ GlobalTheory.FinPl.grpOff B.V (· = q.v), gl g * y ∈ besGrp B.d B.o → gl g ∈ besGrp B.d B.o := by
  intro D k _ _ _ _ q n _ _ c ρ
  refine ⟨fun J s hh F₀ F gl hρ _ _ hF hgl => ?_, fun B s FA F gl _ hF hgl => ?_⟩
  · have key : ∀ g, ∀ y ∈ GlobalTheory.FinPl.grpOff J.W (· = q.v), gl g * y ∈ jacGrp J.d → g ∈ RFJ k n c ρ := fun g y hy h => by
      have := GlobalTheory.LocGrpIff.coord_mem_RFJ (ofSplit q) J hρ s hh F₀ F hF h
      rwa [GlobalTheory.LocGrpIff.coord_mul_off q F (hgl g) hy] at this
    have back := fun g => GlobalTheory.LocGrpIff.mem_jacGrp_of_RFJ (ofSplit q) J hρ s hh F₀ F hF gl hgl (g := g)
    exact ⟨fun g => ⟨fun h => key g 1 (one_mem _) (by rwa [mul_one]), back g⟩, fun g y hy h => back g (key g y hy h)⟩
  · have key : ∀ g, ∀ y ∈ GlobalTheory.FinPl.grpOff B.V (· = q.v), gl g * y ∈ besGrp B.d B.o → g ∈ R k n c (ρ + 1) :=
      fun g y hy h => by
        have := GlobalTheory.LocGrpIff.coord_mem_R (ofSplit q) B s FA F hF h
        rwa [GlobalTheory.LocGrpIff.coord_mul_off q F (hgl g) hy] at this
    have back := fun g hg => GlobalTheory.LocGrp.mem_besGrp (ofSplit q) B s FA F hF (gl g) g hg (hgl g)
    exact ⟨fun g => ⟨fun h => key g 1 (one_mem _) (by rwa [mul_one]), back g⟩, fun g y hy h => back g (key g y hy h)⟩

end

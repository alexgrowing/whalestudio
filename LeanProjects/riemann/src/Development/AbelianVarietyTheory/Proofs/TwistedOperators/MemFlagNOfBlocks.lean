import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseUnipotentVolumeConjDiagonalEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiUnipotentEqProdRootExchange
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacesPartMovedLevelKeepsStandardHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalOfBesselNormalFrameLocal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.PrLevel
open GlobalTheory.RootEx GlobalTheory.SplitWeil GlobalTheory.SplitFlip ValuativeRel

section Loc
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def symStep (n : Type) (c : ℕ) : n ⊕ Fin c → ℕ :=
  if Even c then Sum.elim (fun _ => 2 * (c / 2) + 1) (fun i : Fin c => 2 * (i.val + 1)) else RootEx.lev (c / 2 + 1)

theorem mem_symN_iff (hc : 1 ≤ c) (g : GL (n ⊕ Fin c) k) : g ∈ symN k n c ↔
    ∀ r s, symStep n c s ≤ symStep n c r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := by
  unfold symStep
  split_ifs with h
  · obtain ⟨ρ, rfl⟩ := h
    have e1 : (ρ + ρ) / 2 = ρ := by omega
    have e2 : (ρ + ρ + 1) / 2 = ρ := by omega
    rw [symN, e1, e2]
    exact (GlobalTheory.RootEx.FJUnipotent.fj_unipotent k n (ρ + ρ) ρ (by omega) (by omega)).2.1 g
  · obtain ⟨ρ, rfl⟩ := Nat.not_even_iff_odd.1 h
    rw [symN_odd, show (2 * ρ + 1) / 2 = ρ by omega]
    exact Model.mem_N_iff

theorem symN_block (hc : 1 ≤ c) {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) (a b : n) :
    u.val (.inl a) (.inl b) = (1 : Matrix n n k) a b := by
  rw [(mem_symN_iff hc u).1 hu (.inl a) (.inl b) (by unfold symStep; split_ifs <;> exact le_rfl)]
  simp [Matrix.one_apply]

theorem diag_props {y : GL (n ⊕ Fin c) k} {f : n ⊕ Fin c → k} (hy : y.val = diagonal f) (hf : ∀ a, f (.inl a) = 1) :
    (∀ u ∈ symN k n c, y⁻¹ * u * y ∈ symN k n c) ∧ (∀ u ∈ symN k n c, y * u * y⁻¹ ∈ symN k n c) ∧
      ∀ g, y * embX c g = embX c g * y := by
  have h0 : ∀ r, f r ≠ 0 := fun r h => by
    have := congrFun (congrFun y.mul_inv r) r
    rw [hy, diagonal_mul, h, zero_mul, one_apply_eq] at this
    exact zero_ne_one this
  have e : y = diagGL fun r => Units.mk0 (f r) (h0 r) := Units.ext hy
  refine ⟨fun u hu => ?_, fun u hu => ?_, fun g => Units.ext ?_⟩
  · have e' : y⁻¹ = diagGL fun r => (Units.mk0 (f r) (h0 r))⁻¹ := by rw [e]; exact Units.ext rfl
    have := GlobalTheory.DiagVol.conj_diag_mem (fun r => (Units.mk0 (f r) (h0 r))⁻¹) hu
    rwa [← e', inv_inv] at this
  · rw [e]; exact GlobalTheory.DiagVol.conj_diag_mem _ hu
  · rw [Units.val_mul, Units.val_mul, hy]
    change _ * fromBlocks g.val 0 0 1 = fromBlocks g.val 0 0 1 * _
    ext r s
    rw [diagonal_mul, mul_diagonal]
    rcases r with r | r <;> rcases s with s | s
    · simp [hf]
    · simp
    · simp
    · by_cases h : r = s
      · subst h; simp
      · simp [one_apply_ne h]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem KO_of_mul (hc : 1 ≤ c) {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) {g : GL n k}
    (h : u * embX c g ∈ KO k (n ⊕ Fin c)) : g ∈ KO k n := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff _).1 h
  refine (mem_KO_iff _).2 ⟨fun a b => ?_, fun a b => ?_⟩
  · convert h1 (.inl a) (.inl b) using 1
    change _ = (u.val * (fromBlocks g.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) _ _
    simp [Matrix.mul_apply, symN_block hc hu, Matrix.one_apply]
  · convert h2 (.inl a) (.inl b) using 1
    rw [_root_.mul_inv_rev, ← map_inv]
    change _ = ((fromBlocks (g⁻¹).val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * (u⁻¹).val : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) _ _
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, symN_block hc (inv_mem hu)]
    simp [Matrix.one_apply]

theorem embX_KO {g : GL n k} (h : g ∈ KO k n) : embX c g ∈ KO k (n ⊕ Fin c) := by
  have key : ∀ z : GL n k, (∀ i j, z.val i j ∈ 𝒪[k]) → ∀ r s, (embX c z).val r s ∈ 𝒪[k] := fun z H r s => by
    change fromBlocks z.val 0 0 1 r s ∈ _
    rcases r with r | r <;> rcases s with s | s
    · exact H r s
    · exact zero_mem _
    · exact zero_mem _
    · rw [fromBlocks_apply₂₂, one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
  obtain ⟨h1, h2⟩ := (mem_KO_iff _).1 h
  exact (mem_KO_iff _).2 ⟨key _ h1, by rw [← map_inv]; exact key _ h2⟩

theorem frameGL_KO {a b : ℕ} (h : a + c = b) (x : GL (Fin b) k) : frameGL h x ∈ KO k (Fin a ⊕ Fin c) ↔ x ∈ KO k (Fin b) := by
  rw [mem_KO_iff, mem_KO_iff, ← map_inv]
  exact and_congr ((frame h).forall_congr fun _ => (frame h).forall_congr fun _ => Iff.rfl)
    ((frame h).forall_congr fun _ => (frame h).forall_congr fun _ => Iff.rfl)

end Loc
end GlobalTheory.PrLevel

namespace GlobalTheory.PrLevel
open GlobalTheory.RootEx GlobalTheory.RowRep GlobalTheory.LocGrp GlobalTheory.LocGrpIff

variable {D : D7}

theorem ae_zero {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {z : AE D} (h : (e + cA D e) * z = z)
    (h1 : ∀ w ∈ P, piAt w z = 0) (h2 : ∀ w ∈ P, piAt w (cA D z) = 0) : z = 0 := by
  obtain ⟨e0, -, e2⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  have key : ∀ x : AE D, (∀ w ∈ P, piAt w x = 0) → e * x = 0 := fun x hx =>
    ae_ext (by rw [RingHom.map_mul, e0, zero_mul, RingHom.map_zero]) fun w => by
      change piAt w (e * x) = piAt w 0
      rw [RingHom.map_mul, RingHom.map_zero]
      by_cases hw : w ∈ P
      · rw [hx w hw, mul_zero]
      · rw [show piAt w e = 0 from e2 w hw, zero_mul]
  have e3 : cA D e * z = 0 := by
    have := congrArg (cA D) (key _ h2)
    rwa [RingHom.map_mul, cA_cA, RingHom.map_zero] at this
  rw [← h, add_mul, key _ h1, e3, add_zero]

theorem entry_zero {e : AE D} {Q : Finset (Pl D.host.E)} (he : IsIdemSum e Q) {V : HSp D} {g : GA D V} (hg : SuppAt e V g) {l m : ℕ}
    (P : Mx D l V.rank) (J : Mx D V.rank m) (i j) (h1 : ∀ w ∈ Q, piAt w ((P ⬝ (mt V g - 1) ⬝ J) i j) = 0)
    (h2 : ∀ w ∈ Q, piAt w (((adj J ⬝ gA V) ⬝ (mt V g⁻¹ - 1) ⬝ (giA V ⬝ adj P)) j i) = 0) : (P ⬝ (mt V g - 1) ⬝ J) i j = 0 := by
  have e1 : (e + cA D e) • (mt V g - 1) = mt V g - 1 := Matrix.ext hg
  have e2 : (e + cA D e) * (P ⬝ (mt V g - 1) ⬝ J) i j = (P ⬝ (mt V g - 1) ⬝ J) i j := by
    conv_rhs => rw [← e1, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  have e3 : (adj J ⬝ gA V) ⬝ (mt V g⁻¹ - 1) ⬝ (giA V ⬝ adj P) = adj (P ⬝ (mt V g - 1) ⬝ J) := by
    simp only [GlobalTheory.MixModel.mt_inv, adj_mul, adj_sub, adj_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, gA_giA_cancel,
      Matrix.one_mul]
  rw [e3] at h2
  exact ae_zero he e2 h1 h2

section Witt
variable {K : Type} [Field K] (π : AE D →+* K) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

def Blocks (M : Mx D S.rank S.rank) : Prop :=
  (∀ i j, j ≤ i → π ((d.pX ⬝ M ⬝ d.jX) i j) = 0) ∧ (d.p0 ⬝ M ⬝ d.jX).map π = 0 ∧ (d.pY ⬝ M ⬝ d.jX).map π = 0 ∧
    (d.p0 ⬝ M ⬝ d.j0).map π = 0 ∧ (d.pY ⬝ M ⬝ d.j0).map π = 0 ∧ ∀ i j, i ≤ j → π ((d.pY ⬝ M ⬝ d.jY) i j) = 0

def Adapted {Y : Type} (F : Matrix (Fin S.rank) Y K) (l : Y → ℕ) : Prop :=
  ∃ (Y₀ : Type) (_ : Fintype Y₀) (_ : DecidableEq Y₀) (b : Matrix (Fin S₀.rank) Y₀ K) (b' : Matrix Y₀ (Fin S₀.rank) K)
    (τ : Y₀ ⊕ (Fin ρ ⊕ Fin ρ) → Y) (t : Y₀ ⊕ (Fin ρ ⊕ Fin ρ) → K), b' * b = 1 ∧ b * b' = 1 ∧ Function.Surjective τ ∧
    (∀ r z, F r (τ z) = t z * wCols π d b r z) ∧ ∀ z z', l (τ z') ≤ l (τ z) ↔ wlev Y₀ ρ z' ≤ wlev Y₀ ρ z

variable {π d} {Y : Type} [Fintype Y] [DecidableEq Y] {F : Matrix (Fin S.rank) Y K} {Γ : Matrix Y (Fin S.rank) K} {l : Y → ℕ}

theorem Adapted.uni (h : Adapted π d F l) (h1 : Γ * F = 1) (h2 : F * Γ = 1) {g : GA D S} (hg : g ∈ flagN d) (r s : Y)
    (hrs : l s ≤ l r) : (Γ * ((mt S g).map π * F)) r s = (1 : Matrix Y Y K) r s := by
  obtain ⟨Y₀, _, _, b, b', τ, t, hb, -, hτ, ht, hl⟩ := h
  exact uni_flag π d b b' hb h1 h2 τ hτ t ht l (fun z z' => (hl z z').1) hg r s hrs

theorem Adapted.blocks (h : Adapted π d F l) (h1 : Γ * F = 1) (h2 : F * Γ = 1) {M : Mx D S.rank S.rank}
    (hM : ∀ r s, l s ≤ l r → (Γ * (M.map π * F)) r s = (1 : Matrix Y Y K) r s) : Blocks π d (M - 1) := by
  obtain ⟨Y₀, _, _, b, b', τ, t, hb, hb', hτ, ht, hl⟩ := h
  have e : (M - 1).map π = F * (Γ * (M.map π * F) - 1) * Γ := by
    rw [Matrix.map_sub _ (map_sub π), Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h2,
      ← Matrix.mul_assoc F, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  have W : ∀ z z', wlev Y₀ ρ z' ≤ wlev Y₀ ρ z → (wRows π d b' * (M - 1).map π * wCols π d b) z z' = 0 := fun z z' hz => by
    rw [e]
    exact transfer h1 (wRows_wCols π d b b' hb) τ hτ t ht _ z z' (by rw [Matrix.sub_apply, hM _ _ ((hl _ _).2 hz), sub_self])
  generalize M - 1 = N at W
  have row : ∀ {m : Type} {C : Matrix (Fin S.rank) m K}, b' * d.p0.map π * N.map π * C = 0 → d.p0.map π * N.map π * C = 0 :=
    fun h => by
      have h' := congrArg (b * ·) h
      simpa only [← Matrix.mul_assoc, hb', Matrix.one_mul, Matrix.mul_zero] using h'
  have col : ∀ {m : Type} {C : Matrix m (Fin S.rank) K}, C * N.map π * (d.j0.map π * b) = 0 → C * N.map π * d.j0.map π = 0 :=
    fun h => by
      have h' := congrArg (· * b') h
      simpa only [Matrix.mul_assoc, hb', Matrix.mul_one, Matrix.zero_mul] using h'
  refine ⟨fun i j hij => ?_, ?_, ?_, ?_, ?_, fun i j hij => ?_⟩
  · rw [← Matrix.map_apply (f := π), Matrix.map_mul, Matrix.map_mul]
    exact W (.inr (.inl i)) (.inr (.inl j)) (by simp only [wlev, Sum.elim_inr, Sum.elim_inl]; omega)
  · rw [Matrix.map_mul, Matrix.map_mul]
    exact row (Matrix.ext fun i j => W (.inl i) (.inr (.inl j)) (by simp only [wlev, Sum.elim_inr, Sum.elim_inl]; omega))
  · rw [Matrix.map_mul, Matrix.map_mul]
    exact Matrix.ext fun i j => W (.inr (.inr i)) (.inr (.inl j)) (by simp only [wlev, Sum.elim_inr, Sum.elim_inl]; omega)
  · rw [Matrix.map_mul, Matrix.map_mul]
    exact row (col (Matrix.ext fun i j => W (.inl i) (.inl j) le_rfl))
  · rw [Matrix.map_mul, Matrix.map_mul]
    exact col (Matrix.ext fun i j => W (.inr (.inr i)) (.inl j) (by simp only [wlev, Sum.elim_inr, Sum.elim_inl]; omega))
  · rw [← Matrix.map_apply (f := π), Matrix.map_mul, Matrix.map_mul]
    exact W (.inr (.inr i)) (.inr (.inr j)) (by simp only [wlev, Sum.elim_inr, Sum.elim_inl]; omega)

end Witt

theorem mem_flagN_of_blocks {e : AE D} {Q : Finset (Pl D.host.E)} (he : IsIdemSum e Q) {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ)
    {g : GA D V} (hS : SuppAt e V g) (h : ∀ w ∈ Q, Blocks (piAt w) d (mt V g - 1))
    (h' : ∀ w ∈ Q, Blocks (piAt w) d (mt V g⁻¹ - 1)) : g ∈ flagN d := by
  have aX : giA V ⬝ adj d.pX = d.jY := by rw [d.pX_eq, adj_mul, adj_adj, adj_gA, giA_gA_cancel]
  have aY : giA V ⬝ adj d.pY = d.jX := by rw [d.pY_eq, adj_mul, adj_adj, adj_gA, giA_gA_cancel]
  have a0 : giA V ⬝ adj d.p0 = d.j0 ⬝ giA V₀ := by
    rw [d.p0_eq, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_gA_cancel]
  have b0 : adj d.j0 ⬝ gA V = gA V₀ ⬝ d.p0 := by rw [d.p0_eq, gA_giA_cancel]
  have ev : ∀ {w : Pl D.host.E} {l m : ℕ} {x : Mx D l m}, x.map (piAt w) = 0 → ∀ i j, piAt w (x i j) = 0 :=
    fun h i j => congrFun (congrFun h i) j
  refine GlobalTheory.LocFlag.mem_of_blocks d g (fun i j hij => entry_zero he hS _ _ i j (fun w hw => (h w hw).1 i j hij) fun w hw => ?_)
    (Matrix.ext fun i j => entry_zero he hS _ _ i j (fun w hw => ev (h w hw).2.1 i j) fun w hw => ?_)
    (Matrix.ext fun i j => entry_zero he hS _ _ i j (fun w hw => ev (h w hw).2.2.1 i j) fun w hw => ?_)
    (Matrix.ext fun i j => entry_zero he hS _ _ i j (fun w hw => ev (h w hw).2.2.2.1 i j) fun w hw => ?_)
    (Matrix.ext fun i j => entry_zero he hS _ _ i j (fun w hw => ev (h w hw).2.2.2.2.1 i j) fun w hw => ?_)
  all_goals obtain ⟨-, OX', YX', OO', YO', YY'⟩ := h' w hw
  · rw [aX, ← d.pY_eq]
    exact YY' j i hij
  · refine ev ?_ j i
    rw [a0, ← d.pY_eq, ← Matrix.mul_assoc, Matrix.map_mul, YO', Matrix.zero_mul]
  · rw [aY, ← d.pY_eq]
    exact ev YX' j i
  · refine ev ?_ j i
    rw [a0, b0, ← Matrix.mul_assoc, Matrix.mul_assoc (gA _), Matrix.mul_assoc (gA _),
      Matrix.map_mul, Matrix.map_mul, OO', Matrix.mul_zero, Matrix.zero_mul]
  · refine ev ?_ j i
    rw [aY, b0, Matrix.mul_assoc (gA _), Matrix.mul_assoc (gA _), Matrix.map_mul, OX', Matrix.mul_zero]

end GlobalTheory.PrLevel

namespace GlobalTheory.PrLevel
open GlobalTheory.RootEx GlobalTheory.RowRep GlobalTheory.LocGrp GlobalTheory.LocGrpIff

variable {D : D7}

def Shape {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (N : Subgroup (GA D B)) (em : GA D A →* GA D B) : Prop :=
  (∃ (S₀ : HSp D) (ρ : ℕ) (h : HypDec B S₀ ρ), N = flagN h ∧ ∀ (K : Type) [Field K] (π : AE D →+* K)
    (b b' : Matrix (Fin A.rank) (Fin A.rank) K) (u : Fin c → K), b * b' = 1 → Adapted π h (sumCols d π b u) (symStep _ c)) ∧
  (∀ (K : Type) [Field K] (π : AE D →+* K) (x : GA D A),
    (mt B (em x)).map π * (frameMat B A d.ι).map (π.comp (incA D)) = (frameMat B A d.ι).map (π.comp (incA D)) * (mt A x).map π ∧
    ∀ p, (mt B (em x)).map π *ᵥ (fun r => π (incA D (d.a r p))) = fun r => π (incA D (d.a r p))) ∧
  ∀ x ∈ GfC A, em x ∈ GfC B

theorem shape_jac {A B : HSp D} {c σ : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ) :
    Shape d (flagN (jacDec d h)) (jacDec d h).emb0 := by
  subst h
  have hσ : σ ≤ 2 * σ := by omega
  refine ⟨⟨_, _, _, rfl, fun K _ π b b' u hb => ⟨Fin A.rank, inferInstance, inferInstance, b, b',
      (Sum.map id (Sum.elim (fun i : Fin σ => Fin.castLE hσ i) fun i : Fin σ => (Fin.castLE hσ i).rev)),
      (Sum.elim (fun _ => 1) (Sum.elim (fun i => u (Fin.castLE hσ i)) fun i => u (Fin.castLE hσ i).rev)),
      mul_eq_one_comm.1 hb, hb, ?_, ?_, ?_⟩⟩, fun K _ π x => ⟨?_, fun p => ?_⟩,
    fun x hx => GlobalTheory.Core.Mi.CenAct.witt_embedding_mem_finite_unitary_points _ hx⟩
  · rintro (a | j)
    · exact ⟨Sum.inl a, rfl⟩
    · by_cases h : j.val < σ
      · exact ⟨Sum.inr (Sum.inl ⟨j.val, h⟩), rfl⟩
      · exact ⟨Sum.inr (Sum.inr ⟨2 * σ - 1 - j.val, by omega⟩), congrArg Sum.inr (Fin.ext (by
          simp only [Sum.elim_inr, Fin.val_rev, Fin.val_castLE]; omega))⟩
  · rintro r (a | i | i)
    · exact (one_mul _).symm
    · exact (mul_diagonal u _ _ _).trans (mul_comm _ _)
    · exact (mul_diagonal u _ _ _).trans (mul_comm _ _)
  · rw [symStep, if_pos (even_two_mul σ), show 2 * σ / 2 = σ by omega]
    rintro (a | i | i) (a' | j | j) <;>
      simp only [wlev, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, Fin.val_rev, Fin.val_castLE] <;> omega
  · exact (Matrix.map_mul (f := π)).symm.trans ((congrArg (·.map π) ((jacDec d rfl).wittDecomp_anisotropicEmbedding_inclAnisotropic x)).trans Matrix.map_mul)
  · have eX := (Matrix.map_mul (f := π)).symm.trans (congrArg (·.map π) ((jacDec d rfl).wittDecomp_anisotropicEmbedding_inclX x))
    have eY := (Matrix.map_mul (f := π)).symm.trans (congrArg (·.map π) ((jacDec d rfl).wittDecomp_anisotropicEmbedding_inclY x))
    by_cases h : p.val < σ
    · exact fix_col eX 1 ⟨p.val, h⟩ fun r => (one_mul _).symm
    · obtain ⟨q, rfl⟩ : ∃ q : Fin σ, p = (Fin.castLE hσ q).rev :=
        ⟨⟨2 * σ - 1 - p.1, by omega⟩, Fin.ext (by simp only [Fin.val_rev, Fin.val_castLE]; omega)⟩
      exact fix_col eY 1 q fun r => (one_mul _).symm

theorem shape_bes {A B : HSp D} {c σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (hc : c = 2 * σ + 1) (l : Fin σ → D.host.E) (hl : ∀ a, l a ≠ 0) :
    Shape d (flagN (diagDec (besDec d hc) l hl))
      (GlobalTheory.MixPer.embA (diagDec (besDec d hc) l hl) (GlobalTheory.OrthSumExists.orthDecHsum D _ _)) := by
  subst hc
  have hσ : σ ≤ 2 * σ + 1 := by omega
  have hσ' : σ < 2 * σ + 1 := by omega
  let E : Fin A.rank ⊕ Fin 1 ≃ Fin (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)).rank := finSumFinEquiv
  have vX : ∀ {K : Type} [Field K] (π : AE D →+* K) r (i : Fin σ), π.comp (incA D) (d.a r (Fin.castLE hσ i)) =
      π.comp (incA D) (l i)⁻¹ * ((diagDec (besDec d rfl) l hl).jX.map π) r i := fun π r i => by
    change _ = _ * π.comp (incA D) (((besDec d rfl).e * diagonal l) r i)
    rw [mul_diagonal, ← map_mul, mul_left_comm, inv_mul_cancel₀ (hl i), mul_one]; rfl
  have vY : ∀ {K : Type} [Field K] (π : AE D →+* K) r (i : Fin σ), π.comp (incA D) (d.a r (Fin.castLE hσ i).rev) =
      π.comp (incA D) (star (l i)) * ((diagDec (besDec d rfl) l hl).jY.map π) r i := fun π r i => by
    change _ = _ * π.comp (incA D) (((besDec d rfl).e' * diagonal fun a => (star (l a))⁻¹) r i)
    rw [mul_diagonal, ← map_mul, mul_left_comm, mul_inv_cancel₀ (star_ne_zero.2 (hl i)), mul_one]; rfl
  have core : ∀ {K : Type} [Field K] (π : AE D →+* K) {Z : Type} (X : Matrix (Fin A.rank ⊕ Fin 1) Z K),
      (diagDec (besDec d rfl) l hl).j0.map π * X.submatrix E.symm id =
        fromCols ((frameMat B A d.ι).map (π.comp (incA D))) ((midCol d rfl).map (π.comp (incA D))) * X := fun π _ X => by
    have e : (diagDec (besDec d rfl) l hl).j0.map π =
        (fromCols ((frameMat B A d.ι).map (π.comp (incA D))) ((midCol d rfl).map (π.comp (incA D)))).submatrix id E.symm := by
      rw [← fromCols_map]; rfl
    exact (congrArg (· * X.submatrix E.symm id) e).trans (submatrix_mul_equiv _ _ _ E.symm _)
  refine ⟨⟨_, _, _, rfl, fun K _ π b b' u hb => ⟨Fin A.rank ⊕ Fin 1, inferInstance, inferInstance,
      (fromBlocks b 0 0 (1 : Matrix (Fin 1) (Fin 1) K)).submatrix E.symm id,
      (fromBlocks b' 0 0 (1 : Matrix (Fin 1) (Fin 1) K)).submatrix id E.symm,
      (Sum.elim (Sum.map id fun _ => ⟨σ, by omega⟩)
        (Sum.elim (fun i : Fin σ => Sum.inr (Fin.castLE hσ i)) fun i : Fin σ => Sum.inr (Fin.castLE hσ i).rev)),
      (Sum.elim (Sum.elim (fun _ => 1) fun _ => u ⟨σ, by omega⟩)
        (Sum.elim (fun i => u (Fin.castLE hσ i) * π.comp (incA D) (l i)⁻¹)
          fun i => u (Fin.castLE hσ i).rev * π.comp (incA D) (star (l i)))), ?_, ?_, ?_, ?_, ?_⟩⟩, fun K _ π x => ?_,
    fun x hx => GlobalTheory.Core.Mi.CenAct.embA_mem_GfC _ _ hx⟩
  · refine (submatrix_mul_equiv _ _ _ E.symm _).trans ?_
    rw [fromBlocks_multiply]
    simp [mul_eq_one_comm.1 hb]
  · refine (submatrix_mul_equiv _ _ _ (Equiv.refl _) _).trans ?_
    rw [fromBlocks_multiply]
    simp [hb]
  · rintro (a | j)
    · exact ⟨Sum.inl (Sum.inl a), rfl⟩
    · rcases lt_trichotomy j.val σ with h | h | h
      · exact ⟨Sum.inr (Sum.inl ⟨j.val, h⟩), rfl⟩
      · exact ⟨Sum.inl (Sum.inr 0), congrArg Sum.inr (Fin.ext h.symm)⟩
      · exact ⟨Sum.inr (Sum.inr ⟨2 * σ - j.val, by omega⟩), congrArg Sum.inr (Fin.ext (by
          simp only [Fin.val_rev, Fin.val_castLE]; omega))⟩
  · have e := core π (fromBlocks b 0 0 (1 : Matrix (Fin 1) (Fin 1) K))
    rw [fromCols_mul_fromBlocks, Matrix.mul_zero, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one] at e
    rintro r ((a | a) | i | i)
    · exact (congrFun (congrFun e r) (Sum.inl a)).symm.trans (one_mul _).symm
    · exact (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans (congrArg (u _ * ·) (congrFun (congrFun e r) (Sum.inr a)).symm))
    · exact (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans ((congrArg (u _ * ·) (vX π r i)).trans (mul_assoc _ _ _).symm))
    · exact (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans ((congrArg (u _ * ·) (vY π r i)).trans (mul_assoc _ _ _).symm))
  · rw [symStep, if_neg (Nat.not_even_iff_odd.2 (odd_two_mul_add_one σ)), show (2 * σ + 1) / 2 = σ by omega]
    rintro ((a | a) | i | i) ((a' | a') | j | j) <;>
      simp only [wlev, RootEx.lev, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, Fin.val_rev, Fin.val_castLE] <;> omega
  · rw [embA_apply]
    set h := diagDec (besDec d rfl) l hl
    set o := GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)
    let φ : D.host.E →+* K := π.comp (incA D)
    have eX := (Matrix.map_mul (f := π)).symm.trans (congrArg (·.map π) (h.wittDecomp_anisotropicEmbedding_inclX (o.emb (x, 1))))
    have eY := (Matrix.map_mul (f := π)).symm.trans (congrArg (·.map π) (h.wittDecomp_anisotropicEmbedding_inclY (o.emb (x, 1))))
    have e0 := (Matrix.map_mul (f := π)).symm.trans ((congrArg (·.map π) (h.wittDecomp_anisotropicEmbedding_inclAnisotropic (o.emb (x, 1)))).trans Matrix.map_mul)
    have eA := (Matrix.map_mul (f := π)).symm.trans ((congrArg (·.map π) (o.emb_jA x 1)).trans Matrix.map_mul)
    have eB := (Matrix.map_mul (f := π)).symm.trans ((congrArg (·.map π) (o.emb_jB x 1)).trans Matrix.map_mul)
    rw [GlobalTheory.MixModel.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at eB
    have jA : h.j0.map π * o.jA.map π = (frameMat B A d.ι).map φ := by
      have e : o.jA.map π = (fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) K) (0 : Matrix (Fin 1) (Fin A.rank) K)).submatrix E.symm id := by
        rw [← Matrix.map_one φ (map_zero _) (map_one _), ← Matrix.map_zero φ (map_zero _), ← fromRows_map]; rfl
      rw [e, core, fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
    have jB : h.j0.map π * o.jB.map π = (midCol d rfl).map φ := by
      have e : o.jB.map π = (fromRows (0 : Matrix (Fin A.rank) (Fin 1) K) (1 : Matrix (Fin 1) (Fin 1) K)).submatrix E.symm id := by
        rw [← Matrix.map_one φ (map_zero _) (map_one _), ← Matrix.map_zero φ (map_zero _), ← fromRows_map]; rfl
      refine (congrArg (h.j0.map π * ·) e).trans ((core π _).trans ?_)
      rw [fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add]
    refine ⟨?_, fun p => ?_⟩
    · change _ * (frameMat B A d.ι).map φ = (frameMat B A d.ι).map φ * _
      rw [← jA, ← Matrix.mul_assoc, e0, Matrix.mul_assoc, eA, Matrix.mul_assoc]
    rcases lt_trichotomy p.val σ with hp | hp | hp
    · exact fix_col eX _ ⟨p.val, hp⟩ fun r => vX π r ⟨p.val, hp⟩
    · obtain rfl : p = ⟨σ, hσ'⟩ := Fin.ext hp
      have eZ : (mt B (h.emb0 (o.emb (x, 1)))).map π * (h.j0.map π * o.jB.map π) = h.j0.map π * o.jB.map π := by
        rw [← Matrix.mul_assoc, e0, Matrix.mul_assoc, eB]
      exact fix_col eZ 1 (0 : Fin 1) fun r => ((one_mul _).trans (congrFun (congrFun jB r) (0 : Fin 1))).symm
    · obtain ⟨q, rfl⟩ : ∃ q : Fin σ, p = (Fin.castLE hσ q).rev :=
        ⟨⟨2 * σ - p.1, by omega⟩, Fin.ext (by simp only [Fin.val_rev, Fin.val_castLE]; omega)⟩
      exact fix_col eY _ q fun r => vY π r q

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem shape_row {j : ℕ} (hj : j < D.R.m) : Shape (G.rowDec j hj) (GlobalTheory.CellMass.rowN G j) (GlobalTheory.CellMass.rowEmb G j) := by
  unfold GlobalTheory.CellMass.rowN GlobalTheory.CellMass.rowEmb
  split_ifs with h h'
  · exact shape_jac (G.rowDec j hj) _
  · exact shape_bes (G.rowDec j hj) _ _ _
  · omega

variable {G} in

theorem tilt_cols {j : ℕ} (hj₁ : j < D.R.m) {δ : GA D (G.V (.grid D.R.m j))} (h : GlobalTheory.RowVal.IsTilt G j δ) :
    ∃ l : Fin (D.R.m - 1 - j) → D.host.E,
      HMul.hMul (mt _ δ) (rat (frameMat _ _ (G.rowDec j hj₁).ι)) = rat (frameMat _ _ (G.rowDec j hj₁).ι) ∧
      HMul.hMul (mt _ δ) (rat (G.rowDec j hj₁).a) = rat ((G.rowDec j hj₁).a * diagonal l) := by
  rcases Nat.even_or_odd j with e | ⟨i, hi⟩
  · rw [h.2.1 e, GlobalTheory.MixModel.mt_one]
    exact ⟨fun _ => 1, Matrix.one_mul _, by rw [Matrix.one_mul, diagonal_one, Matrix.mul_one]⟩
  · obtain ⟨n, hn⟩ := D.R.m_even
    obtain ⟨σ, hσ⟩ : ∃ σ, D.R.m - 1 - j = 2 * σ := ⟨(D.R.m - 1 - j) / 2, by omega⟩
    obtain ⟨a, b, c⟩ := h.2.2 σ hj₁ hσ
    refine ⟨fun p => if p.1 < σ then (D.host.xi0 ^ p.1)⁻¹ else star (D.host.xi0 ^ (2 * σ - 1 - p.1)), a,
      Matrix.ext fun r p => ?_⟩
    have hp := p.2
    have hc : σ ≤ D.R.m - 1 - j := by clear hp; omega
    refine Eq.trans ?_ (congrArg (incA D) (mul_diagonal _ _ _ _).symm)
    by_cases hp' : p.1 < σ
    · rw [if_pos hp']
      exact (congrFun (congrFun b r) ⟨p.1, hp'⟩).trans (congrArg (incA D) (mul_diagonal _ _ _ _))
    · rw [if_neg hp']
      obtain ⟨q, rfl⟩ : ∃ q : Fin σ, p = (Fin.castLE hc q).rev :=
        ⟨⟨2 * σ - 1 - p.1, by omega⟩, Fin.ext (by simp only [Fin.val_rev, Fin.val_castLE]; omega)⟩
      rw [show 2 * σ - 1 - (Fin.castLE hc q).rev.1 = q.1 by
        have := q.2; simp only [Fin.val_rev, Fin.val_castLE]; omega]
      exact (congrFun (congrFun c r) q).trans (congrArg (incA D) (mul_diagonal _ _ _ _))

end GlobalTheory.PrLevel

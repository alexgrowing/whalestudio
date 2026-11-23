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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFlagNOfBlocks

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.PrLevel
open GlobalTheory.RootEx GlobalTheory.RowRep GlobalTheory.SplitWeil GlobalTheory.FunObj.LevRowSucc

variable {D : D7}

def phi {B : HSp D} {a c b : ℕ} (hb : b = B.rank) (hab : a + c = b) (β' : GL (Fin B.rank) (Lev.EAf D)) (w : Pl D.host.E) :
    GA D B →* GL (Fin a ⊕ Fin c) (Kw w) :=
  (frameGL hab).toMonoidHom.comp ((inBasis hb β' w).comp (Lev.finE B))

section Frame
variable {A B : HSp D} {c : ℕ} {ε : D.host.E} {d : HermitianOrthogonalExtensionData A B c ε} {N : Subgroup (GA D B)} {em : GA D A →* GA D B}
  {w : Pl D.host.E} {β : GL (Fin A.rank) (Lev.EAf D)} {β' : GL (Fin B.rank) (Lev.EAf D)} {u : Fin c → Kw w}

theorem phi_emb (hS : Shape d N em) (hF : IsSumFrame d w β β' u) {a b : ℕ} (ha : a = A.rank) (hb : b = B.rank) (hab : a + c = b)
    (x : GA D A) : phi hb hab β' w (em x) = embX c (inBasis ha β w (Lev.finE A x)) := by
  subst ha hb
  obtain ⟨Γ, h1, -, e⟩ := frame_val d w hF
  obtain ⟨h0, h2⟩ := hS.2.1 _ (piAt w) x
  refine Units.ext ((e (em x)).trans ?_)
  have a1 : (mt B (em x)).map (piAt w) * d.a.map ((piAt w).comp (incA D)) = d.a.map ((piAt w).comp (incA D)) :=
    Matrix.ext fun r p => congrFun (h2 p) r
  have e1 : (inBasis rfl β w (Lev.finE A x)).val =
      ((GlobalTheory.StdFrames.loc w β)⁻¹).val * (mt A x).map (piAt w) * (GlobalTheory.StdFrames.loc w β).val := by
    refine Matrix.ext fun r s => ?_
    change (GlobalTheory.StdFrames.loc w (β⁻¹ * Lev.finE A x * β⁻¹⁻¹)).val r s =
      ((GlobalTheory.StdFrames.loc w β)⁻¹ * GlobalTheory.StdFrames.loc w (Lev.finE A x) * GlobalTheory.StdFrames.loc w β).val r s
    rw [inv_inv, map_mul, map_mul, map_inv]
  have e2 : (mt B (em x)).map (piAt w) * sumCols d (piAt w) (GlobalTheory.StdFrames.loc w β).val u =
      sumCols d (piAt w) (GlobalTheory.StdFrames.loc w β).val u * fromBlocks (inBasis rfl β w (Lev.finE A x)).val 0 0 1 := by
    refine Eq.trans ?_ (fromCols_mul_fromBlocks _ _ _ _ _ _).symm
    rw [e1, sumCols, mul_fromCols, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, a1]
    simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (GlobalTheory.StdFrames.loc w β).val, Units.mul_inv, Matrix.one_mul]
  exact (congrArg (Γ * ·) e2).trans ((Matrix.mul_assoc _ _ _).symm.trans ((congrArg (· * _) h1).trans (Matrix.one_mul _)))

theorem phi_mem (hS : Shape d N em) (hc : 1 ≤ c) (hF : IsSumFrame d w β β' u) {a b : ℕ} (ha : a = A.rank) (hb : b = B.rank)
    (hab : a + c = b) {n : GA D B} (hn : n ∈ N) : phi hb hab β' w n ∈ symN (Kw w) (Fin a) c := by
  subst ha hb
  obtain ⟨Γ, h1, h2, e⟩ := frame_val d w hF
  obtain ⟨S₀, ρ, h, rfl, hA⟩ := hS.1
  refine (mem_symN_iff hc _).2 fun r s hrs => ?_
  exact (congrFun (congrFun (e n) r) s).trans ((hA _ (piAt w) _ _ u (GlobalTheory.StdFrames.loc w β).mul_inv).uni h1 h2 hn r s hrs)

theorem phi_diag (hF : IsSumFrame d w β β' u) {a b : ℕ} (ha : a = A.rank) (hb : b = B.rank) (hab : a + c = b) {g : GA D B}
    {l : Fin c → D.host.E} (h0 : HMul.hMul (mt B g) (rat (frameMat B A d.ι)) = rat (frameMat B A d.ι))
    (h1 : HMul.hMul (mt B g) (rat d.a) = rat (d.a * diagonal l)) :
    ∃ f, (phi hb hab β' w g).val = diagonal f ∧ ∀ i, f (.inl i) = 1 := by
  subst ha hb
  obtain ⟨Γ, h, -, e⟩ := frame_val d w hF
  set π := piAt w
  set b := (GlobalTheory.StdFrames.loc w β).val
  have hf : (mt B g).map π * sumCols d π b u = sumCols d π b u * diagonal (Sum.elim (fun _ => 1) fun p => π (incA D (l p))) := by
    have a0 : (mt B g).map π * (frameMat B A d.ι).map (π.comp (incA D)) = (frameMat B A d.ι).map (π.comp (incA D)) :=
      Matrix.map_mul.symm.trans (congrArg (·.map π) h0)
    have a1 : (mt B g).map π * d.a.map (π.comp (incA D)) = (d.a * diagonal l).map (π.comp (incA D)) :=
      Matrix.map_mul.symm.trans (congrArg (·.map π) h1)
    rw [Matrix.map_mul, diagonal_map (map_zero _)] at a1
    rw [sumCols, mul_fromCols, ← Matrix.mul_assoc, ← Matrix.mul_assoc, a0, a1]
    refine Matrix.ext fun r s => ?_
    refine Eq.trans ?_ (mul_diagonal _ _ _ _).symm
    rcases s with s | s
    · exact (mul_one _).symm
    · simp only [fromCols_apply_inr, mul_diagonal, Sum.elim_inr, RingHom.comp_apply]
      ring
  exact ⟨_, (e g).trans ((congrArg (Γ * ·) hf).trans ((Matrix.mul_assoc _ _ _).symm.trans
    ((congrArg (· * diagonal _) h).trans (Matrix.one_mul _)))), fun _ => rfl⟩

theorem blocks_of_phi (hc : 1 ≤ c) {S₀ : HSp D} {ρ : ℕ} {h : HypDec B S₀ ρ} (hA : ∀ (K : Type) [Field K] (π : AE D →+* K)
    (b b' : Matrix (Fin A.rank) (Fin A.rank) K) (u : Fin c → K), b * b' = 1 → Adapted π h (sumCols d π b u) (symStep _ c))
    (hF : IsSumFrame d w β β' u) {a b : ℕ} (ha : a = A.rank) (hb : b = B.rank)
    (hab : a + c = b) {n : GA D B} (hn : phi hb hab β' w n ∈ symN (Kw w) (Fin a) c) : Blocks (piAt w) h (mt B n - 1) := by
  subst ha hb
  obtain ⟨Γ, h1, h2, e⟩ := frame_val d w hF
  exact (hA _ (piAt w) _ _ u (GlobalTheory.StdFrames.loc w β).mul_inv).blocks h1 h2 fun r s hrs =>
    (congrFun (congrFun (e n) r) s).symm.trans ((mem_symN_iff hc _).1 hn r s hrs)

end Frame

theorem mem_of_phi {A B : HSp D} {c : ℕ} {ε : D.host.E} {d : HermitianOrthogonalExtensionData A B c ε} {N : Subgroup (GA D B)} {em : GA D A →* GA D B}
    (hS : Shape d N em) (hc : 1 ≤ c) {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {β : GL (Fin A.rank) (Lev.EAf D)}
    {β' : GL (Fin B.rank) (Lev.EAf D)} {u : ∀ w : P, Fin c → Kw w.1} (hF : ∀ w : P, IsSumFrame d w.1 β β' (u w)) {a b : P → ℕ}
    (ha : ∀ w, a w = A.rank) (hb : ∀ w, b w = B.rank) (hab : ∀ w, a w + c = b w) {n : GA D B} (hs : SuppAt e B n)
    (hn : ∀ w : P, phi (hb w) (hab w) β' w.1 n ∈ symN (Kw w.1) (Fin (a w)) c) : n ∈ N := by
  obtain ⟨S₀, ρ, h, rfl, hA⟩ := hS.1
  exact mem_flagN_of_blocks he h hs (fun w hw => blocks_of_phi hc hA (hF ⟨w, hw⟩) (ha _) (hb _) (hab _) (hn ⟨w, hw⟩))
    fun w hw => blocks_of_phi hc hA (hF ⟨w, hw⟩) (ha _) (hb _) (hab _) (by rw [map_inv]; exact inv_mem (hn ⟨w, hw⟩))

theorem inBasis_off {V : HSp D} {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {x : GA D V} (hs : SuppAt e V x)
    (β : GL (Fin V.rank) (Lev.EAf D)) {w : Pl D.host.E} (hw : ∀ v ∈ P, w.under (𝓞 D.host.F) ≠ v.under (𝓞 D.host.F)) :
    inBasis rfl β w (Lev.finE V x) = 1 := by
  set c : Lev.EAf D := toEAf D (e + cA D e) with hc
  have hX : (Lev.finE V x).val = c • (Lev.finE V x).val + (1 - c) • (1 : Matrix _ _ (Lev.EAf D)) := by
    have hM : (Lev.finE V x).val = (mt _ x).map (toEAf D) := rfl
    rw [hM]
    ext i k
    have h0 := congrArg (toEAf D) (hs i k)
    rw [map_mul, Matrix.sub_apply, map_sub] at h0
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
    by_cases hik : i = k
    · subst hik
      simp only [Matrix.one_apply_eq, map_one] at h0 ⊢
      rw [← hc] at h0
      linear_combination -h0
    · simp only [Matrix.one_apply_ne hik, map_zero, sub_zero, mul_zero, add_zero] at h0 ⊢
      exact h0.symm
  exact (GlobalTheory.OffPartLattice.inBasis_mix β _ _ c hX w).1 (GlobalTheory.OffPartLattice.cpt_pair_zero V he w hw)

set_option maxHeartbeats 800000 in

theorem KO_frame {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β β' : GL (Fin n) (Lev.EAf D)} (h : IsFrame β Λ)
    (h' : IsFrame β' Λ) (w : Pl D.host.E) {x : GL (Fin n) (Lev.EAf D)} (hx : inBasis rfl β' w x ∈ KO (Kw w) (Fin n)) :
    inBasis rfl β w x ∈ KO (Kw w) (Fin n) := by
  have key : ∀ {γ γ' : GL (Fin n) (Lev.EAf D)}, IsFrame γ Λ → IsFrame γ' Λ → ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      (γ' * γ⁻¹).val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := fun {γ γ'} a b y hy => by
    refine (b _).2 fun i => ?_
    have e : (γ'⁻¹).val *ᵥ ((γ' * γ⁻¹).val *ᵥ y) = (γ⁻¹).val *ᵥ y := by
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left]
    exact (congrFun e i) ▸ (a y).1 hy i
  have hz : β' * β⁻¹ ∈ St β := (GlobalTheory.LevSplit.mem_St_iff β Λ h _).2 ⟨key h h', by
    rw [_root_.mul_inv_rev, inv_inv]; exact key h' h⟩
  have hk := KO_of_St rfl β w hz
  have e : inBasis rfl β w x = inBasis rfl β w (β' * β⁻¹) * inBasis rfl β' w x * (inBasis rfl β w (β' * β⁻¹))⁻¹ := by
    simp only [inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul]
    congr 2
    group
  rw [e]
  exact mul_mem (mul_mem hk hx) (inv_mem hk)

end GlobalTheory.PrLevel

namespace GlobalTheory.PrLevel
open GlobalTheory.RootEx GlobalTheory.RowRep GlobalTheory.SplitWeil GlobalTheory.FunObj.LevRowSucc

theorem diag_mul {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {y z : GL (n ⊕ Fin c) k}
    (hy : ∃ f, y.val = diagonal f ∧ ∀ i, f (.inl i) = 1) (hz : ∃ f, z.val = diagonal f ∧ ∀ i, f (.inl i) = 1) :
    ∃ f, (y * z).val = diagonal f ∧ ∀ i, f (.inl i) = 1 := by
  obtain ⟨f, hf, hf'⟩ := hy
  obtain ⟨g, hg, hg'⟩ := hz
  exact ⟨_, by rw [Units.val_mul, hf, hg, diagonal_mul_diagonal], fun i => by simp only [hf', hg', mul_one]⟩

theorem mem_conj_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a c b : ℕ}
    (h : a + c = b) (ρ : GL (Fin b) k) (z : GL (Fin a ⊕ Fin c) k) :
    z ∈ ((KO k (Fin b)).map (MulAut.conj ρ).toMonoidHom).map (frameGL h).toMonoidHom ↔
      (frameGL h ρ)⁻¹ * z * frameGL h ρ ∈ KO k (Fin a ⊕ Fin c) := by
  obtain ⟨z, rfl⟩ := (frameGL (k := k) h).surjective z
  rw [← map_inv, ← map_mul, ← map_mul, frameGL_KO, Subgroup.map_equiv_eq_comap_symm', Subgroup.map_equiv_eq_comap_symm',
    Subgroup.mem_comap, Subgroup.mem_comap]
  simp

variable {D : D7}

set_option maxHeartbeats 1600000 in

theorem pr_iff {A B : HSp D} {c : ℕ} {ε : D.host.E} {d : HermitianOrthogonalExtensionData A B c ε} {N : Subgroup (GA D B)} {em : GA D A →* GA D B}
    (hS : Shape d N em) (hc : 1 ≤ c) {Λ : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)} {β : GL (Fin A.rank) (Lev.EAf D)}
    {β' β'' : GL (Fin B.rank) (Lev.EAf D)} (hβ' : IsFrame β' Λ) (hβ'' : IsFrame β'' Λ) (hsd : IsSelfDualC B Λ)
    {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {u : ∀ w : P, Fin c → Kw w.1}
    (hF : ∀ w : P, IsSumFrame d w.1 β β' (u w)) (hF' : ∀ w, ∃ u, IsSumFrame d w β β'' u) {a b : P → ℕ}
    (ha : ∀ w, a w = A.rank) (hb : ∀ w, b w = B.rank) (hab : ∀ w, a w + c = b w) {δ r x : GA D B} {l : Fin c → D.host.E}
    (h0 : HMul.hMul (mt B δ) (rat (frameMat B A d.ι)) = rat (frameMat B A d.ι))
    (h1 : HMul.hMul (mt B δ) (rat d.a) = rat (d.a * diagonal l)) (hr : SuppAt e B r) (s ρ : ∀ w : P, GL (Fin (b w)) (Kw w.1))
    (hs : ∀ w, ∃ f, (frameGL (hab w) (s w)).val = diagonal f ∧ ∀ i, f (.inl i) = 1)
    (hloc : ∀ w : P, inBasis (hb w) β' w.1 (Lev.finE B r) = s w * ρ w) (hx : x ∈ GfC B)
    (hfin : Lev.finE B x = Lev.finE B (δ * r)) {g : GA D A} (hg : g ∈ GfC A) :
    (∃ n ∈ N, x⁻¹ * (n * em g) * x ∈ GfC B ⊓ (congLev D.sp.cm B.gram Λ ⊤).comap (Lev.finE B)) ↔
      Lev.finE A g ∈ prodLev β P ha fun w =>
        symPr (((KO (Kw w.1) (Fin (b w))).map (MulAut.conj (ρ w)).toMonoidHom).map (frameGL (hab w)).toMonoidHom) := by
  have k1 := prodLev_inf_UA hβ' hsd P hb (fun w => KO (Kw w.1) _) fun _ => rfl
  have k2 := prodLev_inf_UA hβ'' hsd P (n' := fun _ => B.rank) (fun _ => rfl) (fun w => KO (Kw w.1) _) fun _ => rfl
  obtain ⟨Y, hY⟩ : ∃ Y : ∀ w : P, GL (Fin (a w) ⊕ Fin c) (Kw w.1), ∀ w, Y w = phi (hb w) (hab w) β' w.1 δ * frameGL (hab w) (s w) :=
    ⟨_, fun _ => rfl⟩
  have hYp : ∀ w : P, (∀ u ∈ symN (Kw w.1) (Fin (a w)) c, (Y w)⁻¹ * u * Y w ∈ symN (Kw w.1) (Fin (a w)) c) ∧
      (∀ u ∈ symN (Kw w.1) (Fin (a w)) c, Y w * u * (Y w)⁻¹ ∈ symN (Kw w.1) (Fin (a w)) c) ∧
      ∀ g, Y w * embX c g = embX c g * Y w := fun w => by
    obtain ⟨f, hf, hf'⟩ := diag_mul (phi_diag (hF w) (ha w) (hb w) (hab w) h0 h1) (hs w)
    exact diag_props (hY w ▸ hf) hf'
  have px : ∀ w : P, phi (hb w) (hab w) β' w.1 x = Y w * frameGL (hab w) (ρ w) := fun w => by
    have e1 : phi (hb w) (hab w) β' w.1 x = phi (hb w) (hab w) β' w.1 (δ * r) :=
      congrArg (fun z => frameGL (hab w) (inBasis (hb w) β' w.1 z)) hfin
    have e2 : phi (hb w) (hab w) β' w.1 r = frameGL (hab w) (s w * ρ w) := congrArg (frameGL (hab w)) (hloc w)
    rw [e1, map_mul, e2, map_mul, hY, mul_assoc]
  have qx : ∀ w : Pl D.host.E, (∀ v ∈ P, w.under (𝓞 D.host.F) ≠ v.under (𝓞 D.host.F)) →
      phi rfl d.rank β'' w x = phi rfl d.rank β'' w δ := fun w hw => by
    have e1 : phi rfl d.rank β'' w x = phi rfl d.rank β'' w (δ * r) :=
      congrArg (fun z => frameGL d.rank (inBasis rfl β'' w z)) hfin
    have e2 : phi rfl d.rank β'' w r = frameGL d.rank 1 := congrArg (frameGL d.rank) (inBasis_off he hr β'' hw)
    rw [e1, map_mul, e2, map_one, mul_one]
  have qp : ∀ w : Pl D.host.E,
      (∀ u ∈ symN (Kw w) (Fin A.rank) c, (phi rfl d.rank β'' w δ)⁻¹ * u * phi rfl d.rank β'' w δ ∈ symN (Kw w) (Fin A.rank) c) ∧
      ∀ g, phi rfl d.rank β'' w δ * embX c g = embX c g * phi rfl d.rank β'' w δ := fun w => by
    obtain ⟨v, hv⟩ := hF' w
    obtain ⟨f, hf, hf'⟩ := phi_diag hv rfl rfl d.rank h0 h1
    exact ⟨(diag_props hf hf').1, (diag_props hf hf').2.2⟩
  have alg : ∀ {G : Type} [Group G] (y n z : G), y * z = z * y → y⁻¹ * (n * z) * y = y⁻¹ * n * y * z := fun y n z h => by
    rw [mul_assoc _ y z, h]; group
  constructor
  · rintro ⟨n, hn, -, hk⟩
    replace hk : Lev.finE B (x⁻¹ * (n * em g) * x) ∈ congLev D.sp.cm B.gram Λ ⊤ := hk
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => ?_, Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => ?_⟩
    · have h2 := (frameGL_KO (hab w) _).2
        (Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (k1 ▸ hk)).1).1 w))
      replace h2 : phi (hb w) (hab w) β' w.1 (x⁻¹ * (n * em g) * x) ∈ KO (Kw w.1) _ := h2
      rw [map_mul, map_mul, map_mul, map_inv, px, phi_emb hS (hF w) (ha w)] at h2
      refine ⟨_, (hYp w).1 _ (phi_mem hS hc (hF w) (ha w) (hb w) (hab w) hn), (mem_conj_KO _ _ _).2 ?_⟩
      rw [← alg _ _ _ ((hYp w).2.2 _)]
      convert h2 using 1
      group
    · have h2 := (frameGL_KO d.rank _).2 (Subgroup.mem_comap.1
        (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (k2 ▸ hk)).1).2 w) hw))
      replace h2 : phi rfl d.rank β'' w (x⁻¹ * (n * em g) * x) ∈ KO (Kw w) _ := h2
      obtain ⟨v, hv⟩ := hF' w
      rw [map_mul, map_mul, map_mul, map_inv, qx w hw, phi_emb hS hv rfl, alg _ _ _ ((qp w).2 _)] at h2
      exact KO_of_mul hc ((qp w).1 _ (phi_mem hS hc hv rfl rfl d.rank hn)) h2
  · intro h
    obtain ⟨hP, hO⟩ := Subgroup.mem_inf.1 h
    choose v hv hv' using fun w : P => Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hP w)
    choose z hz using fun w : P => exists_inBasis_eq (hb w) β' w.1 ((frameGL (hab w)).symm (Y w * v w * (Y w)⁻¹))
    obtain ⟨n, hns, hn⟩ := exists_suppAt_loc_eq B P e he z
    have pn : ∀ w : P, phi (hb w) (hab w) β' w.1 n = Y w * v w * (Y w)⁻¹ := fun w =>
      (congrArg (frameGL (hab w)) (hz w _ (hn w))).trans ((frameGL (hab w)).apply_symm_apply _)
    have e0 : infPart D (e + cA D e) = 0 := by
      rw [RingHom.map_add, (GlobalTheory.FunObj.Comparison₂.cpt_idemSum he).1, GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.FunObj.Comparison₂.cpt_idemSum he).1, add_zero]
    refine ⟨n, mem_of_phi hS hc he hF ha hb hab hns fun w => pn w ▸ (hYp w).2.1 _ (hv w),
      Subgroup.mem_inf.2 ⟨(GfC B).mul_mem ((GfC B).mul_mem ((GfC B).inv_mem hx)
        ((GfC B).mul_mem (GlobalTheory.WeilProduct.mem_GfC_of_supp e0 hns) (hS.2.2 g hg))) hx, ?_⟩⟩
    change Lev.finE B (x⁻¹ * (n * em g) * x) ∈ congLev D.sp.cm B.gram Λ ⊤
    rw [← k1]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => ?_,
      Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => ?_⟩, GlobalTheory.LevSplit.finE_mem_UA _ _⟩
    · refine Subgroup.mem_comap.2 ((frameGL_KO (hab w) _).1 ?_)
      change phi (hb w) (hab w) β' w.1 (x⁻¹ * (n * em g) * x) ∈ KO (Kw w.1) _
      rw [map_mul, map_mul, map_mul, map_inv, px, phi_emb hS (hF w) (ha w), pn]
      have h2 := (mem_conj_KO _ _ _).1 (hv' w)
      convert h2 using 1
      rw [_root_.mul_inv_rev, mul_assoc (frameGL (hab w) (ρ w))⁻¹, mul_assoc (frameGL (hab w) (ρ w))⁻¹,
        ← mul_assoc _ (Y w) (frameGL (hab w) (ρ w)), alg _ _ _ ((hYp w).2.2 _)]
      group
    · refine Subgroup.mem_comap.2 (KO_frame hβ' hβ'' w ((frameGL_KO d.rank _).1 ?_))
      change phi rfl d.rank β'' w (x⁻¹ * (n * em g) * x) ∈ KO (Kw w) _
      obtain ⟨v, hv⟩ := hF' w
      have e2 : phi rfl d.rank β'' w n = frameGL d.rank 1 := congrArg (frameGL d.rank) (inBasis_off he hns β'' hw)
      rw [map_mul, map_mul, map_mul, map_inv, qx w hw, phi_emb hS hv rfl, alg _ _ _ ((qp w).2 _), e2, map_one, mul_one,
        inv_mul_cancel, one_mul]
      exact embX_KO (Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hO w) hw))

end GlobalTheory.PrLevel

namespace GlobalTheory.PrLevel
open GlobalTheory.RootEx GlobalTheory.RowRep GlobalTheory.SplitWeil GlobalTheory.CellMass

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem exists_frame (S : GridChoice W U) {j : ℕ} (hj : j < D.R.m) : ∃ β'' : GL (Fin (G.V (.grid D.R.m j)).rank) (Lev.EAf D),
    IsFrame β'' (G.Λ (.grid D.R.m j)) ∧ ∀ w, ∃ u, IsSumFrame (G.rowDec j hj) w (S.βp j) β'' u := by
  choose y hy _ using fun p : Fin (D.R.m - 1 - j) =>
    exists_gen (rowId_ne_zero G j p) Set.finite_empty (fun _ => 0) fun _ h => absurd h (Set.notMem_empty _)
  obtain ⟨β', h1, h2⟩ := exists_sumFrame (by norm_num : (-1 : D.host.E) ≠ 0) (G.rowDec j hj)
    (G.isV (X := .top j) hj.le fun _ e => by cases e).sd.1 (S.βp_is j hj.le) (rowId_ne_zero G j) y hy
  exact ⟨β', rowLat_eq G j hj ▸ h1, fun w => ⟨_, h2 w⟩⟩

theorem sgn_diag (t : T) (s : ℤˣ) (w : Pl D.host.E) (j : ℕ)
    (h : topRank (locGrid G t w) j + (D.R.m - 1 - j) = (locGrid G t w).rank (D.R.m, j)) :
    ∃ f, (frameGL h (sgnAt G t s w j)).val = diagonal f ∧ ∀ i, f (.inl i) = 1 := by
  have e : (frameGL h (sgnAt G t s w j)).val = (diagonal fun a => ((if Odd j ∧ topRank (locGrid G t w) j + (D.R.m - 1 - j) / 2 ≤ a.1
      then Units.map (Int.castRingHom (Kw w)).toMonoidHom s else 1 : (Kw w)ˣ) : Kw w)).submatrix (frame h) (frame h) := rfl
  refine ⟨_, e.trans (submatrix_diagonal_equiv _ (frame h)), fun i => ?_⟩
  have hi : (frame h (.inl i)).1 = i.1 := rfl
  have := i.2
  simp only [Function.comp_apply]
  rw [if_neg (by omega), Units.val_one]

set_option maxHeartbeats 1600000 in

theorem prSet_eq (S : GridChoice W U) {t : T} (ht : t ∈ U) (Φ : G.Datum) (s : ℤˣ) (β : CosFam G t) {b : Pts G}
    (h : IsRep t S.B s β b) {j : ℕ} (hi : j ∈ idx D) (hj : j < D.R.m) (hb : b j ∈ GfC _) :
    prSet G j ⟨b j, hb⟩ = {g | Lev.finE (G.V (.top j)) g.1 ∈ S.levTop t Φ β j hj} := by
  have hm := idx_le hi
  obtain ⟨δ, r, hδ, ⟨e, he, hr, hloc⟩, -, a, ha, hab⟩ := h.2 j hi hj.le
  obtain ⟨β'', hβ'', hF'⟩ := exists_frame S hj
  obtain ⟨l, h0, h1⟩ := tilt_cols hj hδ
  have hfin : Lev.finE (G.V (.grid D.R.m j)) (b j) = Lev.finE (G.V (.grid D.R.m j)) (δ * r) := by
    have h : Lev.finE (G.V (.grid D.R.m j)) a = 1 := by
      simp only [Lev.finE, GinfC, MonoidHom.mem_ker] at ha ⊢
      rw [MonoidHom.comp_apply, ha, map_one]
    rw [← hab, map_mul, h, one_mul]
  have hf : ∀ {i : ℕ}, 1 ≤ i → i ≤ D.R.m → IsFrame (S.B.β i j) (G.Λ (.grid i j)) := by
    rintro (_ | i) h h'
    · omega
    · exact S.B.isFrame (i + 1) j h h' hj.le
  have hl : ∀ (w : Pl D.host.E) (X : ℕ × ℕ), 1 ≤ X.1 → 1 ≤ X.2 → givenLevel G t w X = KO (Kw w) _ := by
    rintro w ⟨_ | a, _ | b⟩ h h'
    · omega
    · simp at h
    · simp at h'
    · rfl
  ext g
  have key := pr_iff (shape_row G hj) (by omega) (hf (by omega) le_rfl) hβ''
    (G.isV (X := .grid D.R.m j) ⟨le_rfl, hj.le⟩ fun k h => by have := (Node.grid.inj h).1; omega).sd he
    (fun w => S.row t ht w.1 w.2 j hj) hF' (fun w => topRank_eq G t w.1 hj.le)
    (fun w => rank_vertex G t w.1 (X := (D.R.m, j)) ⟨le_rfl, hj.le⟩)
    (fun w => by have := topRank_add (G := locGrid G t w.1) one_le_sLen j; change _ + D.R.m = (locGrid G t w.1).rank (D.R.m, j) + j + 1 at this; omega) h0 h1 hr
    (fun w => sgnAt G t s w.1 j) (fun w => (repsAt G t w.1).elt (β w) (D.R.m, j)) (fun w => sgn_diag t s w.1 j _) hloc hb hfin g.2
  refine key.trans ?_
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  refine Eq.to_iff (congrArg (fun K => Lev.finE (G.V (.top (i + 1))) g.1 ∈ prodLev (S.βp (i + 1)) (locPl G t) _ K) (funext fun w => ?_))
  rw [← hl w.1 (D.R.m, i + 1) (by show 1 ≤ D.R.m; omega) (by show 1 ≤ i + 1; omega)]
  rfl

theorem vol_prSet : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D, ∀ (hj : j < D.R.m) (ν : Measure (GfC (ch.G.V (.top j)))),
    ν.IsHaarMeasure → ∃ c : ℝ, 0 < c ∧ ∀ t Φ β b, IsRep t ch.S.B s β b → ∀ hb : b j ∈ GfC _,
      ν.real (prSet ch.G j ⟨b j, hb⟩) = c * ν.real {g | Lev.finE (ch.G.V (.top j)) g.1 ∈ ch.S.toGridChoice.levTop t Φ β j hj} :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ s _ hi hj _ _ => ⟨1, one_pos, fun t Φ β _ h hb => by
    rw [prSet_eq ch.S.toGridChoice (Set.mem_univ t) Φ s β h hi hj hb, one_mul]⟩⟩⟩

end GlobalTheory.PrLevel

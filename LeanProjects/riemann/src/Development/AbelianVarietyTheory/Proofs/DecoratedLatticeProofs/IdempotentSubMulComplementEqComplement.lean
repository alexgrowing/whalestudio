import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleCharRestrictLocalUnitsResidueChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocalModelCreationWeilActionMovedFramesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfSplitPlaceProductStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReductionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReducedChainLocalIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexEquivalenceReduction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open Formalism.L2.DIV (Pl kP blockTri blkOf upperLeftBlock dBlk resS LevelP)
open GlobalTheory.FunObj.Comparison₂ (IsRed Compat IsIx)
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.StepVec

section Place

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
variable (p : Place D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)

theorem up_down (t : WO S T) : p.up FS FT (p.down FS FT t) = p.e • t := by
  unfold Place.up Place.down
  have : FT.β * (FT.γ * (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * FS.β) * FS.γ = t.map p.π := by
    simp only [← Matrix.mul_assoc, FT.βγ, Matrix.one_mul]
    rw [Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
  rw [this]
  exact Matrix.ext fun i j => p.ι_π _

theorem down_add_up (t : WO S T) (x : Matrix Y Y' k) : p.down FS FT (t + p.up FS FT x) = p.down FS FT t + x := by
  unfold Place.up Place.down
  have : (t + (FT.β * x * FS.γ).map p.ι : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π =
      t.map p.π + FT.β * x * FS.γ := Matrix.ext fun i j => by
    simp only [Matrix.map_apply, Matrix.add_apply, map_add, p.π_ι]
  rw [this, Matrix.mul_add, Matrix.add_mul]
  congr 1
  simp only [← Matrix.mul_assoc, FT.γβ, Matrix.one_mul]
  rw [Matrix.mul_assoc, FS.γβ, Matrix.mul_one]

theorem smul_up (x : Matrix Y Y' k) : p.e • p.up FS FT x = p.up FS FT x :=
  Matrix.ext fun i j => by
    change p.e * p.ι _ = p.ι _
    rw [← p.ι_π, p.π_ι]

def extend (e : AE D) (Ω : WO S T → ℂ) : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Φ x := if IsHalf e x then Φ.1 (p.down FS FT x) * Ω ((1 - p.e) • x) else 0
  map_add' Φ Φ' := funext fun x => by
    simp only [Pi.add_apply, Submodule.coe_add]
    split_ifs
    · rw [add_mul]
    · rw [add_zero]
  map_smul' c Φ := funext fun x => by
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
    split_ifs
    · rw [mul_assoc]
    · rw [mul_zero]

theorem extend_apply (e : AE D) (Ω : WO S T → ℂ) (Φ : SB (Matrix Y Y' k)) (x : WO S T) :
    extend p FS FT e Ω Φ x = if IsHalf e x then Φ.1 (p.down FS FT x) * Ω ((1 - p.e) • x) else 0 := rfl

theorem isModel_extend {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} (hq : p.e * e = p.e) {Λ : AddSubgroup (WO S T)}
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm)
    (hth : ∀ Φ, IsSBHalf e Λ Φ → IsThetaFunO ψ S T (Tm Φ)) (Ω : WO S T → ℂ)
    (hsb : ∀ Φ, IsSBHalf e Λ (extend p FS FT e Ω Φ)) : p.IsModel ψ FS FT (Tm ∘ₗ extend p FS FT e Ω) := by
  have hee := p.split.1
  refine ⟨fun Φ => hth _ (hsb Φ), fun x Φ Φ' h => ?_, fun y hy Φ Φ' h => ?_⟩
  · have hx : IsHalf e (p.up FS FT x) := fun i j => by
      have := congrFun (congrFun (smul_up p FS FT x) i) j
      rw [Matrix.smul_apply, smul_eq_mul] at this
      rw [← this, ← mul_assoc, mul_comm e, hq]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hTm.trans _ (hsb Φ) _ hx]
    congr 1
    funext t
    have h1 : IsHalf e (t + p.up FS FT x) ↔ IsHalf e t := by
      rw [GlobalTheory.PlaceModel.isHalf_iff, GlobalTheory.PlaceModel.isHalf_iff]
      exact AddSubgroup.add_mem_cancel_right _ ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hx)
    have h2 : (1 - p.e) • (t + p.up FS FT x) = (1 - p.e) • t := by
      rw [smul_add, sub_smul 1 p.e (p.up FS FT x), one_smul, smul_up, sub_self, add_zero]
    rw [extend_apply, extend_apply, down_add_up, h, h2]
    exact if_congr h1.symm rfl rfl
  · have hy' : IsHalf (cA D e) y := fun i j => by
      rw [← hy i j, ← mul_assoc, ← RingHom.map_mul, mul_comm e, hq]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hTm.modul _ (hsb Φ) _ hy']
    congr 1
    funext t
    rw [extend_apply, extend_apply, h, up_down, GlobalTheory.PlaceModel.symplO_smul,
      (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy)]
    split_ifs
    · rw [mul_assoc]
    · rw [mul_zero]

def moved (g : GA D S) : Frame k S.rank Y' where
  β := (Formalism.L2.Theta.mt S g).map p.π * FS.β
  γ := FS.γ * (Formalism.L2.Theta.mt S g⁻¹).map p.π
  βγ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc FS.β, FS.βγ, Matrix.one_mul, ← Matrix.map_mul]
    simp [Formalism.L2.Theta.mt]
  γβ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ FS.β, ← Matrix.map_mul]
    simp [Formalism.L2.Theta.mt, FS.γβ]

theorem β_eq_moved (g : GA D S) : FS.β = (Formalism.L2.Theta.mt S g).map p.π * (moved p FS g⁻¹).β := by
  rw [moved, ← Matrix.mul_assoc, ← Matrix.map_mul]
  simp [Formalism.L2.Theta.mt]

theorem map_eq_of_movedTo {π' : EAf D →+* k} (hπ : ∀ a, π' (toEAf D a) = p.π a) {g : GA D S}
    {β : GL (Fin S.rank) (EAf D)} (B : Matrix Y' Y' k) (σ : Fin S.rank → Y')
    (h : MovedTo p S g β ((FS.β * B).submatrix id σ)) :
    β.val.map π' = ((moved p FS g⁻¹).β * B).submatrix id σ := by
  choose s hs using GlobalTheory.ResLoc.toEAf_surj (D := D)
  have h1 := h (β.val.map s) (Matrix.ext fun i j => hs _)
  have h2 : (β.val.map s).map p.π = β.val.map π' := Matrix.ext fun i j => by
    rw [Matrix.map_apply, Matrix.map_apply, ← hπ, hs]; rfl
  rw [Matrix.map_mul, h2] at h1
  have h3 : (Formalism.L2.Theta.mt S g⁻¹).map p.π * (Formalism.L2.Theta.mt S g).map p.π = 1 := by
    rw [← Matrix.map_mul]
    simp [Formalism.L2.Theta.mt]
  rw [← Matrix.one_mul (β.val.map π'), ← h3, Matrix.mul_assoc, h1, moved, Matrix.mul_assoc]
  rfl

theorem coords_down {π' : EAf D →+* k} (hπ : ∀ a, π' (toEAf D a) = p.π a) {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (LS : LatFrame k ι' Y') (LT : LatFrame k ι Y) (ea : ι' ≃ Fin S.rank) (eb : ι ≃ Fin T.rank)
    {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : βS.val.map π' = (FS.β * LS.bas.val).submatrix id fun i => LS.ord (ea.symm i))
    (hT : βT.val.map π' = (FT.β * LT.bas.val).submatrix id fun i => LT.ord (eb.symm i)) (x : WO S T) :
    LT.coords LS (p.down FS FT x) = ((frMapO S T βS βT x).map π').submatrix eb ea := by
  have h1 : (βT⁻¹).val.map π' = ((LT.bas⁻¹).val * FT.γ).submatrix (fun i => LT.ord (eb.symm i)) id := by
    refine Matrix.left_inv_eq_left_inv (A := βT.val.map π') ?_ ?_
    · rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [hT, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_assoc, ← Matrix.mul_assoc FT.γ, FT.γβ,
        Matrix.one_mul, Units.inv_mul]
      exact Matrix.submatrix_one_equiv (eb.symm.trans LT.ord)
  have h2 : ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D)).map π' = x.map p.π := Matrix.ext fun i j => hπ _
  rw [frMapO, Matrix.map_mul, Matrix.map_mul, h1, h2, hS, LatFrame.coords, Place.down]
  ext i j
  change _ = ((LT.bas⁻¹).val * FT.γ * x.map p.π * (FS.β * LS.bas.val)) (LT.ord (eb.symm (eb i))) (LS.ord (ea.symm (ea j)))
  simp only [Matrix.submatrix_apply, Matrix.mul_assoc, Equiv.symm_apply_apply]

end Place

section Prod

def locF {κ X : Type} [CommRing κ] {a b r : ℕ} (t j : ℕ) (hr : r ≤ a) (Rd : X → GL (Fin r) κ → Prop) (lam : X → ℂˣ)
    (χ : ℕ → κˣ →* ℂˣ) (y : Matrix (Fin b) (Fin a) κ) : ℂ :=
  if h : LowZero a y ∧ ∃ gx : GL (Fin a) κ × X, gx.1.val = topL a y ∧ gx.1 ∈ blockTri (blkOf r t) ∧ Rd gx.2 (upperLeftBlock hr gx.1) then
    (lam h.2.choose.2 : ℂ) * (∏ c ∈ Finset.range j, (χ (c + 1) (dBlk (blkOf r t) (c + 1) h.2.choose.1) : ℂ)) *
      (χ (j + 1) (Matrix.GeneralLinearGroup.det h.2.choose.1) : ℂ)⁻¹
  else 0

variable {D : D7}

theorem omegaG_eq_prod {a b r t j : ℕ} (hr : r ≤ a) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
    (χ : ℕ → ∀ w : Pl D.host.E, (kP w)ˣ →* ℂˣ) (ξ : ∀ w : Pl D.host.E, (kP w)ˣ →* ℂˣ) {X : Pg → Type}
    (Rd : ∀ w : Pg, X w → GL (Fin r) (kP w.1) → Prop) (lam : ∀ w : Pg, X w → ℂˣ)
    (hg : ∀ g : ∀ w : Pg, GL (Fin r) (kP w.1), g ∈ P.H ↔ ∀ w, ∃ x, Rd w x (g w))
    (hc : ∀ (g : P.H) (x : ∀ w, X w), (∀ w, Rd w (x w) (g.1 w)) → P.chi g = ∏ w, lam w (x w))
    (y : ∀ w : Pl D.host.E, Matrix (Fin b) (Fin a) (kP w)) :
    omegaG (Formalism.IndefR.Lev.datY a r t j hr Pg Q P χ ξ .B) (χ (j + 1)) y =
      ∏ w : Pg, locF t j hr (Rd w) (lam w) (fun c => χ c w.1) (y w.1) := by
  rw [omegaG]
  split_ifs with H
  · have h2 := H.2.choose_spec
    have h3 : ∀ w : Pg, LowZero a (y w.1) ∧ ∃ gx : GL (Fin a) (kP w.1) × X w, gx.1.val = topL a (y w.1) ∧
        gx.1 ∈ blockTri (blkOf r t) ∧ Rd w gx.2 (upperLeftBlock hr gx.1) := fun w => by
      obtain ⟨x, hx⟩ := (hg _).1 h2.2.2 w
      exact ⟨H.1 w.1 w.2, (H.2.choose w, x), h2.1 w, h2.2.1 w, hx⟩
    have h4 : ∀ w : Pg, (h3 w).2.choose.1 = H.2.choose w := fun w =>
      Units.ext ((h3 w).2.choose_spec.1.trans (h2.1 w).symm)
    have h5 := hc ⟨_, h2.2.2⟩ (fun w => (h3 w).2.choose.2) fun w => by
      have := (h3 w).2.choose_spec.2.2
      rw [h4] at this
      exact this
    simp only [locF, dif_pos (h3 _), Finset.prod_mul_distrib]
    simp only [h4]
    rw [← Units.coe_prod, ← h5]
    rfl
  · refine (Finset.prod_eq_zero_iff.2 (by_contra fun h => H ?_)).symm
    have h3 : ∀ w : Pg, LowZero a (y w.1) ∧ ∃ gx : GL (Fin a) (kP w.1) × X w, gx.1.val = topL a (y w.1) ∧
        gx.1 ∈ blockTri (blkOf r t) ∧ Rd w gx.2 (upperLeftBlock hr gx.1) := fun w =>
      by_contra fun h' => h ⟨w, Finset.mem_univ _, dif_neg h'⟩
    choose h2 g hg' using h3
    exact ⟨fun w hw => h2 ⟨w, hw⟩, fun w => (g w).1, fun w => (hg' w).1, fun w => (hg' w).2.1,
      (hg _).2 fun w => ⟨_, (hg' w).2.2⟩⟩

theorem idem_mul {e a : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {w : Pl D.host.E} (hw : w ∈ P)
    (ha : Formalism.L2.NTheta.IsIdemAt a w) : a * e = a := by
  obtain ⟨-, e1, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  obtain ⟨a0, -, a2⟩ := GlobalTheory.IdemSupport.delta_of_isIdemAt (GlobalTheory.StdFrames.comp_toAd D) ha
  refine (GlobalTheory.StdFrames.comp_toAd D).ext' (by rw [RingHom.map_mul, a0, zero_mul]) fun Q => ?_
  rw [GlobalTheory.IdemSupport.ev_mul]
  by_cases h : Q = w
  · subst h
    rw [show ((GlobalTheory.StdFrames.toAd D).comp (toEAf D)) e Q = 1 from e1 Q hw, mul_one]
  · rw [a2 Q h, zero_mul]

theorem frMapO_smul {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (a : AE D) (x : WO S T)
    (i : Fin T.rank) (j : Fin S.rank) : frMapO S T βS βT (a • x) i j = toEAf D a * frMapO S T βS βT x i j := by
  have : (a • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D a • x.map (toEAf D) :=
    Matrix.ext fun i j => (toEAf D).map_mul _ _
  exact (congrArg (fun z => GlobalTheory.FunObj.Comparison₂.fr βT βS z i j) this).trans
    (congrFun (congrFun (GlobalTheory.FunObj.Comparison₂.fr_smul βT βS _ _) i) j)

theorem redM_eq {a b : ℕ} {w : Pl D.host.E} {c : EAf D} {N N' : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) (hN' : IsIntM N')
    (h : ∀ i j, N' i j = c * N i j) (hc : ∀ (z : EAf D) (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
      (hz' : c * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), resS D.host.F w ⟨c * z, hz'⟩ = resS D.host.F w ⟨z, hz⟩) :
    redM w N = redM w N' := by
  funext i j
  have e : redM w N i j = resS D.host.F w ⟨N i j, hN i j⟩ := dif_pos (hN i j)
  have e' : redM w N' i j = resS D.host.F w ⟨N' i j, hN' i j⟩ := dif_pos (hN' i j)
  have h1 : c * N i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by rw [← h]; exact hN' i j
  exact (e.trans (hc _ (hN i j) h1).symm).trans
    (e'.trans (congrArg (resS D.host.F w) (Subtype.ext (h i j) : (⟨N' i j, hN' i j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      ⟨c * N i j, h1⟩))).symm

theorem idempotent_sub_mul_complement_eq_complement {R : Type} [CommRing R] {e a x : R} (hx : e * x = x) (ha : a * a = a) (h : a * e = a) :
    (e - a) * ((1 - a) * x) = (1 - a) * x := by
  linear_combination hx + x * ha - x * h

theorem ite_and_eq_ite_mul_ite_of_implications {A B B' : Prop} {u v w w' : ℂ} (h1 : B → B') (h2 : B → u = v * w) (h3 : B → w = w') (h4 : v ≠ 0 → B' → B)
    {A' : Prop} (h5 : A → A') {_ : Decidable (A ∧ B)} {_ : Decidable A} {_ : Decidable (A' ∧ B')} :
    (if A ∧ B then u else 0) = if A then v * (if A' ∧ B' then w' else 0) else 0 := by
  by_cases hA : A
  · by_cases hB : B
    · rw [if_pos ⟨hA, hB⟩, if_pos hA, if_pos ⟨h5 hA, h1 hB⟩, h2 hB, h3 hB]
    · rw [if_neg fun h => hB h.2, if_pos hA]
      by_cases hv : v = 0
      · rw [hv, zero_mul]
      · rw [if_neg fun h => hB (h4 hv h.2), mul_zero]
  · rw [if_neg fun h => hA h.1, if_neg hA]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

end Prod

section Step

open GlobalTheory.ChainOnto

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem redM_eq_map {a b : ℕ} (w : Pl D.host.E) {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) :
    redM w N = (Matrix.of fun i j => (⟨N i j, hN i j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)).map (resS D.host.F w) :=
  Matrix.ext fun i j => dif_pos (hN i j)

end Step

section Main

variable {D : D7} {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}

theorem locF_eq {κ X : Type} [CommRing κ] {a b r t j : ℕ} {hr : r ≤ a} {Rd : X → GL (Fin r) κ → Prop} {lam : X → ℂˣ}
    {χ : ℕ → κˣ →* ℂˣ} {y : Matrix (Fin b) (Fin a) κ} {v : ℂ}
    (h : (v ≠ 0 → LowZero a y ∧ ∃ g : GL (Fin a) κ, g.val = topL a y ∧ g ∈ blockTri (blkOf r t) ∧ ∃ x, Rd x (upperLeftBlock hr g)) ∧
      (LowZero a y → ∀ g : GL (Fin a) κ, g.val = topL a y → g ∈ blockTri (blkOf r t) → ∀ x, Rd x (upperLeftBlock hr g) →
        v = (lam x : ℂ) * (∏ c ∈ Finset.range j, (χ (c + 1) (dBlk (blkOf r t) (c + 1) g) : ℂ)) *
          (χ (j + 1) (Matrix.GeneralLinearGroup.det g) : ℂ)⁻¹)) : locF t j hr Rd lam χ y = v := by
  rw [locF]
  split_ifs with H
  · exact (h.2 H.1 _ H.2.choose_spec.1 H.2.choose_spec.2.1 _ H.2.choose_spec.2.2).symm
  · by_contra h0
    obtain ⟨h1, g, g1, g2, x, hx⟩ := h.1 (Ne.symm h0)
    exact H ⟨h1, (g, x), g1, g2, hx⟩

def firstOrd {κ l r : ℕ} (h : κ + l = r) : Fin κ ⊕ Fin l ≃ Fin r := finSumFinEquiv.trans (finCongr h)

theorem firstOrd_val {κ l r : ℕ} (h : κ + l = r) (a : Fin κ ⊕ Fin l) :
    (firstOrd h a).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ l a := by
  rcases a with a | a <;> rfl

theorem isIx_of_isOrd {κ l r t j a : ℕ} (h : κ + l = r) (ha : a = r + j * t) {e : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ Fin a}
    (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e) :
    IsIx ((Equiv.sumCongr (firstOrd h).symm (Equiv.refl (Fin j × Fin t))).trans e) := by
  refine ⟨ha, fun i => ?_, fun c s => ?_⟩
  · obtain ⟨i, rfl⟩ := (firstOrd h).surjective i
    rw [firstOrd_val, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.symm_apply_apply, he]
    rcases i with i | i <;> rfl
  · refine (he (.inr (c, s))).trans ?_
    change κ + l + c.val * t + s.val = _
    rw [h, mul_comm]; omega

theorem rank_first {w : Pl D.host.E} (G : GAt d τ w) : D.R.k + (G.s + 1) = D.R.r := by
  have := G.hs
  unfold Ranks.r
  omega

theorem red_iff {w : Pl D.host.E} (G : GAt d τ w) {π' : EAf D →+* G.k} (hπ : ∀ a, π' (toEAf D a) = G.q.pr a)
    (hred : IsRed (resS D.host.F w) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) (x : G.S.P.J)
    (g : GL (Fin D.R.r) (kP w)) (M : Matrix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.k ⊕ Fin (G.s + 1)) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hM : g.val.submatrix (firstOrd (rank_first G)) (firstOrd (rank_first G)) = M.map (resS D.host.F w)) :
    G.Red x g ↔ MaxM ((x : GL _ G.k).val - M.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) := by
  have key : ∀ a b (z : 𝓞 D.host.E), Ideal.Quotient.mk w.asIdeal z = g.val (firstOrd (rank_first G) a) (firstOrd (rank_first G) b) →
      valuation G.k ((π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (M a b) - (ofSplit G.q).pr (z : D.host.E)) < 1 :=
    fun a b z hz => by
      have h1 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) =
          (ofSplit G.q).pr (z : D.host.E) := hπ (incA D (z : D.host.E))
      rw [← h1, ← RingHom.map_sub, ← hred.ker, RingHom.map_sub, Formalism.L2.DIV.resS_oToS, sub_eq_zero]
      exact (hz.trans (congrFun (congrFun hM a) b)).symm
  constructor
  · intro h a b
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (g.val (firstOrd (rank_first G) a) (firstOrd (rank_first G) b))
    have := Valuation.map_sub_lt _ (h a b _ _ (firstOrd_val _ a) (firstOrd_val _ b) z hz) (key a b z hz)
    rwa [sub_sub_sub_cancel_right] at this
  · intro h a b a' b' ha hb z hz
    obtain rfl : a' = firstOrd (rank_first G) a := Fin.ext (ha.trans (firstOrd_val _ a).symm)
    obtain rfl : b' = firstOrd (rank_first G) b := Fin.ext (hb.trans (firstOrd_val _ b).symm)
    have := Valuation.map_add_lt _ (h a b) (key a b z hz)
    rwa [Matrix.sub_apply, Matrix.map_apply, sub_add_sub_cancel] at this

end Main

end GlobalTheory.LocMod.StepVec

namespace GlobalTheory.LocMod

open StepVec

end GlobalTheory.LocMod

end

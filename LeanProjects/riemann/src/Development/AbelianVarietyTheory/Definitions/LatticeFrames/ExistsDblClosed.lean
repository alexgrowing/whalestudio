import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod.PinModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nonempty_frame (k : Type) [Field k] {N : ℕ} (Y : Type) [Fintype Y] [DecidableEq Y] (h : Fintype.card Y = N) :
    Nonempty (GlobalTheory.LocMod.Frame k N Y) :=
  let e := Fintype.equivFinOfCardEq h
  ⟨⟨(1 : Matrix (Fin N) (Fin N) k).submatrix id e, (1 : Matrix (Fin N) (Fin N) k).submatrix e id,
    by rw [submatrix_mul_equiv]; simp, by rw [← submatrix_mul (he₂ := Function.bijective_id)]; simp⟩⟩

theorem exists_dbl (p : Place D k) {σ : ℕ} (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (n₀ n₁ n₂ : Type)
    [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] {s : k} (hs : s ≠ 0)
    (F₀ : GlobalTheory.LocMod.Frame k B.A.rank n₀) (F₁ : GlobalTheory.LocMod.Frame k J.W₀.rank n₁) (F₂ : GlobalTheory.LocMod.Frame k B'.A.rank n₂) :
    ∃ F : Dbl p B J B' n₀ n₁ n₂ (2 * σ), F.s = s ∧ F.F₀ = F₀ ∧ F.F₁ = F₁ ∧ F.F₂ = F₂ := by
  obtain ⟨G₀, h₀⟩ := Witness.exists_bes p B hs F₀
  obtain ⟨G₁, h₁⟩ := Witness.exists_jac p J hs (Witness.hz_ne p B) F₁
  obtain ⟨G₂, h₂⟩ := Witness.exists_bes p B' (mul_ne_zero hs (Witness.xi_ne p)) F₂
  exact ⟨⟨s, hs, F₀, F₁, F₂, G₀, G₁, G₂, h₀, h₁, h₂⟩, rfl, rfl, rfl, rfl⟩

theorem Dbl_c (p : Place D k) {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} {n₀ n₁ n₂ : Type}
    [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] {c : ℕ}
    (F : Dbl p B J B' n₀ n₁ n₂ c) : c = 2 * σ := by have := F.bes'.1; omega

theorem exists_dbl_closed (D : D7) : ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k)
    (_ : IsNonarchimedeanLocalField k) (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (B : BesLev D 1) (J : JacLev D 1) (B' : BesLev D 0),
    Nonempty (StepBF ψ B J) ∧ Nonempty (StepFB (σ := 0) ψ J B') ∧ Nonempty (Link B B'.L B'.ζ) ∧
      Nonempty (Dbl (σ := 0) p B J B' Unit Unit Unit 0) := by
  obtain ⟨v, ⟨p⟩⟩ := Witness.nonempty_place D
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  obtain ⟨ψ, hψ⟩ := (Inhab.exists_chain D).1
  let B : BesLev D 1 := Inhab.besPlane (GlobalTheory.RegSW.Model.hypFour D) (Inhab.cmHost_imaginaryGenerator_ne_zero D)
  let J : JacLev D 1 := Inhab.jacLine (hypDecThree D)
  let B' : BesLev D 0 := Inhab.besPlane (Inhab.hypRefl (Inhab.plane D)) one_ne_zero
  have e : D.host.xi0⁻¹ • B.ζ = B'.ζ := funext fun _ => inv_mul_cancel₀ (Inhab.cmHost_imaginaryGenerator_ne_zero D)
  have l : Link B B.L B'.ζ := e ▸ Inhab.selfLink B
  obtain ⟨F⟩ := nonempty_frame (v.adicCompletion D.host.F) (N := 1) Unit (by simp)
  obtain ⟨G, -⟩ := exists_dbl (σ := 0) p B J B' Unit Unit Unit one_ne_zero F F F
  exact ⟨_, _, _, _, _, p, ψ, B, J, B', Inhab.nonempty_stepBF hψ B J, Inhab.nonempty_stepFB hψ J B', ⟨l⟩, ⟨G⟩⟩

variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem exists_isOne : ∃ Φ : SB (Matrix Y Y' k), IsOne Φ ∧ Φ.1 0 = 1 := by
  refine ⟨⟨Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1, mem_SB_of_periodic (fun x hx => ?_) fun x y hy => ?_⟩, rfl, ?_⟩
  · exact (Set.mem_of_indicator_ne_zero hx)
  · have : (∀ r q, (x + y) r q ∈ 𝒪[k]) ↔ ∀ r q, x r q ∈ 𝒪[k] :=
      ⟨fun h r q => by simpa using sub_mem (h r q) (hy.intM r q), fun h r q => add_mem (h r q) (hy.intM r q)⟩
    by_cases hx : ∀ r q, x r q ∈ 𝒪[k]
    · rw [Set.indicator_of_mem (by exact this.2 hx), Set.indicator_of_mem (by exact hx)]
    · rw [Set.indicator_of_notMem (by exact fun h => hx (this.1 h)), Set.indicator_of_notMem (by exact hx)]
  · simp

theorem isCombAt_one (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (FS : GlobalTheory.LocMod.Frame k S.rank Y')
    (FT : GlobalTheory.LocMod.Frame k T.rank Y) :
    p.IsCombAt ψ FS FT (Finsupp.single 0 1) (Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) := by
  refine ⟨fun u hu => ?_, fun Tm _ Φ₀ Φ h₀ h => ?_⟩
  · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
    subst hu; intro i j; simp
  · obtain rfl : Φ = Φ₀ := Subtype.ext (h.trans h₀.symm)
    funext w
    simp [comb, Finsupp.support_single_ne_zero, heisO, symplOH, symplO, hO]

theorem toEAf_surj (D : D7) : Function.Surjective (toEAf D) := by
  refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
  exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id

theorem pi_congr (p : Place D k) {a b : Formalism.L2.Theta.AE D} (h : toEAf D a = toEAf D b) : p.π a = p.π b := by
  have h1 : finPart D a = finPart D b := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h
  have h2 : p.e * a = p.e * b := GlobalTheory.SplitScalar.adele_ext (by rw [map_mul, map_mul, GlobalTheory.SplitScalar.infPart_splitIdem p.split, zero_mul, zero_mul])
    (by rw [map_mul, map_mul, h1])
  rw [← p.π_ι (p.π a), p.ι_π, h2, ← p.ι_π, p.π_ι]

theorem exists_movedTo (p : Place D k) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {M M' : Matrix (Fin V.rank) (Fin V.rank) k}
    (hM : M * M' = 1) : ∃ g, SuppAt p.e V g ∧ MovedTo p V g β M := by
  choose f hf using toEAf_surj D
  have key : ∀ b : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D), b.map (toEAf D) = β.val →
      ((β⁻¹).val.map f).map p.π * b.map p.π = 1 := fun b hb => by
    have e : ((β⁻¹).val.map f * b).map (toEAf D) = (1 : Matrix _ _ (Formalism.L2.Theta.AE D)).map (toEAf D) := by
      rw [Matrix.map_mul, hb, show ((β⁻¹).val.map f).map (toEAf D) = (β⁻¹).val from by ext i j; exact hf _, Units.inv_mul,
        Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← Matrix.map_mul, ← Matrix.map_one p.π (map_zero _) (map_one _)]
    ext i j
    exact pi_congr p (congrFun (congrFun e i) j)
  have k0 := key (β.val.map f) (by ext i j; exact hf _)
  have h1 : M * ((β⁻¹).val.map f).map p.π * ((β.val.map f).map p.π * M') = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ M', k0, Matrix.one_mul, hM]
  obtain ⟨g, hg, hg'⟩ := Witness.exists_isLoc p (S := V) (Frame.ofGL 1) ⟨_, _, h1, mul_eq_one_comm.1 h1⟩
  refine ⟨g, hg, fun b hb => ?_⟩
  rw [Matrix.map_mul, hg']
  simp only [Frame.ofGL, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.mul_assoc, key b hb, Matrix.mul_one]

theorem movedTo_unique (p : Place D k) (V : HSp D) (g : GA D V) (β : GL (Fin V.rank) (Lev.EAf D))
    {M M' : Matrix (Fin V.rank) (Fin V.rank) k} (h : MovedTo p V g β M) (h' : MovedTo p V g β M') : M = M' := by
  choose f hf using toEAf_surj D
  have e : (β.val.map f).map (toEAf D) = β.val := by ext i j; exact hf _
  exact (h _ e).symm.trans (h' _ e)

theorem exists_ord (κ l τ j N : ℕ) (h : Fintype.card (Ix (Fin κ ⊕ Fin l) (Fin τ) j) = N) :
    ∃ e : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin N, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e := by
  have h' : κ + l + j * τ = N := by simpa using h
  refine ⟨((finSumFinEquiv.sumCongr finProdFinEquiv).trans finSumFinEquiv).trans (finCongr h'), ?_⟩
  rintro ((i | i) | ⟨a, b⟩) <;> simp [GlobalTheory.SymBridge.zPos]
  ring

variable {u : D.what₂.Word}

theorem exists_gAt (d : Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E)
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (unitVol : IsUnitVol ν) (q : GlobalTheory.FinPl.SplitPt D k)
    (idem : Formalism.L2.NTheta.IsIdemAt q.e PP) (unit : q.UnitAA) (s : ℕ) (hs : s + 1 + 1 = D.R.m) (S : SymData k s D.R.k)
    (char : (ofSplit q).IsChar d.c.ψ S.ψ) (mu : ∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit q).IsComp (d.c.chS j)⁻¹ (S.μ j))
    (FX : ∀ j, j ≤ s + 1 → GlobalTheory.LocMod.Frame k (D.sp.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j))
    (FT : GlobalTheory.LocMod.Frame k D.sp.X'.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2)))
    (FM : GlobalTheory.LocMod.Frame k (D.sp.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit))
    (c : k) (hc : valuation k c = 1) (hxi : valuation k (ofSplit q).xi = 1)
    (hz_unit : ∀ j ρ h, valuation k ((ofSplit q).hz (d.B j ρ h)) = 1) (z₀ : Fin d.Lz.rank → k)
    (last : FM.β = fromCols ((d.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
      (Matrix.of fun r _ => ((d.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r))
    (tau : ∀ h, (τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * c)) • fun i => (ofSplit q).pr ((d.bes s 0 h).ζ i))
    (latX : ∀ j hj (y : XIx (Fin D.R.k) (Fin D.R.t) j → k), (∀ i, y i ∈ 𝒪[k]) ↔
      (fun i => q.sec (((FX j hj).β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X j) (d.x j).L (· = q.v))
    (latM : ∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit → k, (∀ i, y i ∈ 𝒪[k]) ↔
      (fun i => q.sec ((FM.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X (s + 1 + 1)) (d.x (s + 1 + 1)).L (· = q.v))
    (frameTop : ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ≃ Fin D.sp.X'.rank,
      GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) D.sp.X' 1 d.top.β (FT.β.submatrix id e.symm))
    (cg : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ)
    (cg_mid : ∀ j c (H : j + 1 + c = s), (ofSplit q).IsCombAt d.c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (cg j)
      ((S.T (Fin D.R.t)).entry S.ψ ν j c H 1 1))
    (cg_pen : (ofSplit q).IsCombAt d.c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (cg s)
      fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t)))
    (cg_top : (ofSplit q).IsCombAt d.c.ψ (FX (s + 1) le_rfl) FM (cg (s + 1))
      ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))) :
    ∃ t' : ∀ j, GA D (d.st j).V, (∀ j, SuppAt q.e _ (t' j)) ∧ Nonempty (GAt { d with t := t' } τ PP) := by
  set p := ofSplit q with hp
  have hx : p.xi ≠ 0 := Witness.xi_ne p
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  let sc : ℕ → k := fun j => c * p.xi ^ (j / 2) / p.xi ^ (s / 2)
  have sc0 : ∀ j, sc j ≠ 0 := fun j => div_ne_zero (mul_ne_zero hc0 (pow_ne_zero _ hx)) (pow_ne_zero _ hx)
  have hodd := S.odd
  let Q : ∀ j c, j + c = s + 1 → GlobalTheory.LocMod.Frame k (d.st j).V.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) → Prop := fun j =>
    match j with
    | 0 => fun _ _ _ => True
    | j + 1 => fun c hc F => ∀ ρ h, p.IsJacFrame ((d.jac j ρ h).lev (d.x (j + 1)).vol) (sc j) (p.hz (d.B j ρ h)) (FX (j + 1) (by omega)) F
  have hFY : ∀ j c (hc : j + c = s + 1), ∃ F : GlobalTheory.LocMod.Frame k (d.st j).V.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c),
      (∀ ρ h, p.IsBesFrame (d.B j ρ h) (sc j) (FX j (by omega)) F) ∧ Q j c hc F := by
    intro j c hc
    by_cases hj : j % 2 = 0
    · obtain ⟨ρ, rfl⟩ : ∃ ρ, c = 2 * ρ + 1 := ⟨c / 2, by omega⟩
      have h : j + 2 * ρ + 2 = D.R.m := by omega
      obtain ⟨F, hF⟩ := Witness.exists_bes p (d.B j ρ h) (sc0 j) (FX j (by omega))
      refine ⟨F, fun ρ' h' => ?_, ?_⟩
      · obtain rfl : ρ' = ρ := by omega
        exact hF
      · cases j with
        | zero => trivial
        | succ j => intro ρ' h'; omega
    · obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      obtain ⟨ρ, rfl⟩ : ∃ ρ, c = 2 * ρ := ⟨c / 2, by omega⟩
      have h : j + 2 * ρ + 2 = D.R.m := by omega
      obtain ⟨F, hF⟩ := Witness.exists_jac p ((d.jac j ρ h).lev (d.x (j + 1)).vol) (sc0 j) (Witness.hz_ne p (d.B j ρ h))
        (FX (j + 1) (by omega))
      refine ⟨F, fun ρ' h' => by omega, fun ρ' h' => ?_⟩
      obtain rfl : ρ' = ρ := by omega
      exact hF
  choose FY hB hJ using hFY
  have ht : ∀ j, ∃ g : GA D (d.st j).V, SuppAt q.e _ g ∧ ∀ c (hc : j + c = s + 1),
      ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) j ≃ Fin (d.st j).V.rank,
      GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo p (d.st j).V g (d.st j).β
        (((FY j c hc).β * ((S.T (Fin D.R.t)).bas j c hc).val).submatrix id fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i)) := by
    intro j
    by_cases hj : j ≤ s + 1
    · obtain ⟨c, hc⟩ : ∃ c, j + c = s + 1 := ⟨s + 1 - j, by omega⟩
      obtain ⟨e, he⟩ := exists_ord D.R.k (s + 1) D.R.t j (d.st j).V.rank
        ((Fintype.card_congr (stdOrd _ _ j c hc)).trans (Witness.card_frame (FY j c hc)).symm)
      obtain ⟨g, hg, hg'⟩ := exists_movedTo p (d.st j).V (d.st j).β
        (M := ((FY j c hc).β * ((S.T (Fin D.R.t)).bas j c hc).val).submatrix id (e.symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) j c hc)))
        (M' := ((((S.T (Fin D.R.t)).bas j c hc)⁻¹).val * (FY j c hc).γ).submatrix (e.symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) j c hc)) id)
        (by rw [submatrix_mul_equiv, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (FY j c hc).γ, Units.mul_inv, Matrix.one_mul, (FY j c hc).βγ]; rfl)
      refine ⟨g, hg, fun c' hc' => ?_⟩
      obtain rfl : c' = c := by omega
      exact ⟨e, he, hg'⟩
    · exact ⟨1, fun i j => by simp [Formalism.L2.Theta.mt], fun c hc => by omega⟩
  choose t' ht1 ht2 using ht
  refine ⟨t', ht1, ⟨⟨k, ν, unitVol, q, idem, unit, s, hs, S, char, mu, FX, FT, FM, FY, sc, fun j => ?_, fun j => ?_, hz_unit,
    fun j ρ h c hc => hB j c hc ρ h, fun j ρ h c hc => hJ (j + 1) c hc ρ h, z₀, last, fun h => ?_, latX, latM, ht2, frameTop, cg,
    cg_mid, cg_pen, cg_top⟩⟩⟩
  · simp [sc, hc, hxi]
  · simp only [sc]
    rw [show (j + 1 + 1) / 2 = j / 2 + 1 by omega, pow_succ, ← hp]
    ring
  · have : sc s = c := by simp only [sc]; field_simp
    rw [this]; exact tau h

end GlobalTheory.LocMod.PinModel
end

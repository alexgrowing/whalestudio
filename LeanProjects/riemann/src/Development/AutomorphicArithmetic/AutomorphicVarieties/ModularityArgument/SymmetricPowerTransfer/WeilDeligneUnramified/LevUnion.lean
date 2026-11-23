import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnifLtOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.TwoUnder
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FitExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.AutomorphicInSphericalLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LevelStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RepsEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.SplitLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.SaNormal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.CongEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.CongLev
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LevExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.EigGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.BridgeEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ThetaTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ProdChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ClassRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IotaEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.FinMH

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem norm_prd (L : Type) [Field L] [NumberField L] [IsCMField L] (z : Lp L) :
    ∏ w : InfinitePlace L, w.embedding (algebraMap (Lp L) L z) = ((Algebra.norm ℚ z : ℚ) : ℂ) := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ z
  rw [eq_ratCast] at h
  rw [h]
  have hr : ∀ (τ : L →+* ℂ) (x : Lp L), (InfinitePlace.mk τ).embedding (algebraMap (Lp L) L x) = τ (algebraMap (Lp L) L x) := by
    intro τ x
    rcases InfinitePlace.embedding_mk_eq τ with e | e <;> rw [e]
    exact x.2 τ
  refine Finset.prod_bij (fun w _ => (w.embedding.comp (algebraMap (Lp L) L)).toRatAlgHom) (fun _ _ => Finset.mem_univ _)
    (fun w _ w' _ e => ?_) (fun σ _ => ⟨InfinitePlace.mk (ComplexEmbedding.lift L σ.toRingHom), Finset.mem_univ _, ?_⟩) fun _ _ => rfl
  · have e' : w.embedding.comp (algebraMap (Lp L) L) = w'.embedding.comp (algebraMap (Lp L) L) := RingHom.ext fun x => AlgHom.congr_fun e x
    apply (IsCMField.equivInfinitePlace L).injective
    change w.comap (algebraMap (Lp L) L) = w'.comap (algebraMap (Lp L) L)
    rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', InfinitePlace.comap_mk, InfinitePlace.comap_mk, e']
  · ext x
    exact (hr _ _).trans (ComplexEmbedding.lift_algebraMap_apply L _ x)

private theorem lev_union {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (U : Subgroup (UA L n)) (S₀ S₁ S : Finset (Plc L))
    (V₀ V₁ V : ∀ w : Plc L, Lev (Kw w)) (hS : ∀ w, w ∈ S ↔ w ∈ S₀ ∨ w ∈ S₁) (h0 : ∀ w ∈ S₀, V w = V₀ w) (h1 : ∀ w ∈ S₁, V w = V₁ w) :
    lev (lev U S₀ V₀) S₁ V₁ = lev U S V := by
  ext x
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]
  exact ⟨fun h => ⟨h.1.1, fun w hw => ((hS w).1 hw).elim (fun a => h0 w a ▸ h.1.2 w a) fun a => h1 w a ▸ h.2 w a⟩,
    fun h => ⟨⟨h.1, fun w a => h0 w a ▸ h.2 w ((hS w).2 (.inl a))⟩, fun w a => h1 w a ▸ h.2 w ((hS w).2 (.inr a))⟩⟩

private theorem iota_eq {F : Type} [Field F] [NumberField F] {Δ : F} {ι ι' : DX Δ →* DA Δ} (h : IsIotaD ι) (h' : IsIotaD ι') : ι = ι' :=
  MonoidHom.ext fun γ => Subtype.ext (funext fun v => Subtype.ext (Units.ext ((h γ v).trans (h' γ v).symm)))

section

variable {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem bG (hD : D.Ok) (W : Representation ℂ (U3 Δ) V) (Θ : V →ₗ[ℂ] V) (ch : F → ℂ) (h1 : ∀ γ v, Θ (W γ v) = W (theta Δ γ) (Θ v))
    (h2 : ∀ δ τ, HasTau δ τ → LinearMap.trace ℂ V (W δ ∘ₗ Θ) = ch τ) :
    ∃ (B : Base (U3 Δ) (GA Δ) V) (s : B.Tw), D.IsBG ch B s ∧ B.W = W ∧ s.Θ = Θ := baseG F Δ D hD V W Θ ch h1 h2

private theorem bS (hD : D.Ok) (W : Representation ℂ (SU Δ) V) (ch : F → ℂ)
    (h : ∀ (γ : SU Δ) τ, HasTr (γ : DX Δ) τ → LinearMap.trace ℂ V (W γ) = ch τ) (x : DA Δ) :
    ∃ B : Base (SU Δ) (SA Δ) V, D.IsBS ch x B ∧ B.W = W := baseS F Δ D hD V W ch h x

private theorem bK (hD : D.Ok) (W : Representation ℂ (DX Δ) V) (ch : F → ℂ)
    (h1 : ∀ z s, IsScal z s → ∀ v, W s v = ((Algebra.norm ℚ (z : F) : ℚ) : ℂ)⁻¹ • v)
    (h2 : ∀ (g : DX Δ) τ, (mt g).trace = algebraMap F _ (2 + τ) → (mt g).det = algebraMap F _ (2 + τ) → LinearMap.trace ℂ V (W g) = ch τ) :
    ∃ B : Base (DX Δ) (DA Δ) V, D.IsBK ch B ∧ B.W = W := baseK F Δ D hD V W ch h1 h2

private theorem iK {ch : F → ℂ} {B : Base (DX Δ) (DA Δ) V} (h : D.IsBK ch B) : IsIotaD B.ι := h.ι

end

set_option allowUnsafeReducibility true in
attribute [local irreducible] cv Kv Ov DX KD RP SA Lsq

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L] (B : Bridge L)

private theorem baseK' (A : SD B.Δ) (hA : A.Ok) {j : ℕ} (hj : 1 ≤ j) :
    ∃ C : Base (DX B.Δ) (DA B.Δ) (Wt.VD (InfinitePlace L) (2 * j + 1)), A.dat.IsBK (Wt.ch (em B) j) C ∧ C.W = Wt.cK (em B) j :=
  bK A.dat (datOk _ _ A hA).1 (Wt.cK (em B) j) (Wt.ch (em B) j) (fun z s h v => by
    rw [Wt.cK_scal _ hj z s h v, ← norm_prd L]
    congr 2
    exact Finset.prod_congr rfl fun w _ => congrArg w.embedding (B.e_alg _)) (Wt.cK_tr _ hj)

private theorem fitSq (T : Spl B) (S : Finset (Plc L)) (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)) (hb : FitCh T S a b) :
    FitCh T S (fun w => a w ^ 2) (b ^ 2) := fun w hw h => by
  rw [Pi.pow_apply, hb w hw h]
  ext z
  simp

private theorem core (hB : B.Ok) (T : Spl B) (S : Finset (Plc L)) (V : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ) (hA : A.Ok) (f : Fit T S V A)
    {j : ℕ} (hj : 1 ≤ j) (e : InfinitePlace L → ℤ) (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)) (hb : FitCh T S a b)
    (φ : UA L 2 → Wt.VD (InfinitePlace L) j) (h0 : φ ≠ 0) (hφ : IsAF (repE j e) (lev (Kall L 2) S V) φ) (E : ∀ w ∈ S, EigS φ w (V w) (a w))
    (BK : Base (DX B.Δ) (DA B.Δ) (Wt.VD (InfinitePlace L) (2 * j + 1))) (hK : A.dat.IsBK (Wt.ch (em B) j) BK) :
    (∃ φ : UA L 3 → Wt.VG (InfinitePlace L) j, φ ≠ 0 ∧ IsAF (Wt.repG _ j) (lev (Kall L 3) S V) φ ∧
      ∀ w ∈ S, EigT φ w (V w) ![a w, 1, (a w)⁻¹]) ∨ ∃ φ' ∈ BK.Forms, φ' ≠ 0 ∧ A.EigK φ' (b ^ 2) := by
  classical
  haveI : ∀ (K : Type) [Fintype K] (d : ℕ) (n : K → ℕ), FiniteDimensional ℂ (Wt.MH d n) := Wt.finMH
  have hD := (datOk _ _ A hA).1
  refine (inS L B hB T S V A hA f j e a b hb φ h0 hφ E).elim fun y Hy => ?_
  refine (bG A.dat hD (Wt.cG (em B) j) (Wt.thG _ j) (Wt.ch (em B) j) (Wt.cG_int _ hj) (Wt.cG_tr _ hj)).elim fun BG h =>
    h.elim fun s hG => ?_
  refine (bS A.dat hD (Wt.cS (em B) j) (Wt.ch (em B) j) (Wt.cS_tr _ hj) y).elim fun BS hS => ?_
  refine (Hy.2 _ BS hS.1 hS.2).elim fun ψ p => ?_
  refine (specF _ _ A hA _ _ _ _ BG s y BS BK hG.1 Hy.1 hS.1 hK b ψ p.1 p.2.1 p.2.2).imp_left fun q => q.elim fun φ' q => ?_
  exact outG L B hB T S V A hA f j a b hb _ BG s hG.1 hG.2.1 φ' q.1 q.2.1 q.2.2

private theorem second (hB : B.Ok) (T : Spl B) (S S₁ : Finset (Plc L)) (V : ∀ w : Plc L, Lev (Kw w)) (A A₀ : SD B.Δ) (hA : A.Ok) (hA₀ : A₀.Ok)
    (f : Fit T S V A) (hx : A.Ext A₀) (hS : ∀ w ∈ S, w ∈ S₁ ∨ un w ∈ A₀.Sg) (hs1 : S₁ ⊆ S) (v1 : ∀ w ∈ S₁, V w = iw w)
    (m : ℕ) (U : Subgroup (UA L 2)) (hm : 3 ≤ m) (u1 : IsCong m U) (hf : Full U S₁) {j : ℕ}
    (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)) (hb : FitCh T S a b)
    (BK : Base (DX B.Δ) (DA B.Δ) (Wt.VD (InfinitePlace L) (2 * j + 1))) (hK : A.dat.IsBK (Wt.ch (em B) j) BK) (k1 : BK.W = Wt.cK (em B) j)
    (Y : Finset (DA B.Δ)) (hY : A₀.Reps BK.ι Y) (hoff : ∀ y ∈ Y, A.dat.Off y)
    (m2 : ∀ y ∈ Y, ∀ g : SA B.Δ, (B.bS g : UA L 2) ∈ U → g ∈ A₀.lvS y)
    (φ' : DA B.Δ → Wt.VD (InfinitePlace L) (2 * j + 1)) (q1 : φ' ∈ BK.Forms) (q2 : φ' ≠ 0) (q3 : A.EigK φ' b) :
    ∃ φ : UA L 2 → Wt.VD (InfinitePlace L) (2 * j + 1), φ ≠ 0 ∧ IsAF (repE (2 * j + 1) 0) (lev U S₁ iw) φ ∧ ∀ w ∈ S₁, EigS φ w (iw w) (a w) := by
  refine (kNon _ _ A hA A₀ hA₀ hx _ _ BK hK Y hY hoff φ' q1 q2).elim fun x h => h.2.elim fun t ht => ?_
  have sf := kRes _ _ A hA _ _ BK hK x (hoff x h.1) φ' q1 _ q3
  rw [k1] at sf
  have hl := levExt L B hB T S V A hA f A₀ hA₀ hx S₁ hS (fun w hw => ⟨hs1 hw, v1 w hw⟩) U x (hoff x h.1) (m2 x h.1)
  have hn : (fun g : SA B.Δ => φ' (g * x)) ≠ 0 := fun h => ht (congrFun h t)
  have ho := outS L B hB T S V A hA f S₁ hs1 v1 m U hm u1 hf (2 * j + 1) (-((j : ℤ) + 1)) a b hb _ (iK _ hK) x (hoff x h.1) hl _ hn
  exact ho sf

private theorem offAll (T : Spl B) (S S₀ S₁ : Finset (Plc L)) (V V₀ : ∀ w : Plc L, Lev (Kw w)) (A A₀ : SD B.Δ) (f : Fit T S V A) (f₀ : Fit T S₀ V₀ A₀)
    (hS : ∀ w, w ∈ S ↔ w ∈ S₀ ∨ w ∈ S₁) (y : DA B.Δ) (h0 : A₀.dat.Off y) (h1 : ∀ w ∈ S₁, y.1 (un w) = 1) : A.dat.Off y := fun v hv =>
  ((f.sg v).1 hv).elim fun w hw => hw.2 ▸ ((hS w).1 hw.1).elim (fun h => h0 _ ((f₀.sg _).2 ⟨w, h, rfl⟩)) (h1 w)

end

def UpperTheory.V.Z.Sym.W.SpecOutS : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ S₀ : Finset (Plc L), Places (S₀ : Set (Plc L)) → HasTwo S₀ →
    ∀ j : ℕ, 1 ≤ j → ∃ c₀ : ℕ, ∀ c ≥ c₀, ∃ U₂ : Subgroup (UA L 2), IsLevel U₂ ∧
    ∀ S₁ : Finset (Plc L), Disjoint S₀ S₁ → Places ((S₀ : Set (Plc L)) ∪ S₁) → (∀ w ∈ S₁, locU 2 w ⊓ Kall L 2 ≤ U₂) →
    ∀ (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (e : InfinitePlace L → ℤ) (φ : UA L 2 → Wt.VD (InfinitePlace L) j), φ ≠ 0 →
      IsAF (repE j e) (lev (lev (Kall L 2) S₀ (deep c)) S₁ iw) φ →
      (∀ w ∈ S₀, EigS φ w (deep c w) (a w)) → (∀ w ∈ S₁, EigS φ w (iw w) (a w)) →
      (∃ φ' : UA L 3 → Wt.VG (InfinitePlace L) j, φ' ≠ 0 ∧ IsAF (Wt.repG _ j) (lev (lev (Kall L 3) S₀ (deep c)) S₁ iw) φ' ∧
        (∀ w ∈ S₀, EigT φ' w (deep c w) ![a w, 1, (a w)⁻¹]) ∧ ∀ w ∈ S₁, EigT φ' w (iw w) ![a w, 1, (a w)⁻¹]) ∨
      ∃ φ' : UA L 2 → Wt.VD (InfinitePlace L) (2 * j + 1), φ' ≠ 0 ∧ IsAF (repE (2 * j + 1) 0) (lev U₂ S₁ iw) φ' ∧
        ∀ w ∈ S₁, EigS φ' w (iw w) (a w ^ 2)

theorem UpperTheory.V.Z.Sym.W.specOutS : UpperTheory.V.Z.Sym.W.SpecOutS := by
  classical
  intro L _ _ _ hU S₀ hP hT j hj
  refine (bridgeEx L hU).elim fun B hB => ?_
  have T : Spl B := fun w h => (hB.split w h).some
  refine ⟨0, fun c _ => ?_⟩
  refine (fitEx L B hB T S₀ (deep c) hP hT).1.elim fun A₀ h₀ => ?_
  refine (iotaEx (Lp L) B.Δ).2.1.elim fun ι hι => ?_
  refine (repsEx _ _ A₀ h₀.1 classRep ι hι).elim fun Y hY => ?_
  refine (congLev L B hB T S₀ (deep c) A₀ h₀.1 h₀.2 Y fun y hy => (hY.1 y hy).2).elim fun m hm => ?_
  refine (congEx L 2 m (by have := hm.1; omega)).elim fun U u => ?_
  refine ⟨U, u.2.1, fun S₁ hd hP' hf a e φ h0 hφ E0 E1 => ?_⟩
  have hS : ∀ w, w ∈ S₀ ∪ S₁ ↔ w ∈ S₀ ∨ w ∈ S₁ := fun _ => Finset.mem_union
  have hPS : Places ((S₀ ∪ S₁ : Finset (Plc L)) : Set (Plc L)) := by rwa [Finset.coe_union]
  generalize S₀ ∪ S₁ = S at hS hPS
  have hV : ∃ V : ∀ w : Plc L, Lev (Kw w), (∀ w ∈ S₀, V w = deep c w) ∧ ∀ w ∈ S₁, V w = iw w :=
    ⟨fun w => if w ∈ S₁ then iw w else deep c w, fun w hw => if_neg (Finset.disjoint_left.1 hd hw), fun w hw => if_pos hw⟩
  refine hV.elim fun V v => ?_
  have hF := fitEx L B hB T S V hPS fun w hw => (hT w hw).imp fun w' h => ⟨(hS w').2 (.inl h.1), h.2⟩
  refine hF.1.elim fun A hA => (hF.2 a).elim fun b hb => ?_
  have hs0 : S₀ ⊆ S := fun w hw => (hS w).2 (.inl hw)
  have hs1 : S₁ ⊆ S := fun w hw => (hS w).2 (.inr hw)
  have hx : A.Ext A₀ := fitExt L B T S₀ S (deep c) V A₀ A h₀.2 hA.2 hs0 v.1 fun w hw h => v.2 w (((hS w).1 hw).resolve_left h)
  rw [lev_union _ S₀ S₁ S _ _ V hS v.1 v.2] at hφ
  rw [lev_union _ S₀ S₁ S _ _ V hS v.1 v.2]
  refine (baseK' B A hA.1 hj).elim fun BK hK => ?_
  have eι : ι = BK.ι := iota_eq hι (iK _ hK.1)
  refine (core B hB T S V A hA.1 hA.2 hj e a b hb φ h0 hφ (fun w hw =>
    ((hS w).1 hw).elim (fun h => v.1 w h ▸ E0 w h) fun h => v.2 w h ▸ E1 w h) BK hK.1).imp
    (fun r => r.imp fun r h => ⟨h.1, h.2.1, fun w hw => v.1 w hw ▸ h.2.2 w (hs0 hw), fun w hw => v.2 w hw ▸ h.2.2 w (hs1 hw)⟩) fun q => q.elim fun φ' q => ?_
  exact second B hB T S S₁ V A A₀ hA.1 h₀.1 hA.2 hx (fun w hw => ((hS w).1 hw).elim (fun h => .inr ((h₀.2.sg _).2 ⟨w, h, rfl⟩)) .inl) hs1 v.2
    m U hm.1 u.1 ⟨u.2.1.1, hf⟩ _ _ (fitSq B T S a b hb) BK hK.1 hK.2 Y (eι ▸ hY)
    (fun y hy => offAll B T S S₀ S₁ V _ A A₀ hA.2 h₀.2 hS y (hY.1 y hy).1 fun w hw =>
      hm.2.1 w (u.2.2 le_rfl w (hPS.split w (hs1 hw)) (hf w hw)) y hy)
    (hm.2.2 U u.1) φ' q.1 q.2.1 q.2.2

end

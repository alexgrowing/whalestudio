import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Translate
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ExpoMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ProdEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FinOrbSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.HomTrivialOnDetOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OutInvMulMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IndexNeZero

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

private theorem dc_sub {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (S U : Subgroup G) (hS : S.Normal) (a : S)
    (hf : AlgebraTools.FinOrb U U (a : G)) (hc : ∀ u ∈ U, ∃ c ∈ U, c * a = a * c ∧ u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S)
    (φ : G → V) (hφ : ∀ u ∈ U, ∀ g, φ (g * u) = φ g) (c : ℂ) (he : dcF U (a : G) φ = c • φ) (x : G) :
    dcF (U.subgroupOf S) a (fun s : S => φ (x * s)) = c • (fun s : S => φ (x * s)) := by
  classical
  obtain ⟨hf', hdc, -, R, hR1, hR2, hR3⟩ := dcSub G V S U a hf hc hS
  have hφ' : ∀ u ∈ U.subgroupOf S, ∀ g : S, (fun s : S => φ (x * s)) (g * u) = (fun s : S => φ (x * s)) g := by
    intro u hu g
    have := hφ _ (Subgroup.mem_subgroupOf.1 hu) (x * g)
    simpa [mul_assoc] using this
  have h1 := (dcBasic S V (U.subgroupOf S) a hf' (fun s : S => φ (x * s)) hφ').2.2.2.2 R hR1 hR2
  have h2 := (dcBasic G V U a hf φ hφ).2.2.2.2 (R.image (fun r : S => (r : G)))
    (by
      intro y hy
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hy
      exact (hdc r).1 (hR1 r hr))
    (by
      intro y hy
      obtain ⟨r, ⟨hr, hu⟩, hun⟩ := hR3 y hy
      refine ⟨r, ⟨Finset.mem_image_of_mem _ hr, hu⟩, ?_⟩
      rintro _ ⟨hr', hu'⟩
      obtain ⟨r', hr'', rfl⟩ := Finset.mem_image.1 hr'
      rw [hun r' ⟨hr'', hu'⟩])
  funext g
  have h3 := congrFun he (x * g)
  rw [h2, Finset.sum_image (fun a _ b _ h => Subtype.ext h)] at h3
  rw [h1 g]
  simpa [mul_assoc] using h3

private theorem rep_eq {L : Type} [Field L] [NumberField L] [IsCMField L] (B : Bridge L) (j : ℕ) (e : InfinitePlace L → ℤ)
    (γ : SU B.Δ) (k : UA L 2) (hk : ∀ τ, cEmb τ k = cEmb τ (B.rS γ : UA L 2)) :
    repE j e (infC L 2 k) = Wt.cS (em B) j γ := by
  have h1 : infC L 2 k = Wt.infG (em B) 2 ((γ : DX B.Δ) : GL (Fin 2) (Lsq (Lp L) B.Δ)) := by
    funext v
    apply Units.ext
    change ((cEmb v.embedding k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [hk, B.rS_inf]
    rfl
  have hd : ∀ v, Matrix.GeneralLinearGroup.det (infC L 2 k v) = 1 := by
    intro v
    rw [h1]
    have hγ : Matrix.GeneralLinearGroup.det ((γ : DX B.Δ) : GL (Fin 2) (Lsq (Lp L) B.Δ)) = 1 := γ.2
    change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (em B v) _) = 1
    apply Units.ext
    have := congrArg (fun u : (Lsq (Lp L) B.Δ)ˣ => em B v (u : Lsq (Lp L) B.Δ)) hγ
    simpa [Matrix.GeneralLinearGroup.map, RingHom.map_det] using this
  change ((∏ v, Matrix.GeneralLinearGroup.det (infC L 2 k v) ^ e v : ℂˣ) : ℂ) • Wt.mRep 2 _ (infC L 2 k) =
    (Wt.detE 2 0 _ : ℂ) • Wt.mRep 2 _ _
  have hs : (∏ v, Matrix.GeneralLinearGroup.det (infC L 2 k v) ^ e v : ℂˣ) = 1 :=
    Finset.prod_eq_one fun v _ => by rw [hd, one_zpow]
  have ht : ∀ g : InfinitePlace L → GL (Fin 2) ℂ, Wt.detE 2 0 g = 1 := fun g => by simp [Wt.detE]
  rw [hs, ht, h1]
  rfl

end UpperTheory.V.Z.Sym.So

namespace UpperTheory.V.Z.Sym.So

private theorem val_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ)
    (ht : valuation k (t : k) < valuation k (unif k : k) ^ 2) : valuation k (t : k) < 1 := by
  have h1 : valuation k (unif k : k) ≤ 1 := by
    rw [GlAx.unif_spec]
    exact uniformizer_lt_one.le
  exact lt_of_lt_of_le ht (pow_le_one' h1 2)

private theorem sub_normal (L : Type) [Field L] [NumberField L] [IsCMField L] : (finU L 2 ⊓ SUA L).Normal := by
  have h6 := (uaFacts L 2).2.2.2.2.2.1
  have h1 : (finU L 2).Normal := ⟨fun n hn g => by
    refine ((h6 _).1).2 fun τ => ?_
    rw [map_mul, map_mul, map_inv, ((h6 n).1).1 hn τ]
    simp⟩
  have h2 : (SUA L).Normal := by
    unfold SUA
    infer_instance
  infer_instance

private theorem off_on_comm {L : Type} [Field L] [NumberField L] [IsCMField L] (S : Finset (Plc L)) (x a : UA L 2)
    (hx : x ∈ finU L 2) (hoff : OffS S x) (ha : OnS S a) : x * a = a * x := by
  have h5 := (uaFacts L 2).2.2.2.2.1
  have h6 := (uaFacts L 2).2.2.2.2.2.1
  refine h5 _ _ (fun u => ?_) (fun τ => ?_)
  · by_cases h : ∀ w ∈ S, un u ≠ un w
    · rw [map_mul, map_mul, ha.2 u h, one_mul, mul_one]
    · push_neg at h
      obtain ⟨w, hw, hu⟩ := h
      rw [map_mul, map_mul, hoff w hw u hu, one_mul, mul_one]
  · rw [map_mul, map_mul, ((h6 x).1).1 hx τ, ((h6 a).1).1 ha.1 τ]

end UpperTheory.V.Z.Sym.So

namespace UpperTheory.V.Z.Sym.So

private theorem dc_tr {H G V : Type} [Group H] [Group G] [AddCommGroup V] [Module ℂ V] (S U : Subgroup G) (hS : S.Normal)
    (b : H ≃* S) (x : G) (CU : Subgroup H) (hCU : ∀ g, g ∈ CU ↔ x⁻¹ * (b g : G) * x ∈ U) (g : H) (hx : x * (b g : G) = b g * x)
    (hf : AlgebraTools.FinOrb U U (b g : G)) (hc : ∀ u ∈ U, ∃ c ∈ U, c * (b g : G) = b g * c ∧ u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S)
    (φ : G → V) (hφ : ∀ u ∈ U, ∀ g, φ (g * u) = φ g) (c : ℂ) (he : dcF U (b g : G) φ = c • φ) :
    dcF CU g (fun h => φ ((b h : G) * x)) = c • (fun h => φ ((b h : G) * x)) := by
  haveI := hS
  let β : H ≃* S := b.trans (MulAut.conjNormal x⁻¹)
  have hβ : ∀ g, ((β g : S) : G) = x⁻¹ * b g * x := by
    intro g
    simp [β, MulAut.conjNormal_apply]
  have hCU' : CU = (U.subgroupOf S).comap β.toMonoidHom := by
    ext g
    rw [hCU, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    change _ ↔ ((β g : S) : G) ∈ _
    rw [hβ]
  have hβg : β.toMonoidHom g = b g := by
    apply Subtype.ext
    change ((β g : S) : G) = _
    rw [hβ, mul_assoc, ← hx]
    group
  have hfin' := (dcSub G V S U (b g) hf hc hS).1
  have hφ' : ∀ u ∈ U.subgroupOf S, ∀ g : S, (fun s : S => φ (x * s)) (g * u) = (fun s : S => φ (x * s)) g := by
    intro u hu g
    have := hφ _ (Subgroup.mem_subgroupOf.1 hu) (x * g)
    simpa [mul_assoc] using this
  have hm := (dcMap H S V β.toMonoidHom β.bijective (U.subgroupOf S) g g).2.2.2 (by rw [hβg]; exact hfin') (fun s : S => φ (x * s)) hφ'
  have hψ : (fun h => φ ((b h : G) * x)) = (fun s : S => φ (x * s)) ∘ β.toMonoidHom := by
    funext h
    change φ _ = φ (x * ((β h : S) : G))
    rw [hβ]
    simp [mul_assoc]
  rw [hCU', hψ, hm, hβg, dc_sub S U hS (b g) hf hc φ hφ c he x]
  rfl

end UpperTheory.V.Z.Sym.So

namespace UpperTheory.V.Z.Sym.So
private theorem grp1 {G : Type} [Group G] (r p k h x : G) (hr : r = p * k) (hc : (h * x) * k⁻¹ = k⁻¹ * (h * x)) :
    (p * h) * x = r * ((h * x) * k⁻¹) := by
  rw [hr, hc]
  group
end UpperTheory.V.Z.Sym.So

namespace UpperTheory.V.Z.Sym.So
private theorem inS_left {L : Type} [Field L] [NumberField L] [IsCMField L] (B : Bridge L) (hB : B.Ok) (j : ℕ) (e : InfinitePlace L → ℤ)
    (U : Subgroup (UA L 2)) (φ : UA L 2 → Wt.VD (InfinitePlace L) j) (hφ : IsAF (repE j e) U φ) (x : UA L 2) (hxf : x ∈ finU L 2)
    (ι : SU B.Δ →* SA B.Δ) (hι : ∀ γ v, mt ((ι γ : DA B.Δ).1 v) = (mt (γ : DX B.Δ)).map (lmap (cv v) B.Δ)) (γ : SU B.Δ) (g : SA B.Δ) :
    φ ((B.bS (ι γ * g) : UA L 2) * x) = Wt.cS (em B) j γ (φ ((B.bS g : UA L 2) * x)) := by
  obtain ⟨k, hk, hr, hτ⟩ := hB.finS γ (ι γ) (hι γ)
  have hc : (((B.bS g : UA L 2) * x) * k⁻¹) = k⁻¹ * ((B.bS g : UA L 2) * x) :=
    (((uaFacts L 2).2.2.2.1 _ (mul_mem (B.bS g).2.1 hxf) _ (inv_mem hk.1))).eq
  have e1 : ((B.bS (ι γ * g) : UA L 2) * x) = (B.rS γ : UA L 2) * (((B.bS g : UA L 2) * x) * k⁻¹) := by
    rw [map_mul, Subgroup.coe_mul]
    exact grp1 _ _ _ _ _ hr hc
  have e2 : φ ((B.rS γ : UA L 2) * (((B.bS g : UA L 2) * x) * k⁻¹)) = φ (((B.bS g : UA L 2) * x) * k⁻¹) := hφ.left _ (B.rS γ).2.1 _
  have e3 := hφ.inf _ (inv_mem hk.1) ((B.bS g : UA L 2) * x)
  rw [inv_inv] at e3
  rw [e1, e2, e3, rep_eq B j e γ k hτ]
end UpperTheory.V.Z.Sym.So

namespace UpperTheory.V.Z.Sym.So

private theorem gen {Γ H G V : Type} [Group Γ] [Group H] [Group G] [AddCommGroup V] [Module ℂ V] (S U : Subgroup G) (hS : S.Normal)
    (b : H ≃* S) (x : G) (C : Base Γ H V) (hω : C.ω = 1) (hCU : ∀ g, g ∈ C.U ↔ x⁻¹ * (b g : G) * x ∈ U)
    (φ : G → V) (hφ : ∀ u ∈ U, ∀ g, φ (g * u) = φ g)
    (hleft : ∀ γ g, φ ((b (C.ι γ * g) : G) * x) = C.W γ (φ ((b g : G) * x))) (s : S) (hs : φ ((s : G) * x) ≠ 0)
    (P : H → ℂ → Prop) (hP : ∀ g c, P g c → x * (b g : G) = b g * x ∧ AlgebraTools.FinOrb U U (b g : G) ∧
      (∀ u ∈ U, ∃ c ∈ U, c * (b g : G) = b g * c ∧ u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S) ∧ dcF U (b g : G) φ = c • φ) :
    ∃ ψ ∈ C.Forms, ψ ≠ 0 ∧ ∀ g c, P g c → dcF C.U g ψ = c • ψ := by
  refine ⟨fun h => φ ((b h : G) * x), ⟨hleft, fun g u => ?_⟩, fun h => hs ?_, fun g c hgc => ?_⟩
  · rw [hω]
    have h1 := hφ _ ((hCU u.1).1 u.2) ((b g : G) * x)
    have h2 : (b g : G) * x * (x⁻¹ * (b u.1 : G) * x) = (b (g * u.1) : G) * x := by
      rw [map_mul, Subgroup.coe_mul]
      group
    rw [h2] at h1
    simpa using h1
  · have := congrFun h (b.symm s)
    simpa using this
  · obtain ⟨h1, h2, h3, h4⟩ := hP g c hgc
    exact dc_tr S U hS b x C.U hCU g h1 h2 h3 φ hφ c h4

private theorem inS_cu {L : Type} [Field L] [NumberField L] [IsCMField L] {B : Bridge L} (D : Dat B.Δ) (U : Subgroup (UA L 2)) (x : UA L 2) (y : DA B.Δ)
    (hy : ∀ g : SA B.Δ, ∃ g' : SA B.Δ, (g' : DA B.Δ) = y⁻¹ * g * y ∧ (B.bS g' : UA L 2) = x⁻¹ * B.bS g * x)
    (hL : ∀ g : SA B.Δ, (g : DA B.Δ) ∈ D.U2 ↔ (B.bS g : UA L 2) ∈ U) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ch : Lp L → ℂ) (C : Base (SU B.Δ) (SA B.Δ) V) (hC : D.IsBS ch y C) (g : SA B.Δ) :
    g ∈ C.U ↔ x⁻¹ * (B.bS g : UA L 2) * x ∈ U :=
  (hy g).elim fun g' h => ((hC.U g).trans (Iff.of_eq (congrArg (· ∈ D.U2) h.1.symm))).trans
    ((hL g').trans (Iff.of_eq (congrArg (· ∈ U) h.2)))

end UpperTheory.V.Z.Sym.So

namespace UpperTheory.V.Z.Sym.So

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {B : Bridge L} (hB : B.Ok) (T : Spl B) (S : Finset (Plc L))
    (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ) (hA : A.Ok) (hF : Fit T S VL A)
include hB hA hF

private theorem lev5 : ∀ w (h : IsSplitAt w) (n : ℕ) (ψ : Fin n → (Kw w)ˣ →* ℂˣ) (d : Fin n → (Kv (un w))ˣ), n = 2 ∨ n = 3 →
    expo ψ (fun i => iu T w h (d i)) = expo (fun i => (ψ i).comp (iu T w h)) d :=
  (levG L B hB T S VL A hA hF).2.2.2.2

set_option allowUnsafeReducibility true in
attribute [local irreducible] cv Kv Ov DX KD RP SA Lsq

private theorem lev2 : ∀ g : SA B.Δ, (g : DA B.Δ) ∈ A.dat.U2 ↔ (B.bS g : UA L 2) ∈ lev (Kall L 2) S VL :=
  (levG L B hB T S VL A hA hF).2.1

private theorem lev4 : ∀ (g : SA B.Δ) d, A.IsElD g d ↔ OnS S (B.bS g : UA L 2) ∧
    ∀ w ∈ S, ∀ h, cLoc w (B.bS g : UA L 2) = Sig.dg fun i => iu T w h (d (un w) i) :=
  (levG L B hB T S VL A hA hF).2.2.2.1

end

private theorem op0 {L : Type} [Field L] [NumberField L] [IsCMField L] {B : Bridge L} (hB : B.Ok) (T : Spl B) (S : Finset (Plc L))
    (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ) (hA : A.Ok) (hF : Fit T S VL A) (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)) (hab : FitCh T S a b)
    {V : Type} [AddCommGroup V] [Module ℂ V] (φ : UA L 2 → V) (hφ : ∀ u ∈ lev (Kall L 2) S VL, ∀ g, φ (g * u) = φ g)
    (hE : ∀ w ∈ S, EigS φ w (VL w) (a w)) (t : Dat.Par (Lp L)) (x : UA L 2) (hCone : A.Cone t)
    (h1 : OnS S x) (h2 : ∀ w ∈ S, ∀ h, cLoc w x = Sig.dg fun i => iu T w h (SD.dS t (un w) i)) :
    AlgebraTools.FinOrb (lev (Kall L 2) S VL) (lev (Kall L 2) S VL) x ∧
    (∀ u ∈ lev (Kall L 2) S VL, ∃ c ∈ lev (Kall L 2) S VL, c * x = x * c ∧ u * c⁻¹ ∈ finU L 2 ⊓ SUA L ∧ c⁻¹ * u ∈ finU L 2 ⊓ SUA L) ∧
    dcF (lev (Kall L 2) S VL) x φ = A.exS b t • φ := by
  classical
  have hfull : Full (Kall L 2) S := ⟨le_rfl, fun _ _ => inf_le_right⟩
  have hd : ∃ d : ∀ w : Plc L, Fin 2 → (Kw w)ˣ, ∀ w h, d w = fun i => iu T w h (SD.dS t (un w) i) :=
    ⟨fun w => if h : IsSplitAt w then fun i => iu T w h (SD.dS t (un w) i) else 1, fun w h => dif_pos h⟩
  refine hd.elim fun d hd => ?_
  have h3 : ∀ w ∈ S, cLoc w x = Sig.dg (d w) := fun w hw => (h2 w hw (hF.pl.split w hw)).trans (congrArg _ (hd w _).symm)
  have hp := prodEig L 2 _ S VL hF.pl hfull d x h1 h3
  refine ⟨hp.1, fun u hu => (torUA L _ S VL hF.pl hfull u hu).imp fun c hc => ⟨hc.1, hc.2.2.2 x d h1 h3, hc.2.1, hc.2.2.1⟩, ?_⟩
  refine (hp.2 V φ hφ (fun w => expo ![a w, 1] (d w)) fun w hw => ?_).trans (congrArg (· • φ) ?_)
  · have h := hF.pl.split w hw
    have e : d w = ![iu T w h (t (un w)), (iu T w h (t (un w)))⁻¹] := by
      rw [hd w h]
      funext i
      fin_cases i
      · rfl
      · exact map_inv _ _
    rw [e]
    refine hE w hw _ ?_
    have hv := val_lt_one _ _ (hCone _ ((hF.sg _).2 ⟨w, hw, rfl⟩))
    have := ((T w h).val_le 1 (t (un w))).not
    rw [map_one, map_one, map_one, not_le, not_le] at this
    exact this.2 hv
  · refine Finset.prod_bij (fun w _ => un w) (fun w hw => (hF.sg _).2 ⟨w, hw, rfl⟩) (fun w hw w' hw' e => hF.pl.inj hw hw' e)
      (fun v hv => ((hF.sg v).1 hv).elim fun w hw => ⟨w, hw.1, hw.2⟩) fun w hw => ?_
    have h := hF.pl.split w hw
    rw [hd w h, lev5 hB T S VL A hA hF w h 2 _ _ (.inl rfl), hab w hw h]
    congr 1
    funext i
    fin_cases i <;> rfl

private theorem inS_op {L : Type} [Field L] [NumberField L] [IsCMField L] {B : Bridge L} (hB : B.Ok) (T : Spl B) (S : Finset (Plc L))
    (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ) (hA : A.Ok) (hF : Fit T S VL A) (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)) (hab : FitCh T S a b)
    {V : Type} [AddCommGroup V] [Module ℂ V] (φ : UA L 2 → V) (hφ : ∀ u ∈ lev (Kall L 2) S VL, ∀ g, φ (g * u) = φ g)
    (hE : ∀ w ∈ S, EigS φ w (VL w) (a w)) (t : Dat.Par (Lp L)) (g : SA B.Δ) (hCone : A.Cone t) (hEl : A.IsElD g (SD.dS t)) :
    OnS S (B.bS g : UA L 2) ∧ AlgebraTools.FinOrb (lev (Kall L 2) S VL) (lev (Kall L 2) S VL) (B.bS g : UA L 2) ∧
    (∀ u ∈ lev (Kall L 2) S VL, ∃ c ∈ lev (Kall L 2) S VL, c * (B.bS g : UA L 2) = (B.bS g : UA L 2) * c ∧ u * c⁻¹ ∈ finU L 2 ⊓ SUA L ∧ c⁻¹ * u ∈ finU L 2 ⊓ SUA L) ∧
    dcF (lev (Kall L 2) S VL) (B.bS g : UA L 2) φ = A.exS b t • φ :=
  have h := (lev4 hB T S VL A hA hF g _).1 hEl
  ⟨h.1, op0 hB T S VL A hA hF a b hab φ hφ hE t _ hCone h.1 h.2⟩

private theorem inS_left' {L : Type} [Field L] [NumberField L] [IsCMField L] (B : Bridge L) (hB : B.Ok) (j : ℕ) (e : InfinitePlace L → ℤ)
    (U : Subgroup (UA L 2)) (φ : UA L 2 → Wt.VD (InfinitePlace L) j) (hφ : IsAF (repE j e) U φ) (x : UA L 2) (hxf : x ∈ finU L 2)
    (ι : SU B.Δ →* SA B.Δ) (hι : ∀ γ v, mt ((ι γ : DA B.Δ).1 v) = (mt (γ : DX B.Δ)).map (lmap (cv v) B.Δ))
    (W : Representation ℂ (SU B.Δ) (Wt.VD (InfinitePlace L) j)) (hW : W = Wt.cS (em B) j) (γ : SU B.Δ) (g : SA B.Δ) :
    φ ((B.bS (ι γ * g) : UA L 2) * x) = W γ (φ ((B.bS g : UA L 2) * x)) := by
  subst hW
  exact inS_left B hB j e U φ hφ x hxf ι hι γ g

private theorem inS_p {L : Type} [Field L] [NumberField L] [IsCMField L] {B : Bridge L} (hB : B.Ok) (T : Spl B) (S : Finset (Plc L))
    (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ) (hA : A.Ok) (hF : Fit T S VL A) (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)) (hab : FitCh T S a b)
    {V : Type} [AddCommGroup V] [Module ℂ V] (φ : UA L 2 → V) (hφ : ∀ u ∈ lev (Kall L 2) S VL, ∀ g, φ (g * u) = φ g)
    (hE : ∀ w ∈ S, EigS φ w (VL w) (a w)) (x : UA L 2) (hxf : x ∈ finU L 2) (hxo : OffS S x) (t : Dat.Par (Lp L)) (g : SA B.Δ) (c : ℂ)
    (hCone : A.Cone t) (hEl : A.IsElD g (SD.dS t)) (hc : c = A.exS b t) :
    x * (B.bS g : UA L 2) = (B.bS g : UA L 2) * x ∧ AlgebraTools.FinOrb (lev (Kall L 2) S VL) (lev (Kall L 2) S VL) (B.bS g : UA L 2) ∧
    (∀ u ∈ lev (Kall L 2) S VL, ∃ c ∈ lev (Kall L 2) S VL, c * (B.bS g : UA L 2) = (B.bS g : UA L 2) * c ∧ u * c⁻¹ ∈ finU L 2 ⊓ SUA L ∧ c⁻¹ * u ∈ finU L 2 ⊓ SUA L) ∧
    dcF (lev (Kall L 2) S VL) (B.bS g : UA L 2) φ = c • φ := by
  subst hc
  have h := inS_op hB T S VL A hA hF a b hab φ hφ hE t g hCone hEl
  exact ⟨off_on_comm S x _ hxf hxo h.1, h.2⟩

private theorem automorphic_in_spherical_level {L : Type} [Field L] [NumberField L] [IsCMField L] {B : Bridge L} (hB : B.Ok) (T : Spl B) (S : Finset (Plc L))
    (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ) (hA : A.Ok) (hF : Fit T S VL A) (j : ℕ) (e : InfinitePlace L → ℤ)
    (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)) (hab : FitCh T S a b)
    (φ : UA L 2 → Wt.VD (InfinitePlace L) j) (hφ0 : φ ≠ 0) (hφ : IsAF (repE j e) (lev (Kall L 2) S VL) φ) (hE : ∀ w ∈ S, EigS φ w (VL w) (a w)) :
    ∃ y : DA B.Δ, A.dat.Off y ∧ ∀ ch (C : Base (SU B.Δ) (SA B.Δ) (Wt.VD (InfinitePlace L) j)), A.dat.IsBS ch y C → C.W = Wt.cS (em B) j →
      ∃ ψ ∈ C.Forms, ψ ≠ 0 ∧ A.EigS C.U ψ b :=
  (So.translate L S VL hF.pl _ (repE j e) φ hφ hφ0).elim fun x hx => hx.2.2.elim fun s hs => (hB.conj x hx.1).elim fun y hy =>
    ⟨y, fun v hv => ((hF.sg v).1 hv).elim fun w hw => hw.2 ▸ hy.1 _ fun u hu => hx.2.1 w hw.1 u hu, fun ch C hC hW =>
      (gen (H := ↥(SA B.Δ)) (G := ↥(UA L 2)) (finU L 2 ⊓ SUA L) (lev (Kall L 2) S VL) (sub_normal L) B.bS x C hC.ω
      (inS_cu A.dat _ x y hy.2 (lev2 hB T S VL A hA hF) ch C hC) φ hφ.level
      (fun γ g => inS_left' B hB j e _ φ hφ x hx.1 C.ι hC.ι _ hW γ g) ⟨s, hs.1⟩ hs.2
      (fun g c => ∃ t, A.Cone t ∧ A.IsElD g (SD.dS t) ∧ c = A.exS b t)
      (fun g c h => h.elim fun t ht => inS_p hB T S VL A hA hF a b hab φ hφ.level hE x hx.1 hx.2.1 t g c ht.1 ht.2.1 ht.2.2)).elim
        fun ψ h => ⟨ψ, h.1, h.2.1, fun t g h1 h2 => h.2.2 g _ ⟨t, h1, h2, rfl⟩⟩⟩

end UpperTheory.V.Z.Sym.So

set_option allowUnsafeReducibility true in
attribute [local irreducible] cv Kv Ov DX KD RP SA Lsq

theorem UpperTheory.V.Z.Sym.So.inS :
    UpperTheory.V.Z.Sym.So.InS := fun _ _ _ _ _ hB T S VL A hA hF j e a b hab φ h0 hφ hE => automorphic_in_spherical_level hB T S VL A hA hF j e a b hab φ h0 hφ hE

end

import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ConjMemLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DetRoot
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FinToAF
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.HomTrivialOnDetOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OutInvMulMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FinOrbSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ExpoMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RpExistsUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ExpoEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So.OS

section SlopeTestRemainingChoices

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem exFin (n : ℕ) : ∃ p : UA L n →* finU L n,
    (∀ f : finU L n, ∀ k ∈ infU L n, p ((f : UA L n) * k) = f) ∧ ∀ x : UA L n, ∃ k ∈ infU L n, x = (p x : UA L n) * k := by
  obtain ⟨-, -, hs, hc, he, hm, -, -⟩ := uaFacts L n
  have hone : ∀ x : UA L n, x ∈ finU L n → x ∈ infU L n → x = 1 := fun x h₁ h₂ =>
    he x 1 (fun w => by rw [(hm x).2.1 h₂ w, map_one]) (fun τ => by rw [(hm x).1.1 h₁ τ, map_one])
  have hu : ∀ f ∈ finU L n, ∀ k ∈ infU L n, ∀ f' ∈ finU L n, ∀ k' ∈ infU L n, f * k = f' * k' → f = f' := by
    intro f hf k hk f' hf' k' hk' h
    have h₀ : f'⁻¹ * f = k' * k⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    have h₁ := hone _ (mul_mem (inv_mem hf') hf) (h₀ ▸ mul_mem hk' (inv_mem hk))
    exact (inv_mul_eq_one.1 h₁).symm
  choose f hf k hk hx using hs
  refine ⟨{ toFun := fun x => ⟨f x, hf x⟩, map_one' := ?_, map_mul' := ?_ }, ?_, fun x => ⟨k x, hk x, hx x⟩⟩
  · exact Subtype.ext (hu _ (hf 1) _ (hk 1) 1 (one_mem _) 1 (one_mem _) (by rw [← hx, one_mul]))
  · intro x y
    refine Subtype.ext (hu _ (hf (x * y)) _ (hk (x * y)) (f x * f y) (mul_mem (hf x) (hf y)) (k x * k y) (mul_mem (hk x) (hk y)) ?_)
    have hxy := (hc _ (hf y) _ (hk x)).eq
    calc f (x * y) * k (x * y) = (f x * k x) * (f y * k y) := by rw [← hx, ← hx, ← hx]
      _ = f x * (k x * f y) * k y := by simp only [mul_assoc]
      _ = f x * (f y * k x) * k y := by rw [hxy]
      _ = _ := by simp only [mul_assoc]
  · intro f₀ k₀ hk₀
    exact Subtype.ext (hu _ (hf _) _ (hk _) _ f₀.2 _ hk₀ (hx _).symm)

theorem infC_fin {n : ℕ} {x : UA L n} (h : x ∈ finU L n) : infC L n x = 1 := by
  obtain ⟨-, -, -, -, -, hm, -, -⟩ := uaFacts L n
  funext v
  exact (hm x).1.1 h v.embedding

theorem cD_rS (B : Bridge L) (n : ℕ) (e : ℤ) (γ : SU B.Δ) :
    Wt.cD (em B) n e (γ : DX B.Δ) = repE n (0 : InfinitePlace L → ℤ) (infC L 2 (B.rS γ : UA L 2)) := by
  have h₁ : Wt.infG (em B) 2 ((γ : DX B.Δ) : GL (Fin 2) _) = infC L 2 (B.rS γ : UA L 2) := by
    funext v
    apply Units.ext
    show _ = ((cEmb v.embedding (B.rS γ : UA L 2) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
    rw [B.rS_inf]
    rfl
  have hdet : Matrix.GeneralLinearGroup.det ((γ : DX B.Δ) : GL (Fin 2) (Lsq (Lp L) B.Δ)) = 1 :=
    MonoidHom.mem_ker.1 (show (γ : DX B.Δ) ∈ ((Matrix.GeneralLinearGroup.det (n := Fin 2) (R := Lsq (Lp L) B.Δ)).comp (DX B.Δ).subtype).ker from γ.2)
  have h₂ : Wt.detE 2 e (Wt.infG (em B) 2 ((γ : DX B.Δ) : GL (Fin 2) _)) = 1 := by
    show ∏ v, Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (em B v) ((γ : DX B.Δ) : GL (Fin 2) _)) ^ e = 1
    simp [Matrix.GeneralLinearGroup.map_det, hdet]
  show Wt.repD _ n e (Wt.infG (em B) 2 ((γ : DX B.Δ) : GL (Fin 2) _)) = _
  have h₃ : ∀ g : InfinitePlace L → GL (Fin 2) ℂ, repE n (0 : InfinitePlace L → ℤ) g = Wt.mRep 2 _ g := fun g => by
    show ((∏ v, Matrix.GeneralLinearGroup.det (g v) ^ (0 : InfinitePlace L → ℤ) v : ℂˣ) : ℂ) • Wt.mRep 2 _ g = _
    simp
  rw [Wt.repD_apply, h₂, h₁, h₃]
  simp

def eT : ↥(finU L 2 ⊓ SUA L) ≃* ↥((SUA L).subgroupOf (finU L 2)) where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun s := ⟨s.1.1, s.1.2, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem comm_one {C : Type} [CommGroup C] (x y : C) : x * y * x⁻¹ * y⁻¹ = 1 := by
  rw [mul_comm x y, mul_inv_cancel_right, mul_inv_cancel]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Sym.So.OS

namespace UpperTheory.V.Z.Sym.So.OS

section Aux2

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem comm_mem (x y : finU L 2) : x * y * x⁻¹ * y⁻¹ ∈ (SUA L).subgroupOf (finU L 2) := by
  rw [Subgroup.mem_subgroupOf]
  refine MonoidHom.mem_ker.2 ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact comm_one _ _

theorem rat_iota (B : Bridge L) (hB : B.Ok) (p : UA L 2 →* finU L 2)
    (hp1 : ∀ f : finU L 2, ∀ k ∈ infU L 2, p ((f : UA L 2) * k) = f) (ι : DX B.Δ →* DA B.Δ) (hι : IsIotaD ι) (γ₀ : SU B.Δ) :
    ∃ h : ι γ₀ ∈ SA B.Δ, ((B.bS ⟨ι γ₀, h⟩ : ↥(finU L 2 ⊓ SUA L)) : UA L 2) = (p (B.rS γ₀ : UA L 2) : UA L 2) := by
  have hdet : (mt (γ₀ : DX B.Δ)).det = 1 :=
    congrArg Units.val (MonoidHom.mem_ker.1 (show (γ₀ : DX B.Δ) ∈ ((Matrix.GeneralLinearGroup.det (n := Fin 2) (R := Lsq (Lp L) B.Δ)).comp (DX B.Δ).subtype).ker from γ₀.2))
  have hmem : ι γ₀ ∈ SA B.Δ := by
    refine Subgroup.mem_iInf.2 fun v => ?_
    show (ι γ₀).1 v ∈ SU (cv v B.Δ)
    refine MonoidHom.mem_ker.2 (Units.ext ?_)
    show (mt ((ι γ₀).1 v)).det = 1
    rw [hι, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
  refine ⟨hmem, ?_⟩
  obtain ⟨k', hk', hr, -⟩ := hB.finS γ₀ ⟨ι γ₀, hmem⟩ (hι _)
  have h₁ := hp1 ⟨_, (B.bS ⟨ι γ₀, hmem⟩).2.1⟩ k' hk'.1
  have h₂ : p (B.rS γ₀ : UA L 2) = ⟨_, (B.bS ⟨ι γ₀, hmem⟩).2.1⟩ := by rw [hr]; exact h₁
  exact (congrArg Subtype.val h₂).symm

end Aux2

end UpperTheory.V.Z.Sym.So.OS

namespace UpperTheory.V.Z.Sym.So.OS

section Aux3

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

def eS (B : Bridge L) : SA B.Δ ≃* ↥((SUA L).subgroupOf (finU L 2)) := B.bS.trans eT

set_option maxHeartbeats 2000000 in
theorem left_eq (B : Bridge L) (hB : B.Ok) (p : UA L 2 →* finU L 2)
    (hp1 : ∀ f : finU L 2, ∀ k ∈ infU L 2, p ((f : UA L 2) * k) = f)
    (hp2 : ∀ x : UA L 2, ∃ k ∈ infU L 2, x = (p x : UA L 2) * k)
    {m : ℕ} (hm : 3 ≤ m) {U : Subgroup (UA L 2)} (hU : IsCong m U) (ι : DX B.Δ →* DA B.Δ) (hι : IsIotaD ι)
    {n : ℕ} {e : ℤ} (ψ : SA B.Δ → Wt.VD (InfinitePlace L) n)
    (h0 : ∀ (γ : SU B.Δ) (g g' : SA B.Δ), (g' : DA B.Δ) = ι γ * g → ψ g' = Wt.cD (em B) n e (γ : DX B.Δ) (ψ g))
    (γ : ratU L 2) (g g' : ↥((SUA L).subgroupOf (finU L 2))) (hg : (g' : finU L 2) = p γ.1 * g) :
    ψ ((eS B).symm g') = repE n (0 : InfinitePlace L → ℤ) (infC L 2 γ.1) (ψ ((eS B).symm g)) := by
  obtain ⟨k, hk, hγ⟩ := hp2 γ.1
  have hfS : p γ.1 ∈ (SUA L).subgroupOf (finU L 2) := by
    have h₁ := mul_mem g'.2 (inv_mem g.2)
    rwa [hg, mul_inv_cancel_right] at h₁
  have hr : (p γ.1 : UA L 2) * k ∈ ratU L 2 := by rw [← hγ]; exact γ.2
  have hdr := detRoot L m hm U hU _ (p γ.1).2 k hk hr 1 (one_mem _)
    (by rw [mul_one]; exact Subgroup.mem_subgroupOf.1 hfS)
  have hγS : γ.1 ∈ ratU L 2 ⊓ SUA L := ⟨γ.2, by rw [hγ]; exact mul_mem hdr.1 hdr.2⟩
  obtain ⟨γ₀, hγ₀⟩ : ∃ γ₀ : SU B.Δ, (B.rS γ₀ : UA L 2) = γ.1 :=
    ⟨B.rS.symm ⟨γ.1, hγS⟩, congrArg Subtype.val (B.rS.apply_symm_apply ⟨γ.1, hγS⟩)⟩
  obtain ⟨hmem, hf'⟩ := rat_iota B hB p hp1 ι hι γ₀
  rw [hγ₀] at hf'
  have hg₁ : (((eS B).symm g' : SA B.Δ) : DA B.Δ) = ι γ₀ * ((eS B).symm g : SA B.Δ) := by
    have : (eS B).symm g' = ⟨ι γ₀, hmem⟩ * (eS B).symm g := by
      apply (eS B).injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      refine Subtype.ext (Subtype.ext ?_)
      show ((g' : finU L 2) : UA L 2) = (B.bS ⟨ι γ₀, hmem⟩ : UA L 2) * ((g : finU L 2) : UA L 2)
      rw [hg, hf']
      rfl
    exact congrArg Subtype.val this
  have h₁ := h0 γ₀ _ _ hg₁
  rw [cD_rS, hγ₀] at h₁
  exact h₁

end Aux3

end UpperTheory.V.Z.Sym.So.OS

namespace UpperTheory.V.Z.Sym.So.OS

section PrimeReciprocalSums

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

def psiS (B : Bridge L) {V : Type} (ψ : SA B.Δ → V) (s : ↥((SUA L).subgroupOf (finU L 2))) : V := ψ ((eS B).symm s)

instance suaNormal : (SUA L).Normal := by unfold SUA; infer_instance

end PrimeReciprocalSums

end UpperTheory.V.Z.Sym.So.OS

namespace UpperTheory.V.Z.Sym.So.OS

section Aux5

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem dom_two {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ)
    (h : valuation k (t : k) ≤ valuation k ((t⁻¹ : kˣ) : k)) : AlgebraTools.Dom ![t, t⁻¹] := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact le_rfl
  · exact h
  · simp at hij
  · exact le_rfl

theorem val_inv_ge {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ)
    (h : valuation k (t : k) < 1) : valuation k (t : k) ≤ valuation k ((t⁻¹ : kˣ) : k) := by
  have h₀ : valuation k (t : k) ≠ 0 := (Valuation.ne_zero_iff _).2 t.ne_zero
  rw [Units.val_inv_eq_inv_val, map_inv₀]
  exact h.le.trans ((one_le_inv₀ (zero_lt_iff.2 h₀)).2 h.le)

variable {B : Bridge L}

set_option maxHeartbeats 4000000 in
theorem place_el (hB : B.Ok) (T : Spl B) {S : Finset (Plc L)} {VL : ∀ w : Plc L, Lev (Kw w)} {A : SD B.Δ} (hA : A.Ok) (hF : Fit T S VL A)
    {a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ} {b : Chs (Lp L)} (hab : FitCh T S a b) {w : Plc L} (hw : w ∈ S) (h : IsSplitAt w) (t : (Kw w)ˣ)
    (ht : valuation (Kw w) (t : Kw w) < 1) :
    ∃ (t' : Dat.Par (Lp L)) (g : SA B.Δ), A.IsElD g (SD.dS t') ∧ A.DomS (SD.dS t') ∧ A.exS b t' = Dict.expo ![a w, 1] ![t, t⁻¹] ∧
      (B.bS g : UA L 2) = secW 2 w (Sig.dg ![t, t⁻¹]) ∧ (∀ u, un u ≠ un w → cLoc u (B.bS g : UA L 2) = 1) ∧
      ∀ w' ∈ S, ∀ h', cLoc w' (B.bS g : UA L 2) = Sig.dg fun i => iu T w' h' (SD.dS t' (un w') i) := by
  classical
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : (Kv (un w))ˣ, iu T w h t₀ = t :=
    ⟨Units.map ((T w h).i.symm : Kw w →* Kv (un w)) t, Units.ext ((T w h).i.apply_symm_apply _)⟩
  have ht₀' : iu T w h t₀⁻¹ = t⁻¹ := by rw [map_inv, ht₀]
  obtain ⟨t', h1, h2⟩ : ∃ t' : Dat.Par (Lp L), t' (un w) = t₀ ∧ ∀ v, v ≠ un w → t' v = 1 :=
    ⟨Pi.mulSingle _ t₀, Pi.mulSingle_eq_same _ _, fun v hv => Pi.mulSingle_eq_of_ne hv _⟩
  have hdS : SD.dS t' (un w) = ![t₀, t₀⁻¹] := by
    show ![t' (un w), (t' (un w))⁻¹] = _
    rw [h1]
  have hdS1 : ∀ v, v ≠ un w → SD.dS t' v = 1 := by
    intro v hv
    show ![t' v, (t' v)⁻¹] = _
    rw [h2 v hv]
    funext i
    fin_cases i <;> simp
  have hEl := elEx _ _ A hA
  obtain ⟨g, hg₀⟩ : ∃ g : SA B.Δ, A.IsElD (g : DA B.Δ) (SD.dS t') :=
    ⟨⟨(hEl.2.1 (SD.dS t')).choose, hEl.2.2.2.2 _ t' (hEl.2.1 (SD.dS t')).choose_spec.1⟩, (hEl.2.1 (SD.dS t')).choose_spec.1⟩
  have hLG := levG L B hB T S VL A hA hF
  have hL4 := hLG.2.2.2.1
  have hL5 := hLG.2.2.2.2
  have hcl := ((hL4 g _).1 hg₀).2
  have hone : ∀ v, v ≠ un w → (g : DA B.Δ).1 v = 1 := by
    intro v hv
    by_cases hvS : v ∈ A.Sg
    · have hS := (datOk _ _ A hA).2.2.1 v hvS
      apply (eD_facts (Kv v) (Ov v) hS.1 hS.2.1 _ _ (A.hs v hvS) hS.2.2.1).1.1
      rw [hg₀.1 v hvS, map_one, hdS1 v hv]
      exact map_one _
    · exact hg₀.2 v hvS
  have hoff : ∀ u, un u ≠ un w → cLoc u (B.bS g : UA L 2) = 1 := fun u hu =>
    (hB.oneS g (un u)).1 (hone _ hu) u rfl
  have hloc : (B.bS g : UA L 2) ∈ locU 2 w :=
    Subgroup.mem_inf.2 ⟨(B.bS g).2.1, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 (hoff u hu)⟩
  have hcw : cLoc w (B.bS g : UA L 2) = Sig.dg ![t, t⁻¹] := by
    rw [hcl w hw h, hdS]
    congr 1
    funext i
    fin_cases i
    · exact ht₀
    · exact ht₀'
  have hsec := ((uaFacts L 2).1 w h).2.2.2 _ hloc
  rw [hcw] at hsec
  have hwg : un w ∈ A.Sg := (hF.sg _).2 ⟨w, hw, rfl⟩
  refine ⟨t', g, hg₀, ?_, ?_, hsec, hoff, hcl⟩
  · intro v hv
    rcases eq_or_ne v (un w) with rfl | hvw
    · rw [hdS]
      apply dom_two
      have h₃ := val_inv_ge t ht
      rw [← ht₀'] at h₃
      rw [← ht₀] at h₃
      exact ((T w h).val_le _ _).1 h₃
    · rw [hdS1 v hvw]
      intro i j _
      exact le_rfl
  · show ∏ v ∈ A.Sg, Dict.expo ![b v, 1] (SD.dS t' v) = _
    rw [Finset.prod_eq_single (un w) ?_ (fun hn => absurd hwg hn), hdS, hab w hw h]
    · have h₃ := hL5 w h 2 ![a w, 1] ![t₀, t₀⁻¹] (Or.inl rfl)
      have e₁ : (fun i => iu T w h (![t₀, t₀⁻¹] i)) = ![t, t⁻¹] := by
        funext i
        fin_cases i
        · exact ht₀
        · exact ht₀'
      have e₂ : (fun i => (![a w, 1] i).comp (iu T w h)) = ![(a w).comp (iu T w h), 1] := by
        funext i
        fin_cases i
        · rfl
        · exact MonoidHom.one_comp _
      rw [e₁, e₂] at h₃
      exact h₃.symm
    · intro v _ hv
      rw [hdS1 v hv]
      exact ((expoEq (Kv v) (b v)).2.2 2 _).2.1

end Aux5

end UpperTheory.V.Z.Sym.So.OS

end
